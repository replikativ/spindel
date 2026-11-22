(ns org.replikativ.spindel.v2.lifetime
  "Detached weak lifetime metadata. No operation enters a world or calls user code."
  (:require [org.replikativ.spindel.v2.host :as hs]))

;; One lock for indexes and owner memberships: no path from this lock takes a
;; world gate. Application watch maps themselves are changed under that gate.
(defonce ^:private monitor #?(:clj (Object.) :cljs (js-obj)))
(defn locked [f] #?(:clj (locking monitor (f)) :cljs (f)))
(defonce ^:private next-id (atom 0))
(defn- fresh-id [] (swap! next-id inc))

(defrecord Family [worlds generation])
(defrecord Capsule [callbacks owners death])
(defrecord Owner [id capsules weak-capsules])

(defn family [] (->Family (hs/vmap) (atom 0)))
(defn index [] (hs/vmap))
(defn generation [family] @(:generation family))

(defn- remove-exact! [m k entry]
  (when (identical? entry (hs/mget m k)) (hs/mdel! m k)))

(defn- forget-owner! [id weak-capsules]
  (locked #(do (doseq [[_ wc] (hs/mentries weak-capsules)]
                 (when-let [c (hs/deref-weak wc)] (hs/mdel! (:owners c) id)))
               (hs/mclear! weak-capsules))))

(defn owner []
  (let [id (fresh-id) weak-capsules (hs/vmap)
        o (->Owner id (hs/vmap) weak-capsules)]
    ;; The cleaning action sees only WEAK capsule memberships, never the
    ;; owner's strong capsule map (which can lead back through a callback).
    (hs/on-collect! o #(forget-owner! id weak-capsules))
    o))

(defn- capsule [idx id on-death]
  (let [death (atom on-death)
        c (->Capsule (atom {}) (hs/vmap) death)
        wc (hs/weak c)]
    (hs/on-collect! c #(do (locked (fn [] (remove-exact! idx id wc)))
                           (when-let [f @death] (f))))
    [c wc]))

(defn source-token!
  "Share the canonical source capsule. Attach it to the Handle cell BEFORE
   publishing its weak entry. No row resolution or world gate is needed."
  ([idx id cell] (source-token! idx id cell nil))
  ([idx id cell on-death]
   (locked #(if-let [c (some-> (hs/mget idx id) hs/deref-weak)]
              (do (aset cell 1 c)
                  (when on-death (compare-and-set! (:death c) nil on-death))
                  c)
              (let [[c wc] (capsule idx id on-death)]
                (aset cell 1 c)
                (hs/mput! idx id wc)
                c)))))

(defn owned-token!
  "An atom, or a Handle accessing a foreign slice, strongly owns this
   world's canonical capsule. Membership in the capsule is weak."
  [idx world-id id o]
  (locked #(let [[c wc] (if-let [c (some-> (hs/mget idx id) hs/deref-weak)]
                          [c (hs/mget idx id)] (capsule idx id nil))]
             (hs/mput! (:capsules o) world-id c)
             (hs/mput! (:weak-capsules o) world-id wc)
             (hs/mput! (:owners c) (:id o) (hs/weak o))
             (hs/mput! idx id wc)
             c)))

(defn callbacks [idx id]
  ;; Keep capsule live while snapshotting. No callbacks execute under monitor.
  (locked #(if-let [c (some-> (hs/mget idx id) hs/deref-weak)] @(:callbacks c) {})))
(defn add-watch! [c k f] (swap! (:callbacks c) assoc k f) nil)
(defn remove-watch! [c k] (swap! (:callbacks c) dissoc k) nil)

(defn clear-index!
  "World death/terminal release: detach its capsules from EVERY surviving
   object owner by identity and clear their callbacks, including home tokens."
  [idx world-id]
  (locked #(do
             (doseq [[_ wc] (hs/mentries idx)]
               (when-let [c (hs/deref-weak wc)]
                 (reset! (:callbacks c) {})
                 (doseq [[_ wo] (hs/mentries (:owners c))]
                   (when-let [o (hs/deref-weak wo)]
                     (when (identical? c (hs/mget (:capsules o) world-id))
                       (hs/mdel! (:capsules o) world-id)
                       (hs/mdel! (:weak-capsules o) world-id))))
                 (hs/mclear! (:owners c))))
             (hs/mclear! idx))))

(defn unregister-world! [family id]
  (locked #(hs/mdel! (:worlds family) id)))

(defn- collection-action
  "The world's collection action, built in its own function: a JS closure
   shares its enclosing function's context, so one made in
   `register-world!` (where the world is a local) would keep it alive."
  [worlds idx id ww collected!]
  (fn []
    (clear-index! idx id)
    (locked (fn [] (remove-exact! worlds id ww)))
    (when collected! (collected!))))

(defn register-world!
  "O(1) insertion, after independent world metadata fields are initialized.
   Compare the copied sweep generation AFTER publishing registry membership.
   The insertion publishes `w`: family maintenance can find it from then on.
   With `failed!`, a throw after the insertion (installing the collection
   action, requesting the sweep) is a failure of the published world,
   passed to `(failed! t)`, and registration continues; only a throw before
   the insertion propagates."
  ([family w id idx copied-generation request!]
   (register-world! family w id idx copied-generation request! nil nil))
  ([family w id idx copied-generation request! collected!]
   (register-world! family w id idx copied-generation request! collected! nil))
  ([family w id idx copied-generation request! collected! failed!]
   (let [ww (hs/weak w) worlds (:worlds family)]
     (locked #(hs/mput! worlds id ww))
     ;; Exactly one world collection action. Detached index/world registry
     ;; hold only ids and weak refs, and this action does not reference w.
     ;; `collected!` (C1: the world's owner acknowledgement) must not either.
     (try (hs/on-collect! w (collection-action worlds idx id ww collected!))
          (catch #?(:clj Throwable :cljs :default) t
            (if failed! (failed! t) (throw t))))
     (try (when (< copied-generation (generation family)) (request! w))
          (catch #?(:clj Throwable :cljs :default) t
            (if failed! (failed! t) (throw t))))
     nil)))

(defn atom-collected!
  "Increment before snapshot, release the metadata lock before dereferencing
   worlds or scheduling maintenance. No append-only dead-id history."
  [family request!]
  (let [worlds (locked #(do (swap! (:generation family) inc)
                            (hs/mvals (:worlds family))))]
    (doseq [ww worlds] (when-let [w (hs/deref-weak ww)] (request! w)))))

(defn clean-atom-on-collection! [a family request!]
  (let [wf (hs/weak family)]
    (hs/on-collect! a #(when-let [f (hs/deref-weak wf)] (atom-collected! f request!)))))

(defn census [family idx o]
  (locked #(cond-> {:worlds (hs/msize (:worlds family)) :watch-index (hs/msize idx)}
             o (assoc :owner-capsules (hs/msize (:capsules o))
                      :owner-memberships (hs/msize (:weak-capsules o))))))

(defn live-token? [idx id]
  (locked #(boolean (some-> (hs/mget idx id) hs/deref-weak))))
