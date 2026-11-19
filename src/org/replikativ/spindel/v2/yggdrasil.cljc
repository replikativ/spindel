(ns org.replikativ.spindel.v2.yggdrasil
  "Yggdrasil systems in v2 worlds (not engine core): which stores a world
   holds, forks that record each store's base and branch it lazily, and their
   affine settlement (merge, discard, transfer, partition) with a journal the
   caller makes durable.

   State. A world's state holds plain data only: `[::holder]`, the key of its
   host entry, and `[::systems sid]` = `{:base b :meta m}` (`b` nil in the world
   that registered the system and holds its canonical handle, else
   `{:snapshot id}` or `{:checkpoint origin}`). Handles, overlays, policies and
   settlement records live in host registries keyed by that holder key; a
   world is *managed* when it is the world its holder entry names. An engine
   fork the layer did not make inherits its parent's holder key and is
   unmanaged: it reads its nearest managed ancestor's stores at their
   recorded bases (`view`) and cannot resolve them for writing (`system`).

   Settlement records are host atoms (`Fork`'s `:record`), plain data plus a
   few closures under this namespace's keys. Statuses: `:open`, `:settling`,
   `:incomplete`, `:merged`, `:discarded`, `:transferred` (settled by its
   `:owner` only) and `:partitioned` (settled through its leaves). A record
   is unsettled while the registry lists it; it leaves the registry when it
   is terminal (a partitioned one when every leaf is).

   Resolution and settlement do I/O on the caller's thread and are JVM host
   operations: refused in a body or while the thread processes a world (B7)."
  (:require [org.replikativ.spindel.v2.core :as v2]
            [yggdrasil.convergent.overlay :as ovl]
            [yggdrasil.protocols :as yp]))

;; ---------------------------------------------------------------------------
;; Host registries (process-wide)

(defonce ^:private holders (atom {}))       ; holder key -> entry atom
(defonce ^:private policies (atom {}))      ; [holder key, sid] -> policy map
(defonce ^:private settlements (atom {}))   ; fork id -> record atom, unsettled only
(defonce ^:private world-holders            ; managed world -> its holder key
  #?(:clj (java.util.Collections/synchronizedMap (java.util.WeakHashMap.))
     :cljs (js/WeakMap.)))
(defonce ^:private executor
  (atom #?(:clj (fn [f] (future-call f) nil)
           :cljs (fn [f] (js/setTimeout f 0) nil))))

;; every decision that reads more than one record (claims, child adds,
;; parent-ended) is taken under this lock; it guards no I/O
(defonce ^:private claim-lock #?(:clj (Object.) :cljs #js {}))

;; a world gets its holder once: the check, the mint and the state write are
;; one step (review 6)
(defonce ^:private holder-lock #?(:clj (Object.) :cljs #js {}))

(def ^:private default-deadline-ms 30000)

(defrecord Fork [id world record])

(defn set-executor!
  "The executor that runs the layer's lifecycle work (cleanup and discards
   after a world completed): `(f thunk)` runs `thunk` on a host thread. The
   engine's `on-complete` callbacks only hand work to it."
  [f]
  (reset! executor f)
  nil)

(defn- run-later! [thunk]
  (@executor (fn [] (try (thunk) (catch #?(:clj Throwable :cljs :default) _ nil)))))

(defn- refusal [type msg data]
  (ex-info msg (assoc data :type type)))

(defn- weak [w] #?(:clj (java.lang.ref.WeakReference. w) :cljs (js/WeakRef. w)))
(defn- deref-weak [r] (when r #?(:clj (.get ^java.lang.ref.WeakReference r) :cljs (.deref r))))

(defn- host-only! [op]
  (when (or (v2/active-run) (v2/cw))
    (throw (refusal ::not-host (str op ": a host operation, refused in a body or while processing a world (B7)")
                    {:op op}))))

(defn- entry [hk] (when hk (get @holders hk)))
(defn- entry-world [e] (some-> e deref :world deref-weak))
(defn- own-holder [w] #?(:clj (.get ^java.util.Map world-holders w) :cljs (.get world-holders w)))

(defn- released-ex? [e] (boolean (:spindel/released (ex-data e))))

(defn- released? [w]
  (try (v2/world-state w) false
       (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) e
         (if (released-ex? e) true (throw e)))))

(defn- inherited-holder
  "The holder key in `w`'s state (its own, or inherited by an engine fork),
   nil when it has none or `w` is released."
  [w]
  (try (get (v2/world-state w) ::holder)
       (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) e
         (if (released-ex? e) nil (throw e)))))

(defn- record-data
  "The record without the layer's closures: what `status` and the journal see."
  [r]
  (into {} (remove (fn [[k _]] (= (namespace k) (namespace ::x)))) r))

(defn- unsettled? [id] (contains? @settlements id))

(defn- records-where [k v]
  (filter #(= v (get @% k)) (vals @settlements)))

;; ---------------------------------------------------------------------------
;; Holders and world completion

(declare world-completed! finish-pending-cleanup! discard-internal!)

(defn- mint-holder!
  "A new holder entry for `w`, which becomes managed. Its completion is
   observed once (`world-completed!`)."
  [w fork-id parent-hk rec]
  (let [hk (random-uuid)
        e (atom {:key hk :world (weak w) :fork-id fork-id :parent parent-hk :record rec
                 :systems {} :handles {} :overlays {} :pending {} :pending-cleanup []
                 :complete? false})]
    (swap! holders assoc hk e)
    #?(:clj (.put ^java.util.Map world-holders w hk) :cljs (.set world-holders w hk))
    (v2/on-complete w (fn [] (run-later! #(world-completed! hk))))
    hk))

(defn- drop-holder! [hk]
  (swap! holders dissoc hk)
  (swap! policies #(into {} (remove (fn [[[k _] _]] (= k hk))) %)))

(defn- maybe-drop-holder!
  "Drops a holder whose world completed, with no unsettled record of it and
   no cleanup still to run (§2.2 retention)."
  [hk]
  (when-let [e (entry hk)]
    (let [m @e]
      (when (and (or (:complete? m) (some-> (deref-weak (:world m)) v2/complete?))
                 (empty? (:pending-cleanup m))
                 (empty? (:cleanup-owed m))
                 (not-any? #(= hk (:child @%)) (vals @settlements)))
        (drop-holder! hk)))))

(defn- parent-live? [r]
  (let [pe (entry (:parent r))
        pw (entry-world pe)]
    (and pe pw (not (:complete? @pe)) (not (v2/complete? pw)))))

(defn- parent-ended!
  "§2.5: the end of the parent's world (or a discard of the parent) discards
   an unsettled fork (F11). The record is flagged first: one mid-operation is
   discarded when that operation lets go of it."
  [rec reason]
  (let [run? (locking claim-lock
               (swap! rec assoc ::parent-ended reason)
               (contains? #{:open :transferred :incomplete} (:status @rec)))]
    (when run?
      (try (discard-internal! rec reason)
           (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) e
             ;; claimed meanwhile: the flag discards it when it is let go
             (when-not (= ::settling (:type (ex-data e))) (throw e)))))))

(defn- world-completed! [hk]
  (some-> (entry hk) (swap! assoc :complete? true))
  ;; the records name the parent by key: they are found after its holder went
  (doseq [rec (records-where :parent hk)] (parent-ended! rec :parent-ended))
  (finish-pending-cleanup! hk)
  (maybe-drop-holder! hk))

;; ---------------------------------------------------------------------------
;; Policies and the journal

(defn- policy-of
  "The policy registered for `sid` at `hk` or the nearest ancestor holder."
  [hk sid]
  (loop [k hk n 0]
    (when (and k (< n 10000))
      (or (get @policies [k sid])
          (recur (some-> (entry k) deref :parent) (inc n))))))

(defn- branch-name [h]
  (when (satisfies? yp/Branchable h)
    (try (yp/current-branch h) (catch #?(:clj Throwable :cljs :default) _ nil))))

(defn- scope
  "The systems a record settles: its partition's, else every system of the
   child world."
  [r ce]
  (or (:systems r) (set (keys (:systems ce)))))

(defn- locators* [r]
  (when-let [e (entry (:child r))]
    (let [ce @e]
      (into {}
            (keep (fn [sid]
                    (when-let [{:keys [base meta]} (get-in ce [:systems sid])]
                      [sid (cond
                             (nil? base) {:base nil :child-only true :meta meta}
                             (get-in ce [:overlays sid])
                             (cond-> {:base base}
                               (branch-name (get-in ce [:handles sid]))
                               (assoc :branch (branch-name (get-in ce [:handles sid]))))
                             :else {:base base})])))
            (scope r ce)))))

(defn locators
  "F6a: per system of `fork`, what a durable fork row needs to clean up after
   a crash: `{sid {:base b}}`, plus `:branch` once branched (the adapter's
   branch name), or `{:base nil :child-only true :meta m}` for a system
   registered in the fork (its store config is the registrant's, in `meta`)."
  [fork]
  (locators* @(:record fork)))

(defn- descriptor [r]
  (let [msg (fn [x] (if (instance? #?(:clj Throwable :cljs js/Error) x) (ex-message x) x))]
    (-> (record-data r)
        (dissoc :hook-error)
        (update :last-error msg)
        (update :restart-error msg)
        (update :journal-error msg)
        (update :close-report #(if (map? %) (update % :error msg) %))
        (assoc :locators (locators* r)))))

(defn describe
  "A plain-data descriptor of `fork` the caller can persist as EDN:
   `:fork/id`, `:parent-world-id`/`:child-world-id` (`v2/world-id`, unique
   within the family), `:status`, `:phase`, `:operation`, `:plan`, `:done`,
   `:cleaned`, `:owner`, `:meta`, `:leaves`/`:leaf-spec` (a partitioned
   fork), `:partition-of`/`:leaf`/`:systems` (a leaf), `:hook-status`,
   errors as messages and `:locators` (F6a). The journal hook receives the
   same map with `:event`."
  [fork]
  (descriptor @(:record fork)))

(defn- journal-data [r event]
  (assoc (descriptor r) :event event))

(defn- journal!
  "Calls the caller's `:journal` hook with the record's data (F6a). A throw
   is the failure of the step it records."
  ([rec event] (journal! rec event @rec))
  ([rec event r]
   (when-let [f (::journal @rec)] (f (journal-data r event)))))

(defn- journal-quietly!
  "journal! after the outcome is fixed: a failure is kept, not raised."
  [rec event]
  (try (journal! rec event)
       (catch #?(:clj Throwable :cljs :default) t (swap! rec assoc :journal-error t))))

;; ---------------------------------------------------------------------------
;; Registration

(defn- check-forkable! [sys sid]
  (when-not (or (yp/supports-snapshot-overlay? sys) (yp/supports-checkpoint-overlay? sys))
    (throw (refusal ::unsupported-system
                    "register!: the system supports neither snapshot nor checkpoint overlays" {:sid sid}))))

(defn- check-record-open! [rec op]
  (when (and rec (not= :open (:status @rec)))
    (throw (refusal ::fork-not-open (str op ": the fork's settlement is not open")
                    {:fork/id (:fork/id @rec) :status (:status @rec)}))))

(defn- holder-for-write!
  "`w`'s own holder, minted when `w` has none; refused in an unmanaged world."
  [w op]
  (or (own-holder w)
      (locking holder-lock
        (or (own-holder w)
            (if (inherited-holder w)
              (throw (refusal ::unmanaged-world (str op ": a world the layer did not make (F10)") {}))
              (let [hk (mint-holder! w nil nil nil)]
                (v2/swap-world! w assoc ::holder hk)
                hk))))))

(defn register!
  "Registers `sys` in world `w` and returns its id (default
   `(yp/system-id sys)`). `w` holds the canonical handle; in a fork it is a
   child-only system, adopted by the parent on merge. `:policy` overrides
   per-system settlement hooks (`:conflicts`, `:diff`, `:merge`, `:cleanup`,
   each called with a map, §2.6); `:meta` is the registrant's plain data
   (`:merge-rank` orders merges). Refused in a body, in an unmanaged world,
   in a fork whose settlement is not `:open`, for an id `w` already has and
   for a system without owned snapshot or checkpoint overlays."
  [w sys {:keys [id policy meta]}]
  (host-only! "register!")
  (let [sid (or id (yp/system-id sys))
        _ (check-forkable! sys sid)
        hk (holder-for-write! w "register!")
        e (entry hk)]
    ;; admission and the reservation of the id are one step under the
    ;; record's serialization point (review 6): a settlement claim either
    ;; sees the system or refuses it
    (locking claim-lock
      (check-record-open! (:record @e) "register!")
      (when (contains? (:systems @e) sid)
        (throw (refusal ::already-registered "register!: the world already has this system" {:sid sid})))
      (swap! e #(-> % (assoc-in [:systems sid] {:base nil :meta meta}) (assoc-in [:handles sid] sys)))
      (if policy (swap! policies assoc [hk sid] policy) (swap! policies dissoc [hk sid])))
    (try (v2/swap-world! w assoc-in [::systems sid] {:base nil :meta meta})
         (catch #?(:clj Throwable :cljs :default) t
           (locking claim-lock
             (swap! e #(-> % (update :systems dissoc sid) (update :handles dissoc sid)))
             (swap! policies dissoc [hk sid]))
           (throw t)))
    sid))

(defn unregister!
  "Drops the registration of `sid` in `w`, the world that registered it: its
   record and handle go, the store's lifetime stays the caller's (L6).
   Refused for a system `w` inherited and in a fork whose settlement is not
   `:open`. True when it was registered."
  [w sid]
  (host-only! "unregister!")
  (let [hk (own-holder w)
        e (entry hk)]
    (when e
      (when (locking claim-lock
              (check-record-open! (:record @e) "unregister!")
              (when-let [s (get-in @e [:systems sid])]
                (when (:base s)
                  (throw (refusal ::inherited-system "unregister!: the system is inherited from the parent" {:sid sid})))
                (swap! e #(-> % (update :systems dissoc sid) (update :handles dissoc sid)))
                (swap! policies dissoc [hk sid])
                true))
        (v2/swap-world! w update ::systems dissoc sid)
        true))))

(defn systems
  "{sid meta} of the systems world `w` has: its own and those it inherits
   from its parent (for an unmanaged world, as at its fork)."
  [w]
  (let [m (if-let [e (entry (own-holder w))]
            (:systems @e)
            (get (try (v2/world-state w)
                      (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) e
                        (if (released-ex? e) nil (throw e))))
                 ::systems))]
    (into {} (map (fn [[k v]] [k (:meta v)])) m)))

;; ---------------------------------------------------------------------------
;; Queries

(defn fork-of
  "The layer `Fork` of world `w`, or nil when `w` is not one (or its record
   settled and its world completed)."
  [w]
  (when-let [e (entry (own-holder w))]
    (let [{:keys [fork-id record]} @e]
      (when fork-id (->Fork fork-id w record)))))

(defn fork?
  "Whether `w` is a fork the layer made (F8: a transient fork)."
  [w]
  (some? (fork-of w)))

(defn managed-ancestor
  "The nearest world, `w` included, the layer made or registered in, or nil
   (F10)."
  [w]
  (if (own-holder w)
    w
    (let [anc (entry-world (entry (inherited-holder w)))]
      (when (and anc (v2/descendant? w anc)) anc))))

(defn status
  "The settlement state of `fork`: `:status`, `:phase`, `:operation`,
   `:plan`, `:done`, `:cleaned`, `:owner`, `:leaves`, `:last-error`,
   `:hook-status`, `:hook-error`, `:cleanup` and the rest of the record's
   data."
  [fork]
  (let [r @(:record fork)]
    (assoc (record-data r) :hook-error (:hook-error r))))

;; ---------------------------------------------------------------------------
;; Settlement records: claims and transitions

(defn- unsettled-children [r]
  (keep #(get @settlements %) (:children r)))

(defn- claim-refusal
  "Why `op` cannot claim record `r` (nil when it can)."
  [r op opts]
  (let [id (:fork/id r)
        st (:status r)
        internal? (::internal opts)
        merging? (or (= :merge op) (and (= :recover op) (= :merge (:operation r))))
        allowed (case op
                  (:merge :transfer :partition) #{:open :transferred}
                  :discard #{:open :transferred :incomplete}
                  :recover #{:incomplete})]
    (cond
      (= :settling st)
      (refusal ::settling "another settlement holds the fork" {:fork/id id :operation (:operation r)})
      (= :partitioned st)
      (refusal ::partitioned "the fork is partitioned: settle its leaves" {:fork/id id :leaves (:leaves r)})
      (#{:merged :discarded} st)
      (refusal ::settled "the fork is settled" {:fork/id id :status st})
      (not (contains? allowed st))
      (refusal ::fork-not-open (str (name op) ": the fork's settlement is not open") {:fork/id id :status st})
      (and (#{:transferred :incomplete} st) (some? (:owner r)) (not internal?) (not= (:owner opts) (:owner r)))
      (refusal ::not-owner "the fork was transferred: its owner settles it" {:fork/id id :owner (:owner r)})
      (and merging? (or (::parent-ended r) (not (parent-live? r))))
      (refusal ::parent-ended "the parent's runtime ended: the fork cannot merge (F4)" {:fork/id id})
      (and merging? (some-> (entry (:parent r)) deref :record deref :status (not= :open)))
      (refusal ::parent-not-open "the parent's settlement is not open (F4)" {:fork/id id})
      (and (#{:merge :transfer :partition} op) (seq (unsettled-children r)))
      (refusal ::open-children "the fork has unsettled forks: settle them first (F4)"
               {:fork/id id :children (mapv #(:fork/id @%) (unsettled-children r))})
      (and (= :discard op) (not internal?) (some #(= :settling (:status @%)) (unsettled-children r)))
      (refusal ::children-settling "a fork of this fork is settling" {:fork/id id})
      (and (#{:transfer :partition} op) (not (some-> (entry (:child r)) entry-world v2/complete?)))
      (refusal ::runtime-live (str (name op) ": the fork's runtime has not ended") {:fork/id id}))))

(defn- claim!
  "Moves `rec` to `:settling` for `op`, or throws the refusal. Returns the
   record before the claim."
  [rec op opts]
  (locking claim-lock
    (let [r @rec]
      (when-let [ex (claim-refusal r op opts)] (throw ex))
      (reset! rec (-> r
                      (assoc :status :settling
                             :operation (if (= :recover op) (:operation r) op)
                             :phase :claimed
                             ::prior (select-keys r [:status :operation :phase]))
                      (dissoc :last-error :stop-report)))
      r)))

(defn- let-go!
  "Ends a claim with `changes` (a non-terminal status). A parent that ended
   meanwhile discards the fork now, unless the claim released was that
   discard itself (an `:incomplete` discard waits for `recover!` or
   `discard!`, it does not reschedule itself)."
  [rec changes]
  (let [ended? (locking claim-lock
                 (swap! rec #(-> % (merge changes) (dissoc ::prior)))
                 (and (::parent-ended @rec)
                      (not= :discard (:operation @rec))
                      (contains? #{:open :transferred :incomplete} (:status @rec))))]
    (when ended? (run-later! #(discard-internal! rec (::parent-ended @rec))))))

(defn- prior-status [r] (get-in r [::prior :status] :open))

(defn- leaf-settled! [rec]
  (when-let [pid (:partition-of @rec)]
    (when-let [prec (get @settlements pid)]
      (when (and (= :partitioned (:status @prec)) (not-any? unsettled? (:leaves @prec)))
        (swap! settlements dissoc pid)
        (journal-quietly! prec :leaves-settled)
        (maybe-drop-holder! (:child @prec))
        (leaf-settled! prec)))))

(defn- terminal!
  "Fixes the outcome `st`: the record leaves the registry and its parent's
   `:children` (review 10), is journaled, and its holder may go."
  [rec st]
  (locking claim-lock
    (swap! rec #(-> % (assoc :status st :phase nil) (dissoc ::prior)))
    (swap! settlements dissoc (:fork/id @rec))
    (when-let [p (get @settlements (:parent-fork @rec))]
      (swap! p update :children disj (:fork/id @rec))))
  (journal-quietly! rec st)
  (leaf-settled! rec)
  (maybe-drop-holder! (:child @rec)))

(defn- run-hook!
  "Runs the record's pending post-commit hooks in order, each once; a throw
   marks `:hook-status :failed` (the outcome stands) and `recover!` reruns
   the hooks that did not complete."
  [rec]
  (loop []
    (if-let [h (first (::hooks @rec))]
      (when (try (h)
                 (swap! rec update ::hooks (comp vec rest))
                 true
                 (catch #?(:clj Throwable :cljs :default) t
                   (swap! rec assoc :hook-status :failed :hook-error t)
                   false))
        (recur))
      (when (#{:pending :failed} (:hook-status @rec))
        (swap! rec #(-> % (assoc :hook-status :completed) (dissoc :hook-error)))))))

(defn- arm-hooks!
  "Queues the hooks of a settlement: `(hook payload)` when given, then the
   record's standing `:on-settled` with `{:fork/id :status :reason}` (P2:
   the owner of a transferred or partitioned record hears of every terminal
   outcome, the layer's own discards included)."
  [rec hook payload st]
  (let [r @rec
        settled (::on-settled r)
        note (cond-> {:fork/id (:fork/id r) :status st :reason (when (= :discarded st) (:reason r))}
               (:partition-of r) (assoc :partition-of (:partition-of r) :leaf (:leaf r)))
        hs (cond-> []
             hook (conj #(hook payload))
             settled (conj #(settled note)))]
    (when (seq hs)
      (swap! rec assoc ::hooks hs :hook-status :pending :hook-error nil))))

#?(:clj
   (do
     ;; ------------------------------------------------------------------------
     ;; Resolution

     (declare resolve-system!)

     (defn- unknown-system [sid]
       (refusal ::unknown-system "the world has no such system" {:sid sid}))

     (defn- open-overlay [ph base]
       (if-let [cp (:checkpoint base)]
         (yp/overlay-at-checkpoint ph cp {:sync? true :mode :frozen})
         (yp/overlay-at ph (:snapshot base) {:sync? true})))

     (defn- branch!
       "The first resolution of an inherited system in a fork: an owned
        overlay at the recorded base, over the immediate parent's handle (F4).
        Single-flight per holder and system."
       [hk sid]
       (let [e (entry hk)
             p (promise)
             [old _] (swap-vals! e (fn [m] (if (or (get-in m [:handles sid]) (get-in m [:pending sid]))
                                             m
                                             (assoc-in m [:pending sid] p))))]
         (cond
           (get-in old [:handles sid]) (get-in old [:handles sid])
           (get-in old [:pending sid]) (let [[h t] @(get-in old [:pending sid])] (if t (throw t) h))
           :else
           (try
             (let [{:keys [record parent systems]} @e
                   base (get-in systems [sid :base])]
               (check-record-open! record "system")
               (when-not (entry parent)
                 (throw (refusal ::parent-ended "system: the parent's holder is gone" {:sid sid})))
               (let [ph (resolve-system! parent sid)
                     ov (open-overlay ph base)
                     h (ovl/overlay-system ov)
                     ;; the settlement claim serializes with this install: a
                     ;; resolution that lost the race (the fork was claimed or
                     ;; settled meanwhile) discards the overlay it opened, so
                     ;; no branch escapes settlement (review 2)
                     installed? (locking claim-lock
                                  (when (and (identical? e (entry hk))
                                             (or (nil? record) (= :open (:status @record))))
                                    (swap! e #(-> % (assoc-in [:handles sid] h) (assoc-in [:overlays sid] ov)
                                                  (update :pending dissoc sid)))
                                    true))]
                 (when-not installed?
                   (try (yp/discard! ov) (catch Throwable _ nil))
                   (throw (refusal ::fork-not-open "system: the fork was claimed or settled while branching"
                                   {:sid sid})))
                 (when record
                   (try (journal! record :branched)
                        (catch Throwable t
                          (swap! e #(-> % (update :handles dissoc sid) (update :overlays dissoc sid)))
                          (try (yp/discard! ov) (catch Throwable _ nil))
                          (throw t))))
                 (deliver p [h nil])
                 h))
             (catch Throwable t
               (swap! e update :pending dissoc sid)
               (deliver p [nil t])
               (throw t))))))

     (defn- resolve-system! [hk sid]
       (let [e (entry hk)
             m (some-> e deref)]
         (or (get-in m [:handles sid])
             (let [s (get-in m [:systems sid])]
               (if (and s (:base s)) (branch! hk sid) (throw (unknown-system sid)))))))

     (defn system
       "The handle world `w` uses for system `sid`. In a fork the first call
        branches the store at the base recorded at the fork (an owned overlay
        over the immediate parent's handle, which branches the parent first if
        it has not); later calls return the same handle. Refused in an
        unmanaged world (F10), in a body or under a world's gate (B7), and for
        an unbranched system of a fork whose settlement is not `:open`."
       [w sid]
       (host-only! "system")
       (if-let [hk (own-holder w)]
         (if (entry hk)
           (resolve-system! hk sid)
           (throw (refusal ::fork-not-open "system: the fork is settled and its world complete" {:sid sid})))
         (if (inherited-holder w)
           (throw (refusal ::unmanaged-world "system: a world the layer did not make resolves no store for writing (F10)"
                           {:sid sid}))
           (throw (unknown-system sid)))))

     (defn- as-of-base
       "A read-only view of `sid` at `base`, through the nearest holder from
        `hk` up that has a handle of it."
       [hk sid base]
       (when (:checkpoint base)
         (throw (refusal ::no-view "view: an unbranched checkpoint base has no read-only view" {:sid sid})))
       (loop [k hk n 0]
         (let [m (some-> (entry k) deref)]
           (cond
             (or (nil? m) (> n 10000)) (throw (unknown-system sid))
             (get-in m [:handles sid]) (yp/as-of (get-in m [:handles sid]) (:snapshot base))
             :else (recur (:parent m) (inc n))))))

     (defn view
       "A read-only view of system `sid` in world `w` that never branches: `w`'s
        handle when it has one, else the store at `w`'s recorded base (`as-of`).
        An unmanaged world reads its nearest managed ancestor's store at the
        base that ancestor recorded (F10); it is refused (`::no-frozen-base`)
        when that ancestor registered the system itself, and a world with no
        managed ancestor reads none."
       [w sid]
       (host-only! "view")
       (if-let [hk (own-holder w)]
         (let [m @(entry hk)]
           (or (get-in m [:handles sid])
               (if-let [s (get-in m [:systems sid])]
                 (as-of-base hk sid (:base s))
                 (throw (unknown-system sid)))))
         (let [ihk (inherited-holder w)
               anc (entry-world (entry ihk))]
           (when-not (and anc (v2/descendant? w anc))
             (throw (refusal ::no-managed-ancestor "view: the world has no managed ancestor (F10)" {:sid sid})))
           (let [s (get-in (v2/world-state w) [::systems sid])]
             (cond
               (nil? s) (throw (unknown-system sid))
               (:base s) (as-of-base ihk sid (:base s))
               ;; the ancestor registered the system: there is no frozen
               ;; base, and its moving head is never read (F10, review 9)
               :else (throw (refusal ::no-frozen-base
                                     "view: the managed ancestor recorded no base for this system (F10)"
                                     {:sid sid})))))))

     (defn snapshot-ids
       "{sid snapshot-id} of world `w`: a branched or registered system's head,
        else its recorded base (the snapshot id, or the checkpoint origin): the
        fork's state token."
       [w]
       (host-only! "snapshot-ids")
       (let [token (fn [handles sid base]
                     (if-let [h (get handles sid)]
                       (some-> (yp/snapshot-id h) str)
                       (or (:snapshot base) (:checkpoint base))))]
         (if-let [e (entry (own-holder w))]
           (let [{:keys [systems handles]} @e]
             (into {} (map (fn [[sid {:keys [base]}]] [sid (token handles sid base)])) systems))
           (into {} (map (fn [[sid {:keys [base]}]] [sid (token {} sid base)]))
                 (get (v2/world-state w) ::systems)))))

     ;; ------------------------------------------------------------------------
     ;; Forks

     (defn- base-of [pe sid]
       (if-let [h (get-in pe [:handles sid])]
         {:snapshot (str (yp/snapshot-id h))}
         (get-in pe [:systems sid :base])))

     (defn- check-base! [sid base]
       (let [s (:snapshot base) cp (:checkpoint base)]
         (when-not (and (map? base)
                        (if cp
                          (and (nil? s) (yp/checkpoint-origin? cp))
                          (or (uuid? s) (and (string? s) (seq s)))))
           (throw (refusal ::invalid-base "fork!: a base is {:snapshot id} or {:checkpoint origin}"
                           {:sid sid :base base})))))

     (defn fork!
       "A host fork of `parent` with the layer's record (F1): the engine fork is
        uncounted and owned by `:owner`'s root scope (default `parent`), so the
        owner's close joins it. Each system of `parent` gets a base, from
        `:bases` (`{sid {:snapshot id}}` or `{sid {:checkpoint origin}}`), else
        the parent's handle's snapshot id, else the parent's own base; nothing
        branches now. `:meta` is the caller's data, `:journal` is called with
        the record's data at creation and at every change of status, plan,
        done set and branches (F6a), and `:on-discard` runs when the layer
        discards the fork by itself (its parent's world ended, or a discard of
        its parent cascaded). Refused in an unmanaged world and when `parent`
        is a fork whose settlement is not `:open`."
       [parent {:keys [owner bases meta journal on-discard]}]
       (host-only! "fork!")
       (let [phk (holder-for-write! parent "fork!")
             pe (entry phk)
             prec (:record @pe)]
         (check-record-open! prec "fork!")
         (doseq [[sid b] bases]
           (when-not (contains? (:systems @pe) sid) (throw (unknown-system sid)))
           (check-base! sid b))
         (let [child (v2/fork! parent (if owner {:owner owner} {}))
               id (random-uuid)
               rec (atom {:fork/id id :parent phk :parent-fork (:fork-id @pe) :status :open
                          :parent-world-id (v2/world-id parent) :child-world-id (v2/world-id child)
                          :plan nil :done #{} :cleaned #{} :children #{} :owner nil :meta meta
                          ::journal journal ::on-discard on-discard})
               chk (volatile! nil)]
           (try
             (let [pm @pe
                   syss (into {} (map (fn [[sid {m :meta}]]
                                        [sid {:base (or (get bases sid) (base-of pm sid)) :meta m}]))
                              (:systems pm))
                   hk (mint-holder! child id phk rec)]
               (vreset! chk hk)
               (swap! rec assoc :child hk)
               (v2/swap-world! child #(-> % (assoc ::holder hk) (assoc ::systems syss)))
               (swap! (entry hk) assoc :systems syss)
               (locking claim-lock
                 (when prec
                   (check-record-open! prec "fork!")
                   (swap! prec update :children conj id))
                 (swap! settlements assoc id rec))
               (journal! rec :created)
               (->Fork id child rec))
             (catch Throwable t
               (locking claim-lock
                 (swap! settlements dissoc id)
                 (when prec (swap! prec update :children disj id)))
               (try (v2/release-world! child) (catch Throwable _ nil))
               (when @chk (drop-holder! @chk))
               (throw t))))))

     ;; ------------------------------------------------------------------------
     ;; Diff and conflicts

     (defn- branched [r ce]
       (filter #(get-in ce [:overlays %]) (sort-by str (scope r ce))))

     (defn- policy-ctx [r sid]
       (let [ce @(entry (:child r))
             ov (get-in ce [:overlays sid])]
         {:sid sid
          :parent (get-in (some-> (entry (:parent r)) deref) [:handles sid])
          :child (get-in ce [:handles sid])
          :overlay ov
          :base (get-in ce [:systems sid :base])
          :meta (get-in ce [:systems sid :meta])}))

     (defn- default-conflicts [{:keys [sid parent child]}]
       (if (nil? parent)
         []  ; an unbranched parent fork is still at its base
         (try (vec (yp/conflicts parent (str (yp/snapshot-id parent)) (str (yp/snapshot-id child))))
              (catch Throwable t [{:system sid :indeterminate? true :error (ex-message t)}]))))

     (defn- system-conflicts [r sid]
       (let [ctx (policy-ctx r sid)
             f (or (:conflicts (policy-of (:child r) sid)) default-conflicts)]
         (mapv #(assoc % :system sid) (f ctx))))

     (defn conflicts
       "The conflicts of `fork`'s branched systems (in its scope) against the
        parent's head, each tagged `:system`: the system's `:conflicts`
        policy, by default `yp/conflicts` of parent head and child head (a
        throwing detector is an indeterminate conflict). Host data only: also
        on a closed fork."
       [fork]
       (host-only! "conflicts")
       (let [r @(:record fork)
             ce @(entry (:child r))]
         (vec (mapcat #(system-conflicts r %) (branched r ce)))))

     (defn- default-diff [{:keys [child overlay]}]
       (yp/diff child (str (yp/base-ref overlay)) (str (yp/snapshot-id child))))

     (defn diff
       "{sid delta} of `fork`'s branched systems (in its scope): the system's
        `:diff` policy, by default `yp/diff` from the recorded base to the
        child's head (the fork's own changes). Host data only: also on a
        closed fork."
       [fork]
       (host-only! "diff")
       (let [r @(:record fork)
             ce @(entry (:child r))]
         (into {} (map (fn [sid]
                         [sid ((or (:diff (policy-of (:child r) sid)) default-diff) (policy-ctx r sid))]))
               (branched r ce))))

     ;; ------------------------------------------------------------------------
     ;; Settlement steps

     (defn- stuck? [rep]
       (or (= :stuck rep) (= :stuck (:status rep))))

     (defn- seal-live!
       "Seals `w` and returns true, or false when its runtime already ended
        (released or complete): nothing to stop, restart or close."
       [w]
       (if (v2/complete? w)
         false
         (try (v2/seal! w) true
              (catch clojure.lang.ExceptionInfo e (if (released-ex? e) false (throw e))))))

     (defn- refused-ex [rec reason cause data]
       (ex-info (str "settlement refused: " (name reason))
                (merge {:type ::refused :reason reason :fork/id (:fork/id @rec)} data)
                cause))

     (defn- reopen!
       "A refusal before any store changed: the fork goes back to its state
        before the claim, unsealed with its runtime restarted when it was live
        (F5). Returns the exception to throw."
       [rec child opts live? reason cause data]
       (let [restart-error (when live?
                             (try (v2/unseal! child)
                                  (when-let [f (:restart opts)] (f))
                                  nil
                                  (catch Throwable t t)))]
         (let-go! rec (cond-> {:status (prior-status @rec) :phase nil :plan nil :last-error cause}
                        restart-error (assoc :restart-error restart-error)))
         (journal-quietly! rec :refused)
         (refused-ex rec reason cause (cond-> data restart-error (assoc :restart-error restart-error)))))

     (defn- incomplete! [rec cause]
       (let-go! rec {:status :incomplete :last-error cause})
       (journal-quietly! rec :incomplete)
       (ex-info "settlement incomplete: some systems landed, recover! resumes it"
                {:type ::incomplete :fork/id (:fork/id @rec) :done (:done @rec)} cause))

     (defn- close!
       "Ends the fork's runtime: the caller's `:close`, by default release and
        a join bounded by `:deadline-ms`. Returns the report (nil when it
        completed in time)."
       [child opts]
       (try
         (if-let [f (:close opts)]
           (f)
           (do (v2/release-world! child)
               (when (= ::timeout (v2/await-complete child (:deadline-ms opts default-deadline-ms) ::timeout))
                 :timeout)))
         (catch Throwable t {:error t})))

     (defn- cleanup-system! [r sid]
       (let [ce @(entry (:child r))
             {:keys [meta base]} (get-in ce [:systems sid])
             ov (get-in ce [:overlays sid])
             f (:cleanup (policy-of (:child r) sid))]
         (cond
           ov (if f (f {:sid sid :handle ov :meta meta}) (yp/discard! ov))
           (and (nil? base) f) (f {:sid sid :handle (get-in ce [:handles sid]) :meta meta}))
         (swap! (entry (:child r)) #(-> % (update :handles dissoc sid) (update :overlays dissoc sid)))))

     (defn- cleanup-plan
       "The systems a settlement cleans up: overlays in scope; for a discard
        also the child-only systems not adopted by a merge."
       [r ce]
       (vec (filter (fn [sid]
                      (or (get-in ce [:overlays sid])
                          (and (= :discard (:operation r)) (nil? (get-in ce [:systems sid :base]))
                               (not (contains? (:done r) sid)))))
                    (sort-by str (scope r ce)))))

     (defn- run-cleanup!
       "Cleans the record's systems not cleaned yet, journaling each. Returns
        nil, or the first failure."
       [rec]
       (let [r @rec
             e (entry (:child r))]
         (if-not e
           (let [t (refusal ::holder-gone "cleanup: the fork's holder is gone" {:fork/id (:fork/id r)})]
             (swap! rec assoc :cleanup :failed :last-error t)
             t)
           (let [todo (remove (:cleaned r) (cleanup-plan r @e))]
             (try
               (doseq [sid todo]
                 (cleanup-system! @rec sid)
                 (swap! rec update :cleaned conj sid)
                 (journal! rec :cleaned))
               (swap! rec assoc :cleanup :done)
               (swap! e update :cleanup-owed disj (:fork/id r))
               nil
               (catch Throwable t
                 ;; the holder keeps the overlays and policies the retry needs
                 (swap! e update :cleanup-owed (fnil conj #{}) (:fork/id r))
                 (swap! rec assoc :cleanup :failed :last-error t)
                 t))))))

     (defn- defer-cleanup!
       "Cleanup waits for the child world to complete (§2.5): it runs from
        `world-completed!`, or now if the world completed meanwhile."
       [rec]
       (let [r @rec
             e (entry (:child r))]
         (swap! rec assoc :cleanup :pending)
         (swap! e update :pending-cleanup conj rec)
         (when (or (:complete? @e) (some-> (entry-world e) v2/complete?))
           (finish-pending-cleanup! (:child r)))))

     (defn- finish-pending-cleanup! [hk]
       (when-let [e (entry hk)]
         (let [[old _] (swap-vals! e assoc :pending-cleanup [])]
           (doseq [rec (:pending-cleanup old)]
             (run-cleanup! rec)
             (journal-quietly! rec :cleanup)))))

     (defn- merge-plan [r ce]
       (let [rank (fn [sid] [(or (get-in ce [:systems sid :meta :merge-rank]) Long/MAX_VALUE) (str sid)])
             sids (scope r ce)]
         (vec (concat (sort-by rank (filter #(get-in ce [:overlays %]) sids))
                      (sort-by rank (filter #(nil? (get-in ce [:systems % :base])) sids))))))

     (defn- adopt!
       "A child-only system joins the parent world with its meta and policy."
       [r sid]
       (let [ce @(entry (:child r))
             phk (:parent r)
             pe (entry phk)
             pw (entry-world pe)
             {:keys [meta]} (get-in ce [:systems sid])
             h (get-in ce [:handles sid])]
         (when-not (and pe pw) (throw (refusal ::parent-ended "merge: the parent is gone" {:sid sid})))
         (when-not (= h (get-in @pe [:handles sid]))   ; idempotent on recover!
           (when (contains? (:systems @pe) sid)
             (throw (refusal ::already-registered "merge: the parent already has this system" {:sid sid})))
           (v2/swap-world! pw assoc-in [::systems sid] {:base nil :meta meta})
           (swap! pe #(-> % (assoc-in [:systems sid] {:base nil :meta meta}) (assoc-in [:handles sid] h)))
           (when-let [p (policy-of (:child r) sid)] (swap! policies assoc [phk sid] p)))))

     (defn- merge-system! [rec sid opts]
       (let [r @rec
             ce @(entry (:child r))
             meta (get-in ce [:systems sid :meta])]
         (when-let [guard (:guard opts)]
           (when (false? (guard sid meta))
             (throw (refusal ::guard-refused "merge: the guard refused" {:sid sid}))))
         (if-let [ov (get-in ce [:overlays sid])]
           (let [ph (resolve-system! (:parent r) sid)
                 f (:merge (policy-of (:child r) sid))]
             (if f
               (f (assoc (policy-ctx r sid) :parent ph))
               (yp/merge-down! ov (when (:force? opts) {:force? true}))))
           (adopt! r sid))
         (swap! rec update :done conj sid)
         (journal! rec :done)))

     (defn- merge-systems!
       "Plan order, from the first system not done; throws the first failure."
       [rec opts]
       (doseq [sid (:plan @rec)]
         (when-not (contains? (:done @rec) sid)
           (merge-system! rec sid opts))))

     (defn- payload [r op]
       (let [ce (some-> (entry (:child r)) deref)
             metas (fn [sids] (into {} (map (fn [sid] [sid (get-in ce [:systems sid :meta])])) sids))]
         (cond-> {:fork/id (:fork/id r) :meta (:meta r)}
           (:partition-of r) (assoc :partition-of (:partition-of r) :leaf (:leaf r))
           (= :merge op) (assoc :merged (vec (filter #(get-in ce [:systems % :base]) (:plan r)))
                                :adopted (metas (remove #(get-in ce [:systems % :base]) (:plan r))))
           (= :discard op) (assoc :dropped (metas (remove (:done r)
                                                          (filter #(or (get-in ce [:overlays %])
                                                                       (nil? (get-in ce [:systems % :base])))
                                                                  (scope r ce))))
                                  :reason (:reason r)))))

     (defn- finish!
       "Close (if the runtime is live), cleanup (now, or when the child world
        completes), the terminal status, then the hook (once)."
       [rec child opts live? st hook]
       (swap! rec assoc :phase :closing)
       (when live?
         (let [rep (close! child opts)]
           (when rep (swap! rec assoc :close-report rep))))
       (let [hook-payload (payload @rec (:operation @rec))]
         (if (v2/complete? child)
           (let [t (run-cleanup! rec)]
             (when (and t (= :discard (:operation @rec)))
               (throw (incomplete! rec t))))
           (defer-cleanup! rec))
         (arm-hooks! rec hook hook-payload st)
         (terminal! rec st)
         (run-hook! rec)
         (status {:record rec})))

     (defn- check-precheck! [rec opts]
       (let [r @rec
             ce @(entry (:child r))
             cs (when-not (:force? opts) (vec (mapcat #(system-conflicts r %) (branched r ce))))]
         (when (seq cs)
           (throw (refusal ::conflicts "merge: the fork conflicts with its parent" {:conflicts cs})))
         (when-let [f (:precheck opts)]
           (when (false? (f {:fork/id (:fork/id r) :meta (:meta r) :conflicts cs
                             :snapshot-ids (into {} (map (fn [sid]
                                                           [sid (if-let [h (get-in ce [:handles sid])]
                                                                  (some-> (yp/snapshot-id h) str)
                                                                  (get-in ce [:systems sid :base]))]))
                                                 (scope r ce))
                             :plan (merge-plan r ce)}))
             (throw (refusal ::precheck-refused "merge: the precheck refused" {}))))))

     (defn- run-merge! [fork opts]
       (let [rec (:record fork)
             child (:world fork)]
         (try (journal! rec :claimed)
              (catch Throwable t
                (let-go! rec {:status (prior-status @rec) :phase nil :last-error t})
                (throw t)))
         (let [live? (seal-live! child)]
           ;; 2. stop without release (F5)
           (swap! rec assoc :phase :stop)
           (when (and live? (:stop opts))
             (let [rep (try ((:stop opts)) (catch Throwable t {:status :stuck :error t}))]
               (when (stuck? rep)
                 (let [ex (refused-ex rec :stuck (:error rep) {:report rep})]
                   (let-go! rec {:status (prior-status @rec) :phase nil :stop-report rep :last-error ex})
                   (journal-quietly! rec :stuck)
                   (throw ex)))))
           ;; 3. precheck on the stopped fork
           (swap! rec assoc :phase :precheck)
           (try (check-precheck! rec opts)
                (catch Throwable t
                  (throw (reopen! rec child opts live? (or (some-> (ex-data t) :type name keyword) :precheck)
                                  t (select-keys (ex-data t) [:conflicts])))))
           ;; 4. the plan
           (try (swap! rec assoc :phase :mutating :plan (merge-plan @rec @(entry (:child @rec))))
                (journal! rec :plan)
                (catch Throwable t (throw (reopen! rec child opts live? :journal t {}))))
           ;; 5. per system, in plan order
           (try (merge-systems! rec opts)
                (catch Throwable t
                  (if (empty? (:done @rec))
                    (throw (reopen! rec child opts live? :merge t {}))
                    (throw (incomplete! rec t)))))
           ;; 6-9. close, cleanup, terminal, hook
           (finish! rec child opts live? :merged (:on-merge opts)))))

     (defn merge!
       "Merges `fork` into its immediate parent (F4/F5/F6): claim, seal and the
        caller's `:stop` (the runtime stops, the world stays), the precheck
        (per branched system its `:conflicts` policy unless `:force?`, then the
        caller's `:precheck` with a map of the fork's state), the journaled
        plan (branched systems, then child-only ones, each by `:merge-rank`
        meta then sid), per system the caller's `(guard sid meta)` and its
        merge (`:merge` policy or `yp/merge-down!` into the parent's handle;
        a child-only system is adopted), then the caller's `:close` (default:
        release and join within `:deadline-ms`), cleanup and `:merged`, and
        `(on-merge {:fork/id :meta :merged [sid] :adopted {sid meta}})` once.

        Refused (`::refused`, the record back to its state before) when the
        fork is not open to this caller (`:owner` for a transferred one), its
        parent is not live and open, it has unsettled forks, `:stop` reports
        `:stuck` (the fork stays sealed and stopped), or the precheck, a guard
        or the first system's merge refuses (the fork is unsealed and
        `:restart` called). A failure after a system landed leaves it
        `:incomplete` (`::incomplete`; `recover!` resumes). A hook failure
        keeps `:merged` with `:hook-status :failed`. Returns `status`."
       [fork opts]
       (host-only! "merge!")
       (let [rec (:record fork)]
         (if (= :merged (:status @rec))
           (status fork)
           (do (claim! rec :merge opts)
               (swap! rec assoc ::resume (select-keys opts [:guard :close :on-merge :deadline-ms :force?]))
               (run-merge! fork opts)))))

     (defn- discard-children! [rec]
       (doseq [c (unsettled-children @rec)]
         (try (parent-ended! c :parent-discarded)
              (catch Throwable _ nil))))

     (defn- run-discard! [fork opts]
       (let [rec (:record fork)
             child (:world fork)]
         (try (journal! rec :claimed)
              (catch Throwable t
                (let-go! rec {:status (prior-status @rec) :phase nil :last-error t})
                (throw t)))
         (discard-children! rec)
         (let [live? (not (or (v2/complete? child) (released? child)))]
           (swap! rec assoc :phase :mutating :reason (or (::reason opts) :discarded))
           (journal-quietly! rec :plan)
           (finish! rec child opts live? :discarded (or (:on-discard opts) (::on-discard @rec))))))

     (defn- discard-internal!
       "The layer's own discard (parent ended, cascade): no owner check, the
        default close, the hook given at fork or transfer time."
       [rec reason]
       (let [r @rec
             child (entry-world (entry (:child r)))
             opts {::internal true ::reason reason :on-discard (::on-discard r)}]
         (claim! rec :discard opts)
         (swap! rec assoc ::resume (select-keys opts [:on-discard]))
         (if child
           (run-discard! (->Fork (:fork/id r) child rec) opts)
           ;; the child world was collected: nothing runs, clean what is held
           (do (swap! rec assoc :phase :mutating :reason reason)
               (when-let [t (run-cleanup! rec)] (throw (incomplete! rec t)))
               (let [p (payload @rec :discard)]
                 (arm-hooks! rec (::on-discard r) p :discarded)
                 (terminal! rec :discarded))
               (run-hook! rec)))))

     (defn discard!
       "Discards `fork` (F3): its unsettled forks first, then the close (as for
        merge), the cleanup of its branched systems (`:cleanup` policy or
        `yp/discard!`) and of its child-only ones (their `:cleanup` policy),
        `:discarded` and `(on-discard {:fork/id :meta :dropped {sid meta}
        :reason r})` once. Also from `:incomplete` (what has not merged is
        dropped). A close that misses its deadline defers the cleanup to the
        child world's completion (`:cleanup :pending`). A transferred fork is
        discarded by its `:owner` only. Returns `status`."
       [fork opts]
       (host-only! "discard!")
       (let [rec (:record fork)]
         (if (= :discarded (:status @rec))
           (status fork)
           (do (claim! rec :discard opts)
               (swap! rec assoc ::resume (cond-> (select-keys opts [:close :deadline-ms])
                                           true (assoc :on-discard (or (:on-discard opts) (::on-discard @rec)))))
               (run-discard! fork opts)))))

     (defn- retry-claim!
       "Takes the record's retry claim for a failed hook or cleanup of a
        settled fork, under the record's serialization point (review 4): one
        retry at a time, by the owner of an owned record. Returns the record."
       [rec opts]
       (locking claim-lock
         (let [r @rec]
           (when (and (:owner r) (not= (:owner opts) (:owner r)))
             (throw (refusal ::not-owner "the fork was transferred: its owner settles it"
                             {:fork/id (:fork/id r) :owner (:owner r)})))
           (when (or (::retrying r) (= :settling (:status r)))
             (throw (refusal ::settling "another settlement or retry holds the fork" {:fork/id (:fork/id r)})))
           (swap! rec assoc ::retrying true)
           r)))

     (defn recover!
       "Resumes `fork`'s `:incomplete` settlement in this process: a merge from
        the first system not done (then close, cleanup, hook; refused like
        `merge!` when the parent's runtime ended or its settlement is not
        open), a discard's remaining cleanup; or reruns a failed hook or
        cleanup of a settled fork, one retry at a time. Every per-system step
        is idempotent (the adapter contract). An owned (transferred) record
        needs `{:owner owner}`. Returns `status`."
       ([fork] (recover! fork nil))
       ([fork opts]
        (host-only! "recover!")
        (let [rec (:record fork)
              child (:world fork)
              r @rec]
          (if (= :incomplete (:status r))
            (let [claimed (claim! rec :recover (select-keys opts [:owner]))
                  ropts (::resume claimed)]
              (swap! rec assoc :phase :mutating)
              (if (= :merge (:operation claimed))
                (do (try (merge-systems! rec ropts)
                         (catch Throwable t (throw (incomplete! rec t))))
                    (finish! rec child ropts (not (v2/complete? child)) :merged (:on-merge ropts)))
                (finish! rec child ropts false :discarded (:on-discard ropts))))
            (if (or (= :failed (:cleanup r)) (= :failed (:hook-status r)))
              (do (retry-claim! rec opts)
                  (try
                    (when (= :failed (:cleanup @rec))
                      (run-cleanup! rec)
                      (journal-quietly! rec :cleanup))
                    (when (= :failed (:hook-status @rec)) (run-hook! rec))
                    (finally (swap! rec dissoc ::retrying)))
                  (maybe-drop-holder! (:child r))
                  (status fork))
              (status fork))))))

     ;; ------------------------------------------------------------------------
     ;; Transfer and partition (F3; forks whose runtime ended)

     (defn transfer!
       "Moves the settlement authority of `fork`, whose runtime has ended, to
        `owner` (an opaque host value): the record becomes `:transferred`,
        and only `merge!`/`discard!`/`transfer!`/`partition!` passing
        `{:owner owner}` settle it from then on (`:owner` in `opts` names the
        current owner of an already transferred record). `:on-discard`
        replaces the hook the layer runs when it discards the fork itself, and
        `(on-settled {:fork/id :status :reason})` runs at its terminal outcome,
        whoever settles it (the parent-ended discard included). The caller
        persists the move itself (before the call, compensating in its own
        catch; the `:journal` hook sees `:transferred`). Repeating the
        transfer to the record's current owner returns at once. Refused
        unchanged when the fork is not open to this caller, its runtime is
        live, its parent's has ended, or it has unsettled forks. Returns
        `fork`."
       [fork owner {:keys [on-discard on-settled] :as opts}]
       (host-only! "transfer!")
       (when (nil? owner) (throw (refusal ::invalid-owner "transfer!: the owner cannot be nil" {})))
       (let [rec (:record fork)
             r @rec]
         (if (and (= :transferred (:status r)) (= owner (:owner r)))
           fork
           (do (claim! rec :transfer opts)
               (if-not (parent-live? @rec)
                 (let [ex (refused-ex rec :parent-ended nil {})]
                   (swap! rec assoc ::parent-ended :parent-ended)
                   (let-go! rec {:status (prior-status @rec) :phase nil})
                   (throw ex))
                 (do (let-go! rec (cond-> {:status :transferred :owner owner :phase nil :operation nil}
                                    on-discard (assoc ::on-discard on-discard)
                                    on-settled (assoc ::on-settled on-settled)))
                     (journal-quietly! rec :transferred)
                     fork))))))

     (defn leaf-id
       "The id of leaf `leaf-key` of a partition of the fork `fork-id`: the same
        for every call, so a caller can name a leaf before partitioning."
       [fork-id leaf-key]
       (java.util.UUID/nameUUIDFromBytes
        (.getBytes (pr-str [::leaf fork-id leaf-key]) java.nio.charset.StandardCharsets/UTF_8)))

     (defn- leaf-forks [fork rec]
       (into {} (map (fn [[k a]] [k (->Fork (:fork/id @a) (:world fork) a)])) (::leaf-records @rec)))

     (defn partition!
       "Splits the settlement of `fork`, whose runtime has ended, into leaves:
        `leaves` is `{leaf-key #{sid ...}}` with caller-chosen keys, disjoint
        and exhaustive over the fork's systems (its scope, for a leaf). Leaf
        `k` gets the id `(leaf-id (:id fork) k)`. Each leaf is a `Fork` of the
        same child world that settles once, merging or discarding its systems
        only, with the fork's status (`:open`, or `:transferred` and its
        owner); `:on-discard` and `:on-settled` are as for `transfer!` (each
        leaf inherits the fork's when not given). The fork becomes
        `:partitioned`, settled once every leaf is. Repeating the same split
        returns the same leaves (idempotent); a different one is refused.
        Refused unchanged as `transfer!`, and for a split that overlaps, omits
        or names unknown systems. Returns `{leaf-key Fork}`."
       [fork leaves {:keys [on-discard on-settled] :as opts}]
       (host-only! "partition!")
       (let [rec (:record fork)
             r @rec]
         (when (or (not (map? leaves)) (empty? leaves) (some #(or (not (set? %)) (empty? %)) (vals leaves)))
           (throw (refusal ::invalid-partition "partition!: leaves map keys to non-empty system sets" {})))
         (if (and (= :partitioned (:status r)) (= leaves (:leaf-spec r)))
           (if (and (:owner r) (not= (:owner opts) (:owner r)))
             (throw (refusal ::not-owner "the fork was transferred: its owner settles it" {:fork/id (:fork/id r)}))
             (leaf-forks fork rec))
           (let [all (scope r (some-> (entry (:child r)) deref))
                 named (apply concat (vals leaves))]
             (when (not= (count named) (count (set named)))
               (throw (refusal ::overlapping-partition "partition!: the leaves overlap"
                               {:systems (into #{} (keep (fn [[s n]] (when (> n 1) s))) (frequencies named))})))
             (when (not= (set named) all)
               (throw (refusal ::incomplete-partition "partition!: the leaves must cover the fork's systems exactly"
                               {:unknown (remove all named) :omitted (remove (set named) all)})))
             ;; the leaves inherit the record this call claimed (its status
             ;; and owner), not the one read before the claim (review 1)
             (let [claimed (claim! rec :partition opts)]
               (when-not (parent-live? @rec)
                 (let [ex (refused-ex rec :parent-ended nil {})]
                   (swap! rec assoc ::parent-ended :parent-ended)
                   (let-go! rec {:status (prior-status @rec) :phase nil})
                   (throw ex)))
               (let [made (into {} (map (fn [[k sids]]
                                          [k (atom {:fork/id (leaf-id (:fork/id claimed) k) :partition-of (:fork/id claimed)
                                                    :leaf k :systems sids
                                                    :parent (:parent claimed) :child (:child claimed)
                                                    :parent-fork (:parent-fork claimed)
                                                    :parent-world-id (:parent-world-id claimed)
                                                    :child-world-id (:child-world-id claimed)
                                                    :status (:status claimed) :owner (:owner claimed) :meta (:meta claimed)
                                                    :plan nil :done #{} :cleaned #{} :children #{}
                                                    ::journal (::journal claimed)
                                                    ::on-discard (or on-discard (::on-discard claimed))
                                                    ::on-settled (or on-settled (::on-settled claimed))})]))
                                leaves)
                     ;; publishing the leaves and resolving a parent end flagged
                     ;; during the claim are one transition (review 7)
                     ended (locking claim-lock
                             (let [ended (::parent-ended @rec)]
                               (doseq [[_ a] made]
                                 (when ended (swap! a assoc ::parent-ended ended))
                                 (swap! settlements assoc (:fork/id @a) a))
                               (swap! rec #(-> % (merge {:status :partitioned :phase nil :operation nil :leaf-spec leaves
                                                         :leaves (into #{} (map (comp :fork/id deref)) (vals made))
                                                         ::leaf-records made})
                                               (dissoc ::prior)))
                               ended))]
                 (journal-quietly! rec :partitioned)
                 (doseq [[_ a] made] (journal-quietly! a :created))
                 (when ended
                   (doseq [[_ a] made] (run-later! #(discard-internal! a ended))))
                 (leaf-forks fork rec)))))))))
