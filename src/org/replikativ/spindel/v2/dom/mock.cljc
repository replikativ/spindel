(ns org.replikativ.spindel.v2.dom.mock
  "A mock discharge for the v2 DOM tests (phase-d design §5.4, addendum
  §3.8.2, §3.8.12): the operation log and element registry of
  `dom.discharge`'s MockDischarge, plus a child-list model of the tree (so
  tests can read the DOM and ask whether an element is attached), element
  attrs and properties, a queue of deferred work that a test runs with
  `run-deferred!`, and failure injection.

  Elements are gensym ids; the container is any value passed to `render!`
  (tests use :container)."
  (:require [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.v2.dom.render :as render]))

(defn- insert-at [v i x]
  (let [i (min (max 0 i) (count v))]
    (into (conj (subvec v 0 i) x) (subvec v i))))

(defn- remove-at [v i]
  (if (< -1 i (count v)) (into (subvec v 0 i) (subvec v (inc i))) v))

(defn- op!
  "Logs `op`, unless the failure predicate matches it: then throws."
  [{:keys [log fail]} op]
  (when-let [f @fail]
    (when (f op) (throw (ex-info "mock discharge failure" {:op op}))))
  (swap! log conj op))

(defn- detach!
  "Removes child `c` from the parent model."
  [{:keys [parent]} c]
  (swap! parent dissoc c))

(defn- set-kids! [{:keys [kids parent]} p v]
  (swap! kids assoc p v)
  (swap! parent (fn [m] (reduce #(assoc %1 %2 p) m v))))

(defrecord MockDischarge [log elements kids parent nodes attrs props deferred fail]
  disch/PDischarge
  (create-element! [this vnode]
    (let [id (gensym "el-")]
      (op! this {:op :create-element :tag (:tag vnode) :addr (:addr vnode) :id id})
      (swap! nodes assoc id {:tag (:tag vnode) :addr (:addr vnode)})
      id))
  (create-text! [this text]
    (let [id (gensym "text-")]
      (op! this {:op :create-text :text text :id id})
      (swap! nodes assoc id {:text text})
      id))
  (set-attribute! [this el k v]
    (op! this {:op :set-attr :el el :attr k :value v})
    (swap! attrs assoc-in [el k] v)
    (case k
      :value (swap! props assoc-in [el :value] (str v))
      :checked (swap! props assoc-in [el :checked] (boolean v))
      nil))
  (remove-attribute! [this el k]
    (op! this {:op :remove-attr :el el :attr k})
    (swap! attrs update el dissoc k)
    (case k
      :value (swap! props assoc-in [el :value] "")
      :checked (swap! props assoc-in [el :checked] false)
      nil))
  (append-child! [this p c]
    (op! this {:op :append-child :parent p :child c :child-addr (:addr (get @nodes c)) :child-tag (:tag (get @nodes c))})
    (set-kids! this p (conj (get @kids p []) c)))
  (insert-child! [this p c i]
    (op! this {:op :insert-child :parent p :child c :index i :child-addr (:addr (get @nodes c)) :child-tag (:tag (get @nodes c))})
    (set-kids! this p (insert-at (get @kids p []) i c)))
  (remove-child! [this p i]
    (op! this {:op :remove-child :parent p :index i})
    (let [v (get @kids p [])]
      (when-let [c (get v i)] (detach! this c))
      (set-kids! this p (remove-at v i))))
  (replace-child! [this p c i]
    (op! this {:op :replace-child :parent p :child c :index i :child-addr (:addr (get @nodes c)) :child-tag (:tag (get @nodes c))})
    (let [v (get @kids p [])]
      (if (< -1 i (count v))
        (do (detach! this (get v i)) (set-kids! this p (assoc v i c)))
        (set-kids! this p (conj v c)))))
  (move-child! [this p from to]
    (op! this {:op :move-child :parent p :from from :to to})
    (let [v (get @kids p [])
          c (get v from)]
      (when c (set-kids! this p (insert-at (remove-at v from) to c)))))
  (child-index-of [_ p c]
    (first (keep-indexed (fn [i x] (when (= x c) i)) (get @kids p []))))
  (set-text-content! [this el text]
    (op! this {:op :set-text :el el :text text})
    (swap! nodes assoc-in [el :text] text))
  (get-element [_ addr] (get @elements addr))
  (set-element! [_ addr el] (swap! elements assoc addr el))
  (remove-element! [_ addr] (swap! elements dissoc addr))
  (remove-children-range! [this p start n] (disch/default-remove-children-range! this p start n))
  (insert-children! [this p cs start] (disch/default-insert-children! this p cs start))

  render/PMountHost
  (defer! [_ f] (swap! deferred conj f) nil)
  (clear-container! [this container]
    (op! this {:op :clear-container :container container})
    (doseq [c (get @kids container)] (detach! this c))
    (swap! kids assoc container [])
    nil)
  (dom-prop [_ el k] (get-in @props [el k]))
  (set-dom-prop! [this el k v]
    (op! this {:op :set-prop :el el :prop k :value v})
    (swap! props assoc-in [el k] v)
    nil))

(defn make-mock
  "A mock discharge. Returns {:discharge d :log atom :elements atom}."
  []
  (let [d (->MockDischarge (atom []) (atom {}) (atom {}) (atom {}) (atom {}) (atom {}) (atom {})
                           (atom []) (atom nil))]
    {:discharge d :log (:log d) :elements (:elements d)}))

(defn run-deferred!
  "Runs the deferred work queued so far, oldest first (work it queues runs
   too). Returns how many ran; throws after 100000 (work that never ends)."
  [d]
  (loop [n 0]
    (let [[old _] (swap-vals! (:deferred d) (fn [q] (if (seq q) (subvec q 1) q)))]
      (if-let [f (first old)]
        (if (< n 100000)
          (do (f) (recur (inc n)))
          (throw (ex-info "run-deferred!: deferred work does not end" {:runs n})))
        n))))

(defn deferred-count [d] (count @(:deferred d)))

(defn fail-when!
  "Makes every later operation matching `pred` (a fn of the operation map:
   :op, :tag, :child-addr, ...) throw; nil turns it off."
  [d pred]
  (reset! (:fail d) pred)
  nil)

(defn children [d parent] (get @(:kids d) parent []))

(defn attached?
  "Whether `el` is in the tree under `container`."
  [d container el]
  (loop [x el]
    (cond (= x container) true
          (nil? x) false
          :else (recur (get @(:parent d) x)))))

(defn attrs-of [d el] (get @(:attrs d) el))

(defn prop [d el k] (get-in @(:props d) [el k]))

(defn set-prop!
  "Sets a property as the user would (typing): not a discharge write."
  [d el k v]
  (swap! (:props d) assoc-in [el k] v)
  nil)

(defn dom
  "The children of `parent` as data: an element is [tag attrs & children]
   (attrs without fns), a text node its string."
  [d parent]
  (mapv (fn [c]
          (let [{:keys [tag text]} (get @(:nodes d) c)]
            (if tag
              (into [tag (into {} (remove (comp fn? val)) (attrs-of d c))] (dom d c))
              text)))
        (children d parent)))
