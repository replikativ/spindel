(ns org.replikativ.spindel.v2.dom.cache
  "The commit caches of one mount (phase-d design §3.3).

  A store is a volatile of `{:slots {} :attrs {} :keyed {}}`, one per
  mount, passed explicitly: nothing of it is world state, and no build
  reads it. Per element address it holds the committed slot vector and
  attrs; per fragment address the committed keyed entry `{:order :by-key}`.

  The rest are pure functions of the commit walk: slot classification,
  attr and slot reconciliation, and the slot-to-child index adjustment.

  Slot types:
  - :nil    - the slot is empty (a conditional returned nil)
  - :single - one vnode
  - :keyed  - a KeyedFragment"
  (:require [clojure.set]
            [org.replikativ.spindel.dom.core :as core]
            [org.replikativ.spindel.dom.fragment :as frag]))

;; ---------------------------------------------------------------------------
;; The store

(def ^:private empty-store {:slots {} :attrs {} :keyed {}})

(defn new-store "A new, empty store." [] (volatile! empty-store))

(defn reset-store! "Empties `store`." [store] (vreset! store empty-store) nil)

(defn store-empty? [store] (= empty-store @store))

(defn get-slot-cache [store addr] (get-in @store [:slots addr]))
(defn set-slot-cache! [store addr slots] (vswap! store assoc-in [:slots addr] slots) nil)

(defn get-attr-cache [store addr] (get-in @store [:attrs addr]))
(defn set-attr-cache! [store addr attrs] (vswap! store assoc-in [:attrs addr] attrs) nil)

(defn get-keyed-cache
  "The committed keyed entry `{:order :by-key}` of fragment address `addr`."
  [store addr]
  (get-in @store [:keyed addr]))

(defn set-keyed-cache! [store addr entry] (vswap! store assoc-in [:keyed addr] entry) nil)

(defn evict!
  "Drops every cache of `addr`."
  [store addr]
  (vswap! store (fn [s] (-> s
                            (update :slots dissoc addr)
                            (update :attrs dissoc addr)
                            (update :keyed dissoc addr))))
  nil)

;; ---------------------------------------------------------------------------
;; Slots

(defn make-slot
  "A slot entry {:type :nil|:single|:keyed :value child} for a child."
  [child]
  {:type (cond
           (nil? child) :nil
           (frag/keyed-fragment? child) :keyed
           :else :single)
   :value child})

(defn flatten-slot
  "The child vnodes of a slot."
  [slot]
  (case (:type slot)
    :nil []
    :single [(:value slot)]
    :keyed (frag/fragment-items (:value slot))
    []))

(defn flatten-slots
  "The children vector of a vector of slots."
  [slots]
  (into [] (mapcat flatten-slot) slots))

;; ---------------------------------------------------------------------------
;; Reconciliation

(defn vnode-value-equal?
  "Whether two vnodes of plain values render the same, as the same DOM
   nodes: text by content, elements by tag, key, address (their DOM
   identity), attrs and children, recursively. Lifecycle fns (`:ref`,
   `:on-commit`, ...) are not compared: surviving elements get their own
   effect comparison."
  [a b]
  (cond
    (and (nil? a) (nil? b)) true
    (or (nil? a) (nil? b)) false
    (and (core/text-node? a) (core/text-node? b)) (= (:content a) (:content b))
    (and (:tag a) (:tag b))
    (and (= (:tag a) (:tag b))
         (= (:key a) (:key b))
         (= (:addr a) (:addr b))
         (= (:attrs a) (:attrs b))
         (let [ca (:children a) cb (:children b)]
           (and (= (count ca) (count cb))
                (every? true? (map vnode-value-equal? ca cb)))))
    :else false))

(defn reconcile-attrs
  "Attr deltas from `prev-attrs` to `new-attrs`, or nil for none."
  [prev-attrs new-attrs]
  (let [prev-attrs (or prev-attrs {})
        new-attrs (or new-attrs {})
        prev-keys (set (keys prev-attrs))
        new-keys (set (keys new-attrs))
        deltas (concat
                (map (fn [k] {:delta :add :path [k] :value (get new-attrs k)})
                     (clojure.set/difference new-keys prev-keys))
                (map (fn [k] {:delta :remove :path [k] :old-value (get prev-attrs k)})
                     (clojure.set/difference prev-keys new-keys))
                (keep (fn [k]
                        (when (not= (get prev-attrs k) (get new-attrs k))
                          {:delta :update :path [k]
                           :old-value (get prev-attrs k) :value (get new-attrs k)}))
                      (clojure.set/intersection prev-keys new-keys)))]
    (when (seq deltas) (vec deltas))))

(defn- same-single?
  "Whether two :single slot values are the same child: text by content,
   elements by tag and address (a keyed element's address embeds its key),
   anything else by value."
  [prev new]
  (cond
    (and (core/text-node? prev) (core/text-node? new))
    (= (:content prev) (:content new))

    (and (core/vnode? prev) (core/vnode? new))
    (and (= (:tag prev) (:tag new))
         (if (and (:addr prev) (:addr new))
           (= (:addr prev) (:addr new))
           (= (:key prev) (:key new))))

    :else (= prev new)))

(defn- reconcile-slot
  "{:slot new-slot :delta delta-or-nil} for slot `i` from `prev-slot` to
   child `new`. A [:keyed :keyed] pair of one fragment (one address) yields
   no delta: the commit walk diffs it against the keyed cache itself; a pair
   of two fragments is a :replace-fragment."
  [i prev-slot new]
  (let [new-slot (make-slot new)
        prev (:value prev-slot)]
    {:slot new-slot
     :delta (case [(or (:type prev-slot) :nil) (:type new-slot)]
              [:nil :nil] nil
              [:nil :single] {:delta :add :path [i] :value new}
              [:nil :keyed] {:delta :add-fragment :path [i] :value new}
              [:single :nil] {:delta :remove :path [i] :old-value prev}
              [:single :single] (when-not (same-single? prev new)
                                  {:delta :update :path [i] :old-value prev :value new})
              [:single :keyed] {:delta :replace-with-fragment :path [i] :old-value prev :value new}
              [:keyed :nil] {:delta :remove-fragment :path [i] :old-value prev}
              [:keyed :single] {:delta :replace-fragment-with-single :path [i] :old-value prev :value new}
              ;; another fragment in this slot (one moved across slots) has
              ;; nothing in common with the previous one: replaced
              [:keyed :keyed] (when (not= (:addr prev) (:addr new))
                                {:delta :replace-fragment :path [i] :old-value prev :value new}))}))

(defn reconcile-children
  "{:slots new-slots :deltas slot-deltas} from the committed `prev-slots`
   to the children `new-children` (one per slot)."
  [prev-slots new-children]
  (let [prev-slots (or prev-slots [])
        results (mapv (fn [i] (reconcile-slot i (get prev-slots i) (get new-children i)))
                      (range (max (count prev-slots) (count new-children))))]
    {:slots (mapv :slot results)
     :deltas (into [] (keep :delta) results)}))
