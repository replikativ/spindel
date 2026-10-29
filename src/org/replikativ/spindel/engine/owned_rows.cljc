(ns org.replikativ.spindel.engine.owned-rows
  "Internal owned row cells. Only the store mutates them, under its gate.
  Ordinary assoc/dissoc operations return immutable maps for stable planning.")

(def ^:private absent #?(:clj (Object.) :cljs (js-obj)))

(def layouts
  (into {}
        (map (fn [[table fields]]
               [table {:fields fields :positions (zipmap fields (range))}]))
        {:entities [:kind :origin :owner :creator :completed? :kept? :result
                    :tokens :key :order :dirty? :reference? :source-world]
         :runs [:spin :owner :pred :ancestors :status :creations :spawned :seq
                :anchor :retired? :origin :source-world]
         :obligations [:kind :debtor :creditor :standing? :cont :token :order
                       :origin :slot :filter :dormant? :timer-armed?]
         :scopes [:kind :parent :status :order]}))

(declare value lookup)

(deftype Row [owner layout #?(:clj ^objects data :cljs data)]
  #?@(:clj
      [clojure.lang.ILookup
       (valAt [this key] (lookup this key nil))
       (valAt [this key not-found] (lookup this key not-found))
       clojure.lang.IPersistentMap
       (assoc [this key val] (assoc (value this) key val))
       (assocEx [this key val]
                (if (contains? (value this) key)
                  (throw (ex-info "Key already present" {:key key}))
                  (assoc (value this) key val)))
       (without [this key] (dissoc (value this) key))
       (containsKey [this key] (not (identical? absent (lookup this key absent))))
       (entryAt [this key]
                (let [v (lookup this key absent)]
                  (when-not (identical? absent v) (clojure.lang.MapEntry/create key v))))
       (count [this] (count (value this)))
       (cons [this entry] (conj (value this) entry))
       (empty [_] {})
       (equiv [this other] (= (value this) other))
       (seq [this] (seq (value this)))
       (iterator [this] (.iterator ^java.lang.Iterable (value this)))
       clojure.lang.MapEquivalence
       clojure.lang.IHashEq
       (hasheq [this] (hash (value this)))
       java.util.Map
       (size [this] (count (value this)))
       (isEmpty [this] (empty? (value this)))
       (containsValue [this val] (.containsValue ^java.util.Map (value this) val))
       (get [this key] (lookup this key nil))
       (keySet [this] (.keySet ^java.util.Map (value this)))
       (values [this] (.values ^java.util.Map (value this)))
       (entrySet [this] (.entrySet ^java.util.Map (value this)))
       (put [_ _ _] (throw (UnsupportedOperationException. "Use the owned store")))
       (remove [_ _] (throw (UnsupportedOperationException. "Use the owned store")))
       (putAll [_ _] (throw (UnsupportedOperationException. "Use the owned store")))
       (clear [_] (throw (UnsupportedOperationException. "Use the owned store")))
       Object
       (equals [this other] (.equals ^Object (value this) other))
       (hashCode [this] (.hashCode ^Object (value this)))
       (toString [this] (str (value this)))]
      :cljs
      [ILookup
       (-lookup [this key] (lookup this key nil))
       (-lookup [this key not-found] (lookup this key not-found))
       IAssociative
       (-contains-key? [this key] (not (identical? absent (lookup this key absent))))
       (-assoc [this key val] (assoc (value this) key val))
       IMap
       (-dissoc [this key] (dissoc (value this) key))
       ICounted
       (-count [this] (count (value this)))
       ICollection
       (-conj [this entry] (conj (value this) entry))
       IEmptyableCollection
       (-empty [_] {})
       IEquiv
       (-equiv [this other] (= (value this) other))
       IHash
       (-hash [this] (hash (value this)))
       ISeqable
       (-seq [this] (seq (value this)))]))

(defn row? [x] (instance? Row x))

(defn owner [^Row row] (.-owner row))

(defn lookup [^Row row key not-found]
  (let [layout (.-layout row)
        index (get (:positions layout) key)
        ^objects data (.-data row)]
    (if (some? index)
      (let [v (aget data index)] (if (identical? absent v) not-found v))
      (get (aget data (count (:fields layout))) key not-found))))

(defn value
  "Materialize an immutable semantic row. Non-cell values pass through."
  [row]
  (if-not (row? row) row
          (let [^Row row row
                fields (:fields (.-layout row))
                ^objects data (.-data row)]
            (loop [i 0 result (transient (aget data (count fields)))]
              (if (= i (count fields)) (persistent! result)
                  (let [v (aget data i)]
                    (recur (inc i) (if (identical? absent v) result (assoc! result (nth fields i) v)))))))))

(defn create [owner layout values]
  (let [fields (:fields layout)
        data #?(:clj (object-array (inc (count fields))) :cljs (make-array (inc (count fields))))
        positions (:positions layout)]
    (dotimes [i (count fields)] (aset data i absent))
    (aset data (count fields)
          (reduce-kv (fn [extra key val]
                       (if-let [i (get positions key)]
                         (do (aset data i val) extra)
                         (assoc extra key val))) {} values))
    (Row. owner layout data)))

(defn copy [^Row row token]
  (let [^objects data (.-data row)]
    (Row. token (.-layout row) (aclone data))))

(defn set-field!
  "The store supplies its current edit token after recording the old value."
  [^Row row token key val present?]
  (when-not (identical? token (.-owner row))
    (throw (ex-info "Row belongs to another edit owner" {})))
  (let [layout (.-layout row)
        ^objects data (.-data row)
        index (get (:positions layout) key)]
    (if (some? index)
      (aset data index (if present? val absent))
      (let [i (count (:fields layout))]
        (aset data i (if present? (assoc (aget data i) key val) (dissoc (aget data i) key))))))
  row)
