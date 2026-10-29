(ns org.replikativ.spindel.owned-pages-spike
  "Mutable-page ownership probe. This checks the physical fork boundary,
  not the lifetime transition algebra."
  (:import [java.util HashMap]))

(def ^:private page-count 64)

(defn new-world []
  (let [owner (Object.)]
    (object-array [owner (object-array [owner (object-array page-count)])])))

(defn- page-index [id]
  (bit-and (hash id) (dec page-count)))

(defn read-row [^objects world id]
  (let [^objects root (aget world 1)
        ^objects pages (aget root 1)
        ^objects page (aget pages (page-index id))]
    (when page
      (let [^HashMap rows (aget page 1)]
        (.get rows id)))))

(defn put-row!
  "Mutate only pages owned by this world epoch. Caller holds the store gate."
  [^objects world id value]
  (let [owner (aget world 0)
        ^objects root (aget world 1)
        ^objects root (if (identical? owner (aget root 0))
                        root
                        (let [^objects old-pages (aget root 1)
                              root (object-array [owner (aclone old-pages)])]
                          (aset world 1 root)
                          root))
        ^objects pages (aget root 1)
        index (page-index id)
        ^objects old (aget pages index)
        ^objects page (if (and old (identical? owner (aget old 0)))
                        old
                        (let [^HashMap old-rows (when old (aget old 1))
                              rows (if old (HashMap. old-rows) (HashMap.))
                              page (object-array [owner rows])]
                          (aset pages index page)
                          page))]
    (let [^HashMap rows (aget page 1)]
      (.put rows id value))
    world))

(defn frozen-fork!
  "Share the root in O(1), then give both writers fresh ownership tokens.
  Caller holds the store gate."
  [^objects parent]
  (let [root (aget parent 1)
        child (object-array [(Object.) root])]
    (aset parent 0 (Object.))
    child))

(defn verify!
  "Check in-place reuse before sharing and isolation on both fork branches."
  []
  (let [parent (new-world)
        _ (put-row! parent :a 1)
        before (aget ^objects parent 1)
        _ (put-row! parent :a 2)
        same (aget ^objects parent 1)
        child (frozen-fork! parent)]
    (assert (identical? before same))
    (assert (identical? same (aget ^objects child 1)))
    (put-row! parent :a 3)
    (assert (= 3 (read-row parent :a)))
    (assert (= 2 (read-row child :a)))
    (put-row! child :a 4)
    (assert (= 3 (read-row parent :a)))
    (assert (= 4 (read-row child :a)))
    (let [parent-root (aget ^objects parent 1)]
      (put-row! parent :a 5)
      (assert (identical? parent-root (aget ^objects parent 1))))
    true))
