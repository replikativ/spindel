(ns org.replikativ.spindel.v2.dom.mounted-model-test
  "The mounted model on engine v2 (phase-d design §3.3): the committed tree
   is the mounted model, and unmount is the difference between two
   successive committed trees (`commit/retire-dead!`). The caches live in a
   per-mount store passed explicitly, not in world state, so two mounts
   share nothing. A KeyedFragment carries its `:keys`; the commit reads the
   order from them, with no fallback to the items' `:key` attributes.

   Ported from dom/mounted_model_test (old engine), with the store in place
   of the execution context."
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.dom.commit :as commit]
            [org.replikativ.spindel.v2.dom.cache :as cache]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.dom.core :as dom-core]))

(defn- dom-text [s] (dom-core/make-text-vnode s))

(defn- vn [tag addr & slot-values]
  (let [slots (mapv cache/make-slot slot-values)]
    {:tag tag :addr addr :attrs {}
     :slots slots :children (cache/flatten-slots slots)}))

(defn- li [k]
  {:tag :li :addr (keyword (str "el-li-" k)) :key k :attrs {}
   :slots [] :children []})

(defn- fragment
  "A hand-built KeyedFragment at `addr` with its `:keys`."
  [addr ks]
  (assoc (frag/keyed-fragment (mapv li ks) nil) :addr addr :keys (vec ks)))

(deftest tree-addrs-is-the-mounted-model
  (testing "element addrs + fragment call sites + keyed items; :nil slots
            contribute nothing"
    (let [tree (vn :div :el-root
                   (vn :span :el-child)
                   nil                      ; a :nil conditional slot
                   (fragment :el-frag ["a" "b"]))]
      (is (= #{:el-root :el-child :el-frag :el-li-a :el-li-b}
             (commit/tree-addrs tree))))))

(deftest retire-dead-is-the-tree-difference
  (testing "prev-minus-new addresses lose caches and registry entries;
            addresses in both trees are untouched"
    (let [store (cache/new-store)
          {:keys [discharge elements]} (disch/make-mock-discharge)
          prev (vn :div :el-root (vn :span :el-keep) (vn :ul :el-gone))
          new' (vn :div :el-root (vn :span :el-keep) nil)]
      (doseq [a [:el-root :el-keep :el-gone]]
        (cache/set-slot-cache! store a [])
        (disch/set-element! discharge a (keyword (str "node-" (name a)))))
      (commit/retire-dead! discharge store prev new')
      (is (nil? (cache/get-slot-cache store :el-gone)) "dead addr evicted")
      (is (nil? (get @elements :el-gone)) "dead addr out of the registry")
      (is (some? (cache/get-slot-cache store :el-keep)) "surviving addr spared")
      (is (= :node-el-keep (get @elements :el-keep))
          "surviving registry entry spared")
      (is (some? (cache/get-slot-cache store :el-root))))))

(deftest reclaimed-address-is-never-dead
  (testing "an address present in both trees, even under a different
            parent, is not in the difference, so nothing evicts it"
    (let [store (cache/new-store)
          {:keys [discharge]} (disch/make-mock-discharge)
          prev (vn :div :el-root (vn :section :el-old-parent (vn :p :el-moved)))
          new' (vn :div :el-root (vn :article :el-new-parent (vn :p :el-moved)))]
      (cache/set-slot-cache! store :el-moved [])
      (cache/set-slot-cache! store :el-old-parent [])
      (commit/retire-dead! discharge store prev new')
      (is (some? (cache/get-slot-cache store :el-moved))
          "re-claimed under a new parent, still mounted, never retired")
      (is (nil? (cache/get-slot-cache store :el-old-parent))
          "the parent that actually left is retired"))))

(deftest fragment-call-site-retires-with-its-fragment-and-not-before
  (testing "a live fragment survives a dead parent; a dead fragment's keyed
            cache retires with no cascade"
    (let [store (cache/new-store)
          {:keys [discharge]} (disch/make-mock-discharge)
          f (fragment :el-frag ["a"])
          with-frag (vn :div :el-root (vn :section :el-sec f))
          churned (vn :div :el-root (vn :article :el-sec2 f))
          without (vn :div :el-root nil)]
      (cache/set-keyed-cache! store :el-frag {:by-key {} :order ["a"]})
      (commit/retire-dead! discharge store with-frag churned)
      (is (some? (cache/get-keyed-cache store :el-frag))
          "live fragment survives its dead parent")
      (commit/retire-dead! discharge store churned without)
      (is (nil? (cache/get-keyed-cache store :el-frag))
          "dead fragment's keyed cache retired"))))

(deftest violation-collection-round-trips
  (testing "record -> drain non-empty -> drain empty"
    (disch/collect-violations!)
    (disch/record-violation! ::probe {:x 1})
    (let [vs (disch/drain-violations!)]
      (is (= 1 (count vs)))
      (is (= ::probe (:kind (first vs)))))
    (is (empty? (disch/drain-violations!)))))

;; ---------------------------------------------------------------------------
;; The store (§3.3)

(defn- mount!
  "Mounts `vnode` on a fresh mock and store: render-initial! and seed."
  [vnode]
  (let [store (cache/new-store)
        {:keys [discharge] :as m} (disch/make-mock-discharge)]
    (binding [disch/*rendered-addrs* (atom {})]
      (disch/render-initial! discharge vnode))
    (commit/seed-subtree-caches! store vnode)
    (assoc m :store store)))

(deftest the-store-holds-the-committed-caches
  (let [tree (vn :div :el-root (vn :span :el-a) (fragment :el-frag ["x" "y"]))
        {:keys [store]} (mount! tree)]
    (testing "seeding writes slots, attrs and keyed entries into the store"
      (is (= [:single :keyed] (mapv :type (cache/get-slot-cache store :el-root))))
      (is (= {} (cache/get-attr-cache store :el-a)))
      (is (= {:order ["x" "y"] :by-key {"x" (li "x") "y" (li "y")}}
             (cache/get-keyed-cache store :el-frag))
          "a keyed entry is the order and the vnodes by key, nothing else"))
    (testing "reset empties the store"
      (cache/reset-store! store)
      (is (cache/store-empty? store)))))

(deftest two-stores-share-nothing
  (let [tree (vn :div :el-root (vn :span :el-a))
        a (mount! tree)
        b (mount! tree)
        tree' (vn :div :el-root nil)]
    (commit/commit-update! (:discharge a) (:store a) tree tree')
    (is (nil? (cache/get-slot-cache (:store a) :el-a)) "a retired :el-a")
    (is (some? (cache/get-slot-cache (:store b) :el-a)) "b still has it")
    (is (= [:nil] (mapv :type (cache/get-slot-cache (:store a) :el-root))))
    (is (= [:single] (mapv :type (cache/get-slot-cache (:store b) :el-root))))))

(deftest a-fragment-orders-by-its-keys
  (let [tree (vn :div :el-root (fragment :el-frag ["a" "b" "c"]))
        {:keys [discharge store log]} (mount! tree)
        tree' (vn :div :el-root (fragment :el-frag ["c" "a" "b"]))]
    (reset! log [])
    (commit/commit-update! discharge store tree tree')
    (is (= ["c" "a" "b"] (:order (cache/get-keyed-cache store :el-frag))))
    (is (seq (filter #(= :move-child (:op %)) @log)) "the reorder moves a child")
    (is (empty? (filter #(#{:create-element :remove-child} (:op %)) @log))
        "no item is recreated")))

(deftest a-fragment-without-keys-is-refused
  (testing "no fallback to the items' :key attributes"
    (let [bare (assoc (frag/keyed-fragment [(li "a")] nil) :addr :el-frag)
          tree (vn :div :el-root bare)]
      (is (thrown-with-msg? #?(:clj Exception :cljs :default) #":keys"
                            (commit/seed-subtree-caches! (cache/new-store) tree))))))

(deftest an-unbound-address-is-reported
  (testing "a commit of an address with no element records a violation"
    (disch/collect-violations!)
    (let [store (cache/new-store)
          {:keys [discharge]} (disch/make-mock-discharge)]
      (commit/commit-update! discharge store nil (vn :div :el-unbound))
      (is (= [::commit/commit-unbound-addr] (mapv :kind (disch/drain-violations!)))))))

(deftest log-throttles-are-capped
  (testing "a once-per-address throttle logs each address once, and at most
            its cap of addresses"
    (let [logged (atom #{})
          n (+ 8 disch/log-throttle-cap)
          firsts (count (filter #(disch/first-log? logged %) (range n)))]
      (is (= disch/log-throttle-cap firsts))
      (is (not (disch/first-log? logged 0)) "an address is logged once")
      (is (= disch/log-throttle-cap (count @logged))))))

#?(:clj
   (deftest a-wide-element-commits-in-linear-steps
     ;; sol's confirmation pass, P2: each slot's physical base is carried
     ;; through the walk, not recomputed from every preceding slot. The steps
     ;; are counted as slot flattenings, not timed.
     (let [n 10000
           tree (apply vn :div :el-wide (map #(dom-text (str %)) (range n)))
           {:keys [discharge store]} (mount! tree)
           steps (atom 0)
           flatten-slot @#'cache/flatten-slot]
       (with-redefs-fn {#'cache/flatten-slot (fn [slot] (swap! steps inc) (flatten-slot slot))}
         #(commit/commit-update! discharge store tree tree))
       (is (<= @steps (* 4 n)) (str @steps " slot flattenings for " n " slots")))))
