(ns org.replikativ.spindel.engine.native-cells-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [async deftest is testing]])
            [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.addressing :as addr]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]])
  #?(:clj (:import [java.lang.ref Reference WeakReference])))

(defn runtime [] (c/runtime {:cps-exit? true :audit? true}))

(defn observe! [rt spin outcomes]
  (binding [ec/*execution-context* rt]
    (c/observe! rt spin #(swap! outcomes conj [:ok %]) #(swap! outcomes conj [:error %]))))

(deftest public-atoms-use-native-world-storage
  (let [rt (runtime) calls (atom [])]
    (binding [ec/*execution-context* rt]
      (let [a (ratom/atom nil :meta {:name :native})
            alias (ratom/->RuntimeAtom (ratom/atom-id a))
            b (ratom/atom [])]
        (is (nil? @a))
        (is (= {:name :native} (meta alias)))
        (add-watch a :watch
                   (fn [k ref old new]
                     (swap! calls conj [k (identical? ref alias) old new
                                        (identical? (rtp/world-identity rt)
                                                    (rtp/world-identity (ec/current-execution-context)))])
                     (swap! b conj new)))
        (is (= false (reset! alias false)))
        (is (true? (rtp/cas-runtime-cell! rt a (ratom/atom-id a) false [:value])))
        (is (false? (rtp/cas-runtime-cell! rt a (ratom/atom-id a) (with-meta [:value] {:identity :other}) :wrong)))
        (is (= [:value :more] (swap! alias conj :more)))
        (is (= [false [:value] [:value :more]] @b))
        (is (= [[:watch true nil false true]
                [:watch false false [:value] true]
                [:watch true [:value] [:value :more] true]] @calls))
        (remove-watch alias :watch)
        (reset! a :quiet)
        (is (= 3 (count @calls)))
        (is (= :atom (get-in (c/snapshot rt) [:entities (ratom/atom-id a) :kind])))
        (doseq [path [[:atoms (ratom/atom-id a) :lifetime/owner]
                      [:listeners (ratom/atom-id a) :forged]]]
          (is (thrown? #?(:clj Exception :cljs js/Error)
                       (rtp/swap-state! rt path (constantly :forged)))))))
    (verify-boundaries! rt)))

(deftest decorated-context-allocates-in-the-active-run
  (let [rt (runtime) cell (atom nil) outcomes (atom []) gate (c/ticket :body)
        spin (c/cspin rt :owner
                      (binding [ec/*execution-context* (assoc rt :bindings {:scope :lexical})]
                        (reset! cell (ratom/atom 10))
                        (c/park gate)))]
    (observe! rt spin outcomes)
    (let [id (ratom/atom-id @cell)]
      (is (= [:owner 1] (get-in (c/snapshot rt) [:entities id :owner])))
      (c/cancel-spin! rt spin)
      (is (nil? (get-in (c/snapshot rt) [:entities id])))
      (binding [ec/*execution-context* rt]
        (is (false? (rtp/runtime-cell-present? rt id)))
        (is (thrown? #?(:clj Exception :cljs js/Error) (reset! @cell :resurrected)))))
    (verify-boundaries! rt)))

(deftest public-cell-and-metadata-survive-protected-cleanup
  (let [rt (runtime) other (runtime) cell (atom nil) callback (atom nil)
        trace (atom []) calls (atom []) outcomes (atom []) gate (c/ticket :body)
        spin (c/cspin rt :owner
                      (binding [ec/*execution-context* (assoc rt :bindings {:scope :lexical})]
                        (let [a (ratom/atom 41 :meta {:resource :owned})]
                          (reset! cell a)
                          (add-watch a :watch (fn [_ _ old new] (swap! calls conj [old new])))
                          (try (c/park gate)
                               (finally
                                 (swap! trace conj [@a (meta a)])
                                 (c/await-finalization (fn [r _] (reset! callback r)))
                                 (swap! a inc)
                                 (swap! trace conj [@a (meta a)
                                                    (get-in (ec/current-execution-context) [:bindings :scope])]))))))]
    (observe! rt spin outcomes)
    (let [id (ratom/atom-id @cell)]
      (c/cancel-spin! rt spin)
      (is (= [[41 {:resource :owned}]] @trace))
      (is (= [:error] (mapv first @outcomes)))
      (is (nil? (get-in (c/snapshot rt) [:entities id])))
      (is (false? (c/join-ready? rt [:owner 1])))
      ;; The callback must restore its lexical bindings on the native runner's
      ;; selected world, regardless of the caller's ambient context.
      (binding [ec/*execution-context* other]
        (@callback :done)
        (is (identical? other (ec/current-execution-context))))
      (is (= [[41 {:resource :owned}] [42 {:resource :owned} :lexical]] @trace))
      (is (empty? @calls) "Retained cleanup writes emit no ordinary watches")
      (is (c/join-ready? rt [:owner 1]))
      (is (empty? (:cleanup-cells (c/snapshot rt))))
      (binding [ec/*execution-context* rt]
        (is (false? (rtp/runtime-cell-present? rt id)))))
    (verify-boundaries! rt)))

(deftest explicit-cell-target-does-not-borrow-the-callers-owner
  (let [caller (runtime) target (runtime) result (atom nil) outcomes (atom [])
        spin (c/cspin caller :caller
                      (let [receipt (rtp/allocate-runtime-cell! target :target {:meta {:target true}})]
                        (reset! result receipt)
                        (:id receipt)))]
    (observe! caller spin outcomes)
    (let [{:keys [id anchor]} @result]
      (is (some? anchor))
      (is (= [:root c/w] (get-in (c/snapshot target) [:entities id :owner])))
      (is (nil? (get-in (c/snapshot caller) [:entities id])))
      (binding [ec/*execution-context* target]
        (let [a (ratom/->RuntimeAtom id)]
          (is (= :target @a))
          (is (= {:target true} (meta a))))))
    (verify-boundaries! caller)
    (verify-boundaries! target)))

#?(:clj
   (deftest retirement-during-a-host-transform-cannot-recreate-the-cell
     (let [rt (runtime) cell (atom nil) entered (promise) continue (promise)
           outcomes (atom []) gate (c/ticket :body)
           spin (c/cspin rt :owner
                         (binding [ec/*execution-context* rt]
                           (reset! cell (ratom/atom 0))
                           (c/park gate)))]
       (observe! rt spin outcomes)
       (let [a @cell id (ratom/atom-id a)
             writer (future
                      (binding [ec/*execution-context* rt]
                        (try
                          (swap! a (fn [value]
                                     (deliver entered true)
                                     (when-not (= true (deref continue 5000 ::timeout))
                                       (throw (ex-info "Transform test timeout" {})))
                                     (inc value)))
                          :committed
                          (catch Exception _ :refused))))]
         (try
           (is (= true (deref entered 5000 ::timeout)))
           (c/cancel-spin! rt spin)
           (is (nil? (get-in (c/snapshot rt) [:entities id])))
           (finally (deliver continue true)))
         (is (= :refused (deref writer 5000 ::timeout)))
         (is (nil? (get-in (c/snapshot rt) [:entities id]))))
       (verify-boundaries! rt))))

#?(:clj
   (do
     (defn- dropped-native-cell [rt]
       (binding [ec/*execution-context* rt]
         (let [a (ratom/atom :discarded)]
           (add-watch a :unused (fn [_ _ _ _] nil))
           [(ratom/atom-id a) (WeakReference. a)])))

     (deftest host-collection-reaps-an-idle-cell-from-a-live-native-world
       (let [rt (runtime) [id weak] (dropped-native-cell rt)]
         (try
           (is (loop [remaining 200]
                 (cond
                   (and (nil? (.get ^WeakReference weak))
                        (nil? (get-in (c/snapshot rt) [:entities id]))) true
                   (zero? remaining) false
                   :else (do (System/gc) (Thread/sleep 10) (recur (dec remaining)))))
               "Actual all-alias collection releases ordinary native storage")
           (is (empty? (:source-gc (c/snapshot rt))))
           (verify-boundaries! rt)
           (finally (Reference/reachabilityFence rt)))))))

(deftest copied-continuation-selects-the-fork-cell-and-fork-local-watches
  (let [parent (c/runtime {:audit? true}) gate (c/ticket :body)
        cell (atom nil) calls (atom []) outcomes (atom [])
        spin (c/cspin parent :owner
                      (binding [ec/*execution-context* (assoc parent :bindings {:scope :lexical})]
                        (let [a (ratom/atom 0)]
                          (reset! cell a)
                          (add-watch a :parent (fn [_ _ old new] (swap! calls conj [old new])))
                          (c/park gate)
                          (swap! a inc)
                          ;; Keep the copied owner wanted while inspecting its
                          ;; private payload; completed idle scopes may reclaim
                          ;; their cells and following reads resume at parent.
                          (c/park (c/ticket :after-write))
                          [@a (get-in (ec/current-execution-context) [:bindings :scope])])))]
    (observe! parent spin outcomes)
    (let [child (c/fork-parked! parent [:w 1])
          token (c/pending-ticket child gate)
          id (ratom/atom-id @cell)]
      (binding [ec/*execution-context* child]
        (c/resume-ticket! child token :resume))
      (binding [ec/*execution-context* parent]
        (is (= 0 @@cell) "A fork resume cannot write the parent's cell"))
      (binding [ec/*execution-context* child]
        (is (= 1 @@cell))
        (is (empty? (rtp/runtime-cell-watches child id))))
      (is (empty? @calls) "A fork never fires its parent's ordinary watches")
      (verify-boundaries! parent))))

(deftest local-watches-do-not-freeze-a-borrowed-following-value
  (let [parent (c/runtime {:audit? true})
        a (binding [ec/*execution-context* parent] (ratom/atom 0))
        child (c/fork-parked! parent [:w 1]) id (ratom/atom-id a) calls (atom [])]
    (binding [ec/*execution-context* child]
      (remove-watch a :absent)
      (add-watch a :child (fn [_ _ old new] (swap! calls conj [old new])))
      (is (nil? (get-in (c/snapshot child) [:entities id]))))
    (binding [ec/*execution-context* parent] (reset! a 1))
    (binding [ec/*execution-context* child]
      (is (= 1 @a))
      (remove-watch a :absent)
      (is (nil? (get-in (c/snapshot child) [:entities id]))))
    (binding [ec/*execution-context* parent] (reset! a 2))
    (binding [ec/*execution-context* child]
      (is (= 2 @a))
      (reset! a 3))
    (is (= [[2 3]] @calls) "The fork retains its local watch through payload COW")
    (binding [ec/*execution-context* parent] (reset! a 4))
    (binding [ec/*execution-context* child] (is (= 3 @a)))
    (verify-boundaries! parent)))

(deftest native-runner-selects-its-world-without-a-user-binding
  (let [rt (runtime) other (runtime) cell (atom nil) outcomes (atom [])
        spin (c/cspin rt :owner
                      (reset! cell (ratom/atom :native))
                      (c/park (c/ticket :body)))]
    (binding [ec/*execution-context* other]
      (c/observe! rt spin #(swap! outcomes conj [:ok %]) #(swap! outcomes conj [:error %]))
      (is (identical? other (ec/current-execution-context))))
    (let [id (ratom/atom-id @cell)]
      (is (= [:owner 1] (get-in (c/snapshot rt) [:entities id :owner])))
      (is (nil? (get-in (c/snapshot other) [:entities id]))))
    (verify-boundaries! rt)))

(deftest macro-introduced-scope-restores-on-the-selected-fork
  (let [parent (c/runtime {:audit? true}) cell (atom nil) seen (atom [])
        gate (c/ticket :body) outcomes (atom [])
        spin (c/cspin parent :owner
                      (let [a (ratom/atom 0)]
                        (reset! cell a)
                        (addr/with-key :inside
                          (c/park gate)
                          (swap! a inc)
                          (swap! seen conj [(addr/current-key ec/*execution-context*)
                                            (ec/same-world? parent ec/*execution-context*)]))
                        (swap! seen conj [(addr/current-key ec/*execution-context*)])
                        (c/park (c/ticket :after-scope))))]
    (observe! parent spin outcomes)
    (let [child (c/fork-parked! parent [:w 1])]
      (c/resume-ticket! child (c/pending-ticket child gate) :ready)
      (is (= [[:inside false] [nil]] @seen))
      (binding [ec/*execution-context* parent] (is (= 0 @@cell)))
      (binding [ec/*execution-context* child] (is (= 1 @@cell)))
      (verify-boundaries! parent))))

#?(:clj
   (do
     (defn- start-raw-id-fork-transform []
       (let [parent (c/runtime {:audit? true})
             a (binding [ec/*execution-context* parent] (ratom/atom 0))
             id (ratom/atom-id a)
             child (c/fork-parked! parent [:w 1])
             entered (promise) continue (promise)
             writer (future
                      (binding [ec/*execution-context* child]
                        (rtp/swap-runtime-cell!
                         child nil id
                         (fn [value]
                           (deliver entered true)
                           (when-not (= true (deref continue 15000 ::timeout))
                             (throw (ex-info "Fork transform test timeout" {})))
                           (inc value)) [])))]
         ;; No wrapper or anchor escapes. The typed operation retains only its
         ;; ordinary storage claim; that claim must survive actual host GC.
         {:parent parent :child child :id id :weak (WeakReference. a)
          :entered entered :continue continue :writer writer}))

     (deftest following-cow-inherits-an-already-observed-host-collection-receipt
       (let [{:keys [parent child id weak entered continue writer]} (start-raw-id-fork-transform)]
         (try
           (is (= true (deref entered 5000 ::timeout)))
           (is (loop [remaining 200]
                 (cond
                   (and (nil? (.get ^WeakReference weak))
                        (get-in (c/snapshot parent) [:source-gc [c/w id id]])) true
                   (zero? remaining) false
                   :else (do (System/gc) (Thread/sleep 10) (recur (dec remaining)))))
               "Host collection is observed while the inherited transform is claimed")
           (finally (deliver continue true)))
         (is (= 1 (deref writer 15000 ::timeout)))
         (is (nil? (get-in (c/snapshot parent) [:entities id])))
         (is (nil? (get-in (c/snapshot child) [:entities id]))
             "COW after host collection cannot leave an uncollectable child copy")
         (is (empty? (:source-gc (c/snapshot parent))))
         (is (empty? (:source-gc (c/snapshot child))))
         (verify-boundaries! parent)
         (Reference/reachabilityFence parent)
         (Reference/reachabilityFence child)))))

#?(:clj
   (do
     (defn- start-owned-raw-id-transform []
       (let [parent (c/runtime {:audit? true}) info (atom nil)
             gate (c/ticket :body) outcomes (atom [])
             spin (c/cspin parent :owner
                           (let [a (ratom/atom 0)]
                             (reset! info {:id (ratom/atom-id a) :weak (WeakReference. a)}))
                           (c/park gate))]
         (observe! parent spin outcomes)
         (let [{:keys [id weak]} @info entered (promise) continue (promise)
               writer (future
                        (rtp/swap-runtime-cell!
                         parent nil id
                         (fn [value]
                           (deliver entered true)
                           (when-not (= true (deref continue 15000 ::timeout))
                             (throw (ex-info "Owned fork transform test timeout" {})))
                           (inc value)) []))]
           {:parent parent :spin spin :id id :weak weak
            :entered entered :continue continue :writer writer})))

     (deftest parked-fork-copies-inherit-an-existing-host-collection-receipt
       ;; These IDs exercise different JVM family-map traversal orders.
       (doseq [world [[:w 1] [:w 9] [:w 10]]]
         (let [{:keys [parent spin id weak entered continue writer]} (start-owned-raw-id-transform)
               child (atom nil)]
           (try
             (is (= true (deref entered 5000 ::timeout)))
             (is (loop [remaining 200]
                   (cond
                     (and (nil? (.get ^WeakReference weak))
                          (get-in (c/snapshot parent) [:source-gc [c/w id id]])) true
                     (zero? remaining) false
                     :else (do (System/gc) (Thread/sleep 10) (recur (dec remaining)))))
                 "A host receipt can precede a parked fork while a raw-ID operation is claimed")
             (reset! child (c/fork-parked! parent world))
             (finally (deliver continue true)))
           (is (= 1 (deref writer 15000 ::timeout)))
           (is (nil? (get-in (c/snapshot parent) [:entities id])))
           (is (nil? (get-in (c/snapshot @child) [:entities id])))
           (is (empty? (:source-gc (c/snapshot parent))))
           (is (empty? (:source-gc (c/snapshot @child))))
           (verify-boundaries! parent)
           (Reference/reachabilityFence spin)
           (Reference/reachabilityFence parent)
           (Reference/reachabilityFence @child))))))

(defn- fork-with-dropped-owned-cell [world]
  (let [parent (c/runtime {:audit? true}) holder (atom nil) outcomes (atom [])
        spin (c/cspin parent :owner
                      (let [a (ratom/atom 0)] (reset! holder a))
                      (c/park (c/ticket :body)))]
    (observe! parent spin outcomes)
    (let [a @holder id (ratom/atom-id a)
          weak #?(:clj (WeakReference. a) :cljs (js/WeakRef. a))
          child (c/fork-parked! parent world)]
      (try
        (reset! holder nil)
        {:parent parent :child child :spin spin :id id :weak weak}
        (finally #?(:clj (Reference/reachabilityFence a) :cljs nil))))))

(defn- copied-cell-collected? [{:keys [parent child id weak]}]
  (and (nil? #?(:clj (.get ^WeakReference weak) :cljs (.deref weak)))
       (nil? (get-in (c/snapshot parent) [:entities id]))
       (nil? (get-in (c/snapshot child) [:entities id]))))

(defn- check-copied-cell-collection! [{:keys [parent child spin]}]
  (is (contains? (c/snapshot parent) :source-gc))
  (is (contains? (c/snapshot child) :source-gc))
  (is (empty? (:source-gc (c/snapshot parent))))
  (is (empty? (:source-gc (c/snapshot child))))
  (is (some? spin))
  (verify-boundaries! parent))

#?(:clj
   (deftest one-host-receipt-reclaims-preexisting-copies-in-every-family-order
     (doseq [world [[:w 1] [:w 9] [:w 10]]]
       (let [{:keys [spin] :as info} (fork-with-dropped-owned-cell world)]
         (try
           (is (loop [remaining 200]
                 (cond (copied-cell-collected? info) true
                       (zero? remaining) false
                       :else (do (System/gc) (Thread/sleep 10) (recur (dec remaining)))))
               "Publishing a child's receipt first must not strand parent backing")
           (check-copied-cell-collection! info)
           (finally (Reference/reachabilityFence spin)))))))

#?(:cljs
   (deftest native-node-collection-reclaims-forked-cell-storage
     (if-not (fn? (.-gc js/globalThis))
       (println "Skipping native cell heap probe: Node --expose-gc is required")
       (async done
              (let [info (fork-with-dropped-owned-cell [:w 1])]
                (letfn [(attempt! [remaining]
                          (js/setTimeout
                           (fn []
                             (.gc js/globalThis)
                        ;; WeakRef observations occur after the GC job ends.
                             (js/setTimeout
                              (fn []
                                (cond
                                  (copied-cell-collected? info)
                                  (do (check-copied-cell-collection! info) (done))
                                  (zero? remaining)
                                  (do (is false "Native forked cells were not collected") (done))
                                  :else (attempt! (dec remaining))))
                              10)) 0))]
                  (attempt! 100)))))))

(deftest reconstructed-id-values-identify-the-same-retained-allocation
  (let [rt (runtime) callback (atom nil) trace (atom []) outcomes (atom [])
        spin (c/cspin rt :owner
                      (let [original (ratom/atom 41 :meta {:scope :owned})
                            id (ratom/atom-id original)
                            reconstructed (keyword (namespace id) (name id))
                            alias (ratom/->RuntimeAtom reconstructed)]
                        (is (= id reconstructed))
                        #?(:cljs (is (not (identical? id reconstructed))))
                        (try (c/park (c/ticket :body))
                             (finally
                               (swap! trace conj [@alias (meta alias)])
                               (c/await-finalization (fn [r _] (reset! callback r)))
                               (swap! alias inc)
                               (swap! trace conj [@alias (meta alias)])))))]
    (observe! rt spin outcomes)
    (c/cancel-spin! rt spin)
    (is (= [[41 {:scope :owned}]] @trace))
    (is (fn? @callback))
    (when-let [resume @callback] (resume :ready))
    (is (= [[41 {:scope :owned}] [42 {:scope :owned}]] @trace))
    (is (c/join-ready? rt [:owner 1]))
    (verify-boundaries! rt)))

(deftest owner-retirement-clears-borrowed-fork-watches-without-host-collection
  (let [parent (c/runtime {:audit? true})
        ;; Fork before the owner creates its cell, so the child borrows the
        ;; parent's later storage instead of receiving a local source copy.
        child (c/fork-parked! parent [:w 1])
        holder (atom nil) calls (atom []) outcomes (atom [])
        spin (c/cspin parent :owner
                      (reset! holder (ratom/atom :owned))
                      (c/park (c/ticket :body)))]
    (observe! parent spin outcomes)
    (let [a @holder id (ratom/atom-id a)]
      (binding [ec/*execution-context* child]
        (add-watch a :borrowed (fn [_ _ old new] (swap! calls conj [old new])))
        (is (= :owned @a))
        (is (nil? (get-in (c/snapshot child) [:entities id])))
        (is (contains? (rtp/get-state child [:listeners id]) :borrowed)))
      (c/cancel-spin! parent spin)
      (is (identical? a @holder) "The host wrapper is still live: this is owner retirement")
      (is (false? (rtp/runtime-cell-present? parent id)))
      (is (false? (rtp/runtime-cell-present? child id)))
      (is (nil? (rtp/get-state child [:listeners id]))
          "A borrowed watch cannot outlive the ordinary backing allocation")
      (is (empty? @calls))
      (is (empty? (:source-gc (c/snapshot parent))))
      (is (empty? (:source-gc (c/snapshot child))))
      (verify-boundaries! parent)
      #?(:clj (Reference/reachabilityFence a) :cljs nil))))
