(ns org.replikativ.spindel.engine.compact-runtime-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.compact-runtime :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.lifetime.model :as model]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.incremental.interval :as iv]
            [clojure.data :as data]
            [clojure.walk :as walk]))

(deftype EqualID [id]
  #?@(:clj [Object
            (hashCode [_] 0)
            (equals [_ other] (and (instance? EqualID other) (= id (.-id ^EqualID other))))]
      :cljs [IHash (-hash [_] 0)
             IEquiv (-equiv [_ other] (and (instance? EqualID other) (= id (.-id other))))]))

(defn- model-value [value]
  ;; The executable model uses symbolic identifiers and error values. Keep
  ;; equality/collision and actual exception identity tests on the runtime too.
  (walk/postwalk
   (fn [x]
     (cond
       (uuid? x) [:token (str x)]
       (instance? EqualID x) [:equal-id (.-id ^EqualID x)]
       (instance? #?(:clj org.replikativ.spindel.compact_runtime.Failure :cljs c/Failure) x)
       [:failure (ex-message (:error x)) (ex-data (:error x))]
       :else x)) value))

(defn verify-boundaries! [rt]
  (reduce
   (fn [state [raw-action raw-actual raw-family]]
     ;; Map iteration order is unspecified by the contract. Replay the
     ;; runtime's witnessed subscriber order without changing logical state.
     (let [action (model-value raw-action)
           family (model-value (or raw-family {c/w raw-actual}))
           order (zipmap (:delivery-order action) (range))
           state (if (:delivery-order action)
                   (update-in state [:worlds (:w action) :obligations]
                              #(into (sorted-map-by
                                      (fn [x y]
                                        (let [rank (compare (get order x 1000000000) (get order y 1000000000))]
                                          (if (zero? rank) (compare x y) rank)))) %)) state)
           notifications (zipmap (:notification-order action) (range))
           state (if (:notification-order action)
                   (update-in state [:env :handles (:tok action) :touched]
                              #(into (sorted-set-by
                                      (fn [x y]
                                        (let [rank (compare (get notifications x 1000000000)
                                                            (get notifications y 1000000000))]
                                          (if (zero? rank) (compare x y) rank)))) %)) state)
           expected (model/step state action)]
       (is (= (set (keys (:worlds expected))) (set (keys family))))
       (doseq [[id actual] family]
         (let [world (get-in expected [:worlds id])
               ev (assoc (select-keys world [:entities :runs :obligations :queue :lineage :root :status
                                             :admission :seal-seq :scopes :pins :fdeps :releasing])
                         :seq (get world :seq 0) :serial (get-in expected [:serial :o] 0)
                         :clock (get-in expected [:clocks id] 0)
                         :handles (get-in expected [:env :handles])
                         :threads (get-in expected [:env :threads])
                         :gc (vec (get-in expected [:env :gc] []))
                         :global (assoc (select-keys expected [:registry :known-worlds :lineages :caps])
                                        :generation-clock (get expected :generation-clock {})))
               difference (take 2 (data/diff ev actual))]
           (when-not (= ev actual)
             (throw (ex-info "Boundary mismatch" {:action action :world id :difference (vec difference)})))
           (is (= true (= ev actual)))))
       (is (empty? (inv/check expected)))
       expected))
   (model/init-state) @(:audit rt)))

(deftest compact-track-and-prefix
  (let [rt (c/runtime {:audit? true})
        source (c/signal rt :source 1)
        prefix (atom 0)
        s (c/cspin rt :spin (swap! prefix inc) (* 2 (iv/get-new (c/track source))))
        results (atom [])
        cancel (c/observe! rt s #(swap! results conj %) #(throw %))]
    (c/set-signal! rt source 2)
    (c/set-signal! rt source 3)
    (is (= [2 4 6] @results))
    (is (= 1 @prefix))
    (verify-boundaries! rt)
    (cancel)))

(deftest compact-diamond
  (let [rt (c/runtime {:audit? true})
        source (c/signal rt :source 0)
        b (c/cspin rt :b (* 2 (iv/get-new (c/track source))))
        cc (c/cspin rt :c (* 3 (iv/get-new (c/track source))))
        d (c/cspin rt :d (+ (c/await b) (c/await cc)))
        e (c/cspin rt :e (* 2 (c/await d)))
        f (c/cspin rt :f (* 3 (c/await d)))
        g (c/cspin rt :g (+ (c/await e) (c/await f)))
        dv (atom []) gv (atom [])]
    (c/observe! rt d #(swap! dv conj %) #(throw %))
    (c/observe! rt g #(swap! gv conj %) #(throw %))
    (doseq [i (range 1 4)] (c/set-signal! rt source i))
    (is (= [0 5 10 15] @dv))
    (is (= [0 25 50 75] @gv))
    (verify-boundaries! rt)))

(deftest compact-owned-prefix-and-errors
  (let [rt (c/runtime {:audit? true}) holder (atom nil)
        spin (c/cspin rt :spin
                      (let [s (c/signal rt :inner 1)]
                        (reset! holder s) (iv/get-new (c/track s))))
        result (atom [])]
    (c/observe! rt spin #(swap! result conj %) #(throw %))
    (c/set-signal! rt @holder 2)
    (is (= [1 2] @result))
    (verify-boundaries! rt))
  (let [rt (c/runtime {:audit? true}) error (ex-info "failed" {})
        child (c/cspin rt :child (throw error))
        parent (c/cspin rt :parent (c/await child))
        errors (atom [])]
    (c/observe! rt parent #(is false (str %)) #(swap! errors conj %))
    (is (= [error] @errors))
    (verify-boundaries! rt)))

(deftest compact-idle-release-and-incarnation-fencing
  (let [rt (c/runtime {:audit? true}) first (c/cspin rt :spin :first) result (atom [])]
    (c/observe! rt first #(swap! result conj %) #(throw %))
    (c/release-idle! rt)
    (is (thrown? #?(:clj Exception :cljs js/Error)
                 (c/observe! rt first #(swap! result conj %) #(throw %))))
    (let [fresh (c/cspin rt :spin :fresh)]
      (c/observe! rt fresh #(swap! result conj %) #(throw %)))
    (is (= [:first :fresh] @result))
    (verify-boundaries! rt)))

#?(:clj
   (deftest compact-cancellation-keeps-physical-evidence
     (let [rt (c/runtime {:audit? true}) entered (promise) leave (promise)
           errors (atom []) result (atom []) refused (atom nil)
           spin (c/cspin rt :spin
                         (deliver entered true)
                         @leave
                         (try (c/signal rt :late-source 1)
                              (catch Exception e (reset! refused (:error (ex-data e)))))
                         :late)
           worker (future (c/observe! rt spin #(swap! result conj %) #(swap! errors conj %)))]
       (try
         (is (= true (deref entered 10000 ::timeout)))
         (c/cancel-spin! rt spin)
         (is (= :unwinding (get-in (c/snapshot rt) [:runs [:spin 1] :status])))
         (finally (deliver leave true)))
       (is (fn? (deref worker 10000 ::timeout)))
       (is (= :cancelled @refused))
       (is (empty? @result))
       (is (= 1 (count @errors)))
       (is (empty? (:runs (c/snapshot rt))))
       (verify-boundaries! rt))))

#?(:clj
   (deftest compact-concurrent-observers
     (let [rt (c/runtime {:audit? true}) spin (c/cspin rt :spin 42)
           results (atom []) subscriptions (atom [])
           jobs (mapv (fn [_]
                        (future
                          (dotimes [_ 20]
                            (swap! subscriptions conj
                                   (c/observe! rt spin #(swap! results conj %) #(throw %))))))
                      (range 4))]
       (doseq [job jobs] (is (not= ::timeout (deref job 10000 ::timeout))))
       (c/drain! rt)
       (is (= (vec (repeat 80 42)) @results))
       (doseq [unsubscribe @subscriptions] (unsubscribe))
       (verify-boundaries! rt))))

(deftest compact-native-directory-honors-id-equality-and-collisions
  (let [rt (c/runtime {:audit? true})
        first (c/cspin rt (EqualID. 1) :first)
        alias (c/cspin rt (EqualID. 1) :wrong)
        distinct (c/cspin rt (EqualID. 2) :distinct)
        results (atom [])]
    (c/observe! rt first #(swap! results conj %) #(throw %))
    (c/observe! rt alias #(swap! results conj %) #(throw %))
    (c/observe! rt distinct #(swap! results conj %) #(throw %))
    (is (= [:first :first :distinct] @results))
    (verify-boundaries! rt)))

(deftest compact-reclaims-a-cache-with-a-retired-creator
  (let [rt (c/runtime {:audit? true})
        parent (c/cspin rt :parent
                        (let [child (c/cspin rt :child 1)] (c/await child)))
        values (atom []) errors (atom [])]
    (c/observe! rt parent #(swap! values conj %) #(swap! errors conj %))
    (c/cancel-spin! rt parent)
    (c/release-idle! rt)
    (is (= [1] @values))
    (is (empty? (:entities (c/snapshot rt))))
    (verify-boundaries! rt)))

#?(:clj
   (deftest compact-restart-fences-a-queued-old-continuation
     (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 1)
           prefix (atom 0)
           spin (c/cspin rt :spin (swap! prefix inc) (* 2 (iv/get-new (c/track source))))
           original-execute @#'c/execute!
           pause? (atom false) entered (promise) leave (promise)
           first-values (atom []) second-values (atom [])]
       (c/observe! rt spin #(swap! first-values conj %) (fn [_]))
       (with-redefs-fn
         {#'c/execute! (fn [runtime node]
                         (when (compare-and-set! pause? true false)
                           (deliver entered true) @leave)
                         (original-execute runtime node))}
         (fn []
           (reset! pause? true)
           (let [worker (future (c/set-signal! rt source 2))]
             (try
               (is (= true (deref entered 10000 ::timeout)))
               (c/cancel-spin! rt spin)
               (c/observe! rt spin #(swap! second-values conj %) #(throw %))
               (finally (deliver leave true)))
             (is (nil? (deref worker 10000 ::timeout))))))
       (is (= 2 @prefix))
       (is (= [2] @first-values))
       (is (= [4] @second-values))
       (verify-boundaries! rt))))

(deftest compact-deepening-dependency-waits-for-current-results
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
        tail (c/cspin rt :tail (* 10 (iv/get-new (c/track source))))
        inner (c/cspin rt :inner (inc (c/await tail)))
        middle (c/cspin rt :middle (inc (c/await inner)))
        b (c/cspin rt :b
                   (let [x (iv/get-new (c/track source))]
                     (if (zero? x) 0 (c/await middle))))
        cc (c/cspin rt :c (* 100 (iv/get-new (c/track source))))
        d (c/cspin rt :d (+ (c/await b) (c/await cc)))
        values (atom [])]
    (c/observe! rt d #(swap! values conj %) #(throw %))
    (c/set-signal! rt source 1)
    (c/set-signal! rt source 2)
    (is (= [0 112 222] @values))
    (verify-boundaries! rt)))

(deftest compact-host-finalization-preserves-wanted-work
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 1)
        spin (c/cspin rt :spin (* 2 (iv/get-new (c/track source))))
        values (atom [])]
    (c/observe! rt spin #(swap! values conj %) #(throw %))
    (c/notify-unreachable! rt spin)
    (is (empty? (get-in (c/snapshot rt) [:entities :spin :tokens])))
    (c/set-signal! rt source 2)
    (is (= [2 4] @values))
    (verify-boundaries! rt)))

(deftest compact-host-finalization-reclaims-idle-caches
  (let [rt (c/runtime {:audit? true}) spin (c/cspin rt :spin 42)]
    (c/observe! rt spin (fn [_]) #(throw %))
    (c/notify-unreachable! rt spin)
    (c/notify-unreachable! rt spin)
    (is (empty? (:entities (c/snapshot rt))))
    (verify-boundaries! rt)))

(deftest compact-repeated-child-handles-do-not-accumulate-tokens
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
        parent (c/cspin rt :parent
                        (c/track source)
                        (let [child (c/cspin rt :child (iv/get-new (c/track source)))
                              value (c/await child)]
                          (c/notify-unreachable! rt child)
                          value))
        values (atom [])]
    (c/observe! rt parent #(swap! values conj %) #(throw %))
    (doseq [i (range 1 11)]
      (c/set-signal! rt source i)
      (is (empty? (get-in (c/snapshot rt) [:entities :child :tokens]))))
    (is (= (vec (range 11)) @values))
    (verify-boundaries! rt)))

#?(:clj
   (deftest compact-jvm-cleaner-does-not-retain-the-host-handle
     (let [rt (c/runtime {:audit? true})
           weak (let [handle (c/cspin rt :spin 42)]
                  (c/observe! rt handle (fn [_]) #(throw %))
                  (java.lang.ref.WeakReference. handle))
           deadline (+ (System/nanoTime) 3000000000)]
       (loop []
         (when (and (seq (:entities (c/snapshot rt))) (< (System/nanoTime) deadline))
           (System/gc)
           (Thread/sleep 10)
           (recur)))
       (is (nil? (.get weak)))
       (is (empty? (:entities (c/snapshot rt))))
       (verify-boundaries! rt))))

(deftest compact-ticket-deliveries-fence-old-registrations
  (let [rt (c/runtime {:audit? true}) ticket (c/ticket :outside)
        spin (c/cspin rt :spin (c/park ticket)) values (atom [])]
    (c/observe! rt spin #(swap! values conj %) (fn [_]))
    (let [old (c/pending-ticket rt ticket)]
      (c/cancel-spin! rt spin)
      (c/observe! rt spin #(swap! values conj %) #(throw %))
      (c/resume-ticket! rt old :late)
      (is (empty? @values))
      (c/resume-ticket! rt (c/pending-ticket rt ticket) 42)
      (is (= [42] @values)))
    (verify-boundaries! rt)))

(deftest compact-parked-fork-copies-only-owned-rows
  (let [rt (c/runtime {:audit? true}) ticket (c/ticket :outside)
        unused (c/signal rt :unrelated :unrelated)
        holder (atom nil) values (atom [])
        spin (c/cspin rt :spin
                      (let [source (c/signal rt :inside 1)]
                        (reset! holder source)
                        (let [value (c/park ticket)]
                          (c/signal rt :after value)
                          (let [result (+ value (iv/get-new (c/track source)))]
                            (swap! values conj result)
                            result))))]
    (c/observe! rt spin (fn [_]) #(throw %))
    (let [parent-delivery (c/pending-ticket rt ticket)
          child (c/fork-parked! rt [:w 1])
          child-delivery (c/pending-ticket child ticket)
          before (c/snapshot-family rt)]
      (is (= #{:spin :inside} (set (keys (:entities (c/snapshot child))))))
      (is (thrown? #?(:clj Exception :cljs js/Error) (c/resume-ticket! child parent-delivery :wrong-world)))
      (is (= before (c/snapshot-family rt)))
      (c/set-signal! rt @holder 7)
      (c/resume-ticket! child child-delivery 10)
      (c/resume-ticket! rt parent-delivery 20)
      (is (= [11 27] @values))
      (is (= 10 (get-in (c/snapshot child) [:entities :after :result])))
      (is (= 20 (get-in (c/snapshot rt) [:entities :after :result])))
      (is (nil? (get-in (c/snapshot child) [:entities (:id unused)])))
      (c/resume-ticket! child child-delivery :duplicate)
      (is (= [11 27] @values))
      (verify-boundaries! rt))))

(deftest compact-tickets-handle-absent-nil-and-false-ids
  (doseq [id [nil false :outside]]
    (let [rt (c/runtime {:audit? true}) ticket (c/ticket id)
          spin (c/cspin rt :spin (c/park ticket)) values (atom [])]
      (is (nil? (c/pending-ticket rt ticket)))
      (c/observe! rt spin #(swap! values conj %) #(throw %))
      (c/resume-ticket! rt (c/pending-ticket rt ticket) 42)
      (is (= [42] @values))
      (is (nil? (c/pending-ticket rt ticket)))
      (verify-boundaries! rt))))

(deftest compact-fork-refusals-publish-no-rows
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 1) ticket (c/ticket :outside)
        spin (c/cspin rt :spin (c/track source) (c/park ticket))]
    (c/observe! rt spin (fn [_]) #(throw %))
    (let [before (c/snapshot-family rt)]
      (is (thrown? #?(:clj Exception :cljs js/Error) (c/fork-parked! rt [:w 1])))
      (is (= before (c/snapshot-family rt))))
    (is (= :spin (:id spin)))
    (verify-boundaries! rt)))

(deftest compact-fork-finalization-routes-to-both-worlds
  (let [rt (c/runtime {:audit? true}) ticket (c/ticket :outside)
        spin (c/cspin rt :spin (c/park ticket))]
    (c/observe! rt spin (fn [_]) #(throw %))
    (let [child (c/fork-parked! rt [:w 1])]
      (c/notify-unreachable! rt spin)
      (is (empty? (get-in (c/snapshot rt) [:entities :spin :tokens])))
      (is (empty? (get-in (c/snapshot child) [:entities :spin :tokens])))
      (is (= :parked (get-in (c/snapshot rt) [:runs [:spin 1] :status])))
      (is (= :inherited (get-in (c/snapshot child) [:runs [:spin 1] :status])))
      (c/resume-ticket! child (c/pending-ticket child ticket) 42)
      (is (empty? (:entities (c/snapshot child))))
      (verify-boundaries! rt))))

(deftest compact-invoking-an-inherited-spin-starts-a-fresh-run
  (let [rt (c/runtime {:audit? true}) ticket (c/ticket :outside)
        spin (c/cspin rt :spin (c/park ticket)) values (atom [])]
    (c/observe! rt spin (fn [_]) #(throw %))
    (let [child (c/fork-parked! rt [:w 1]) old (c/pending-ticket child ticket)]
      (c/observe! child spin #(swap! values conj %) #(throw %))
      (c/resume-ticket! child old :late)
      (is (empty? @values))
      (c/resume-ticket! child (c/pending-ticket child ticket) 42)
      (is (= [42] @values))
      (let [fresh (c/cspin child :fresh 7)]
        (c/observe! child fresh #(swap! values conj %) #(throw %)))
      (is (= [42 7] @values))
      (verify-boundaries! rt))))

(deftest compact-two-track-sites-survive-run-reuse
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
        prefix (atom 0)
        spin (c/cspin rt :spin
                      (swap! prefix inc)
                      (+ (iv/get-new (c/track source)) (iv/get-new (c/track source))))
        values (atom [])]
    (c/observe! rt spin #(swap! values conj %) #(throw %))
    (doseq [i (range 1 11)] (c/set-signal! rt source i))
    (is (= (mapv #(* 2 %) (range 11)) @values))
    (is (= 1 @prefix))
    (verify-boundaries! rt)))

(deftest compact-run-pool-and-scratch-release-owned-references
  (let [rt (c/runtime) source (c/signal rt :source 0)
        b (c/cspin rt :b (iv/get-new (c/track source)))
        parent (c/cspin rt :parent (c/await b))]
    (c/observe! rt parent (fn [_]) #(throw %))
    (dotimes [i 1000] (c/set-signal! rt source i))
    (let [stats (c/storage-stats rt)]
      (is (= 2 (:live-runs stats)))
      (is (<= 1 (:pooled-runs stats) 32))
      (is (= 0 (:pooled-references stats)))
      (is (= 0 (:orphan-creation-links stats)))
      (is (= 0 (:scratch-references stats))))))

(def ^:dynamic *tag* :outside)

(deftest compact-fork-restores-user-bindings-and-keeps-world-authority
  (let [rt (c/runtime {:audit? true}) ticket (c/ticket :outside)
        values (atom [])
        spin (c/cspin rt :spin
                      (binding [*tag* :inside]
                        (c/park ticket)
                        (c/signal rt :after *tag*)
                        (swap! values conj *tag*)
                        *tag*))]
    (c/observe! rt spin (fn [_]) #(throw %))
    (is (= :outside *tag*))
    (let [child (c/fork-parked! rt [:w 1])]
      (c/resume-ticket! child (c/pending-ticket child ticket) 1)
      (is (= [:inside] @values))
      (is (= :outside *tag*))
      (is (= :inside (get-in (c/snapshot child) [:entities :after :result])))
      (is (nil? (get-in (c/snapshot rt) [:entities :after])))
      (verify-boundaries! rt))))

(deftest compact-restored-bindings-pump-loop-thunks-without-nesting
  (let [rt (c/runtime) source (c/signal rt :source 0) ticket (c/ticket :outside)
        wrong (atom false) values (atom [])
        spin (c/cspin rt :spin
                      (binding [*tag* :inside]
                        (c/park ticket)
                        (loop [i 0]
                          (if (< i 1000)
                            (do (c/track source)
                                (when-not (= :inside *tag*) (reset! wrong true))
                                (recur (inc i)))
                            :done))))]
    (c/observe! rt spin #(swap! values conj %) #(throw %))
    (c/resume-ticket! rt (c/pending-ticket rt ticket) 1)
    (c/set-signal! rt source 1)
    (is (= [:done :done] @values))
    (is (false? @wrong))
    (is (= :outside *tag*))
    (is (= 0 (:pooled-references (c/storage-stats rt))))))

(deftest compact-deliveries-cannot-cross-independent-families
  (let [a (c/runtime {:audit? true}) b (c/runtime {:audit? true}) ticket (c/ticket :outside)
        av (atom []) bv (atom [])
        sa (c/cspin a :spin (c/park ticket)) sb (c/cspin b :spin (c/park ticket))]
    (c/observe! a sa #(swap! av conj %) #(throw %))
    (c/observe! b sb #(swap! bv conj %) #(throw %))
    (let [delivery (c/pending-ticket a ticket) before (c/snapshot-family b)]
      (is (thrown? #?(:clj Exception :cljs js/Error) (c/resume-ticket! b delivery :wrong-family)))
      (is (= before (c/snapshot-family b)))
      (c/resume-ticket! a delivery 42)
      (c/resume-ticket! b (c/pending-ticket b ticket) 43))
    (is (= [42] @av)) (is (= [43] @bv))
    (verify-boundaries! a) (verify-boundaries! b)))

(deftest compact-root-named-spin-adopts-a-retired-creators-cache
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
        holder (atom nil) values (atom [])
        parent (c/cspin rt :root
                        (let [n (iv/get-new (c/track source))]
                          (if (= 1 n) :skip
                              (let [child (c/cspin rt :child 1)]
                                (reset! holder child)
                                (c/await child)))))]
    (c/observe! rt parent #(swap! values conj %) #(throw %))
    (c/set-signal! rt source 1)
    (c/set-signal! rt source 2)
    (is (= [1 :skip 1] @values))
    (is (= :child (:id @holder)))
    (verify-boundaries! rt)))

(deftest compact-handles-cannot-silently-import-foreign-token-state
  (let [a (c/runtime {:audit? true}) b (c/runtime {:audit? true})
        spin (c/cspin a :spin 42)
        before (c/snapshot-family b)]
    (is (thrown? #?(:clj Exception :cljs js/Error)
                 (c/observe! b spin (fn [_]) #(throw %))))
    (is (= before (c/snapshot-family b)))
    (verify-boundaries! a) (verify-boundaries! b)))

(deftest compact-track-perspectives-follow-completed-generations
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0) values (atom [])
        spin (c/cspin rt :spin
                      (let [v (c/track source)] [(iv/get-old v) (iv/get-new v)]))]
    (c/observe! rt spin #(swap! values conj %) #(throw %))
    (c/set-signal! rt source 1)
    (c/set-signal! rt source 2)
    (is (= [[0 0] [0 1] [1 2]] @values))
    (verify-boundaries! rt)))

(deftest compact-cancel-before-first-result-retires-the-stale-generation
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
        ticket (c/ticket :outside) perspectives (atom [])
        spin (c/cspin rt :spin
                      (let [v (c/track source)]
                        (swap! perspectives conj [(iv/get-old v) (iv/get-new v)])
                        (c/park ticket)))]
    (c/observe! rt spin (fn [_]) (fn [_]))
    (c/set-signal! rt source 1)
    (c/set-signal! rt source 2)
    (c/cancel-spin! rt spin)
    (is (= [[0 0] [0 1] [1 2]] @perspectives))
    (is (empty? (:runs (c/snapshot rt))))
    (is (nil? (c/pending-ticket rt ticket)))
    (verify-boundaries! rt)))

(deftest compact-resumed-errors-reach-the-right-handler
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
        error (ex-info "resumed body failed" {})
        spin (c/cspin rt :spin
                      (let [value (iv/get-new (c/track source))]
                        (if (= 1 value) (throw error) value)))
        values (atom []) errors (atom [])]
    (c/observe! rt spin #(swap! values conj %) #(swap! errors conj %))
    (c/set-signal! rt source 1)
    (c/set-signal! rt source 2)
    (is (= [0 2] @values))
    (is (= [error] @errors))
    (verify-boundaries! rt))
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
        spin (c/cspin rt :spin
                      (try (let [value (iv/get-new (c/track source))]
                             (if (= 1 value) (throw (ex-info "recover" {})) value))
                           (catch #?(:clj Exception :cljs :default) _ :recovered)))
        values (atom [])]
    (c/observe! rt spin #(swap! values conj %) #(throw %))
    (c/set-signal! rt source 1)
    (c/set-signal! rt source 2)
    (is (= [0 :recovered 2] @values))
    (verify-boundaries! rt)))

(deftest compact-source-and-cancellation-capabilities-stay-in-their-family
  (let [a (c/runtime {:audit? true}) b (c/runtime {:audit? true})
        foreign (c/signal a :source 1) local (c/signal b :source 2)
        foreign-spin (c/cspin a :spin 0)
        local-spin (c/cspin b :spin (iv/get-new (c/track local)))
        values (atom []) errors (atom [])]
    (c/observe! b local-spin #(swap! values conj %) #(throw %))
    (let [before (c/snapshot-family b)]
      (is (thrown? #?(:clj Exception :cljs js/Error) (c/set-signal! b foreign 9)))
      (is (thrown? #?(:clj Exception :cljs js/Error) (c/cancel-spin! b foreign-spin)))
      (is (thrown? #?(:clj Exception :cljs js/Error) (c/notify-unreachable! b foreign-spin)))
      (is (= before (c/snapshot-family b))))
    (c/observe! b (c/cspin b :foreign-track (c/track foreign)) (fn [_]) #(swap! errors conj %))
    (is (= [:unknown-source] (mapv #(-> % ex-data :error) @errors)))
    (c/set-signal! b local 3)
    (is (= [2 3] @values))
    (verify-boundaries! a) (verify-boundaries! b)))

(deftest compact-rewritten-hof-restores-lexical-bindings
  (let [rt (c/runtime {:audit? true}) ticket (c/ticket :outside) values (atom [])
        spin (c/cspin rt :spin
                      (mapv (fn [x]
                              (binding [*tag* x]
                                [(c/park ticket) *tag*]))
                            [:first :second]))]
    (c/observe! rt spin #(swap! values conj %) #(throw %))
    (c/resume-ticket! rt (c/pending-ticket rt ticket) 1)
    (is (= :outside *tag*))
    (c/resume-ticket! rt (c/pending-ticket rt ticket) 2)
    (is (= [[[1 :first] [2 :second]]] @values))
    (is (= :outside *tag*))
    (verify-boundaries! rt)))

(deftest compact-fanin-retains-cold-children-across-coalesced-invalidations
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
        children (mapv (fn [id] (c/cspin rt [:leaf id] (iv/get-new (c/track source)))) (range 3))
        spin (c/cspin rt :root
                      (loop [remaining children total 0]
                        (if-let [child (first remaining)]
                          (recur (next remaining) (+ total (c/await child)))
                          total)))
        values (atom [])]
    (c/observe! rt spin #(swap! values conj %) #(throw %))
    (doseq [value [1 2 3]] (c/set-signal! rt source value))
    (is (= [0 3 6 9] @values))
    (verify-boundaries! rt)))

(deftest compact-ancestry-does-not-accumulate-unreferenced-history
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
        spin (c/cspin rt :spin (iv/get-new (c/track source))) values (atom [])]
    (c/observe! rt spin #(swap! values conj %) #(throw %))
    (doseq [value (range 1 51)]
      (c/set-signal! rt source value)
      (is (zero? (:ancestry-references (c/storage-stats rt)))))
    (is (= (vec (range 51)) @values))
    (verify-boundaries! rt)))

#?(:clj
   (deftest compact-physical-cancellation-detaches-a-surviving-creators-cache
     (let [rt (c/runtime {:audit? true}) created (promise) leave (promise)
           child-holder (atom nil) errors (atom [])
           spin (c/cspin rt :parent
                         (let [child (c/cspin rt :child 42)]
                           (reset! child-holder child)
                           (c/await child)
                           (deliver created true)
                           @leave))
           worker (future (c/observe! rt spin (fn [_]) #(swap! errors conj %)))]
       (try
         (is (= true (deref created 10000 ::timeout)))
         (c/cancel-spin! rt spin)
         (is (nil? (get-in (c/snapshot rt) [:entities :child :creator])))
         (finally (deliver leave true)))
       (is (fn? (deref worker 10000 ::timeout)))
       (is (= 1 (count @errors)))
       (is (= 42 (get-in (c/snapshot rt) [:entities :child :result])))
       (is (some? @child-holder))
       (verify-boundaries! rt))))

(deftest compact-reclamation-retains-no-per-entity-generation-history
  (let [rt (c/runtime)]
    (dotimes [i 100]
      (let [handle (c/cspin rt [:ephemeral i] 42)]
        (c/observe! rt handle (fn [_]) #(throw %))
        (c/notify-unreachable! rt handle)))
    (is (empty? (:entities (c/snapshot rt))))
    (is (empty? (get-in (c/snapshot rt) [:global :generation-clock])))
    (is (zero? (:live-runs (c/storage-stats rt))))
    (is (zero? (:pooled-references (c/storage-stats rt))))))

(deftest compact-recreated-entity-cannot-adopt-an-earlier-incarnations-cache
  (doseq [audit? [false true]]
    (let [rt (c/runtime {:audit? audit?}) source (c/signal rt :source 0) holder (atom nil)
          original (c/cspin rt :parent
                            (let [child (c/cspin rt :child 42)]
                              (reset! holder child)
                              (c/await child)))
          cancel (c/observe! rt original (fn [_]) #(throw %))]
      (cancel)
      (c/cancel-spin! rt original)
      (c/notify-unreachable! rt original)
      (is (nil? (get-in (c/snapshot rt) [:entities :parent])))
      (let [creator (get-in (c/snapshot rt) [:entities :child :creator])
            replacement (c/cspin rt :parent
                                 (c/track source)
                                 (c/cspin rt :child :different-body)
                                 :replacement)]
        (c/observe! rt replacement (fn [_]) #(throw %))
        (c/set-signal! rt source 1)
        (is (= creator (get-in (c/snapshot rt) [:entities :child :creator])))
        (is (= 42 (get-in (c/snapshot rt) [:entities :child :result])))
        (is (some? @holder))
        (when audit? (verify-boundaries! rt))))))
