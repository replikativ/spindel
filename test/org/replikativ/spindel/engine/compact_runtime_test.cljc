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
   (fn [state [raw-action raw-actual]]
     ;; Map iteration order is unspecified by the contract. Replay the
     ;; runtime's witnessed subscriber order without changing logical state.
     (let [action (model-value raw-action)
           actual (model-value raw-actual)
           order (zipmap (:delivery-order action) (range))
           state (if (:delivery-order action)
                   (update-in state [:worlds c/w :obligations]
                              #(into (sorted-map-by
                                      (fn [x y]
                                        (let [rank (compare (get order x 1000000000) (get order y 1000000000))]
                                          (if (zero? rank) (compare x y) rank)))) %)) state)
           expected (model/step state action)
           world (get-in expected [:worlds c/w])
           ev (assoc (select-keys world [:entities :runs :obligations :queue])
                     :seq (get world :seq 0) :serial (get-in expected [:serial :o] 0)
                     :clock (get-in expected [:clocks c/w] 0)
                     :handles (get-in expected [:env :handles])
                     :threads (get-in expected [:env :threads])
                     :gc (vec (get-in expected [:env :gc] [])))
           difference (take 2 (data/diff ev actual))]
       (when-not (= ev actual)
         (throw (ex-info "Boundary mismatch" {:action action :difference (vec difference)})))
       (is (= true (= ev actual)))
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
