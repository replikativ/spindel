(ns org.replikativ.spindel.engine.owned-runtime-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.lifetime.model :as model]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.test-helpers :refer [async]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [clojure.data :as data]
            [clojure.walk :as walk]))

(deftype EqualID [id]
  #?@(:clj [Object
            (hashCode [_] 0)
            (equals [_ other] (and (instance? EqualID other) (= id (.-id ^EqualID other))))]
      :cljs [IHash (-hash [_] 0)
             IEquiv (-equiv [_ other] (and (instance? EqualID other) (= id (.-id other))))]))

#?(:cljs
   (deftest inline-memberships-match-native-set-mutations
     (let [actual (c/->InlineSet nil nil nil 0 nil) expected (js/Set.)
           keys [nil false js/undefined 0 -0.0 js/NaN 1 2 :key (js-obj) (array) [1] [1]]
           seed (volatile! 31245)
           check (fn []
                   (let [reference (js/Array.from expected) copied (.toArray actual) visited (array)]
                     (is (= (.-size expected) (.-size actual) (.-length copied)))
                     (.forEach actual (fn [value] (.push visited value)))
                     (is (= (.-length reference) (.-length visited)))
                     (dotimes [i (.-length reference)]
                       (is (js/Object.is (aget reference i) (aget copied i)))
                       (is (js/Object.is (aget reference i) (aget visited i))))
                     (doseq [key keys]
                       (is (= (.has expected key) (.has actual key)))
                       (let [pred (fn [value] (js/Object.is key value))]
                         (is (= (.some reference pred) (.some actual pred)))))))]
       ;; Cross the inline/spill boundary, empty it again, then exercise mixed
       ;; inserts/removals/clears with stable object keys, nil/false and NaN.
       (doseq [key keys] (.add expected key) (.add actual key) (check))
       (doseq [key keys] (is (= (.delete expected key) (.delete actual key))) (check))
       (dotimes [_ 2000]
         (let [bits (vreset! seed (bit-or (+ (js/Math.imul 1664525 @seed) 1013904223) 0))
               key (nth keys (mod (unsigned-bit-shift-right bits 0) (count keys)))
               op (bit-and (unsigned-bit-shift-right bits 20) 7)]
           (cond (< op 4) (do (.add expected key) (is (identical? actual (.add actual key))))
                 (< op 6) (is (= (.delete expected key) (.delete actual key)))
                 (= op 7) (do (.clear expected) (.clear actual))))
         (check)))))

#?(:cljs
   (deftest owned-queue-wraps-grows-removes-and-releases-storage
     (let [q (c/->OwnedQueue (doto (make-array 16) (.fill nil)) 0 0)
           expected (atom []) seed (volatile! 981)
           check (fn []
                   (let [copied (.toArray q)]
                     (is (= @expected (vec copied)))
                     (is (= (count @expected) (.-length q)))
                     (is (= 0 (.staleReferences q)))
                     (when (empty? @expected) (is (<= (.capacity q) 256)))))]
       (dotimes [i 1024] (.add q i) (swap! expected conj i))
       (dotimes [_ 901] (is (= (first @expected) (.poll q))) (swap! expected #(vec (rest %))))
       (dotimes [i 900] (.add q i) (swap! expected conj i))
       (check)
       (.removeWhere q even?) (swap! expected #(vec (remove even? %))) (check)
       (dotimes [_ (count @expected)] (is (= (first @expected) (.poll q))) (swap! expected #(vec (rest %))))
       (check)
       (is (= 16 (.capacity q)))
       (dotimes [_ 3000]
         (let [bits (vreset! seed (bit-or (+ (js/Math.imul 1664525 @seed) 1013904223) 0))
               value (bit-and (unsigned-bit-shift-right bits 9) 31)
               op (bit-and (unsigned-bit-shift-right bits 20) 7)]
           (cond
             (< op 4) (do (.add q value) (swap! expected conj value))
             (= op 4) (do (is (= (first @expected) (.poll q))) (swap! expected #(vec (rest %))))
             (= op 5) (let [before @expected index (first (keep-indexed #(when (= %2 value) %1) before))]
                        (is (= (some? index) (.remove q value)))
                        (when (some? index) (reset! expected (into (subvec before 0 index) (subvec before (inc index))))))
             (= op 6) (do (.removeWhere q even?) (swap! expected #(vec (remove even? %))))
             :else (do (.clear q) (reset! expected []))))
         (check)))))

(defn- model-value [value]
  ;; The executable model uses symbolic identifiers and error values. Keep
  ;; equality/collision and actual exception identity tests on the runtime too.
  (cond
    (uuid? value) [:token (str value)]
    (inst? value) [:instant (inst-ms value)]
    (instance? EqualID value) [:equal-id (.-id ^EqualID value)]
    (instance? #?(:clj org.replikativ.spindel.engine.impl.owned.Failure :cljs c/Failure) value)
    [:failure (ex-message (:error value)) (model-value (ex-data (:error value)))]
    (instance? #?(:clj Throwable :cljs js/Error) value)
    [:exception (ex-message value) (model-value (ex-data value))]
    :else (walk/walk model-value identity value)))

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
               ev (if (contains? actual :native)
                    (assoc ev :native (get-in expected [:env :native])
                           :cleanup-cells (get-in expected [:env :cleanup-cells] {})) ev)
               ev (if (contains? actual :source-gc)
                    (assoc ev :source-gc
                           (into {} (filter (fn [[[world _ _] _]] (= world id))
                                            (get-in expected [:env :source-gc] {})))) ev)
               difference (take 2 (data/diff ev actual))]
           (when-not (= ev actual)
             (throw (ex-info "Boundary mismatch" {:action action :world id :difference (vec difference)})))
           (is (= true (= ev actual)))))
       (is (empty? (inv/check expected)))
       (is (empty? (inv/edge-check {:before state :action action :after expected})))
       expected))
   (model/init-state (when (contains? (c/snapshot rt) :native) {:slices? true :cps-exit? true})) @(:audit rt)))

(deftest completed-ownership-island-becomes-value-only-before-gc
  (doseq [audit? [false true]]
    (let [rt (c/runtime {:audit? audit?}) calls (atom 0)
          child (c/cspin rt :child 42)
          parent (c/cspin rt :parent (swap! calls inc) (c/await child))
          values (atom []) stop (c/observe! rt parent #(swap! values conj %) #(throw %))]
      (stop)
      (let [state (c/snapshot rt)]
        (is (empty? (:runs state)))
        (is (empty? (:obligations state)))
        (is (= {:parent 42 :child 42} (update-vals (:entities state) :result)))
        (is (= 0 (:idle-body-references (c/storage-stats rt)))))
      ((c/observe! rt parent #(swap! values conj %) #(throw %)))
      (is (= [42 42] @values))
      (is (= 1 @calls))
      (c/notify-unreachable! rt parent)
      (c/notify-unreachable! rt child)
      (is (empty? (:entities (c/snapshot rt))))
      (is (= 0 (:live-runs (c/storage-stats rt))))
      (when audit? (verify-boundaries! rt)))))

(deftest an-independent-observer-keeps-the-completed-closure
  (let [rt (c/runtime {:audit? true}) child (c/cspin rt :child 42)
        parent (c/cspin rt :parent (c/await child))
        stop-one (c/observe! rt parent (fn [_]) #(throw %))
        stop-two (c/observe! rt parent (fn [_]) #(throw %))]
    (stop-one)
    (is (= 2 (:live-runs (c/storage-stats rt))))
    (stop-two)
    (is (= 0 (:live-runs (c/storage-stats rt))))
    (is (empty? (:obligations (c/snapshot rt))))
    (verify-boundaries! rt)))

(deftest completed-source-owner-is-not-its-own-anchor
  (let [rt (c/runtime {:audit? true})
        parent (c/cspin rt :parent (c/signal rt :owned 1) 42)]
    (c/observe! rt parent (fn [_]) #(throw %))
    (is (nil? (get-in (c/snapshot rt) [:entities :owned])))
    (is (= 42 (get-in (c/snapshot rt) [:entities :parent :result])))
    (is (= 0 (:live-runs (c/storage-stats rt))))
    (verify-boundaries! rt)))

(deftest native-delivery-is-once-only-and-outside-gate
  (let [rt (c/runtime {:audit? true}) callbacks (atom nil) values (atom [])
        cancelled (atom 0)
        s (c/cspin rt :native
                   (inc (c/await-host
                         (fn [succeed! fail!]
                           (is #?(:clj (not (Thread/holdsLock (:gate rt))) :cljs true))
                           (reset! callbacks [succeed! fail!])
                           #(swap! cancelled inc)))))
        unsubscribe (c/observe! rt s #(swap! values conj %) #(throw %))]
    (is (= [] @values))
    ((first @callbacks) 41)
    ((first @callbacks) 99)
    ((second @callbacks) (ex-info "late" {}))
    (is (= [42] @values))
    (is (= 0 @cancelled))
    (verify-boundaries! rt)
    (unsubscribe)))

(deftest native-cancel-fences-stale-delivery
  (let [rt (c/runtime {:audit? true}) callbacks (atom []) values (atom [])
        cancelled (atom 0)
        s (c/cspin rt :native
                   (c/await-host (fn [succeed! _]
                                   (swap! callbacks conj succeed!)
                                   (fn []
                                     (is #?(:clj (not (Thread/holdsLock (:gate rt))) :cljs true))
                                     (swap! cancelled inc)))))
        un1 (c/observe! rt s #(swap! values conj %) (fn [_]))]
    (c/cancel-spin! rt s)
    (is (= 1 @cancelled))
    (let [un2 (c/observe! rt s #(swap! values conj %) #(throw %))]
      ((first @callbacks) :obsolete)
      ((second @callbacks) :fresh)
      (is (= [:fresh] @values))
      (is (= 1 @cancelled))
      (verify-boundaries! rt)
      (un1) (un2))))

(deftest native-cancel-during-start-and-synchronous-delivery
  (doseq [deliver? [true false]]
    (let [rt (c/runtime {:audit? true}) holder (atom nil) cancelled (atom 0) values (atom [])
          s (c/cspin rt :native
                     (c/await-host
                      (fn [succeed! _]
                        (if deliver? (succeed! :done) (c/cancel-spin! rt @holder))
                        #(swap! cancelled inc))))]
      (reset! holder s)
      (let [unsubscribe (c/observe! rt s #(swap! values conj %) (fn [_]))]
        (is (= (if deliver? [:done] []) @values))
        (is (= (if deliver? 0 1) @cancelled))
        (verify-boundaries! rt)
        (unsubscribe)))))

(deftest native-start-failure-enters-cps-catch
  (let [rt (c/runtime {:audit? true}) values (atom [])
        s (c/cspin rt :native
                   (try (c/await-host (fn [_ _] (throw (ex-info "start failed" {}))))
                        (catch #?(:clj Exception :cljs :default) e (ex-message e))))
        unsubscribe (c/observe! rt s #(swap! values conj %) #(throw %))]
    (is (= ["start failed"] @values))
    (verify-boundaries! rt)
    (unsubscribe)))

(deftest native-throwing-cancel-still-drains-committed-work
  (let [rt (c/runtime {:audit? true}) failures (atom 0)
        failure (ex-info "detach failed" {})
        s (c/cspin rt :native (c/await-host (fn [_ _] (fn [] (throw failure)))))]
    (c/observe! rt s (fn [_]) (fn [_] (swap! failures inc)))
    (is (identical? failure (try (c/cancel-spin! rt s) nil
                                 (catch #?(:clj Exception :cljs :default) e e))))
    (is (= 1 @failures))
    (verify-boundaries! rt)))

(deftest throwing-observers-finish-deliveries-and-preserve-the-computation-result
  (doseq [failed? [false true]]
    (let [rt (c/runtime {:audit? true}) callbacks (atom nil)
          computation-error (ex-info "computation rejected" {})
          observer-errors [(ex-info "observer one" {}) (ex-info "observer two" {})]
          attempted (atom []) delivered (atom []) cached (atom [])
          s (c/cspin rt :native
                     (c/await-host (fn [resolve reject] (reset! callbacks [resolve reject]) nil)))
          receive (fn [value] (swap! delivered conj value))]
      (doseq [error observer-errors]
        (let [observer (fn [_] (swap! attempted conj error) (throw error))]
          (c/observe! rt s observer observer)))
      (c/observe! rt s receive receive)
      (let [caught (try ((nth @callbacks (if failed? 1 0)) (if failed? computation-error 42)) nil
                        (catch #?(:clj Throwable :cljs :default) error error))]
        (is (= 2 (count @attempted)))
        (is (identical? (first @attempted) caught))
        (is (= [(if failed? computation-error 42)] @delivered)))
      ;; Observers cannot turn a cached success into a computation failure,
      ;; nor replace the original rejection with their own exceptions.
      (c/observe! rt s #(swap! cached conj %) #(swap! cached conj %))
      (is (= [(if failed? computation-error 42)] @cached))
      ((first @callbacks) :late)
      ((second @callbacks) (ex-info "late rejection" {}))
      (is (= 2 (count @attempted)))
      (is (= 1 (count @delivered)))
      (verify-boundaries! rt))))

(deftest throwing-observer-still-delivers-reentrant-registration
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
        s (c/cspin rt :reader (iv/get-new (c/track source)))
        delivered (atom []) failure (ex-info "observer failed" {})]
    (c/observe! rt s
                (fn [value]
                  (when (= 1 value)
                    (c/observe! rt s #(swap! delivered conj %) #(throw %))
                    (throw failure)))
                #(throw %))
    (is (identical? failure (try (c/set-signal! rt source 1) nil
                                 (catch #?(:clj Throwable :cljs :default) error error))))
    (is (= [1] @delivered))
    (verify-boundaries! rt)))

#?(:cljs
   (deftest falsey-observer-and-cancellation-errors-are-reported
     (doseq [payload [nil false] cancel? [false true]]
       (let [rt (c/runtime) callbacks (atom nil) delivered (atom [])
             s (c/cspin rt :native
                        (c/await-host
                         (fn [resolve reject]
                           (reset! callbacks [resolve reject])
                           (when cancel? (fn [] (throw payload))))))]
         (when-not cancel?
           (c/observe! rt s (fn [_] (throw payload)) (fn [_]))
           (c/observe! rt s (fn [_] (throw (ex-info "later observer" {}))) (fn [_])))
         (c/observe! rt s #(swap! delivered conj %) #(swap! delivered conj :cancelled))
         (let [caught (try
                        (if cancel? (c/cancel-spin! rt s) ((first @callbacks) 42))
                        {:thrown? false}
                        (catch :default error {:thrown? true :payload error}))]
           (is (= {:thrown? true :payload payload} caught))
           (is (= [(if cancel? :cancelled 42)] @delivered)))))))

#?(:clj
   (deftest first-observer-error-survives-a-dispatch-handoff
     (let [rt (c/runtime) deliver (atom nil)
           s (c/cspin rt :native (c/await-host (fn [resolve _] (reset! deliver resolve) nil)))
           first-error (ex-info "first observer" {}) later-error (ex-info "later observer" {})
           dispatch-var (ns-resolve 'org.replikativ.spindel.engine.impl.owned 'next-dispatch!)
           dispatch @dispatch-var injected? (atom false)]
       (c/observe! rt s (fn [_] (throw first-error)) #(throw %))
       ;; Force an arrival between the empty observation and releasing the
       ;; drain claim, without adding a production scheduling hook.
       (with-redefs-fn
         {dispatch-var (fn [runtime]
                         (let [entry (dispatch runtime)]
                           (when (and (nil? entry) (compare-and-set! injected? false true))
                             (c/observe! rt s (fn [_] (throw later-error)) #(throw %)))
                           entry))}
         #(is (identical? first-error (try (@deliver 42) nil (catch Throwable error error))))))))

(deftest native-registration-refuses-fork-atomically
  (let [rt (c/runtime {:audit? true})
        s (c/cspin rt :native (c/await-host (fn [_ _] (fn []))))
        unsubscribe (c/observe! rt s (fn [_]) (fn [_]))
        before (c/snapshot-family rt)]
    (is (try (c/fork-parked! rt :child) false (catch #?(:clj Exception :cljs :default) _ true)))
    (is (= before (c/snapshot-family rt)))
    (verify-boundaries! rt)
    (unsubscribe)))

(deftest native-external-thread-delivery
  (async done
         (let [rt (c/runtime {:audit? true})
               s (c/cspin rt :native
                          (inc (c/await-host
                                (fn [succeed! _]
                                  #?(:clj (future (succeed! 41)) :cljs (js/setTimeout #(succeed! 41) 0))
                                  nil))))]
           (c/observe! rt s
                       (fn [value]
                         (is (= 42 value))
                         (verify-boundaries! rt)
                         (done))
                       (fn [error] (is false (str error)) (done))))))

#?(:clj
   (deftest native-cancel-races-physical-registration-start
     (dotimes [_ 20]
       (let [rt (c/runtime {:audit? true}) entered (promise) release (promise)
             cancelled (atom 0) failures (atom 0) values (atom [])
             start (fn [succeed! _]
                     (deliver entered succeed!)
                     @release
                     (fn []
                       (is (not (Thread/holdsLock (:gate rt))))
                       (swap! cancelled inc)))
             s (c/cspin rt :native (c/await-host start))
             runner (future (c/observe! rt s #(swap! values conj %) (fn [_] (swap! failures inc))))
             callback (deref entered 10000 nil)]
         (is (some? callback))
         (when callback
           (c/cancel-spin! rt s)
           (is (= [:unwinding] (mapv :status (vals (:runs (c/snapshot rt))))))
           (is (= 0 @cancelled))
           (callback :obsolete))
         (deliver release true)
         (is (fn? (deref runner 10000 nil)))
         (is (= 1 @cancelled))
         (is (= 1 @failures))
         (is (= [] @values))
         (verify-boundaries! rt)))))

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

(deftest portable-computation-targets-keep-family-local-tokens
  (let [a (c/runtime {:audit? true}) b (c/runtime {:audit? true})
        body (fn [succeed! _] (succeed! 42))
        target (spin-core/->Spin :portable body) values (atom [])]
    (c/register-computation! a target :portable)
    (c/register-computation! a target :portable)
    (c/invoke-computation! a target :portable body #(swap! values conj [:a %]) #(throw %))
    (c/invoke-computation! b target :portable body #(swap! values conj [:b %]) #(throw %))
    (is (= [[:a 42] [:b 42]] @values))
    (is (= 1 (count (:handles (c/snapshot a)))))
    (is (= 1 (count (:handles (c/snapshot b)))))
    (c/release-idle! a)
    (let [before (c/snapshot-family a)]
      (is (thrown? #?(:clj Exception :cljs js/Error)
                   (c/invoke-computation! a target :portable body (fn [_]) #(throw %))))
      (is (= before (c/snapshot-family a))))
    ;; Reuse in B cannot inherit A's dropped capability or mint another token.
    (c/invoke-computation! b target :portable body #(swap! values conj [:b %]) #(throw %))
    (is (= [[:a 42] [:b 42] [:b 42]] @values))
    (verify-boundaries! a) (verify-boundaries! b)))

(deftest portable-first-use-is-not-local-body-construction
  (let [rt (c/runtime {:audit? true}) body (fn [succeed! _] (succeed! 7))
        target (spin-core/->Spin :portable body)
        parent (c/make-spin rt :parent
                            (fn [succeed! fail!]
                              (c/await-computation-effect! target :portable body succeed! fail!)))
        values (atom [])
        unsubscribe (c/observe! rt parent #(swap! values conj %) #(throw %))]
    (is (= [7] @values))
    (is (nil? (get-in (c/snapshot rt) [:entities :portable :creator])))
    (verify-boundaries! rt)
    (unsubscribe)))

(deftest portable-explicit-world-invocation-honors-its-target
  (let [a (c/runtime {:audit? true}) b (c/runtime {:audit? true}) values (atom [])
        body (fn [succeed! _] (succeed! 42)) target (spin-core/->Spin :portable body)
        parent (c/cspin a :parent
                        (c/invoke-computation! b target :portable body #(swap! values conj [:b %]) #(throw %))
                        :a-done)]
    (c/observe! a parent #(swap! values conj [:a %]) #(throw %))
    (is (= [[:b 42] [:a :a-done]] @values))
    (is (nil? (get-in (c/snapshot a) [:entities :portable])))
    (is (= 42 (get-in (c/snapshot b) [:entities :portable :result])))
    (verify-boundaries! a) (verify-boundaries! b)))

(deftest portable-handoff-refuses-an-unwinding-slice-before-editing
  (let [rt (c/runtime {:audit? true}) other (c/runtime {:audit? true}) holder (atom nil) errors (atom [])
        body (fn [succeed! _] (succeed! 42)) target (spin-core/->Spin :portable body)
        _ (c/register-computation! rt target :portable)
        fresh (spin-core/->Spin :fresh body)
        attempts [(fn [] (c/register-computation! rt target :portable))
                  (fn [] (c/register-computation! rt fresh :fresh))
                  (fn [] (c/invoke-computation! rt target :portable body (fn [_]) #(throw %)))
                  (fn [] (c/invoke-computation! rt fresh :fresh body (fn [_]) #(throw %)))
                  (fn [] (c/register-computation! other fresh :fresh))
                  (fn [] (c/invoke-computation! other fresh :fresh body (fn [_]) #(throw %)))]
        check (fn []
                (let [before [(c/snapshot-family rt) (c/snapshot-family other)]]
                  (doseq [attempt attempts]
                    (try (attempt) (is false "Unwinding call was admitted")
                         (catch #?(:clj Exception :cljs :default) error (swap! errors conj error))))
                  (is (= before [(c/snapshot-family rt) (c/snapshot-family other)]))))
        parent (c/cspin rt :parent (c/cancel-spin! rt @holder) (check))]
    (reset! holder parent)
    (c/observe! rt parent (fn [_]) (fn [_]))
    (is (= 6 (count @errors)))
    (verify-boundaries! rt) (verify-boundaries! other)))

#?(:clj
   (deftest portable-registration-race-mints-one-token
     (let [rt (c/runtime {:audit? true}) target (spin-core/->Spin :portable (fn [_ _]))
           start (promise)
           workers (doall (repeatedly 8 #(future @start (c/register-computation! rt target :portable))))]
       (deliver start true)
       (doseq [worker workers] (is (nil? (deref worker 10000 :timeout))))
       (is (= 1 (count (:handles (c/snapshot rt)))))
       (verify-boundaries! rt))))

#?(:clj
   (deftest portable-descriptor-does-not-retain-its-runtime
     (let [body (fn [succeed! _] (succeed! 42))
           target (spin-core/->Spin :portable body)
           weak ((fn []
                   (let [rt (c/runtime)]
                     (c/register-computation! rt target :portable)
                     (c/invoke-computation! rt target :portable body (fn [_]) #(throw %))
                     (java.lang.ref.WeakReference. rt))))]
       (try
         (loop [remaining 50]
           (when (and (pos? remaining) (.get weak))
             (System/gc)
             (Thread/sleep 10)
             (recur (dec remaining))))
         (is (nil? (.get weak)))
         (finally (java.lang.ref.Reference/reachabilityFence target))))))

(deftest source-cas-is-identity-based-and-refusal-is-atomic
  (let [rt (c/runtime {:audit? true}) initial (with-meta [1] {:version 0})
        equal-value (with-meta [1] {:version 1}) source (c/signal rt :source initial)
        before (c/snapshot-family rt)]
    (is (= initial equal-value))
    (is (not (identical? initial equal-value)))
    (is (false? (c/compare-and-set-signal! rt source equal-value [2])))
    (is (= before (c/snapshot-family rt)))
    (is (identical? initial (c/read-signal rt source)))
    (is (true? (c/compare-and-set-signal! rt source initial [2])))
    (is (= [2] (c/read-signal rt source)))
    (verify-boundaries! rt)))

(deftest cached-await-production-and-replayed-transitions-have-the-same-state
  (let [view (fn [rt]
               (-> (c/snapshot rt)
                   (dissoc :handles)
                   (update :global dissoc :generation-clock)
                   (update :entities #(into {} (map (fn [[id node]] [id (dissoc node :tokens)]) %)))))
        exercise (fn [audit?]
                   (let [rt (c/runtime {:audit? audit?})
                         checkpoints (atom [])
                         cached (c/cspin rt :cached 42)
                         _ (c/observe! rt cached (fn [_]) #(throw %))
                         parent (c/cspin rt :parent
                                         (let [source (c/signal rt :owned 0)
                                               child (c/cspin rt :child (c/await cached))]
                                           (let [value (+ (iv/get-new (c/track source)) (c/await child))]
                                      ;; User code can inspect the world as soon
                                      ;; as the ready continuation is invoked.
                                             (swap! checkpoints conj (view rt))
                                             value)))
                         values (atom [])
                         cancel (c/observe! rt parent #(swap! values conj %) #(throw %))
                         source (c/signal rt :owned 0)]
                     (doseq [value [1 2 3]] (c/set-signal! rt source value))
                     (when audit? (verify-boundaries! rt))
                     {:view (view rt) :checkpoints @checkpoints
                      :values @values
                      :keep [cached parent source cancel]}))
        traced (exercise true) fast (exercise false)]
    (is (= [42 43 44 45] (:values fast) (:values traced)))
    (is (= (:checkpoints traced) (:checkpoints fast)))
    (is (= (:view traced) (:view fast)))))

(deftest source-swap-retries-user-code-outside-the-gate
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
        calls (atom []) values (atom [])
        s (c/cspin rt :observer (iv/get-new (c/track source)))
        unsubscribe (c/observe! rt s #(swap! values conj %) #(throw %))]
    (is (= 3 (c/swap-signal! rt source
                             (fn [value]
                               (is #?(:clj (not (Thread/holdsLock (:gate rt))) :cljs true))
                               (swap! calls conj value)
                               (when (zero? value) (c/set-signal! rt source 2))
                               (inc value)))))
    (is (= [0 2] @calls))
    (is (= [0 2 3] @values))
    (is (= 6 (c/swap-signal! rt source + 1 2)))
    (verify-boundaries! rt)
    (unsubscribe)))

#?(:clj
   (deftest source-swap-concurrent-writers-do-not-lose-updates
     (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
           ready (promise)
           workers (doall (repeatedly 4 #(future @ready (dotimes [_ 25] (c/swap-signal! rt source inc)))))]
       (deliver ready true)
       (doseq [worker workers] (is (nil? (deref worker 10000 :timeout))))
       (is (= 100 (c/read-signal rt source)))
       (verify-boundaries! rt))))

#?(:clj
   (deftest source-release-during-swap-does-not-resurrect-it
     (let [rt (c/runtime {:audit? true}) holder (atom nil) ticket (c/ticket :waiting)
           s (c/cspin rt :owner
                      (reset! holder (c/signal rt :owned-source 0))
                      (c/park ticket))
           entered (promise) release (promise)]
       (c/observe! rt s (fn [_]) (fn [_]))
       (let [worker (future
                      (try
                        (c/swap-signal! rt @holder
                                        (fn [value] (deliver entered true) @release (inc value)))
                        (catch Exception error (ex-message error))))]
         (is (= true (deref entered 10000 nil)))
         (c/cancel-spin! rt s)
         (let [before (c/snapshot-family rt)]
           (deliver release true)
           (is (= "Released source" (deref worker 10000 nil)))
           (is (= before (c/snapshot-family rt))))
         (verify-boundaries! rt)))))

#?(:clj
   (deftest source-burst-while-dispatch-is-busy-retains-only-latest-state
     (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
           values (atom []) observed (c/cspin rt :observed (iv/get-new (c/track source)))
           unsubscribe (c/observe! rt observed #(swap! values conj %) #(throw %))
           entered (promise) release (promise)
           start (fn [_ _] (deliver entered true) @release nil)
           blocker (c/cspin rt :blocker (c/await-host start))
           runner (future (c/observe! rt blocker (fn [_]) (fn [_])))]
       (is (= true (deref entered 10000 nil)))
       (dotimes [i 128] (c/set-signal! rt source (inc i)))
       (is (= [0] @values))
       (is (= 1 (count (:queue (c/snapshot rt)))))
       (is (= 128 (c/read-signal rt source)))
       (deliver release true)
       (is (fn? (deref runner 10000 nil)))
       (is (= [0 128] @values))
       (c/cancel-spin! rt blocker)
       (verify-boundaries! rt)
       (unsubscribe))))

(deftest varied-depth-ready-work-stays-glitch-free
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 0)
        edges [[] [] [0] [1] [0 1] [2 4] [3] [6 1]
               [5 7] [4 6] [8 9] [2 3] [10 11] [7 11] [12 13] [9 14]]
        spins (reduce (fn [spins i]
                        (let [children (mapv spins (nth edges i))]
                          (conj spins
                                (c/cspin rt [:node i]
                                         (loop [children children total (iv/get-new (c/track source))]
                                           (if-let [child (first children)]
                                             (recur (next children) (mod (+ total (c/await child)) 100000))
                                             total)))))) [] (range (count edges)))
        values (mapv (fn [_] (atom [])) spins)
        subscriptions (mapv (fn [s values] (c/observe! rt s #(swap! values conj %) #(throw %))) spins values)
        expected (fn [input]
                   (reduce (fn [values deps]
                             (conj values (mod (reduce + input (map values deps)) 100000))) [] edges))]
    (doseq [input [1 2]] (c/set-signal! rt source input))
    (is (= (apply mapv vector (map expected [0 1 2])) (mapv deref values)))
    (verify-boundaries! rt)
    (doseq [unsubscribe subscriptions] (unsubscribe))))

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
      (is (= #{:spin} (set (keys (:entities (c/snapshot child))))))
      (is (= 11 (get-in (c/snapshot child) [:entities :spin :result])))
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

(deftest idle-reactive-caches-refresh-after-losing-validation
  (doseq [audit? [false true] transitive? [false true] cancel-child? [false true]]
    (let [rt (c/runtime {:audit? audit?}) input (c/signal rt :input 1)
          control (c/signal rt :control true)
          leaf (c/cspin rt :leaf (iv/get-new (c/track input)))
          child (if transitive? (c/cspin rt :child (c/await leaf)) leaf)
          warm (c/observe! rt child (fn [_]) #(throw %))
          parent (c/cspin rt :parent
                          (if (iv/get-new (c/track control)) (c/await child) :off))
          values (atom [])]
      (c/observe! rt parent #(swap! values conj %) #(throw %))
      (warm)
      (when cancel-child? (c/cancel-spin! rt leaf))
      (c/set-signal! rt control false)
      (c/set-signal! rt input 2)
      (is (= [1 :off] @values))
      (c/set-signal! rt control true)
      (is (= [1 :off 2] @values))
      (when audit? (verify-boundaries! rt)))))

(deftest consumed-debtor-cancellation-survives-a-parked-creditors-completion
  (doseq [audit? [false true]]
    (let [rt (c/runtime {:audit? audit?}) input (c/signal rt :input 1)
          child (c/cspin rt :child (iv/get-new (c/track input)))
          warm (c/observe! rt child (fn [_]) #(throw %))
          callbacks (atom []) calls (atom 0) values (atom [])
          parent (c/cspin rt :parent
                          (swap! calls inc)
                          (let [value (c/await child)]
                            (c/await-host (fn [resolve _] (swap! callbacks conj resolve) nil))
                            value))
          stop (c/observe! rt parent #(swap! values conj %) #(throw %))]
      (warm)
      (c/cancel-spin! rt child)
      (c/set-signal! rt input 2)
      ((first @callbacks) nil)
      (is (= [1] @values))
      (stop)
      (is (get-in (c/snapshot rt) [:entities :parent :dirty?]))
      (let [stop-again (c/observe! rt parent #(swap! values conj %) #(throw %))]
        (is (= 2 @calls))
        (is (= 2 (count @callbacks)))
        ((last @callbacks) nil)
        (is (= [1 2] @values))
        (stop-again))
      (when audit? (verify-boundaries! rt)))))

(deftest forked-parked-creditor-copies-lost-validation
  (doseq [audit? [false true]]
    (let [rt (c/runtime {:audit? audit?}) input (c/signal rt :input 1)
          child (c/cspin rt :child (iv/get-new (c/track input)))
          warm (c/observe! rt child (fn [_]) #(throw %)) ticket (c/ticket :outside)
          parent (c/cspin rt :parent
                          (let [value (c/await child)] (c/park ticket) value))]
      (c/observe! rt parent (fn [_]) #(throw %))
      (warm)
      (c/cancel-spin! rt child)
      (let [fork (c/fork-parked! rt [:w 1])]
        (c/resume-ticket! fork (c/pending-ticket fork ticket) nil)
        (is (= 1 (get-in (c/snapshot fork) [:entities :parent :result])))
        (is (get-in (c/snapshot fork) [:entities :parent :dirty?]))
        (c/resume-ticket! rt (c/pending-ticket rt ticket) nil)
        (is (get-in (c/snapshot rt) [:entities :parent :dirty?]))
        (when audit? (verify-boundaries! rt))))))

(deftest idle-pure-caches-preserve-one-shot-results
  (doseq [audit? [false true]]
    (let [rt (c/runtime {:audit? audit?})
          calls (atom 0) child (c/cspin rt :child (swap! calls inc))
          values (atom [])]
      ((c/observe! rt child #(swap! values conj %) #(throw %)))
      (is (empty? (:runs (c/snapshot rt))))
      (is (not (get-in (c/snapshot rt) [:entities :child :dirty?])))
      ((c/observe! rt child #(swap! values conj %) #(throw %)))
      (is (= [1 1] @values))
      (is (= 1 @calls))
      (when audit? (verify-boundaries! rt)))))

(deftest awaiting-a-dirty-completion-refreshes-the-target
  (doseq [audit? [false true]]
    (let [rt (c/runtime {:audit? audit?}) source (c/signal rt :source 0)
          child (c/cspin rt :child (iv/get-new (c/track source)))
          values (atom [])]
      (c/observe! rt child (fn [_]) (fn [_]))
      (c/cancel-spin! rt child)
      (c/set-signal! rt source 7)
      (let [parent (c/cspin rt :parent (c/await child))]
        (c/observe! rt parent #(swap! values conj %) #(throw %))
        (is (= [7] @values))
        (when audit? (verify-boundaries! rt))))))

(deftest awaiting-an-inherited-spin-starts-a-fresh-run
  (let [rt (c/runtime {:audit? true}) ticket (c/ticket :outside)
        spin (c/cspin rt :spin (c/park ticket)) values (atom []) original (atom [])]
    (c/observe! rt spin #(swap! original conj %) #(throw %))
    (let [child (c/fork-parked! rt [:w 1]) old (c/pending-ticket child ticket)
          parent (c/cspin child :parent (c/await spin))]
      (c/observe! child parent #(swap! values conj %) #(throw %))
      (c/resume-ticket! child old :late)
      (is (empty? @values))
      (c/resume-ticket! child (c/pending-ticket child ticket) 9)
      (is (= [9] @values))
      (is (empty? @original))
      (c/resume-ticket! rt (c/pending-ticket rt ticket) 10)
      (is (= [10] @original))
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

(deftest forked-rejection-restores-nested-bindings-and-finally-in-its-own-world
  (let [rt (c/runtime {:audit? true}) source (c/signal rt :source 1)
        ticket (c/ticket :outside) cleanup (atom []) parent-values (atom [])
        failure (ex-info "rejected ticket" {})
        spin (c/cspin rt :spin
                      (binding [*tag* :outer]
                        (let [result (binding [*tag* :inner]
                                       (try (c/park ticket)
                                            :unexpected-success
                                            (catch #?(:clj Exception :cljs :default) error
                                              [*tag* (c/read-signal rt source) (ex-message error)])
                                            (finally (swap! cleanup conj [*tag* (c/read-signal rt source)]))))]
                          [*tag* result])))]
    (c/observe! rt spin #(swap! parent-values conj %) #(throw %))
    (let [child (c/fork-parked! rt [:w 1])]
      ;; The restricted parked-fork prototype has no general inherited-source
      ;; materialization yet. Distinct local sources test world authority here.
      (c/signal child :source 20)
      (c/set-signal! rt source 10)
      (c/reject-ticket! child (c/pending-ticket child ticket) failure)
      (is (= [:outer [:inner 20 "rejected ticket"]]
             (get-in (c/snapshot child) [:entities :spin :result])))
      (is (= [] @parent-values))
      (is (= [[:inner 20]] @cleanup))
      (is (= :outside *tag*))
      (c/reject-ticket! rt (c/pending-ticket rt ticket) failure)
      (is (= [[:outer [:inner 10 "rejected ticket"]]] @parent-values))
      (is (= [[:inner 20] [:inner 10]] @cleanup))
      (is (= :outside *tag*))
      (verify-boundaries! rt))))

(deftest asynchronous-rejection-restores-bindings-through-catch-and-finally
  (async done
         (let [rt (c/runtime) cleanup (atom nil) failure (ex-info "native rejection" {})
               spin (c/cspin rt :spin
                             (binding [*tag* :inside]
                               (try (c/await-host
                                     (fn [_ reject]
                                       #?(:clj (future (reject failure))
                                          :cljs (js/setTimeout #(reject failure) 0))
                                       nil))
                                    (catch #?(:clj Exception :cljs :default) error
                                      [*tag* (identical? failure error)])
                                    (finally (reset! cleanup *tag*)))))]
           (c/observe! rt spin
                       (fn [value]
                         (is (= [:inside true] value))
                         (is (= :inside @cleanup))
                         (done))
                       (fn [error] (is false (str error)) (done)))
           (is (= :outside *tag*)))))

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
      (is (= #{:spin} (set (keys (:entities (c/snapshot child))))))
      (is (= :inside (get-in (c/snapshot child) [:entities :spin :result])))
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
      (is (thrown? #?(:clj Exception :cljs js/Error) (c/read-signal b foreign)))
      (is (thrown? #?(:clj Exception :cljs js/Error) (c/compare-and-set-signal! b foreign 1 9)))
      (is (thrown? #?(:clj Exception :cljs js/Error)
                   (c/swap-signal! b foreign (fn [_] (is false "Foreign swap called user code")))))
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

(deftest wide-retention-graph-drops-obsolete-proofs-and-edges
  (let [rt (c/runtime {:audit? true :record-audit? false})
        source (c/signal rt :wide-source 0)
        children (mapv (fn [i] (c/cspin rt [:wide-child i] (iv/get-new (c/track source))))
                       (range 96))
        stops (mapv #(c/observe! rt % (fn [_]) (fn [e] (throw e))) children)]
    ;; Populate root proofs, then remove every host root and change the input.
    (c/set-signal! rt source 1)
    (doseq [stop stops] (stop))
    (c/set-signal! rt source 2)
    (doseq [child children] (c/notify-unreachable! rt child))
    ;; Structural graph auditing runs at every boundary above; the smaller
    ;; island tests separately replay the complete semantic model.
    (let [state (c/snapshot rt) stats (c/storage-stats rt)]
      (is (= #{:wide-source} (set (keys (:entities state)))))
      (is (empty? (:runs state)))
      (is (empty? (:obligations state)))
      (is (zero? (:liveness-scratch-references stats)))
      (is (zero? (:stale-liveness-references stats))))))

(deftest structural-auditing-without-retained-history
  (let [rt (c/runtime {:audit? true :record-audit? false})
        ticket (c/ticket :structural-only)
        values (atom [])
        spin (c/cspin rt :structural-spin (c/park ticket))]
    (c/observe! rt spin #(swap! values conj %) #(throw %))
    (let [child (c/fork-parked! rt :structural-child)]
      (c/resume-ticket! child (c/pending-ticket child ticket) :child)
      (c/resume-ticket! rt (c/pending-ticket rt ticket) :parent)
      (is (= [:parent] @values))
      (is (= :child (get-in (c/snapshot child) [:entities :structural-spin :result])))
      (doseq [runtime [rt child]]
        (is (some? (:audit runtime)))
        (is (nil? @(:audit runtime)))
        (is (zero? (:liveness-scratch-references (c/storage-stats runtime))))))))

#?(:clj
   (deftest structural-only-mode-still-checks-derived-state
     (let [rt (c/runtime {:audit? true :record-audit? false})
           source (c/signal rt :checked-source 0)
           audit-var (ns-resolve 'org.replikativ.spindel.engine.impl.owned 'audit-derived-state!)
           checked (ex-info "structural check reached" {})]
       (with-redefs-fn {audit-var (fn [_] (throw checked))}
         #(is (identical? checked
                          (try (c/set-signal! rt source 1) nil
                               (catch Throwable error error))))))))

(deftest completed-later-track-replay-keeps-earlier-source-reactive
  (let [rt (c/runtime {:audit? true}) early (c/signal rt :early 0)
        late (c/signal rt :late 0) values (atom [])
        spin (c/cspin rt :parent
                      [(iv/get-new (c/track early)) (iv/get-new (c/track late))])]
    (c/observe! rt spin #(swap! values conj %) #(throw %))
    (c/set-signal! rt late 1)
    (c/set-signal! rt early 1)
    (is (= [[0 0] [0 1] [1 1]] @values))
    (verify-boundaries! rt)))

(deftest completed-prefix-survives-a-working-successor-and-stale-delivery
  (let [rt (c/runtime {:audit? true}) early (c/signal rt :early 0)
        late (c/signal rt :late 0) gate (c/ticket :suffix) values (atom [])
        spin (c/cspin rt :parent
                      (let [a (iv/get-new (c/track early))
                            b (iv/get-new (c/track late))]
                        (when (pos? b) (c/park gate))
                        [a b]))]
    (c/observe! rt spin #(swap! values conj %) #(throw %))
    (c/set-signal! rt late 1)
    (let [obsolete (c/pending-ticket rt gate)]
      (is (some? obsolete))
      (c/set-signal! rt early 1)
      (let [current (c/pending-ticket rt gate)]
        (is (some? current))
        (is (not= obsolete current))
        (c/resume-ticket! rt obsolete :obsolete)
        (is (= [[0 0]] @values))
        (c/resume-ticket! rt current :ready)))
    (is (= [[0 0] [1 1]] @values))
    (c/set-signal! rt late 2)
    (c/resume-ticket! rt (c/pending-ticket rt gate) :ready)
    (is (= [[0 0] [1 1] [1 2]] @values))
    (verify-boundaries! rt)))
