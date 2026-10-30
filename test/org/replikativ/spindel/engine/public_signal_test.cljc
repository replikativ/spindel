(ns org.replikativ.spindel.engine.public-signal-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.signal :as signal]
            [org.replikativ.spindel.incremental.deltaable :as delta]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]))

(defn- runtime [] (context/create-execution-context {:engine :owned :audit? true}))
(defn- observe! [task values] (task #(swap! values conj %) #(throw %)))
(defn- plain [value] (delta/unwrap-deltaable value))
(defn- interval-view [interval]
  [(plain (:old interval)) (plain (:new interval)) (:deltas interval)])

(deftest public-signals-preserve-values-generation-and-identity-cas
  (doseq [engine [:simple :owned]]
    (let [rt (context/create-execution-context {:engine engine :audit? true})]
      (binding [ec/*execution-context* rt]
        (let [s (signal/signal nil)]
          (is (nil? @s))
          (is (= [nil nil nil] (interval-view (signal/get-signal-detailed s))))
          (is (= false (reset! s false)))
          (is (false? @s))
          (is (= [nil false nil] (interval-view (signal/get-signal-detailed s))))
          (is (= 1 (:generation (signal/get-signal-state s))))
          (is (false? (signal/swap-signal-changed? s identity)))
          (is (= 2 (:generation (signal/get-signal-state s))))
          (is (signal/compare-and-set-signal! s false 42))
          (is (not (signal/compare-and-set-signal! s false 43)))
          (is (= 42 @s))
          (is (= 3 (:generation (signal/get-signal-state s))))))
      (if (= :owned engine) (verify-boundaries! rt) (context/stop-context! rt)))))

(deftest public-track-delivers-real-intervals-independently-to-every-observer
  (let [rt (runtime) left (atom []) right (atom [])]
    (binding [ec/*execution-context* rt]
      (let [s (signal/signal [])
            a (spin (interval-view (track s)))
            b (spin (interval-view (track s)))]
        (observe! a left) (observe! b right)
        (is (= [[nil [] nil]] @left @right))
        (swap! s conj :x)
        (is (= @left @right))
        (is (= [[] [:x]] (take 2 (last @left))))
        (is (seq (last (last @left))))
        (is (= 2 (count (:observers (signal/get-signal-state s)))))
        (swap! s conj :y)
        (is (= @left @right))
        (is (= [[:x] [:x :y]] (take 2 (last @left))))
        (is (= 3 (count @left)))
        (is (= 2 (:generation (signal/get-signal-state s))))))
    (verify-boundaries! rt)))

(deftest reactive-await-prefix-remains-live-before-an-independent-public-track
  (let [rt (runtime) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [a (signal/signal 1) b (signal/signal 10)
            child (spin (iv/get-new (track a)))
            parent (spin (let [x (await child) y (iv/get-new (track b))] [x y]))]
        (observe! parent values)
        (reset! b 20)
        (reset! a 2)
        (reset! b 30)
        (is (= [[1 10] [1 20] [2 20] [2 30]] @values))
        (is (= {:variant :ok :payload [2 30] :clean? true}
               (rtp/computation-result rt parent (spin-core/spin-id parent))))))
    (verify-boundaries! rt)))

(deftest public-batch-publishes-final-values-and-keeps-per-write-watches
  (let [rt (runtime) values (atom []) watched (atom [])]
    (binding [ec/*execution-context* rt]
      (let [a (signal/signal 0) b (signal/signal 10)
            parent (spin [(iv/get-new (track a)) (iv/get-new (track b))])]
        (add-watch a :watch (fn [key ref old new]
                              (is (= :watch key)) (is (identical? a ref))
                              (is #?(:clj (not (Thread/holdsLock (:gate rt))) :cljs true))
                              (swap! watched conj [old new])))
        (observe! parent values)
        (is (= :batch-result
               (signal/batch
                (reset! a 1)
                (is (= [[0 10]] @values))
                (signal/batch (reset! a 2) (reset! b 20))
                (is (= [[0 10]] @values))
                (is (= [[0 1] [1 2]] @watched))
                :batch-result)))
        (is (= [[0 10] [2 20]] @values))
        (remove-watch a :watch)
        (reset! a 3)
        (is (= [[0 1] [1 2]] @watched))
        (is (= [3 20] (last @values)))))
    (verify-boundaries! rt)))

(deftest public-signal-transforms-revalidate-after-reentrant-writes
  (let [rt (runtime) calls (atom 0)]
    (binding [ec/*execution-context* rt]
      (let [s (signal/signal 0)]
        (is (= 11 (swap! s (fn [value]
                             (is #?(:clj (not (Thread/holdsLock (:gate rt))) :cljs true))
                             (when (= 1 (swap! calls inc)) (reset! s 10))
                             (inc value)))))
        (is (= 2 @calls))
        (is (= 11 @s))
        (is (= 2 (:generation (signal/get-signal-state s))))))
    (verify-boundaries! rt)))

(deftest public-then-native-track-does-not-reuse-another-signals-interval
  (let [rt (runtime) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [public (signal/signal 1) raw (owned/signal rt :raw 99)
            task (owned/cspin rt :mixed
                              [(iv/get-new (owned/track (::rtp/signal-source (meta public))))
                               (iv/get-new (owned/track raw))])]
        (owned/observe! rt task #(swap! values conj %) #(throw %))
        (is (= [[1 99]] @values))
        (owned/set-signal! rt raw 100)
        (is (= [1 100] (last @values)))))
    (verify-boundaries! rt)))

(deftest finalization-retains-public-owned-signal-payload-without-reactivating-work
  (let [rt (runtime) finish (atom nil) local (atom nil) cleanup (atom []) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [task (spin (let [s (signal/signal 4)]
                         (reset! local s)
                         (try
                           (await-finalization (fn [r _] (reset! finish r)))
                           (finally
                             (swap! cleanup conj @s)
                             (swap! s inc)
                             (swap! cleanup conj @s)))))
            reason (ex-info "cancel public source" {})]
        (task #(swap! values conj [:ok %]) #(swap! values conj [:error %]))
        (rtp/cancel-computation! rt task (spin-core/spin-id task) (spin-core/spin-body task) reason)
        (is (= [[:error reason]] @values))
        (is (empty? @cleanup))
        (@finish :done)
        (is (= [4 5] @cleanup))
        (is (empty? (:cleanup-cells (owned/snapshot rt))))
        (is (nil? (get-in (owned/snapshot rt) [:entities (:id @local)])))
        (is (some? (try @@local nil (catch #?(:clj Throwable :cljs :default) error error))))))
    (verify-boundaries! rt)))

(deftest reentrant-watches-preserve-first-commit-batch-publication-order
  (let [rt (runtime) values (atom []) order (atom [])]
    (binding [ec/*execution-context* rt]
      (let [a (signal/signal 0) b (signal/signal 0)
            parent (spin [(iv/get-new (track a)) (iv/get-new (track b))])]
        (observe! parent values)
        (add-watch a :nested (fn [_ _ _ _] (reset! b 2)))
        (signal/batch
         (reset! a 1)
         (reset! order @signal/*batched-signal-ids*))
        (is (= [(:id a) (:id b)] @order))
        (is (= [[0 0] [1 2]] @values))))
    (verify-boundaries! rt)))

(deftest explicit-signal-construction-selects-the-requested-world-root
  (let [caller (runtime) destination (runtime) result (atom nil)]
    (binding [ec/*execution-context* caller]
      (let [task (spin (reset! result (signal/signal destination 7)) :done)]
        (task (fn [_]) #(throw %))))
    (is (= 7 (rtp/public-signal-value destination @result)))
    (is (nil? (get-in (owned/snapshot caller) [:entities (:id @result)])))
    (is (= owned/root (get-in (owned/snapshot destination) [:entities (:id @result) :owner])))
    (verify-boundaries! caller)
    (verify-boundaries! destination)))

(deftype EqualityTrap []
  #?@(:clj [Object (equals [_ _] (throw (ex-info "unexpected equality" {}))) (hashCode [_] 0)]
      :cljs [IEquiv (-equiv [_ _] (throw (ex-info "unexpected equality" {})))]))

(deftest ordinary-signal-writes-do-not-observe-payload-equality
  ;; Opaque host equality is checked directly; the scalar cases above replay
  ;; these same lifetime transitions using symbolic model values.
  (doseq [engine [:simple :owned]]
    (let [rt (context/create-execution-context {:engine engine :audit? false})
          a (EqualityTrap.) b (EqualityTrap.)]
      (binding [ec/*execution-context* rt]
        (let [s (signal/signal a)]
          (is (identical? b (reset! s b)))
          (is (identical? b @s))
          (is (identical? a (swap! s (constantly a))))
          (is (identical? a @s))))
      (when (= :simple engine) (context/stop-context! rt)))))

(deftest empty-batch-does-not-require-an-execution-context
  (binding [ec/*execution-context* nil]
    (is (= 42 (signal/batch 42)))
    #?(:cljs (is (= 43 (signal/batch* (fn [] 43)))))))

(deftest stale-public-signal-cannot-read-or-track-a-replacement-allocation
  (let [rt (runtime) escaped (atom nil) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [task (spin (let [s (signal/signal 1)] (reset! escaped s) :done))]
        (observe! task values))
      (let [old @escaped
            replacement (signal/register-signal! rt (signal/->SignalRef (:id old) 9))
            errors (atom [])
            reader (spin (iv/get-new (track old)))]
        (is (= 9 @replacement))
        (is (some? (try @old nil (catch #?(:clj Throwable :cljs :default) error error))))
        (reader (fn [_] (is false "Stale track resumed")) #(swap! errors conj %))
        (is (= 1 (count @errors)))
        (is (= 9 @replacement))))
    (verify-boundaries! rt)))

#?(:clj
   (deftest concurrent-public-signal-writes-do-not-lose-commits-or-stall-the-drain
     ;; Exercise the actual public route without retaining diagnostic history.
     (let [rt (context/create-execution-context {:engine :owned :audit? false})
           values (atom []) watches (atom 0) errors (atom [])]
       (binding [ec/*execution-context* rt]
         (let [s (signal/signal 0)
               task (spin (iv/get-new (track s)))]
           (add-watch s :count (fn [_ _ _ _] (swap! watches inc)))
           (task #(swap! values conj %) #(swap! errors conj %))
           (let [workers (doall (repeatedly 4 #(future (dotimes [_ 100] (swap! s inc)))))
                 timeout (Object.)]
             (doseq [worker workers]
               (is (not (identical? timeout (deref worker 10000 timeout))))))
           (is (= 400 @s))
           (is (= 400 (:generation (signal/get-signal-state s))))
           (is (= 400 @watches))
           (is (= 400 (last @values)))
           (is (empty? @errors))
           (is (= {:variant :ok :payload 400 :clean? true}
                  (rtp/computation-result rt task (spin-core/spin-id task)))))))))
