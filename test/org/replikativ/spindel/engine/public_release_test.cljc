(ns org.replikativ.spindel.engine.public-release-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.lifecycle :as lifecycle]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.signal :as signal]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]))

(defn- runtime [] (context/create-execution-context {:engine :owned}))
(defn- failure [f]
  (try (f) nil (catch #?(:clj Throwable :cljs :default) error error)))

(deftest release-selects-the-explicit-decorated-world-and-is-repeatable
  (let [a (runtime) b (runtime) calls (atom [])
        decorated (assoc a :bindings {:application/scope :selected})
        reason (ex-info "first release" {})
        completion (binding [ec/*execution-context* b]
                     (context/release-context! decorated reason))]
    (is (satisfies? rtp/PWorldRelease completion))
    (is (identical? completion (context/release-context! a (ex-info "ignored" {}))))
    (let [detach (completion #(swap! calls conj [:joined %]) #(swap! calls conj [:error %]))]
      (is (ifn? detach))
      (is (= [[:joined nil]] @calls))
      (detach)
      (detach)
      (is (= [[:joined nil]] @calls)))
    (is (failure #(binding [ec/*execution-context* decorated] (signal/signal 1))))
    (binding [ec/*execution-context* b]
      (let [source (signal/signal 1)]
        (is (= 2 (swap! source inc)))))
    (context/release-context! b)))

(deftest release-retains-cleanup-state-through-two-sequential-acknowledgements
  (let [rt (runtime) trace (atom []) errors (atom []) joined (atom [])
        reason (ex-info "release with cleanup" {})]
    (binding [ec/*execution-context* rt]
      (let [pending (sync/deferred) first-ack (sync/deferred) second-ack (sync/deferred)
            target
            (spin
             (let [cell (ratom/atom 41)]
               (try
                 (await pending)
                 (finally
                   (swap! trace conj [:cleanup @cell])
                   (let [value (await-finalization
                                (fn [succeed fail]
                                  (first-ack
                                   (fn [x]
                                     (second-ack (fn [y] (succeed (+ x y))) fail))
                                   fail)))]
                     (swap! cell + value)
                     (swap! trace conj [:returned @cell]))))))]
        (target #(swap! trace conj [:unexpected %]) #(swap! errors conj %))
        (let [completion (context/release-context! rt reason)]
          (is (= [[:cleanup 41]] @trace))
          (is (= 1 (count @errors)))
          (is (identical? reason (first @errors)))
          (let [detach (lifecycle/observe! completion #(swap! joined conj [:detached %]) #(throw %))]
            (detach)
            (detach))
          (lifecycle/observe! completion #(swap! joined conj [:joined %]) #(throw %))
          (is (empty? @joined))
          (is (failure #(rtp/read-public-deferred rt first-ack)))
          (is (failure #(pending (fn [_]) (fn [_]))))
          (is (identical? completion (context/release-context! rt (ex-info "repeat" {}))))
          (is (true? (first-ack 1)))
          (is (= [[:cleanup 41]] @trace))
          (is (empty? @joined))
          (is (true? (second-ack 2)))
          (is (= [[:cleanup 41] [:returned 44]] @trace))
          (is (= [[:joined nil]] @joined)))))))

(deftest another-native-world-can-await-release-without-owning-its-cleanup
  (let [a (runtime) b (runtime) values (atom [])
        completion (context/release-context! a)]
    (binding [ec/*execution-context* b]
      (let [observer (spin (await completion) :joined)]
        (observer #(swap! values conj %) #(throw %))
        (is (= [:joined] @values))))
    (context/release-context! b)))

(deftest release-observers-preserve-the-callers-context
  (let [a (runtime) b (runtime) completion (context/release-context! a)
        observed (atom [])]
    (binding [ec/*execution-context* b]
      (completion
       (fn [_]
         (swap! observed conj (identical? b ec/*execution-context*))
         (let [source (signal/signal 1)]
           (swap! observed conj (swap! source inc))))
       #(throw %)))
    (is (= [true 2] @observed))
    (context/release-context! b)))

(deftest an-observer-fault-does-not-revise-joining-or-strand-other-observers
  (let [rt (runtime) calls (atom []) observer-error (ex-info "observer failed" {})]
    (binding [ec/*execution-context* rt]
      (let [pending (sync/deferred) ack (sync/deferred)
            target (spin (try (await pending) (finally (await-finalization ack))))]
        (target (fn [_]) (fn [_]))
        (let [completion (context/release-context! rt)]
          (lifecycle/observe! completion (fn [_] (throw observer-error)) #(throw %))
          (lifecycle/observe! completion #(swap! calls conj %) #(throw %))
          (is (identical? observer-error (failure #(ack 1))))
          (is (= [nil] @calls))
          (is (identical? completion (context/release-context! rt)))
          (completion #(swap! calls conj %) #(throw %))
          (is (= [nil nil] @calls)))))))

#?(:clj
   (deftest logical-release-does-not-certify-a-running-bodys-return
     (let [rt (runtime) entered (promise) resume (promise) values (atom []) joined (atom [])
           returned (atom false)
           target (binding [ec/*execution-context* rt]
                    (spin-core/make-spin
                     (fn [succeed _]
                       (try
                         (deliver entered true)
                         (when-not (= true (deref resume 5000 ::timeout))
                           (throw (ex-info "Physical release test timed out" {})))
                         (succeed :late)
                         (finally (reset! returned true))))
                     :release-physical {}))
           worker (future (binding [ec/*execution-context* rt]
                            (target #(swap! values conj [:ok %]) #(swap! values conj [:error %]))))]
       (try
         (is (= true (deref entered 5000 ::timeout)))
         (let [completion (context/release-context! rt)]
           (lifecycle/observe! completion #(swap! joined conj %) #(throw %))
           (is (false? @returned))
           (is (empty? @joined)))
         (finally (deliver resume true)))
       (is (not= ::timeout (deref worker 5000 ::timeout)))
       (is (true? @returned))
       (is (= [nil] @joined))
       (is (= [:error] (mapv first @values))))))
