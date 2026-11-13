(ns org.replikativ.spindel.v2.port.spawned-child-trampoline-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.port.support2 :as h]))

(use-fixtures :each h/fixture)

(defn- looper [k]
  (spin (loop [i 0] (if (< i 3) (do (await (spin i)) (recur (inc i))) [k i]))))

(defn- settle-loop [d]
  (comb/spawn! (spin (loop [i 0]
                       (if (< i 3)
                         (do (await (spin nil)) (recur (inc i))) i)))
               {:on-success d}))

(deftest a-child-spawned-from-a-body-runs-its-loop
  (let [d (v2/deferred)]
    (is (= :ok (h/result (spin (comb/spawn! (looper :x) {:on-success d}) :ok))))
    (is (= [:x 3] (h/result d)))))

(deftest a-child-spawned-from-a-loop-body-runs-its-loop
  (let [ds [(v2/deferred) (v2/deferred)]]
    (is (= :parent-done
           (h/result (spin (loop [j 0]
                             (if (< j 2)
                               (do (comb/spawn! (looper j) {:on-success (ds j)}) (recur (inc j)))
                               :parent-done))))))
    (is (= [[0 3] [1 3]] (mapv h/result ds)))))

(deftest a-child-spawned-after-an-await-runs-its-loop
  (let [ready (v2/deferred) d (v2/deferred)
        parent (spin (await ready) (comb/spawn! (looper :after) {:on-success d}) :ok)]
    (v2/value-async parent (fn [_ _]))
    (ready :go)
    (is (= :ok (h/result parent)))
    (is (= [:after 3] (h/result d)))))

(deftest a-loop-started-by-a-spawn-callback-runs-to-its-end
  (let [ok (v2/deferred) failed (v2/deferred)]
    (is (= :parent-done
           (h/result (spin (comb/spawn! (spin :child) {:on-success (fn [_] (settle-loop ok))})
                           (comb/spawn! (spin (throw (ex-info "child" {}))) {:on-error (fn [_] (settle-loop failed))})
                           :parent-done))))
    (is (= [3 3] (mapv h/result [ok failed])))))

(deftest a-loop-started-by-a-what-if-watch-callback-runs-to-its-end
  ;; A frozen fork plus observe! replaces the old what-if view/watch facade.
  (let [child (v2/fork! v2/*world*) d (promise)
        watched (v2/host-call! child #(binding [v2/*world* child] (spin :watched)))
        stop (v2/observe! watched (fn [_ err?]
                                    (when-not err?
                                      (binding [v2/*world* child]
                                        (comb/spawn! (looper :watch) {:on-success #(deliver d %)})))))]
    (try (is (= [:watch 3] (deref d 2000 ::timeout)))
         (finally (stop)))))

(deftest a-throw-in-a-later-iteration-rejects-the-spin
  (let [rejections (atom 0)
        s (spin (loop [i 0]
                  (when (= i 1) (throw (ex-info "bounce-error" {})))
                  (await (spin nil)) (recur (inc i))))]
    (comb/spawn! s {:on-error (fn [_] (swap! rejections inc))})
    (is (= "bounce-error" (h/result (spin (try (await s) (catch Exception e (ex-message e)))))))
    (is (= 1 @rejections))))

(deftest a-throw-in-a-loop-started-by-a-spawn-callback-reaches-its-handler
  (let [handled (atom 0) escaped (atom nil)]
    (try
      (comb/spawn! (spin :now)
                   {:on-success (fn [_]
                                  (comb/spawn!
                                   (spin (loop [i 0]
                                           (when (= i 1) (throw (ex-info "callback-bounce" {})))
                                           (await (spin nil)) (recur (inc i))))
                                   {:on-error (fn [_] (swap! handled inc))}))})
      (catch Throwable e (reset! escaped e)))
    (is (nil? @escaped)) (is (= 1 @handled))))

(deftest parallel-children-run-inline-run-their-loops
  (is (= [[:a 3] [:b 3]] (h/result (comb/parallel (looper :a) (looper :b))))))

(deftest race-children-run-inline-run-their-loops
  (is (= [:a 3] (h/result (comb/race (looper :a) (looper :b))))))

(deftest work-children-run-inline-run-their-loops
  (let [gate (v2/deferred) dx (v2/deferred) dy (v2/deferred)
        parent (task (await gate)
                     (let [x (task (deliver dx (await (looper :x))))
                           y (task (deliver dy (await (looper :y))))]
                       (v2/await-all [x y]) :done))]
    (gate :go)
    (is (= :done (h/result parent)))
    (is (= [[:x 3] [:y 3]] (mapv h/result [dx dy])))))

(deftest a-cps-task-run-inline-by-the-synchronous-executor-runs-its-loop
  (is (= [:task 3]
         (h/result (task (await (task (loop [i 0]
                                        (if (< i 3) (do (await (spin i)) (recur (inc i))) [:task i])))))))))

(deftest ^:gap a-generator-loops-before-its-first-yield
  ;; The old async sequence generator is a user-facing facility, but v2
  ;; currently exposes neither gen-aseq/yield nor anext.
  (let [gen (ns-resolve 'org.replikativ.spindel.v2.core 'gen-aseq)
        anext (ns-resolve 'org.replikativ.spindel.v2.core 'anext)]
    (is (some? gen) "v2 needs an async generator macro")
    (is (some? anext) "v2 needs async sequence consumption")
    (when (and gen anext)
      (is (= 3 (eval '(let [g (org.replikativ.spindel.v2.core/gen-aseq
                               (loop [i 0]
                                 (if (< i 3)
                                   (do (org.replikativ.spindel.v2.core/await (org.replikativ.spindel.v2.core/spin i))
                                       (recur (inc i)))
                                   (org.replikativ.spindel.v2.core/yield i))))]
                        (org.replikativ.spindel.v2.port.support/result
                         (org.replikativ.spindel.v2.core/spin
                          (first (org.replikativ.spindel.v2.core/await
                                  (org.replikativ.spindel.v2.core/anext g))))))))))))

(deftest a-partial-cps-loop-over-fresh-spins-runs-to-its-end
  (is (= 3 (h/result (spin (loop [i 0]
                             (if (< i 3) (do (await (spin i)) (recur (inc i))) i)))))))

(deftest a-partial-cps-loop-over-a-cached-spin-runs-to-its-end
  (let [s (spin :cached)]
    (is (= :cached (h/result s)))
    (is (= [:cached :cached :cached]
           (h/result (spin (loop [i 0 acc []]
                             (if (< i 3) (recur (inc i) (conj acc (await s))) acc))))))))

(deftest a-partial-cps-loop-catching-a-cached-cancellation-runs-to-its-end
  (let [never (v2/deferred) t (task (await never))]
    (v2/cancel-task! t)
    (is (v2/cancelled? (h/result t)))
    (is (= 3 (h/result (spin (loop [i 0 caught 0]
                               (if (< i 3)
                                 (recur (inc i) (try (await t) caught (catch Exception _ (inc caught))))
                                 caught))))))))

(deftest a-loop-over-an-already-discarded-scope-runs-to-its-end
  ;; The v2 equivalent is discarding a fork. A repeated discard should
  ;; settle harmlessly, as the old scope's discard did. Use offload for H4.
  (let [child (v2/fork! v2/*world*)]
    (v2/discard! child)
    (is (= 3 (h/result (spin (loop [i 0]
                               (if (< i 3)
                                 (do (v2/offload (fn [] (v2/discard! child)))
                                     (recur (inc i)))
                                 i))))))))
