(ns org.replikativ.spindel.engine.await-prefix-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.kernel :as kernel]
            [org.replikativ.spindel.lifetime.model :as model]
            [org.replikativ.spindel.engine.impl.owned :as owned #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def w [:w 0])

(defn- fixture [root-owned?]
  (let [await-o (if root-owned? [:o 3] [:o 1])
        late-o (if root-owned? [:o 4] [:o 3])
        actions (vec (concat
                      [{:t :t02 :w w :e :a :value 0}
                       {:t :t02 :w w :e :b :value 0}
                       {:t :t04 :w w :e :parent :mode :callback}]
                      (when root-owned? [{:t :t04 :w w :e :child :mode :callback}])
                      (when-not root-owned?
                        [{:t :t05 :w w :r [:parent 1] :kind :await-reactive
                          :debtor [:entity w :child] :order 0}])
                      [{:t :t05 :w w :r [:child 1] :kind :track :debtor [:entity w :a] :order 0}
                       {:t :t07 :w w :r [:child 1] :value 0}]
                      (when root-owned?
                        [{:t :t05 :w w :r [:parent 1] :kind :await-reactive
                          :debtor [:entity w :child] :order 0}])
                      [{:t :t06 :w w :o await-o :value 0}
                       {:t :t05 :w w :r [:parent 1] :kind :track :debtor [:entity w :b] :order 1}
                       {:t :t07 :w w :r [:parent 1] :value [0 0]}
                       {:t :t08 :w w :e :parent :value [0 0]}]))]
    {:actions actions :await-o await-o :late-o late-o}))

(deftest consumed-await-prefix-survives-later-track-and-refreshes-on-its-own-trigger
  (doseq [root-owned? [false true]]
    (let [{:keys [actions await-o late-o]} (fixture root-owned?)
          initial (reduce model/step (model/init-state) actions)
          later [{:t :signal-write :w w :e :b :value 1}
                 {:t :t08 :w w :e :b :value 1}]
          finish [{:t :t07 :w w :r [:parent 2] :value [0 1]}
                  {:t :t08 :w w :e :parent :value [0 1]}]
          earlier [{:t :signal-write :w w :e :a :value 1}
                   {:t :t08 :w w :e :a :value 1}
                   {:t :t07 :w w :r [:child 2] :value 1}
                   {:t :t08 :w w :e :child :value 1}]
          new-await (if root-owned? [:o 5] [:o 4])
          fresh [{:t :t05 :w w :r [:parent 3] :kind :await-reactive
                  :debtor [:entity w :child] :order 0}
                 {:t :t06 :w w :o new-await :value 1}
                 {:t :t05 :w w :r [:parent 3] :kind :track :debtor [:entity w :b] :order 1}
                 {:t :t07 :w w :r [:parent 3] :value [1 1]}
                 {:t :t08 :w w :e :parent :value [1 1]}]
          handoff! (fn [s]
                     (doseq [o [await-o late-o]]
                       (is (= [:run w [:parent 2]]
                              (get-in s [:worlds w :obligations o :creditor]))))
                     (is (= (if root-owned? [:root w] [:parent 2])
                            (:owner (model/ent s w :child)))))
          after-finish! (fn [s]
                          (handoff! s)
                          (is (nil? (model/run s w [:parent 1])))
                          (is (= [0 1] (:result (model/ent s w :parent)))))
          trigger! (fn [s]
                     (is (= [:parent 3] (model/current s w :parent)))
                     (is (= [:run w [:parent 2]]
                            (get-in s [:worlds w :obligations await-o :creditor]))
                         "The triggering await must re-register and reread its debtor"))]
      ;; These assertions are semantic expectations, independently of refinement.
      (let [handoff (reduce model/step initial later)
            finished (reduce model/step handoff finish)
            triggered (reduce model/step finished earlier)]
        (handoff! handoff)
        (when-not root-owned?
          (is (= [:parent 2] (:owner (model/run handoff w [:child 1])))))
        (after-finish! finished)
        (trigger! triggered)
        (is (= [1 1] (:result (model/ent (reduce model/step triggered fresh) w :parent)))))
      (doseq [cells? [false true]]
        (let [actual (kernel/restore (model/init-state) {:cells? cells?})
              expected (atom (model/init-state))
              apply! (fn [xs]
                       (doseq [action xs]
                         (swap! expected model/step action)
                         (kernel/step! actual action)
                         (is (= (:worlds @expected) (:worlds (kernel/snapshot actual))))))]
          (apply! (concat actions later))
          (handoff! (kernel/snapshot actual))
          (when-not root-owned?
            (is (= [:parent 2] (:owner (model/run (kernel/snapshot actual) w [:child 1])))))
          (apply! finish)
          (after-finish! (kernel/snapshot actual))
          (apply! earlier)
          (trigger! (kernel/snapshot actual))
          (apply! fresh)
          (is (= [1 1] (:result (model/ent (kernel/snapshot actual) w :parent)))))))))

(deftest native-await-prefix-keeps-root-owned-and-cold-parent-owned-children-reactive
  (doseq [root-owned? [false true]]
    (let [rt (owned/runtime {:audit? true}) a (owned/signal rt :a 0)
          b (owned/signal rt :b 0) values (atom [])
          child (owned/cspin rt :child (iv/get-new (owned/track a)))
          parent (owned/cspin rt :parent
                              (let [x (owned/await child) y (iv/get-new (owned/track b))]
                                [x y]))]
      (when root-owned? (owned/observe! rt child (fn [_]) #(throw %)))
      (owned/observe! rt parent #(swap! values conj %) #(throw %))
      (owned/set-signal! rt b 1)
      (let [state (owned/snapshot rt)
            generation (last (sort-by second (for [[id run] (:runs state)
                                                   :when (= :parent (:spin run))] id)))]
        (is (= (if root-owned? [:root owned/w] generation)
               (get-in state [:entities :child :owner]))))
      (owned/set-signal! rt a 1)
      (is (= [[0 0] [0 1] [1 1]] @values))
      (verify-boundaries! rt))))

(deftest native-await-prefix-survives-a-parked-successor
  (let [rt (owned/runtime {:audit? true}) a (owned/signal rt :a 0)
        b (owned/signal rt :b 0) gate (owned/ticket :suffix) values (atom [])
        child (owned/cspin rt :child (iv/get-new (owned/track a)))
        parent (owned/cspin rt :parent
                            (let [x (owned/await child) y (iv/get-new (owned/track b))]
                              (when (pos? y) (owned/park gate))
                              [x y]))]
    (owned/observe! rt parent #(swap! values conj %) #(throw %))
    (owned/set-signal! rt b 1)
    (let [obsolete (owned/pending-ticket rt gate)]
      (owned/set-signal! rt a 1)
      (let [current (owned/pending-ticket rt gate)]
        (is (not= obsolete current))
        (owned/resume-ticket! rt obsolete :obsolete)
        (is (= [[0 0]] @values))
        (owned/resume-ticket! rt current :ready)))
    (is (= [[0 0] [1 1]] @values))
    (verify-boundaries! rt)))

(deftest suffix-await-ownership-stays-with-the-basis-and-cancelling-the-successor-releases-only-its-child
  (let [{:keys [actions]} (fixture false)
        initial-actions (vec (concat (drop-last 2 actions)
                                     [{:t :t05 :w w :r [:parent 1] :kind :await-reactive
                                       :debtor [:entity w :suffix] :order 2}
                                      {:t :t07 :w w :r [:suffix 1] :value :suffix}
                                      {:t :t06 :w w :o [:o 4] :value :suffix}]
                                     (take-last 2 actions)))
        initial (reduce model/step (model/init-state) initial-actions)
        reentry {:t :t09 :w w :e :parent :cause :track :order 1}
        completion {:t :t07 :w w :r [:parent 2] :value [0 1]}
        cancellation {:t :t11 :w w :r [:parent 2]}
        handoff! (fn [s]
                   (is (= [:parent 2] (:owner (model/ent s w :child))))
                   (is (= [:parent 1] (:owner (model/ent s w :suffix))))
                   (is (= [:parent 1] (:owner (model/run s w [:suffix 1]))))
                   (is (= [:run w [:parent 1]]
                          (get-in s [:worlds w :obligations [:o 4] :creditor]))))
        finished! (fn [s]
                    (is (some? (model/ent s w :child)))
                    (is (nil? (model/ent s w :suffix)))
                    (is (nil? (get-in s [:worlds w :obligations [:o 4]]))))
        cancelled! (fn [s]
                     (is (nil? (model/ent s w :child)))
                     (is (nil? (model/run s w [:child 1]))))]
    (let [handoff (model/step initial reentry)
          finished (model/step handoff completion)]
      (handoff! handoff)
      (finished! finished)
      (cancelled! (model/step finished cancellation)))
    (doseq [cells? [false true]]
      (let [actual (kernel/restore initial {:cells? cells?})]
        (kernel/step! actual reentry)
        (handoff! (kernel/snapshot actual))
        (kernel/step! actual completion)
        (finished! (kernel/snapshot actual))
        (kernel/step! actual cancellation)
        (cancelled! (kernel/snapshot actual))))))

(deftest foreign-await-prefix-transfer-never-adopts-the-foreign-child
  (let [v [:w 1]
        initial-actions
        [{:t :t02 :w w :e :a :value 0}
         {:t :t04 :w w :e :child :mode :callback}
         {:t :t05 :w w :r [:child 1] :kind :track :debtor [:entity w :a] :order 0}
         {:t :t07 :w w :r [:child 1] :value 0}
         {:t :t19 :w w :v v :k [:k 0] :scope [:root w] :systems #{}}
         {:t :t02 :w v :e :b :value 0}
         {:t :t04 :w v :e :parent :mode :callback}
         {:t :t05 :w v :r [:parent 1] :kind :await-reactive :debtor [:entity w :child] :order 0}
         {:t :t06 :w v :o [:o 3] :value 0}
         {:t :t05 :w v :r [:parent 1] :kind :track :debtor [:entity v :b] :order 1}
         {:t :t07 :w v :r [:parent 1] :value [0 0]}]
        initial (reduce model/step (model/init-state) initial-actions)
        reentry {:t :t09 :w v :e :parent :cause :track :order 1}
        check! (fn [s]
                 (is (= (model/wr initial w) (model/wr s w)))
                 (is (= [:run v [:parent 2]]
                        (get-in s [:worlds v :obligations [:o 3] :creditor]))))]
    (check! (model/step initial reentry))
    (doseq [cells? [false true]]
      (let [actual (kernel/restore initial {:cells? cells?})]
        (kernel/step! actual reentry)
        (check! (kernel/snapshot actual))))))

(deftest native-triggering-await-refreshes-the-child-error-variant
  (let [rt (owned/runtime {:audit? true}) a (owned/signal rt :a 0)
        b (owned/signal rt :b 0) values (atom []) error (ex-info "child failed" {})
        child (owned/cspin rt :child
                           (let [x (iv/get-new (owned/track a))]
                             (if (zero? x) x (throw error))))
        parent (owned/cspin rt :parent
                            (let [x (try (owned/await child)
                                         (catch #?(:clj Throwable :cljs :default) caught
                                           (if (identical? error caught) :child-error (throw caught))))
                                  y (iv/get-new (owned/track b))]
                              [x y]))]
    (owned/observe! rt parent #(swap! values conj %) #(throw %))
    (owned/set-signal! rt b 1)
    (owned/set-signal! rt a 1)
    (is (= [[0 0] [0 1] [:child-error 1]] @values))
    (verify-boundaries! rt)))
