(ns org.replikativ.spindel.engine.native-retirement-reentry-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.protocols :as rtp]))

;; Only exported native APIs and protocol operations; no mutable row access.
;; The typed constructor invalidates B lazily; the native observation then
;; executes its new generation under the explicitly selected current A Run.
(deftest mixed-entity-and-run-ownership-retirement-is-not-reentrant
  (let [rt (c/runtime {:audit? true})
        driver (c/signal rt :driver 0)
        ticket (c/ticket :a-park)
        a-handle (atom nil) a-owner (atom nil)
        errors (atom [])
        b (c/cspin rt :b
                   (reset! a-handle
                           (c/cspin rt :a
                                    (reset! a-owner (lifetime/current-scope rt))
                                    (c/park ticket)))
                   (c/track driver))
        descriptor-target #?(:clj (Object.) :cljs (js-obj))]
    (binding [ec/*execution-context* rt]
      (c/observe! rt b (fn [_]) (fn [error] (swap! errors conj [:b-first error])))
      (let [original-a @a-handle]
        ;; A's allocation belongs to B1; its separately invoked Run is Root-owned.
        (c/observe! rt original-a (fn [_]) (fn [error] (swap! errors conj [:a error])))
        (let [before (c/snapshot rt)
              a-run (first (for [[r row] (:runs before) :when (= :a (:spin row))] r))]
          (is (= (:root before) (get-in before [:runs a-run :owner])))
          ;; Descriptor replacement is a supported lazy invalidation operation.
          (rtp/register-computation!
           rt descriptor-target :b
           (with-meta (:body b) {::rtp/computation {:captured-locals {:replacement true}}}))
          (binding [ec/*owner-scope* @a-owner]
            (c/observe! rt b (fn [_]) (fn [error] (swap! errors conj [:b-second error]))))
          (let [ready (c/snapshot rt)
                b-run (first (for [[r row] (:runs ready) :when (= :b (:spin row))] r))]
            ;; Guard the witness itself: independent Run ancestry is acyclic,
            ;; whereas adding entity lifetime edges would make a union cycle.
            (is (= :parked (get-in ready [:runs a-run :status])))
            (is (= :completed (get-in ready [:runs b-run :status])))
            (is (= a-run (get-in ready [:runs b-run :owner])))
            (is (= b-run (get-in ready [:entities :a :owner])))
            (let [failure (try (c/cancel-spin! rt original-a) nil
                               (catch #?(:clj Throwable :cljs :default) error error))]
              (is (nil? failure) (str "Recursive retirement corrupted native storage: " failure))
              (when-not failure
                (is (empty? (:runs (c/snapshot rt))))
                (is (= {:a 1 :b-first 1 :b-second 1}
                       (frequencies (map first @errors))))
                ;; Reuse pooled arrays while all fresh Runs stay live. Duplicate
                ;; pool entries alias concurrent Runs and lose these identities.
                (let [fresh (mapv (fn [id]
                                    (let [h (c/cspin rt id (c/park (c/ticket id)))]
                                      (c/observe! rt h (fn [_]) (fn [_])) h))
                                  [:fresh-1 :fresh-2 :fresh-3])
                      state (c/snapshot rt)]
                  (is (= (set (map :id fresh)) (set (map :spin (vals (:runs state))))))
                  (is (= 3 (:live-runs (c/storage-stats rt)))))))))))))

(deftest scope-retirement-is-not-reentrant-through-a-child-run
  (let [rt (c/runtime {:audit? true})
        driver (c/signal rt :driver 0)
        ticket (c/ticket :a-park)
        a-handle (atom nil) a-owner (atom nil) scope-holder (atom nil)
        errors (atom [])
        b (c/cspin rt :b
                   (reset! a-handle
                           (c/cspin rt :a
                                    (reset! a-owner (lifetime/current-scope rt))
                                    (c/park ticket)))
                   (c/track driver))
        descriptor-target #?(:clj (Object.) :cljs (js-obj))]
    (binding [ec/*execution-context* rt]
      (c/observe! rt b (fn [_]) (fn [error] (swap! errors conj [:b-first error])))
      (let [original-a @a-handle]
        ;; A's allocation belongs to B1; its separately invoked Run is Root-owned.
        (c/observe! rt original-a (fn [_]) (fn [error] (swap! errors conj [:a error])))
        (let [before (c/snapshot rt)
              a-run (first (for [[r row] (:runs before) :when (= :a (:spin row))] r))]
          (is (= (:root before) (get-in before [:runs a-run :owner])))
          ;; Descriptor replacement is a supported lazy invalidation operation.
          (rtp/register-computation!
           rt descriptor-target :b
           (with-meta (:body b) {::rtp/computation {:captured-locals {:replacement true}}}))
          (reset! scope-holder (lifetime/open-scope! rt :reentry @a-owner))
          (binding [ec/*owner-scope* @scope-holder]
            (c/observe! rt b (fn [_]) (fn [error] (swap! errors conj [:b-second error]))))
          (let [ready (c/snapshot rt)
                b-run (first (for [[r row] (:runs ready) :when (= :b (:spin row))] r))]
            ;; Guard the witness itself: independent Run ancestry is acyclic,
            ;; whereas adding entity lifetime edges would make a union cycle.
            (is (= :parked (get-in ready [:runs a-run :status])))
            (is (= :completed (get-in ready [:runs b-run :status])))
            (is (= [:scope :id 0] (get-in ready [:runs b-run :owner])))
            (is (= a-run (get-in ready [:scopes [:scope :id 0] :parent])))
            (is (= b-run (get-in ready [:entities :a :owner])))
            (let [failure (try (lifetime/close-scope! rt @scope-holder) nil
                               (catch #?(:clj Throwable :cljs :default) error error))]
              (is (nil? failure) (str "Recursive Scope retirement corrupted native storage: " failure))
              (when-not failure
                (let [closed (c/snapshot rt)]
                  (is (empty? (:runs closed)))
                  (is (= 0 (:scope-balance closed)))
                  (is (= #{(:root closed)} (set (keys (:scopes closed))))))
                (is (true? (rtp/execution-owner-joined? rt @scope-holder)))
                (is (nil? (lifetime/close-scope! rt @scope-holder)))
                (is (= 0 (:scope-balance (c/snapshot rt))))
                (is (= {:a 1 :b-first 1 :b-second 1}
                       (frequencies (map first @errors))))
                ;; Reuse pooled arrays while all fresh Runs stay live. Duplicate
                ;; pool entries alias concurrent Runs and lose these identities.
                (let [fresh (mapv (fn [id]
                                    (let [h (c/cspin rt id (c/park (c/ticket id)))]
                                      (c/observe! rt h (fn [_]) (fn [_])) h))
                                  [:fresh-1 :fresh-2 :fresh-3])
                      state (c/snapshot rt)]
                  (is (= (set (map :id fresh)) (set (map :spin (vals (:runs state))))))
                  (is (= 3 (:live-runs (c/storage-stats rt)))))))))))))

(deftest native-sibling-freezes-ancestry-after-a-completed-ancestor-is-forgotten
  (let [rt (c/runtime {:audit? true}) driver (c/signal rt :driver 0) a-driver (c/signal rt :a-driver 0)
        a (atom nil) a-owner (atom nil) s (atom nil) before (atom nil)
        failure (atom nil) errors (atom []) during (atom nil) during-joined (atom nil)
        b (c/cspin rt :z-parent
                   (reset! a (c/cspin rt :a-child
                                      (reset! a-owner (lifetime/current-scope rt))
                                      (c/track a-driver)))
                   (c/track driver))]
    (binding [ec/*execution-context* rt]
      (c/observe! rt b (fn [_]) #(swap! errors conj [:b-first %]))
      (c/observe! rt @a (fn [_]) #(swap! errors conj [:a %]))
      (rtp/register-computation!
       rt #?(:clj (Object.) :cljs (js-obj)) :z-parent
       (with-meta (:body b) {:org.replikativ.spindel.engine.protocols/computation
                             {:captured-locals {:replacement true}}}))
      (reset! s (lifetime/open-scope! rt :sibling @a-owner))
      (binding [ec/*owner-scope* @s]
        (c/observe! rt b (fn [_]) #(swap! errors conj [:b-second %])))
      (let [x (c/cspin rt :zz-sibling
                       ;; This ordinary body is physically executing while its
                       ;; own Scope cancels B2 before reaching sibling X.
                       (reset! before (c/snapshot rt))
                       (reset! failure
                               (try (lifetime/close-scope! rt @s) nil
                                    (catch #?(:clj Throwable :cljs :default) error error)))
                       (when-not @failure
                         (reset! during (c/snapshot rt))
                         (reset! during-joined (rtp/execution-owner-joined? rt @s)))
                       :body-return)]
        (binding [ec/*owner-scope* @s]
          (c/observe! rt x (fn [_]) #(swap! errors conj [:x %]))))
      (let [runs (:runs @before)
            a-run (first (for [[r row] runs :when (= :a-child (:spin row))] r))
            b-run (first (for [[r row] runs :when (= :z-parent (:spin row))] r))
            x-run (first (for [[r row] runs :when (= :zz-sibling (:spin row))] r))]
        (is (= (:root @before) (get-in runs [a-run :owner])))
        (is (= :completed (get-in runs [a-run :status])))
        (is (= [:scope :id 0] (get-in runs [b-run :owner])))
        (is (= [:scope :id 0] (get-in runs [x-run :owner])))
        (is (= b-run (get-in @before [:entities :a-child :owner])))
        (is (nil? @failure) (str "Later sibling lost its ancestor: " @failure))
        (when-not @failure
          (is (nil? (get-in @during [:runs a-run]))))
        (when-not @failure
          (is (= :unwinding (get-in @during [:runs x-run :status]))))
        (when-not @failure
          (is (= [x-run [:scope :id 0] a-run (:root @before) (second (:root @before))]
                 (get-in @during [:runs x-run :anchor]))))
        (when-not @failure
          (is (false? @during-joined))
          (is (true? (rtp/execution-owner-joined? rt @s)))
          (let [after (c/snapshot rt)]
            (is (= 0 (:scope-balance after)))
            (is (= #{(:root after)} (set (keys (:scopes after)))))
            (is (empty? (:runs after)))))))))
