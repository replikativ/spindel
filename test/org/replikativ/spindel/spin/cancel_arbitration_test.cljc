(ns org.replikativ.spindel.spin.cancel-arbitration-test
  "Regression (#117): every way a parked or inline-resumed await continuation
  can be resumed — completion, inline completion, cancellation, race settle —
  resumes it exactly once.

  Each test drives one interleaving deterministically: the cancellation is
  injected at the exact point (a redef of the step before it, or the awaited
  child's own body), never by timing. Each counts the resolve, reject and
  `finally` invocations, so a slice resumed twice fails as surely as one that
  is stranded. The redef tests are JVM-only; the rest run on both platforms."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]))

(defn- recorder
  "Callbacks that log every invocation, and the log."
  []
  (let [calls (atom [])]
    {:calls calls
     :resolve (fn [v] (swap! calls conj [:resolved v]) v)
     :reject (fn [e] (swap! calls conj [:rejected (:type (ex-data e))]) nil)}))

(def ^:private cancelled [:rejected spin-core/spin-cancelled])

(defn- in-context [f]
  (let [context (ctx/create-execution-context)]
    (try
      (binding [ec/*execution-context* context]
        (f context))
      (finally
        (ctx/stop-context! context)))))

(defn- parked [s]
  (ec/get-state [:await-conts (spin-core/spin-id s)]))

(defn- live-parked
  "The continuations still a cancellation target: parked, not advanced."
  [s]
  (into {} (remove (fn [[_ c]] (or (::simple/resume-claimed? c)
                                   (::simple/resumed? c))))
        (parked s)))

;; -----------------------------------------------------------------------------
;; 1. A child await registered after cancel-spin! read the parked conts
;; -----------------------------------------------------------------------------

#?(:clj
   (deftest a-child-await-that-parks-while-its-parent-is-cancelled-is-rejected
     (in-context
      (fn [context]
        (let [d (sync/create-deferred context)
              child (spin (await d))
              finals (atom 0)
              parent (spin (try (await child) (finally (swap! finals inc))))
              {:keys [calls resolve reject]} (recorder)
              fired (atom false)
              track ec/deps-track-spin!]
          ;; The parent passed the await's entry check; it is cancelled before
          ;; its child continuation is registered (cancel-spin! finds nothing to
          ;; reject), then registers and parks on a child that never completes.
          (with-redefs [ec/deps-track-spin!
                        (fn [sid aid]
                          (when (and (= sid (spin-core/spin-id parent))
                                     (compare-and-set! fired false true))
                            (spin-core/cancel-spin! parent))
                          (track sid aid))]
            (parent resolve reject))
          (is @fired)
          (is (= [cancelled] @calls) "the parent is rejected with the cancellation, once")
          (is (= 1 @finals) "its finally runs once")
          (is (empty? (live-parked parent)) "no continuation stays parked")
          (is (nil? (ec/spin-current-result (spin-core/spin-id child)))
              "the child is not started"))))))

;; -----------------------------------------------------------------------------
;; 2. Inline child completion vs cancellation
;; -----------------------------------------------------------------------------

(deftest a-child-completing-inline-after-its-parent-was-cancelled-does-not-resume-it-again
  (testing "the child completes synchronously; the parent is cancelled while it runs"
    (in-context
     (fn [_]
       (let [parent-ref (atom nil)
             finals (atom 0)
             child (spin (do (spin-core/cancel-spin! @parent-ref) :v))
             parent (spin (try (await child) (finally (swap! finals inc))))
             {:keys [calls resolve reject]} (recorder)]
         (reset! parent-ref parent)
         (parent resolve reject)
         (is (= [cancelled] @calls) "cancellation owns the slice: rejected once, never resolved")
         (is (= 1 @finals) "the finally runs once")
         (is (empty? (live-parked parent))))))))

#?(:clj
   (deftest a-cached-child-does-not-resume-a-parent-cancelled-after-registration
     (testing "the child has a cached result; the parent is cancelled after its cont is registered"
       (in-context
        (fn [_]
          (let [child (spin :v)
                _ (child identity identity)
                finals (atom 0)
                parent (spin (try (await child) (finally (swap! finals inc))))
                {:keys [calls resolve reject]} (recorder)
                fired (atom false)
                add! ec/continuation-add!]
            (with-redefs [ec/continuation-add!
                          (fn [sid cont]
                            (let [ret (add! sid cont)]
                              (when (and (= sid (spin-core/spin-id parent))
                                         (compare-and-set! fired false true))
                                (spin-core/cancel-spin! parent))
                              ret))]
              (parent resolve reject))
            (is @fired)
            (is (= 1 (count @calls)) "resumed exactly once")
            (is (= 1 @finals) "the finally runs once")
            (is (= [cancelled] @calls) "cancellation linearized first and owns the slice")
            (is (empty? (live-parked parent)))))))))

(deftest a-cancelled-parent-that-already-moved-past-a-child-await-is-rejected-once
  (testing "a resumed reactive await is no longer a place to reject the body"
    (in-context
     (fn [context]
       (let [d (sync/create-deferred context)
             child (spin :a)
             finals (atom 0)
             parent (spin (try (await child) (await d) (finally (swap! finals inc))))
             {:keys [calls resolve reject]} (recorder)]
         (parent resolve reject)
         (is (= [] @calls) "parked on the deferred")
         (spin-core/cancel-spin! parent)
         (is (= [cancelled] @calls))
         (is (= 1 @finals))
         (is (empty? (live-parked parent))))))))

(deftest cancelling-a-completed-parent-does-not-re-run-its-reject-path
  (in-context
   (fn [_]
     (let [child (spin :a)
           finals (atom 0)
           parent (spin (try (await child) (finally (swap! finals inc))))
           {:keys [calls resolve reject]} (recorder)]
       (parent resolve reject)
       (is (= [[:resolved :a]] @calls))
       (spin-core/cancel-spin! parent)
       (is (= [[:resolved :a]] @calls) "a completed spin's callbacks do not fire again")
       (is (= 1 @finals))))))

#?(:clj
   (deftest a-queued-completion-and-the-inline-path-deliver-one-result-once
     (testing "the child's pending completion is processed after the parent registered"
       (in-context
        (fn [context]
          (let [child (spin :v)
                _ (child identity identity)
                cid (spin-core/spin-id child)
                finals (atom 0)
                parent (spin (try (await child) (finally (swap! finals inc))))
                {:keys [calls resolve reject]} (recorder)
                fired (atom false)
                add! ec/continuation-add!]
            (with-redefs [ec/continuation-add!
                          (fn [sid cont]
                            (let [ret (add! sid cont)]
                              (when (and (= sid (spin-core/spin-id parent))
                                         (compare-and-set! fired false true))
                                ;; the drain processes the child's completion now
                                (simple/process-event! context {:type :spin-completion :id cid}))
                              ret))]
              (parent resolve reject))
            (is @fired)
            (is (= [[:resolved :v]] @calls) "one completion, one resume")
            (is (= 1 @finals))))))))

#?(:clj
   (deftest a-delayed-inline-claim-does-not-re-deliver-an-earlier-completion
     (testing "completions A and B are queued-delivered before the inline path claims A"
       (in-context
        (fn [context]
          (let [child (spin :a)
                _ (child identity identity)
                cid (spin-core/spin-id child)
                finals (atom 0)
                parent (spin (try (await child) (finally (swap! finals inc))))
                {:keys [calls resolve reject]} (recorder)
                fired (atom false)
                add! ec/continuation-add!]
            (with-redefs [ec/continuation-add!
                          (fn [sid cont]
                            (let [ret (add! sid cont)]
                              (when (and (= sid (spin-core/spin-id parent))
                                         (compare-and-set! fired false true))
                                (simple/process-event! context {:type :spin-completion :id cid})
                                (ec/spin-cache-result! cid (spin-core/ok :b))
                                (simple/process-event! context {:type :spin-completion :id cid}))
                              ret))]
              (parent resolve reject))
            (is @fired)
            (is (= [[:resolved :a] [:resolved :b]] @calls) "two completions, two resumes")
            (is (= 2 @finals))))))))

#?(:clj
   (deftest an-inline-delivery-is-not-repeated-by-the-queued-completion
     (testing "the queued completion of the same result is skipped, a re-completion is not"
       (in-context
        (fn [context]
          (let [child (spin :v)
                _ (child identity identity)
                cid (spin-core/spin-id child)
                finals (atom 0)
                parent (spin (try (await child) (finally (swap! finals inc))))
                {:keys [calls resolve reject]} (recorder)]
            (parent resolve reject)
            (is (= [[:resolved :v]] @calls))
            (simple/process-event! context {:type :spin-completion :id cid})
            (is (= [[:resolved :v]] @calls) "the same completion reaches the await once")
            (is (= 1 @finals))
            (is (seq (parked parent)) "the reactive edge survives")
            (ec/spin-cache-result! cid (spin-core/ok :w))
            (simple/process-event! context {:type :spin-completion :id cid})
            (is (= [[:resolved :v] [:resolved :w]] @calls) "a re-completion still re-fires")
            (is (= 2 @finals))))))))

#?(:clj
   (deftest a-fork-does-not-inherit-the-parents-in-flight-claim
     (in-context
      (fn [context]
        (let [d (sync/create-deferred context)
              child (spin (await d))
              finals (atom 0)
              parent (spin (try (await child) (finally (swap! finals inc))))
              pid (spin-core/spin-id parent)
              _ (parent identity identity)
              [cont-id] (keys (parked parent))
              result (spin-core/ok :x)
              ;; a queued completion claimed it in the parent world and has
              ;; not resumed the slice yet when the fork is taken
              held (simple/claim-continuation-for-resume! context pid cont-id {:result result})
              fork (ctx/fork-context context)]
          (is held "claimed in the parent world")
          (is (nil? (simple/claim-continuation-for-resume! context pid cont-id {:result (spin-core/ok :y)}))
              "busy in the parent world")
          (binding [ec/*execution-context* fork]
            (spin-core/cancel-spin! parent))
          (is (= 1 @finals) "cancelling in the fork rejects the slice the fork never resumed")
          (let [fork2 (ctx/fork-context context)]
            (is (some? (simple/claim-continuation-for-resume! fork2 pid cont-id {:result result}))
                "the same completion is still deliverable in a fork")))))))

#?(:clj
   (deftest a-queued-resume-delivers-the-result-it-claimed
     (testing "the child re-completes between the claim and the resume"
       (in-context
        (fn [context]
          (let [d (sync/create-deferred context)
                child (spin (await d))
                cid (spin-core/spin-id child)
                parent (spin (await child))
                {:keys [calls resolve reject]} (recorder)
                claim! simple/claim-continuation-for-resume!
                fired (atom false)]
            (parent resolve reject)
            (ec/spin-cache-result! cid (spin-core/ok :a))
            (with-redefs [simple/claim-continuation-for-resume!
                          (fn [& args]
                            (let [ret (apply claim! args)]
                              (when (compare-and-set! fired false true)
                                (ec/spin-cache-result! cid (spin-core/ok :b)))
                              ret))]
              (simple/process-event! context {:type :spin-completion :id cid}))
            (simple/process-event! context {:type :spin-completion :id cid})
            (is (= [[:resolved :a] [:resolved :b]] @calls)
                "each completion is delivered once, with its own result")))))))

#?(:clj
   (deftest a-stale-cancellation-re-check-leaves-a-newer-registration-alone
     (in-context
      (fn [_]
        (let [d (sync/create-deferred ec/*execution-context*)
              s (spin (await d))
              sid (spin-core/spin-id s)
              rejected (atom 0)
              reg (fn [r] {:id ::slot :registration r :kind :await-once
                           :event-key [:test/slot sid] :on-resume (fn [_] nil)})
              a (reg :a)
              b (reg :b)]
          (s identity identity)
          (ec/continuation-add! sid a)
          ;; a resumed A, its slice registered B at the same id
          (ec/continuation-add! sid b)
          (spin-core/abort-spin-chain! sid (ex-info "cancelled" {:type spin-core/spin-cancelled}))
          (is (= {:result spin-core/incomplete}
                 (spin-core/cancelled-after-registration sid a (fn [_] (swap! rejected inc)))))
          (is (zero? @rejected) "A's reject is not run for B")
          (is (= :b (:registration (get (parked s) ::slot))) "B stays registered"))))))

;; -----------------------------------------------------------------------------
;; 3. Direct cancellation of an in-flight race
;; -----------------------------------------------------------------------------

(deftest cancelling-an-in-flight-race-rejects-it
  (in-context
   (fn [context]
     (let [d1 (sync/create-deferred context)
           d2 (sync/create-deferred context)
           a (spin (await d1))
           b (spin (await d2))
           r (comb/race a b)
           {:keys [calls resolve reject]} (recorder)]
       (r resolve reject)
       (is (= [] @calls))
       (spin-core/cancel-spin! r)
       (is (= [cancelled] @calls) "the race's own callback fires with the cancellation")
       (is (empty? (parked r)) "its fan-out continuation is spent")
       (is (spin-core/spin-cancelled? a))
       (is (spin-core/spin-cancelled? b))
       (spin-core/cancel-spin! r)
       (is (= [cancelled] @calls) "a second cancellation settles nothing")))))

#?(:clj
   (deftest a-race-cancelled-before-its-fan-out-is-registered-is-rejected
     (in-context
      (fn [context]
        (let [d1 (sync/create-deferred context)
              d2 (sync/create-deferred context)
              r (comb/race (spin (await d1)) (spin (await d2)))
              {:keys [calls resolve reject]} (recorder)
              fired (atom false)
              add! ec/continuation-add!]
          (with-redefs [ec/continuation-add!
                        (fn [sid cont]
                          (when (and (= sid (spin-core/spin-id r))
                                     (compare-and-set! fired false true))
                            (spin-core/cancel-spin! r))
                          (add! sid cont))]
            (r resolve reject))
          (is @fired)
          (is (= [cancelled] @calls))
          (is (empty? (parked r))))))))

#?(:clj
   (deftest a-generation-sweep-during-cancel-spin-does-not-strand-a-race
     (in-context
      (fn [context]
        (let [d1 (sync/create-deferred context)
              d2 (sync/create-deferred context)
              r (comb/race (spin (await d1)) (spin (await d2)))
              {:keys [calls resolve reject]} (recorder)
              abort spin-core/abort-spin-chain!]
          (r resolve reject)
          (with-redefs [spin-core/abort-spin-chain!
                        (fn [sid err]
                          (abort sid err)
                          ;; a signal change's generation sweep runs between
                          ;; cancel-spin!'s cache write and its read of the conts
                          (when (= sid (spin-core/spin-id r))
                            (simple/clear-all-await-continuations! context)))]
            (spin-core/cancel-spin! r))
          (is (= [cancelled] @calls)))))))

#?(:clj
   (defn- settled-calls
     "The calls once something settled (or 2 s passed), after a grace period
     in which a duplicate settlement would show up."
     [calls]
     (loop [n 0]
       (when (and (empty? @calls) (< n 200))
         (Thread/sleep 10)
         (recur (inc n))))
     (Thread/sleep 50)
     @calls))

#?(:clj
   (deftest a-late-delivery-does-not-settle-a-cancelled-race
     (in-context
      (fn [context]
        (let [d1 (sync/create-deferred context)
              d2 (sync/create-deferred context)
              finals (atom 0)
              a (spin (try (await d1) (finally (swap! finals inc))))
              b (spin (try (await d2) (finally (swap! finals inc))))
              r (comb/race a b)
              {:keys [calls resolve reject]} (recorder)]
          (r resolve reject)
          (Thread/sleep 50)
          (spin-core/cancel-spin! r)
          (sync/deliver! d1 :late)
          (is (= [cancelled] (settled-calls calls)))
          (is (= 2 @finals) "each child unwinds once"))))))

#?(:clj
   (deftest a-race-settles-once-when-cancelled-while-its-winner-completes
     (in-context
      (fn [context]
        (let [race-ref (atom nil)
              d (sync/create-deferred context)
              a (spin (do (spin-core/cancel-spin! @race-ref) :a))
              b (spin (await d))
              r (comb/race a b)
              {:keys [calls resolve reject]} (recorder)]
          (reset! race-ref r)
          (r resolve reject)
          (is (= [cancelled] (settled-calls calls))
              "the cancellation claimed the race first; the winner settles nothing"))))))
