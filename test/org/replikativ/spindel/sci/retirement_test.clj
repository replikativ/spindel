(ns org.replikativ.spindel.sci.retirement-test
  (:require [clojure.test :refer [deftest is]]
            [sci.core :as sci]
            [sci.impl.world :as sci-world]
            [org.replikativ.spindel.engine.component :as component]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.sci.world :as world]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.yggdrasil.construction :as construction]))

(defn- error-type [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn- create! [runtime]
  (world/create! runtime {:spindel-primitives? false}))

(deftest explicit-child-retirement-preserves-parent-and-sibling
  (let [parent (context/create-execution-context)
        ref (create! parent)
        original (world/context-in parent ref)
        _ (sci/eval-string* original "(def n (atom 0)) (def pending (map (fn [_] (swap! n inc)) [1 2]))")
        child (context/fork-context parent :mode :frozen)
        sibling (context/fork-context parent :mode :frozen)
        child-heap (world/context-in child ref)
        sibling-heap (world/context-in sibling ref)
        saved (sci/eval-string* child-heap "pending")]
    (try
      (is (= 1 (first saved)))
      (is (nil? (world/retire-in! child ref child-heap)))
      (is (thrown-with-msg? Exception #"retired" (first saved)))
      (is (thrown-with-msg? Exception #"not available" (world/context-in child ref)))
      (is (nil? (sci/retire! child-heap)) "Retrying exact heap cleanup is idempotent")
      (is (= [1 2] (sci/eval-string* sibling-heap "(vec pending)")))
      (is (= 0 (sci/eval-string* original "@n")))
      (is (= [1 2] (sci/eval-string* original "(vec pending)")))
      (finally
        (sci/retire! child-heap)
        (world/retire-in! sibling ref sibling-heap)
        (world/retire-in! parent ref original)
        (context/close-context! child)
        (context/close-context! sibling)
        (context/close-context! parent)))))

(deftest cleanup-failure-retains-exact-component-for-retry
  (let [runtime (context/create-execution-context)
        ref (create! runtime)
        heap (world/context-in runtime ref)
        retire sci/retire!
        failure (ex-info "Cleanup failed before ACK" {})
        calls (atom [])]
    (try
      (with-redefs [sci/retire! (fn [selected]
                                  (swap! calls conj selected)
                                ;; A failed cleanup can already have closed its heap.
                                  (retire selected)
                                  (throw failure))]
        (is (identical? failure (try (world/retire-in! runtime ref heap)
                                     (catch Exception e e)))))
      (is (= 1 (count @calls)))
      (is (identical? heap (world/context-in runtime ref)))
      (is (nil? (world/retire-in! runtime ref heap)))
      (is (thrown-with-msg? Exception #"not available" (world/context-in runtime ref)))
      (finally (retire heap) (context/close-context! runtime)))))

(deftest stale-missing-and-shared-lookups-do-not-grant-retirement-authority
  (let [runtime (context/create-execution-context)
        ref (create! runtime)
        original (world/context-in runtime ref)
        replacement (sci/fork original)
        shared (binding [ec/*execution-context* runtime]
                 (component/register! (component/shared original)))]
    (try
      (is (not (satisfies? component/PComponentRetirement
                           (component/shared (world/->InterpreterWorld original)))))
      (world/replace-context! runtime ref original replacement)
      (is (= ::world/stale-context
             (error-type #(world/retire-in! runtime ref original))))
      (is (= ::world/not-interpreter
             (error-type #(world/retire-in! runtime shared original))))
      (is (= 3 (sci/eval-string* original "(+ 1 2)")) "Replacement publication retains old heap")
      (is (= 4 (sci/eval-string* replacement "(+ 2 2)")))
      (binding [ec/*execution-context* runtime] (component/unregister! ref))
      (is (= ::world/not-interpreter
             (error-type #(world/retire-in! runtime ref replacement))))
      (is (= 5 (sci/eval-string* replacement "(+ 2 3)")) "Missing lookup is not cleanup ACK")
      (finally
        (sci/retire! replacement)
        (sci/retire! original)
        (context/close-context! runtime)))))

(deftest a-replacement-cannot-be-unregistered-by-a-stale-release
  (let [runtime (context/create-execution-context)
        ref (create! runtime)
        original (world/context-in runtime ref)
        replacement (sci/fork original)
        retire sci/retire!]
    (try
      ;; Deliberately violate the caller's exclusion contract to exercise the
      ;; defensive final identity check; it must still preserve the replacement.
      (with-redefs [sci/retire! (fn [heap]
                                  (retire heap)
                                  (world/replace-context! runtime ref original replacement))]
        (is (= ::world/stale-context
               (error-type #(world/retire-in! runtime ref original)))))
      (is (identical? replacement (world/context-in runtime ref)))
      (is (= 42 (sci/eval-string* replacement "42")))
      (finally
        (retire original)
        (world/retire-in! runtime ref replacement)
        (context/close-context! runtime)))))

(deftest failed-unpublished-sci-target-remains-owned-until-cleanup-ack
  (doseq [fork [(fn [runtime] (context/fork-context runtime :mode :frozen))
                (fn [runtime] (binding [ec/*execution-context* runtime]
                                (ygg/fork! {:mode :frozen :sync? true})))]]
    (let [runtime (context/create-execution-context)
          ref (create! runtime)
          heap (world/context-in runtime ref)
          source (:sci.impl/world heap)
          cache (atom {source :source})
          fail? (atom true)
          copies (atom 0)
          original (ex-info "Fork cache refused" {:test-refusal true})
          cache-owner (reify
                        sci-world/IForkableWorldCache
                        (-fork-world-cache! [_ _ target]
                          (swap! copies inc)
                          (swap! cache assoc target :unpublished)
                          (throw original))
                        sci-world/IWorldCache
                        (-retire-world-cache! [_ selected]
                          (when @fail? (throw (ex-info "Cleanup before ACK refused" {})))
                          (swap! cache dissoc selected)))]
      (try
        (sci/call-with-context heap #(sci-world/register-world-cache! cache-owner))
        (let [error (try (fork runtime) nil (catch Exception e e))
              owner (:construction/owner (ex-data error))]
          (is (construction/owner? owner))
          (is (= 1 @copies))
          (is (= 2 (count @cache)) "The exact unpublished target remains owned")
          (is (= :component-recovery (:kind (first (:receipts (construction/info owner))))))
          (is (not (contains? (first (:receipts (construction/info owner))) :resource)))
          (is (= :source-alive (sci/eval-string* heap ":source-alive")))
          (reset! fail? false)
          (construction/dispose! owner {:sync? true})
          (construction/dispose! owner {:sync? true})
          (is (= 1 @copies) "Recovery never repeats the fork")
          (is (= {source :source} @cache))
          (is (= :closed (:status (construction/info owner))))
          (is (= :source-alive (sci/eval-string* heap ":source-alive"))))
        (finally
          (reset! fail? false)
          (world/retire-in! runtime ref heap)
          (context/close-context! runtime))))))
