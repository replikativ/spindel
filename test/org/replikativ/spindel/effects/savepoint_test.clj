(ns org.replikativ.spindel.effects.savepoint-test
  "The laws of docs/savepoints.md."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.savepoint :as sp :refer [savepoint]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [outcome (deref result 5000 ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok (first outcome)) (second outcome) (throw (second outcome))))))

(defn- accumulate!
  "World state the program writes between its sites."
  [n]
  (rtp/swap-state! ec/*execution-context* [:test/acc] (fn [acc] (+ (or acc 0) n))))

(defn- program []
  (spin
   (let [a (savepoint :step 1)]
     (accumulate! a)
     (let [b (savepoint :step 2)]
       (accumulate! b)
       [a b (rtp/get-state ec/*execution-context* [:test/acc])]))))

(defn- take! [queue]
  (let [value (.poll ^java.util.concurrent.LinkedBlockingQueue queue
                     5 java.util.concurrent.TimeUnit/SECONDS)]
    (when (nil? value) (throw (ex-info "No savepoint event arrived" {})))
    value))

(defmacro ^:private with-session [[root session events handlers] & body]
  `(let [~root (context/create-execution-context)
         ~events (java.util.concurrent.LinkedBlockingQueue.)
         post# (fn [event#] (.put ~events event#))
         ~session (sp/open! ~root {:seed 7
                                   :fork-opts {:systems :none}
                                   :handlers (merge {sp/any-site post#} ~handlers)})]
     (try
       ~@body
       (finally
         (await-cps (sp/close! ~session))
         (context/stop-context! ~root)))))

(deftest identity-without-a-handler
  (let [root (context/create-execution-context)]
    (try
      (binding [ec/*execution-context* root]
        (is (= [1 2 3] @(program))))
      (finally (context/stop-context! root)))))

(deftest resume-continues-with-the-handlers-value
  (with-session [root session events {}]
    (sp/start! session (binding [ec/*execution-context* root] (program)))
    (let [first-site (take! events)]
      (is (= [:step 1 0] ((juxt :savepoint/site :savepoint/payload :savepoint/seq) first-site)))
      (sp/resume first-site 10))
    (let [second-site (take! events)]
      (is (= 1 (:savepoint/seq second-site)))
      (sp/resume second-site 20))
    (let [end (take! events)]
      (is (= sp/result-site (:savepoint/site end)))
      (is (= [10 20 30] (:savepoint/payload end))))))

(deftest a-fork-starts-from-the-state-at-its-site
  (with-session [root session events {}]
    (sp/start! session (binding [ec/*execution-context* root] (program)))
    (let [first-site (take! events)
          anchor (await-cps (sp/fork first-site))]
      (testing "the original runs to its end"
        (sp/resume first-site 1)
        (sp/resume (take! events) 2)
        (is (= [1 2 3] (:savepoint/payload (take! events)))))
      (testing "the anchor is still at the first site, with nothing accumulated"
        (is (sp/pending? anchor))
        (is (nil? (rtp/get-state (:savepoint/world anchor) [:test/acc]))))
      (testing "forks of the anchor are independent continuations"
        (doseq [[a b] [[10 20] [100 200]]]
          (let [branch (await-cps (sp/fork anchor))]
            (is (not= (sp/seed (:savepoint/world branch))
                      (sp/seed (:savepoint/world anchor))))
            (sp/resume branch a)
            (let [second-site (take! events)]
              (is (= (:fork-id (:savepoint/world branch))
                     (:fork-id (:savepoint/world second-site))))
              (sp/resume second-site b))
            (is (= [a b (+ a b)] (:savepoint/payload (take! events)))))))
      (testing "the root is untouched by its forks"
        (is (= 3 (rtp/get-state root [:test/acc])))))))

(deftest fork-seeds-are-reproducible-and-distinct
  (let [seeds (fn []
                (with-session [root session events {}]
                  (sp/start! session (binding [ec/*execution-context* root] (program)))
                  (let [site (take! events)]
                    (mapv #(sp/seed (:savepoint/world %))
                          [(await-cps (sp/fork site)) (await-cps (sp/fork site))]))))
        first-run (seeds)]
    (is (= 2 (count (set first-run))))
    (is (= first-run (seeds)))))

(deftest a-savepoint-is-resumed-at-most-once-in-its-world
  (with-session [root session events {}]
    (sp/start! session (binding [ec/*execution-context* root] (program)))
    (let [site (take! events)]
      (sp/resume site 1)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not pending" (sp/resume site 1)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not pending"
                            (await-cps (sp/fork site)))))))

(deftest a-fork-may-run-under-other-handlers
  (with-session [root session events {}]
    (sp/start! session (binding [ec/*execution-context* root] (program)))
    (let [site (take! events)
          seen (java.util.concurrent.LinkedBlockingQueue.)
          ;; the child answers :step itself and reports only its end
          child (await-cps (sp/fork site {:handlers {:step (fn [s] (sp/resume s 5))
                                                     sp/result-site #(.put seen %)}}))]
      (sp/resume child 4)
      (is (= [4 5 9] (:savepoint/payload (take! seen))))
      (is (nil? (.poll events 200 java.util.concurrent.TimeUnit/MILLISECONDS))
          "the inherited catch-all saw nothing of the child"))))

(deftest close-unwinds-pending-worlds-and-discards-them
  (let [root (context/create-execution-context)
        events (java.util.concurrent.LinkedBlockingQueue.)
        session (sp/open! root {:fork-opts {:systems :none}
                                :handlers {sp/any-site #(.put events %)}})]
    (try
      (sp/start! session (binding [ec/*execution-context* root] (program)))
      (let [site (take! events)]
        (await-cps (sp/fork site))
        (await-cps (sp/fork site)))
      (await-cps (sp/close! session))
      (is (= :discarded (:status @(:scope session))))
      (is (empty? (:activities @(:scope session))))
      (finally (context/stop-context! root)))))

;; -----------------------------------------------------------------------------
;; Addresses
;; -----------------------------------------------------------------------------

(defn- branching-program []
  (spin
   (let [extra? (savepoint :flag true)]
     (when extra? (savepoint :extra 1))
     (loop [i 0 seen []]
       (if (< i 3)
         (recur (inc i) (conj seen (savepoint :item i)))
         (savepoint :tail seen))))))

(defn- addresses-of
  "Run `branching-program` answering :flag with `extra?`; site -> addresses."
  [extra?]
  (with-session [root session events {}]
    (sp/start! session (binding [ec/*execution-context* root] (branching-program)))
    (loop [seen {}]
      (let [event (take! events)]
        (if (:savepoint/terminal? event)
          seen
          (do (sp/resume event (if (= :flag (:savepoint/site event))
                                 extra?
                                 (:savepoint/payload event)))
              (recur (update seen (:savepoint/site event) (fnil conj [])
                             (:savepoint/address event)))))))))

(deftest a-site-keeps-its-address-when-upstream-control-flow-changes
  (let [with-extra (addresses-of true)
        without-extra (addresses-of false)]
    (is (= 1 (count (:extra with-extra))))
    (is (nil? (:extra without-extra)))
    (testing "downstream of the branch"
      (is (= (:tail with-extra) (:tail without-extra)))
      (is (= (:item with-extra) (:item without-extra))))
    (testing "occurrences of one site are distinct and ordered alike"
      (is (= 3 (count (set (:item with-extra))))))
    (testing "and the same in a second execution"
      (is (= with-extra (addresses-of true))))))

(deftest a-fork-mints-the-addresses-its-source-would
  (with-session [root session events {}]
    (sp/start! session (binding [ec/*execution-context* root] (branching-program)))
    (let [flag (take! events)
          anchor (await-cps (sp/fork flag))
          run (fn [sp-value]
                (sp/resume sp-value false)
                (loop [seen []]
                  (let [event (take! events)]
                    (if (:savepoint/terminal? event)
                      seen
                      (do (sp/resume event (:savepoint/payload event))
                          (recur (conj seen (:savepoint/address event))))))))
          original (run flag)]
      (is (= 4 (count original)))
      (is (= original (run (await-cps (sp/fork anchor))))))))

(deftest close-wins-against-a-world-that-is-still-running
  ;; The world is between two sites when the session closes: whichever of
  ;; close! and the next savepoint comes second must see the other.
  (dotimes [_ 50]
    (let [root (context/create-execution-context)
          events (java.util.concurrent.LinkedBlockingQueue.)
          session (sp/open! root {:fork-opts {:systems :none}
                                  :handlers {sp/any-site #(.put events %)}})]
      (try
        (sp/start! session (binding [ec/*execution-context* root] (program)))
        (sp/resume (take! events) 1)
        (await-cps (sp/close! session))
        (is (= :discarded (:status @(:scope session))))
        (finally (context/stop-context! root))))))

;; -----------------------------------------------------------------------------
;; Law 1 inside a session; abandon; failures of handlers
;; -----------------------------------------------------------------------------

(deftest a-site-without-a-handler-is-the-identity-inside-a-session
  (let [root (context/create-execution-context)
        ends (java.util.concurrent.LinkedBlockingQueue.)
        session (sp/open! root {:fork-opts {:systems :none}
                                :handlers {:other-site (fn [_] (throw (ex-info "unreachable" {})))
                                           sp/result-site #(.put ends %)}})]
    (try
      (sp/start! session (binding [ec/*execution-context* root] (program)))
      (is (= [1 2 3] (:savepoint/payload (take! ends))))
      (is (empty? (sp/pending root)))
      (finally
        (await-cps (sp/close! session))
        (context/stop-context! root)))))

(defn- guarded-program [log]
  (spin
   (try
     (let [a (savepoint :step 1)]
       (swap! log conj [:continued a])
       a)
     (finally (swap! log conj :finally)))))

(deftest abandon-unwinds-the-computation-and-consumes-the-savepoint
  (let [log (atom [])]
    (with-session [root session events {}]
      (sp/start! session (binding [ec/*execution-context* root] (guarded-program log)))
      (let [site (take! events)]
        (sp/abandon site)
        (let [end (take! events)]
          (is (= sp/abandoned-site (:savepoint/site end)))
          (is (:savepoint/terminal? end)))
        (is (= [:finally] @log) "finally ran, the body did not continue")
        (is (not (sp/pending? site)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not pending" (sp/resume site 1)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not pending" (sp/abandon site)))))))

(deftest a-consumed-savepoint-stays-consumed-in-a-forked-world
  (with-session [root session events {}]
    (sp/start! session (binding [ec/*execution-context* root] (program)))
    (let [branch (await-cps (sp/fork (take! events)))]
      (sp/resume branch 1)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not pending" (sp/resume branch 1)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not pending"
                            (await-cps (sp/fork branch)))))))

(deftest a-handler-that-throws-fails-the-computation-once
  (let [seen (atom nil)
        ends (java.util.concurrent.LinkedBlockingQueue.)
        root (context/create-execution-context)
        session (sp/open! root {:fork-opts {:systems :none}
                                :handlers {:step (fn [s]
                                                   (reset! seen s)
                                                   (throw (ex-info "handler boom" {})))
                                           sp/error-site #(.put ends %)
                                           sp/result-site #(.put ends %)}})]
    (try
      (sp/start! session (binding [ec/*execution-context* root] (program)))
      (let [end (take! ends)]
        (is (= sp/error-site (:savepoint/site end)))
        (is (= "handler boom" (ex-message (:savepoint/payload end)))))
      (is (not (sp/pending? @seen)) "the failed site cannot re-enter the computation")
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not pending" (sp/resume @seen 1)))
      (is (nil? (.poll ends 200 java.util.concurrent.TimeUnit/MILLISECONDS)))
      (finally
        (await-cps (sp/close! session))
        (context/stop-context! root)))))

(deftest a-terminal-handler-that-throws-does-not-end-the-computation-twice
  (let [ends (atom [])
        root (context/create-execution-context)
        session (sp/open! root {:fork-opts {:systems :none}
                                :handlers {:step (fn [s] (sp/resume s (:savepoint/payload s)))
                                           sp/result-site (fn [event]
                                                            (swap! ends conj (:savepoint/site event))
                                                            (throw (ex-info "terminal boom" {})))
                                           sp/error-site #(swap! ends conj (:savepoint/site %))}})]
    (try
      (sp/start! session (binding [ec/*execution-context* root] (program)))
      ;; long enough for a second terminal to arrive if one were produced
      (Thread/sleep 300)
      (finally
        (await-cps (sp/close! session))
        (context/stop-context! root)))
    (is (= [sp/result-site] @ends))))

(deftest a-session-runs-one-computation
  (with-session [root session events {}]
    (sp/start! session (binding [ec/*execution-context* root] (program)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"one computation"
                          (sp/start! session (binding [ec/*execution-context* root]
                                               (program)))))))

;; -----------------------------------------------------------------------------
;; Concurrency
;; -----------------------------------------------------------------------------

(defn- race!
  "Run the thunks at once; returns their outcomes."
  [thunks]
  (let [gate (java.util.concurrent.CountDownLatch. 1)
        runs (mapv (fn [thunk]
                     (future (.await gate)
                             (try [:ok (thunk)]
                                  (catch Throwable error
                                    [:error (:type (ex-data error))]))))
                   thunks)]
    (.countDown gate)
    (mapv deref runs)))

(deftest exactly-one-of-concurrent-resumes-and-abandons-wins
  (dotimes [_ 20]
    (with-session [root session events {}]
      (sp/start! session (binding [ec/*execution-context* root] (program)))
      (let [site (take! events)
            outcomes (race! (concat (repeat 4 #(sp/resume site 1))
                                    (repeat 4 #(sp/abandon site))))]
        (is (= 1 (count (filter #(= :ok (first %)) outcomes))))
        (is (= 7 (count (filter #(= [:error ::sp/not-pending] %) outcomes))))
        ;; exactly one continuation ran: a second site, or an abandoned end
        (is (some? (take! events)))
        (is (nil? (.poll events 50 java.util.concurrent.TimeUnit/MILLISECONDS)))))))

(deftest a-fork-that-loses-to-a-resume-is-rejected-not-resolved-empty
  (dotimes [_ 40]
    (with-session [root session events {}]
      (sp/start! session (binding [ec/*execution-context* root] (program)))
      (let [site (take! events)
            [forked _] (race! [#(await-cps (sp/fork site)) #(sp/resume site 1)])]
        (if (= :ok (first forked))
          (do (is (some? (:savepoint/address (second forked))))
              (is (sp/pending? (second forked))))
          (is (= [:error ::sp/not-pending] forked)))))))

;; -----------------------------------------------------------------------------
;; A synchronous executor and a handler that resumes inline
;; -----------------------------------------------------------------------------

(deftest inline-resumes-do-not-grow-the-stack
  (let [sites 5000
        root (context/create-execution-context :executor (executor/synchronous-executor))
        end (promise)
        session (sp/open! root {:fork-opts {:systems :none}
                                :handlers {:tick (fn [s] (sp/resume s (:savepoint/payload s)))
                                           sp/result-site #(deliver end (:savepoint/payload %))
                                           sp/error-site #(deliver end (:savepoint/payload %))}})]
    (try
      (sp/start! session
                 (binding [ec/*execution-context* root]
                   (spin (loop [i 0 sum 0]
                           (if (< i sites)
                             (recur (inc i) (+ sum (savepoint :tick i)))
                             sum)))))
      (is (= (reduce + (range sites)) (deref end 20000 ::timeout)))
      (finally
        (await-cps (sp/close! session))
        (context/stop-context! root)))))

;; -----------------------------------------------------------------------------
;; Durable boundary
;; -----------------------------------------------------------------------------

(deftest process-local-savepoint-state-does-not-serialize
  (with-session [root session events {}]
    (sp/start! session (binding [ec/*execution-context* root] (program)))
    (take! events)
    (let [edn (context/serialize-context root)]
      (is (not (re-find #":savepoint/(session|handlers|pending|task)" edn)))
      (is (re-find #":savepoint/seed" edn)))))

(deftest an-abandoned-world-is-given-back-before-the-session-ends
  (with-session [root session events {}]
    (sp/start! session (binding [ec/*execution-context* root] (program)))
    (let [site (take! events)
          anchors (mapv (fn [_] (await-cps (sp/fork site))) (range 5))
          handles #(count (:handles @(:scope session)))]
      (is (= 5 (handles)))
      (run! sp/abandon (rest anchors))
      (dotimes [_ 4] (is (= sp/abandoned-site (:savepoint/site (take! events)))))
      (loop [tries 0]
        (when (and (< tries 100) (not= 1 (handles)))
          (Thread/sleep 20)
          (recur (inc tries))))
      (is (= 1 (handles)))
      (is (sp/pending? (first anchors))))))
