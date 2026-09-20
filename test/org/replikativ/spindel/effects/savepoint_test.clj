(ns org.replikativ.spindel.effects.savepoint-test
  "The laws of docs/savepoints.md."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.savepoint :as sp :refer [savepoint]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
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
      (is (nil? (.poll events)) "the inherited catch-all saw nothing of the child"))))

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
