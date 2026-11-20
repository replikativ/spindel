(ns org.replikativ.spindel.v2.host-item-isolation-test
  "A queued host item, or a host callback, that throws belongs to its own
   caller: the thread that happens to drive the turn (an unrelated host
   operation, e.g. `release-world!`) never receives its exception."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2]))

(deftest a-queued-item-that-throws-does-not-reach-the-turns-driver
  (let [w (v2/world)
        inside (promise) go (promise)
        ;; thread A holds the gate inside its own item, so B's item queues
        a (future (v2/host-call! w (fn [] (deliver inside true) @go :a)))]
    (is (true? (deref inside 2000 ::timeout)))
    (v2/send-world! w (fn [] (throw (ex-info "B's item" {:b true}))))
    (let [ran (atom false)]
      (v2/send-world! w (fn [] (reset! ran true)))
      ;; B's throw is reported on stderr by the thread that drove the turn (A's)
      (deliver go true)
      (is (= :a (deref a 2000 ::timeout)) "NEGATIVE: A received B's exception")
      (is (true? @ran) "the turn goes on after it"))
    (v2/release-world! w)
    (is (true? (v2/await-complete w 2000 ::timeout)))))

(deftest release-world-is-not-hit-by-a-concurrent-send
  (testing "a sent fn writing a signal while the world is released (dvergr's room-facts listener)"
    (let [thrown (atom [])]
      (binding [*err* (java.io.StringWriter.)]
        (dotimes [_ 500]
          (let [w (v2/world) s (v2/signal w 0)
                go (java.util.concurrent.CountDownLatch. 1)
                f (future (.await go)
                          (try (v2/send-world! w #(swap! s inc)) (catch Throwable _ nil)))]
            (.countDown go)
            (try (v2/release-world! w)
                 (catch Throwable t (swap! thrown conj (ex-message t))))
            (deref f 1000 nil))))
      (is (empty? @thrown) "NEGATIVE: release-world! threw a sent item's exception"))))

(deftest a-host-callback-that-throws-does-not-reach-the-turns-driver
  (let [w (v2/world)
        s (v2/signal w 0)
        seen (atom 0)]
    (v2/observe! s (fn [_ _] (throw (ex-info "observer" {}))))
    (v2/observe! s (fn [_ _] (swap! seen inc)))
    (binding [*err* (java.io.StringWriter.)]
      (is (nil? (try (v2/write! s 1) nil (catch Throwable t t))) "NEGATIVE: the writer received the observer's exception"))
    (is (pos? @seen) "the other observer still runs")
    (v2/release-world! w)))
