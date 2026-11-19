(ns org.replikativ.spindel.v2.yggdrasil-review-test
  "Regressions for the review of the yggdrasil layer (review-sol.md, findings
   1-10). Races are forced with latches, barriers or a queued lifecycle
   executor, never by sleeping."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.ygg-support :as s
             :refer [caught close-world! dh-system done! put! root st val-in with-stores]]
            [org.replikativ.spindel.v2.yggdrasil :as ygg]
            [yggdrasil.protocols :as yp]))

(defn- reviewed-fork [w sids & [opts]]
  (let [f (ygg/fork! w (or opts {}))]
    (doseq [sid sids] (put! (ygg/system (:world f) sid) :x (str "child-" sid)))
    (close-world! (:world f))
    f))

(defmacro with-manual-executor [q & body]
  `(let [~q (atom [])]
     (ygg/set-executor! (fn [f#] (swap! ~q conj f#)))
     (try ~@body
          (finally (ygg/set-executor! (fn [f#] (future-call f#) nil))))))

(defn- run-queued!
  "Runs the queued lifecycle work, and what it queues, to quiescence; a
   reschedule loop fails the test instead of spinning."
  [q]
  (loop [n 0]
    (let [[fs _] (swap-vals! q (constantly []))]
      (cond (empty? fs) nil
            (> n 50) (is false "lifecycle work keeps rescheduling itself")
            :else (do (doseq [f fs] (f)) (recur (inc n)))))))

(defn- deref! [p] (let [v (deref p 10000 ::timeout)] (is (not= ::timeout v)) v))

(defn- var-of [sym] (ns-resolve 'org.replikativ.spindel.v2.yggdrasil sym))

(deftest f1-a-partition-inherits-the-owner-of-the-record-it-claimed
  (with-stores
    (let [w (root [(dh-system "kb")])
          f (reviewed-fork w ["kb"])
          scope (var-of 'scope)
          orig @scope
          worker (promise)
          entered (promise)
          release (promise)]
      (with-redefs-fn {scope (fn [r ce]
                               (when (= (Thread/currentThread) (deref worker 0 nil))
                                 (deliver entered true) @release)
                               (orig r ce))}
        (fn []
          (let [part (future (deliver worker (Thread/currentThread))
                             (ygg/partition! f {:all #{"kb"}} {:owner :alice}))]
            (deref! entered)
            (ygg/transfer! f :alice {})
            (deliver release true)
            (let [{:keys [all]} (deref! part)]
              (is (= :alice (:owner (ygg/status all))))
              (is (= ::ygg/not-owner (caught #(ygg/merge! all {}))) "NEGATIVE: a leaf without its owner")
              (ygg/discard! all {:owner :alice})))))
      (done! w))))

(deftest f2-a-resolution-that-loses-to-settlement-discards-its-overlay
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          f (ygg/fork! w {})
          before (yp/branches kb)
          open (var-of 'open-overlay)
          orig @open
          entered (promise)
          release (promise)]
      (with-redefs-fn {open (fn [ph base] (deliver entered true) @release (orig ph base))}
        (fn []
          (let [resolution (future (try (ygg/system (:world f) "kb") ::resolved
                                        (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))]
            (deref! entered)
            (is (= :discarded (:status (ygg/discard! f {}))))
            (deliver release true)
            (is (= ::ygg/fork-not-open (deref! resolution)) "NEGATIVE: a handle of a discarded fork")
            (is (= before (yp/branches kb)) "the overlay it opened is gone"))))
      (done! w))))

(deftest f3-recovery-does-not-merge-into-an-ended-parent
  (with-stores
    (with-manual-executor q
      (let [a (dh-system "a")
            b (dh-system "b")
            w (root [a {:meta {:merge-rank 0}}] [b {:meta {:merge-rank 1}}])
            f (reviewed-fork w ["a" "b"])
            late? (atom true)]
        (is (= ::ygg/incomplete
               (caught #(ygg/merge! f {:guard (fn [sid _] (when (and @late? (= "b" sid)) (throw (ex-info "late" {}))))}))))
        (done! w)
        (reset! late? false)
        (is (= ::ygg/parent-ended (caught #(ygg/recover! f))))
        (is (nil? (val-in b :x)) "NEGATIVE: recovery merged into a completed parent")
        (run-queued! q)
        (is (= :discarded (st f)))))))

(deftest f3-a-parent-end-during-a-claim-is-honoured-at-release
  (with-stores
    (with-manual-executor q
      (let [w (root [(dh-system "kb")])
            f (reviewed-fork w ["kb"])
            gate (promise)]
        (is (= ::ygg/refused
               (caught #(ygg/merge! f {:precheck (fn [_] (done! w) (run-queued! q) (deliver gate true) false)}))))
        (is (deref! gate))
        (run-queued! q)
        (is (= :discarded (st f)) "the flag set during the claim discarded it at release")))))

(deftest f4-concurrent-recoveries-run-a-failed-hook-once
  (with-stores
    (let [w (root [(dh-system "kb")])
          f (reviewed-fork w ["kb"])
          calls (atom 0)
          entered (promise)
          release (promise)]
      (ygg/merge! f {:on-merge (fn [_] (when (= 1 (swap! calls inc)) (throw (ex-info "down" {})))
                                 (deliver entered true) @release)})
      (is (= :failed (:hook-status (ygg/status f))))
      (let [first-recovery (future (ygg/recover! f))]
        (deref! entered)
        (let [second-recovery (future (caught #(ygg/recover! f)))]
          (is (= ::ygg/settling (deref second-recovery 2000 ::ran-the-hook)) "NEGATIVE: a second recovery ran the hook")
          (deliver release true)
          (deref second-recovery 10000 nil))
        (is (= :completed (:hook-status (deref! first-recovery)))))
      (is (= 2 @calls))
      (done! w))))

(deftest f5-a-failed-cleanup-keeps-what-its-retry-needs
  (with-stores
    (let [kb (dh-system "kb")
          w (v2/world)
          cleanups (atom 0)
          _ (ygg/register! w kb {:policy {:cleanup (fn [{:keys [handle]}]
                                                     (when (= 1 (swap! cleanups inc)) (throw (ex-info "busy" {})))
                                                     (yp/discard! handle))}})
          f (reviewed-fork w ["kb"])]
      (is (= [:merged :failed] ((juxt :status :cleanup) (ygg/merge! f {}))))
      (is (some? (ygg/fork-of (:world f))) "NEGATIVE: the holder went with the cleanup owed")
      (is (= :done (:cleanup (ygg/recover! f))))
      (is (= 2 @cleanups))
      (is (nil? (ygg/fork-of (:world f))) "then it goes")
      (done! w))))

(deftest f6-concurrent-first-registrations-share-one-holder
  (with-stores
    (let [w (v2/world)
          mint (var-of 'mint-holder!)
          orig @mint
          mints (atom 0)
          barrier (java.util.concurrent.CyclicBarrier. 2)]
      (with-redefs-fn {mint (fn [& args]
                              (swap! mints inc)
                              ;; under the bug both threads meet here; under the fix the
                              ;; second waits for the first's registration
                              (try (.await barrier 500 java.util.concurrent.TimeUnit/MILLISECONDS)
                                   (catch Exception _ nil))
                              (apply orig args))}
        (fn []
          (let [regs (mapv (fn [sid] (future (ygg/register! w (dh-system sid) {}))) ["a" "b"])]
            (is (= ["a" "b"] (mapv deref! regs))))))
      (is (= 1 @mints) "NEGATIVE: one world got two holders")
      (is (= #{"a" "b"} (set (keys (ygg/systems w)))))
      (is (= #{"a" "b"} (set (keys (ygg/locators (ygg/fork! w {})))))))
    (testing "the same id registers once"
      (let [w (v2/world)
            start (java.util.concurrent.CountDownLatch. 1)
            regs (mapv (fn [_] (future (.await start)
                                       (try (ygg/register! w (dh-system "kb") {}) :ok
                                            (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
                       (range 2))]
        (.countDown start)
        (is (= #{:ok ::ygg/already-registered} (set (map deref! regs))))))))

(deftest f7-leaves-published-after-the-parent-ended-are-discarded
  (with-stores
    (with-manual-executor q
      (let [w (root [(dh-system "kb")] [(dh-system "data")])
            settled (atom #{})
            f (reviewed-fork w ["kb" "data"] {:on-discard #(swap! settled conj [:discard (:leaf %) (:reason %)])})
            leaf-id (var-of 'leaf-id)
            orig @leaf-id
            ended (atom false)]
        (run-queued! q)
        (let [leaves (with-redefs-fn {leaf-id (fn [id k]
                                                (when (compare-and-set! ended false true)
                                                  (done! w) (run-queued! q))
                                                (orig id k))}
                       #(ygg/partition! f {:a #{"kb"} :b #{"data"}} {}))]
          (run-queued! q)
          (is (every? #(= :discarded (st %)) (vals leaves)) "NEGATIVE: leaves outlived the parent")
          (is (= #{[:discard :a :parent-ended] [:discard :b :parent-ended]} @settled))
          (is (nil? (ygg/fork-of (:world f)))))))))

(deftest f8-the-owner-recovers-an-incomplete-transferred-merge
  (with-stores
    (let [a (dh-system "a")
          b (dh-system "b")
          w (root [a {:meta {:merge-rank 0}}] [b {:meta {:merge-rank 1}}])
          f (reviewed-fork w ["a" "b"])
          late? (atom true)]
      (ygg/transfer! f :alice {})
      (is (= ::ygg/incomplete
             (caught #(ygg/merge! f {:owner :alice
                                     :guard (fn [sid _] (when (and @late? (= "b" sid)) (throw (ex-info "late" {}))))}))))
      (reset! late? false)
      (is (= ::ygg/not-owner (caught #(ygg/recover! f))))
      (is (= :merged (:status (ygg/recover! f {:owner :alice}))) "NEGATIVE: the owner could not recover")
      (is (= "child-b" (val-in b :x)))
      (done! w))))

(deftest f9-an-engine-fork-of-the-registering-world-has-no-frozen-base
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])]
      (put! kb :x "before")
      (let [u (v2/fork! w)]
        (put! kb :x "after")
        (is (= ::ygg/no-frozen-base (caught #(ygg/view u "kb"))) "NEGATIVE: it read the moving head")
        (done! u w)))))

(deftest f10-settled-children-leave-their-parents-record
  (with-stores
    (let [w (root [(dh-system "kb")])
          p (ygg/fork! w {})]
      (dotimes [i 3]
        (let [c (ygg/fork! (:world p) {})]
          (if (even? i) (ygg/merge! c {}) (ygg/discard! c {}))))
      (is (empty? (:children (ygg/describe p))) "NEGATIVE: settled ids accumulate")
      (let [open (ygg/fork! (:world p) {})]
        (is (= #{(:id open)} (:children (ygg/describe p))))
        (ygg/discard! open {}))
      (ygg/discard! p {})
      (done! w))))
