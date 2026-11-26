(ns org.replikativ.spindel.v2.savepoint-layer-test
  "The v2 savepoint session layer (org.replikativ.spindel.v2.savepoint)."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.savepoint :as sp]
            [org.replikativ.spindel.v2.trace :as trace]))

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 400) false :else (do (Thread/sleep 5) (recur (inc n))))))

(defn- ends []
  (let [a (atom [])]
    [a {sp/result-site (fn [e] (swap! a conj [:result (:savepoint/payload e) (:savepoint/world e)]))
        sp/error-site (fn [e] (swap! a conj [:error (:savepoint/world e)]))
        sp/abandoned-site (fn [e] (swap! a conj [:abandoned (:savepoint/world e)]))}]))

(deftest no-handler-is-identity
  (let [w (v2/world) [es hs] (ends) s (sp/open! w {:handlers hs})]
    (sp/start! s #(task (inc (sp/savepoint :site 41))))
    (is (wait-until #(seq @es)))
    (is (= [:result 42 w] (first @es)))
    ((sp/close! s) identity identity)))

(deftest resume-in-place-with-an-address
  (let [w (v2/world) seen (atom nil) [es hs] (ends)
        s (sp/open! w {:handlers (assoc hs :choose (fn [p] (reset! seen p) (sp/resume p (* 10 (:savepoint/payload p)))))})]
    (sp/start! s #(task (inc (sp/savepoint :choose 4))))
    (is (wait-until #(seq @es)))
    (is (= [:result 41 w] (first @es)))
    (let [[frame key] (:savepoint/address @seen)]
      (is (= [] frame))
      (is (integer? key)))
    (is (not (sp/pending? @seen)))
    ((sp/close! s) identity identity)))

(deftest explicit-ids
  ;; the handler records the savepoint after resuming it: the test closes the
  ;; session once it sees it, and a resume after that throws on the
  ;; handler's executor thread, uncaught (it reached the next no-uncaught
  ;; test's handler)
  (let [w (v2/world) seen (atom nil)
        s (sp/open! w {:handlers {:choose (fn [p] (sp/resume p 1) (reset! seen p))}})]
    (sp/start! s #(task (sp/savepoint :choose nil {:id [:x 3]})))
    (is (wait-until #(some? @seen)))
    (is (= [:x 3] (:savepoint/address @seen)))
    ((sp/close! s) identity identity)))

(deftest forks-are-independent-particles-with-their-own-seeds
  (let [w (v2/world) pending (atom nil) [es hs] (ends)
        s (sp/open! w {:seed 7 :handlers (assoc hs :choose (fn [p] (reset! pending p)))})]
    (sp/start! s #(task (+ 100 (sp/savepoint :choose nil))))
    (is (wait-until #(some? @pending)))
    (let [p @pending
          kids (mapv (fn [_] (sp/fork p)) (range 3))]
      (is (sp/pending? p) "forking leaves the source pending")
      (is (every? sp/pending? kids))
      (is (= 3 (count (set (map #(sp/seed (:savepoint/world %)) kids)))) "derived seeds differ")
      (doseq [[k v] (map vector kids [1 2 3])] (sp/resume k v))
      (is (wait-until #(= 3 (count @es))))
      (is (= #{101 102 103} (set (map second @es))))
      (is (every? #(not= w (nth % 2)) @es) "each ends in its own world")
      (sp/abandon p)
      (is (wait-until #(= 4 (count @es))))
      (is (= :abandoned (first (last @es)))))
    ((sp/close! s) identity identity)))

(deftest a-chain-of-forks-never-repeats-a-seed
  ;; each fork is forked again before it runs: a replay from the same site
  ;; of the last fork's world, as an MH chain does
  (let [w (v2/world) pending (atom nil)
        s (sp/open! w {:seed 7 :handlers {:choose (fn [p] (reset! pending p))}})]
    (sp/start! s #(task (sp/savepoint :choose nil)))
    (is (wait-until #(some? @pending)))
    (let [chain (take 6 (iterate sp/fork @pending))
          seeds (map #(sp/seed (:savepoint/world %)) chain)]
      (is (= 6 (count (set seeds))) (str (vec seeds))))
    ((sp/close! s) identity identity)))

(deftest copy-consumes-the-source
  (let [w (v2/world) pending (atom nil) [es hs] (ends)
        s (sp/open! w {:handlers (assoc hs :choose (fn [p] (reset! pending p)))})]
    (sp/start! s #(task (* 2 (sp/savepoint :choose nil))))
    (is (wait-until #(some? @pending)))
    (let [p @pending
          [a b] (sp/copy p 2)]
      (is (not (sp/pending? p)))
      (is (thrown? Exception (sp/resume p 1)))
      (sp/resume a 5) (sp/resume b 6)
      (is (wait-until #(= 2 (count @es))))
      (is (= #{10 12} (set (map second @es)))))
    ((sp/close! s) identity identity)))

(deftest an-unactivated-fork-is-abandoned-without-running
  (let [w (v2/world) pending (atom nil) ran (atom 0)
        s (sp/open! w {:handlers {:choose (fn [p] (reset! pending p))}})]
    (sp/start! s #(task (try (sp/savepoint :choose nil) (finally (swap! ran inc)))))
    (is (wait-until #(some? @pending)))
    (let [k (sp/fork @pending)]
      (sp/abandon k)
      (is (not (sp/pending? k)))
      (Thread/sleep 50)
      (is (zero? @ran) "nothing ran in the discarded fork"))
    ((sp/close! s) identity identity)))

(deftest abandoning-then-releasing-an-unactivated-fork
  ;; abandon gives the fork's world back; the caller's release of it, racing
  ;; or after, does nothing
  (dotimes [_ 50]
    (let [w (v2/world) pending (atom nil)
          s (sp/open! w {:handlers {:choose (fn [p] (reset! pending p))}})]
      (sp/start! s #(task (sp/savepoint :choose nil)))
      (is (wait-until #(some? @pending)))
      (let [k (sp/fork @pending)]
        (sp/abandon k)
        (is (nil? (sp/release-world! s (:savepoint/world k)))))
      ((sp/close! s) identity identity))))

(defmacro ^:private no-uncaught [& body]
  `(let [uncaught# (atom [])
         prev# (Thread/getDefaultUncaughtExceptionHandler)]
     (Thread/setDefaultUncaughtExceptionHandler
      (reify Thread$UncaughtExceptionHandler
        (uncaughtException [_# _# e#] (swap! uncaught# conj e#))))
     (try ~@body
          (Thread/sleep 50)
          (is (empty? @uncaught#) (str (first @uncaught#)))
          (finally (Thread/setDefaultUncaughtExceptionHandler prev#)))))

(deftest a-world-released-at-a-savepoint-ends-abandoned
  ;; T21: host waits receive ::released. The root's owner released it, the
  ;; session did not give it back: its end is delivered, abandoned
  (no-uncaught
   (let [w (v2/world) pending (atom nil) [es hs] (ends)
         s (sp/open! w {:handlers (assoc hs :choose (fn [p] (reset! pending p)))})]
     (sp/start! s #(task (sp/savepoint :choose nil)))
     (is (wait-until #(some? @pending)))
     (v2/release-world! w)
     (is (wait-until #(seq @es)))
     (is (= [[:abandoned w]] @es))
     (let [closed (promise)]
       ((sp/close! s) #(deliver closed [:ok %]) #(deliver closed [:err %]))
       (is (= [:ok nil] (deref closed 1000 ::timeout)) "closing over a released root")))))

(deftest a-run-in-a-released-root-rejects
  ;; a trace run waiting at a savepoint settles when its root is released
  (let [w (v2/world) s (sp/open! w)
        parked (promise) result (promise)]
    ((trace/run s #(task (sp/savepoint :choose nil) :done)
                (fn [sp' _] (deliver parked sp')
                  (fn [_ _]))) ; never decides
     #(deliver result [:ok %]) #(deliver result [:err %]))
    (is (some? (deref parked 1000 nil)))
    (v2/release-world! w)
    (let [[k e] (deref result 1000 ::timeout)]
      (is (= :err k))
      (is (:spindel/released (ex-data e))))))

(deftest a-fork-released-by-its-owner-ends-abandoned
  ;; an activated instance is owned by the session's root: releasing the
  ;; root releases it, and its end is delivered too
  (no-uncaught
   (let [w (v2/world) pending (atom nil) [es hs] (ends)
         s (sp/open! w {:handlers (assoc hs :choose (fn [p] (reset! pending p)))})]
     (sp/start! s #(task (sp/savepoint :choose nil) (sp/savepoint :choose nil)))
     (is (wait-until #(some? @pending)))
     (let [first-pending @pending
           k (sp/fork first-pending)
           kw (:savepoint/world k)]
       (sp/resume k 1)
       (is (wait-until #(not (identical? first-pending @pending))) "the fork reached its next savepoint")
       (v2/release-world! w)
       (is (wait-until #(= 2 (count @es))))
       (is (= #{[:abandoned w] [:abandoned kw]} (set @es)))))))

(deftest a-world-the-session-gave-back-delivers-no-end
  (no-uncaught
   (let [w (v2/world) pending (atom nil) [es hs] (ends)
         s (sp/open! w {:handlers (assoc hs :choose (fn [p] (reset! pending p)))})]
     (sp/start! s #(task (sp/savepoint :choose nil) (sp/savepoint :choose nil)))
     (is (wait-until #(some? @pending)))
     (let [first-pending @pending
           k (sp/fork first-pending)]
       (sp/resume k 1)
       (is (wait-until #(not (identical? first-pending @pending))))
       (sp/release-world! s (:savepoint/world k))
       (Thread/sleep 100)
       (is (empty? @es)))
     ((sp/close! s) identity identity))))

(deftest handled-counts-the-default-handler
  (let [w (v2/world) s (sp/open! w)]
    (is (not (sp/handled? w :x)))
    (sp/install-handlers! w {:default (fn [_])})
    (is (sp/handled? w :x))
    ((sp/close! s) identity identity)))

(deftest a-handler-forks-and-resumes-its-forks
  ;; from inside the publishing world's callback: no host call into the fork
  (let [w (v2/world) [es hs] (ends)
        s (sp/open! w {:handlers (assoc hs :choose (fn [p]
                                                     (let [k (sp/fork p)]
                                                       (sp/resume k 7)
                                                       (sp/resume p 1))))})]
    (sp/start! s #(task (sp/savepoint :choose nil)))
    (is (wait-until #(= 2 (count @es))))
    (is (= #{1 7} (set (map second @es))))
    ((sp/close! s) identity identity)))

(deftest resuming-a-fork-while-its-world-is-busy
  ;; the activation may wait behind other items of the fork's world; the
  ;; end is watched once it is born
  (let [w (v2/world) pending (atom nil) [es hs] (ends)
        s (sp/open! w {:handlers (assoc hs :choose (fn [p] (reset! pending p)))})]
    (sp/start! s #(task (+ 1 (sp/savepoint :choose nil))))
    (is (wait-until #(some? @pending)))
    (let [errors (atom 0)]
      (dotimes [_ 200]
        (let [k (sp/fork @pending)
              fw (:savepoint/world k)
              writer (future (dotimes [j 20] (v2/assoc-in-world! fw [:x j] j)))]
          (try (sp/resume k 1) (catch Exception _ (swap! errors inc)))
          @writer))
      (is (zero? @errors))
      (is (wait-until #(= 200 (count (filter (comp #{:result} first) @es))))))
    ((sp/close! s) identity identity)))

(deftest disposing-fork-anchors-gives-their-worlds-back
  ;; anchors made by forking a savepoint are unborn instances: disposing
  ;; one discards it (S7), and the publication stays forkable
  (let [w (v2/world) pending (atom nil) [es hs] (ends)
        s (sp/open! w {:handlers (assoc hs :choose (fn [p] (reset! pending p)))})]
    (sp/start! s #(task (inc (sp/savepoint :choose nil))))
    (is (wait-until #(some? @pending)))
    (let [anchors (vec (repeatedly 5 #(sp/fork @pending)))]
      (is (= 5 (count @(:worlds s))))
      (run! sp/dispose anchors)
      (is (empty? @(:worlds s)) "the session gives the anchors' worlds back")
      (is (every? (comp not sp/pending?) anchors))
      (let [k (sp/fork @pending)]
        (sp/resume k 41)
        (is (wait-until #(some (fn [[t v]] (= [t v] [:result 42])) @es)) "the publication still forks")))
    ((sp/close! s) identity identity)))

(deftest the-session-gives-back-only-the-worlds-it-made
  ;; a branch that continued in the root ends first: releasing "its world"
  ;; must not release the root, whose root scope owns the other branches
  (let [w (v2/world) pending (atom nil) [es hs] (ends)
        s (sp/open! w {:handlers (assoc hs :choose (fn [p] (reset! pending p)))})]
    (sp/start! s #(task (inc (sp/savepoint :choose nil))))
    (is (wait-until #(some? @pending)))
    (let [k (sp/fork @pending)]
      (sp/resume @pending 1)
      (is (wait-until #(some (fn [[t v]] (= [t v] [:result 2])) @es)))
      (sp/release-world! s w)
      (sp/resume k 10)
      (is (wait-until #(some (fn [[t v]] (= [t v] [:result 11])) @es)) "the fork still runs")
      (is (nil? (v2/get-in-world w [:probe])) "the root is not released: it still answers"))
    ((sp/close! s) identity identity)))

(deftest a-fork-given-back-by-its-handler-right-after-activation
  ;; once activated, a fork runs on to its next savepoint, whose handler may
  ;; give its world back before resume has watched its end: nothing is left
  ;; to watch, and neither resume nor a host thread fails
  (let [uncaught (atom [])
        prev (Thread/getDefaultUncaughtExceptionHandler)]
    (Thread/setDefaultUncaughtExceptionHandler
     (reify Thread$UncaughtExceptionHandler
       (uncaughtException [_ _ e] (swap! uncaught conj e))))
    (try
      (let [w (v2/world) pending (atom nil) given-back (atom 0) s (promise)
            session (sp/open! w {:handlers {:a (fn [p] (reset! pending p))
                                            :b (fn [p] (sp/release-world! @s (:savepoint/world p))
                                                 (swap! given-back inc))}})]
        (deliver s session)
        (sp/start! session #(task (sp/savepoint :a nil) (sp/savepoint :b nil)))
        (is (wait-until #(some? @pending)))
        (let [errors (atom [])]
          (dotimes [_ 200]
            (try (sp/resume (sp/fork @pending) 1) (catch Exception e (swap! errors conj e))))
          (is (empty? @errors) (str (first @errors)))
          (is (wait-until #(= 200 @given-back))))
        (Thread/sleep 50)
        (is (empty? @uncaught) (str (first @uncaught)))
        ((sp/close! session) identity identity))
      (finally (Thread/setDefaultUncaughtExceptionHandler prev)))))
