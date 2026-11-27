(ns org.replikativ.spindel.v2.no-inline-test
  "D (H2): a JVM host thread that opts out of inline turns
   (`without-inline-turns`) enqueues and hands off, as on a world created
   with `:inline? false`."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await take! offload]]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)

(defn- vworld
  ([] (vworld {}))
  ([opts] (v2/world (merge {:verify? true :hook (verify/checking-hook *divergences*)} opts))))

(defmacro ^:private checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- held-executor
  "An executor that keeps its runnables until `(run-all)`, so the world's
   drainer is busy until then; `(pass!)` runs them and lets later ones
   through to the default executor."
  []
  (let [q (java.util.concurrent.LinkedBlockingQueue.)
        through (atom false)
        run-all (fn [] (loop [] (when-let [r (.poll q)] (.run ^Runnable r) (recur))))]
    [(reify java.util.concurrent.Executor
       (execute [_ r]
         (if @through
           (.execute ^java.util.concurrent.Executor @hs/default-executor r)
           (.add q r))))
     run-all
     (fn pass! [] (reset! through true) (run-all))]))

(defn- new-thread
  "`(f)` on a new, dedicated thread with the caller's bindings (a pooled
   `future` may reuse one thread for several calls); a future of its value."
  [f]
  (let [t (java.util.concurrent.FutureTask. ^Callable (bound-fn* f))]
    (.start (Thread. t))
    t))

(defn- off-thread
  "`(f)` on a new thread opted out of inline turns; a future of its value."
  [f]
  (new-thread #(v2/without-inline-turns f)))

(deftest an-opted-in-caller-runs-no-slice-on-a-mixed-world
  (checked
   (let [w (vworld)
         ran-on (java.util.concurrent.ConcurrentHashMap.)
         record! (fn [tag] (.put ran-on (Thread/currentThread) tag) tag)]
     (binding [v2/*world* w]
       (testing "the same operation, inline and opted in"
         (let [me (Thread/currentThread)
               inline (task (Thread/currentThread))
               [caller ran-on] (deref (off-thread #(let [t (task (Thread/currentThread))]
                                                     [(Thread/currentThread) (v2/value t 2000 ::timeout)]))
                                      10000 [::stuck ::stuck])]
           (is (identical? me (v2/value inline 2000 ::timeout)) "an ordinary caller runs the slice")
           (is (instance? Thread ran-on))
           (is (not (identical? caller ran-on)) "an opted-in caller hands it off")))
       (testing "concurrent inline and opted-in callers on one world"
         (let [xs (vec (repeatedly 4 #(v2/signal 0)))
               total (spin (loop [i 0 acc 0]
                             (if (< i 4) (recur (inc i) (+ acc (iv/get-new (track (nth xs i))))) acc)))
               _ (v2/observe! total (fn [_ _]))
               worker (fn [i]
                        (fn []
                          (let [ts (vec (for [n (range 100)]
                                          (do (v2/write! (nth xs i) (inc n))
                                              (task (record! i) (* 2 (iv/get-new (track (nth xs i))))))))]
                            [(Thread/currentThread) ts])))
               runs (mapv (fn [i] (if (even? i) (new-thread (worker i)) (off-thread (worker i)))) (range 4))
               results (mapv #(deref % 10000 ::stuck) runs)]
           (is (not-any? #{::stuck} results))
           (is (= 400 (v2/value total 5000 ::timeout)) "every write applied")
           (doseq [[_ ts] results t ts] (is (pos? (v2/value t 5000 ::timeout))))
           (let [opted (set (map first (take-nth 2 (rest results))))
                 slices (set (keys ran-on))]
             (is (= 2 (count opted)))
             (is (empty? (filter opted slices)) "no slice ran on an opted-in thread")))))
     (v2/release-world! w)
     (is (true? (v2/await-complete w 5000 ::timeout))))))

(deftest commands-return-nil-and-apply-in-fifo-order
  (checked
   (let [w (vworld)
         [mb s d] (binding [v2/*world* w] [(v2/mailbox) (v2/signal 0) (v2/deferred)])
         seen (atom [])]
     (binding [v2/*world* w]
       (v2/observe! s (fn [v _] (swap! seen conj v)))
       (let [t (task (loop [i 0 acc []] (if (< i 50) (recur (inc i) (conj acc (take! mb))) acc)))
             rs @(off-thread
                  (fn []
                    (let [posts (mapv #(v2/post! mb %) (range 50))
                          writes (mapv #(v2/write! s %) (range 1 6))
                          reset (reset! s 6)
                          host (v2/host! w (fn [] :ran))
                          created (task (await d))]
                      [posts writes reset host (v2/deliver! d :delivered) created])))
             [posts writes reset host delivered created] rs]
         (is (every? nil? posts))
         (is (= [1 2 3 4 5] writes) "write! returns the value it queued")
         (is (= 6 reset) "reset! returns the value it queued")
         (is (nil? host) "a bare host item returns nothing when it is queued")
         (is (= :delivered delivered))
         (is (= (vec (range 50)) (v2/value t 2000 ::timeout)) "posts arrive in order")
         (is (= :delivered (v2/value created 2000 ::timeout)) "a task created by an opted-in caller runs")
         (is (true? (loop [n 0] (cond (= 6 (peek @seen)) true (> n 200) false :else (do (Thread/sleep 5) (recur (inc n)))))))
         (is (apply <= @seen) "writes commit in order")))
     (v2/release-world! w))))

(deftest host-call-replies-and-an-interrupted-wait-leaves-the-item
  (checked
   (let [w (vworld)
         s (binding [v2/*world* w] (v2/signal 1))]
     (is (= 42 @(off-thread #(v2/host-call! w (fn [] 42)))))
     (is (= 2 @(off-thread #(swap! s inc))) "swap! replies its new value")
     (is (thrown-with-msg? clojure.lang.ExceptionInfo #"boom"
                           (try @(off-thread #(v2/host-call! w (fn [] (throw (ex-info "boom" {})))))
                                (catch java.util.concurrent.ExecutionException e (throw (.getCause e)))))
         "an item's throw reaches the waiting caller")
     (v2/release-world! w)))
  (testing "an interrupt ends the wait for an uncontended item; the item still runs"
    (checked
     (let [[ex run-all pass!] (held-executor)
           w (vworld {:executor ex})
           ran (promise)
           waiting (promise)
           caller (future (v2/without-inline-turns
                           (fn []
                             (deliver waiting (Thread/currentThread))
                             (try (v2/host-call! w (fn [] (deliver ran true) :late))
                                  (catch InterruptedException _ :interrupted)))))
           ^Thread th (deref waiting 2000 nil)]
       (Thread/sleep 50)
       (.interrupt th)
       (is (= :interrupted (deref caller 2000 ::stuck)))
       (is (not (realized? ran)) "the item waits for the drainer")
       (run-all)
       (is (true? (deref ran 2000 false)) "the item ran after its caller stopped waiting")
       (pass!)
       (v2/release-world! w)
       (is (true? (v2/await-complete w 5000 ::timeout)))))))

(deftest the-setting-is-ignored-inside-a-gate
  (checked
   (let [w (vworld)
         other (vworld)
         s (binding [v2/*world* w] (v2/signal 0))]
     (is (= [:inner :other]
            (v2/host-call! w (fn [] (v2/without-inline-turns
                                     (fn [] [(v2/host! w (fn [] :inner)) (v2/host! other (fn [] :other))])))))
         "an item runs a nested host item at once, and another world's inline")
     (binding [v2/*world* w]
       (is (= 5 (v2/value (task (v2/no-inline (v2/write! s 5)) (iv/get-new (track s))) 2000 ::timeout))
           "a slice's write is an effect of its run (Z#44), applied at once"))
     (v2/release-world! w)
     (v2/release-world! other))))

(deftest release-and-acknowledgements-from-an-opted-in-thread
  (checked
   (let [[ex run-all pass!] (held-executor)
         w (vworld {:executor ex})
         gate (promise)
         s (binding [v2/*world* w] (v2/signal 0))
         ;; an offload that ignores interrupts: its acknowledgement comes
         ;; after the release
         t (binding [v2/*world* w]
             (task (offload #(loop [] (when-not (realized? gate) (Thread/onSpinWait) (recur)))
                            {:pool @hs/default-executor})))]
     (is (fn? @(off-thread #(v2/release-world! w))) "release returns its rows-left fn before it commits")
     (is (not (v2/complete? w)))
     (is (= 1 @(off-thread #(v2/write! s 1)))
         "admitted before the release committed: refused in its item, not at the call")
     (run-all)
     (is (= ::released (try (v2/write! s 1) (catch clojure.lang.ExceptionInfo e (when (:spindel/released (ex-data e)) ::released))))
         "after the release committed, admission refuses")
     (pass!)
     (is (= ::timeout (v2/await-complete w 100 ::timeout)) "the offload is outstanding")
     (deliver gate :done)
     (is (true? (v2/await-complete w 5000 ::timeout)) "its acknowledgement is accepted after release")
     (is (v2/handle? t)))))

(deftest nesting-restores-the-setting
  ;; a fresh world each time: its gate is free and its queue empty, so an
  ;; inline caller runs the item before returning
  (let [inline-here? #(let [w (v2/world)] (= :x (v2/host! w (fn [] :x))))]
    (is (inline-here?) "inline by default")
    (is (false? (v2/without-inline-turns
                 (fn []
                   (v2/without-inline-turns (fn [] nil))
                   (inline-here?))))
        "still opted out after a nested opt-out returns")
    (is (inline-here?) "restored after the outer one")
    (is (true? (try (v2/no-inline (throw (ex-info "out" {})))
                    (catch clojure.lang.ExceptionInfo _ (inline-here?))))
        "restored when the body throws")))

(defn- capturing-executor
  "An executor that only collects its runnables; `(run-captured)` runs them
   (and those they submit) on the calling thread."
  []
  (let [q (java.util.concurrent.LinkedBlockingQueue.)]
    [(reify java.util.concurrent.Executor (execute [_ r] (.add q r)))
     (fn run-captured [] (loop [n 0] (if-let [r (.poll q)] (do (.run ^Runnable r) (recur (inc n))) n)))
     q]))

(deftest a-throwing-inline-item-still-hands-off
  ;; an inline item holds the gate; an opted-in item is queued and its
  ;; drainer loses the gate (its claim is spent); then the inline item
  ;; throws. The inline caller must hand off after unlocking, or the
  ;; queued item is stranded
  (checked
   (let [[ex run-captured q] (capturing-executor)
         w (vworld {:executor ex})
         in-item (promise)
         go (promise)
         ran (promise)
         inline (future (v2/host! w (fn [] (deliver in-item true) @go (throw (ex-info "boom" {})))))]
     (is (true? (deref in-item 2000 false)))
     @(off-thread #(v2/host! w (fn [] (deliver ran true))))
     (is (= 1 (run-captured)) "the drainer ran and lost the gate")
     (deliver go true)
     (is (thrown-with-msg? Exception #"boom" (try @inline (catch java.util.concurrent.ExecutionException e (throw (.getCause e))))))
     (is (pos? (.size ^java.util.Collection q)) "the inline caller handed off")
     (run-captured)
     (is (true? (deref ran 1000 false)) "the queued item ran")
     (v2/release-world! w)
     (run-captured))))

(deftest an-interrupted-fork-still-starts-the-childs-work
  ;; the fork item commits after its opted-in caller stopped waiting; the
  ;; child's inherited task start must still be scheduled
  (checked
   (let [[ex run-captured] (capturing-executor)
         w (vworld {:executor ex :budget 1})
         worlds (atom [])
         waiting (promise)
         forker (off-thread (fn []
                              (binding [v2/*world* w] (task (swap! worlds conj (v2/current-world)) :x))
                              (deliver waiting (Thread/currentThread))
                              (try (v2/fork! w) (catch InterruptedException _ :interrupted))))
         ^Thread th (deref waiting 2000 nil)]
     (Thread/sleep 50)
     (.interrupt th)
     (is (= :interrupted (deref forker 2000 ::stuck)))
     (loop [n 0] (when (and (< n 20) (pos? (run-captured))) (recur (inc n))))
     (is (= 2 (count (distinct @worlds))) "the task started in the parent and in the child")
     (v2/release-world! w)
     (run-captured))))
