(ns org.replikativ.spindel.v2.formal-review-test
  "Engine fixes from the ansatz formal review (2026-11-17): I12 on revalidation,
   host items refused after release, exact `blocked?` beyond depth 64, kind
   checks on host source operations, `(await-any [])`, readoption by kind."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)
(defn- vworld [] (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))
(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))
(defn- wait-until [f] (loop [n 400] (or (f) (when (pos? n) (Thread/sleep 5) (recur (dec n))))))
(defn- rank [w h] (v2/call-in! w #(aget ^objects (#'v2/row-of h) rw/C-RANK)))
(defn- invalid [f] (try (f) :accepted (catch clojure.lang.ExceptionInfo e (or (:spindel/invalid (ex-data e)) (throw e)))))

(deftest revalidation-raises-the-rank
  ;; I12/I14: c reads d; c is demoted; d reruns with the same value and now awaits a deeper
  ;; e, so it is raised; c's revalidation must raise c above d
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [flag (v2/signal false)
             e1 (spin 1) e2 (spin (inc (await e1))) e3 (spin (inc (await e2)))
             d (spin (if (iv/get-new (track flag)) (do (await e3) 1) 1))
             c (spin (inc (await d)))
             stop-d (v2/observe! d (fn [_ _]))
             stop-c (v2/observe! c (fn [_ _]))]
         (is (= 2 (v2/value c 1000 ::timeout)))
         (stop-c)
         (v2/write! flag true)
         (is (= 1 (v2/value d 1000 ::timeout)))
         (is (wait-until #(> (long (rank w d)) 1)) "d was raised")
         (is (= 2 (v2/value c 1000 ::timeout)))
         (is (> (long (rank w c)) (long (rank w d))) "I12 after revalidation")
         (stop-d))))))

(deftest host-items-queued-before-release-are-refused
  (checked
   (let [w (vworld)
         s (binding [v2/*world* w] (v2/signal 1))
         lk (aget ^objects w rw/W-LOCK)
         ran (atom false)]
     (hs/lock! lk)
     (let [queued #(count (seq (aget ^objects w rw/W-INGRESS)))
           op1 (future (v2/write! s 2))
           _ (is (wait-until #(= 1 (queued))))
           op2 (future (binding [v2/*world* w] (task (reset! ran true) :ran)))
           _ (is (wait-until #(= 2 (queued))))
           ops [op1 op2]]
       (#'v2/release-world* w)                  ; T21 first
       (hs/unlock! lk)
       (is (nil? (try (#'v2/process! w) nil (catch Throwable t t))))
       (run! #(deref % 1000 ::timeout) ops)
       (is (true? (v2/await-complete w 2000 ::timeout)))
       (is (false? @ran) "no task body runs in a released world")
       (is (= [[:release-world true] [:write false] [:spawn-top false]]
              (mapv (juxt (comp first :item) :accepted)
                    (drop-while #(not= :release-world (first (:item %))) (verify/log w)))))))))

(deftest a-blocked-chain-deeper-than-64
  ;; §4.5.6 is a least fixpoint without a depth bound: 100 tasks, each awaiting the next,
  ;; the last a deferred: the first is blocked
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [gate (v2/deferred)
             ts (loop [i 0 prev gate acc []]
                  (if (= i 100) acc
                      (let [t (let [p prev] (task (await p)))] (recur (inc i) t (conj acc t)))))
             top (peek ts)]
         (is (wait-until #(v2/call-in! w (fn [] (#'v2/blocked? w (#'v2/row-of top) 0)))))
         (v2/deliver! gate :go)
         (is (= :go (v2/value top 2000 ::timeout))))))))

(deftest host-source-operations-check-kinds
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 1) d (v2/deferred) m (v2/mailbox) t (task 1)]
         (is (= [:write :deliver :post :release]
                [(invalid #(v2/write! d 1)) (invalid #(v2/deliver! s 1))
                 (invalid #(v2/post! s 1)) (invalid #(v2/sem-release! m))]))
         (is (= :accepted (invalid #(do (v2/pin! t) (v2/unpin! t)))) "a task may be pinned")
         (is (= :take (try (v2/value (task (v2/take! s)) 1000 ::timeout) nil
                           (catch clojure.lang.ExceptionInfo e (:spindel/invalid (ex-data e))))))
         (is (= 1 (v2/value s)) "nothing changed")
         (v2/post! m :x)
         (is (= :x (v2/value (task (v2/take! m)) 1000 ::timeout)) "the right kind still works"))))))

(deftest await-any-of-nothing-is-an-error
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (is (= :any (try (v2/value (task (v2/await-any [])) 1000 ::timeout) nil
                        (catch clojure.lang.ExceptionInfo e (:spindel/invalid (ex-data e))))))
       (is (= [] (v2/value (task (v2/await-all [])) 1000 ::timeout)))))))

(deftest readoption-needs-the-same-kind
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [flag (v2/signal false)
             c (spin (if (iv/get-new (track flag)) (v2/mailbox) (v2/signal 1)))
             stop (v2/observe! c (fn [_ _]))
             h1 (v2/value c 1000 ::timeout)]
         (is (= 1 (v2/value h1 1000 ::timeout)))
         (v2/write! flag true)
         (is (wait-until #(not= h1 (v2/value c 1000 ::timeout))))
         (let [h2 (v2/value c 1000 ::timeout)]
           (v2/post! h2 :x)                      ; a mailbox, not the readopted signal
           (is (= :x (v2/value (task (v2/take! h2)) 1000 ::timeout))))
         (stop))))))

(deftest world-id-is-the-worlds-own
  (let [w (v2/world {})
        c (v2/fork! w)]
    (is (number? (v2/world-id w)))
    (is (not= (v2/world-id w) (v2/world-id c)) "a fork has its own id")))

(deftest a-host-operation-inside-a-slice-starts-no-nested-slice
  ;; D0: one slice per world. observe!/value-async/pin! of a computation that needs a run,
  ;; called from a running body, queue its run; an await (which parks first) still runs the
  ;; debtor inline
  (let [depths (atom [])
        orig @#'v2/slice!]
    (with-redefs [v2/slice! (fn [r g]
                              (let [r* (#'v2/active-run)]
                                (swap! depths conj (boolean (and r* (aget ^objects r* rw/R-SLICE)))))
                              (orig r g))]
      (checked
       (let [w (vworld)]
         (binding [v2/*world* w]
           (let [c (spin (+ 1 2)) d (spin (+ 3 4)) seen (promise) seen2 (promise)]
             (is (= :ok (v2/value (task (v2/observe! c (fn [v _] (deliver seen v)))
                                        (v2/value-async d (fn [v _] (deliver seen2 v)))
                                        :ok)
                                  1000 ::timeout)))
             (is (= [3 7] [(deref seen 1000 ::none) (deref seen2 1000 ::none)]))
             (is (not-any? true? @depths) "no slice starts while another run holds the slice")
             (is (= 2 (v2/value (task (inc (await (spin 1)))) 1000 ::timeout)) "awaits unchanged"))))))))

(deftest host-creations-queued-before-release-are-refused
  ;; a host signal or pull sequence admitted before T21 and processed after it (refusal
  ;; samples, root-shut): refused like every other host item
  (checked
   (let [w (vworld)
         lk (aget ^objects w rw/W-LOCK)
         queued #(count (seq (aget ^objects w rw/W-INGRESS)))]
     (hs/lock! lk)
     (let [a (future (binding [v2/*world* w] (v2/signal 3)))
           _ (is (wait-until #(= 1 (queued))))
           b (future (binding [v2/*world* w] (v2/aseq [k 0] (when (< k 1) [k (inc k)]))))
           _ (is (wait-until #(= 2 (queued))))]
       (#'v2/release-world* w)
       (hs/unlock! lk)
       (is (nil? (try (#'v2/process! w) nil (catch Throwable t t))))
       (deref a 1000 nil) (deref b 1000 nil)
       (is (= [[:release-world true] [:create-source-top false] [:create-link-top false]]
              (mapv (juxt (comp first :item) :accepted)
                    (drop-while #(not= :release-world (first (:item %))) (verify/log w)))))
       (is (true? (v2/await-complete w 2000 ::timeout)))))))

(deftest a-body-creates-nothing-after-its-world-is-released
  ;; user decision 2026-11-18 (model root-shut on body paths): a released world takes no new
  ;; work from bodies either. Releasing from a body cancels every run (tasks through the root
  ;; scope, computations through their revoked demand), and a creation in a released world
  ;; throws ::released before any item; either way nothing is created
  (doseq [mk [:task :spin]]
    (checked
     (let [w (vworld)
           seen (atom [])
           attempt (fn [label f]
                     (swap! seen conj [label (try (some? (f))
                                                  (catch clojure.lang.ExceptionInfo _ false))]))]
       (binding [v2/*world* w]
         (let [body (fn [] (v2/release-world! w))
               x (case mk
                   :task (task (body)
                               (attempt :spawn #(task 1))
                               (attempt :create-comp #(spin 1))
                               (attempt :signal #(v2/signal 1))
                               (attempt :aseq #(v2/aseq [k 0] (when (< k 1) [k (inc k)]))))
                   :spin (spin (body)
                               (attempt :spawn #(task 1))
                               (attempt :create-comp #(spin 1))
                               (attempt :signal #(v2/signal 1))
                               (attempt :aseq #(v2/aseq [k 0] (when (< k 1) [k (inc k)])))))]
           (when (= mk :spin) (v2/value-async x (fn [_ _])))
           (is (true? (v2/await-complete w 2000 ::timeout)))
           (is (every? (comp false? second) @seen) (str mk ": no handle " @seen))
           (is (not-any? #(#{:spawn :create-comp :create-source :create-link} (first (:item %)))
                         (drop-while #(not= :release-world (first (:item %))) (verify/log w))))))))))
