(ns org.replikativ.spindel.v2.host-fork-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task spin await await-finalization]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.lifetime :as lt]
            [org.replikativ.spindel.v2.verify :as verify]))

(defn- env [options]
  (let [jobs (atom []) submitted (java.util.concurrent.CountDownLatch. 1)
        executor (reify java.util.concurrent.Executor
                   (execute [_ f] (swap! jobs conj f) (.countDown submitted)))]
    {:p (v2/world (merge {:executor executor :verify? true} options))
     :jobs jobs :submitted submitted}))
(defn- pump! [{:keys [jobs]}]
  (loop [fuel 1000]
    (when-let [f (first @jobs)] (assert (pos? fuel)) (swap! jobs subvec 1) (.run ^Runnable f) (recur (dec fuel)))))
(defn- fork-events [w] (count (filter #(= :fork-host (first (:item %))) (aget ^objects w rw/W-LOG))))
(defn- snapshot [w]
  {:rank @(deref #'v2/world-order) :next-id (#'v2/peek-id w)
   :worlds (:worlds (lt/census (aget ^objects w rw/W-FAMILY) (aget ^objects w rw/W-WATCHES) nil))
   :acquisition (:next-child (aget ^objects w rw/W-CLOSE))
   :owned (some-> (aget ^objects w rw/W-OWNED) hs/msize)
   :fork-host (fork-events w) :epoch (aget ^objects w rw/W-EPOCH)})
(defn- close! [w] (v2/release-world! w))
(defn- failure [f] (try (f) nil (catch Throwable e e)))
(defn- attempt [w failures] (swap! failures conj (failure #(v2/fork! w))))

(deftest noninline-outside-jvm-caller-waits-and-gets-the-one-committed-world
  (let [{:keys [p submitted] :as e} (env {:inline? false}) before (snapshot p)
        caller (future (v2/fork! p))]
    (try
      (is (.await submitted 5 java.util.concurrent.TimeUnit/SECONDS))
      (is (not (realized? caller)))
      (is (= before (snapshot p)))
      (pump! e)
      (let [c (deref caller 5000 ::timeout)]
        (is (not= ::timeout c))
        (is (= rw/T-WORLD (aget ^objects c rw/TYPE)))
        (is (= 1 (fork-events p)))
        (is (= [0 1] (:acquisition (snapshot p)))))
      (close! p) (pump! e)
      (is (:terminal? (aget ^objects p rw/W-CLOSE)))
      (finally (future-cancel caller)))))

(deftest inline-return-preserves-frozen-cow-and-fresh-weak-custody
  (doseq [verify? [false true]]
    (let [violations (atom []) p (v2/world {:verify? verify? :hook (when verify? (verify/checking-hook violations))})]
      (binding [v2/*world* p]
        (let [x (v2/signal 1) c (v2/fork! p) cx (v2/in-world c x)]
          (is (= 1 (v2/value cx)))
          (v2/write! x 2) (is (= 1 (v2/value cx)))
          (v2/write! cx 3) (is (= 2 (v2/value x)))
          (is (= 3 (v2/value cx)))
          (is (not (identical? (aget ^objects p rw/W-CUSTODY) (aget ^objects c rw/W-CUSTODY))))
          (is (nil? (aget ^objects (aget ^objects c rw/W-HOLDER) 0)))
          (when verify? (is (empty? @violations)) (is (empty? (verify/world-close-violations p))))
          (close! p))))))

(deftest same-world-host-item-and-real-observer-callback-handoff-after-unlock
  (doseq [queued? [false true] throws? [false true]]
    (let [jobs (atom []) marker (atom false) child (atom nil) child-work (atom []) handoffs (atom [])
          executor (reify java.util.concurrent.Executor (execute [_ f] (if queued? (swap! jobs conj f) (.run ^Runnable f))))
          p (v2/world {:executor executor}) original-handoff @#'v2/handoff!
          original-own @#'v2/own-child! expected-child (atom nil) callback-thread (atom nil)]
      (binding [v2/*world* p]
        (let [gate (v2/deferred) x (v2/signal 0)
              worker (task (await gate)
                           (when-not (identical? p (v2/current-world))
                             (swap! child-work conj [@marker (hs/held? (aget ^objects p rw/W-LOCK))])))
              withdraw (v2/observe! x
                                    (fn [value failed?]
                                      (when (and (not failed?) (= 1 value))
                                        (reset! callback-thread (Thread/currentThread))
                                        (reset! marker true)
                                        (try
                                          (v2/deliver! gate :go)
                                          (reset! child (v2/fork! p))
                                          (is (hs/held? (aget ^objects p rw/W-LOCK)))
                                          (is (some? (aget ^objects @child rw/W-HOLDER)))
                                          (when throws? (throw (ex-info "callback throws after accepting child" {})))
                                          (finally (reset! marker false))))))]
          (with-redefs-fn
            {#'v2/own-child! (fn [w scope c strong?]
                               (let [value (original-own w scope c strong?)]
                                 (when (and (identical? p w) (identical? @callback-thread (Thread/currentThread)))
                                   (reset! expected-child c))
                                 value))
             #'v2/handoff! (fn [w]
                             ;; Capture the accepted child before fork! returns,
                             ;; preserving red detection of an early handoff.
                             (when (identical? w @expected-child)
                               (swap! handoffs conj [@marker (hs/held? (aget ^objects p rw/W-LOCK))]))
                             (original-handoff w))}
            #(let [error (failure (fn [] (v2/write! x 1)))]
               (is (= throws? (some? error)))
               (pump! {:jobs jobs})))
          (is (some? @child))
          (is (identical? @child @expected-child))
          (is (seq @handoffs))
          (is (every? #{[false false]} @handoffs))
          (is (= [[false false]] @child-work))
          ;; A later parent request owns the accepted child even when the
          ;; observer callback threw before returning to its gate owner.
          (let [c @child cap (v2/register-world-settlement! (v2/world-host-owner c) c [])]
            (close! p) (pump! {:jobs jobs})
            (is (= 1 (:child-terminal (v2/world-close-status p))))
            (v2/acknowledge-world-settlement! cap {:settled? true :value :closed})
            (pump! {:jobs jobs})
            (is (:terminal? (v2/world-close-status p))))
          (withdraw) (hs/fence! worker))))))

(deftest same-world-ordinary-host-item-can-return-a-child
  (let [p (v2/world) c (atom nil)]
    (v2/host! p #(reset! c (v2/fork! p)))
    (is (some? @c)) (close! p)))

(deftest forbidden-contexts-refuse-before-enqueue-or-allocation
  (let [p (v2/world {:verify? true}) q (v2/world) failures (atom []) before (snapshot p)]
    (binding [v2/*world* p]
      (let [t (task (attempt p failures)) c (spin (attempt p failures))
            ft (task (try :body (finally (attempt p failures))))
            ct (task (let [r (v2/cleanup-resource (fn [cb] (attempt p failures) (cb :closed) nil))]
                       (try :body (finally (await-finalization (v2/cleanup-operation r))))))]
        (v2/value c)
        (v2/host! q #(attempt p failures))
        (is (= 5 (count @failures)))
        (is (every? some? @failures))
        (is (= (:rank before) (:rank (snapshot p))))
        (is (= 0 (fork-events p)))
        (is (nil? (aget ^objects p rw/W-OWNED)))
        (is (hs/mpsc-empty? (aget ^objects p rw/W-INGRESS)))
        (hs/fence! [t c ft ct])))
    (doseq [invalid [nil {} [] (object-array 2)]] (is (some? (failure #(v2/fork! invalid)))))
    (close! p) (close! q)))

(deftest lifecycle-order-is-decided-on-the-source-control-turn
  (doseq [close-first? [true false]]
    (let [{:keys [p] :as e} (env {:inline? false}) before (snapshot p)
          original-internal @#'v2/internal! fork-submitted (java.util.concurrent.CountDownLatch. 1)
          fork-thread (atom nil)]
      (when close-first? (close! p))
      (with-redefs-fn
        {#'v2/internal! (fn [w f]
                          (let [value (original-internal w f)]
                            ;; The close may already have scheduled the drainer.
                            ;; Signal THIS actual control enqueue, not any job.
                            (when (and (identical? p w) (identical? @fork-thread (Thread/currentThread)))
                              (.countDown fork-submitted))
                            value))}
        (fn []
          (let [caller (future (reset! fork-thread (Thread/currentThread))
                               (try [:child (v2/fork! p)] (catch Throwable error [:error error])))]
            (try
              (is (.await fork-submitted 5 java.util.concurrent.TimeUnit/SECONDS))
              (when-not close-first? (close! p))
              (pump! e)
              (let [[kind value] (deref caller 5000 [::timeout nil])]
                (if close-first?
                  (do (is (= :error kind)) (is (:spindel/released (ex-data value)))
                      (is (= (:rank before) (:rank (snapshot p)))) (is (= 0 (fork-events p))))
                  (do (is (= :child kind)) (is (some? (aget ^objects value rw/W-HOLDER)))
                      (is (= 1 (fork-events p))) (is (:terminal? (aget ^objects value rw/W-CLOSE))))))
              (is (:terminal? (aget ^objects p rw/W-CLOSE)))
              (finally (future-cancel caller)))))))))

(deftest unborn-refusal-is-never-replayed-after-birth
  (doseq [phase [:before-intent :intent :claim]]
    (let [p (v2/world) pubs (atom []) pending (atom []) original-internal @#'v2/internal!
          initiator (Thread/currentThread)]
      (v2/install-handlers! p {:s #(swap! pubs conj %)})
      (binding [v2/*world* p]
        (let [t (task (v2/savepoint :s nil)) c (v2/instantiate (first @pubs))]
          (case phase
            :before-intent nil
            ;; activate!'s first after-gate call is OUTSIDE any gate (cw=nil).
            ;; Pause this exact child submission before delegation; a cw=c hook
            ;; would instead stop after the child claim and merge the windows.
            :intent (with-redefs-fn
                      {#'v2/internal! (fn [w f]
                                        (if (and (identical? c w) (identical? initiator (Thread/currentThread)))
                                          (swap! pending conj #(original-internal c f))
                                          (original-internal w f)))}
                      #(v2/activate! c :go))
            :claim (with-redefs-fn {#'v2/internal! (fn [w f] (if (and (identical? w p) (identical? initiator (Thread/currentThread)))
                                                               (swap! pending conj #(original-internal p f))
                                                               (original-internal w f)))} #(v2/activate! c :go)))
          (when (= phase :intent)
            (is (hs/flag? (aget ^objects c rw/W-ACTIVATION-INTENT)))
            (is (nil? (:identity (aget ^objects c rw/W-ACTIVATION)))))
          (when (= phase :claim)
            (is (hs/flag? (aget ^objects c rw/W-ACTIVATION-INTENT)))
            (is (some? (:identity (aget ^objects c rw/W-ACTIVATION)))))
          (let [before (snapshot c)]
            (is (some? (failure #(v2/fork! c))))
            (is (= before (snapshot c)))
            (doseq [f @pending] (f))
            (when (= phase :before-intent) (v2/activate! c :go))
            (is (= (:rank before) (:rank (snapshot c))))
            (is (= 0 (fork-events c)))
            (is (nil? (aget ^objects c rw/W-OWNED))))
          (close! p) (hs/fence! t))))))

(deftest predictable-capacity-refusal-precedes-every-source-mutation
  (let [p (v2/world {:verify? true})]
    (v2/call-in! p #(aset ^objects p rw/W-CLOSE (assoc (aget ^objects p rw/W-CLOSE) :next-child [4294967295 4294967295])))
    (let [before (snapshot p)]
      (is (= :world-acquisition-order-exhausted (:spindel/invalid (ex-data (failure #(v2/fork! p))))))
      (is (= before (snapshot p))))
    (close! p))
  (let [p (v2/world {:verify? true}) before (snapshot p)
        isolated (atom [4294967295 4294967295])
        original-allocate @#'v2/allocate-world-order! initiator (Thread/currentThread)]
    ;; Exercise the real allocator with isolated storage; never reset the live
    ;; process allocator or let a successful World reuse an ordinal.
    (with-redefs-fn {#'v2/allocate-world-order!
                     (fn [] (if (and (identical? initiator (Thread/currentThread))
                                     (identical? p (#'v2/cw)))
                              (swap! isolated #'v2/next-world-order) (original-allocate)))}
      #(is (= :world-order-exhausted (:spindel/invalid (ex-data (failure (fn [] (v2/fork! p))))))))
    (is (= [4294967295 4294967295] @isolated))
    (is (= before (snapshot p))) (close! p)))

(defn- closed-child-fixture []
  (let [p (v2/world) c (v2/fork! p) payload (byte-array (* 1024 1024))
        world (java.lang.ref.WeakReference. c) private (java.lang.ref.WeakReference. payload)]
    (v2/reset-world! c {:payload payload}) (close! c)
    {:parent p :world world :payload private}))
(deftest a-live-parent-does-not-retain-a-closed-child-or-private-payload
  (let [{:keys [parent world payload]} (closed-child-fixture)
        ready? #(and (nil? (.get ^java.lang.ref.WeakReference world)) (nil? (.get ^java.lang.ref.WeakReference payload)))]
    (is (loop [n 100] (System/gc) (if (ready?) true (if (zero? n) false (do (Thread/sleep 10) (recur (dec n)))))))
    (is (not (:requested? (v2/world-close-status parent))))
    (dotimes [_ 1000] (close! (v2/fork! parent)))
    (is (= 1 (:worlds (lt/census (aget ^objects parent rw/W-FAMILY) (aget ^objects parent rw/W-WATCHES) nil))))
    (is (<= (reduce + 0 (map #(count (aget ^objects % 0)) (hs/mvals (aget ^objects parent rw/W-OWNED)))) 16))
    (is (zero? (count (aget ^objects parent rw/W-AFTER))))
    (close! parent)))

(deftest a-real-result-callback-can-return-a-child-between-slices
  (let [p (v2/world) child (atom nil)]
    (binding [v2/*world* p]
      (let [t (task :ready)]
        (v2/value-async t (fn [_ failed?]
                            (is (not failed?))
                            (is (hs/held? (aget ^objects p rw/W-LOCK)))
                            (reset! child (v2/fork! p))))
        (is (some? @child))
        (is (some? (aget ^objects @child rw/W-HOLDER)))
        (close! p) (hs/fence! t)))))
