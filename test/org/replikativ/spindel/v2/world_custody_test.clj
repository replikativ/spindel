(ns org.replikativ.spindel.v2.world-custody-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await await-finalization]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]))

(defn- env []
  (let [jobs (atom []) executor (reify java.util.concurrent.Executor (execute [_ f] (swap! jobs conj f)))]
    {:world (v2/world {:executor executor}) :jobs jobs :executor executor}))
(defn- pump! [{:keys [jobs]}]
  (loop [fuel 1000]
    (when-let [f (first @jobs)]
      (assert (pos? fuel)) (swap! jobs subvec 1) (.run ^Runnable f) (recur (dec fuel)))))
(defn- status [w] (v2/world-close-status w))
(defn- close! [w] (v2/close-world! (v2/world-host-owner w) w))
(defn- cap [w names] (v2/register-world-settlement! (v2/world-host-owner w) w names))
(defn- ack! [c] (v2/acknowledge-world-settlement! c {:settled? true :value :closed}))
(defn- result [f] (try (f) :ok (catch Throwable error (:spindel/invalid (ex-data error)))))

(deftest two-parent-publication-has-one-winner-and-retains-the-loser-reservation
  (let [{p :world :keys [executor] :as e} (env) q (v2/world {:executor executor}) c (v2/world {:executor executor})
        pcap (cap p [:p]) qcap (cap q [:q]) native (cap c [])
        pr (:p (v2/world-preparations pcap)) qr (:q (v2/world-preparations qcap))
        entered (java.util.concurrent.CountDownLatch. 2) proceed (java.util.concurrent.CountDownLatch. 1)
        original-own @#'v2/own-child! callers (atom [])]
    (close! p) (close! q)
    (try
      (with-redefs-fn
        {#'v2/own-child! (fn [w scope child strong?]
                           (when (identical? child c) (.countDown entered) (.await proceed))
                           (original-own w scope child strong?))}
        (fn []
          (reset! callers [(future (result #(v2/finish-world-preparation! pr {:world c})))
                           (future (result #(v2/finish-world-preparation! qr {:world c})))])
          (is (.await entered 5 java.util.concurrent.TimeUnit/SECONDS))
          (.countDown proceed)))
      (let [results (mapv #(deref % 5000 ::timeout) @callers)
            winner (if (= :ok (first results)) p q) loser (if (identical? winner p) q p)
            winning-cap (if (identical? winner p) pcap qcap) losing-cap (if (identical? loser p) pcap qcap)
            losing-reservation (if (identical? loser p) pr qr)]
        (pump! e)
        (is (= #{:ok :world-custody} (set results)))
        (is (= 0 (:preparations (status winner))))
        (is (= 1 (:preparations (status loser))))
        (is (= 1 (:child-terminal (status winner))))
        (is (= 0 (:child-terminal (status loser))))
        (ack! winning-cap)
        (is (not (:terminal? (status winner))))
        (ack! native) (pump! e)
        (is (:terminal? (status winner)))
        ;; The rejected producer certifies no separate acquisition only after
        ;; observing that the one actual shared output has really joined.
        (v2/finish-world-preparation! losing-reservation {:disposed? true})
        (ack! losing-cap) (pump! e)
        (is (:terminal? (status loser))))
      (finally (.countDown proceed) (doseq [f @callers] (future-cancel f))))))

(deftest creation-order-rejects-mutual-publication-without-closing-an-ancestor
  (let [{p :world :keys [executor] :as e} (env) q (v2/world {:executor executor})
        pc (cap p [:q]) qc (cap q [:p]) pr (:q (v2/world-preparations pc)) qr (:p (v2/world-preparations qc))]
    (is (= :ok (result #(v2/finish-world-preparation! pr {:world q}))))
    (is (not (:requested? (status p))))
    (is (= :world-preparation (result #(v2/finish-world-preparation! qr {:world p}))))
    (is (not (:requested? (status p))) "rejection never disposes the older/ancestor output")
    (is (= 1 (:preparations (status q))))
    ;; P was never Q's acquisition: the invalid borrowed ancestor is not
    ;; closed/joined to discharge Q's producer. Certify no acquisition instead.
    (v2/finish-world-preparation! qr {:disposed? true})
    (ack! qc) (pump! e)
    (close! p) (pump! e) (ack! pc)
    (is (:terminal? (status p)))))

(deftest independent-world-ids-and-nested-paths-sort-by-successful-acquisition
  (let [{p :world :keys [executor] :as e} (env) c (v2/world {:executor executor}) d (v2/world {:executor executor})
        pc (cap p [:c :d]) cc (cap c []) dc (cap d [])
        a (ex-info "first" {}) b (ex-info "second" {})]
    (is (= (aget ^objects c rw/ID) (aget ^objects d rw/ID)))
    (v2/call-in! c #(aset ^objects c rw/W-CLOSE (assoc (aget ^objects c rw/W-CLOSE) :audit "z-last")))
    (v2/call-in! d #(aset ^objects d rw/W-CLOSE (assoc (aget ^objects d rw/W-CLOSE) :audit "a-first")))
    (v2/finish-world-preparation! (:c (v2/world-preparations pc)) {:world c})
    (v2/finish-world-preparation! (:d (v2/world-preparations pc)) {:world d})
    (close! p) (pump! e) (ack! pc)
    (v2/acknowledge-world-settlement! dc {:settled? true :error b})
    (v2/acknowledge-world-settlement! cc {:settled? true :error a})
    (pump! e)
    (is (= [a b] (:spindel/cleanup-failures (ex-data (first (:outcome (status p)))))))))

(deftest populated-root-adoption-preserves-real-explicit-scope-authorization
  (let [{p :world :keys [executor] :as e} (env) c (v2/world {:executor executor}) g (v2/fork! c)
        native (cap g []) installed (atom false) rejected (atom nil) finished (atom false)]
    (binding [v2/*world* p]
      (let [gate (v2/deferred)
            owner (task
                   (let [scope (v2/open-scope!)]
                     (#'v2/own-child! (v2/current-world) scope c false)
                     (reset! installed true)
                     (try (await gate)
                          (finally
                            (await-finalization (v2/close-world! g))
                            (reset! finished true)
                            (v2/close-scope-fx! scope)))))]
        (is @installed)
        (let [other (task (try :other
                               (finally (try (v2/close-world! g)
                                             (catch Throwable error (reset! rejected (:spindel/invalid (ex-data error))))))))]
          (is (= :world-target @rejected))
          (hs/fence! other))
        (close! p) (pump! e)
        (is (not @finished))
        (is (:execution-retired? (status g)))
        (ack! native) (pump! e)
        (is @finished)
        (is (:terminal? (status p)))
        (hs/fence! owner)))))

(deftest concurrent-mutual-publication-can-only-install-the-increasing-edge
  (let [{p :world :keys [executor] :as e} (env) q (v2/world {:executor executor})
        pc (cap p [:q]) qc (cap q [:p]) pr (:q (v2/world-preparations pc)) qr (:p (v2/world-preparations qc))
        entered (java.util.concurrent.CountDownLatch. 2) proceed (java.util.concurrent.CountDownLatch. 1)
        original-own @#'v2/own-child! callers (atom [])]
    (try
      (with-redefs-fn
        {#'v2/own-child! (fn [w scope child strong?]
                          ;; Both independent parent prechecks have completed;
                          ;; the central ordering check is still ahead of us.
                           (.countDown entered) (.await proceed)
                           (original-own w scope child strong?))}
        (fn []
          (reset! callers [(future (result #(v2/finish-world-preparation! pr {:world q})))
                           (future (result #(v2/finish-world-preparation! qr {:world p})))])
          (is (.await entered 5 java.util.concurrent.TimeUnit/SECONDS))
          (.countDown proceed)))
      (is (= [:ok :world-publication-order] (mapv #(deref % 5000 ::timeout) @callers)))
      (is (nil? (aget ^objects p rw/W-HOLDER)))
      (is (some? (aget ^objects q rw/W-HOLDER)))
      (is (= 1 (:preparations (status q))))
      (is (not (:requested? (status p))))
      (v2/finish-world-preparation! qr {:disposed? true})
      (ack! qc) (close! p) (pump! e) (ack! pc)
      (is (:terminal? (status p)))
      (finally (.countDown proceed) (doseq [f @callers] (future-cancel f))))))

(deftest order-rejection-keeps-older-open-and-closed-outputs-explicit
  (doseq [released? [false true]]
    (let [{old :world :keys [executor] :as e} (env) p (v2/world {:executor executor})
          pc (cap p [:old]) reservation (:old (v2/world-preparations pc))]
      (when released? (close! old))
      (is (= :world-publication-order (result #(v2/finish-world-preparation! reservation {:world old}))))
      (is (= released? (:requested? (status old))))
      (is (= 1 (:preparations (status p))))
      ;; Explicit adapter reconciliation, never an automatic rejection fallback.
      (close! old) (pump! e)
      (v2/finish-world-preparation! reservation {:disposed? true})
      (close! p) (pump! e) (ack! pc)
      (is (:terminal? (status p))))))

(deftest a-younger-already-terminal-unowned-output-can-be-adopted-for-joined-disposal
  (let [{p :world :keys [executor] :as e} (env) c (v2/world {:executor executor}) pc (cap p [:c])]
    (close! c) (pump! e)
    (is (:terminal? (status c)))
    (is (= :ok (result #(v2/finish-world-preparation! (:c (v2/world-preparations pc)) {:world c}))))
    (close! p) (pump! e) (ack! pc)
    (is (:terminal? (status p)))))

(deftest activation-and-host-publication-share-one-custody-winner
  (doseq [activation-wins? [true false]]
    (let [{p :world :keys [executor] :as e} (env) q (v2/world {:executor executor}) pubs (atom [])
          qc (cap q [:instance]) reservation (:instance (v2/world-preparations qc))]
      (v2/install-handlers! p {:s #(swap! pubs conj %)})
      (binding [v2/*world* p]
        (let [t (task (v2/savepoint :s nil)) c (v2/instantiate (first @pubs)) native (cap c [])
              original-own @#'v2/own-child! entered (java.util.concurrent.CountDownLatch. 1)
              proceed (java.util.concurrent.CountDownLatch. 1) activation (atom nil) read (atom [])]
          (try
            (with-redefs-fn
              {#'v2/own-child! (fn [w scope child strong?]
                                 (if (and (identical? w p) (identical? child c))
                                   (if activation-wins?
                                     (let [r (original-own w scope child strong?)]
                                       (.countDown entered) (.await proceed) r)
                                     (do (.countDown entered) (.await proceed)
                                         (original-own w scope child strong?)))
                                   (original-own w scope child strong?)))}
              (fn []
                (reset! activation (future (v2/activate! c :chosen)))
                (is (.await entered 5 java.util.concurrent.TimeUnit/SECONDS))
                (v2/value-async (v2/in-world c t) (fn [v failed?] (swap! read conj [v failed?])))
                (is (= (if activation-wins? :world-preparation :ok)
                       (result #(v2/finish-world-preparation! reservation {:world c}))))
                (.countDown proceed)
                (is (not= ::timeout (deref @activation 5000 ::timeout)))))
            (pump! e)
            (if activation-wins?
              (do (is (= [[:chosen false]] @read))
                  (is (= 1 (:preparations (status q))))
                  (close! p))
              (do (is (= 1 (count @read)))
                  (is (:spindel/released (ex-data (ffirst @read))))
                  (is (aget ^objects c rw/W-UNBORN))
                  (is (:execution-retired? (status c)))
                  (is (= 1 (:child-terminal (status q))))))
            (pump! e) (ack! native) (pump! e)
            (when activation-wins? (v2/finish-world-preparation! reservation {:disposed? true}))
            (close! p) (close! q) (pump! e) (ack! qc)
            (is (:terminal? (status p)))
            (is (:terminal? (status q)))
            (finally (.countDown proceed) (when @activation (future-cancel @activation)))))))))

(deftest root-host-adoption-does-not-authorize-an-unrelated-engine-task
  (let [{p :world :keys [executor] :as e} (env) c (v2/world {:executor executor}) g (v2/fork! c)
        pc (cap p [:c]) rejected (atom nil)]
    (v2/finish-world-preparation! (:c (v2/world-preparations pc)) {:world c})
    (binding [v2/*world* p]
      (let [t (task (try :body (finally (try (v2/close-world! g)
                                             (catch Throwable error (reset! rejected (:spindel/invalid (ex-data error))))))))]
        (is (= :world-target @rejected)) (hs/fence! t)))
    (close! p) (pump! e) (ack! pc)))

(defn- last-world-chain-fixture []
  (loop [w (v2/world) i 0 worlds [] nodes [] tokens []]
    (if (= i 1000)
      {:last w :worlds worlds :nodes nodes :tokens tokens}
      (recur (v2/fork! w) (inc i)
             (conj worlds (java.lang.ref.WeakReference. w))
             (conj nodes (java.lang.ref.WeakReference. (aget ^objects w rw/W-LINEAGE)))
             (conj tokens (java.lang.ref.WeakReference. (aget ^objects w rw/W-CLEANUP-IDENTITY)))))))

(deftest a-held-last-fork-does-not-retain-historical-worlds-lineage-nodes-or-tokens
  (let [{:keys [last worlds nodes tokens]} (last-world-chain-fixture)
        cleared? #(and (every? (fn [^java.lang.ref.WeakReference x] (nil? (.get x))) worlds)
                       (every? (fn [^java.lang.ref.WeakReference x] (nil? (.get x))) nodes)
                       ;; The one direct immutable witness retains its parent's
                       ;; token. It must not retain the preceding 999 tokens.
                       (every? (fn [^java.lang.ref.WeakReference x] (nil? (.get x))) (butlast tokens)))]
    (is (loop [n 200] (System/gc) (if (cleared?) true (if (zero? n) false (do (Thread/sleep 10) (recur (dec n)))))))
    (is (some? (.get ^java.lang.ref.WeakReference (clojure.core/last tokens))))
    (is (nil? (hs/deref-weak (:parent @(.-parent ^org.replikativ.spindel.v2.core.WorldLineage (aget ^objects last rw/W-LINEAGE))))))
    (close! last)))

(deftest nested-child-failure-path-sorts-before-a-later-direct-sibling
  (let [{p :world :as e} (env) a (v2/fork! p) b (v2/fork! p) g (v2/fork! a)
        gc (cap g []) bc (cap b []) first-error (ex-info "nested first" {}) later-error (ex-info "sibling later" {})]
    (close! p) (pump! e)
    (v2/acknowledge-world-settlement! bc {:settled? true :error later-error})
    (v2/acknowledge-world-settlement! gc {:settled? true :error first-error})
    (pump! e)
    (is (:terminal? (status p)))
    (is (= [first-error later-error]
           (:spindel/cleanup-failures (ex-data (first (:outcome (status p)))))))))
