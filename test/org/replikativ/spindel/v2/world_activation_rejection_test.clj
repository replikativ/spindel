(ns org.replikativ.spindel.v2.world-activation-rejection-test
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]))

(defn- env []
  (let [jobs (atom []) executor (reify java.util.concurrent.Executor (execute [_ f] (swap! jobs conj f)))]
    {:p (v2/world {:executor executor}) :q (v2/world {:executor executor}) :jobs jobs}))
(defn- pump! [{:keys [jobs]}]
  (loop [fuel 1000]
    (when-let [f (first @jobs)]
      (assert (pos? fuel)) (swap! jobs subvec 1) (.run ^Runnable f) (recur (dec fuel)))))
(defn- close! [w] (v2/close-world! (v2/world-host-owner w) w))
(defn- cap [w names] (v2/register-world-settlement! (v2/world-host-owner w) w names))
(defn- instance [p]
  (let [pubs (atom [])]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (let [t (task (v2/savepoint :s nil))]
        {:task t :child (v2/instantiate (first @pubs))}))))

(deftest post-intent-items-behind-rejection-never-run-under-the-winning-custody
  (let [{:keys [p q] :as e} (env) {c :child t :task} (instance p)
        qc (cap q [:c]) cc (cap c []) qr (:c (v2/world-preparations qc))
        entered (java.util.concurrent.CountDownLatch. 1) proceed (java.util.concurrent.CountDownLatch. 1)
        original-own @#'v2/own-child! original-internal @#'v2/internal!
        admission (atom []) publisher (atom nil) effects (atom []) rejected (atom []) read (atom [])]
    (try
      (with-redefs-fn {#'v2/internal! (fn [w f] (if (identical? w p) (swap! admission conj f) (original-internal w f)))}
        #(v2/activate! c :must-not-run))
      (with-redefs-fn
        {#'v2/own-child! (fn [w scope child strong?]
                           (let [r (original-own w scope child strong?)]
                             (when (and (identical? w q) (identical? child c))
                               (.countDown entered) (.await proceed)) r))}
        (fn []
          (reset! publisher (future (v2/finish-world-preparation! qr {:world c})))
          (is (.await entered 5 java.util.concurrent.TimeUnit/SECONDS))
          ;; The winner holds after immutable custody, before claim/release.
          ;; Queue the losing S4 rejection first, then ordinary submitted items.
          (aset ^objects c rw/W-INLINE false)
          (doseq [f @admission] (original-internal p f))
          (is (hs/flag? (aget ^objects c rw/W-ACTIVATION-INTENT)))
          (v2/send-world! c #(swap! effects conj :send))
          (v2/host! c #(swap! effects conj :host) #(swap! rejected conj %) nil)
          (v2/value-async (v2/in-world c t) (fn [v failed?] (swap! read conj [v failed?])))
          (pump! e)
          (aset ^objects c rw/W-INLINE true)
          (is (empty? @effects))
          (is (= 1 (count @rejected)))
          (is (:spindel/released (ex-data (first @rejected))))
          (is (= 1 (count @read)))
          (is (:spindel/released (ex-data (ffirst @read))))
          (is (not (:requested? (v2/world-close-status c))) "loser cannot dispose using the winner's authority")
          (is (= 0 (:deferred-host (v2/world-close-status c))))
          (.countDown proceed)
          (is (not= ::timeout (deref @publisher 5000 ::timeout)))))
      (pump! e)
      (v2/acknowledge-world-settlement! cc {:settled? true :value :physically-closed})
      (close! p) (close! q) (pump! e)
      (v2/acknowledge-world-settlement! qc {:settled? true :value :closed})
      (is (:terminal? (v2/world-close-status q)))
      (finally (.countDown proceed) (when @publisher (future-cancel @publisher))))))

(deftest stale-pre-marker-activate-reconciles-rejection-release-and-birth
  (doseq [mode [:custody-rejected :released :born]]
    (let [{:keys [p q] :as e} (env) {c :child t :task} (instance p)
          target (aget ^objects c rw/W-ACTIVATION-INTENT)
          original-set hs/flag-set! original-own @#'v2/own-child!
          entered (java.util.concurrent.CountDownLatch. 1) proceed (java.util.concurrent.CountDownLatch. 1)
          stopped (atom false) delayed (atom nil) read (atom [])]
      (when (= mode :custody-rejected)
        (#'v2/internal-call! q #(original-own q (aget ^objects q rw/W-ROOT) c false)))
      (try
        (with-redefs-fn
          {#'hs/flag-set! (fn [flag value]
                            (when (and (identical? flag target) value (compare-and-set! stopped false true))
                             ;; All public entry checks have passed. Reconcile a
                             ;; completed lifecycle after this stale write resumes.
                              (.countDown entered) (.await proceed))
                            (original-set flag value))}
          (fn []
            (reset! delayed (future (v2/activate! c :stale)))
            (is (.await entered 5 java.util.concurrent.TimeUnit/SECONDS))
            (if (= mode :released) (v2/release-world! c) (v2/activate! c :second))
            (is (not (hs/flag? target)))
            (.countDown proceed)
            (is (not= ::timeout (deref @delayed 5000 ::timeout)))))
        (pump! e)
        (is (not (:activation-pending? (v2/world-close-status c))))
        (is (= 0 (:deferred-host (v2/world-close-status c))))
        (when (= mode :born)
          (v2/value-async (v2/in-world c t) (fn [v failed?] (swap! read conj [v failed?])))
          (is (= [[:second false]] @read)))
        (close! p) (close! q) (pump! e)
        (finally (.countDown proceed) (when @delayed (future-cancel @delayed)))))))
