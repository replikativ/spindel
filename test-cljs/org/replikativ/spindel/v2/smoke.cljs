(ns org.replikativ.spindel.v2.smoke
  "Node smoke run of engine v2 (CLJS)."
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await await-all take!]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.incremental.interval :as iv]))

(defn- ordinary-case [selector ready]
  (task
   (case selector
     :await (await ready)
     :track (await ready)
     :external (await ready)
     :sleep (await ready)
     :spawn (await ready)
     :spin (await ready)
     :fork (await ready)
     :savepoint (await ready)
     :scope (await ready)
     :custom (await ready)
     :custom-helper (await ready))))

(defn- finalizer-case [selector ready]
  (task
   (try :body
        (finally
          (case selector
            :await (await ready)
            :track (await ready)
            :external (await ready)
            :sleep (await ready)
            :spawn (await ready)
            :spin (await ready)
            :fork (await ready)
            :savepoint (await ready)
            :scope (await ready)
            :custom (await ready)
            :custom-helper (await ready))))))

(defn- case-dispatch-smoke! []
  (let [w (v2/world)]
    (try
      (binding [v2/*world* w]
        (let [ready (v2/deferred)]
          (v2/deliver! ready :ok)
          (doseq [selector [:await :track :external :sleep :spawn :spin :fork
                            :savepoint :scope :custom :custom-helper]]
            (let [ordinary (atom []) finalizer (atom [])]
              (v2/value-async (ordinary-case selector ready)
                              (fn [value failed?] (swap! ordinary conj [value failed?])))
              (assert (= [[:ok false]] @ordinary) (str "ordinary case " selector))
              (v2/value-async (finalizer-case selector ready)
                              (fn [value failed?]
                                (swap! finalizer conj
                                       [(:spindel/invalid
                                         (ex-data (first (:spindel/cleanup-failures (ex-data value)))))
                                        failed?])))
              (assert (= [[:finalizer-effect true]] @finalizer) (str "finalizer case " selector))))))
      (println "CASE DISPATCH OK: ordinary 11/11; finalizer admission 11/11")
      (finally (v2/release-world! w)))))

(defn- cleanup-smoke! [done]
  (let [w (v2/world) complete (atom nil) events (atom []) result (atom nil)]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource (fn [cb] (reset! complete cb) nil))]
                 (try
                   (try
                     (try :body
                          (finally
                            (swap! events conj :inner-enter)
                            (v2/await-finalization (v2/cleanup-operation resource))
                            (swap! events conj :inner-exit)))
                     (catch :default _ (swap! events conj :resurrected)))
                   (swap! events conj :suffix)
                   (finally
                     (swap! events conj :outer)
                     (assert (= [:inner-enter :inner-exit :outer] @events))
                     (assert (v2/cancelled? (first @result)))
                     (reset! done true)))))]
        (v2/value-async t (fn [v failed?] (reset! result [v failed?])))
        (v2/cancel-task! t)
        (assert (v2/cancelled? (first @result)))
        (@complete :closed)
        (@complete :duplicate)))))

(defn- cleanup-fork-smoke! [done]
  (let [w (v2/world) complete (atom nil) registrations (atom 0) inherited (atom [])]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource
                               (fn [cb] (swap! registrations inc) (reset! complete cb) nil))]
                 (try :body
                      (finally
                        (try (v2/await-finalization (v2/cleanup-operation resource))
                             (catch :default e
                               (swap! inherited conj (:spindel/forked (ex-data e)))))))))
            child (v2/fork! w)
            child-result (atom nil)]
        (v2/host-call! child (fn [] nil))
        (v2/value-async (v2/in-world child t) #(reset! child-result [%1 %2]))
        (assert (= [:body false] @child-result))
        (assert (= [true] @inherited))
        (v2/value-async t
                        (fn [v failed?]
                          (assert (= [:body false] [v failed?]))
                          (assert (= 1 @registrations))
                          (assert (= [true] @inherited))
                          (reset! done true)))
        (@complete :closed)))))

(defn -main []
  (case-dispatch-smoke!)
  (let [w (v2/world)
        out (atom []) cleanup-done (atom false) fork-cleanup-done (atom false)]
    (cleanup-smoke! cleanup-done)
    (cleanup-fork-smoke! fork-cleanup-done)
    (binding [v2/*world* w]
      (let [a (v2/atom 0) seen (atom [])]
        (v2/host-call! w #(binding [v2/*world* nil]
                            (add-watch a :k (fn [_ _ o n] (swap! seen conj [o n])))))
        (swap! a inc)
        (assert (= [[0 1]] @seen))
        (remove-watch a :k)
        (let [b (v2/atom 0)]
          (swap! a (fn [v] (swap! b inc) (inc v)))
          (assert (= 1 @b)))
        (let [other (v2/world)
              b (binding [v2/*world* other] (v2/atom :other))]
          (binding [v2/*world* other]
            (assert (contains? (try (reset! a :wrong) {} (catch :default e (ex-data e))) :spindel/missing-state))
            (assert (= :other @b)))))
      (let [p (comb/parallel (spin 10) (spin 20))]
        (v2/value-async p (fn [v err?] (assert (not err?)) (assert (= [10 20] v)))))
      (let [s (v2/signal :first)
            c (spin (iv/get-new (track s)))
            keep (v2/observe! c (fn [_ _]))
            r (comb/race c (v2/deferred))
            seen (atom [])]
        (v2/value-async r (fn [v err?] (assert (not err?)) (swap! seen conj v)))
        (v2/write! s :changed)
        (v2/value-async r (fn [v err?] (assert (not err?)) (swap! seen conj v)))
        (assert (= [:first :first] @seen))
        (keep))
      (let [ready (v2/deferred)
            trigger (v2/deferred)
            bad (task (await trigger) (throw (ex-info "first error" {:first true})))
            r (comb/race bad ready)
            seen (atom [])]
        (v2/value-async r (fn [v err?] (swap! seen conj [(:first (ex-data v)) err?])))
        (v2/deliver! trigger :fail)
        (v2/deliver! ready :late)
        (assert (= [[true true]] @seen)))
      (let [winner (v2/deferred) finish (v2/deferred)
            shared (task (await finish))
            r (comb/race winner shared)
            seen (atom [])]
        (v2/deliver! winner :winner)
        (v2/deliver! finish :shared)
        (v2/value-async r (fn [v err?] (assert (not err?)) (swap! seen conj v)))
        (v2/value-async shared (fn [v err?] (assert (not err?)) (swap! seen conj v)))
        (assert (= [:winner :shared] @seen)))
      (let [x (v2/signal 1)
            a (spin (* 10 (iv/get-new (track x))))
            b (spin (+ 1 (await a)))
            d (v2/deferred)
            mb (v2/mailbox)
            t (task (let [[p q] (await-all [b d])] (+ p q (take! mb))))
            _ (v2/observe! b (fn [v _] (swap! out conj [:b v])))]
        (v2/write! x 2)
        (v2/deliver! d 100)
        (v2/post! mb 1000)
        (v2/value-async t (fn [v err?] (swap! out conj [:t v err?])))
        (js/setTimeout
         (fn []
           (let [expected [[:b 11] [:b 21] [:t 1111 false]]]
             (println "observed" @out)
             (assert @cleanup-done "shielded cleanup smoke did not finish")
             (assert @fork-cleanup-done "inherited cleanup smoke did not finish")
             (if (= expected @out)
               (println "SMOKE OK")
               (do (println "SMOKE FAIL, expected" expected) (js/process.exit 1)))))
         50)))))

(set! *main-cli-fn* -main)
