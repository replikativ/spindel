(ns org.replikativ.spindel.lifetime.pending-host-cancellation-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [clojure.walk :as walk]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.host-origin-model-test :as h]
            [org.replikativ.spindel.lifetime.cached-causal-host-test :as cached]
            [org.replikativ.spindel.engine.kernel :as kernel]))

(def a h/a)
(def b h/b)
(defn- view [s]
  (walk/postwalk
   (fn [x]
     (if (and (keyword? x) (#{"cancelled" "released"} (name x))
              (#{"org.replikativ.spindel.engine.kernel" "org.replikativ.spindel.lifetime.model"} (namespace x)))
       (keyword "error" (name x)) x))
   (dissoc s :uses)))

(defn- trace! [initial actions]
  (let [engines (mapv #(kernel/restore initial {:cells? %}) [false true])]
    (reduce
     (fn [states action]
       (let [before (peek states)
             {after :state refusal :refusal} (m/attempt before action)]
         (is (nil? refusal) (pr-str [action refusal]))
         (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
         (is (empty? (inv/edge-check {:before before :action action :after after})) (pr-str action))
         (doseq [engine engines]
           (try
             (kernel/step! engine action)
             (catch #?(:clj Throwable :cljs :default) error
               ;; Preserve the original exception even when ex-data is nil.
               (is false (str "Unexpected kernel failure for " (pr-str action) ": " error))
               (throw error)))
           (let [actual (kernel/snapshot engine)]
             (is (= (view after) (view actual)) (pr-str action))
             (is (empty? (inv/check actual)))
             (is (empty? (inv/edge-check {:before before :action action :after actual})))))
         (conj states after))) [initial] actions)))

(defn- outcomes [states o]
  (vec (for [state (rest states) event (:events state)
             :when (and (= :host-delivery (:event event)) (= a (:world event)) (= o (:o event)))] event)))
(defn- packet [state]
  (first (filter :register-host (m/pending-events state a))))
(defn- running-basis [mode]
  (peek (trace! (m/init-state)
                [{:t :t04 :w a :e :worker :mode :callback}
                 (h/fork a b)
                 {:t :t04 :w b :e :worker :mode mode :filter {:mode :causal-follow}}])))

(deftest current-cancellation-settles-pending-entity-join-once
  (doseq [mode [:deref :callback] installed? [false true]]
    (let [pending (running-basis mode) o (:register-host (packet pending))
          before (if installed? (peek (trace! pending [{:t :queued :w a}])) pending)
          states (trace! before [{:t :t11 :w a :r [:worker 1]}
                                 {:t :t11 :w a :r [:worker 1]}])
          after (peek states)]
      (is (= [{:event :host-delivery :world a :o o :value ::m/cancelled :causal? true}]
             (outcomes states o)))
      (is (contains? (:host-delivered after) [a o]))
      (is (nil? (get-in after [:worlds a :obligations o])))
      (is (empty? (filter :register-host (m/pending-events after a))))
      (is (empty? (:runs (m/wr after a))))
      (is (= (:clocks before) (:clocks after))))))

(deftest pending-cancellation-preserves-queue-and-outside-neighbors
  (doseq [outside? [false true]]
    (let [initial (peek (trace! (m/init-state {:host-registrations 6 :invocations 6})
                               [{:t :t04 :w a :e :prefix :mode :callback}
                                {:t :t04 :w a :e :worker :mode :callback}
                                {:t :t04 :w a :e :suffix :mode :callback}
                                (h/fork a b)
                                {:t :t04 :w b :e :prefix :mode :callback}
                                {:t :t04 :w b :e :worker :mode :callback}
                                {:t :t04 :w b :e :suffix :mode :callback}]))
          [prefix target suffix] (:queue (m/wr initial a))
          held (mapv #(hash-map :w a :event %) [prefix target suffix])
          before (if outside? (-> initial (assoc-in [:worlds a :queue] [])
                                  (assoc-in [:env :outside] held)) initial)
          after (peek (trace! before [{:t :t11 :w a :r [:worker 1]}]))]
      (is (= :worker (:e target)))
      (is (= (if outside? [] [prefix suffix]) (:queue (m/wr after a))))
      (is (= (if outside? [(first held) (last held)] []) (get-in after [:env :outside])))
      (is (= (:seq (m/wr before a)) (:seq (m/wr after a))))
      (is (= (:clocks before) (:clocks after))))))

(deftest withdrawal-before-cancellation-does-not-publish
  (doseq [mode [:deref :callback]]
    (let [before (running-basis mode) o (:register-host (packet before))
          states (trace! before [{:t (if (= mode :deref) :withdraw-deref :unsubscribe) :w a :o o}
                                 {:t :t11 :w a :r [:worker 1]}])]
      (is (empty? (outcomes states o)))
      (is (not (contains? (:host-delivered (peek states)) [a o]))))))

(deftest explicit-cancellation-retains-its-custom-reason
  (doseq [reason [:custom-reason nil false]]
    (let [before (peek (trace! (m/init-state)
                               [{:t :t01 :w a :e :worker :tok :worker-handle}
                                {:t :t04 :w a :e :worker :tok :worker-handle :mode :callback}
                                (h/fork a b)
                                {:t :t04 :w b :e :worker :mode :callback :filter {:mode :causal-follow}}]))
          o (:register-host (packet before))
          states (trace! before [{:t :cancel-computation :w a :e :worker :tok :worker-handle :value reason}])]
      (is (= [reason] (mapv :value (outcomes states o))))
      (is (contains? (:host-delivered (peek states)) [a o])))))

(deftest cached-h1-and-cancellation-share-causal-history
  (doseq [h1-first? [false true]]
    (let [before (peek (trace! (m/init-state)
                               (concat [(first cached/reactive-prefix) (h/fork a b)]
                                       (rest cached/reactive-prefix)
                                       [{:t :t04 :w b :e :worker :mode :callback :filter {:mode :causal-follow}}])))
          o (:register-host (packet before))
          actions (if h1-first? [{:t :queued :w a} {:t :t11 :w a :r [:worker 1]}]
                      [{:t :t11 :w a :r [:worker 1]}])
          states (trace! before actions)
          events (outcomes states o)]
      (is (= 1 (count events)))
      (is (true? (:causal? (first events))))
      (is (= (if h1-first? {:event :host-delivery :world a :o o :causal? true}
                   {:event :host-delivery :world a :o o :value ::m/cancelled :causal? true})
             (first events)))
      (is (contains? (:host-delivered (peek states)) [a o])))))

(deftest stale-predecessor-cancellation-keeps-the-committed-join
  (let [before (peek (trace! (m/init-state)
                             (concat [(first cached/reactive-prefix) (h/fork a b)]
                                     (rest cached/reactive-prefix)
                                     [{:t :signal-write :w a :e :source :value 1}
                                      {:t :t08 :w a :e :source :value 1}
                                      {:t :t04 :w b :e :worker :mode :callback :filter {:mode :causal-follow}}])))
        target (packet before) o (:register-host target)
        states (trace! before [{:t :t11 :w a :r [:worker 1]} {:t :queued :w a}])
        retired (second states) installed (peek states)]
    (is (= :stale (:status (m/run before a [:worker 1]))))
    (is (= target (packet retired)))
    (is (empty? (outcomes states o)))
    (is (= (:ob target) (get-in installed [:worlds a :obligations o])))
    (is (= (m/current before a :worker) (m/current installed a :worker)))))

(deftest t34-keeps-pending-host-release-in-its-original-queue-phase
  ;; The release-profile patch supplies kernel T34 ingress support separately.
  ;; Here the model proves nested T11 cannot consume or reorder these packets.
  (let [before (running-basis :callback) o (:register-host (packet before))
        after (h/checked before {:t :t34 :w a})
        events (:events after)
        host-index (first (keep-indexed #(when (and (= :host-delivery (:event %2)) (= o (:o %2))) %1) events))
        run-index (first (keep-indexed #(when (= :run-exit (:event %2)) %1) events))]
    (is (= [{:event :host-delivery :world a :o o :value ::m/released :causal? true}]
           (outcomes [before after] o)))
    (is (number? run-index))
    (is (number? host-index))
    (when (and (number? run-index) (number? host-index)) (is (< run-index host-index)))))
