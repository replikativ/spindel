(ns org.replikativ.spindel.lifetime.pending-host-withdrawal-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.host-origin-model-test :as h]
            [org.replikativ.spindel.engine.kernel :as kernel]))

(def a h/a)
(def b h/b)
(def observer [:o 2])
(def other-observer [:o 3])
(defn- basis-at [mode source creditor]
  (h/walk! (m/init-state {:slices? true :host-registrations 4 :invocations 4})
           (into (if (= a source) [(h/fork a b)] [(h/fork a b) (h/fork b h/c)])
                 [{:t :t04 :w source :e :worker :mode :callback}
                  (assoc h/park :w source)
                  {:t :t04 :w creditor :e :worker :mode mode}
                  {:t :t04 :w creditor :e :worker :mode :callback
                   :filter {:mode :causal-follow :origin creditor}}]) true))
(defn- basis [mode] (basis-at mode a b))
(defn- view [state]
  ;; These comparisons cover withdrawal or unchanged refusal, not generated
  ;; producer outcomes. Preserve every application value and diagnostic.
  (dissoc state :uses))

(defn- withdrawal [mode]
  {:t (if (= :deref mode) :withdraw-deref :unsubscribe) :w a :o observer})
(defn- packets [state]
  (filter :register-host (m/pending-events state a)))
(defn- refused-unchanged! [before action error]
  (let [{:keys [state refusal]} (m/attempt before action)]
    (is (= error (:error refusal)))
    (is (= before state)))
  (doseq [cells? [false true]]
    (let [engine (kernel/restore before {:cells? cells?})
          actual-error (try (kernel/step! engine action) nil
                            (catch #?(:clj Exception :cljs :default) e (:error (ex-data e))))]
      (is (= (name error) (some-> actual-error name)))
      (is (= (view before) (view (kernel/snapshot engine)))))))

(deftest pending-host-withdrawal-preserves-unrelated-queue-and-computation
  (doseq [mode [:deref :callback]]
    (let [before (basis mode)
          target (first (packets before))
          other (second (packets before))
          after (h/walk! before [(withdrawal mode) (withdrawal mode)] true)]
      (is (= observer (:register-host target)))
      (is (= other-observer (:register-host other)))
      (is (= [other] (:queue (m/wr after a))))
      (is (= (:entities (m/wr before a)) (:entities (m/wr after a))))
      (is (= (:runs (m/wr before a)) (:runs (m/wr after a))))
      (is (= (:seq (m/wr before a)) (:seq (m/wr after a))))
      (is (= (:clocks before) (:clocks after)))
      (is (nil? (get-in after [:worlds a :obligations observer])))
      ;; Consuming the preserved registration cannot resurrect the removed one.
      (let [installed (h/walk! after [{:t :queued :w a}] true)]
        (is (nil? (get-in installed [:worlds a :obligations observer])))
        (is (= (:ob other) (get-in installed [:worlds a :obligations other-observer])))))))

(deftest pending-host-withdrawal-keeps-deref-and-standing-callback-distinct
  (refused-unchanged! (basis :callback)
                      {:t :withdraw-deref :w a :o observer} ::m/not-host-deref)
  (refused-unchanged! (basis :deref)
                      {:t :unsubscribe :w a :o observer} ::m/not-standing))

(deftest installed-host-deref-withdrawal-is-a-sealed-cancellation-control
  (let [installed (h/walk! (basis :deref) [{:t :queued :w a}] true)
        ;; Admission guard checkpoint, not a claim that T26 leaves the same
        ;; one-shot row installed after its own cancellation work.
        before (-> installed (assoc-in [:worlds a :status] :sealed)
                   (assoc-in [:worlds a :admission] :fenced)
                   (assoc-in [:worlds a :seal-seq]
                             (max (get-in installed [:clocks a] 0)
                                  (get-in installed [:worlds a :seq] 0))))
        after (h/walk! before [(withdrawal :deref) (withdrawal :deref)] true)]
    (is (nil? (get-in after [:worlds a :obligations observer])))
    (is (= (:queue (m/wr before a)) (:queue (m/wr after a))))
    (is (= (:entities (m/wr before a)) (:entities (m/wr after a))))
    (is (= (:runs (m/wr before a)) (:runs (m/wr after a))))
    (is (= (:clocks before) (:clocks after)))))

(defn- sealed-cached-basis
  ([mode neighbor?] (sealed-cached-basis mode neighbor? 42))
  ([mode neighbor? value]
   (let [initial (h/walk! (m/init-state {:slices? true :host-registrations 5 :invocations 5})
                          [(h/fork a b) (h/fork b h/c)
                           {:t :t02 :w b :e :pulse :kind :signal :value 0}
                           {:t :t04 :w b :e :worker :mode :callback}
                           {:t :t05 :w b :r [:worker 1] :kind :track :debtor [:entity b :pulse] :order 0}
                           {:t :t07 :w b :r [:worker 1] :value value}
                           {:t :queued :w b}] true)
         sealed (h/checked initial {:t :t26 :k [:cap b] :op :seal-cached :kind :discard
                                    :caller (m/execution-holder a [:root a])})]
     (is (= :sealed (:status (m/wr sealed b))))
     (is (= :completed (:status (m/run sealed b [:worker 1]))))
     (is (= value (:result (m/ent sealed b :worker))))
    ;; T26 and enqueueing a HOST into a sealed debtor are model setup. Neither
    ;; enables the kernel's intentionally unsupported cut/seal entry surfaces.
    ;; The live descendant can request this existing cache without entering B.
     (reduce h/checked sealed
             (cond-> [{:t :t04 :w h/c :e :worker :mode mode}
                      {:t :t04 :w h/c :e :worker :mode :callback
                       :filter {:mode :causal-follow :origin h/c}}]
               neighbor? (conj {:t :t04 :w h/c :e :worker :mode :callback}))))))

(deftest sealed-pending-host-withdrawal-preserves-queue-and-outside-order
  (doseq [mode [:deref :callback] outside? [false true]]
    (let [sealed (sealed-cached-basis mode false)
          [target other] (filter :register-host (m/pending-events sealed b))
          ;; Outside registration is also a valid physical checkpoint extent;
          ;; moving the exact immutable envelope preserves its allocated seq.
          before (if outside?
                   (-> sealed (update-in [:worlds b :queue] #(vec (remove #{target} %)))
                       (update-in [:env :outside] (fnil conj []) {:w b :event target}))
                   sealed)
          action (assoc (withdrawal mode) :w b)
          after (h/walk! before [action action] true)]
      (is (= observer (:register-host target)))
      (is (= other-observer (:register-host other)))
      (is (> (:seq target) (:seal-seq (m/wr sealed b))))
      (is (= [other] (vec (filter :register-host (:queue (m/wr after b))))))
      (is (empty? (get-in after [:env :outside])))
      (is (= (:clocks before) (:clocks after)))
      (is (= (:entities (m/wr before b)) (:entities (m/wr after b))))
      (is (= (:runs (m/wr before b)) (:runs (m/wr after b)))))))

(deftest pending-host-withdrawal-preserves-neighboring-outside-envelopes
  (doseq [mode [:deref :callback]]
    (let [sealed (sealed-cached-basis mode true)
          [target prefix suffix :as registrations] (vec (filter :register-host (m/pending-events sealed b)))
          neighbors (mapv #(hash-map :w b :event %) [prefix target suffix])
          ;; Real immutable registration envelopes in a valid sealed-world
          ;; extent; withdrawing the middle one must preserve both neighbors.
          before (-> sealed
                     (update-in [:worlds b :queue] #(vec (remove (set registrations) %)))
                     (assoc-in [:env :outside] neighbors))
          after (h/walk! before [(assoc (withdrawal mode) :w b)] true)]
      (is (= 3 (count registrations)))
      (is (= [(first neighbors) (last neighbors)] (get-in after [:env :outside])))
      (is (= (:clocks before) (:clocks after)))
      (is (= (:queue (m/wr before b)) (:queue (m/wr after b)))))))

(deftest sealing-current-work-settles-its-already-pending-hosts-before-withdrawal
  (doseq [mode [:deref :callback]]
    (let [before (basis-at mode b h/c)
          sealed (h/checked before {:t :t26 :k [:cap b] :op :seal-existing :kind :discard
                                    :caller (m/execution-holder a [:root a])})
          deliveries (filter #(= :host-delivery (:event %)) (:events sealed))
          after (h/walk! sealed [(assoc (withdrawal mode) :w b)] true)]
      (is (= {[:o 0] 1 observer 1 other-observer 1} (frequencies (map :o deliveries))))
      (is (every? #(= ::m/cancelled (:value %)) deliveries))
      (is (empty? (filter :register-host (m/pending-events sealed b))))
      (is (nil? (m/run sealed b [:worker 1])))
      (is (= (:entities (m/wr sealed b)) (:entities (m/wr after b))))
      (is (= (:runs (m/wr sealed b)) (:runs (m/wr after b))))
      (is (= (:clocks sealed) (:clocks after)))
      (is (empty? (:events after))))))

(deftest sealed-withdrawal-preserves-application-data-even-with-runtime-enum-names
  (doseq [value [::kernel/cancelled ::m/cancelled {:nested [::kernel/cancelled ::m/released]}]]
    (let [before (sealed-cached-basis :deref false value)
          action (assoc (withdrawal :deref) :w b)
          after (h/checked before action)]
      ;; Use this namespace's exact canonical view, without the host-origin
      ;; harness's generated-error-domain conversion, for application payloads.
      (doseq [cells? [false true]]
        (let [engine (kernel/restore before {:cells? cells?})]
          (kernel/step! engine action)
          (let [actual (kernel/snapshot engine)]
            (is (= (view after) (view actual)))
            (is (= value (get-in actual [:worlds b :entities :worker :result])))))))))

(deftest pending-host-proof-rejects-forged-origin-debtor-or-duplicate-envelope
  (let [before (basis :deref)
        target (first (packets before))]
    (doseq [bad [(assoc-in before [:worlds a :queue 0 :ob :filter :origin] a)
                 (assoc-in before [:worlds a :queue 0 :ob :debtor] [:entity b :worker])
                 (assoc-in before [:worlds a :queue 0 :e] :different)
                 (update-in before [:env :outside] conj {:w a :event target})]]
      (refused-unchanged! bad (withdrawal :deref) ::m/invalid-host-registration))))

(deftest pending-host-withdrawal-does-not-delete-stale-cold-start-controls
  (let [initial (basis :deref)
        request {:start-for :worker :creditor-world b :o [:o 999]}
        ;; A stale request is deliberately retained: creditor cancellation and
        ;; HOST withdrawal have different envelope lifetime rules.
        before (m/enqueue initial a request)
        stale (last (:queue (m/wr before a)))
        after (h/walk! before [(withdrawal :deref)] true)]
    (is (= stale (last (:queue (m/wr after a)))))
    (is (= (vec (rest (:queue (m/wr before a)))) (:queue (m/wr after a))))))

(deftest pending-host-withdrawal-retains-quiescent-cut-refusal
  (doseq [mode [:deref :callback]]
    (let [before (assoc-in (basis mode) [:cuts :cut]
                           {:protocol :p1q :phase :fenced :participants {:worlds #{a}}})]
      (refused-unchanged! before (withdrawal mode) ::m/not-admitted))))

(deftest host-withdrawal-does-not-revoke-an-already-committed-delivery
  (let [before (h/walk! (basis :deref)
                        [{:t :queued :w a}
                         {:t :t06 :w a :o [:o 1] :value 42}
                         {:t :t07 :w a :r [:worker 1] :value 42}
                         {:t :queued :w a} {:t :queued :w a}] true)
        committed (:events before)
        after (h/walk! before [(withdrawal :deref) (withdrawal :deref)] true)]
    (is (some #(and (= :host-delivery (:event %)) (= observer (:o %))) committed))
    (is (nil? (get-in after [:worlds a :obligations observer])))
    (is (= (:entities (m/wr before a)) (:entities (m/wr after a))))
    (is (= (:runs (m/wr before a)) (:runs (m/wr after a))))
    (is (empty? (:events after)))))

(deftest ordinary-active-cut-keeps-the-existing-operation-distinction
  (doseq [phase [:fenced :ready :captured :attached]]
    (let [before (-> (basis :callback)
                     (assoc-in [:worlds a :admission] :fenced)
                     (assoc-in [:cuts :cut]
                               {:protocol :p1 :phase phase :participants {:worlds #{a}}}))]
      ;; Guard-only cut checkpoint: withdrawal refuses every active cut, while
      ;; unsubscribe's pre-existing policy fences only quiescent (:p1q) cuts.
      (refused-unchanged! before {:t :withdraw-deref :w a :o observer} ::m/not-admitted)
      (let [action {:t :unsubscribe :w a :o observer}
            {expected :state refusal :refusal} (m/attempt before action)]
        (is (nil? refusal))
        (is (= [other-observer] (mapv :register-host (packets expected))))
        (doseq [cells? [false true]]
          (let [engine (kernel/restore before {:cells? cells?})]
            (kernel/step! engine action)
            (is (= (view expected) (view (kernel/snapshot engine))))))))))
