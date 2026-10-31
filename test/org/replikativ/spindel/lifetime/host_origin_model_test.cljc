(ns org.replikativ.spindel.lifetime.host-origin-model-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.engine.kernel :as kernel]
            [clojure.walk :as walk]))

(def a [:w 0])
(def b [:w 1])
(def c [:w 2])
(defn fork [from to] {:t :t19 :w from :v to :k [:cap to] :scope [:root from] :systems #{}})
(def park {:t :t05 :w a :r [:worker 1] :kind :await-once :debtor [:host :gate] :order 0})
(defn- view [s]
  (walk/postwalk
   (fn [x]
     (if (and (keyword? x) (#{"cancelled" "released"} (name x))
              (#{"org.replikativ.spindel.engine.kernel" "org.replikativ.spindel.lifetime.model"} (namespace x)))
       (keyword "error" (name x)) x))
   ;; :uses counts finite-search allocations in the reference explorer; the
   ;; kernel does not maintain this instrumentation. Every semantic field,
   ;; including the complete event sequence, remains compared.
   (dissoc s :uses)))
(defn checked [before action]
  (let [{after :state :keys [refusal observation]} (m/attempt before action)]
    (is (nil? refusal) (pr-str [action refusal]))
    (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
    (is (empty? (inv/edge-check {:before before :action action :after after
                                 :refusal refusal :observation observation})) (pr-str action))
    after))
(defn completion-order-witness [before action actual]
  ;; Observation map iteration is unspecified. Witness only the input order
  ;; for a completion, keeping every row; never edit the output event stream.
  (let [w (:w action)
        completion? (or (= :t08 (:t action))
                        (and (= :queued (:t action))
                             (:completion (first (:queue (m/wr before w))))))
        order (when completion?
                (vec (keep (fn [event]
                             (when (and (= :host-delivery (:event event)) (= w (:world event)))
                               (:o event))) (:events actual))))
        ranks (zipmap order (range))]
    (if (seq order)
      (update-in before [:worlds w :obligations]
                 #(into (sorted-map-by (fn [x y]
                                         (compare [(get ranks x (count ranks)) (pr-str x)]
                                                  [(get ranks y (count ranks)) (pr-str y)]))) %))
      before)))

(defn walk! [initial actions kernel?]
  (let [engines (when kernel? (mapv #(kernel/restore initial {:cells? %}) [false true]))]
    (reduce (fn [before action]
              (let [after (checked before action)]
                (doseq [engine engines]
                  (kernel/step! engine action)
                  (let [actual (kernel/snapshot engine)
                        witnessed (completion-order-witness before action actual)
                        {expected :state refusal :refusal} (m/attempt witnessed action)]
                    (is (nil? refusal) (pr-str [action refusal]))
                    (is (= (set (keys (get-in before [:worlds (:w action) :obligations])))
                           (set (keys (get-in witnessed [:worlds (:w action) :obligations])))))
                    (is (= (view expected) (view actual)) (pr-str action))))
                after)) initial actions)))
(defn foreign-origin-basis []
  (walk! (m/init-state {:slices? true})
         [(fork a b) {:t :t04 :w a :e :worker :mode :callback} park
          {:t :t04 :w b :e :worker :mode :callback :filter {:mode :causal-follow :origin b}}
          {:t :queued :w a}] true))
(defn host-rows [state world]
  (into {} (filter #(= :host (first (:creditor (val %))))) (:obligations (m/wr state world))))
(defn deliveries [state world]
  (filter #(and (= :host-delivery (:event %)) (= world (:world %))) (:events state)))
(def cut-actions
  [{:t :t20 :c :cut :scope [:root a]
    :participants {:worlds #{a} :components #{} :systems #{}}}
   {:t :t21 :c :cut} {:t :t22 :c :cut}
   {:t :t23 :c :cut :v c :k [:cap c]}])

(deftest sibling-copy-does-not-inherit-a-foreign-origin-host
  (doseq [cut? [false true]]
    (let [before (foreign-origin-basis)
          copied (walk! before (if cut? cut-actions [(fork a c)]) (not cut?))
          host (get-in before [:worlds a :obligations [:o 2]])]
      (is (= b (get-in host [:filter :origin])))
      (is (nil? (get-in copied [:worlds c :obligations [:o 2]])))
      (is (empty? (host-rows copied c)))
      ;; The worker's genuine external continuation is copied; the callback is
      ;; not. No source/callback execution authority is fabricated from its id.
      (is (= :inherited (:status (m/run copied c [:worker 1]))))
      (when-not cut?
        (let [after (walk! copied [{:t :t06 :w c :o [:o 1] :value 42}
                                   {:t :t07 :w c :r [:worker 1] :value 42}] true)]
          ;; No HOST root remains: real Rule L reclaims the completed copy
          ;; and its notification, so there is no subsequent queued action.
          (is (empty? (:queue (m/wr after c))))
          (is (empty? (host-rows after c)))
          (is (empty? (deliveries after c))))))))

(deftest direct-foreign-host-remains-valid-at-its-debtor
  (let [before (foreign-origin-basis)
        after (walk! before [{:t :t06 :w a :o [:o 1] :value 42}
                             {:t :t07 :w a :r [:worker 1] :value 42}
                             {:t :queued :w a}] true)]
    (is (= #{[:o 0] [:o 2]} (set (map :o (deliveries after a)))))
    (is (= #{42} (set (map :value (deliveries after a)))))))

(deftest origin-descendants-inherit-value-only-host-descriptors
  (doseq [cut? [false true] kind [:callback :deref]]
    (let [before (walk! (m/init-state)
                        [{:t :t04 :w a :e :worker :mode kind :filter {:mode :causal-follow}}
                         park] true)
          copied (walk! before (if cut? cut-actions [(fork a c)]) (not cut?))
          ob (get-in copied [:worlds c :obligations [:o 0]])]
      (is (= {:mode :causal-follow :origin a} (:filter ob)))
      (is (true? (:descriptor? ob)))
      (is (nil? (:cont ob)))
      (when-not cut?
        (let [after (walk! copied [{:t :t06 :w c :o [:o 1] :value 42}
                                   {:t :t07 :w c :r [:worker 1] :value 42}
                                   {:t :queued :w c}] true)]
          (is (= [[:o 0]] (mapv :o (deliveries after c)))))))))

(deftest registration-authenticates-origin-and-defaults-to-isolated
  (let [initial (m/init-state)]
    (doseq [filter [{:mode :causal-follow :origin b} {:mode :unknown} {:mode :local :origin nil} nil]]
      (let [action {:t :t04 :w a :e :worker :mode :callback :filter filter}
            {after :state refusal :refusal} (m/attempt initial action)]
        (is (= ::m/invalid-host-filter (:error refusal)))
        (is (= initial after))
        (doseq [cells? [false true]]
          (let [engine (kernel/restore initial {:cells? cells?})
                error (try (kernel/step! engine action) nil
                           (catch #?(:clj Exception :cljs :default) ex (ex-data ex)))]
            (is (= "invalid-host-filter" (some-> error :error name)))
            (is (= (view initial) (view (kernel/snapshot engine))))))))
    (doseq [filter [::absent {:mode :local} {:mode :local :origin a}]]
      (let [action (cond-> {:t :t04 :w a :e :worker :mode :callback}
                     (not= ::absent filter) (assoc :filter filter))
            before (walk! initial [action park] true)
            after (walk! before [(fork a c)] true)]
        (is (= {:mode :local :origin a} (get-in before [:worlds a :obligations [:o 0] :filter])))
        (is (empty? (host-rows after c)))))))

(deftest independent-origin-oracle-rejects-the-old-mode-only-copy
  (let [before (foreign-origin-basis)
        action (fork a c)
        after (checked before action)
        old-host (get-in before [:worlds a :obligations [:o 2]])
        illegal (-> old-host (assoc :origin :inherited :source-world a :descriptor? true
                                    :cont nil :debtor [:entity c :worker]))
        corrupted (assoc-in after [:worlds c :obligations [:o 2]] illegal)
        edge {:before before :action action :after corrupted}]
    (is (seq (inv/host-origin-errors corrupted)))
    (is (seq (inv/host-origin-edge-errors edge)))
    ;; A coherent wrong row plus a plausible causal delivery must fail the
    ;; independent edge proof as well as the state census.
    (let [delivered (assoc corrupted :events [{:event :host-delivery :world c :e :worker
                                               :o [:o 2] :value 42 :causal? true}])]
      (is (seq (inv/host-origin-edge-errors {:before corrupted :action {:t :t08 :w c :e :worker}
                                             :after delivered}))))
    ;; Rewriting the origin to the source would pass a mode-only selection
    ;; test, but cannot alter the actual registration's captured origin.
    (is (seq (inv/host-origin-edge-errors
              (assoc edge :after (assoc-in corrupted [:worlds c :obligations [:o 2] :filter :origin] a)))))
    (let [released-origin (assoc-in corrupted [:worlds b] {:id b :status :released :lineage (:lineage (m/wr corrupted b))})]
      (is (seq (inv/host-origin-errors released-origin))))))

(deftest released-origin-keeps-immutable-descendant-proof
  (let [before (walk! (m/init-state)
                      [{:t :t04 :w a :e :worker :mode :callback :filter {:mode :causal-follow}}
                       park (fork a c)] true)
        released (checked before {:t :t34 :w a})]
    (is (= :released (:status (m/wr released a))))
    (is (= (get-in before [:lineages a]) (get-in released [:lineages a])))
    (is (true? (boolean (inv/host-origin-ancestor? released a c))))
    (is (empty? (inv/host-origin-errors released)))
    (is (= a (get-in released [:worlds c :obligations [:o 0] :filter :origin])))))

(deftest copy-oracle-does-not-trust-after-entity-selection
  (doseq [cut? [false true]]
    (let [before (walk! (m/init-state)
                        [{:t :t04 :w a :e :worker :mode :callback :filter {:mode :causal-follow}}
                         park] true)
          actions (if cut? cut-actions [(fork a c)])
          basis (walk! before (vec (butlast actions)) (not cut?))
          action (last actions)
          after (checked basis action)
          missing (-> after
                      (update-in [:worlds c :obligations] dissoc [:o 0])
                      (update-in [:worlds c :entities] dissoc :worker))]
      (is (seq (inv/host-origin-edge-errors {:before basis :action action :after missing})))))
  (let [before (walk! (m/init-state)
                      [{:t :t04 :w a :e :worker :mode :callback :filter {:mode :causal-follow}}
                       park
                       {:t :t04 :w a :e :unselected :mode :callback :filter {:mode :causal-follow}}] true)
        action (fork a c)
        after (checked before action)
        forged (-> after
                   (assoc-in [:worlds c :entities :unselected]
                             (get-in before [:worlds a :entities :unselected]))
                   (assoc-in [:worlds c :obligations [:o 2]]
                             (assoc (get-in before [:worlds a :obligations [:o 2]])
                                    :origin :inherited :source-world a :descriptor? true
                                    :cont nil :debtor [:entity c :unselected])))]
    (is (seq (inv/host-origin-edge-errors {:before before :action action :after forged})))))

(deftest registration-oracle-uses-the-actual-attributed-slice
  (let [before (walk! (m/init-state {:slices? true})
                      [(fork a b)
                       {:t :t04 :w a :e :actor :mode :callback}
                       {:t :slice-enter :w a :r [:actor 1] :th :actor-thread}] true)
        action {:t :t04 :w b :th :actor-thread :e :target :mode :callback
                :filter {:mode :causal-follow}}
        after (walk! before [action] true)
        ob (get-in after [:worlds a :obligations [:o 1]])]
    (is (= a (get-in ob [:filter :origin])))
    (is (nil? (m/ent after b :target)))
    (is (empty? (inv/host-origin-edge-errors {:before before :action action :after after})))
    (let [wrong (assoc-in after [:worlds a :obligations [:o 1] :filter :origin] b)]
      (is (seq (inv/host-origin-edge-errors {:before before :action action :after wrong}))))
    (let [bad (assoc action :filter {:mode :causal-follow :origin b})
          {state :state refusal :refusal} (m/attempt before bad)]
      (is (= ::m/invalid-host-filter (:error refusal)))
      (is (= before state)))))

(deftest incomplete-order-witness-cannot-hide-a-host-delivery
  (let [before (walk! (foreign-origin-basis)
                      [{:t :t06 :w a :o [:o 1] :value 42}
                       {:t :t07 :w a :r [:worker 1] :value 42}] true)
        action {:t :queued :w a}
        ;; A fake actual output omits the direct foreign registration. It can
        ;; order the first row but cannot delete the second input observation.
        fake {:events [{:event :host-delivery :world a :o [:o 0] :value 42}]}
        witnessed (completion-order-witness before action fake)
        expected (checked witnessed action)]
    (is (= (get-in before [:worlds a :obligations])
           (get-in witnessed [:worlds a :obligations])))
    (is (= #{[:o 0] [:o 2]} (set (map :o (deliveries expected a)))))
    (is (not= (:events fake) (:events expected)))))

(deftest nested-copy-oracle-uses-the-before-basis
  (doseq [cut? [false true]]
    (let [before (walk! (m/init-state)
                        [(fork a b)
                         {:t :t04 :w a :e :worker :mode :callback :filter {:mode :causal-follow}}
                         park] true)
          prepared (if cut? (walk! before (vec (butlast cut-actions)) false) before)
          inner (if cut? (last cut-actions) (fork a c))
          ;; A coordinator's admitted immutable action envelope. T19 uses
          ;; its open source A; T23 uses open B while A's basis is fenced.
          ;; Generic queued :action is not a supported kernel control path.
          dispatcher (if cut? b a)
          queued (m/enqueue prepared dispatcher {:action inner})
          action {:t :queued :w dispatcher}
          after (walk! queued [action] false)
          omitted (-> after
                      (update-in [:worlds c :obligations] dissoc [:o 0])
                      (update-in [:worlds c :entities] dissoc :worker))]
      (is (true? (get-in after [:worlds c :obligations [:o 0] :descriptor?])))
      (is (empty? (inv/host-origin-edge-errors {:before queued :action action :after after})))
      (is (seq (inv/host-origin-edge-errors {:before queued :action action :after omitted}))))))

(deftest queued-host-install-conserves-registration-origin-and-row
  (let [before (walk! (m/init-state {:slices? true})
                      [(fork a b)
                       {:t :t04 :w a :e :worker :mode :callback}
                       park
                       {:t :t04 :w b :e :worker :mode :callback
                        :filter {:mode :causal-follow :origin b}}] true)
        packet (first (:queue (m/wr before a)))
        action {:t :queued :w a}
        after (walk! before [action] true)
        rewritten (assoc-in after [:worlds a :obligations [:o 2] :filter :origin] a)]
    (is (= b (:caller-world packet)))
    (is (= (:ob packet) (get-in after [:worlds a :obligations [:o 2]])))
    (is (empty? (inv/host-origin-edge-errors {:before before :action action :after after})))
    ;; The placement world and forged origin are both known. A state-only
    ;; lineage check cannot authenticate a direct registration's old origin.
    (is (empty? (inv/host-origin-errors rewritten)))
    (is (seq (inv/host-origin-edge-errors {:before before :action action :after rewritten})))
    (is (seq (inv/host-origin-edge-errors
              {:before before :action action
               :after (assoc-in after [:worlds a :obligations [:o 2] :standing?] false)})))
    (let [replaced (update-in after [:worlds a :queue] conj
                              (assoc-in packet [:ob :filter :origin] a))]
      (is (seq (inv/host-origin-edge-errors {:before before :action action :after replaced}))))))

(deftest queued-composition-conserves-exact-storage-and-footprint
  (doseq [cut? [false true]]
    (let [base (walk! (m/init-state)
                      [(fork a b)
                       {:t :t04 :w a :e :worker :mode :callback :filter {:mode :causal-follow}}
                       park] true)
          prepared (if cut? (walk! base (vec (butlast cut-actions)) false) base)
          dispatcher (if cut? b a)
          inner (if cut? (last cut-actions) (fork a c))
          before (-> prepared
                     (m/enqueue dispatcher {:action inner})
                     (m/enqueue dispatcher {:completion :tail-one :debtor-world dispatcher :value 1})
                     (m/enqueue dispatcher {:completion :tail-two :debtor-world dispatcher :value 2}))
          action {:t :queued :w dispatcher}
          after (checked before action)
          front (first (:queue (m/wr before dispatcher)))
          corruptions
          [[:old-sequence-head (update-in after [:worlds dispatcher :queue] #(into [front] %))]
           [:alter-tail (assoc-in after [:worlds dispatcher :queue 0 :value] :forged)]
           [:drop-tail (update-in after [:worlds dispatcher :queue] #(vec (rest %)))]
           [:reorder-tail (update-in after [:worlds dispatcher :queue] #(vec (reverse %)))]
           [:source-entity (assoc-in after [:worlds a :entities :worker :order] :forged)]
           [:cut-metadata (assoc-in after [:cuts :forged] {:phase :captured})]
           [:cap-metadata (assoc-in after [:caps [:cap c] :published?] :forged)]
           [:known-world (update after :known-worlds conj [:w :forged])]
           [:clock (update-in after [:clocks dispatcher] (fnil inc 0))]
           [:outside (update-in after [:env :outside] conj {:w dispatcher :event {:forged true}})]
           [:extra-diagnostic (update after :events conj {:event :forged})]]]
      (is (= 2 (count (:queue (m/wr after dispatcher)))) (pr-str cut?))
      (is (empty? (inv/queued-action-composition-errors {:before before :action action :after after})))
      (doseq [[label bad] corruptions]
        ;; Assert the compound checker itself rejects the edit, independently
        ;; of whether a whole-state census also happens to find it invalid.
        (is (seq (inv/queued-action-composition-errors {:before before :action action :after bad}))
            (pr-str [cut? label]))))))

(deftest queued-composition-preserves-inner-diagnostic-prefix
  (let [before (m/enqueue (m/init-state) a
                          {:action {:t :t04 :w a :e :diagnostic-source :mode :callback}})
        action {:t :queued :w a}
        after (checked before action)
        events (:events after)]
    (is (seq events))
    (doseq [bad [(assoc after :events [])
                 (assoc after :events (into [(first events)] events))
                 (assoc-in after [:events 0 :event] :forged)]]
      (is (seq (inv/queued-action-composition-errors {:before before :action action :after bad}))))))

(deftest finite-nested-queue-controls-consume-each-wrapper-once
  (let [leaf {:t :t04 :w a :e :nested-source :mode :callback :filter {:mode :causal-follow}}
        before (-> (m/init-state)
                   (m/enqueue a {:action {:t :queued :w a}})
                   (m/enqueue a {:action leaf}))
        action {:t :queued :w a}
        expected-context (assoc-in before [:worlds a :queue] [])
        context (inv/custody-effective-context before action)
        after (checked before action)]
    ;; The context helper consumes both genuine queued action envelopes, but
    ;; does not execute T04 or invent its entity/Run while finding the leaf.
    (is (= {:before expected-context :action leaf} context))
    (is (= leaf (inv/custody-effective-delivery before action)))
    (is (nil? (m/ent (:before context) a :nested-source)))
    (is (m/ent after a :nested-source))
    (is (empty? (:queue (m/wr after a))))
    (is (empty? (inv/queued-action-composition-errors {:before before :action action :after after})))
    (is (= [{:mode :causal-follow :origin a}]
           (mapv :filter (vals (host-rows after a)))))))

(deftest nested-host-registration-inspects-the-leaf-front
  (let [base (walk! (m/init-state)
                    [(fork a b)
                     {:t :t04 :w a :e :worker :mode :callback} park] true)
        ;; Genuine enqueues allocate increasing envelope clocks before the
        ;; foreign T04 appends its real register-host packet behind them.
        queued (-> base
                   (m/enqueue a {:action {:t :queued :w a}})
                   (m/enqueue a {:action {:t :queued :w a}}))
        before (walk! queued [{:t :t04 :w b :e :worker :mode :callback
                               :filter {:mode :causal-follow :origin b}}] true)
        packet (last (:queue (m/wr before a)))
        action {:t :queued :w a}
        context (inv/custody-effective-context before action)
        after (checked before action)
        wrong (assoc-in after [:worlds a :obligations [:o 2] :filter :origin] a)]
    (is (= packet (first (get-in context [:before :worlds a :queue]))))
    (is (= (assoc-in before [:worlds a :queue] [packet]) (:before context)))
    (is (= action (:action context)))
    (is (= (:ob packet) (get-in after [:worlds a :obligations [:o 2]])))
    (is (empty? (inv/host-origin-edge-errors {:before before :action action :after after})))
    (is (seq (inv/host-origin-edge-errors {:before before :action action :after wrong})))))

(deftest nested-adoption-proves-the-original-physical-frame
  (let [r [:adoptable 1] ticket (cleanup/ticket a r)
        base (walk! (m/init-state {:slices? true :cps-exit? true})
                    [{:t :t04 :w a :e :adoptable :mode :callback}
                     {:t :slice-enter :w a :r r :th :worker}
                     {:t :t02 :w a :scope r :e :retained :kind :atom :value :original}
                     {:t :t11 :w a :r r}] false)
        before (-> base
                   (m/enqueue a {:action {:t :queued :w a}})
                   (m/enqueue a {:action {:t :cleanup-adopt :n ticket :th :worker}}))
        action {:t :queued :w a}
        after (checked before action)
        corrupt (-> after
                    (assoc-in [:env :threads :foreign] (get-in after [:env :threads :worker]))
                    (update-in [:env :threads] dissoc :worker))]
    (is (empty? (cleanup/errors corrupt)))
    (is (some #(= :TL21 (:id %))
              (inv/original-resource-edge-check {:before before :action action :after corrupt})))
    (is (some #(= :TL21 (:id %))
              (inv/queued-action-composition-errors {:before before :action action :after corrupt})))
    (is (some #(= :TL21 (:id %))
              (inv/edge-check {:before before :action action :after corrupt})))))
