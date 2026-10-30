(ns org.replikativ.spindel.engine.public-cancellation-model-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [clojure.walk :as walk]
            [org.replikativ.spindel.engine.kernel :as kernel]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.model :as m]))

(def w [:w 0])
(def v [:w 1])
(def r [:target 1])
(def reason {:diagnostic-error :first})
(def later-reason {:diagnostic-error :second})
(def construct {:t :t01 :w w :e :target :tok :handle})
(def invoke {:t :t04 :w w :e :target :tok :handle :mode :callback})
(def cancel {:t :cancel-computation :w w :e :target :tok :handle :value reason})

(defn- view [state]
  (walk/postwalk
   (fn [x]
     (if (and (keyword? x) (#{"cancelled" "released"} (name x))
              (#{"org.replikativ.spindel.engine.kernel"
                 "org.replikativ.spindel.lifetime.model"} (namespace x)))
       (keyword "error" (name x)) x))
   (select-keys state [:worlds :env :serial :events :generation-clock :clocks
                       :host-delivered :registry :caps :durable :known-worlds
                       :lineages :cuts :records])))

(defn- checked-walk! [initial actions]
  (let [kernels (mapv #(kernel/restore initial {:cells? %}) [false true])]
    (vec
     (reductions
      (fn [before action]
        (let [{after :state :keys [refusal observation]} (m/attempt before action)]
          (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
          (is (empty? (inv/edge-check {:before before :action action :after after
                                       :refusal refusal :observation observation})) (pr-str action))
          (doseq [actual kernels]
            (let [error (try (kernel/step! actual action) nil
                             (catch #?(:clj Exception :cljs :default) ex (ex-data ex)))]
              (is (= (some-> refusal :error name) (some-> error :error name))
                  (pr-str [action refusal error]))
              (is (= (view after) (view (kernel/snapshot actual))) (pr-str action))))
          after)) initial actions))))

(defn- deliveries [state]
  (filter #(= :host-delivery (:event %)) (:events state)))

(deftest pre-entry-cancellation-has-an-explicit-nil-generation-fence
  (let [states (checked-walk! (m/init-state)
                              [construct cancel (assoc cancel :value later-reason) invoke
                               {:t :invalidate-computation :w w :e :target}
                               invoke {:t :t07 :w w :r r :value :fresh}])
        first-cancel (nth states 2) repeated (nth states 3)
        cached-invoke (nth states 4) fresh (peek states)]
    (is (= {:run nil :result reason} (:cancelled-completion (m/ent first-cancel w :target))))
    (is (= reason (:result (m/ent first-cancel w :target))))
    (is (true? (:completed? (m/ent first-cancel w :target))))
    (is (false? (:dirty? (m/ent first-cancel w :target))))
    (is (empty? (:runs (m/wr first-cancel w))))
    (is (= (dissoc first-cancel :events) (dissoc repeated :events)))
    (is (nil? (m/current cached-invoke w :target)))
    ;; Cached T04 diagnostics identify the entity; the committed host command
    ;; captures its cached payload, rather than duplicating it in this event.
    (is (= [:target] (mapv :e (deliveries cached-invoke))))
    (is (= reason (:result (m/ent cached-invoke w :target))))
    (doseq [cells? [false true]]
      (let [actual (kernel/restore first-cancel {:cells? cells?})
            commands (:commands (kernel/step! actual invoke))]
        (is (= [reason] (mapv :value (filter #(= :host (:op %)) commands))))))
    (is (= :fresh (:result (m/ent fresh w :target))))
    (is (not (contains? (m/ent fresh w :target) :cancelled-completion)))))

(deftest cancelling-a-completed-cache-discards-old-publication-but-not-served-delivery
  (doseq [serve-first? [false true]]
    (let [actions (cond-> [construct invoke {:t :t07 :w w :r r :value :old}]
                    serve-first? (conj {:t :t08 :w w :e :target :value :old}))
          states (checked-walk! (m/init-state)
                                (into actions [cancel {:t :t08 :w w :e :target :value :old}]))
          before (nth states (count actions))
          cancelled (nth states (inc (count actions)))
          final (peek states)]
      (when serve-first? (is (= [:old] (mapv :value (deliveries before)))))
      (is (= reason (:result (m/ent cancelled w :target))))
      (is (empty? (:queue (m/wr cancelled w))))
      (is (= (if serve-first? [] [reason]) (mapv :value (deliveries cancelled))))
      (is (empty? (deliveries final)))
      (is (= reason (:result (m/ent final w :target)))))))

(deftest parked-parents-and-hosts-receive-the-exact-explicit-reason
  (let [states (checked-walk!
                (m/init-state)
                [construct invoke
                 {:t :t04 :w w :e :parent :mode :callback}
                 {:t :t05 :w w :r [:parent 1] :kind :await-reactive :debtor [:entity w :target]}
                 {:t :t05 :w w :r r :kind :await-once :debtor [:host :gate]}
                 cancel {:t :t07 :w w :r r :value :late}
                 {:t :t07 :w w :r [:parent 1] :value :caught}])
        cancelled (nth states 6) late (nth states 7) parent-completed (peek states)]
    (is (= [reason] (mapv :value (deliveries cancelled))))
    (is (= [reason] (mapv :value (filter #(= :resume (:event %)) (:events cancelled)))))
    (is (= :running (:status (m/run cancelled w [:parent 1]))))
    (is (= (dissoc cancelled :events) (dissoc late :events)))
    (is (= :caught (:result (m/ent parent-completed w :parent))))
    (is (not (contains? (m/ent parent-completed w :parent) :cancelled-completion)))))

(deftest cancellation-shaped-body-errors-do-not-create-explicit-cancel-authority
  (let [shaped {:type :spin-cancelled :error :cancelled}
        states (checked-walk! (m/init-state)
                              [construct invoke {:t :t07 :w w :r r :value shaped}])
        after (peek states)]
    (is (= shaped (:result (m/ent after w :target))))
    (is (not (contains? (m/ent after w :target) :cancelled-completion)))
    (is (empty? (get-in after [:env :native])))))

(deftest consumed-reactive-parents-lose-validation-without-an-explicit-fence
  (let [states (checked-walk!
                (m/init-state)
                [construct {:t :t02 :w w :e :source :value 0} invoke
                 {:t :t05 :w w :r r :kind :track :debtor [:entity w :source]}
                 {:t :t04 :w w :e :parent :mode :callback}
                 {:t :t05 :w w :r [:parent 1] :kind :await-reactive :debtor [:entity w :target]}
                 {:t :unsubscribe :w w :o [:o 0]}
                 {:t :t07 :w w :r r :value :child}
                 {:t :t08 :w w :e :target :value :child}
                 {:t :t07 :w w :r [:parent 1] :value :parent}
                 cancel])
        after (peek states)]
    (is (true? (:dirty? (m/ent after w :parent))))
    (is (not (contains? (m/ent after w :parent) :cancelled-completion)))
    (is (not-any? #(and (= :body-entry (:event %)) (= :parent (:e %))) (:events after)))))

(deftest repeated-cancel-preserves-protected-wait-and-a-fresh-generation-wins
  (let [n (cleanup/ticket w r)
        actions [construct invoke {:t :slice-enter :w w :r r :th :worker}
                 {:t :t02 :w w :scope r :e :cell :kind :atom :value 42}
                 {:t :t05 :w w :r r :kind :await-once :debtor [:host :gate]}
                 {:t :t38 :th :worker} cancel
                 {:t :cleanup-claim :n n :th :cleaner}
                 {:t :cleanup-park :th :cleaner} {:t :t38 :th :cleaner}
                 (assoc cancel :value later-reason)
                 {:t :invalidate-computation :w w :e :target}
                 invoke {:t :t07 :w w :r [:target 2] :value :fresh}
                 {:t :cleanup-deliver :n n :sequence 1 :value :io}
                 {:t :cleanup-claim :n n :th :cleaner}
                 {:t :cleanup-return :th :cleaner} {:t :t38 :th :cleaner}
                 {:t :t07 :w w :r r :value :late}]
        states (checked-walk! (m/init-state {:slices? true :cps-exit? true}) actions)
        waiting (nth states 10) repeated (nth states 11) fresh (nth states 14) final (peek states)]
    (is (= reason (get-in waiting [:env :native n :cancel-value])))
    (is (= :waiting (get-in waiting [:env :native n :phase])))
    (is (= (get-in waiting [:env :native]) (get-in repeated [:env :native])))
    (is (= (get-in waiting [:env :cleanup-cells]) (get-in repeated [:env :cleanup-cells])))
    (is (= reason (:result (m/ent repeated w :target))))
    (is (= :fresh (:result (m/ent fresh w :target))))
    (is (not (contains? (m/ent fresh w :target) :cancelled-completion)))
    (is (= :fresh (:result (m/ent final w :target))))
    (is (empty? (get-in final [:env :cleanup-cells])))
    (is (nil? (get-in final [:env :native n])))))

(deftest dirty-cancellation-can-enter-fresh-and-world-copies-stay-independent
  (let [states (checked-walk!
                (m/init-state)
                [construct invoke {:t :invalidate-computation :w w :e :target}
                 cancel invoke {:t :t07 :w w :r [:target 2] :value :fresh}])
        cancelled (nth states 4) fresh (peek states)]
    (is (true? (:dirty? (m/ent cancelled w :target))))
    (is (= reason (:result (m/ent cancelled w :target))))
    (is (= :fresh (:result (m/ent fresh w :target)))))
  (let [states (checked-walk!
                (m/init-state)
                [construct (assoc invoke :filter {:mode :causal-follow :origin w})
                 {:t :t05 :w w :r r :kind :await-once :debtor [:host :gate]}
                 {:t :t19 :w w :v v :k :fork :scope [:root w] :systems #{}}
                 (assoc cancel :w v)])
        before (nth states 4) after (peek states)]
    (is (= (m/ent before w :target) (m/ent after w :target)))
    (is (not (contains? (m/ent after w :target) :cancelled-completion)))
    (is (= reason (:result (m/ent after v :target))))
    (is (= {:run r :result reason} (:cancelled-completion (m/ent after v :target))))))

(deftest admission-is-checked-before-an-idempotent-cancel-can-touch-authority
  (let [before (last (checked-walk! (m/init-state) [construct cancel]))
        fenced (m/step before {:t :t20 :c :cut :scope [:root w]
                               :participants {:worlds #{w} :systems #{}}})
        invalid-token (assoc cancel :tok :unknown)]
    (doseq [[state action error] [[before invalid-token ::m/unknown-handle]
                                  [fenced cancel ::m/not-admitted]]]
      (is (= error (get-in (m/attempt state action) [:refusal :error])))
      (is (= state (last (checked-walk! state [action])))))))

(deftest prior-completed-bases-cannot-regain-publication-after-public-cancel
  (let [states (checked-walk!
                (m/init-state)
                [construct {:t :t02 :w w :e :source :value 0} invoke
                 {:t :t05 :w w :r r :kind :track :debtor [:entity w :source]}
                 {:t :t07 :w w :r r :value :old}
                 {:t :t09 :w w :e :target :cause :dirty :order -1}
                 cancel {:t :t07 :w w :r r :value :late-basis}
                 {:t :t07 :w w :r [:target 2] :value :late-current} invoke])
        before (nth states 6) cancelled (nth states 7) final (peek states)]
    (is (= :completed (:status (m/run before w r))))
    (is (= {:run [:target 2] :result reason}
           (:cancelled-completion (m/ent cancelled w :target))))
    (is (empty? (:runs (m/wr cancelled w))))
    (is (= reason (:result (m/ent final w :target))))
    (is (nil? (m/current final w :target)))))

(deftest cancellation-is-visible-before-the-active-slice-physically-returns
  (let [n (cleanup/ticket w r)
        states (checked-walk!
                (m/init-state {:slices? true :cps-exit? true})
                [construct invoke {:t :slice-enter :w w :r r :th :worker}
                 cancel {:t :t07 :w w :r r :value :late-success}
                 {:t :t38 :th :worker}
                 {:t :cleanup-claim :n n :th :cleaner}
                 {:t :cleanup-return :th :cleaner} {:t :t38 :th :cleaner}])
        cancelled (nth states 4) late (nth states 5) final (peek states)]
    (is (= reason (:result (m/ent cancelled w :target))))
    (is (= :unwinding (:status (m/run cancelled w r))))
    (is (false? (m/join-ready? cancelled w r)))
    (is (= (dissoc cancelled :events) (dissoc late :events)))
    (is (m/join-ready? final w r))
    (is (= reason (:result (m/ent final w :target))))))
