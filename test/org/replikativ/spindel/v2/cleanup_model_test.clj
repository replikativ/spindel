(ns org.replikativ.spindel.v2.cleanup-model-test
  "Finite contract exploration; not the external formal model or CPS proof.
   Two waits in an inner finalizer, one outer finalizer, and one resource ack."
  (:require [clojure.test :refer [deftest is]]))

(defn- initial []
  {:phase :body :remaining 2 :regions [:outer :inner] :active nil :wait nil
   :canceled? false :result nil :resource? true :sequence 0 :exits []})

(defn- step [s event]
  (case event
    :return (when (= :body (:phase s)) (assoc s :phase :cleanup :active :inner))
    :cancel (when (and (not (:canceled? s)) (not= :done (:phase s)))
              (cond-> (assoc s :canceled? true :result :cancelled)
                (= :body (:phase s)) (assoc :phase :cleanup :active :inner)))
    :wait (when (and (= :cleanup (:phase s)) (pos? (:remaining s)))
            (-> s (assoc :phase :waiting
                         :wait {:registered? false :outcome nil :controller :local})
                (update :sequence inc)))
    :registered (when (and (:wait s) (not (get-in s [:wait :registered?])))
                  (assoc-in s [:wait :registered?] true))
    :complete (when (and (:wait s) (nil? (get-in s [:wait :outcome])))
                (assoc-in s [:wait :outcome] :ok))
    :resume (when (and (get-in s [:wait :registered?]) (get-in s [:wait :outcome]))
              (-> s (assoc :phase :cleanup :wait nil) (update :remaining dec)))
    :inner-exit (when (and (= :cleanup (:phase s)) (zero? (:remaining s)))
                  (-> s (assoc :phase :outer :active :outer :regions [:outer])
                      (update :exits conj :inner)))
    :outer-exit (when (= :outer (:phase s))
                  (-> s (assoc :phase :done :active nil :regions []
                               :result (if (:canceled? s) :cancelled :ok))
                      (update :exits conj :outer)))
    :ack (when (:resource? s) (assoc s :resource? false))))

(def ^:private events [:return :cancel :wait :registered :complete :resume :inner-exit :outer-exit :ack])

(defn- successors [s] (set (keep #(step s %) events)))

(defn- reachable []
  (loop [seen #{(initial)} todo [(initial)]]
    (if-let [s (peek todo)]
      (let [fresh (remove seen (successors s))]
        (recur (into seen fresh) (into (pop todo) fresh)))
      seen)))

(defn- retirable? [s]
  (and (= :done (:phase s)) (empty? (:regions s)) (nil? (:active s))
       (nil? (:wait s)) (not (:resource? s))))

(defn- inherited [s]
  (when (:wait s)
    (assoc s :wait {:registered? true :outcome :forked :controller nil})))

(deftest bounded-interleavings-conserve-cleanup-obligations
  (let [states (reachable)]
    (is (> (count states) 50))
    (doseq [s states]
      (is (<= (count (:regions s)) 2))
      (is (= (count (:exits s)) (count (distinct (:exits s)))))
      (when (:wait s)
        (is (= :inner (:active s)))
        (is (not (retirable? s)))
        (when-let [canceled (step s :cancel)]
          (is (= (:wait s) (:wait canceled))))
        (let [child (inherited s) grandchild (inherited child)]
          (is (= :forked (get-in child [:wait :outcome])))
          (is (nil? (get-in child [:wait :controller])))
          (is (= (:wait child) (:wait grandchild)))
          (is (= :local (get-in s [:wait :controller])))))
      (when (:canceled? s) (is (= :cancelled (:result s))))
      (when (empty? (successors s))
        (is (retirable? s))
        (is (= [:inner :outer] (:exits s)))))))

;; Z#67 finite transition exploration. This deliberately models host preparation,
;; physical acknowledgement and error entitlement rather than reusing runtime
;; implementation functions. It is bounded testing, not an external proof.
(defn- close-initial []
  {:requested? false :run? true :resource? true :preparation :pending
   :child :absent :child-run? false :child-host? false :child-ingress? false
   :execution? false :terminal? false :host? true :recovery :none
   :child-error? true :cached-error? false :route nil :delivered? false
   :report-events 0 :reported? false})

(defn- close-step [s event]
  (case event
    :request (when-not (:requested? s) (assoc s :requested? true))
    :publish (when (= :pending (:preparation s))
               (assoc s :preparation :published :child :open :child-run? true :child-host? true))
    :dispose-preparation (when (= :pending (:preparation s)) (assoc s :preparation :disposed))
    :child-request (when (and (:requested? s) (= :open (:child s))) (assoc s :child :requested))
    :child-retire (when (and (= :requested (:child s)) (:child-run? s)) (assoc s :child-run? false))
    :resource-ack (when (:resource? s) (assoc s :resource? false))
    :claim-lexical (when (and (:requested? s) (not= :absent (:child s))
                              (not (:child-ingress? s)) (nil? (:route s)))
                     (assoc s :route :lexical))
    :consume-child-report (when (and (:child-error? s) (not= :terminal (:child s)))
                            (assoc s :child-error? false))
    :child-ack (when (and (= :requested (:child s)) (not (:child-run? s)) (:child-host? s))
                 (assoc s :child-host? false))
    :child-terminal (when (and (= :requested (:child s)) (not (:child-run? s)) (not (:child-host? s)))
                      (assoc s :child :terminal :cached-error? (:child-error? s) :child-error? false))
    :child-ingress (when (and (= :terminal (:child s)) (not (:child-ingress? s)))
                     (cond-> (assoc s :child-ingress? true)
                       (nil? (:route s)) (assoc :route :automatic)
                       (and (not= :lexical (:route s)) (:cached-error? s))
                       (-> (update :report-events inc) (assoc :reported? true))))
    :lexical-catch (when (and (= :lexical (:route s)) (= :terminal (:child s)) (not (:delivered? s)))
                     (assoc s :delivered? true))
    :lexical-abandon (when (and (= :lexical (:route s)) (= :terminal (:child s)) (not (:delivered? s)))
                       (cond-> (assoc s :delivered? true)
                         (:cached-error? s) (-> (update :report-events inc) (assoc :reported? true))))
    :run-exit (when (and (:requested? s) (:run? s) (not= :pending (:preparation s))
                         (or (= :absent (:child s)) (= :terminal (:child s)))
                         (or (not= :lexical (:route s)) (:delivered? s)))
                (assoc s :run? false))
    :execution-retired (when (and (:requested? s) (not (:execution? s)) (not (:run? s))
                                  (not (:resource? s)) (not= :pending (:preparation s))
                                  (not (:child-run? s)))
                         (assoc s :execution? true))
    :recovery (when (and (:host? s) (= :none (:recovery s))) (assoc s :recovery :ambiguous))
    :reconcile (when (= :ambiguous (:recovery s)) (assoc s :recovery :known))
    :host-ack (when (and (:execution? s) (:host? s) (not= :ambiguous (:recovery s))) (assoc s :host? false))
    :terminal (when (and (:execution? s) (not (:terminal? s)) (not (:host? s))
                         (or (= :absent (:child s)) (:child-ingress? s)))
                (assoc s :terminal? true))))

(def ^:private close-events
  [:request :publish :dispose-preparation :child-request :child-retire :resource-ack
   :claim-lexical :consume-child-report :child-ack :child-terminal :child-ingress
   :lexical-catch :lexical-abandon :run-exit :execution-retired :recovery :reconcile :host-ack :terminal])

(deftest staged-close-finite-conservation-and-conditional-progress
  (let [successors (fn [s] (set (keep #(close-step s %) close-events)))
        states (loop [seen #{(close-initial)} todo [(close-initial)]]
                 (if-let [s (peek todo)]
                   (let [fresh (remove seen (successors s))]
                     (recur (into seen fresh) (into (pop todo) fresh))) seen))]
    (is (> (count states) 400))
    (doseq [s states]
      (is (<= (:report-events s) 1) "one newly unreported entitlement, regardless of route/consumption order")
      (when (:execution? s)
        (is (:requested? s))
        (is (not-any? s [:run? :resource? :child-run?]))
        (is (not= :pending (:preparation s))))
      (when (:terminal? s)
        (is (:execution? s))
        (is (not (:host? s)))
        (is (or (= :absent (:child s)) (:child-ingress? s))))
      (doseq [next (successors s)]
        (when (:execution? s) (is (:execution? next)))
        (when (:terminal? s) (is (:terminal? next))))
      (when (empty? (successors s))
        (is (:terminal? s) "under the model's finite fair/physical-ack assumptions no nonterminal sink exists")))
    ;; The declared dependency order admits C ack without P execution retirement.
    (is (some #(and (not (:execution? %)) (= :requested (:child %))
                    (not (:child-run? %)) (:child-host? %) (close-step % :child-ack)) states))))

(defn- activation-step [s event]
  (letfn [(complete [s outcome]
            (cond-> s
              (= :pending (:ordinary s))
              (-> (assoc :ordinary outcome) (update :completions inc))))]
    (case event
      :submit (when-not (:intent? s) (assoc s :intent? true))
      :ordinary (when (and (:intent? s) (= :none (:ordinary s)))
                  (case (:child s)
                    :born (assoc s :ordinary :accepted :completions 1)
                    :released (assoc s :ordinary :released :completions 1)
                    (assoc s :ordinary :pending)))
      :withdraw (when (= :pending (:ordinary s)) (assoc s :ordinary :withdrawn))
      :claim (when (and (:intent? s) (not (:claim? s))) (assoc s :claim? true))
      :parent-request (when (= :open (:parent s)) (assoc s :parent :requested))
      :admit (when (and (:claim? s) (nil? (:decision s)) (= :open (:parent s)) (= :unborn (:child s)))
               (assoc s :decision :accepted :execution-debt? true :terminal-debt? true))
      :reject (when (and (:claim? s) (nil? (:decision s))
                         (or (= :requested (:parent s)) (= :released (:child s))))
                (complete (assoc s :decision :rejected :child :released) :released))
      :birth (when (and (= :accepted (:decision s)) (= :unborn (:child s)))
               (if (= :requested (:parent s))
                 (complete (assoc s :child :released) :released)
                 (complete (assoc s :child :born :body 1) :accepted)))
      :child-release (when-not (= :released (:child s))
                       (complete (assoc s :child :released) :released))
      :execution-ack (when (and (:execution-debt? s) (= :released (:child s)))
                       (assoc s :execution-debt? false))
      :native-ack (when (and (:native? s) (= :released (:child s))) (assoc s :native? false))
      :terminal-ack (when (and (:terminal-debt? s) (= :released (:child s)) (not (:native? s)))
                      (assoc s :execution-debt? false :terminal-debt? false))
      :parent-retired (when (and (= :requested (:parent s)) (not (:retired? s)) (not (:execution-debt? s)))
                        (assoc s :retired? true))
      :parent-terminal (when (and (:retired? s) (not (:terminal? s)) (not (:terminal-debt? s)))
                         (assoc s :terminal? true)))))

(deftest activation-handoff-finite-no-unowned-execution-or-late-admission
  (let [initial {:intent? false :claim? false :ordinary :none :completions 0
                 :parent :open :child :unborn :decision nil :body 0 :native? true
                 :execution-debt? false :terminal-debt? false :retired? false :terminal? false}
        events [:submit :ordinary :withdraw :claim :parent-request :admit :reject :birth
                :child-release :execution-ack :native-ack :terminal-ack :parent-retired :parent-terminal]
        successors (fn [s] (set (keep #(activation-step s %) events)))
        states (loop [seen #{initial} todo [initial]]
                 (if-let [s (peek todo)]
                   (let [fresh (remove seen (successors s))]
                     (recur (into seen fresh) (into (pop todo) fresh))) seen))]
    (is (> (count states) 100))
    (is (some #(and (:intent? %) (not (:claim? %)) (= :pending (:ordinary %))) states))
    (doseq [s states]
      (is (<= (:body s) 1))
      (is (<= (:completions s) 1))
      (when (= :born (:child s)) (is (= :accepted (:decision s))))
      (when (:retired? s) (is (not (:execution-debt? s))))
      (when (:terminal? s) (is (and (:retired? s) (not (:terminal-debt? s)))))
      (doseq [next (successors s)]
        (when (:retired? s)
          (is (:retired? next))
          (is (= (:body s) (:body next)) "no fresh execution after parent retirement")))
      (when (empty? (successors s))
        (is (:terminal? s))
        (is (not= :pending (:ordinary s)))))))
