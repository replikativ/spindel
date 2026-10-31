(ns org.replikativ.spindel.lifetime.cached-causal-host-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.host-origin-model-test :as h]))

(def a [:w 0])
(def b [:w 1])
(def causal {:mode :causal-follow})

(defn- trace! [initial actions]
  (reduce (fn [edges item]
            (let [before (if (seq edges) (:after (peek edges)) initial)
                  action (if (fn? item) (item before) item)
                  after (h/walk! before [action] true)]
              (conj edges {:before before :action action :after after}))) [] actions))

(defn- deliveries [edges w o]
  (vec (for [edge edges event (get-in edge [:after :events])
             :when (and (= :host-delivery (:event event)) (= w (:world event)) (= o (:o event)))]
         event)))

(defn- tl1? [edge]
  (some #(= :TL1 (:id %)) (inv/edge-check edge)))

(def reactive-prefix
  [{:t :t02 :w a :scope [:root a] :e :source :kind :signal :value 0}
   {:t :t04 :w a :e :worker :mode :callback}
   {:t :t05 :w a :r [:worker 1] :kind :track :debtor [:entity a :source] :order 0}
   {:t :t07 :w a :r [:worker 1] :value 10}
   {:t :t08 :w a :e :worker :value 10}])

(def next-completion
  [{:t :signal-write :w a :e :source :value 1}
   {:t :t08 :w a :e :source :value 1}
   (fn [s] {:t :t07 :w a :r (m/current s a :worker) :value 20})
   {:t :t08 :w a :e :worker :value 20}])

(defn- cached-trace [foreign? mode]
  (trace! (m/init-state)
          (concat reactive-prefix
                  (when foreign? [(h/fork a b)])
                  [{:t :t04 :w (if foreign? b a) :e :worker :mode mode :filter causal}]
                  (when foreign? [{:t :queued :w a}])
                  next-completion)))

(deftest cached-causal-publication-is-once-for-local-and-queued-hosts
  (doseq [foreign? [false true] mode [:callback :deref]]
    (let [edges (cached-trace foreign? mode)
          o [:o 2]
          events (deliveries edges a o)
          cached-edge (nth edges (if foreign? 7 5))
          final (:after (peek edges))]
      (is (= 1 (count events)))
      (is (true? (:causal? (first events))))
      ;; The cached diagnostic does not acquire T08's :value field (nor :e
      ;; for queued registration) as a side effect of the history correction.
      (is (= (cond-> {:event :host-delivery :world a :o o :causal? true}
               (not foreign?) (assoc :e :worker)) (first events)))
      (is (contains? (get-in cached-edge [:after :host-delivered]) [a o]))
      (is (contains? (:host-delivered final) [a o]))
      (is (empty? (inv/check-trace edges))))))

(deftest noncached-causal-publication-and-local-callbacks-retain-their-contracts
  (let [edges (trace! (m/init-state)
                      (concat [(first reactive-prefix) (assoc (second reactive-prefix) :filter causal)]
                              (drop 2 reactive-prefix) next-completion))
        events (deliveries edges a [:o 0])]
    (is (= [{:event :host-delivery :world a :e :worker :o [:o 0] :value 10 :causal? true}]
           events))
    (is (empty? (inv/check-trace edges))))
  (let [before (h/foreign-origin-basis)
        edges (trace! before [{:t :t06 :w a :o [:o 1] :value 42}
                              {:t :t07 :w a :r [:worker 1] :value 42}
                              {:t :t08 :w a :e :worker :value 42}])]
    (is (not (contains? (:host-delivered before) [a [:o 2]])))
    (is (= [{:event :host-delivery :world a :e :worker :o [:o 2] :value 42 :causal? true}]
           (deliveries edges a [:o 2])))
    (is (empty? (inv/check-trace edges))))
  (doseq [foreign? [false true]]
    (let [edges (trace! (m/init-state)
                        (concat reactive-prefix
                                (when foreign? [(h/fork a b)])
                                [{:t :t04 :w (if foreign? b a) :e :worker :mode :callback}]
                                (when foreign? [{:t :queued :w a}]) next-completion))
          events (deliveries edges a [:o 2])]
      (is (= 2 (count events)))
      (is (= (cond-> {:event :host-delivery :world a :o [:o 2]}
               (not foreign?) (assoc :e :worker)) (first events)))
      (is (false? (:causal? (second events))))
      (is (not (contains? (get-in (peek edges) [:after :host-delivered]) [a [:o 2]]))))))

(deftest copied-causal-registration-delivers-independently-in-each-world
  (let [edges (trace! (m/init-state)
                      [{:t :t04 :w a :e :worker :mode :callback :filter causal}
                       {:t :t05 :w a :r [:worker 1] :kind :await-once :debtor [:host :gate] :order 0}
                       (h/fork a b)
                       {:t :t06 :w a :o [:o 1] :value 10}
                       {:t :t07 :w a :r [:worker 1] :value 10}
                       {:t :t08 :w a :e :worker :value 10}
                       {:t :t06 :w b :o [:o 1] :value 20}
                       {:t :t07 :w b :r [:worker 1] :value 20}
                       {:t :t08 :w b :e :worker :value 20}])]
    (is (= [10] (mapv :value (deliveries edges a [:o 0]))))
    (is (= [20] (mapv :value (deliveries edges b [:o 0]))))
    (is (= #{[a [:o 0]] [b [:o 0]]} (get-in (peek edges) [:after :host-delivered])))
    (is (empty? (inv/check-trace edges)))))

(deftest unsubscribe-does-not-forget-publication-or-affect-new-registration
  (let [initial-edges (cached-trace false :callback)
        before (:after (peek initial-edges))
        edges (trace! before [{:t :unsubscribe :w a :o [:o 2]}
                              {:t :t04 :w a :e :worker :mode :callback :filter causal}])
        final (:after (peek edges))]
    (is (contains? (:host-delivered final) [a [:o 2]]))
    (is (contains? (:host-delivered final) [a [:o 3]]))
    (is (nil? (get-in final [:worlds a :obligations [:o 2]])))
    (is (= 1 (count (deliveries edges a [:o 3]))))
    (is (empty? (inv/check-trace (into initial-edges edges)))))
  (let [edges (trace! (m/init-state)
                      [{:t :t04 :w a :e :worker :mode :callback :filter causal}
                       {:t :t05 :w a :r [:worker 1] :kind :await-once :debtor [:host :gate] :order 0}
                       {:t :unsubscribe :w a :o [:o 0]}
                       {:t :t06 :w a :o [:o 1] :value 10}
                       {:t :t07 :w a :r [:worker 1] :value 10}])]
    (is (empty? (deliveries edges a [:o 0])))
    (is (empty? (get-in (peek edges) [:after :host-delivered])))))

(deftest independent-oracle-rejects-coordinated-cache-and-history-corruption
  (doseq [foreign? [false true] mode [:callback :deref]]
    (let [edges (cached-trace foreign? mode)
          index (if foreign? 7 5) edge (nth edges index)
          strip-tag (fn [events] (mapv #(if (= [:o 2] (:o %)) (dissoc % :causal?) %) events))
          corrupted (-> edge
                        (update-in [:after :events] strip-tag)
                        (update-in [:after :host-delivered] disj [a [:o 2]]))
          erased (-> corrupted
                     (update-in [:after :events] #(vec (remove (fn [ev] (= [:o 2] (:o ev))) %))))]
      (is (tl1? corrupted))
      (is (tl1? erased))
      (is (tl1? (update-in edge [:after :host-delivered] conj [b [:o 2]])))
      (is (tl1? (update-in edge [:after :events] conj
                           {:event :host-delivery :world a :o [:o 2]})))
      ;; A forged second publication is detected from the registration's
      ;; BEFORE filter even when both duplicate diagnostics omit :causal?.
      (let [last-edge (update-in (peek edges) [:after :events] conj
                                 {:event :host-delivery :world a :o [:o 2]})
            broken-trace (-> edges (assoc index corrupted)
                             (assoc (dec (count edges)) last-edge))]
        (testing (str "later duplicate for " mode)
          (is (tl1? last-edge))
          (is (some #(= [[[:host a [:o 2]] 2]] (:evidence %))
                    (inv/check-trace broken-trace))))))))

(defn- terminal-actions [terminal after-value? filter]
  (concat
   [(first reactive-prefix)]
   (when (= terminal :t13) [{:t :t12 :w a :scope [:scope :id 0] :parent [:root a]}])
   [(cond-> {:t :t04 :w a :e :worker :mode :callback :filter filter}
      (= terminal :t13) (assoc :scope [:scope :id 0]))
    (nth reactive-prefix 2)]
   (when after-value? (drop 3 reactive-prefix))
   [(case terminal
      :t11 {:t :t11 :w a :r [:worker 1]}
      :t13 {:t :t13 :w a :scope [:scope :id 0]}
      :t34 {:t :t34 :w a})]))

(deftest causal-errors-and-values-share-one-registration-history
  (doseq [terminal [:t11 :t13 :t34] after-value? [false true]]
    (let [edges (trace! (m/init-state) (terminal-actions terminal after-value? causal))
          events (deliveries edges a [:o 0])
          final (:after (peek edges))]
      (is (= 1 (count events)))
      (is (true? (:causal? (first events))))
      (is (= (if after-value? 10 (if (= terminal :t34) ::m/released ::m/cancelled))
             (:value (first events))))
      (is (contains? (:host-delivered final) [a [:o 0]]))
      (is (nil? (get-in final [:worlds a :obligations [:o 0]])))
      (is (some #(and (= :obligation-exit (:event %)) (= [:o 0] (:o %)))
                (get-in (peek edges) [:after :events])))
      (is (empty? (inv/check-trace edges)))))
  (doseq [terminal [:t11 :t13 :t34]]
    (let [edges (trace! (m/init-state) (terminal-actions terminal true {:mode :local}))
          events (deliveries edges a [:o 0])]
      (is (= 2 (count events)))
      (is (false? (:causal? (first events))))
      (is (not (contains? (second events) :causal?)))
      (is (empty? (get-in (peek edges) [:after :host-delivered]))))))

(deftest direct-foreign-cached-host-is-not-rejected-after-its-value
  (let [initial-edges (cached-trace true :callback)
        edges (trace! (:after (peek initial-edges))
                      [{:t :unsubscribe :w a :o [:o 0]}
                       {:t :t11 :w a :r (m/current (:after (peek initial-edges)) a :worker)}])]
    (is (empty? (deliveries edges a [:o 2])))
    (is (contains? (get-in (peek edges) [:after :host-delivered]) [a [:o 2]]))
    (is (empty? (inv/check-trace (into initial-edges edges))))))

(deftest first-direct-foreign-host-error-keeps-its-real-origin
  (let [edges (trace! (m/init-state)
                      [(first reactive-prefix) (h/fork a b)
                       (second reactive-prefix) (nth reactive-prefix 2)
                       {:t :t04 :w b :e :worker :mode :callback :filter causal}
                       {:t :queued :w a}
                       {:t :unsubscribe :w a :o [:o 0]}
                       {:t :t11 :w a :r [:worker 1]}])]
    (is (= [{:event :host-delivery :world a :o [:o 2] :value ::m/cancelled :causal? true}]
           (deliveries edges a [:o 2])))
    (is (contains? (get-in (peek edges) [:after :host-delivered]) [a [:o 2]]))
    (is (empty? (inv/check-trace edges)))))

(deftest inherited-host-error-is-world-qualified-and-authenticated
  (let [edges (trace! (m/init-state)
                      [{:t :t04 :w a :e :worker :mode :callback :filter causal}
                       {:t :t05 :w a :r [:worker 1] :kind :await-once :debtor [:host :gate] :order 0}
                       (h/fork a b)
                       {:t :t11 :w b :r [:worker 1]}
                       {:t :t11 :w a :r [:worker 1]}])]
    (is (= [::m/cancelled] (mapv :value (deliveries edges b [:o 0]))))
    (is (= [::m/cancelled] (mapv :value (deliveries edges a [:o 0]))))
    (is (= #{[a [:o 0]] [b [:o 0]]} (get-in (peek edges) [:after :host-delivered])))
    (is (empty? (inv/check-trace edges)))
    ;; A stale descriptor cannot manufacture egress by claiming another
    ;; world's origin, even on the error path. This is a corruption control.
    (let [before (:after (nth edges 2))
          invalid (assoc-in before [:worlds b :obligations [:o 0] :filter :origin] [:w 99])
          ob (get-in invalid [:worlds b :obligations [:o 0]])
          after (m/deliver-host (assoc invalid :events []) b [:o 0] ob
                                {:event :host-delivery :world b :o [:o 0] :value ::m/cancelled})]
      (is (empty? (:events after)))
      (is (not (contains? (:host-delivered after) [b [:o 0]]))))))

(deftest first-error-missing-tag-or-history-cannot-hide-from-oracles
  (doseq [terminal [:t11 :t13 :t34]]
    (let [edges (trace! (m/init-state) (terminal-actions terminal false causal))
          edge (peek edges)
          corrupt (-> edge
                      (update-in [:after :events]
                                 #(mapv (fn [ev] (if (= :host-delivery (:event ev)) (dissoc ev :causal?) ev)) %))
                      (update-in [:after :host-delivered] disj [a [:o 0]]))
          omitted (update-in corrupt [:after :events] #(vec (remove (fn [ev] (= :host-delivery (:event ev))) %)))]
      (is (tl1? corrupt))
      (is (tl1? omitted))
      (let [duplicate (update-in corrupt [:after :events] conj
                                 {:event :host-delivery :world a :o [:o 0] :value ::m/cancelled})]
        (is (some #(= [[[:host a [:o 0]] 2]] (:evidence %))
                  (inv/check-trace (conj (pop edges) duplicate))))))))

(deftest pending-host-release-and-tombstone-rejection-are-once-in-the-model
  ;; The kernel release profile explicitly excludes queued HOST/start ingress.
  ;; Keep this core-model proof separate rather than widening that adapter.
  (doseq [cached? [false true]]
    (let [before (h/walk! (m/init-state)
                          (concat [(first reactive-prefix) (h/fork a b)]
                                  [(second reactive-prefix) (nth reactive-prefix 2)]
                                  (when cached? (drop 3 reactive-prefix))
                                  [{:t :t04 :w b :e :worker :mode :callback :filter causal}]) true)
          packet (first (filter :register-host (get-in before [:worlds a :queue])))
          action {:t :t34 :w a}
          after (h/checked before action)
          edge {:before before :action action :after after}
          o (:register-host packet)
          outcome (filter #(and (= :host-delivery (:event %)) (= o (:o %))) (:events after))
          ;; Re-delivery of the real admitted packet after tombstoning must
          ;; not publish a second outcome, and must preserve the first one.
          retried (m/enqueue after a packet)]
      (is (some? packet))
      (is (= [{:event :host-delivery :world a :o o :value ::m/released :causal? true}]
             (vec outcome)))
      (is (contains? (:host-delivered after) [a o]))
      (is (= after retried))
      (is (empty? (inv/check-trace [edge])))
      (let [corrupt (-> edge
                        (update-in [:after :events]
                                   #(mapv (fn [ev] (if (= o (:o ev)) (dissoc ev :causal?) ev)) %))
                        (update-in [:after :host-delivered] disj [a o]))]
        (is (tl1? corrupt))))))

(deftest ephemeral-t04-authority-requires-local-immediate-cache-publication
  (let [before (h/walk! (m/init-state) (concat reactive-prefix [(h/fork a b)]) true)
        action {:t :t04 :w a :e :worker :mode :deref :filter causal}
        after (h/walk! before [action] true)
        edge {:before before :action action :after after}
        wrong-world {:event :host-delivery :world b :o [:o 2] :causal? true}
        forged (-> edge (update-in [:after :events] conj wrong-world)
                   (update-in [:after :host-delivered] conj [b [:o 2]]))]
    (is (nil? (inv/causal-host-registration-proof before action wrong-world)))
    (is (tl1? forged))
    (is (empty? (inv/edge-check edge))))
  (let [before (m/init-state)
        action {:t :t04 :w a :e :worker :mode :deref :filter causal}
        after (h/walk! before [action] true)
        invented {:event :host-delivery :world a :o [:o 0] :causal? true}
        forged {:before before :action action
                :after (-> after (update :events conj invented)
                           (update :host-delivered (fnil conj #{}) [a [:o 0]]))}]
    (is (nil? (inv/causal-host-registration-proof before action invented)))
    (is (tl1? forged)))
  (let [before (h/walk! (m/init-state) (concat reactive-prefix [(h/fork a b)]) true)
        action {:t :t04 :w b :e :worker :mode :deref :filter causal}
        after (h/walk! before [action] true)
        premature {:event :host-delivery :world a :o [:o 2] :causal? true}
        forged {:before before :action action
                :after (-> after (update :events conj premature)
                           (update :host-delivered (fnil conj #{}) [a [:o 2]]))}]
    ;; Even an actual completed ancestor must consume the admitted queued
    ;; packet before its foreign registration has publication authority.
    (is (nil? (inv/causal-host-registration-proof before action premature)))
    (is (tl1? forged))))

(deftest vanished-cached-deref-registration-still-identifies-later-duplicates
  (doseq [foreign? [false true]]
    (let [edges (cached-trace foreign? :deref)
          edge (peek edges)
          duplicate {:event :host-delivery :world a :o [:o 2]}
          corrupt (update-in edge [:after :events] conj duplicate)]
      (is (contains? (get-in edge [:before :host-delivered]) [a [:o 2]]))
      (is (nil? (get-in edge [:before :worlds a :obligations [:o 2]])))
      (is (nil? (inv/causal-host-registration-proof (:before edge) (:action edge) duplicate)))
      (is (= (get-in edge [:after :host-delivered]) (get-in corrupt [:after :host-delivered])))
      (is (tl1? corrupt))
      (is (some #(= [[[:host a [:o 2]] 2]] (:evidence %))
                (inv/check-trace (conj (pop edges) corrupt)))))))
