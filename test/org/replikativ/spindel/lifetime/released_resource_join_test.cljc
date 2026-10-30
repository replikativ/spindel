(ns org.replikativ.spindel.lifetime.released-resource-join-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]))

(def w [:w 0])
(def root [:root w])
(def ancestor [:scope :id 0])
(def parent [:parent 1])
(def owner [:owner 1])
(def consumer [:host [:o 2]])
(def mailbox :mailbox)
(def raw-frame [:mailbox-frame consumer])
(def receipt [:mailbox-callback w owner consumer])
(def release-world {:t :t34 :w w})

(defn checked [before action]
  (let [{after :state :keys [refusal observation]} (m/attempt before action)
        edge {:before before :action action :after after :refusal refusal :observation observation}]
    (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
    (is (empty? (inv/edge-check edge)) (pr-str [action (inv/edge-check edge)]))
    (when-not (= :join (:t action)) (is (nil? refusal) (pr-str [action refusal])))
    after))

(defn blocked [state targets]
  (doseq [target targets]
    (let [action {:t :join :w w :x target :timeout? true}
          result (m/attempt state action)]
      (is (false? (m/join-ready? state w target)))
      (is (= ::m/join-timeout (get-in result [:refusal :error])) (pr-str target))
      (checked state action))))

(defn ready [state targets]
  (doseq [target targets]
    (is (= {:complete? true :busy []}
           (:observation (m/attempt state {:t :join :w w :x target :timeout? true}))))
    (checked state {:t :join :w w :x target :timeout? true})))

(defn raw-with-forgotten-owner [variant]
  (let [initial (reduce checked (m/init-state {:slices? true})
                        [{:t :t12 :w w :scope ancestor :parent root}
                         {:t :t04 :w w :e :parent :scope ancestor :mode :callback}
                         {:t :t04 :w w :e :owner :scope parent :mode :callback}
                         {:t :mailbox-create :w w :e mailbox :allocation mailbox :scope owner}])
        selected (if (= :error variant)
                   (checked initial {:t :mailbox-take :w w :e mailbox :allocation mailbox
                                     :kind :host :consumer consumer :o [:o 2] :order 0})
                   (let [posted (checked initial {:t :mailbox-post-request :w w :e mailbox
                                                  :allocation mailbox :value 41})
                         event (first (:queue (m/wr posted w)))
                         buffered (checked posted (assoc (dissoc event :mailbox-post)
                                                         :t :mailbox-post :w w :e mailbox))
                         taken (checked buffered {:t :mailbox-take :w w :e mailbox :allocation mailbox
                                                  :kind :host :consumer consumer :o [:o 2] :order 0})
                         mid (get-in taken [:worlds w :entities mailbox :mailbox :reservations consumer :message-id])]
                     (checked taken {:t :mailbox-claim :w w :e mailbox :allocation mailbox :consumer consumer
                                     :message-id mid :frame raw-frame :inline? true})))
        retired (checked selected {:t :t11 :w w :r owner})]
    (is (nil? (m/run retired w owner)))
    (is (nil? (m/ent retired w mailbox)))
    (is (= [owner parent ancestor root w] (get-in retired [:env :native receipt :anchor])))
    retired))

(defn return-raw [state]
  (checked state {:t :mailbox-return :w w :e mailbox :allocation mailbox :consumer consumer :frame raw-frame}))

(deftest released-raw-success-retains-ancestry-after-its-ordinary-owner-was-forgotten
  (let [before (raw-with-forgotten-owner :ok)
        targets [owner parent ancestor root w]
        released (checked before release-world)]
    (is (= [owner parent ancestor root w] (get-in released [:env :native receipt :anchor])))
    (is (= #{:id :lineage :status} (set (keys (m/wr released w)))))
    (blocked before targets)
    (blocked released targets)
    (let [returned (return-raw released)]
      (is (empty? (get-in returned [:env :native])))
      (is (empty? (get-in returned [:env :cleanup-cells])))
      (ready returned targets))))

(deftest released-queued-raw-rejection-blocks-until-entry-and-real-return
  (let [before (raw-with-forgotten-owner :error)
        targets [owner parent ancestor root w]
        released (checked before release-world)
        entered (checked released {:t :mailbox-claim :w w :e mailbox :allocation mailbox
                                   :consumer consumer :variant :error :callback receipt :frame raw-frame})]
    (is (= :queued (get-in released [:env :native receipt :phase])))
    (is (false? (get-in released [:env :native receipt :physical?])))
    (is (= [owner parent ancestor root w] (get-in released [:env :native receipt :anchor])))
    (blocked before targets)
    (blocked released targets)
    (is (= :executing (get-in entered [:env :native receipt :phase])))
    (blocked entered targets)
    (ready (return-raw entered) targets)))

(deftest independent-release-oracle-rejects-the-old-blanket-restamp-even-if-indices-agree
  (doseq [variant [:ok :error]]
    (let [before (raw-with-forgotten-owner variant)
          released (checked before release-world)
          lost-anchor [owner w]
          corrupt (assoc-in released [:env :native receipt :anchor] lost-anchor)
          ;; Corrupt the mirrored physical edge too: mutual consistency cannot
          ;; certify that a vanished ordinary owner's ancestor IDs were kept.
          corrupt (if (= :ok variant)
                    (assoc-in corrupt [:env :cleanup-cells [w owner mailbox] :mailbox :physical raw-frame :anchor]
                              lost-anchor) corrupt)
          edge {:before before :action release-world :after corrupt}]
      (is (empty? (inv/check corrupt)))
      (is (m/join-ready? corrupt w ancestor))
      (is (seq (inv/released-join-evidence-errors edge)))
      (is (some #(= :TL19 (:id %)) (inv/edge-check edge)))
      (is (empty? (inv/released-join-evidence-errors (assoc edge :after released)))))))

(deftest ordinary-and-timer-release-ancestry-follows-live-adoption-before-freezing
  (doseq [timer? [false true]]
    (let [child [:child 1] successor [:parent 2]
          timer-o [:o 2] timer-id [:timer w timer-o]
          initial (reduce checked (m/init-state {:slices? true})
                          [{:t :t12 :w w :scope ancestor :parent root}
                           {:t :t04 :w w :e :parent :scope ancestor :mode :callback}
                           {:t :t01 :w w :e :child :scope parent :order 0}
                           {:t :t04 :w w :e :child :scope parent :mode :callback}
                           {:t :slice-enter :w w :r child :th :worker}])
          initial (if timer?
                    (reduce checked initial
                            [{:t :timer-register :w w :r child :th :worker :o timer-o :n timer-id
                              :order 0 :delay-ms 10 :value 41}
                             {:t :timer-install-result :w w :n timer-id :variant :ok :handle? true}]) initial)
          adopted (checked initial {:t :t09 :w w :e :parent :cause :track :order 1})
          released (checked adopted release-world)
          expected [child successor ancestor root w]
          old-anchor [child parent ancestor root w]
          corrupt (assoc-in released [:env :threads :worker :anchor] old-anchor)
          corrupt (if timer? (assoc-in corrupt [:env :native timer-id :anchor] old-anchor) corrupt)]
      (is (= successor (:owner (m/run adopted w child))))
      (is (= expected (get-in released [:env :threads :worker :anchor])))
      (when timer? (is (= expected (get-in released [:env :native timer-id :anchor]))))
      (is (m/join-ready? released w parent))
      (blocked released [child successor ancestor root w])
      (is (empty? (inv/check corrupt)))
      (is (seq (inv/released-join-evidence-errors {:before adopted :action release-world :after corrupt})))
      (let [disposed (if timer?
                       (reduce checked released
                               [{:t :timer-handle-release :w w :n timer-id :phase :claim}
                                {:t :timer-handle-release :w w :n timer-id :phase :returned :variant :ok}]) released)
            returned (checked disposed {:t :t38 :th :worker})]
        (ready returned [child successor ancestor root w])))))
