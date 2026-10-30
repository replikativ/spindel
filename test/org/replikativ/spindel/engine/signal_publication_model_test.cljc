(ns org.replikativ.spindel.engine.signal-publication-model-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [clojure.walk :as walk]
            [org.replikativ.spindel.engine.kernel :as kernel]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.model :as m]))

(def w [:w 0])
(def v [:w 1])
(def publish {:t :signal-publish :w w :e :source})
(defn- write [value] {:t :signal-write :w w :e :source :value value :publish? false})

(defn- view [state]
  (walk/postwalk
   (fn [value]
     (if (and (keyword? value) (#{"cancelled" "released"} (name value))
              (#{"org.replikativ.spindel.engine.kernel"
                 "org.replikativ.spindel.lifetime.model"} (namespace value)))
       (keyword "error" (name value)) value))
   (select-keys state [:worlds :env :serial :events :clocks :generation-clock])))

(defn- checked-walk! [initial actions]
  ;; Keep both concrete stores alive through the whole trace so restoring a
  ;; snapshot cannot repair an index between deferred writes and publication.
  (let [actuals (mapv #(kernel/restore initial {:cells? %}) [false true])]
    (vec
     (reductions
      (fn [before action]
        (let [{after :state :keys [refusal observation]} (m/attempt before action)]
          (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
          (is (empty? (inv/edge-check {:before before :action action :after after
                                       :refusal refusal :observation observation})) (pr-str action))
          (doseq [actual actuals]
            (let [error (try (kernel/step! actual action) nil
                             (catch #?(:clj Exception :cljs :default) e (ex-data e)))
                  snapshot (kernel/snapshot actual)]
              (is (= (some-> refusal :error name) (some-> error :error name)) (pr-str action))
              (is (= (view after) (view snapshot))
                  (pr-str action))))
          after)) initial actions))))

(defn- notifications [state world]
  (mapv #(select-keys % [:completion :debtor-world :value :source-change?])
        (filter :source-change? (:queue (m/wr state world)))))

(deftest deferred-writes-publish-the-latest-value-once-without-rewriting-it
  (doseq [kind [:signal :atom] value [nil false 2]]
    (let [actions [{:t :t02 :w w :e :source :kind kind :value :initial}
                   (write 1) (write value) publish publish]
          states (checked-walk! (m/init-state) actions)
          before (nth states 3) once (nth states 4) twice (nth states 5)
          event {:completion :source :debtor-world w :value value :source-change? true}]
      (is (= value (:result (m/ent before w :source))))
      (is (empty? (:queue (m/wr before w))))
      (is (empty? (get-in before [:env :outside])))
      (is (= (m/ent before w :source) (m/ent once w :source)))
      (is (= [event] (notifications once w)))
      (is (= [event] (notifications twice w)))
      (is (= 1 (count (:queue (m/wr twice w))))))))

(deftest default-write-still-publishes-and-deferred-write-does-not-alter-a-queued-notification
  (let [states (checked-walk!
                (m/init-state)
                [{:t :t02 :w w :e :source :value 0}
                 (dissoc (write 1) :publish?)
                 (write 2) publish
                 (assoc (write 3) :publish? true)])
        default (nth states 2) deferred (nth states 3) published (nth states 4) explicit (peek states)]
    (is (= [1] (mapv :value (notifications default w))))
    (is (= 2 (:result (m/ent deferred w :source))))
    (is (= (notifications default w) (notifications deferred w)))
    (is (= [2] (mapv :value (notifications published w))))
    (is (= [3] (mapv :value (notifications explicit w))))))

(deftest publication-reaches-foreign-followers-only-at-the-explicit-boundary
  (let [actions [{:t :t02 :w w :e :source :value 0}
                 {:t :t19 :w w :v v :k :fork :scope [:root w] :systems #{}}
                 {:t :t04 :w v :e :observer :mode :callback}
                 {:t :t05 :w v :r [:observer 1] :kind :track :debtor [:entity w :source]}
                 (write 1) (write 2) publish publish]
        states (checked-walk! (m/init-state) actions)
        before (nth states 6) once (nth states 7) twice (nth states 8)
        fdeps (:fdeps (m/wr before w))]
    (is (= #{[:source v [:o 1]]} fdeps))
    (doseq [world [w v]]
      (is (empty? (:queue (m/wr before world))))
      (is (= [{:completion :source :debtor-world w :value 2 :source-change? true}]
             (notifications once world)))
      (is (= (notifications once world) (notifications twice world))))
    (is (= fdeps (:fdeps (m/wr twice w))))
    (is (= 2 (:result (m/ent twice w :source))))
    (is (nil? (m/ent twice v :source)))
    (is (= [:run v [:observer 1]]
           (get-in twice [:worlds v :obligations [:o 1] :creditor])))))

(deftest publication-refuses-invalid-or-closed-source-authority-without-mutation
  (let [source (m/step (m/init-state) {:t :t02 :w w :e :source :value 0})
        spin (m/step (m/init-state) {:t :t04 :w w :e :source :mode :callback})
        released (m/step source {:t :t34 :w w})
        fenced (m/step source {:t :t20 :c :cut :scope [:root w]
                               :participants {:worlds #{w} :systems #{}}})
        quiescent (m/step source {:t :t20q :c :cut :scope [:root w]
                                  :participants {:worlds #{w} :systems #{}}})]
    (doseq [[before error] [[(m/init-state) ::m/released]
                            [spin ::m/released]
                            [released ::m/not-live]
                            [fenced ::m/not-admitted]
                            [quiescent ::m/not-admitted]]]
      (is (= error (get-in (m/attempt before publish) [:refusal :error])))
      (is (= before (peek (checked-walk! before [publish])))))))

(deftest publication-is-an-ordinary-effect-and-cannot-escape-retired-cleanup
  (let [initial (m/init-state {:slices? true :cps-exit? true})
        actions [{:t :t02 :w w :e :source :value 0}
                 {:t :t04 :w w :e :worker :mode :callback}
                 {:t :slice-enter :w w :r [:worker 1] :th :thread}
                 {:t :t11 :w w :r [:worker 1]}]
        retired (peek (checked-walk! initial actions))
        action (assoc publish :th :thread)]
    (is (= ::m/cancelled (get-in (m/attempt retired action) [:refusal :error])))
    (is (= retired (peek (checked-walk! retired [action]))))))
