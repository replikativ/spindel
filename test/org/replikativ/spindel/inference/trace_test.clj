(ns org.replikativ.spindel.inference.trace-test
  "The inference layer over savepoint traces, through its own API."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.inference.trace :as itrace]
            [org.replikativ.spindel.inference.effects :refer [sample observe factor]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [anglican.runtime :as ar]))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [outcome (deref result 20000 ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok (first outcome)) (second outcome) (throw (second outcome))))))

(defmacro ^:private with-session [[root session] & body]
  `(let [~root (context/create-execution-context)
         ~session (sp/open! ~root {:fork-opts {:systems :none} :retain-released? false})]
     (try
       ~@body
       (finally
         (await-cps (sp/close! ~session))
         (context/close-context! ~root)))))

(defn- model []
  (spin
   (let [x (sample (ar/normal 0.0 1.0) :id :x)
         z (sample (ar/normal x 1.0) :id :z)]
     (observe (ar/normal z 1.0) 3.0 :id :y)
     (factor -0.5)
     [x z])))

(defn- log-normal [v mean sd]
  (ar/observe* (ar/normal mean sd) v))

(deftest assess-is-the-hand-computed-log-joint
  (with-session [root session]
    (let [t (await-cps (trace/run session
                                  (binding [ec/*execution-context* root] (model))
                                  (itrace/policy {:constraints {:x 0.5 :z 2.0}})))
          expected (+ (log-normal 0.5 0.0 1.0)
                      (log-normal 2.0 0.5 1.0)
                      (log-normal 3.0 2.0 1.0)
                      -0.5)]
      (is (= [0.5 2.0] (:trace/result t)))
      (is (< (Math/abs (- expected (itrace/log-joint t))) 1e-9))
      (testing "with everything fixed the weight is the joint"
        (is (< (Math/abs (- expected (itrace/log-weight t))) 1e-9)))
      (is (empty? (itrace/latent-addresses t))))))

(deftest forward-simulation-weighs-by-the-likelihood
  (with-session [root session]
    (let [t (await-cps (trace/run session
                                  (binding [ec/*execution-context* root] (model))
                                  (itrace/policy)))
          [_ z] (:trace/result t)]
      (is (= [:x :z] (itrace/latent-addresses t)))
      (is (< (Math/abs (- (+ (log-normal 3.0 z 1.0) -0.5) (itrace/log-weight t))) 1e-9))
      (testing "every site has its density, sampled ones included"
        (is (every? (comp number? :log-prob :note) (itrace/entries t)))))))

(deftest a-chain-repeats-its-conditioning-in-every-move
  ;; x ~ N(0,1), z | x ~ N(x,1) fixed at 3  =>  x | z ~ N(1.5, 1/2)
  (let [finals
        (mapv (fn [seed]
                (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG (long seed))
                (with-session [root session]
                  (let [constraints {:z 3.0}
                        initial (await-cps (trace/run session
                                                      (binding [ec/*execution-context* root] (model))
                                                      (itrace/policy {:constraints constraints})))
                        {final :trace} (await-cps (itrace/mh-chain initial 60
                                                                  {:constraints constraints}))]
                    (is (= [:x] (itrace/latent-addresses final)))
                    (is (= 3.0 (second (:trace/result final))))
                    (first (:trace/result final)))))
              (range 1 81))
        mean (/ (reduce + finals) (count finals))]
    (is (< (Math/abs (- mean 1.5)) 0.25) (str "x mean " mean))))

(deftest a-block-moves-together
  (with-session [root session]
    (let [initial (await-cps (trace/run session
                                        (binding [ec/*execution-context* root] (model))
                                        (itrace/policy)))
          both (fn [_ _] {:targets #{:x :z} :log-selection (constantly 0.0)})
          moved (atom nil)]
      (await-cps (itrace/mh-chain initial 30
                                  {:select both
                                   :on-step (fn [{:keys [accepted? trace]}]
                                              (when accepted? (reset! moved trace)))}))
      (is (some? @moved) "some block move was accepted")
      (let [[x z] (:trace/result initial)
            [x' z'] (:trace/result @moved)]
        (is (and (not= x x') (not= z z')) "both targets were proposed")))))

(deftest a-malformed-proposal-is-an-error-not-a-null-pointer
  (with-session [root session]
    (let [initial (await-cps (trace/run session
                                        (binding [ec/*execution-context* root] (model))
                                        (itrace/policy)))
          outcome (try (await-cps (itrace/mh-step initial {:propose (fn [_ _] {:value 1.0})}))
                       (catch Throwable error error))]
      (is (= ::itrace/malformed-proposal (:type (ex-data outcome)))))))

(deftest a-chain-holds-the-worlds-of-one-trace
  ;; Every move forks a world per site it reruns. Whatever the move's outcome,
  ;; the loser's worlds go back, the proposal's own world included (it is
  ;; released from inside its own terminal handler).
  (with-session [root session]
    (let [initial (await-cps (trace/run session
                                        (binding [ec/*execution-context* root] (model))
                                        (itrace/policy)))
          sites (count (:trace/order initial))
          {:keys [accepted]} (await-cps (itrace/mh-chain initial 150 nil))
          handles #(count (:handles @(:scope session)))]
      (is (< 10 accepted 140) "both outcomes happened")
      (loop [tries 0]
        (when (and (< tries 100) (> (handles) (+ sites 2)))
          (Thread/sleep 20)
          (recur (inc tries))))
      (is (<= (handles) (+ sites 2)) (str (handles) " worlds for " sites " sites")))))
