(ns org.replikativ.spindel.engine.component-construction-test
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.engine.component :as component]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.yggdrasil.construction :as construction]))

(defrecord Retirable [id calls fail-copy? fail-cleanup? child?]
  component/PWorldComponent
  (realization [this] this)
  component/PComponentRetirement
  (retire-component! [_]
    (swap! calls conj [:retire id child?])
    (when @fail-cleanup? (throw (ex-info "Cleanup before ACK failed" {}))))
  rtp/PForkable
  (fork-value [this _ _]
    (swap! calls conj [:fork id])
    (when fail-copy? (throw (ex-info "Second component refused" {:copy-refused true})))
    (assoc this :child? true)))

(defn- failure [f] (try (f) nil (catch Exception error error)))

(defn- register-pair! [runtime calls fail-cleanup?]
  ;; Match the constructor's set order rather than assume a particular hash order.
  (let [[first-id second-id] (vec (set [0 1]))]
    (binding [ec/*execution-context* runtime]
      (component/register! first-id (->Retirable :first calls false fail-cleanup? false))
      (component/register! second-id (->Retirable :second calls true (atom false) false)))))

(deftest direct-and-ygg-failures-release-earlier-component-copies
  (doseq [fork [(fn [runtime] (context/fork-context runtime :mode :frozen))
                (fn [runtime] (binding [ec/*execution-context* runtime]
                                (ygg/fork! {:mode :frozen :sync? true})))]]
    (let [runtime (context/create-execution-context) calls (atom [])]
      (try
        (register-pair! runtime calls (atom false))
        (is (:copy-refused (ex-data (failure #(fork runtime)))))
        (is (= [[:fork :first] [:fork :second] [:retire :first true]] @calls))
        (is (= 2 (count (binding [ec/*execution-context* runtime] (component/registered)))))
        (finally (context/close-context! runtime))))))

(deftest direct-failure-keeps-cleanup-owner-and-retries-without-reforking
  (let [runtime (context/create-execution-context) calls (atom []) fail? (atom true)]
    (try
      (register-pair! runtime calls fail?)
      (let [error (failure #(context/fork-context runtime :mode :frozen))
            owner (:construction/owner (ex-data error))]
        (is (construction/owner? owner))
        (is (= :held (:status (construction/info owner))))
        (is (= [[:fork :first] [:fork :second] [:retire :first true]] @calls))
        (reset! fail? false)
        (construction/dispose! owner {:sync? true})
        (construction/dispose! owner {:sync? true})
        (is (= [[:fork :first] [:fork :second] [:retire :first true] [:retire :first true]] @calls))
        (is (= :closed (:status (construction/info owner)))))
      (finally (context/close-context! runtime)))))

(deftest observer-failure-after-component-ack-keeps-the-copy-owned
  (let [runtime (context/create-execution-context) calls (atom [])]
    (try
      (binding [ec/*execution-context* runtime]
        (component/register! (->Retirable :only calls false (atom false) false)))
      (is (= :observer-refused
             (:type (ex-data
                     (failure #(context/fork-context
                                runtime :mode :frozen
                                :fork-observer (fn [event]
                                                 (when (= :component-value (:phase event))
                                                   (throw (ex-info "Observer refused" {:type :observer-refused}))))))))))
      (is (= [[:fork :only] [:retire :only true]] @calls))
      (finally (context/close-context! runtime)))))

(deftest observer-refusal-before-copy-is-not-an-uncertain-acquisition
  (let [runtime (context/create-execution-context) calls (atom [])]
    (try
      (binding [ec/*execution-context* runtime]
        (component/register! (->Retirable :only calls false (atom false) false)))
      (let [error (failure #(context/fork-context
                             runtime :mode :frozen
                             :fork-observer (fn [event]
                                              (when (= :component-before (:phase event))
                                                (throw (ex-info "Before-copy refusal" {:before-copy true}))))))]
        (is (:before-copy (ex-data error)))
        (is (nil? (:construction/owner (ex-data error))))
        (is (empty? @calls)))
      (finally (context/close-context! runtime)))))

(deftest successful-construction-does-not-retire-a-published-child
  (let [runtime (context/create-execution-context) calls (atom [])]
    (try
      (let [ref (binding [ec/*execution-context* runtime]
                  (component/register! (->Retirable :only calls false (atom false) false)))
            child (context/fork-context runtime :mode :frozen)]
        (try
          (is (= [[:fork :only]] @calls))
          (is (:child? (component/resolve-in child ref)))
          ;; Only its final owner may release a successfully published child.
          (component/retire-component! (component/resolve-in child ref))
          (is (= [[:fork :only] [:retire :only true]] @calls))
          (finally (context/close-context! child))))
      (finally (context/close-context! runtime)))))

(deftest multiple-acquired-components-unwind-in-reverse-order
  (let [runtime (context/create-execution-context) calls (atom [])
        ids (vec (set [0 1 2]))]
    (try
      (binding [ec/*execution-context* runtime]
        (doseq [[id role] (map vector ids [:first :second :third])]
          (component/register! id (->Retirable role calls (= :third role) (atom false) false))))
      (is (:copy-refused (ex-data (failure #(context/fork-context runtime :mode :frozen)))))
      (is (= [[:fork :first] [:fork :second] [:fork :third]
              [:retire :second true] [:retire :first true]] @calls))
      (finally (context/close-context! runtime)))))

(deftest returned-cleanup-capabilities-are-owned-and-deduplicated-by-identity
  (let [runtime (context/create-execution-context) calls (atom [])
        ids (vec (set [0 1 2]))
        child (->Retirable :same calls false (atom false) true)]
    (try
      (binding [ec/*execution-context* runtime]
        (doseq [id (take 2 ids)]
          ;; Source and child may have different protocol implementations.
          (component/register!
           id (reify component/PWorldComponent
                (realization [this] this)
                rtp/PForkable
                (fork-value [_ _ _] child))))
        (component/register! (last ids) (->Retirable :third calls true (atom false) false)))
      (is (:copy-refused (ex-data (failure #(context/fork-context runtime :mode :frozen)))))
      (is (= [[:fork :third] [:retire :same true]] @calls))
      (finally (context/close-context! runtime)))))
