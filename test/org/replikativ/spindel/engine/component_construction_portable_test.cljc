(ns org.replikativ.spindel.engine.component-construction-portable-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.component :as component]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.yggdrasil.construction :as construction]))

(deftest direct-engine-component-rollback-is-portable
  (doseq [fails? [false true]]
    (let [runtime (context/create-execution-context)
          fail? (atom fails?) calls (atom 0)
          [first-id second-id] (vec (set [0 1]))
          child (reify component/PWorldComponent
                  (realization [this] this)
                  component/PComponentRetirement
                  (retire-component! [_]
                    (swap! calls inc)
                    (when @fail? (throw (ex-info "Retry cleanup" {})))))]
      (try
        (binding [ec/*execution-context* runtime]
          (component/register! first-id
                               (reify component/PWorldComponent
                                 (realization [this] this)
                                 rtp/PForkable
                                 (fork-value [_ _ _] child)))
          (component/register! second-id
                               (reify component/PWorldComponent
                                 (realization [this] this)
                                 rtp/PForkable
                                 (fork-value [_ _ _] (throw (ex-info "Copy refused" {:refused true}))))))
        (let [error (try (context/fork-context runtime :mode :frozen) nil
                         (catch #?(:clj Throwable :cljs :default) error error))]
          (is (= 1 @calls))
          (if fails?
            (let [owner (:construction/owner (ex-data error)) result (atom nil)]
              (is (construction/owner? owner))
              (reset! fail? false)
              ((construction/dispose! owner {:sync? false})
               #(reset! result [:ok %]) #(reset! result [:error %]))
              (is (= [:ok nil] @result))
              (is (= 2 @calls)))
            (is (:refused (ex-data error)))))
        (finally (context/close-context! runtime))))))
