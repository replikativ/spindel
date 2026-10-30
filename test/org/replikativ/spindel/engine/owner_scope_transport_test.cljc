(ns org.replikativ.spindel.engine.owner-scope-transport-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [is.simm.partial-cps.async :as pcps #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.protocols :as rtp]))

(deftest absent-owner-transport-does-not-dispatch-without-a-context
  (binding [ec/*execution-context* nil]
    (with-redefs [rtp/capture-execution-owner
                  (fn [& _] (throw (ex-info "Unexpected capture dispatch" {})))
                  rtp/restore-execution-owner
                  (fn [& _] (throw (ex-info "Unexpected restore dispatch" {})))]
      (is (nil? (ec/capture-owner-scope nil)))
      (is (nil? (ec/restore-owner-scope nil :current-owner)))
      (is (nil? (ec/restore-owner-binding nil :current-owner :entered-owner))))))

(deftest combined-context-and-absent-owner-binding-resumes-outside-any-context
  (let [rt (context/create-execution-context)]
    (try
      (doseq [outcome [:success :error]]
        (let [parked (atom nil) values (atom []) entered (atom [])]
          (binding [ec/*execution-context* nil ec/*owner-scope* nil]
            (let [operation
                  (pcps/async
                   (let [value (binding [ec/*execution-context* rt ec/*owner-scope* nil]
                                 (swap! entered conj [(identical? rt ec/*execution-context*) ec/*owner-scope*])
                                 (pcps/await (fn [resolve reject]
                                               (reset! parked [resolve reject])
                                               nil)))]
                     [value ec/*execution-context* ec/*owner-scope*]))]
              (pcps/with-trampoline
                (operation #(swap! values conj [:ok %])
                           #(swap! values conj [:error [ec/*execution-context* ec/*owner-scope* (ex-data %)]])))
              (is (= [[true nil]] @entered))
              (is (some? @parked))
              (is (empty? @values))
              ;; The binding/trampoline that parked the operation has returned.
              ;; Neither context nor owner is supplied by this external resume.
              (binding [pcps/*in-trampoline* false]
                (pcps/with-trampoline
                  (if (= :success outcome)
                    ((first @parked) :ready)
                    ((second @parked) (ex-info "Expected rejection" {:reason :expected})))))
              (is (= [(if (= :success outcome)
                        [:ok [:ready nil nil]]
                        [:error [nil nil {:reason :expected}]])]
                     @values))
              (is (nil? ec/*execution-context*))
              (is (nil? ec/*owner-scope*))))))
      (finally (context/stop-context! rt)))))

(deftest captured-native-owner-still-requires-a-backend-for-restoration
  (let [rt (context/create-execution-context {:engine :owned})]
    (try
      (let [captured (binding [ec/*execution-context* rt]
                       (ec/capture-owner-scope (lifetime/root-scope rt)))]
        (is (some? captured))
        (binding [ec/*execution-context* nil]
          (is (thrown? #?(:clj Exception :cljs js/Error)
                       (ec/restore-owner-scope captured nil)))))
      (finally (context/release-context! rt)))))
