(ns org.replikativ.spindel.engine.native-cps-fork-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]))

(deftest copied-cps-work-acquires-its-own-cleanup-only-after-entry
  (doseq [prior-finalization? [false true]]
    (let [finished (atom [])
          rt (c/runtime {:cps-exit? true :audit? true
                         :on-finalization-result #(swap! finished conj %)})
          first-gate (c/ticket :first) second-gate (c/ticket :second)
          callbacks (atom []) trace (atom []) results (atom [])
          spin (c/cspin rt :spin
                        (let [cell (c/signal rt :cell 40)]
                          (when prior-finalization?
                            (c/await-finalization (fn [r _] (r :prior))))
                          (try
                            (c/park first-gate)
                            (c/park second-gate)
                            (finally
                              (swap! trace conj [:before (c/read-signal rt cell)])
                              (c/await-finalization (fn [r _] (swap! callbacks conj r)))
                              (c/set-signal! rt cell 41)
                              (swap! trace conj [:after (c/read-signal rt cell)])))))]
      (c/observe! rt spin #(swap! results conj [:ok %]) #(swap! results conj [:error %]))
      (let [parent-run (get-in (c/snapshot rt) [:runs [:spin 1]])
            child (c/fork-parked! rt [:w 1])
            child-state (c/snapshot child)
            delivery (c/pending-ticket child first-gate)]
        (is (:cps-entered? parent-run))
        (is (= :inherited (get-in child-state [:runs [:spin 1] :status])))
        (is (not (get-in child-state [:runs [:spin 1] :cps-entered?])))
        (is (= (:finalization-sequence parent-run)
               (get-in child-state [:runs [:spin 1] :finalization-sequence])))
        (when prior-finalization? (is (pos? (:finalization-sequence parent-run))))
        (is (empty? (:native child-state)))
        (is (empty? (:cleanup-cells child-state)))
        (c/resume-ticket! child delivery :child-enter)
        (is (get-in (c/snapshot child) [:runs [:spin 1] :cps-entered?]))
        (c/cancel-spin! child spin)
        (is (= [[:before 40]] @trace))
        (is (= 1 (count @callbacks)))
        (is (false? (c/join-ready? child [:spin 1])))
        (is (empty? (:native (c/snapshot rt))))
        ((first @callbacks) :child-cleanup)
        (is (= [[:before 40] [:after 41]] @trace))
        (is (c/join-ready? child [:spin 1]))
        (is (empty? (:cleanup-cells (c/snapshot child))))
        (is (= :parked (get-in (c/snapshot rt) [:runs [:spin 1] :status])))
        (is (= 40 (get-in (c/snapshot rt) [:entities :cell :result])))
        ((first @callbacks) :duplicate)
        (c/resume-ticket! child delivery :stale)
        (is (= [[:before 40] [:after 41]] @trace))
        (c/cancel-spin! rt spin)
        (is (= 2 (count @callbacks)))
        ((second @callbacks) :parent-cleanup)
        (is (c/join-ready? rt [:spin 1]))
        (is (= [[:before 40] [:after 41] [:before 40] [:after 41]] @trace))
        (is (= #{[:w 0] [:w 1]} (set (map #(first (:owner %)) @finished))))
        (is (= 2 (count @finished)))
        (is (= [:error] (mapv first @results))))
      (verify-boundaries! rt))))

(deftest unfinished-cps-cleanup-refuses-fork-without-publication
  (doseq [cancelled? [false true]]
    (let [rt (c/runtime {:cps-exit? true :audit? true})
          callback (atom nil) results (atom []) gate (c/ticket :body)
          spin (c/cspin rt :spin
                        (let [cell (c/signal rt :cell 7)]
                          (try
                            (when cancelled? (c/park gate))
                            :done
                            (finally
                              (c/await-finalization (fn [r _] (reset! callback r)))
                              (c/read-signal rt cell)))))]
      (c/observe! rt spin #(swap! results conj [:ok %]) #(swap! results conj [:error %]))
      (when cancelled? (c/cancel-spin! rt spin))
      (let [before (c/snapshot-family rt)
            error (try (c/fork-parked! rt [:w 1]) nil
                       (catch #?(:clj Exception :cljs :default) error error))]
        (is (= :unsupported-finalization-fork (:error (ex-data error))))
        (is (= before (c/snapshot-family rt))))
      (@callback :cleanup)
      (is (c/join-ready? rt [:spin 1]))
      (is (= [(if cancelled? :error :ok)] (mapv first @results)))
      (verify-boundaries! rt))))
