(ns org.replikativ.spindel.dom.deferred-eviction-test
  "Regression: per-element cache eviction on unmount must be DEFERRED to
  end-of-cycle and must spare any address still claimed by a live element
  in the same render pass.

  Eager evict-on-unmount is unsafe — unmount runs before the live subtree
  is render-initial!'d, so an address can appear in both a destroyed
  subtree and a live one within one pass (a churned parent whose keyed
  descendants survive). Evicting eagerly would wipe the live descendant's
  cache; its next reconcile then diffs against an empty cache and emits
  :add-only deltas, duplicating the DOM subtree."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.cache :as cache]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]))

(deftest deferred-eviction-spares-live-addresses
  (testing "call-refs-on-unmount! defers eviction; flush spares *rendered-addrs*"
    (with-ctx [_ctx]
      ;; Two cached addresses: one whose element is genuinely gone, one
      ;; that a live element re-claims this pass.
      (cache/set-slot-cache! :el-dead [{:type :nil :value nil}])
      (cache/set-slot-cache! :el-live [{:type :nil :value nil}])
      (binding [disch/*pending-evictions* (atom #{})
                disch/*rendered-addrs*    (atom {:el-live {:tag :div :addr :el-live}})]
        ;; Unmount a vnode at each address.
        (#'disch/call-refs-on-unmount! {:tag :div :addr :el-dead})
        (#'disch/call-refs-on-unmount! {:tag :div :addr :el-live})

        ;; Eviction is DEFERRED — both caches still present mid-pass.
        (is (some? (cache/get-slot-cache :el-dead))
            "eviction is deferred, not eager")
        (is (some? (cache/get-slot-cache :el-live))
            "eviction is deferred, not eager")

        ;; End-of-cycle flush.
        (disch/flush-pending-evictions!)
        (is (nil? (cache/get-slot-cache :el-dead))
            "address with no live claimant is evicted")
        (is (some? (cache/get-slot-cache :el-live))
            "address still claimed in *rendered-addrs* is spared")))))

(deftest flush-removes-element-registry-entry-on-unmount
  (testing "flush-pending-evictions! drops the discharge's addr->element entry
            for unmounted addresses, but spares addresses re-claimed live (#8)"
    (with-ctx [_ctx]
      (let [{:keys [discharge elements]} (disch/make-mock-discharge)]
        ;; Register an element at each address (as render-initial! would).
        (disch/set-element! discharge :el-dead :node-dead)
        (disch/set-element! discharge :el-live :node-live)
        (binding [disch/*pending-evictions* (atom #{})
                  disch/*rendered-addrs*    (atom {:el-live {:tag :div :addr :el-live}})]
          (#'disch/call-refs-on-unmount! {:tag :div :addr :el-dead})
          (#'disch/call-refs-on-unmount! {:tag :div :addr :el-live})
          ;; Pass the discharge so flush also prunes the element registry.
          (disch/flush-pending-evictions! discharge)
          (is (nil? (get @elements :el-dead))
              "unmounted address must be removed from the element registry")
          (is (= :node-live (get @elements :el-live))
              "address still claimed by a live element must be retained"))))))

(deftest eager-eviction-fallback-without-render-pass
  (testing "Outside a render pass (no *pending-evictions* binding) eviction is eager"
    (with-ctx [_ctx]
      (cache/set-slot-cache! :el-x [{:type :nil :value nil}])
      ;; No *pending-evictions* binding → fall back to eager evict-cache!.
      (#'disch/call-refs-on-unmount! {:tag :div :addr :el-x})
      (is (nil? (cache/get-slot-cache :el-x))
          "with no render pass active, unmount evicts immediately"))))
