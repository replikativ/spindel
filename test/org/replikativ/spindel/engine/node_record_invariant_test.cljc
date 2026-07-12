(ns org.replikativ.spindel.engine.node-record-invariant-test
  "Regression for spindel#31: every `[:nodes id]` entry must be a
  SpinNode/SignalNode RECORD (or absent). A field-path write
  (`[:nodes id :field]`) on an absent node materializes a plain map,
  which every downstream `(or node (->spin-node …))` guard keeps
  forever; the first protocol call on it (`get-observers` in
  cache-result!) then throws and the spin's completion silently never
  notifies its observers. Seen in CI as an executor-task-fault during
  parallel-test (a sleep-timer resume caching into a poisoned node).

  The two culprit sites — make-spin's `:spin-scope` snapshot and the
  combinators' `set-owned-spins!` (whose clear-on-done can race a GC /
  generation-boundary reap of the node) — now swap the WHOLE node."
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer [deftest is testing] :include-macros true])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.test-helpers :as th]))

(deftest set-owned-spins-preserves-record-invariant
  (testing "set-owned-spins! on an ABSENT (reaped) node must not
          materialize a plain map — absence is preserved"
    (th/with-ctx [ctx]
      (spin-core/set-owned-spins! ::reaped-spin [::child-a])
      (let [n (rtp/get-state ctx [:nodes ::reaped-spin])]
        (is (or (nil? n) (record? n))
            "no plain-map node was created for the reaped spin"))))
  (testing "set-owned-spins! on an existing node keeps the record"
    (th/with-ctx [ctx]
      (let [s (spin-core/make-spin (fn [resolve _reject] (resolve 1)))
            sid (spin-core/spin-id s)]
        (spin-core/set-owned-spins! sid [::child-b])
        (let [n (rtp/get-state ctx [:nodes sid])]
          (is (record? n))
          (is (= [::child-b] (:owned-spins n))))
        ;; clearing (done? flip) keeps the record too
        (spin-core/set-owned-spins! sid nil)
        (is (record? (rtp/get-state ctx [:nodes sid])))))))

(deftest spin-scope-write-preserves-record-invariant
  (testing "make-spin's :spin-scope snapshot lands on a RECORD node even
          when scope keys are captured"
    ;; Register a (namespaced, test-only) scope key; registration is
    ;; additive and only affects spins whose ctx carries the key.
    (bindings/register-spin-scope-key! ::probe-scope)
    (th/with-ctx [ctx]
      (binding [ec/*execution-context* (assoc ctx :bindings
                                              (assoc (:bindings ctx) ::probe-scope :v))]
        (let [s (spin-core/make-spin (fn [resolve _reject] (resolve 1)))
              sid (spin-core/spin-id s)
              n (rtp/get-state ctx [:nodes sid])]
          (is (record? n) "the node is a record, not a plain map")
          (is (= {::probe-scope :v} (:spin-scope n))
              "the scope snapshot landed on the record"))))))
