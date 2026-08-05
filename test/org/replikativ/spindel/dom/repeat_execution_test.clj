(ns org.replikativ.spindel.dom.repeat-execution-test
  "A body executed MORE THAN ONCE for one commit must produce the same DOM as
   executing it once.

   This is the second half of the invariant `superseded_run_test` covers. That
   one asserts an ABANDONED run changes nothing; this one asserts a REPEATED
   run changes nothing extra. They fail on opposite releases, which is the
   point:

     spindel 0.1.37 (pre-R3)  — repeat is safe, abandonment CORRUPTS
     spindel 0.1.38 (R3)      — abandonment is safe, repeat DUPLICATES

   Neither is correct. R3 removed the compute-time cache write that had been
   doing double duty as BOTH the reconciliation baseline AND an
   already-emitted marker; separating the baseline was right, and nothing
   replaced the marker. `*applied-vnodes*` cannot be it — it is object-identity
   keyed by design, so two vnodes from two executions are invisible to it.

   Measured downstream before this test existed: collapsing and re-expanding a
   sidebar section in simmis went from 9 containers to 15, because the expand's
   `:add` was applied twice.

   The fix these tests define acceptance for is not another dedup guard but
   moving reconciliation to commit time, so that promoting the baseline and
   applying the delta are ONE step — a second execution then diffs against an
   already-advanced baseline and collapses to nothing."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.cache :as cache]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.dom.foreach :refer [ifor-each]]
            [org.replikativ.spindel.test-async :refer [await-drain]]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]))

(defn clean-context-fixture [f]
  (binding [ec/*execution-context* nil]
    (f)))

(use-fixtures :each clean-context-fixture)

(defn- op-counts
  "Structural ops only — creates and inserts. Attribute writes are idempotent
   at the DOM level (setting the same class twice is invisible), but an extra
   `insert-child!` is a second node on screen."
  [log]
  {:creates (count (filter #(= :create-element (:op %)) @log))
   :inserts (count (filter #(= :insert-child (:op %)) @log))})

;; =============================================================================
;; 1. The unit-level property, on the reconcilers themselves
;; =============================================================================
;;
;; This one does not need the engine at all, and it states the mechanism in the
;; smallest possible form: reconciling twice against an UNADVANCED baseline
;; emits the delta twice; advancing the baseline as part of the first
;; reconciliation makes the second a no-op. Everything below is this property
;; wearing more machinery.

(deftest reconciling-twice-against-one-baseline-emits-twice
  (testing "attrs: the shape of the duplication, in isolation"
    (let [committed {:class "editor"}
          built     {:class "editor readonly"}
          twice     [(cache/reconcile-attrs committed built)
                     (cache/reconcile-attrs committed built)]]
      (is (= 1 (count (first twice))))
      (is (= 1 (count (second twice)))
          "against an unadvanced baseline, the second execution re-emits")
      ;; and the property the fix must establish:
      (is (empty? (cache/reconcile-attrs built built))
          "against an ADVANCED baseline, the second execution is a no-op")))

  (testing "children: the same shape for a conditional child appearing"
    (let [collapsed [{:type :nil :value nil}]
          child     {:tag :div :addr :el-items}
          r1        (cache/reconcile-children collapsed [child])
          r2        (cache/reconcile-children collapsed [child])]
      (is (= 1 (count (:deltas r1))))
      (is (= 1 (count (:deltas r2)))
          "unadvanced baseline re-emits the :add — this is the 9 -> 15")
      (is (empty? (:deltas (cache/reconcile-children (:slots r1) [child])))
          "advanced baseline emits nothing"))))

;; =============================================================================
;; NOT YET REPRODUCED end-to-end — read before trying again
;; =============================================================================
;;
;; The browser duplicates reliably: collapsing and re-expanding simmis's sidebar
;; Memory section goes 9 -> 15 `.nav-section-items` on 0.1.38 and stays at 9 on
;; 0.1.37. Two harness fixtures FAILED to reproduce it, both passing on the
;; buggy version:
;;
;;   1. conditional child = an awaited plain child spin
;;   2. conditional child = an awaited `ifor-each` whose render-fn returns spins
;;      (the literal shape of nav.cljc:735) — mount 8 creates, 3 collapse/expand
;;      cycles reached 29 against a 32 budget, i.e. no duplication
;;
;;   3. item-identity-changing `ifor-each` (expansion state assoc'd INTO the
;;      item, per sharp-edge #2, so the per-key memo misses and every section
;;      re-renders) + two async levels + toggling WITHOUT draining between, so
;;      an expand supersedes an in-flight collapse
;;
;; Attempt 3 was aimed by browser instrumentation, which had measured the
;; missing ingredient directly: ONE expand ran 18 element builds and 56
;; discharges, and the SAME address appeared twice in the build log. It still
;; did not reproduce, and it failed in a way worth recording:
;;
;;   the op log came out BYTE-IDENTICAL on pre-R3 (f9dc70e~1) and R3
;;   — same 36 creates / 30 set-attrs / 33 appends / 6 inserts on both.
;;
;; Identical logs mean the fixture never exercises the staging-vs-direct-write
;; distinction at all: every tree it builds eventually commits, so where the
;; cache write happens cannot matter. The harness itself CAN discriminate the
;; two versions — `superseded_run_test` fails 3/3 on pre-R3 and passes on R3 —
;; so this is the fixture's shape, not a limitation of the runner.
;;
;; THE HARNESS CANNOT ANSWER "WHAT IS ON SCREEN". `MockDischarge/remove-child!`
;; is INDEX-addressed and `child-index-of` returns nil (documented in the mock:
;; it has no DOM), so a removal cannot be attributed to a node. Replaying the op
;; log into a tree and counting nodes reachable from the root — the harness
;; equivalent of `querySelectorAll`, and the metric the browser used — reports
;; ZERO live containers for a clean, fully-drained expand that unquestionably
;; renders. Any duplication metric built on this log is unsound in BOTH
;; directions; op counts are the only trustworthy readout, and they cannot
;; express "9 became 15".
;;
;; So a faithful final-state harness (jsdom-backed, asserting on a real tree)
;; is not an optional nicety for this bug — it is a PREREQUISITE for acceptance.
;; Candidate still untried under the current harness:
;;   - driving through the real render effect rather than a mock discharge
;;
;; Until then, `toggled-*` acceptance for the repeat case does NOT exist, and
;; any claim that a fix is a "strict improvement" rests on the unit property
;; above plus a browser check — not on this suite.
