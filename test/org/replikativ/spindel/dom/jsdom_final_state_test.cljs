(ns org.replikativ.spindel.dom.jsdom-final-state-test
  "Assertions on the REAL tree: what is on screen after the toggles settle.

   Why this namespace exists. The JVM harness asserts on `MockDischarge`'s op
   log, and that log cannot answer \"what is attached\": `remove-child!` is
   INDEX-addressed and `child-index-of` returns nil (the mock has no DOM), so
   `apply-seq-diff!` silently falls back to offset 0. Replaying the log into a
   tree and counting reachable nodes — the obvious workaround — reports ZERO
   live containers for a clean, fully-drained expand that unquestionably
   renders. Op counts are the only trustworthy readout there, and they cannot
   express the defect we are chasing, which is stated as a NODE COUNT:
   collapsing and re-expanding a sidebar section in simmis went 9 -> 15.

   Here the discharge is `dom/browser`'s real `DOMDischarge` over a jsdom
   document, so `child-index-of` is real, fragment offsets are real, and the
   assertion is a `querySelectorAll` — the same measurement taken in Chrome.

   Coordination note: CLJS is single-threaded, so `await-drain` (which blocks)
   is JVM-only — a synchronous wait cannot observe `setTimeout`. Awaiting a
   `comb/sleep` is the only way to yield to the event loop, and it is how the
   engine's own async ops resolve. That is coordination, not a timing patch:
   the fixture's own children resolve through the same mechanism."
  (:refer-clojure :exclude [await])
  (:require [cljs.test :refer-macros [is testing use-fixtures]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.browser :as browser]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.spin.cps :refer-macros [spin]]
            [org.replikativ.spindel.test-async :refer [<?] :refer-macros [deftest-async <?]]
            ["jsdom" :refer [JSDOM]]))

(def ^:private current-test-ctx (atom nil))

(use-fixtures :each
  {:before (fn [] (let [c (ctx/create-execution-context)]
                    (reset! current-test-ctx c)
                    (set! ec/*execution-context* c)))
   :after  (fn [] (when-let [c @current-test-ctx]
                    (ctx/stop-context! c)
                    (set! ec/*execution-context* nil)
                    (reset! current-test-ctx nil)))})

(defn- fresh-body []
  (let [dom (JSDOM. "<!DOCTYPE html><html><body></body></html>")]
    (.-body (.-document (.-window dom)))))

(defn- n-matching
  "How many nodes match `sel` — the harness equivalent of the browser count."
  [body sel]
  (.-length (.querySelectorAll body sel)))

;; =============================================================================
;; 0. The harness proves itself before it is trusted
;; =============================================================================
;;
;; The JVM replay metric FAILED exactly here — it reported 0 for a state that
;; definitely renders. Any final-state harness must pass this before its
;; verdict on the interesting case means anything.

(deftest-async harness-reports-what-is-actually-on-screen
  (testing "a clean expand and collapse, fully settled between"
    (let [body (fresh-body)
          discharge (browser/make-dom-discharge (.-ownerDocument body))
          open? (sig/signal false)
          root (spin
                (let [{o :new} (track open?)]
                  (el/div {:class "shell"}
                          (when o
                            (el/ul {:class "section-items"}
                                   (el/li "one"))))))]
      (render/render-spin! body root discharge)
      (<? (comb/sleep 50))
      (is (= 0 (n-matching body ".section-items")) "collapsed at mount")
      (reset! open? true)
      (<? (comb/sleep 50))
      (is (= 1 (n-matching body ".section-items"))
          "expanded: exactly one container is on screen")
      (reset! open? false)
      (<? (comb/sleep 50))
      (is (= 0 (n-matching body ".section-items"))
          "collapsed again: the container is gone"))))

;; =============================================================================
;; 1. A duplication bug, stated as a node count — MEASURED, both versions
;; =============================================================================
;;
;; The shape the browser duplicates on: expansion state lives IN the ifor-each
;; item (sharp-edge #2 forces this — closure variables are invisible to the
;; diff), so toggling one section changes that item's value and every section
;; re-renders.
;;
;; What these two tests establish, on a real jsdom tree:
;;
;;   in-flight toggles : 6 sections become 12, and 2 containers remain
;;   SETTLED toggles   : mount 6 ok; settled EXPAND 6 + 1 container ok;
;;                       settled COLLAPSE -> 12 sections, container NOT removed
;;
;; So the race is NOT required. A single fully-settled collapse duplicates the
;; fragment. And the numbers are IDENTICAL on pre-R3 (f9dc70e~1) and on R3, so
;; this is NOT the R3 staging regression — it is an older, independent defect
;; in the ifor-each collapse path that both releases carry.
;;
;; That also means it is a candidate explanation for the duplications seen in
;; simmis before R3 ever existed. It does NOT explain the 0.1.37-vs-0.1.38 A/B
;; measured in Chrome (9 stays 9 / 9 becomes 15); that difference is still
;; unaccounted for, and may be a second mechanism layered on this one.
;;
;; These tests FAIL on both versions today. They are the acceptance criterion
;; for the fix, not a description of working behaviour.

(deftest-async collapse-expand-in-flight-does-not-duplicate
  (testing "after in-flight collapse/expand cycles, exactly one items
            container is on screen"
    (let [body (fresh-body)
          discharge (browser/make-dom-discharge (.-ownerDocument body))
          open-set (sig/signal #{})
          ids ["a" "b" "c" "d" "e" "f"]
          section-fn (fn [{:keys [id open?]}]
                       (spin
                        (await (comb/sleep 1))
                        (el/div {:key id :class "section"}
                                (when open?
                                  (el/ul {:class "section-items"}
                                         (el/li "one")
                                         (el/li "two"))))))
          root (spin
                (let [{os :new} (track open-set)
                      frag (await (foreach/for-each*
                                   {:file "jsdom-final-state" :line 1 :column 1}
                                   :id section-fn
                                   (mapv (fn [id] {:id id
                                                   :open? (contains? os id)})
                                         ids)))]
                  (el/nav {:class "shell"} frag)))]
      (render/render-spin! body root discharge)
      (<? (comb/sleep 100))
      (is (= 0 (n-matching body ".section-items")) "nothing expanded at mount")
      (is (= 6 (n-matching body ".section")) "all sections mounted")
      ;; Expand / collapse / expand with no settle in between, three times.
      (<? (comb/sleep 1))
      (reset! open-set #{"c"})
      (<? (comb/sleep 1))
      (reset! open-set #{})
      (<? (comb/sleep 1))
      (reset! open-set #{"c"})
      (<? (comb/sleep 150))
      (reset! open-set #{})
      (<? (comb/sleep 1))
      (reset! open-set #{"c"})
      (<? (comb/sleep 150))
      (reset! open-set #{})
      (<? (comb/sleep 1))
      (reset! open-set #{"c"})
      (<? (comb/sleep 300))
      (is (= 6 (n-matching body ".section"))
          (str "the section list must not grow, got "
               (n-matching body ".section")))
      (is (= 1 (n-matching body ".section-items"))
          (str "exactly one items container may be on screen, got "
               (n-matching body ".section-items"))))))

;; Is the in-flight race required, or does the same shape duplicate even when
;; every toggle is allowed to settle? This separates "supersession mishandled"
;; from "ifor-each re-render duplicates" — a much wider defect.

(deftest-async collapse-expand-settled-does-not-duplicate
  (testing "same shape, every toggle fully settled"
    (let [body (fresh-body)
          discharge (browser/make-dom-discharge (.-ownerDocument body))
          open-set (sig/signal #{})
          ids ["a" "b" "c" "d" "e" "f"]
          section-fn (fn [{:keys [id open?]}]
                       (spin
                        (await (comb/sleep 1))
                        (el/div {:key id :class "section"}
                                (when open?
                                  (el/ul {:class "section-items"}
                                         (el/li "one")
                                         (el/li "two"))))))
          root (spin
                (let [{os :new} (track open-set)
                      frag (await (foreach/for-each*
                                   {:file "jsdom-settled" :line 1 :column 1}
                                   :id section-fn
                                   (mapv (fn [id] {:id id
                                                   :open? (contains? os id)})
                                         ids)))]
                  (el/nav {:class "shell"} frag)))]
      (render/render-spin! body root discharge)
      (<? (comb/sleep 200))
      (is (= 6 (n-matching body ".section")) "mount")
      (reset! open-set #{"c"})
      (<? (comb/sleep 300))
      (is (= 6 (n-matching body ".section")) "after settled expand")
      (is (= 1 (n-matching body ".section-items")) "one container open")
      (reset! open-set #{})
      (<? (comb/sleep 300))
      (is (= 6 (n-matching body ".section")) "after settled collapse")
      (is (= 0 (n-matching body ".section-items")) "container closed"))))

;; =============================================================================
;; 2. Isolation: is the root element PRESERVED across a re-render?
;; =============================================================================
;;
;; While diagnosing the above, `render-initial!` was observed minting a NEW
;; address for the root element on every re-render — the old one evicted, the
;; whole subtree rebuilt. That is what R1 ("identity is the address") forbids,
;; and rebuilding the world each render is also why so much churn reaches the
;; discharge layer.
;;
;; These two isolate the trigger. Both spins track the same signal and emit the
;; same element; they differ ONLY in whether an `await` sits between the track
;; and the element construction. Node identity is checked directly: a property
;; stamped on the mounted node survives iff the node was reconciled in place.

(defn- stamp! [el] (set! (.-__spindelMark el) "kept") el)
(defn- kept? [el] (= "kept" (.-__spindelMark el)))

(deftest-async element-identity-survives-rerender-without-await
  (testing "track -> element, no await between"
    (let [body (fresh-body)
          discharge (browser/make-dom-discharge (.-ownerDocument body))
          n (sig/signal 0)
          root (spin
                (let [{v :new} (track n)]
                  (el/div {:class "root"} (el/span (str "n=" v)))))]
      (render/render-spin! body root discharge)
      (<? (comb/sleep 50))
      (stamp! (.querySelector body ".root"))
      (reset! n 1)
      (<? (comb/sleep 100))
      (is (= 1 (n-matching body ".root")) "exactly one root")
      (is (kept? (.querySelector body ".root"))
          "the root node must be reconciled in place, not recreated"))))

(deftest-async element-identity-survives-rerender-with-await
  (testing "track -> await -> element (the shape the nav uses)"
    (let [body (fresh-body)
          discharge (browser/make-dom-discharge (.-ownerDocument body))
          n (sig/signal 0)
          root (spin
                (let [{v :new} (track n)
                      _ (await (comb/sleep 1))]
                  (el/div {:class "root"} (el/span (str "n=" v)))))]
      (render/render-spin! body root discharge)
      (<? (comb/sleep 100))
      (stamp! (.querySelector body ".root"))
      (reset! n 1)
      (<? (comb/sleep 200))
      (is (= 1 (n-matching body ".root")) "exactly one root")
      (is (kept? (.querySelector body ".root"))
          "an await between track and element must not change the address"))))

;; =============================================================================
;; 3. OPEN, SEPARATE DEFECT: the fragment's parent is re-minted each re-render
;; =============================================================================
;;
;; Found while diagnosing the eviction bug, and NOT fixed by it. Probing
;; `render-initial!` showed the nav getting a NEW address on every re-render:
;;
;;   mount   nav :el-12707852...
;;   expand  nav :el-17fec733...   <- re-minted, whole subtree rebuilt
;;
;; R1 says identity IS the address, so a stable call site must keep its
;; address; re-minting rebuilds the world on every render. The two tests above
;; isolate the trigger: `track -> await -> element` preserves node identity
;; (both pass), so neither the await nor the track is at fault on its own. It
;; is the awaited ifor-each FRAGMENT child that destabilises the parent.
;;
;; ROOT CAUSE, measured. The address is
;; `content-hash[source-loc, parent-addr, slot-index]`. Probing all three at the
;; nav's construction, across two renders:
;;
;;   render 1  parent=:keyed-0435e69b  slot=0  chain=:spin-07ecfb2e  (item c)
;;   render 2  parent=:keyed-1653f3a8  slot=0  chain=:spin-07ecfb2e  (item b)
;;
;; slot and the spin chain-head are STABLE. The parent is not — and it is a
;; `:keyed-...` address, i.e. an `ifor-each` ITEM's scope. The outer body's
;; element is being addressed as though it lived inside one of the fragment's
;; items, and WHICH item varies per render (c, then b). That nondeterminism is
;; the instability. The per-item keyed addresses are themselves stable
;; (`:keyed-0435e69b` is item c in both renders), so item addressing is fine.
;;
;; The mechanism: `with-keyed-context-fn` installs `:dom/parent-addr` with a
;; synchronous `binding` around a thunk that only STARTS async work — the item
;; render-fn returns a spin, so the `finally` fires immediately (the ENTER/EXIT
;; pairs all print during the synchronous kick-off, before any item body
;; resolves). The scope therefore does not track the item's continuation, and
;; when the parent body resumes from `(await (for-each* ...))` it inherits the
;; ambient context left by whichever item continuation resumed last.
;;
;; This is why the two tests above pass: with no fragment there is no keyed
;; scope to leak, so `track -> await -> element` is stable.
;;
;; The fix must make the keyed scope part of the item spin's captured context
;; (re-established per continuation, torn down when it completes) rather than a
;; synchronous dynamic binding, and/or have a resuming body restore its OWN dom
;; bindings instead of inheriting ambient ones. That is engine-level and
;; deserves its own change; the eviction fix above is independent of it and
;; complete on its own.
;;
;; This test FAILS. It is the acceptance criterion for that follow-up.

(deftest-async fragment-parent-keeps-its-identity-across-rerender
  (testing "a parent whose child is an awaited ifor-each fragment must be
            reconciled in place, not re-created"
    (let [body (fresh-body)
          discharge (browser/make-dom-discharge (.-ownerDocument body))
          open-set (sig/signal #{})
          ids ["a" "b" "c"]
          section-fn (fn [{:keys [id open?]}]
                       (spin
                        (await (comb/sleep 1))
                        (el/div {:key id :class "section"}
                                (when open? (el/ul {:class "section-items"})))))
          root (spin
                (let [{os :new} (track open-set)
                      frag (await (foreach/for-each*
                                   {:file "jsdom-identity" :line 1 :column 1}
                                   :id section-fn
                                   (mapv (fn [id] {:id id
                                                   :open? (contains? os id)})
                                         ids)))]
                  (el/nav {:class "shell"} frag)))]
      (render/render-spin! body root discharge)
      (<? (comb/sleep 200))
      (is (= 3 (n-matching body ".section")) "mounted")
      (stamp! (.querySelector body ".shell"))
      (reset! open-set #{"b"})
      (<? (comb/sleep 300))
      (is (= 3 (n-matching body ".section")) "still three sections")
      (is (kept? (.querySelector body ".shell"))
          "R1: the nav's address must be stable across re-renders"))))
