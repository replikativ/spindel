(ns org.replikativ.spindel.dom.differential-fuzz-regressions-test
  "Minimal cases found by the differential DOM fuzzer
   (`differential_fuzz_test.cljs`), pinned on a real jsdom tree.

   Defect 1 is FIXED; its tests assert the correct behaviour. Each other
   defect below is OPEN. Its test is a strict expected-failure: it
   asserts the defect still reproduces, so the suite stays green while it is
   open AND turns red the moment a change fixes it — at which point the
   assertion is flipped to the correct-behaviour one (already written next
   to it). Run them asserting correct behaviour with

     SPINDEL_EXPECT_FIXED=1 node target/dom-fuzz.js

   Every defect is stated twice: as hand-written spindel code (the readable
   repro) and as the fuzzer's minimal case replayed through the same
   oracle (`run-case`)."
  (:refer-clojure :exclude [await])
  (:require [cljs.test :refer-macros [deftest is async]]
            [org.replikativ.spindel.dom.browser :as browser]
            [org.replikativ.spindel.dom.differential-fuzz-harness :as h]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer-macros [spin]]
            [org.replikativ.spindel.spin.sync :as sync])
  (:require-macros [org.replikativ.spindel.dom.foreach :refer [ifor-each]]
                   [org.replikativ.spindel.signal]))

(def ^:private expect-fixed?
  (= "1" (some-> js/process .-env (aget "SPINDEL_EXPECT_FIXED"))))

(defn- known-defect
  "Assert `observed` against `correct`: equal under SPINDEL_EXPECT_FIXED=1,
   otherwise still DIFFERENT (strict expected-failure)."
  [observed correct note]
  (if expect-fixed?
    (is (= correct observed) note)
    (is (not= correct observed)
        (str "KNOWN DEFECT no longer reproduces — it looks fixed. Flip this "
             "test to assert the correct behaviour (SPINDEL_EXPECT_FIXED=1 "
             "shows it passing). " note))))

(defn- known-defect-case
  "The fuzzer's minimal case through the oracle: fails while the defect is
   open, passes once it is fixed."
  [fuzz-case done]
  (let [saved ec/*execution-context*]
    (.then (h/run-case fuzz-case)
           (fn [r]
             (set! ec/*execution-context* saved)
             (if expect-fixed?
               (is (:pass? r) (pr-str (:failures r)))
               (is (not (:pass? r))
                   "KNOWN DEFECT no longer reproduces through the oracle — flip this test"))
             (done)))))

(defn- fixed-case
  "A fuzzer minimal case of a FIXED defect through the oracle: must pass."
  [fuzz-case done]
  (let [saved ec/*execution-context*]
    (.then (h/run-case fuzz-case)
           (fn [r]
             (set! ec/*execution-context* saved)
             (is (:pass? r) (pr-str (:failures r)))
             (done)))))

(defn- scenario
  "Mount `(make-root ctx)` on a fresh jsdom body; run each step of `steps`
   (fns of no args) to quiescence. Resolves to the body's innerHTML."
  [make-root steps]
  (let [restore-logs! (h/quiet-logs!)
        c (ctx/create-execution-context)
        _ (set! ec/*execution-context* c)
        body (h/fresh-body)
        root (make-root c)]
    (render/render-spin! body root (browser/make-dom-discharge (.-ownerDocument body)))
    (-> (reduce (fn [p step] (.then p (fn [_] (step) (h/settle! c))))
                (h/settle! c)
                steps)
        (.then (fn [_]
                 (let [html (.-innerHTML body)]
                   (ctx/stop-context! c)
                   (h/release-containers!)
                   (set! ec/*execution-context* nil)
                   (restore-logs!)
                   html))))))

;; =============================================================================
;; Defect 1 (FIXED) — a superseded slice completed CLEAN and was served
;; =============================================================================
;;
;; Shape: a parent tracks signal A and renders an async ifor-each whose items
;; are spins that ALSO track A and then await a deferred (track at the top,
;; then await — the documented shape). Prepend an item while the items are
;; suspended on the deferred, then deliver it.
;;
;;   expected  <li>1:2</li><li>0:2</li>      (both items see 2 entries)
;;   was       <li>1:2</li><li>0:1</li>      (item 0 rendered from the OLD A)
;;
;; Mechanism (engine-state probes): `:signal-change` filtered item 0 out as
;; a DESCENDANT observer (its parent re-creates it) and did nothing else to
;; it — it stayed :clean with its await on the deferred intact. Its
;; freshness relied on the parent's re-run reaching it inside the batch,
;; where the await fast path is off; but the parent's for-each awaited the
;; new item 1 first and suspended. The delivery then completed item 0's
;; superseded run, `cache-result!` certified it :clean, and the parent's
;; later re-registration (same id, identical captures — a B-gate no-op)
;; served it. The second case below is the B-gate variant: an element
;; spin re-registered with CHANGED captures while running, whose old run
;; completed first and cleaned the node the B-gate had dirtied.
;;
;; Fix (formalism §3.4, "no stale certification"): a filtered descendant is
;; invalidated at the change, and a run invalidated while in flight is
;; marked `:stale-run?`, so its completion leaves the node :dirty
;; (`simple/invalidate-node`, `cache-result!`). Engine-level regression:
;; `engine/stale_run_test.cljc`.

(defn- defect-1-root [a d]
  (spin (let [{v :new} (track a)]
          (el/ul {:class "root"}
                 (await (ifor-each :id (:xs v)
                                   (fn [item]
                                     (spin (let [{s :new} (track a)
                                                 _ (await d)]
                                             (el/li {:key (:id item)}
                                                    (str (:id item) ":" (count (:xs s)))))))))))))

(deftest defect-1-superseded-slice-not-served-from-cache
  (async done
         (let [a (atom nil) d (atom nil)]
           (-> (scenario (fn [c]
                           (reset! a (sig/signal c {:xs [{:id 0}]}))
                           (reset! d (sync/create-deferred c))
                           (defect-1-root @a @d))
                         [#(swap! @a update :xs (fn [xs] (into [{:id 1}] xs)))
                          #(sync/deliver! @d :go)])
               (.then (fn [html]
                        (is (= "<ul class=\"root\"><li>1:2</li><li>0:2</li></ul>" html)
                            "item 0 must render the A value current at quiescence")
                        (done)))))))

(deftest defect-1-fuzzer-minimal-case
  (async done
         (fixed-case
          {:program {:op :spin :tracks [0] :dfr nil
                     :body {:op :for :sig 0 :key? false
                            :item {:op :el :tag :div :attr nil
                                   :children [{:op :spin :tracks [0] :dfr 0
                                               :body {:op :for :sig 0 :key? false
                                                      :item {:op :text :kind :lit :ref 0}}}]}}}
           :init [{:b false :n 0 :xs [{:id 0 :v 0}]}
                  {:b false :n 0 :xs []}
                  {:b false :n 0 :xs []}]
           :ops [[:ins 0 1 0 0]]}
          done)))

;; Nested: the same shape one level down, with a prepend at BOTH levels in
;; one change. Groups are spins that track A and render an inner ifor-each
;; of items that track A and await the deferred.

(defn- defect-1-nested-root [a d]
  (spin (let [{v :new} (track a)]
          (el/div {:class "root"}
                  (await (ifor-each :id (:groups v)
                                    (fn [g]
                                      (spin (let [{_ :new} (track a)]
                                              (el/section {:key (:id g)}
                                                          (await (ifor-each :id (:items g)
                                                                            (fn [item]
                                                                              (spin (let [{s :new} (track a)
                                                                                          _ (await d)]
                                                                                      (el/i {:key (:id item)}
                                                                                            (str (:id g) "." (:id item) ":"
                                                                                                 (count (:groups s)))))))))))))))))))

(deftest defect-1-nested-prepend-at-both-levels
  (async done
         (let [a (atom nil) d (atom nil)]
           (-> (scenario (fn [c]
                           (reset! a (sig/signal c {:groups [{:id 0 :items [{:id 0}]}]}))
                           (reset! d (sync/create-deferred c))
                           (defect-1-nested-root @a @d))
                         [#(swap! @a (fn [m]
                                       {:groups [{:id 1 :items [{:id 0}]}
                                                 {:id 0 :items [{:id 1} {:id 0}]}]}))
                          #(sync/deliver! @d :go)])
               (.then (fn [html]
                        (is (= (str "<div class=\"root\">"
                                    "<section><i>1.0:2</i></section>"
                                    "<section><i>0.1:2</i><i>0.0:2</i></section>"
                                    "</div>")
                               html)
                            "every item renders the A current at quiescence")
                        (done)))))))

;; Removal in the same change, then re-adding the removed item: a removed
;; descendant is invalidated and never re-created; re-adding it must re-run
;; it rather than serve its pre-removal result.

(defn- removal-scenario [steps]
  (let [a (atom nil) d (atom nil)]
    (scenario (fn [c]
                (reset! a (sig/signal c {:xs [{:id 0} {:id 1}]}))
                (reset! d (sync/create-deferred c))
                (defect-1-root @a @d))
              (mapv (fn [step] #(step @a @d)) steps))))

(deftest defect-1-removal-in-the-change
  (async done
         (-> (removal-scenario [(fn [a _] (swap! a assoc :xs [{:id 1}]))
                                (fn [_ d] (sync/deliver! d :go))])
             (.then (fn [html]
                      (is (= "<ul class=\"root\"><li>1:1</li></ul>" html)
                          "the removed item is gone, the kept one is current")
                      (done))))))

(deftest defect-1-removal-then-re-add
  (async done
         (-> (removal-scenario [(fn [a _] (swap! a assoc :xs [{:id 1}]))
                                (fn [_ d] (sync/deliver! d :go))
                                (fn [a _] (swap! a assoc :xs [{:id 0} {:id 1}]))])
             (.then (fn [html]
                      (is (= "<ul class=\"root\"><li>0:2</li><li>1:2</li></ul>" html)
                          "the re-added item re-runs against the current A")
                      (done))))))

;; The superseded slice need not be the tracking spin itself. Here the item's
;; element is built in a spin (an await sits in a sibling slot): slot 0
;; embeds a nested spin that tracks A, slot 1 awaits the deferred. A flip of
;; A plus a move suspends the re-run behind the earlier item; the element's
;; old slice — holding slot 0's PRE-flip vnode — completes on delivery and
;; is served from cache (`title` stays at the old value for item 0 only).

(deftest defect-1-fuzzer-case-stale-sibling-slot
  (async done
         (fixed-case
          {:program {:op :spin :tracks [0] :dfr nil
                     :body {:op :for :sig 0 :key? false
                            :item {:op :el :tag :div :attr nil
                                   :children [{:op :el :tag :div :attr nil
                                               :children [{:op :spin :tracks [0] :dfr nil
                                                           :body {:op :el :tag :div :attr [:sig 0] :children []}}
                                                          {:op :spin :tracks [] :dfr 0
                                                           :body {:op :text :kind :lit :ref 0}}]}
                                              {:op :text :kind :lit :ref 0}]}}}
           :init [{:b false :n 0 :xs [{:id 0 :v 0} {:id 1 :v 0}]}
                  {:b false :n 0 :xs []}
                  {:b false :n 0 :xs []}]
           :ops [[:flip 0] [:move 0 0 3]]}
          done)))

;; =============================================================================
;; Defect 2 — ifor-each items without :key: updates silently corrupt the list
;; =============================================================================
;;
;; OUTSIDE the documented contract (docs/api-reference.md: `:key` is "stable
;; identity within an ifor-each fragment") but silent, and the `render.cljc`
;; namespace docstring's own example omits it:
;;
;;   (ifor-each :id new (fn [todo] (el/li (:text todo))))
;;
;; Measured on jsdom, item roots without `:key`:
;;
;;   [0]   -> [1 0]   renders NOTHING (both items gone)
;;   [0]   -> [0 1]   renders nothing
;;   [0 1] -> [1 0]   renders k0 k1 k0 (duplicate)
;;   [0 1] -> [1]     unchanged k0 k1 (removal lost)
;;
;; With `:key (:id item)` on the item root every case is correct.
;;
;; Mechanism: the commit layer orders a fragment by its item VNODES' `:key`
;; (`commit.cljc` `fragment-order+by-key`: `(mapv :key items)`), i.e. by the
;; element attribute, not by the ifor-each key-fn the items were built
;; under. Without the attribute every item's key is nil: `order` is
;; `[nil nil]`, `by-key` collapses to one entry, and `keyed-seq-diff` diffs
;; garbage. The key-fn's keys exist at build time (`for-each*`'s
;; `resolved-items` carry `:key`) but are not put on the fragment. Carrying
;; them (or stamping the key onto the item vnode) would make the attribute
;; unnecessary; failing loudly on a nil item key would at least make the
;; contract visible.

(defn- defect-2-root [xs]
  (spin (let [{v :new} (track xs)]
          (el/div {:class "root"}
                  (ifor-each :id v (fn [item] (el/div {:class "item"} (str "k" (:id item)))))))))

(deftest defect-2-unkeyed-items-prepend
  (async done
         (let [xs (atom nil)]
           (-> (scenario (fn [c]
                           (reset! xs (sig/signal c [{:id 0}]))
                           (defect-2-root @xs))
                         [#(reset! @xs [{:id 1} {:id 0}])])
               (.then (fn [html]
                        (known-defect html
                                      "<div class=\"root\"><div class=\"item\">k1</div><div class=\"item\">k0</div></div>"
                                      "an unkeyed item root must still follow the ifor-each key-fn")
                        (done)))))))

(deftest defect-2-fuzzer-minimal-case
  (async done
         (known-defect-case
          {:program {:op :spin :tracks [0] :dfr nil
                     :body {:op :for :sig 0 :key? false
                            :item {:op :text :kind :lit :ref 0}}}
           :init [{:b false :n 0 :xs [{:id 0 :v 0}]}
                  {:b false :n 0 :xs []}
                  {:b false :n 0 :xs []}]
           :ops [[:ins 0 1 0 0]]
           :profile #{:unkeyed}}
          done)))

;; =============================================================================
;; Defect 3 — a fragment beside a sibling grows from EMPTY at the wrong index
;; =============================================================================
;;
;; `apply-seq-diff!` documents fragment offsets ("rendered alongside sibling
;; elements (a heading above, a footer below) ... the offset is derived once
;; at entry from the first prev-vnode's DOM element position"), and the
;; api-reference still prescribes the sole-child wrapping rule. The gap the
;; fuzzer found: with NO prev-vnode — the fragment was empty — the offset
;; falls back to 0, so the first grown items are inserted BEFORE the
;; preceding sibling:
;;
;;   (el/div "head" (ifor-each :id xs …))    xs: [] -> [{:id 0}]
;;   expected  <div>head<div>k0</div></div>
;;   actual    <div><div>k0</div>head</div>
;;
;; (`fragment-offset` in dom/discharge.cljc.) A fresh mount of the same
;; state is correct; only the empty -> non-empty transition misplaces. The
;; fragment's start is still derivable without a prev element — from the
;; slot structure (the count of DOM nodes the preceding slots flattened to),
;; which `build-element` already keeps as `:slots`.

(defn- defect-3-root [xs]
  (spin (let [{v :new} (track xs)]
          (el/div {:class "root"}
                  "head"
                  (ifor-each :id v (fn [item]
                                     (el/div {:key (:id item) :class "item"}
                                             (str "k" (:id item)))))))))

(deftest defect-3-empty-fragment-beside-sibling-grows-at-index-0
  (async done
         (let [xs (atom nil)]
           (-> (scenario (fn [c]
                           (reset! xs (sig/signal c []))
                           (defect-3-root @xs))
                         [#(reset! @xs [{:id 0}])])
               (.then (fn [html]
                        (known-defect html
                                      "<div class=\"root\">head<div class=\"item\">k0</div></div>"
                                      "grown items belong after the sibling that precedes the fragment")
                        (done)))))))

(deftest defect-3-fuzzer-minimal-case
  (async done
         (known-defect-case
          {:program {:op :spin :tracks [0] :dfr nil
                     :body {:op :el :tag :div :attr nil
                            :children [{:op :text :kind :lit :ref 0}
                                       {:op :for :sig 0 :key? false
                                        :item {:op :text :kind :lit :ref 0}}]}}
           :init [{:b false :n 0 :xs []}
                  {:b false :n 0 :xs []}
                  {:b false :n 0 :xs []}]
           :ops [[:ins 0 0 0 0]]
           :profile #{:siblings}}
          done)))

;; =============================================================================
;; Defect 4 — a context that awaited a Deferred is never garbage-collected
;; =============================================================================
;;
;; Found while bounding the fuzzer's memory: every trial's contexts stayed
;; reachable after `stop-context!` (heap grew ~1.7 MB per trial with a jsdom
;; window per mount, ~0.2 MB with one shared document; a 2 GB node heap ran
;; out). The retainer path from a dead trial's DOM container to a GC root:
;;
;;   container <- render-spin! resolve closure <- cont in the context's state
;;   <- backend state-atom <- held value {:atom-id :runtime} of
;;   `atom-finalization-registry` (org.replikativ.spindel.atom) <- global
;;
;; `create-atom` registers each RuntimeAtom with a FinalizationRegistry
;; (CLJS) / Cleaner (JVM) whose HELD VALUE / cleaning action strongly
;; references the creating `runtime`. Both APIs require the opposite: the
;; registry keeps the held value alive until the target is collected, so if
;; the target is reachable from the held value, it never is. Here the
;; context's state reaches the RuntimeAtom (a Deferred's state atom, captured
;; by the spin that awaits it), so the atom, the whole context, and
;; everything its continuations close over (DOM containers, discharges) are
;; pinned for the life of the process. The cleanup action needs a weak path
;; to the runtime's state (and must survive the context RECORD being
;; re-created by `assoc` while its backend lives).
;;
;; Runs only when node exposes `gc` (`node --expose-gc target/dom-fuzz.js`);
;; otherwise it is skipped (no assertion). The control (a context with no
;; runtime atom) must be collected, or the measurement is inconclusive.

(defn- collected?
  "Resolve to whether the context made by `setup!` is collected after
   `stop-context!` and two GC passes separated by event-loop turns (WeakRefs
   clear only between turns)."
  [setup!]
  (let [ref (let [c (ctx/create-execution-context)]
              (set! ec/*execution-context* c)
              (setup! c)
              (ctx/stop-context! c)
              (set! ec/*execution-context* nil)
              (js/WeakRef. (:backend c)))
        turn #(js/Promise. (fn [r _] (js/setTimeout r 0)))]
    (-> (turn)
        (.then (fn [_] (js/gc) (turn)))
        (.then (fn [_] (js/gc) (turn)))
        (.then (fn [_] (nil? (.deref ref)))))))

(deftest defect-4-context-pinned-by-atom-finalization-registry
  (async done
         (if-not (exists? js/gc)
           (done)
           (let [restore-logs! (h/quiet-logs!)]
             (-> (collected? (fn [_] nil))
                 (.then (fn [control]
                          (is control "control: a context without runtime atoms is collected")
                          (collected? (fn [c]
                                        (let [d (sync/create-deferred c)]
                                          ((spin (await d)) identity identity))))))
                 (.then (fn [awaited]
                          (restore-logs!)
                          (known-defect awaited true
                                        "a stopped context must be collectable once unreferenced")
                          (done))))))))
