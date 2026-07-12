(ns org.replikativ.spindel.dom.render
  "Reactive rendering - connects spindel's signal system to DOM.

  **Delta-Direct Rendering (New Model):**

  In the delta-direct model, there is no diffing:
  1. Elements are macros that capture source location
  2. Each element has a stable address (from source-loc + parent + slot)
  3. Elements cache their children by slot position
  4. On re-render, slot reconciliation produces deltas directly
  5. Deltas are discharged to the DOM without re-diffing

  The render! function:
  1. Executes a spin that produces vdom with deltas
  2. Mounts vdom to the DOM container (first render)
  3. Re-executes when tracked signals change
  4. Discharges deltas directly to the DOM (no diffing)

  Usage:
    (render! container
      (spin
        (let [{:keys [new]} (track todos)]
          (el/ul
            (ifor-each :id new
              (fn [todo] (el/li (:text todo))))))))

  The spin re-runs whenever tracked signals change. Element macros
  produce vnodes with deltas attached that are discharged to the DOM."
  (:require [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.engine.core :as ec]
            [replikativ.logging :as log]))

;; =============================================================================
;; Render State
;; =============================================================================

(defrecord RenderState
           [container       ; DOM container element
            discharge       ; Discharge implementation
            current-vdom    ; Current vdom tree (with deltas cleared)
            mounted?])      ; Whether initial mount has happened

;; =============================================================================
;; Render Cycle
;; =============================================================================

(defn ^:no-doc root-identity-changed?
  "True when the mounted root and the new root are not the same DOM node.

  Deltas are discharged against DOM elements bound by `:addr`, and the mounted
  root is the one node no parent slot can address. When a spin's body returns a
  different root element — a conditional at the TOP of a spin, e.g.
  `(if loading? (el/div …) (el/div …))` — the new root's addr has no element
  bound to it, so every delta beneath it targets a node that was never created
  and the whole render silently vanishes. Detect that and re-mount.

  Only element vnodes carry an `:addr`. Compare addrs when both have them,
  otherwise fall back to `:tag` so element↔text transitions also re-mount. A
  first render (no `current-vdom`) is not a change — `initial-mount!` owns it."
  [current-vdom new-vdom]
  (boolean
   (when (and current-vdom new-vdom)
     (let [ca (:addr current-vdom)
           na (:addr new-vdom)]
       (if (and ca na)
         (not= ca na)
         (not= (:tag current-vdom) (:tag new-vdom)))))))

(defn initial-mount!
  "Perform initial mount of vdom to container."
  [render-state vdom]
  (let [{:keys [container discharge]} render-state
        ;; Clear any existing content
        _ (when container
            (set! (.-innerHTML container) ""))
        ;; Render initial vdom
        root-el (binding [disch/*rendered-addrs* (atom {})]
                  (disch/render-initial! discharge vdom))
        ;; Clear deltas for next render cycle
        cleared-vdom (disch/clear-deltas-deep vdom)]
    ;; Append to container
    (when (and container root-el)
      (.appendChild container root-el))
    ;; No transfer needed — address-based refs work with cleared vdom
    ;; (clear-deltas-deep preserves :addr fields)
    (assoc render-state
           :current-vdom cleared-vdom
           :mounted? true)))

(defn update-render!
  "Apply vdom changes to DOM using delta-direct rendering.

  In the new model:
  1. Vnodes arrive with deltas already computed (from element* slot reconciliation)
  2. We collect all nodes with deltas
  3. We discharge deltas directly (no diffing)
  4. We clear deltas for next render cycle

  Uses *rendered-vnodes* to track vnodes that are fully rendered during
  this cycle. When a parent's :add delta triggers render-initial! for a child,
  the child vnode is marked as rendered. If the same child appears in the
  nodes-with-deltas list (because it had deltas from element* reconciliation
  against empty cache), discharge-vnode! will skip it to prevent double-rendering.

  DOM refs are stored by stable address (:addr on vnodes), so no transfer
  is needed between old and new vdom objects."
  [render-state new-vdom]
  (let [{:keys [container discharge current-vdom]} render-state]
    (cond
      ;; No new vdom. The root spin produced nothing this cycle: keep the last
      ;; frame rather than tearing the app down. A root that legitimately wants
      ;; to render nothing should return an empty element, not nil.
      (nil? new-vdom) render-state

      ;; The root element itself changed. Tear the old tree down properly, then
      ;; mount the new one — all inside ONE eviction pass, so that an address
      ;; the new tree re-claims (A→B→A) is spared by `(pending - live)`.
      (root-identity-changed? current-vdom new-vdom)
      (do
        (log/debug :render/root-replace {:old (:addr current-vdom)
                                         :new (:addr new-vdom)})
        (binding [disch/*rendered-vnodes* (atom #{})
                  disch/*rendered-addrs* (atom {})
                  disch/*pending-evictions* (atom #{})]
          ;; Refs get their nil call and caches are SCHEDULED (not yet dropped):
          ;; foreign nodes (TipTap et al.) rely on this to release resources.
          (disch/call-refs-on-unmount! current-vdom)
          (let [root-el (disch/render-initial! discharge new-vdom)]
            (when container
              (set! (.-innerHTML container) "")
              (when root-el (.appendChild container root-el))))
          (disch/flush-pending-evictions! discharge))
        (assoc render-state :current-vdom (disch/clear-deltas-deep new-vdom)))

      :else
      (do
        ;; Discharge deltas directly - no diffing needed
        ;; DOM refs found by address, no transfer needed
        (binding [disch/*rendered-vnodes* (atom #{})
                  disch/*rendered-addrs* (atom {})
                  disch/*pending-evictions* (atom #{})]
          (let [nodes-with-deltas (disch/collect-nodes-with-deltas new-vdom)]
            (when (seq nodes-with-deltas)
              (log/trace :render/delta-update {:nodes-with-deltas (count nodes-with-deltas)})
              (doseq [node nodes-with-deltas]
                (disch/discharge-vnode! discharge node))))
          (disch/flush-pending-evictions! discharge))

        ;; Clear deltas for next render cycle
        ;; No ref transfer needed — cleared vnodes carry same :addr values
        (let [cleared-vdom (disch/clear-deltas-deep new-vdom)]
          (assoc render-state :current-vdom cleared-vdom))))))

;; =============================================================================
;; Render! API
;; =============================================================================

#?(:cljs
   (defn make-render-state
     "Create render state for a container element."
     [container discharge-or-nil]
     (let [discharge (or discharge-or-nil
                         ;; Lazy require to avoid circular deps
                         (let [browser-ns (js/require "org.replikativ.spindel.dom.browser")]
                           ((.-make-dom-discharge browser-ns)
                            (.-ownerDocument container))))]
       (->RenderState container discharge nil false))))

(defn render-once!
  "Render vdom to container once (non-reactive).

  This is useful for static content or testing."
  [container vdom discharge]
  (let [state (->RenderState container discharge nil false)]
    (initial-mount! state vdom)))

(defn create-render-effect
  "Create a render effect function for use with spin completion callbacks.

  Returns a function that:
  - On first call: mounts vdom to container
  - On subsequent calls: discharges deltas to DOM (no diffing)

  The returned function should be called with the vdom result.

  Each render effect carries a long-lived `*applied-vnodes*` set that
  tracks vnode objects whose deltas have already been applied. This is
  what makes cached spin results safe to embed in a re-emitting parent:
  the same vnode object encountered in a later cycle is recognized and
  its deltas are not re-applied (which would duplicate children — the
  cross-spin reuse bug).

  Storage: a weak set (CLJ: `Collections/newSetFromMap` over
  `WeakHashMap`, wrapped in `synchronizedSet` to tolerate parallel
  signal-change drains; CLJS: `js/WeakSet`). Identity semantics — when
  a spin re-runs and produces a fresh cached result, the OLD vnode is
  no longer referenced via the spin's :result cache and the weak set
  lets it become GC-eligible rather than pinning it for the lifetime
  of the render effect (which would leak unboundedly in long-running
  apps)."
  [container discharge]
  (let [state-atom (atom (->RenderState container discharge nil false))
        applied    (disch/make-applied-vnodes)]
    (fn [vdom]
      (when vdom
        (let [state @state-atom
              has-deltas? (seq (:deltas vdom))]
          (log/debug ::render-effect-callback {:mounted? (:mounted? state)
                                               :vdom-tag (:tag vdom)
                                               :vdom-has-deltas? has-deltas?
                                               :vdom-deltas (:deltas vdom)})
          (binding [disch/*applied-vnodes* applied]
            (if (:mounted? state)
              ;; Update with delta-direct rendering
              (swap! state-atom update-render! vdom)
              ;; Initial mount
              (reset! state-atom (initial-mount! state vdom)))))))))

;; =============================================================================
;; Integration with Spin System
;; =============================================================================

#?(:cljs
   (defn- clear-render-error-overlay! [container]
     (when-let [el (.querySelector container "[data-spindel-render-error]")]
       (.remove el))))

#?(:cljs
   (defn- show-render-error-overlay!
     "Dev-only (goog.DEBUG) visible surface for a REJECTED render spin.
      Without it, a body exception cascades monadically to the root and
      the UI freezes at the last resolved frame with a single log line —
      practically invisible. Updated in place on repeated rejects;
      removed on the next successful resolve."
     [container spin-id error]
     (when ^boolean js/goog.DEBUG
       (let [existing (.querySelector container "[data-spindel-render-error]")
             el (or existing (.createElement js/document "div"))
             msg (str (or (some-> error .-message) error))
             stack (or (some-> error .-stack) "")]
         (set! (.-cssText (.-style el))
               (str "position:fixed;left:8px;right:8px;bottom:8px;z-index:99999;"
                    "background:#3b0d0d;color:#ffb4b4;border:1px solid #a33;"
                    "border-radius:6px;padding:10px 14px;font:12px/1.5 monospace;"
                    "max-height:40vh;overflow:auto;white-space:pre-wrap;"))
         (.setAttribute el "data-spindel-render-error" "true")
         (set! (.-textContent el)
               (str "spindel render REJECTED — UI frozen at last resolved frame\n"
                    "spin: " spin-id "\n" msg
                    (when (seq stack) (str "\n\n" stack))))
         (when-not existing (.appendChild container el))))))

(defn render-spin!
  "Execute a spin and render its vdom result.

  The spin should return vdom with deltas (from element macros).
  When tracked signals change, the spin re-executes and the
  deltas are discharged directly to the DOM.

  Returns a map with:
    :stop!    - Function to stop reactive updates
    :state    - Atom containing render state

  Example:
    (render-spin! container
      (spin
        (let [{:keys [new]} (track items)]
          (el/ul
            (ifor-each :id new
              (fn [todo] (el/li (:text todo))))))))
  "
  [container the-spin discharge]
  (let [render-effect (create-render-effect container discharge)
        spin-id (spin-core/spin-id the-spin)
        ;; Capture the context so `:stop!` can cancel against it later, even
        ;; if the caller invokes it with no *execution-context* bound.
        ctx (try (ec/current-execution-context)
                 (catch #?(:clj Throwable :cljs :default) _ nil))]

    (log/debug :render/start {:spin-id spin-id})

    ;; Execute the spin - it will re-run when signals change
    ;; The completion callback renders the vdom
    (the-spin
      ;; resolve callback
     (fn [vdom]
       (log/trace :render/vdom-received {:spin-id spin-id :has-vdom (some? vdom)})
       #?(:cljs (clear-render-error-overlay! container))
       (render-effect vdom))
      ;; reject callback — a rejected render produces NO vdom: the whole
      ;; tree silently freezes at the last resolved frame (correct Result-
      ;; monad semantics, terrible observability — the sharp-edges 'silent
      ;; wrong behavior' pattern). In dev builds, surface it visibly.
     (fn [error]
       (log/error :render/error {:spin-id spin-id :error error})
       #?(:cljs (show-render-error-overlay! container spin-id error))))

    ;; Return control map
    {:spin-id spin-id
     :stop! (fn []
              (log/debug :render/stop {:spin-id spin-id})
              ;; Cancel the render spin: tears down its reactive continuations
              ;; and signal/spin dependency subscriptions so it stops
              ;; re-executing on signal changes, and lets the engine reclaim
              ;; its node + conts. Without this, a stopped render keeps its
              ;; reactive machinery (and the render-effect closure it resumes
              ;; into) alive for the lifetime of the context.
              (when ctx
                (binding [ec/*execution-context* ctx]
                  (spin-core/cancel-spin! the-spin)))
              nil)}))
