(ns org.replikativ.spindel.dom.render
  "Reactive rendering - connects spindel's signal system to DOM.

  **Commit-time reconciliation:**

  1. Elements are macros that capture source location
  2. Each element has a stable address (source-loc + parent + slot)
  3. Builds are PURE VALUES - no cache reads, no deltas, no staging
  4. At the commit point the arrived tree is diffed against the
     committed per-address caches (dom/commit) and the caches advance
     in the same step as the DOM write
  5. A stale build committed later diffs against the already-advanced
     baseline and collapses to its genuine residual

  Usage:
    (render! container
      (spin
        (let [{:keys [new]} (track todos)]
          (el/ul
            (ifor-each :id new
              (fn [todo] (el/li (:text todo))))))))

  The spin re-runs whenever tracked signals change; each completion's
  tree is committed through dom/commit."
  (:require [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.cache :as cache]
            [org.replikativ.spindel.dom.commit :as commit]
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
                  (disch/render-initial! discharge vdom))]
    ;; Append to container
    (when (and container root-el)
      (.appendChild container root-el))
    ;; The whole tree just reached the DOM: SEED the caches from the tree
    ;; itself. This replaces promoting the build's staging — staging is
    ;; last-write-wins per address, so when several builds raced before this
    ;; mount, the staged value could describe a build the DOM never received.
    ;; The tree the DOM holds is the only sound source. (Commit point
    ;; ordering unchanged; this is still the commit point that matters most —
    ;; a spin with no tracks runs its body exactly once, here.)
    (commit/seed-subtree-caches! vdom)
    ;; No transfer needed — address-based refs work with cleared vdom
    ;; (clear-deltas-deep preserves :addr fields)
    ;; builds are pure values — nothing to clear
    (assoc render-state
           :current-vdom vdom
           :mounted? true)))

(defn update-render!
  "Apply an arrived vdom tree to the DOM via commit-time reconciliation
  (dom/commit): diff against the committed per-address caches, apply,
  advance the caches in the same step. DOM refs are stored by stable
  address (:addr on vnodes), so no transfer is needed between old and
  new vdom objects."
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
        (binding [disch/*rendered-addrs* (atom {})
                  disch/*pending-evictions* (atom #{})]
          ;; Refs get their nil call and caches are SCHEDULED (not yet dropped):
          ;; foreign nodes (TipTap et al.) rely on this to release resources.
          (disch/call-refs-on-unmount! current-vdom)
          (let [root-el (disch/render-initial! discharge new-vdom)]
            (when container
              (set! (.-innerHTML container) "")
              (when root-el (.appendChild container root-el))))
          ;; The new tree is in the DOM: seed its caches from the tree (same
          ;; reasoning as initial-mount! — the arrived tree is the authority,
          ;; not last-write-wins staging). Before the evictions, so an address
          ;; this pass unmounted is not resurrected by the seeding.
          (commit/seed-subtree-caches! new-vdom)
          (disch/flush-pending-evictions! discharge))
        (assoc render-state :current-vdom new-vdom))

      :else
      (do
        ;; Discharge deltas directly - no diffing needed
        ;; DOM refs found by address, no transfer needed
        (binding [disch/*rendered-addrs* (atom {})
                  disch/*pending-evictions* (atom #{})]
          ;; COMMIT-TIME RECONCILIATION (dom/commit): diff the arrived tree
          ;; against the committed caches, apply, and advance the caches in
          ;; the same step. Build-time :deltas on the vnodes are IGNORED —
          ;; they were computed against whatever baseline the build happened
          ;; to see, and when N builds race before a commit they all carry
          ;; the same :add (measured: six builds of one container per settled
          ;; expand, the same :add discharged in two passes). Here a stale
          ;; build diffs against the advanced baseline and collapses to its
          ;; genuine residual. Unmount refs + deferred evictions flow through
          ;; the same apply-child-delta! paths as before.
          (commit/commit-reconcile! discharge new-vdom)
          (disch/flush-pending-evictions! discharge))
        (assoc render-state :current-vdom new-vdom)))))

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

  Builds are pure values, so cached spin results embedded by a
  re-emitting parent are safe by construction: committing the same
  state twice diffs to nothing. No per-object applied tracking is
  needed."
  [container discharge]
  (let [state-atom (atom (->RenderState container discharge nil false))]
    (fn [vdom]
      (when vdom
        (let [state @state-atom]
          (log/debug ::render-effect-callback {:mounted? (:mounted? state)
                                               :vdom-tag (:tag vdom)})
          (if (:mounted? state)
            ;; Commit-time reconciliation (dom/commit) — diff the arrived
            ;; tree against the committed caches at the point of writing
            (swap! state-atom update-render! vdom)
            ;; Initial mount
            (reset! state-atom (initial-mount! state vdom))))))))

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
