# Nested Spin Support in Spindel DOM

## Problem Statement

Components want local reactive state (e.g., collapse/expand toggle). The natural pattern:

```clojure
(defn property-box [{:keys [properties ...]}]
  (spin
    (let [open-signal (signal false)
          open? (iv/get-new (track open-signal))
          toggle! (fn [_] (swap! open-signal not))]
      (el/div {:on-click toggle!}
        (when open? ...)))))
```

This creates a nested spin that needs to be `await`ed from the parent.

### Current Limitation

`await` and `track` only work **textually inside a spin macro body**. They are CPS breakpoints that the spin macro transforms at compile time.

When you call a helper function from inside a spin, that function's body is NOT CPS-transformed:

```clojure
(defn helper []
  (await something))  ; NOT CPS-transformed - throws error!

(spin
  (helper))  ; helper is called, but its body isn't transformed
```

### Error Manifestation

```
"await called outside of spin context (should be CPS-transformed)"
```

This happens when `await` is called from a regular function (like `render-page-header`) even if that function is transitively called from inside a spin.

## Simple Fallback (Native HTML)

For simple local state like collapse/expand, use native HTML:

```clojure
(defn property-box [{:keys [properties ...]}]
  (el/details {:class "property-box"}
    (el/summary {:class "property-box-header"}
      "Properties")
    (el/div {:class "property-box-content"}
      ...)))
```

The browser handles the open/close state natively.

## Proper Solution: Element* as CPS Breakpoint

### Architecture Overview

Make element evaluation aware of Spin children by registering `element*` as a CPS breakpoint in the spin macro.

### Files Involved

1. **`spindel/dom/element-effect.cljc`** (NEW)
   - Element CPS breakpoint handler
   - `await-children` helper that evaluates thunks and awaits Spins

2. **`spindel/spin/cps.cljc`**
   - Register element* breakpoint from element-effect.cljc
   - Include in `build-breakpoints`

3. **`spindel/dom/elements.cljc`**
   - `element*` becomes the target of CPS transformation
   - Possibly split into sync/async paths

### Proposed Implementation

#### element-effect.cljc

```clojure
(ns org.replikativ.spindel.dom.element-effect
  "CPS breakpoint for element evaluation with Spin child support."
  (:require [org.replikativ.spindel.spin.protocols :as spin-p]
            [org.replikativ.spindel.dom.elements :as el]))

(defn spin? [x]
  (satisfies? spin-p/PSpin x))

;; This gets CPS-transformed by the spin macro
(defn element-with-async-children
  "Evaluate child thunks, awaiting any that return Spins.
   Must be called from within CPS context (spin body)."
  [tag source-loc attrs child-thunks]
  ;; Loop through children, await Spins
  ;; Returns final vnode
  ...)

;; Breakpoint handler for spin macro
(def element-breakpoint
  {:handler 'org.replikativ.spindel.dom.element-effect/element-with-async-children
   :direct-handler-sym 'org.replikativ.spindel.dom.element-effect/element-handler-direct})
```

#### Integration in cps.cljc

```clojure
(ns org.replikativ.spindel.spin.cps
  (:require [org.replikativ.spindel.dom.element-effect :as elem-eff]
            ...))

(defn build-breakpoints []
  (merge async/breakpoints
         ;; Existing effects (await, track)
         (build-effect-breakpoints)
         ;; Element breakpoint for async children
         {'org.replikativ.spindel.dom.elements/element*
          (:handler elem-eff/element-breakpoint)}))
```

### Key Design Decisions

1. **Transparent API**: No changes to `el/div`, `el/span`, etc.
2. **Opt-in complexity**: Only spins that have Spin children pay the cost
3. **Fallback path**: If no Spin children, behaves like current sync path

### Testing Strategy

1. Nested spin with signal/track in child component
2. Multiple Spin children in same parent
3. Deeply nested spins (grandchildren)
4. Mixed sync and async children

## Related Files

- `/home/christian-weilbach/Development/simmis/src/is/simm/uis/web/desktop/views/types.cljc` - property-box component
- `/home/christian-weilbach/Development/simmis/src/is/simm/uis/web/desktop/block_editor.cljs` - uses property-box

## Fallback Restoration

If nested spin support doesn't work, restore property-box to use `<details>`:

```clojure
(defn property-box [{:keys [properties ...]}]
  (el/details {:class "property-box"}
    (el/summary {:class "property-box-header"
                 :on-click (fn [e] (.stopPropagation e))}
      (el/span {:class "property-box-toggle"} "▶")
      (el/span {:class "property-box-title"}
        (str "Properties (" (count properties) ")")))
    (when (seq properties)
      (el/div {:class "property-box-content"}
        ...))))
```

No changes needed to block_editor.cljs - just remove the `await` wrapper.
