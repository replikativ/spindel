# AsyncSeq Integration with Spindel

## Summary

Successfully integrated partial-cps's AsyncSeq protocol with spindel's Mailbox. The integration **works correctly** when using raw CPS functions, but has a known limitation with the `make-spin` wrapper.

## What Works ✅

### 1. Direct CPS Function Usage
```clojure
;; Await raw partial-cps async functions - WORKS PERFECTLY
(binding [ec/*execution-context* ctx]
  @(spin (await (aseq/into [] (take 3) mailbox))))
;; => [msg1 msg2 msg3]

;; Works with vectors too
@(spin (await (aseq/into [] (take 2) [1 2 3])))
;; => [1 2]
```

### 2. Pre-created Spins
```clojure
;; Create spin first, then await it - WORKS
(def my-spin (spin-core/make-spin (aseq/into [] (take 2) [1 2 3])))
@(spin (await my-spin))
;; => [1 2]
```

## Known Limitation ⚠️

### Inline Spin Creation + Await Hangs

```clojure
;; This HANGS - do not use this pattern
@(spin
  (await (spin-core/make-spin
           (aseq/into [] (take 2) [1 2 3]))))
```

**Workaround:** Use raw CPS functions directly (recommended) or pre-create spins.

## Implementation Details

### Mailbox PAsyncSeq Extension

`PAsyncSeq/anext` returns a **CPS function** (not a Spin) to maintain compatibility with partial-cps:

```clojure
(extend-type Mailbox
  aseq/PAsyncSeq
  (anext [mbx]
    ;; Returns CPS function: (fn [resolve reject] ...)
    (fn [resolve reject]
      ;; Capture execution context for nested operations
      (let [exec-ctx (try (ec/current-execution-context) (catch _ nil))]
        (mbx
          ;; Wrap resolve to rebind context
          (fn [msg]
            (if exec-ctx
              (binding [ec/*execution-context* exec-ctx]
                (resolve [msg mbx]))
              (resolve [msg mbx])))
          ;; Wrap reject to rebind context
          (fn [error]
            (if exec-ctx
              (binding [ec/*execution-context* exec-ctx]
                (reject error))
              (reject error))))))))
```

**Key insights:**
1. Must return CPS function, not Spin (matches vector/list implementations in partial-cps)
2. Must capture and rebind `*execution-context*` (not captured in spindel's binding system)
3. Wraps both resolve and reject continuations to maintain context across async boundaries

### Why Context Rebinding Is Necessary

Spindel's `*execution-context*` is deliberately NOT captured in continuation bindings (see `engine/bindings.cljc:54`). When partial-cps resumes its continuations, the context needs to be explicitly rebound.

## Testing Findings

### Test Results

| Scenario | Vector | Mailbox | Status |
|----------|--------|---------|--------|
| Raw CPS await | ✅ [1 2] | ✅ [100 200 300] | Works |
| Pre-created spin | ✅ [1 2] | Not tested | Works |
| Inline create+await | ⏱️ Hangs | ⏱️ Hangs | Known issue |

### Diagnostic Results

**Test Script Output:**
```
=== Test 1: Pre-created spin (WORKS) ===
Creating spin...
Spin created: #object[org.replikativ.spindel.spin.core.Spin ...]
Result: [1 2]

=== Test 2: Inline create+await (HANGS?) ===
Starting inline test with 5 second timeout...
  Inside future, creating and awaiting...
TIMEOUT! Future did not complete.

=== Test 3: Inline WITHOUT make-spin (WORKS?) ===
Awaiting raw CPS function...
Result: [100 200]
```

## Investigation into Hang Issue

### Hypotheses Tested

1. **✅ Raw CPS functions work** - Confirmed. Spindel's await correctly handles partial-cps CPS functions (see `effects/await.cljc:172-176`)

2. **✅ Hang is specific to make-spin** - Confirmed. Both vectors and Mailboxes hang when wrapped in make-spin

3. **✅ Executor exists** - Confirmed. `:atoms` runtime creates default executor (`engine/impl/simple.cljc`)

4. **❓ Event queue processing** - Unclear. Events are enqueued but unclear if they're being processed in time

5. **❓ Thread blocking issue** - Possible. When `@spin` blocks (see `spin/core.cljc:279`), it may prevent event loop progress

### Likely Cause

The hang appears to be a **circular event dependency**:

1. Outer spin calls `(await inner-spin)`
2. await-spin registers continuation waiting for `:spin/complete` event
3. await-spin calls `(inner-spin noop noop)` to start inner spin
4. Inner spin tries to execute (calls partial-cps functions)
5. Partial-cps operations generate events (deferred delivery, mailbox operations)
6. Events need to be processed, but...
7. Outer spin is blocked on `@spin` waiting for inner to complete
8. Deadlock if event processing can't proceed

## Recommended Usage

### ✅ DO: Use Raw CPS Functions

```clojure
;; This is the recommended pattern
(defn take-n [agent n]
  (spin
    (await (aseq/into [] (take n) (:outbox agent)))))

;; Usage
@(take-n my-agent 5)  ;; => [msg1 msg2 msg3 msg4 msg5]
```

### ❌ DON'T: Wrap CPS in make-spin

```clojure
;; This will hang - avoid this pattern
(spin
  (await (spin-core/make-spin
           (aseq/into [] (take n) mailbox))))
```

## Files Modified

- `src/is/simm/spindel/spin/sync.cljc` - Added PAsyncSeq extension to Mailbox
- `src/ratatosk/agents/patterns.clj` - Added FRP stream patterns using AsyncSeq

## Future Work

1. **Investigate inline spin creation hang** - May require changes to spin lifecycle or event processing
2. **Add comprehensive tests** - Test all AsyncSeq operations (sequence, transduce, for, etc.)
3. **Document best practices** - Create guide for mixing spindel and partial-cps
4. **Consider spindel-native stream abstraction** - May want spindel-specific stream combinators
