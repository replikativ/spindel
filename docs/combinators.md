# Combinators

Spindel provides combinators for composing spins with concurrency, timing, and error handling.

```clojure
(require '[org.replikativ.spindel.spin.combinators
           :refer [parallel race sleep timeout debounce throttle
                   sample relieve accumulate]]
         '[org.replikativ.spindel.spin.core :refer [ok error attempt absolve]]
         '[org.replikativ.spindel.incremental.interval :as iv])
```

## Concurrency

### `parallel` — Concurrent Execution

Execute multiple spins concurrently. Returns a vector of results when all complete.

```clojure
(spin
  (let [[a b c] (await (parallel
                         (fetch-user user-id)
                         (fetch-posts user-id)
                         (fetch-settings user-id)))]
    {:user a :posts b :settings c}))
```

- **Fail-fast**: If any child fails, all siblings are cancelled and the error propagates
- **Reactive**: When children track signals that change, children re-run and `parallel` updates
- **Thread-pool**: Each child runs on a separate worker thread

### `race` — First to Complete

Execute multiple spins concurrently. Returns the result of the first to complete; losers are cancelled.

```clojure
(spin
  (await (race
    (fetch-from-primary)
    (fetch-from-replica))))
```

- **Winner takes all**: First spin to complete wins
- **Losers cancelled**: Cooperative cancellation at next `await` point

### `sleep` — Time Delay

Create a spin that completes after a duration (milliseconds).

```clojure
(spin
  (await (sleep 1000))       ;; wait 1 second, returns nil
  (await (sleep 500 :done))) ;; wait 500ms, returns :done
```

### `timeout` — Deadline with Fallback

Race a spin against a deadline. Returns fallback value if the spin doesn't complete in time.

```clojure
(spin
  (let [data (await (timeout (fetch-remote-data) 5000 :cached-default))]
    (process data)))
```

Equivalent to `(race source-spin (sleep timeout-ms fallback-value))`.

## Rate Control

These combinators control how frequently reactive re-executions deliver results.

### `debounce` — Wait for Quiet Period

Delay delivery until a quiet period elapses. Useful for text input — wait until the user stops typing.

```clojure
(spin
  (let [content (await (debounce (track content-signal) 300))]
    (search-preview content)))
```

When the signal changes, the timer restarts. The spin only receives the value after 300ms of no changes.

### `throttle` — Max Frequency

Limit updates to a maximum frequency (Hz). A merge function combines intermediate values.

```clojure
;; Limit to 60 updates/second, keep latest value
(spin
  (let [pos (await (throttle (track mouse-signal) 60 (fn [_ new] new)))]
    (update-cursor pos)))

;; Collect all values between deliveries
(spin
  (let [events (await (throttle (track event-signal) 10
                        (fn [acc new] (conj (or acc []) new))))]
    (process-batch events)))
```

The merge function signature: `(fn [accumulated-value new-value] -> merged-value)`

### `sample` — Fixed Interval Polling

Take the latest value at fixed intervals, ignoring intermediate changes.

```clojure
;; Sync state to server every 5 seconds
(spin
  (let [state (await (sample (track app-state) 5000))]
    (persist-to-server! state)))
```

### `relieve` — Drop Intermediate Values

When the observer is slower than the producer, drop intermediate values and always deliver the latest.

```clojure
;; Real-time display where freshness matters more than completeness
(spin
  (let [data (await (relieve (track sensor-signal)))]
    (render-dashboard data)))
```

### `accumulate` — Preserve Deltas

When used with `throttle`, intermediate deltas are normally lost. `accumulate` preserves all deltas by merging intervals:

```clojure
;; Without accumulate — intermediate deltas may be lost
(spin
  (let [items (await (throttle (track items-signal) 10 (fn [_ new] new)))]
    ;; deltas may be incomplete
    ))

;; With accumulate — all deltas preserved
(spin
  (let [iv (await (throttle
                    (accumulate items-signal iv/merge-intervals)
                    10
                    (fn [_ new] new)))]
    ;; iv contains ALL deltas since last delivery
    (doseq [{:keys [delta path value]} (:deltas iv)]
      (case delta
        :add    (render-item-at path value)
        :remove (remove-item-at path)
        :update (update-item-at path value)))))
```

`merge-intervals` is **associative** (CRDT-like): `merge(merge(a,b),c) = merge(a,merge(b,c))`. It preserves the original baseline (`:old`), uses the latest value (`:new`), and concatenates + compacts deltas.

## Error Handling

### Result Type

Spins produce `Result` values — either success or error:

```clojure
(require '[org.replikativ.spindel.spin.core :refer [ok error ok? error? unwrap match]])
```

```clojure
;; Create results
(ok 42)           ;; success
(error (ex-info "oops" {}))  ;; failure

;; Check results
(ok? (ok 42))     ;; => true
(error? (ok 42))  ;; => false

;; Unwrap (throws on error)
(unwrap (ok 42))  ;; => 42
(unwrap (error (ex-info "oops" {})))  ;; throws!

;; Pattern match
(match result
  (fn [value] (println "Success:" value))
  (fn [err]   (println "Error:" err)))
```

### `attempt` — Capture Errors

Wrap a spin's result so errors don't propagate. The result becomes a zero-argument function that either returns the value or throws:

```clojure
(spin
  (let [result-fn (await (attempt risky-spin))]
    (try
      (result-fn)  ;; returns value or throws
      (catch Exception e
        :fallback))))
```

### `absolve` — Unwrap Captured Errors

The inverse of `attempt` — calls the wrapped function, converting captured errors back to thrown exceptions:

```clojure
(spin
  (let [value (await (absolve safe-spin))]
    ;; If safe-spin returned an error-wrapping function, it throws here
    (process value)))
```

### Cancellation

Spins support cooperative cancellation:

```clojure
(require '[org.replikativ.spindel.spin.core :refer [cancel-spin! spin-cancelled?]])

;; Cancel a spin (and all its observers)
(cancel-spin! my-spin)

;; Check cancellation
(spin-cancelled? my-spin)  ;; => true
```

Cancellation is **cooperative** — spins check at `await` and `track` points. CPU-bound code without breakpoints won't be interrupted.

### Cleanup

Spins are automatically cleaned up when garbage collected. For explicit cleanup:

```clojure
(require '[org.replikativ.spindel.spin.core :refer [cleanup-spin!]])

;; Remove spin from dependency graph and signal observer lists
(cleanup-spin! my-spin)
;; Don't deref after cleanup!
```

## Semaphore — Rate Limiting

Limit concurrent access with fork-safe semaphores:

```clojure
(require '[org.replikativ.spindel.semaphore :refer [semaphore acquire release holding]])

(def sem (semaphore 3))  ;; max 3 concurrent

;; Manual acquire/release
(spin
  (await (acquire sem))
  (try
    (do-limited-work)
    (finally
      (release sem))))

;; Or use `holding` for automatic release
(spin
  (await (holding sem
           (spin (do-limited-work)))))
```

- **FIFO fairness**: Waiters served in order
- **Fork-safe**: State stored in execution context
- `@sem` returns current available permits

## See Also

- [Effects](effects.md) — `await`, `track`, `yield`
- [Incremental](incremental.md) — Delta tracking with `accumulate`
- [Pub/Sub](pubsub.md) — Fan-out and topic routing
