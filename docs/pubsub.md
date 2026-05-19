# Pub/Sub

Spindel provides a pub/sub system for fan-out broadcasting and topic-based routing over async sequences, with configurable buffering and backpressure.

```clojure
(require '[org.replikativ.spindel.pubsub.mult :as mult]
         '[org.replikativ.spindel.pubsub.pub :as pub]
         '[org.replikativ.spindel.pubsub.buffer :as buf]
         '[org.replikativ.spindel.seq.core :refer [gen-aseq yield]])
```

## Mult — Fan-Out Broadcasting

A `mult` broadcasts every item from a source async sequence to all taps. Each tap receives all items.

```clojure
;; Create source sequence
(def source (gen-aseq (yield 1) (yield 2) (yield 3)))

;; Create mult
(def m (mult/mult source))

;; Create taps (each receives ALL items)
(def tap1 (mult/tap m (buf/fixed-buffer 10)))
(def tap2 (mult/tap m (buf/fixed-buffer 10)))

;; Both tap1 and tap2 receive: 1, 2, 3
```

### Backpressure

By default, the producer waits until **all** taps have accepted a value before proceeding to the next. This prevents fast producers from overwhelming slow consumers.

```clojure
;; Rendezvous (no buffer) — maximum backpressure
(def tap-sync (mult/tap m))

;; Buffered — producer only blocks when buffer full
(def tap-buf (mult/tap m (buf/fixed-buffer 100)))
```

### Lifecycle

```clojure
;; Remove a tap
(mult/untap m tap1)

;; Check if source is exhausted
(mult/mult-closed? m)  ;; => true when source sequence ends

;; Check if a tap is closed
(mult/tap-closed? tap1)
```

When the source sequence ends, all taps are closed automatically (unless created with `close? false`).

## Pub — Topic-Based Routing

A `pub` routes items to subscribers based on a topic function. Each topic gets its own mult.

```clojure
;; Source with different event types
(def events
  (gen-aseq
    (yield {:type :user   :action "login"})
    (yield {:type :system :action "heartbeat"})
    (yield {:type :user   :action "click"})
    (yield {:type :system :action "metrics"})))

;; Create pub with topic function
(def p (pub/pub events :type))

;; Subscribe to specific topics
(def user-events   (pub/sub p :user))
(def system-events (pub/sub p :system))

;; user-events receives:
;;   {:type :user :action "login"}
;;   {:type :user :action "click"}

;; system-events receives:
;;   {:type :system :action "heartbeat"}
;;   {:type :system :action "metrics"}
```

### Per-Topic Buffers

You can configure buffers per topic at pub creation time:

```clojure
(def p (pub/pub events :type
         (fn [topic]
           (case topic
             :user   (buf/fixed-buffer 100)    ;; user events buffered
             :system (buf/sliding-buffer 10)    ;; system events: keep latest 10
             nil))))                            ;; default: rendezvous
```

Or per subscription:

```clojure
(def fast-sub (pub/sub p :user (buf/dropping-buffer 50)))
```

### Lifecycle

```clojure
;; Unsubscribe
(pub/unsub p :user user-events)

;; Unsubscribe all
(pub/unsub-all p)

;; Check if source exhausted
(pub/pub-closed? p)
```

## Buffer Types

Buffers control how items are held between producer and consumer.

### Fixed Buffer

Blocks the producer when full. Items are delivered in FIFO order.

```clojure
(buf/fixed-buffer 10)  ;; holds up to 10 items
```

Use when you need all items and can tolerate producer backpressure.

### Dropping Buffer

Never blocks the producer. Drops **new** items when full.

```clojure
(buf/dropping-buffer 10)  ;; holds up to 10, drops new arrivals when full
```

Use when the producer must never block and you can afford to lose the latest items.

### Sliding Buffer

Never blocks the producer. Drops **oldest** items when full.

```clojure
(buf/sliding-buffer 10)  ;; holds up to 10, discards oldest when full
```

Use when freshness matters more than completeness (e.g., real-time displays).

### No Buffer (Rendezvous)

Pass `nil` for synchronous handoff — the producer waits for the consumer on every item.

```clojure
(mult/tap m nil)  ;; rendezvous
(mult/tap m)      ;; also rendezvous (default)
```

### Buffer Comparison

| Buffer | Blocks producer? | On overflow | Order |
|--------|-----------------|-------------|-------|
| `fixed-buffer` | Yes, when full | Waits | FIFO |
| `dropping-buffer` | Never | Drops new items | FIFO |
| `sliding-buffer` | Never | Drops oldest items | FIFO |
| `nil` (rendezvous) | Yes, always | N/A | Synchronous |

### Buffer Inspection

```clojure
(buf/full? buffer)          ;; true if at capacity
(buf/buffer-empty? buffer)  ;; true if no items
(buf/unblocking? buffer)    ;; true if never blocks (dropping/sliding)
```

## Integration with gen-aseq

The source for mult and pub is any `PAsyncSeq` — typically created with `gen-aseq`:

```clojure
;; Infinite event source
(def event-source
  (gen-aseq
    (loop []
      (let [event (await (next-event))]
        (yield event)
        (recur)))))

;; Fan out to multiple processors
(def m (mult/mult event-source))
(def logger-tap   (mult/tap m (buf/sliding-buffer 100)))
(def processor-tap (mult/tap m (buf/fixed-buffer 50)))

;; Each tap processes independently
(spin
  (loop [s logger-tap]
    (when-let [[event rest] (await (anext s))]
      (log-event event)
      (recur rest))))

(spin
  (loop [s processor-tap]
    (when-let [[event rest] (await (anext s))]
      (process-event event)
      (recur rest))))
```

## See Also

- [Effects](effects.md) — `yield` and async sequences
- [Combinators](combinators.md) — Rate control
- [Getting Started](getting-started.md) — Basic tutorial
