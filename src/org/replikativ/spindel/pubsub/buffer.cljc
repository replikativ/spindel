(ns org.replikativ.spindel.pubsub.buffer
  "Buffer protocol and implementations for pub/sub backpressure.

   Follows core.async's buffer semantics:
   - IBuffer protocol for user-extensible buffers
   - IUnblocking marker protocol for non-blocking buffers
   - Built-in implementations: fixed, dropping, sliding

   Buffers manage backpressure between producers and consumers.
   A nil buffer means rendezvous (synchronous handoff).")

;; =============================================================================
;; Buffer Protocol
;; =============================================================================

(defprotocol PBuffer
  "Protocol for message buffers in pub/sub.

   Buffers sit between producer and consumer, managing backpressure.
   Implementations control how messages are queued and when the producer
   should block."

  (full? [buffer]
    "Returns true if buffer cannot accept more items.

     When full? returns true, producer must wait (backpressure).
     Non-blocking buffers (IUnblocking) should never return true.")

  (add! [buffer item]
    "Add item to buffer. Returns buffer.

     Called when producer has an item to deliver.
     For dropping/sliding buffers, may silently discard.")

  (remove! [buffer]
    "Remove and return oldest item from buffer.

     Called when consumer is ready to receive.
     Returns nil if buffer is empty (should check with count first).")

  (close-buf! [buffer]
    "Called when buffer is closed. Cleanup if needed."))

(defprotocol IUnblocking
  "Marker protocol for buffers that never block the producer.

   Buffers implementing this protocol always return false from full?.
   Examples: dropping-buffer, sliding-buffer.")

;; =============================================================================
;; Fixed Buffer
;; =============================================================================

;; THREAD SAFETY (spindel#34): buffers are mutated and re-read from
;; DIFFERENT drain threads — the producer side (deliver-to-all-taps!)
;; adds on one thread while the consumer side (TapSeq anext) rechecks
;; `count` on another, with only the availability-promise atoms between
;; them. The JVM implementations previously wrapped a raw (unsynchronized)
;; java.util.LinkedList: a plain-field data race under the JMM, so the
;; consumer's recheck could read a STALE size 0 after the producer's add
;; and then await a promise that had already been swapped and delivered —
;; a silent, load-dependent lost wakeup (one reply in a pub round-trip
;; simply never arriving). Inline delivery used to run the consumer on
;; the producer's thread and mostly hid this; resume-as-event (#27/#29)
;; made cross-thread producer/consumer the norm and exposed it.
;;
;; All implementations are now ATOM-backed vectors (as CLJS always was):
;; every add!/remove!/count is a volatile-semantics atom op, which is
;; exactly the happens-before edge the check-act-recheck patterns in
;; mult/pub assume — capture waiter, recheck buffer: if the capture saw
;; the post-add promise, the recheck is GUARANTEED to see the added item.
;; remove! uses swap-vals! so take-and-return is a single atomic step.
;; FIFO: conj appends, remove! pops the front.

#?(:clj
   (deftype FixedBuffer [buf-atom ^long n]
     PBuffer
     (full? [_]
       (>= (count @buf-atom) n))
     (add! [this item]
       (swap! buf-atom conj item)
       this)
     (remove! [_]
       (let [[old _] (swap-vals! buf-atom
                                 (fn [b] (if (seq b) (vec (rest b)) b)))]
         (first old)))
     (close-buf! [_])

     clojure.lang.Counted
     (count [_]
       (count @buf-atom)))

   :cljs
   (deftype FixedBuffer [buf-atom n]
     PBuffer
     (full? [_]
       (>= (count @buf-atom) n))
     (add! [this item]
       (swap! buf-atom conj item)
       this)
     (remove! [_]
       (let [buf @buf-atom]
         (when (seq buf)
           (swap! buf-atom (fn [b] (vec (rest b))))
           (first buf))))
     (close-buf! [_])

     ICounted
     (-count [_]
       (count @buf-atom))))

(defn fixed-buffer
  "Create a fixed-size buffer.

   When full, producer blocks until consumer removes items.
   Maintains FIFO order.

   Example:
     (fixed-buffer 10)  ; Buffer up to 10 items"
  [n]
  (assert (pos? n) "Buffer size must be positive")
  (FixedBuffer. (atom []) n))

;; =============================================================================
;; Dropping Buffer
;; =============================================================================

#?(:clj
   (deftype DroppingBuffer [buf-atom ^long n]
     IUnblocking

     PBuffer
     (full? [_]
       false)  ; Never blocks - drops newest when full
     (add! [this item]
       ;; size check + conj in ONE swap so a concurrent add cannot
       ;; overshoot n.
       (swap! buf-atom (fn [b] (if (< (count b) n) (conj b item) b)))
       this)
     (remove! [_]
       (let [[old _] (swap-vals! buf-atom
                                 (fn [b] (if (seq b) (vec (rest b)) b)))]
         (first old)))
     (close-buf! [_])

     clojure.lang.Counted
     (count [_]
       (count @buf-atom)))

   :cljs
   (deftype DroppingBuffer [buf-atom n]
     IUnblocking

     PBuffer
     (full? [_]
       false)
     (add! [this item]
       (when-not (>= (count @buf-atom) n)
         (swap! buf-atom conj item))
       this)
     (remove! [_]
       (let [buf @buf-atom]
         (when (seq buf)
           (swap! buf-atom (fn [b] (vec (rest b))))
           (first buf))))
     (close-buf! [_])

     ICounted
     (-count [_]
       (count @buf-atom))))

(defn dropping-buffer
  "Create a dropping buffer.

   Never blocks producer - drops new items when full.
   Use when losing newest data is acceptable (e.g., rate limiting).

   Example:
     (dropping-buffer 100)  ; Keep oldest 100, drop new ones when full"
  [n]
  (assert (pos? n) "Buffer size must be positive")
  (DroppingBuffer. (atom []) n))

;; =============================================================================
;; Sliding Buffer
;; =============================================================================

#?(:clj
   (deftype SlidingBuffer [buf-atom ^long n]
     IUnblocking

     PBuffer
     (full? [_]
       false)  ; Never blocks - slides oldest when full
     (add! [this item]
       ;; conj + slide in ONE swap (drop the OLDEST when over n).
       (swap! buf-atom (fn [b]
                         (let [b' (conj b item)]
                           (if (> (count b') n) (vec (rest b')) b'))))
       this)
     (remove! [_]
       (let [[old _] (swap-vals! buf-atom
                                 (fn [b] (if (seq b) (vec (rest b)) b)))]
         (first old)))
     (close-buf! [_])

     clojure.lang.Counted
     (count [_]
       (count @buf-atom)))

   :cljs
   (deftype SlidingBuffer [buf-atom n]
     IUnblocking

     PBuffer
     (full? [_]
       false)
     (add! [this item]
       (swap! buf-atom (fn [buf]
                         (let [buf' (conj buf item)]
                           (if (> (count buf') n)
                             (vec (rest buf'))
                             buf'))))
       this)
     (remove! [_]
       (let [buf @buf-atom]
         (when (seq buf)
           (swap! buf-atom (fn [b] (vec (rest b))))
           (first buf))))
     (close-buf! [_])

     ICounted
     (-count [_]
       (count @buf-atom))))

(defn sliding-buffer
  "Create a sliding buffer.

   Never blocks producer - discards oldest items when full.
   Use when only recent data matters (e.g., real-time metrics).

   Example:
     (sliding-buffer 100)  ; Keep newest 100, slide oldest out"
  [n]
  (assert (pos? n) "Buffer size must be positive")
  (SlidingBuffer. (atom []) n))

;; =============================================================================
;; Buffer Utilities
;; =============================================================================

(defn unblocking?
  "Returns true if buffer never blocks producer.

   Dropping and sliding buffers are unblocking.
   Fixed buffers can block when full."
  [buffer]
  (satisfies? IUnblocking buffer))

(defn buffer-empty?
  "Returns true if buffer has no items."
  [buffer]
  (zero? (count buffer)))
