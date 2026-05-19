(ns org.replikativ.spindel.pubsub.buffer
  "Buffer protocol and implementations for pub/sub backpressure.

   Follows core.async's buffer semantics:
   - IBuffer protocol for user-extensible buffers
   - IUnblocking marker protocol for non-blocking buffers
   - Built-in implementations: fixed, dropping, sliding

   Buffers manage backpressure between producers and consumers.
   A nil buffer means rendezvous (synchronous handoff)."
  #?(:clj (:import [java.util LinkedList])))

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

#?(:clj
   (deftype FixedBuffer [^LinkedList buf ^long n]
     PBuffer
     (full? [_]
       (>= (.size buf) n))
     (add! [this item]
       (.addFirst buf item)
       this)
     (remove! [_]
       (when-not (.isEmpty buf)
         (.removeLast buf)))
     (close-buf! [_])

     clojure.lang.Counted
     (count [_]
       (.size buf)))

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
  #?(:clj (FixedBuffer. (LinkedList.) n)
     :cljs (FixedBuffer. (atom []) n)))

;; =============================================================================
;; Dropping Buffer
;; =============================================================================

#?(:clj
   (deftype DroppingBuffer [^LinkedList buf ^long n]
     IUnblocking

     PBuffer
     (full? [_]
       false)  ; Never blocks - drops newest when full
     (add! [this item]
       (when-not (>= (.size buf) n)
         (.addFirst buf item))
       this)
     (remove! [_]
       (when-not (.isEmpty buf)
         (.removeLast buf)))
     (close-buf! [_])

     clojure.lang.Counted
     (count [_]
       (.size buf)))

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
  #?(:clj (DroppingBuffer. (LinkedList.) n)
     :cljs (DroppingBuffer. (atom []) n)))

;; =============================================================================
;; Sliding Buffer
;; =============================================================================

#?(:clj
   (deftype SlidingBuffer [^LinkedList buf ^long n]
     IUnblocking

     PBuffer
     (full? [_]
       false)  ; Never blocks - slides oldest when full
     (add! [this item]
       (when (= (.size buf) n)
         (.removeLast buf))  ; Slide oldest out
       (.addFirst buf item)
       this)
     (remove! [_]
       (when-not (.isEmpty buf)
         (.removeLast buf)))
     (close-buf! [_])

     clojure.lang.Counted
     (count [_]
       (.size buf)))

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
  #?(:clj (SlidingBuffer. (LinkedList.) n)
     :cljs (SlidingBuffer. (atom []) n)))

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
