(ns examples.shared.logging-discharge
  "Shared `LoggingDischarge` wrapper used by the diagnostic side panels in
   todo-demo, infinite-scroll-demo, and block-editor-demo.

   Implements every `PDischarge` method (including the batch ops
   `remove-children-range!` / `insert-children!` and the
   `child-index-of` query used for fragment-offset computation), so
   sub-1 DOM operations get logged the same way regardless of which
   delta path the discharge layer picks.

   Each entry is a small map with at least an `:op` key. Many entries
   also carry a `:type :add` / `:type :remove` tag so log viewers can
   colour them; consult the rendering code in each example for the
   exact format used in HTML.

   The discharge does NOT count operations itself — examples that want
   a running total either look at `(count @log)` or maintain their own
   counter."
  (:require [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.browser :as browser]))

(defn- short-str
  "Truncate `v` to `n` characters for log display."
  [v n]
  (let [s (str v)]
    (subs s 0 (min n (count s)))))

(defrecord LoggingDischarge [inner log]
  disch/PDischarge

  (create-element! [_ vnode]
    (swap! log conj {:op :create :tag (:tag vnode) :type :add})
    (disch/create-element! inner vnode))

  (create-text! [_ text]
    (swap! log conj {:op :create-text :text (short-str text 30) :type :add})
    (disch/create-text! inner text))

  (set-attribute! [_ el attr-name attr-value]
    (swap! log conj {:op :set-attr :attr attr-name :value (short-str attr-value 30)})
    (disch/set-attribute! inner el attr-name attr-value))

  (remove-attribute! [_ el attr-name]
    (swap! log conj {:op :remove-attr :attr attr-name})
    (disch/remove-attribute! inner el attr-name))

  (append-child! [_ parent child]
    (swap! log conj {:op :append :type :add})
    (disch/append-child! inner parent child))

  (insert-child! [_ parent child index]
    (swap! log conj {:op :insert :index index :type :add})
    (disch/insert-child! inner parent child index))

  (remove-child! [_ parent index]
    (swap! log conj {:op :remove :index index :type :remove})
    (disch/remove-child! inner parent index))

  (replace-child! [_ parent new-child index]
    (swap! log conj {:op :replace :index index :type :add})
    (disch/replace-child! inner parent new-child index))

  (move-child! [_ parent from-idx to-idx]
    (swap! log conj {:op :move :from from-idx :to to-idx})
    (disch/move-child! inner parent from-idx to-idx))

  (child-index-of [_ parent child]
    (disch/child-index-of inner parent child))

  (set-text-content! [_ el text]
    (swap! log conj {:op :set-text :text (short-str text 30)})
    (disch/set-text-content! inner el text))

  (get-element [_ addr]
    (disch/get-element inner addr))

  (set-element! [_ addr el]
    (disch/set-element! inner addr el))

  (remove-children-range! [_ parent start-idx cnt]
    (swap! log conj {:op :remove-range :start start-idx :count cnt :type :remove})
    (disch/remove-children-range! inner parent start-idx cnt))

  (insert-children! [_ parent children start-idx]
    (swap! log conj {:op :insert-children :start start-idx :count (count children) :type :add})
    (disch/insert-children! inner parent children start-idx)))

(defn make-logging-discharge
  "Wrap a `browser/make-dom-discharge` with op-logging into `log`.

   `log` is an atom holding a vector; each PDischarge call conj's one map."
  [document log]
  (->LoggingDischarge (browser/make-dom-discharge document) log))
