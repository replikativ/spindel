(ns org.replikativ.spindel.incremental.sequence-algebra
  "Delta algebra for ordered sequences (vectors).

   A sequence diff is a single map with six fields:

     {:degree      Long   ; size of the sequence after :grow, before :shrink
      :grow        Long   ; slots appended at the tail (nil-initialised)
      :shrink      Long   ; slots removed from the tail
      :permutation {i j}  ; sparse-map permutation on [0, degree)
      :change      {i v}  ; positions whose value is replaced
      :freeze      #{i}}  ; positions promised immutable from here on

   Application order — fixed and load-bearing:

       grow → permutation → shrink → change → freeze

   With this order:
     - `:grow` is the first operation; permutation can reference the new
       slots; change can populate them.
     - `:shrink` happens after permutation; the soon-to-be-removed slots
       can be permuted-into and then dropped together.
     - `:change` keys live in *post-shrink* space `[0, degree-shrink)`,
       so they always reference surviving positions.
     - `:freeze` is metadata; it does not transform values. It just
       carries forward the promise that listed positions won't change.

   The pipeline is the unique normal form. Two diffs that produce the
   same observable effect have equal field-by-field representations (up
   to fixed-point omission in :permutation).

   Algebraic structure
   -------------------
   The diff set under `compose-deltas` forms a *monoid* (not a group —
   `:shrink` is irreversible). Permutations alone form `S_n`, which is
   a group; we inherit those operations from `permutation.cljc`.

   The carrier is non-free: the equational laws

     grow g1 ; grow g2          = grow (g1+g2)
     perm π1 ; perm π2          = perm (π2 ∘ π1)
     shrink s1 ; shrink s2      = shrink (s1+s2)
     change i v ; change i w    = change i w
     grow g ; shrink min(g,_)   collapse partially

   are *all* identifications in our monoid — the free monoid on these
   generators would be unbounded; the quotient gives one canonical
   representative per equivalence class. `compose-deltas` is exactly
   the function that computes the canonical representative."
  (:require [clojure.set :as set]
            [org.replikativ.spindel.incremental.algebra :as a]
            [org.replikativ.spindel.incremental.permutation :as p]))

;; =============================================================================
;; Construction helpers
;; =============================================================================

(defn diff
  "Build a sequence diff. All fields are optional; defaults are the
   identity values. The single required field is `:degree`.

   Convention: callers usually want to provide `:degree` (the size after
   grow and before shrink) and one of `:grow`, `:shrink`, `:permutation`,
   `:change`, `:freeze`. The rest defaults safely."
  [{:keys [degree grow shrink permutation change freeze]
    :or   {grow 0 shrink 0 permutation {} change {} freeze #{}}}]
  {:pre [(some? degree) (<= 0 grow degree) (<= 0 shrink degree)]}
  {:degree degree :grow grow :shrink shrink
   :permutation permutation :change change :freeze freeze})

(defn empty-diff
  "The identity diff at the given size: degree=size, all other fields
   empty. Composes neutrally on either side."
  [size]
  {:degree size :grow 0 :shrink 0 :permutation {} :change {} :freeze #{}})

(defn size-before
  "Size of the vector this diff expects as input. Equals `degree - grow`."
  [d]
  (- (:degree d) (:grow d 0)))

(defn size-after
  "Size of the vector this diff produces as output. Equals
   `degree - shrink`."
  [d]
  (- (:degree d) (:shrink d 0)))

;; =============================================================================
;; Apply
;; =============================================================================

(defn- apply-pipeline [old d]
  (let [degree (:degree d)
        grow   (:grow d 0)
        shrink (:shrink d 0)
        sz-after (- degree shrink)
        v (vec old)]
    (when (not= (- degree grow) (count v))
      (throw (ex-info "Sequence diff size mismatch in apply"
                      {:expected-size-before (- degree grow)
                       :actual-size (count v)
                       :diff d})))
    (-> v
        ;; Phase 1: grow — append `grow` nil slots
        (into (repeat grow nil))
        ;; Phase 2: permutation
        (->> (p/arrange (:permutation d {})))
        ;; Phase 3: shrink — drop trailing `shrink` slots
        (subvec 0 sz-after)
        ;; Phase 4: change — assoc each (k, v) where k must be < sz-after
        (as-> v* (reduce-kv (fn [acc k val]
                              (assoc acc k val))
                            v* (:change d {})))
        ;; Phase 5: freeze — pure metadata, no value transformation
        )))

;; =============================================================================
;; Compose
;;
;; Given d1 (taking A → B) and d2 (taking B → C), return d (A → C).
;;
;; The composed diff:
;;   :degree  = (degree d1) + (grow d2)    [maximum intermediate width]
;;   :grow    = grow1 + grow2
;;   :shrink  = shrink1 + shrink2
;;   :permutation = π2 ∘ split-swap ∘ π1
;;     where split-swap swaps two adjacent ranges:
;;       [n_B, degree1) of size s1  (the shrink1 region)
;;       [degree1, degree) of size g2  (the grow2 region)
;;     after split-swap the shrink1 region is at the tail of the combined
;;     space, so the total shrink (s1+s2) removes both regions correctly.
;;   :change  = {π2(i) ↦ v | (i,v) ∈ c1, π2(i) < n_C} ∪ c2
;;     c2 overrides c1' on key collision.
;;   :freeze  = {π2(i) | i ∈ fz1, π2(i) < n_C} ∪ fz2
;; =============================================================================

(defn- compose-pair [d1 d2]
  (let [g1 (:grow d1 0)   g2 (:grow d2 0)
        s1 (:shrink d1 0) s2 (:shrink d2 0)
        deg1 (:degree d1) deg2 (:degree d2)
        π1 (:permutation d1 {})
        π2 (:permutation d2 {})
        c1 (:change d1 {})
        c2 (:change d2 {})
        fz1 (:freeze d1 #{})
        fz2 (:freeze d2 #{})
        ;; intermediate-size invariants
        n-B (- deg1 s1)          ; size between d1 and d2; = deg2 - g2
        n-C (- deg2 s2)
        deg (+ deg1 g2)          ; combined degree = n_A + g1 + g2
        ;; split-swap: swap shrink1 region and grow2 region so the
        ;; doomed shrink1 slots end up at the tail of the combined space.
        ss (p/split-swap n-B s1 g2)
        ;; combined permutation: apply π1 first, then split-swap, then π2.
        π (p/compose π2 ss π1)
        ;; reproject c1 through π2; drop entries that land in the
        ;; shrink2 region (positions ≥ n_C).
        c1' (persistent!
             (reduce-kv (fn [acc i v]
                          (let [j (p/apply-perm π2 i)]
                            (if (< j n-C) (assoc! acc j v) acc)))
                        (transient {}) c1))
        ;; c2 overrides c1' at shared keys
        c (merge c1' c2)
        ;; reproject fz1 through π2 similarly
        fz1' (persistent!
              (reduce (fn [acc i]
                        (let [j (p/apply-perm π2 i)]
                          (if (< j n-C) (conj! acc j) acc)))
                      (transient #{}) fz1))
        fz (set/union fz1' fz2)]
    {:degree deg :grow (+ g1 g2) :shrink (+ s1 s2)
     :permutation π :change c :freeze fz}))

;; =============================================================================
;; State diff (compute a diff from two states)
;;
;; First-cut implementation: detect the trivial "no change" and
;; "everything different" cases. For the latter we emit a
;; *change-everything* diff: degree = (max |a| |b|), grow/shrink for
;; the size difference, and :change covering every position of b.
;; This is correct but verbose; a future refinement can use longest-
;; common-prefix/suffix to compress the diff.
;; =============================================================================

(defn- naive-state-diff [a b]
  (let [na (count a)
        nb (count b)
        degree (max na nb)
        grow   (max 0 (- nb na))
        shrink (max 0 (- na nb))
        change (persistent!
                (reduce (fn [acc i] (assoc! acc i (nth b i))) (transient {})
                        (range nb)))]
    {:degree degree :grow grow :shrink shrink
     :permutation {} :change change :freeze #{}}))

(defn- linear-state-diff
  "Detect longest common prefix/suffix and emit a smaller diff when the
   change is localised (single insert, remove, or contiguous overwrite).
   Falls back to `naive-state-diff` for arbitrary edits."
  [a b]
  (let [na (count a) nb (count b)
        lcp (loop [i 0]
              (cond
                (or (= i na) (= i nb))            i
                (= (nth a i) (nth b i))           (recur (inc i))
                :else                              i))
        max-suf (min (- na lcp) (- nb lcp))
        lcs (loop [k 0]
              (cond
                (= k max-suf)                                   k
                (= (nth a (- na 1 k)) (nth b (- nb 1 k)))       (recur (inc k))
                :else                                            k))
        a-mid-start lcp
        a-mid-end (- na lcs)
        b-mid-start lcp
        b-mid-end (- nb lcs)
        a-mid-len (- a-mid-end a-mid-start)
        b-mid-len (- b-mid-end b-mid-start)]
    (cond
      ;; Identical vectors — empty diff at size n.
      (and (zero? a-mid-len) (zero? b-mid-len))
      (empty-diff na)

      ;; Pure insert: a's middle empty, b's middle non-empty.
      (zero? a-mid-len)
      (let [change (persistent!
                    (reduce (fn [acc k]
                              (assoc! acc (+ b-mid-start k)
                                      (nth b (+ b-mid-start k))))
                            (transient {}) (range b-mid-len)))
            ;; Build the permutation, then canonicalise (drop fixed
            ;; points). Append at the tail produces an all-identity
            ;; permutation; without canonicalisation the diff would
            ;; carry useless fixed-point entries.
            π (p/canonicalize
               (persistent!
                (reduce (fn [acc i]
                          (let [tail-pos (+ na i)
                                target   (+ b-mid-start i)]
                            (assoc! acc tail-pos target)))
                          ;; And shift the originally-trailing items rightward.
                        (let [base (transient {})]
                          (reduce (fn [acc i] (assoc! acc i (+ i b-mid-len)))
                                  base (range b-mid-start na)))
                        (range b-mid-len))))]
        {:degree (+ na b-mid-len) :grow b-mid-len :shrink 0
         :permutation π :change change :freeze #{}})

      ;; Pure remove: b's middle empty, a's middle non-empty.
      (zero? b-mid-len)
      (let [;; Doomed items at [a-mid-start, a-mid-end) move to the
            ;; trailing positions [na - a-mid-len, na) so the final
            ;; :shrink can drop them. Surviving items at [a-mid-end, na)
            ;; shift left by a-mid-len to close the gap.
            tail-start (- na a-mid-len)
            π (p/canonicalize
               (persistent!
                (reduce (fn [acc i]
                          (assoc! acc (+ a-mid-start i)
                                  (+ tail-start i)))
                        (let [base (transient {})]
                          (reduce (fn [acc i] (assoc! acc i (- i a-mid-len)))
                                  base (range a-mid-end na)))
                        (range a-mid-len))))]
        {:degree na :grow 0 :shrink a-mid-len
         :permutation π :change {} :freeze #{}})

      ;; Mixed change in the middle — fall back to naive.
      :else
      (naive-state-diff a b))))

;; =============================================================================
;; Algebra instance
;; =============================================================================

(defrecord SequenceAlgebra []
  a/DeltaAlgebra
  (-apply-deltas [_ old deltas]
    (apply-pipeline old deltas))

  (-compose-deltas [_ d1 d2]
    (let [b1 (- (:degree d1) (:shrink d1 0))
          a2 (- (:degree d2) (:grow d2 0))]
      (when (not= b1 a2)
        (throw (ex-info "Sequence diffs not composable (size mismatch)"
                        {:size-after-d1 b1 :size-before-d2 a2
                         :d1 d1 :d2 d2}))))
    (compose-pair d1 d2))

  (-empty-deltas [_ context]
    (empty-diff (:size context 0)))

  a/DeltaAlgebraEmpty?
  (-empty-deltas? [_ d]
    (and (zero? (:grow d 0))
         (zero? (:shrink d 0))
         (empty? (:permutation d {}))
         (empty? (:change d {}))
         (empty? (:freeze d #{}))))

  a/StateDiffable
  (-state-diff [_ a b _relations]
    (linear-state-diff a b)))

(def sequence-algebra
  "Singleton instance of `SequenceAlgebra`. Use as the algebra for any
   reactive value that is an ordered sequence (a Clojure vector)."
  (->SequenceAlgebra))
