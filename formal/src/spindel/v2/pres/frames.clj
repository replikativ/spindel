(ns ^:ansatz/lean spindel.v2.pres.frames
  "Frames from views (formal/notes/proof-layout.md, option B), kernel-checked (Init only).

  A part of the invariant survives a primitive edit as a *frame* when the edit writes no World field
  the part reads. This namespace states both halves once:

    footprints  what each primitive edit writes. `writes-<edit>`: the edited world equals the input
                world with only the written fields replaced, e.g.
                  writes-mark-edge : mark-edge w x = set-comps (set-edges w (:edges (mark-edge w x)))
                                                              (:comps (mark-edge w x))
                Most are `rfl`; the edge edits defined by `match` and the checked insert by `if` are
                proved by cases. `footprints` is the same table as data, keyed by the base lemma of
                the primitive (the name the copier knows it by).
    views       what a part reads. `defview` declares the World fields a part's rest predicate reads
                and states, for every other field f, `<rest>-frame-<f> : rest (set-f w v) = rest w`
                (by `rfl`: the kernel checks that the rest predicate does not look at f).

  `frame-term` composes the two into a proof of `rest (edit w ...) = rest w` for an edit whose
  footprint misses the view: `writes-<edit>`, then one frame lemma per written field. spindel.v2.pres.part
  uses it for the frame cells of a part declared with a view (`frame!`, `defpart`), instead of a
  hand-written `nil` cell or a hand-written frame lemma.

  Fields are named as in `World` (state.clj): scopes comps tasks runs sources edges acts res cleanup
  pubs pins forks pending-act released next-id."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]))

(def world-fields
  '[scopes comps tasks runs sources edges acts res cleanup pubs pins forks pending-act released next-id])

(def ^:private field-types
  '{scopes (List ScopeRow) comps (List CompRow) tasks (List TaskRow) runs (List RunRow)
    sources (List SourceRow) edges (List EdgeRow) acts (List ActRow) res (List ResRow)
    cleanup (List CleanupRow) pubs (List PubRow) pins (List Nat) forks (List ForkRow)
    pending-act Nat released Bool next-id Nat})

(defn- setter [f] (symbol (str "set-" f)))
(defn- proj [f x] (list (keyword f) x))

(defn replaced
  "The world `w` with the fields `fs` (outermost first) set to their values in `w2`:
  (set-f1 (set-f2 w (:f2 w2)) (:f1 w2))."
  [w w2 fs]
  (reduce (fn [acc f] (list (setter f) acc (proj f w2))) w (reverse fs)))

(def ^:private frames-ns *ns*)
(defn- eval-here [form] (binding [*ns* frames-ns] (eval form)))

;; ===========================================================================
;; Footprints: what each primitive edit writes
;; ===========================================================================

;; base lemma of the primitive -> {:lemma writes-<edit>, :writes [fields, outermost first],
;;                                  :binders [..], :edit form}
(defonce footprints (atom {}))

(defmacro ^:private defwrites
  "`writes-<nm>`: the edit `edit` (over the binders) equals `w` with only `fields` replaced. The base
  lemma `base` of the primitive is recorded in `footprints`. The proof is `rfl` unless given."
  [base nm binders edit fields & proof]
  (let [lemma (symbol (str "writes-" nm))]
    `(do (a/theorem ~lemma ~binders (~'= ~edit ~(replaced 'w edit fields)) ~@(or (seq proof) ['(rfl)]))
         (swap! footprints assoc '~base {:lemma '~lemma :writes '~fields :binders '~binders :edit '~edit}))))

;; one-table row edits
(defwrites well-formed-scope-upd scope-upd [w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow)] (scope-upd w x f) [scopes])
(defwrites well-formed-close-scope-id close-scope-id [w :- World, x :- Nat] (close-scope-id w x) [scopes])
(defwrites well-formed-scope-del scope-del [w :- World, x :- Nat] (scope-del w x) [scopes])
(defwrites well-formed-comp-upd comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow)] (comp-upd w x f) [comps])
(defwrites well-formed-comp-del-unref comp-del [w :- World, x :- Nat] (comp-del w x) [comps])
(defwrites well-formed-task-upd task-upd [w :- World, x :- Nat, f :- (=> TaskRow TaskRow)] (task-upd w x f) [tasks])
(defwrites well-formed-run-upd run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow)] (run-upd w x f) [runs])
(defwrites well-formed-run-del run-del [w :- World, x :- Nat] (run-del w x) [runs])
(defwrites well-formed-source-upd source-upd [w :- World, x :- Nat, f :- (=> SourceRow SourceRow)] (source-upd w x f) [sources])
(defwrites well-formed-edge-upd edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow)] (edge-upd w x f) [edges])
(defwrites well-formed-act-upd act-upd [w :- World, x :- Nat, f :- (=> ActRow ActRow)] (act-upd w x f) [acts])
(defwrites well-formed-resource-upd resource-upd [w :- World, x :- Nat, f :- (=> ResRow ResRow)] (resource-upd w x f) [res])
(defwrites well-formed-resource-del resource-del [w :- World, x :- Nat] (resource-del w x) [res])
(defwrites well-formed-cleanup-upd cleanup-upd [w :- World, x :- Nat, f :- (=> CleanupRow CleanupRow)] (cleanup-upd w x f) [cleanup])
(defwrites well-formed-cleanup-del cleanup-del [w :- World, x :- Nat] (cleanup-del w x) [cleanup])
(defwrites well-formed-cleanup-ins cleanup-ins [w :- World, r :- CleanupRow] (cleanup-ins w r) [cleanup])
(defwrites well-formed-pub-upd pub-upd [w :- World, x :- Nat, f :- (=> PubRow PubRow)] (pub-upd w x f) [pubs])
(defwrites well-formed-fork-del fork-del [w :- World, x :- Nat] (fork-del w x) [forks])

;; inserts with a fresh id: the row and the allocator
(defwrites well-formed-scope-ins-fresh scope-ins-fresh [w :- World, r :- ScopeRow] (bump (scope-ins w r)) [scopes next-id])
(defwrites well-formed-comp-ins-fresh comp-ins-fresh [w :- World, r :- CompRow] (bump (comp-ins w r)) [comps next-id])
(defwrites well-formed-task-ins-fresh task-ins-fresh [w :- World, r :- TaskRow] (bump (task-ins w r)) [tasks next-id])
(defwrites well-formed-run-ins-fresh run-ins-fresh [w :- World, r :- RunRow] (bump (run-ins w r)) [runs next-id])
(defwrites well-formed-source-ins-fresh source-ins-fresh [w :- World, r :- SourceRow] (bump (source-ins w r)) [sources next-id])
(defwrites well-formed-act-ins-fresh act-ins-fresh [w :- World, r :- ActRow] (bump (act-ins w r)) [acts next-id])
(defwrites well-formed-resource-ins-fresh resource-ins-fresh [w :- World, r :- ResRow] (bump (resource-ins w r)) [res next-id])
(defwrites well-formed-fork-ins-fresh fork-ins-fresh [w :- World, r :- ForkRow] (bump (fork-ins w r)) [forks next-id])
(defwrites well-formed-insert-edge-fresh insert-edge-fresh [w :- World, e :- EdgeRow] (insert-edge-fresh w e) [edges next-id])
(defwrites well-formed-insert-edge-checked insert-edge-checked [w :- World, e :- EdgeRow] (insert-edge-checked w e) [edges next-id]
  (cases hk (edge-ok-in w e))
  (all_goals (simp only [insert-edge-checked hk])))

;; the allocator and the scalar fields
(defwrites well-formed-bump bump [w :- World] (bump w) [next-id])
(defwrites well-formed-set-pins set-pins [w :- World, v :- (List Nat)] (set-pins w v) [pins])
(defwrites well-formed-set-pending-act set-pending-act [w :- World, v :- Nat] (set-pending-act w v) [pending-act])
(defwrites well-formed-set-released set-released [w :- World, v :- Bool] (set-released w v) [released])

;; edge edits that adjust the creditor's pending count: edges and computations
(defwrites well-formed-mark-edge mark-edge [w :- World, x :- Nat] (mark-edge w x) [comps edges]
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(defwrites well-formed-unmark-edge unmark-edge [w :- World, x :- Nat] (unmark-edge w x) [comps edges]
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(defwrites well-formed-remove-edge remove-edge [w :- World, x :- Nat] (remove-edge w x) [comps edges]
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))
(defwrites well-formed-drop-cred-edges drop-cred-edges [w :- World, a :- Nat] (drop-cred-edges w a) [comps edges])
(defwrites well-formed-drop-edges drop-edges [w :- World, p :- (=> EdgeRow Bool)] (drop-edges w p) [comps edges])
(defwrites well-formed-drop-act drop-act [w :- World, a :- Nat] (drop-act w a) [acts comps edges])

;; Rule R's filter: every row table except cleanup (a part that reads only the scalar fields or the
;; cleanup table has it as a frame)
(defwrites well-formed-filter-world filter-world [w :- World, K :- (=> Nat Bool)] (filter-world K w)
  [scopes comps tasks runs sources edges acts res pubs forks])

;; ===========================================================================
;; Views: what a part reads
;; ===========================================================================

;; rest predicate -> {:params [sym type ...], :reads #{fields}}
(defonce views (atom {}))

(defn frame-lemma [rest f] (symbol (str rest "-frame-" f)))

(defn defview
  "Declare that the rest predicate `rest` (with bundle parameters `params`, as in mk-bundle) reads only
  the World fields `reads`. States and checks `<rest>-frame-<f>` for every other field f:
  (= (rest params (set-f w v)) (rest params w)), by `rfl`."
  [rest params reads]
  (let [reads (set reads)
        unknown (remove (set world-fields) reads)
        pn (vec (take-nth 3 params))]
    (assert (empty? unknown) (str "defview " rest ": unknown fields " (vec unknown)))
    (doseq [f world-fields :when (not (reads f))]
      (eval-here
       (list 'ansatz.core/theorem (frame-lemma rest f)
             (into (vec params) ['w :- 'World 'v :- (field-types f)])
             (list '= (apply list rest (concat pn [(list (setter f) 'w 'v)])) (apply list rest (concat pn ['w])))
             '(rfl))))
    (swap! views assoc rest {:params params :reads reads})
    rest))

(defn frame?
  "Is the primitive (by its base lemma) a frame for the rest predicate's view?"
  [rest base]
  (let [v (get @views rest) fp (get @footprints base)]
    (boolean (and v fp (:lemma fp) (not-any? (:reads v) (:writes fp))))))

(defn frame-term
  "A proof of (= (rest pargs w2) (rest pargs w)), where w2 is the primitive `base` applied (the
  edited world, as an expression over w) and `args` the arguments of its writes lemma, or nil if
  the primitive's footprint meets the view."
  [rest pargs base w w2 args]
  (when (frame? rest base)
    (let [{:keys [lemma writes]} (get @footprints base)
          app (fn [& xs] (apply list rest (concat pargs xs)))
          ;; the worlds between: (set-f1 (set-f2 w ..) ..): inner-i has the fields after i replaced
          inner (fn [i] (replaced w w2 (drop i writes)))
          chain (reduce (fn [acc i]
                          (let [f (nth writes i)
                                step (apply list (frame-lemma rest f) (concat pargs [(inner (inc i)) (proj f w2)]))]
                            (if acc (list 'Eq.trans acc step) step)))
                        nil (range (count writes)))]
      (list 'Eq.trans (list 'congrArg (list 'fn ['fw :- 'World] (apply app ['fw])) (apply list lemma args)) chain))))

(defn frame-theorem!
  "State and check `nm : rest params (edit ...) = rest params w` for the primitive `base`, proved by
  `frame-term` (its footprint and the view of `rest`). Used for the per-edit frame lemmas that parts
  had written by hand (e.g. `i1-scopes-rest-mark-edge`), so they keep their names and statements."
  [nm rest base]
  (let [{:keys [params]} (get @views rest)
        {:keys [binders edit]} (get @footprints base)
        pn (vec (take-nth 3 params))
        args (vec (take-nth 3 binders))
        t (or (frame-term rest pn base 'w edit args)
              (throw (ex-info (str nm ": " base " is not a frame of " rest) {:rest rest :base base})))]
    (eval-here
     (list 'ansatz.core/theorem nm (into (vec params) binders)
           (list '= (apply list rest (concat pn [edit])) (apply list rest (concat pn ['w])))
           (list 'exact t)))
    nm))
