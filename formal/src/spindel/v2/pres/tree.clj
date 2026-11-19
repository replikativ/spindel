(ns spindel.v2.pres.tree
  "The generic step tree (formal/notes/proof-layout.md, option A, stage 2), kernel-checked (Init only).

  The copier re-checks the composite lemmas of the base proof once per bundle. Here they are checked
  once, over an abstract rest part Q and two structures of obligations:

    Leaf Q       one field per primitive edit the tree reaches: Base and Q of the input world give Q of
                 the edited world (the prototype's GPrim, in the bare shape: no call-site context).
                 Chunked into structures of at most `chunk` fields (R1: a flat structure of 150 fields
                 of this shape does not elaborate in a 1 GB heap; chunks of 25 take seconds).
    Over Q P     one field per composite that some bundle overrides (`over-targets`, R3): the hooks
                 where a part's own proof replaces the generic one. `over-default` fills every field
                 with the generic proof (the `gqd-` copies), proved once from the leaves.

  The tree itself is the bundle `gq` (parameters Q, P : Leaf Q, O : Over Q P), copied by the copier
  once: its leaves are Leaf's fields, its override points call Over's fields, everything else is the
  generic copy. A part converted to the tree (`restate!`) builds an instance of Leaf from its primitive
  cells and restates each lemma the copier used to generate for it as an application of the generic
  lemma, with the same name and statement.

  Stage 3 adds call-site context additively: a contextual leaf is a new field whose default is the
  bare one (ignoring the context), and the tree calls it at those sites; existing instances keep
  working. The 24 call sites with path facts in scope are listed in proof-layout.md section 5b."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.inv.copier :as c]
            [spindel.v2.pres.frames :as frames]))

(def ^:private theorem-source @#'c/theorem-source)
(def ^:private eval-theorem! @#'c/eval-theorem!)
(def ^:private copy-form @#'c/copy-form)
(def ^:private source-of @#'c/source-of)
(def ^:private closure @#'c/closure)
(def ^:private inv-premise? @#'c/inv-premise?)
(defn- bnames [binders] (vec (take-nth 3 binders)))
(def chunk 20)

;; The roots of the converted parts (their former lcopy! roots) and the composites some bundle
;; overrides. `over-targets` is checked against the copier's override! calls by test/../tree_test.clj.
(def roots '[inv-end-basis inv-remove-empty-at nat-fold-inv inv-cancel-losers inv-normalize inv-job-apply
             inv-cancel-pred inv-cut-suffix inv-fire-edge])
(def over-targets
  '#{inv-await-step inv-await-wire inv-cancel-acts inv-cancel-losers inv-cancel-pred inv-cancel-run-local inv-cascade
     inv-cleanup-set inv-clear-comp-run inv-close-local inv-close-source inv-close-source0 inv-consume-entry inv-cut-suffix
     inv-debtor-side inv-deliver-res inv-demand-reactive inv-demote inv-demote-finish inv-dep-consumed inv-detach
     inv-detach-source inv-end-link inv-fill-slot inv-fin-loop inv-finalize-debtor inv-fire-dep inv-fire-edge
     inv-fire-observe inv-fire-task-cancelled inv-fire-wait inv-fire-wait-act inv-insert-edge-checked
     inv-invalidate-dependents inv-job-apply inv-norm-loop inv-norm-round inv-normalize inv-react-add inv-react-edges
     inv-react-loop inv-react-one inv-realize-link inv-remove-if-empty inv-resume inv-retire-local inv-retire-with
     inv-run-cascade})

(defn- ev [form] (eval-theorem! form))
(def ^:private declared? @#'c/declared?)
(defn- ev-struct [form] (when-not (declared? (second form)) (eval form)))

;; ---- the base predicates of a generic bundle: p [params] w = inv-sample w && rest
(defn- mk-defs! [p params pargs]
  (let [s #(symbol (str p %)) pv (vec params) app (fn [h] (concat (list h) pargs ['w]))]
    (ev (list 'a/defn (s "-rest") (conj pv 'w :- 'World) 'Bool '(Q w)))
    (ev (list 'a/defn (symbol p) (conj pv 'w :- 'World) 'Bool (list 'Bool.and '(inv-sample w) (app (s "-rest")))))
    (ev (list 'a/theorem (s "-sample") (conj pv 'w :- 'World) (list '=> (list '= (app (symbol p)) true) '(= (inv-sample w) true))
              '(intro h) (list 'simp 'only [(symbol p) 'Bool.and_eq_true] 'at 'h) '(exact (And.left h))))
    (ev (list 'a/theorem (s "-rest-of") (conj pv 'w :- 'World) (list '=> (list '= (app (symbol p)) true) (list '= (app (s "-rest")) true))
              '(intro h) (list 'simp 'only [(symbol p) 'Bool.and_eq_true] 'at 'h) '(exact (And.right h))))
    (ev (list 'a/theorem (s "-intro") (conj pv 'w :- 'World) (list '=> '(= (inv-sample w) true) (list '= (app (s "-rest")) true) (list '= (app (symbol p)) true))
              '(intros h1 h2) (list 'simp 'only [(symbol p) 'h1 'h2 'Bool.and_self])))
    (ev (list 'a/theorem (s "-parts") (conj pv 'w :- 'World)
              (list '=> (list '= (app (symbol p)) true) '(And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
              '(intro h) (list 'exact (list 'inv-parts 'w (concat (list (s "-sample")) pargs ['w 'h])))))))

;; ---- leaves
(defn leaf-info [orig]
  (let [[_ _ binders stmt] (theorem-source orig) prems (vec (butlast (rest stmt))) concl (last stmt)
        i (first (keep-indexed (fn [i p] (when (inv-premise? p) i)) prems))]
    {:binders binders :prems prems :i i :w (second (second (nth prems i))) :w2 (second (second concl))}))
(defn- fsym [o] (symbol (str "o-" (name o))))
(defn- chunks [xs] (vec (partition-all chunk xs)))
(defn- cname [base k] (symbol (str base (char (+ 65 k)))))
(defn- acc [base k fld obj] (list (symbol (str (cname base k) "." (name fld))) (list (symbol (str base "." (char (+ 97 k)))) obj)))

(defonce tree (atom nil))   ; {:leaves [..] :over [..] :lchunks .. :ochunks ..}

(defn- leaf-field [o]
  (let [{:keys [binders prems w w2]} (leaf-info o)]
    (list (fsym o) (list 'forall binders (concat ['=>] prems [(list '= (list 'Q w) true) (list '= (list 'Q w2) true)])))))
(defn- leaf-acc [o] (let [{:keys [lchunks]} @tree k (first (keep-indexed (fn [k ch] (when (some #{o} ch) k)) lchunks))]
                      (acc "Leaf" k (fsym o) 'P)))
(defn- leaf-rest-f [p pargs o]
  (let [{:keys [binders prems i w]} (leaf-info o) hs (vec (map-indexed (fn [j _] (symbol (str "h" j))) prems))]
    (apply list (leaf-acc o) (concat (bnames binders) (assoc hs i (concat (list (symbol (str p "-sample"))) pargs [w (nth hs i)])) ['R]))))

(defn build!
  "Elaborate the generic tree once: Leaf, the default copy gqd, Over and over-default, and gq."
  []
  (let [prims (set (keys @frames/footprints))
        GD (c/mk-bundle 'gqd '[Q :- (=> World Bool), P :- (Leaf Q)] "gqd-" {})
        probe (c/mk-bundle 'gqd '[] "gqd-" {})
        _ (swap! (:renames probe) merge (zipmap prims prims) {'inv-parts 'inv-parts})
        union (set (mapcat #(closure probe %) roots))
        leaves (vec (sort (filter prims union)))
        comps (set (remove prims union))
        over (vec (sort (filter over-targets comps)))
        lch (chunks leaves) och (chunks over)]
    (reset! tree {:leaves leaves :over over :lchunks lch :ochunks och :composites comps})
    ;; Leaf Q
    (doseq [[k ch] (map-indexed vector lch)]
      (ev-struct (apply list 'a/structure (cname "Leaf" k) '[Q (=> World Bool)] (map leaf-field ch))))
    (ev-struct (apply list 'a/structure 'Leaf '[Q (=> World Bool)]
                 (for [k (range (count lch))] (list (symbol (str (char (+ 97 k)))) (list (cname "Leaf" k) 'Q)))))
    ;; the default copy: every composite of the tree, generic in Q, P
    (mk-defs! "gqd" (:params GD) '[Q P])
    (swap! (:renames GD) assoc 'inv-parts 'gqd-parts)
    (doseq [o leaves :when (not= o 'inv-parts)] (c/prim! GD o (leaf-rest-f "gqd" '[Q P] o)))
    (doseq [r roots] (c/lcopy! GD r))
    ;; Over Q P: the override points, with the default copy's statements
    (let [stmt (fn [x] (let [[_ _ binders st] (copy-form GD (source-of GD x) 'x @(:renames GD))]
                         [(vec (drop 6 binders)) st]))]
      (doseq [[k ch] (map-indexed vector och)]
        (ev-struct (apply list 'a/structure (cname "Over" k) '[Q (=> World Bool) P (Leaf Q)]
                     (for [x ch :let [[bs st] (stmt x)]] (list (fsym x) (list 'forall bs st))))))
      (ev-struct (apply list 'a/structure 'Over '[Q (=> World Bool) P (Leaf Q)]
                   (for [k (range (count och))] (list (symbol (str (char (+ 97 k)))) (list (cname "Over" k) 'Q 'P)))))
      (ev (list 'a/defn 'over-default '[Q :- (=> World Bool), P :- (Leaf Q)] '(Over Q P)
                  (apply list 'Over.mk
                         (for [[k ch] (map-indexed vector och)]
                           (apply list (symbol (str (cname "Over" k) ".mk"))
                                  (for [x ch :let [[bs _] (stmt x)]]
                                    (list 'fn bs (apply list (get @(:renames GD) x) 'Q 'P (bnames bs))))))))))
    ;; gq: the tree, its leaves calling Leaf, its override points calling Over
    (let [GQ (c/mk-bundle 'gq '[Q :- (=> World Bool), P :- (Leaf Q), O :- (Over Q P)] "gq-" {})
          oacc (fn [x] (let [k (first (keep-indexed (fn [k ch] (when (some #{x} ch) k)) och))] (acc "Over" k (fsym x) 'O)))]
      (mk-defs! "gq" (:params GQ) '[Q P O])
      (swap! (:renames GQ) assoc 'inv-parts 'gq-parts)
      (doseq [o leaves :when (not= o 'inv-parts)]
        (c/prim! GQ o (leaf-rest-f "gq" '[Q P O] o)))
      (doseq [x over]
        (let [[_ _ binders st] (copy-form GQ (source-of GQ x) 'x @(:renames GQ))
              nm (@#'c/copy-name GQ x)]
          (c/override! GQ x [] (list 'a/theorem nm binders st (list 'exact (apply list (oacc x) (bnames (drop 9 binders))))))))
      (doseq [r roots] (c/lcopy! GQ r))
      ;; composites reached only through override points (whose deps are the Over fields): copy them
      ;; too, so every composite of the tree has its gq- lemma
      (doseq [x (sort comps)] (c/lcopy! GQ x))
      (swap! tree assoc :GQ GQ :GD GD))
    @tree))

;; ---- a part converted to the tree
(defn- field-proof [B o]
  (let [{:keys [binders prems i w w2]} (leaf-info o) hs (vec (map-indexed (fn [j _] (symbol (str "h" j))) prems))
        pn (bnames (:params B)) b (fn [s] (symbol (str (name (:pred B)) s)))
        cell (get @(:renames B) o)]
    (list 'fn (vec (concat binders (mapcat (fn [h p] [h :- p]) hs prems) ['hq :- (list '= (concat (list (b "-rest")) pn [w]) true)]))
          (concat (list (b "-rest-of")) pn [w2]
                  [(apply list cell (concat pn (bnames binders) (assoc hs i (concat (list (b "-intro")) pn [w (nth hs i) 'hq]))))]))))

(defn restate!
  "Convert bundle B to the tree: its Leaf instance `pname` (from its primitive cells; a missing cell
  of a frame is generated), and every lemma the copier would generate for B from `broots`, restated
  with its old name and statement and proved by the generic lemma."
  [B pname broots]
  (let [{:keys [leaves lchunks GQ]} @tree
        pv (vec (:params B)) pn (bnames pv)
        Q (concat (list (symbol (str (name (:pred B)) "-rest"))) pn)
        Q (if (seq pn) Q (first Q))]
    ;; a leaf B has no cell for: copy its base proof for B (a primitive proved through others, e.g.
    ;; insert-edge-checked), or else an rfl frame cell
    (doseq [o leaves :when (and (not= o 'inv-parts) (not (contains? @(:renames B) o)))]
      (when (seq (c/lcopy-try! B o)) (c/prim! B o nil)))
    (ev (list 'a/defn pname pv (list 'Leaf Q)
              (apply list 'Leaf.mk (for [[k ch] (map-indexed vector lchunks)]
                                     (apply list (symbol (str (cname "Leaf" k) ".mk")) (map #(field-proof B %) ch))))))
    (let [P (if (seq pn) (apply list pname pn) pname)
          names (vec (for [r broots, x (closure B r) :when (not (contains? @(:renames B) x))] x))]
      (doseq [x (distinct names)]
        (let [[_ nm binders st] (copy-form B (source-of B x) (@#'c/copy-name B x) @(:renames B))]
          (ev (list 'a/theorem nm binders st
                    (list 'exact (apply list (get @(:renames GQ) x) Q P (list 'over-default Q P) (bnames (drop (count pv) binders))))))
          (swap! (:renames B) assoc x nm)
          (swap! (:copied B) conj nm)))
      (count (distinct names)))))
(build!)
