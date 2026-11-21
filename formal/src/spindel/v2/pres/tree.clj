(ns spindel.v2.pres.tree
  "The generic step tree (formal/notes/proof-layout.md §5c, §5d), kernel-checked (Init only).

  Every composite lemma x of the base proof is checked once, over an abstract rest part Q, by open
  recursion: `pres-x` takes one hypothesis per lemma x's proof calls (S c over Q: c's statement with
  well-formed replaced by `gp Q`, Base and Q) and proves S x over Q by x's base proof. A part restates
  each lemma the copier used to generate for it, under the old name and statement, as pres-x applied
  to the part's lemma for every callee (`restate!`). Its table (`part!`) says where that is not
  enough:

    :over   x -> the part's own proof of x (content: a deferred violation, an argument over edits).
    :sites  an update primitive, or a composite taking a row function (`serve-or`), is one callee
            per row function; [p F] -> the part's proof there (default: its cell, with the bundle's
            extra argument and the site's facts). A :ctx or :pass row keyed by p alone holds at
            every site of p.
    :ctx    x or [p F] -> the facts from the path the part's own proof (or site entry) takes there.
    :own    x -> facts a node takes from above it and passes on, named: [h fact ...].
    :pass   caller -> callee or [p F] -> the terms the caller passes for those facts, over its locals.
            Forwarding is inferred (`infer`): a caller with no :pass for such a callee, whose call
            arguments the facts mention are its own binders, takes the facts itself and passes them.
    :gates  a gate node (`gates`) whose continuation takes the gate's fact, named.
    :src    x -> the part's proof of x where passes are not enough (base vocabulary).

  The facts are the part's, in its own vocabulary. A node whose proof passes or takes such facts
  (or calls a gate the part takes) gets the part's own generic lemma `pres-x@<part>`, generated from
  the base proof with the part's passes; every other node uses the shared `pres-x`. So a part's
  facts reach only its own lemmas, and a reader finds all of them in the part's table.

  A part may be parameterised (g8's x8s, g7's companions comp-awake-owns-run awc awr and alive-runs-listed kc0 kl0 kd0): its
  predicate is Q := (B p) for the fixed parameters p, which every restated lemma takes first, as the
  copier's lemmas did. The shared generic lemmas do not see them; the part's own (pres-x@<part>)
  take them after Q, so that the part's facts may mention them (g10's job condition names its
  exempt lists). A part that is another part at fixed parameters (i1-runs = i1-runs-exempt []) uses that part's
  lemmas as its cells: the bundle's extra argument in first position (`(grx-x (List.nil Nat))`).

  transition, the item dispatcher, is cut by item: the tree derives `raw0-<item>-inv` from raw0-inv's base
  proof (one branch each) and proves well-formed-transition by dispatching to them, so a part that passes into one
  transition regenerates one branch, not the dispatcher (`raw0-split`)."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.pres.part :as c]
            [spindel.v2.pres.frames :as frames]
            [spindel.v2.pres.exempt :as exempt]))

(def ^:private base-theorem-source @#'c/theorem-source)
;; lemmas the tree derives from a base proof (raw0's branches, below), by name
(defonce ^:private derived (atom {}))
(declare fill-rows)
(defn- theorem-source [x] (some-> (or (get @derived x) (base-theorem-source x)) fill-rows))
(def ^:private eval-theorem! @#'c/eval-theorem!)
(def ^:private copy-form @#'c/copy-form)
(def ^:private copy-name @#'c/copy-name)
(def ^:private inv-premise? @#'c/inv-premise?)
(def ^:private declared? @#'c/declared?)
(defn- bnames [binders] (vec (take-nth 3 binders)))
(defn- ev [form] (eval-theorem! form))

;; ===========================================================================
;; The generic part: gp Q w = Base w and Q w
;; ===========================================================================

(ev '(a/defn gp [Q :- (=> World Bool), w :- World] Bool (Bool.and (well-formed w) (Q w))))
(ev '(a/theorem gp-well-formed [Q :- (=> World Bool), w :- World] (=> (= (gp Q w) true) (= (well-formed w) true))
       (intro h) (simp only [gp Bool.and_eq_true] at h) (exact (And.left h))))
(ev '(a/theorem gp-parts [Q :- (=> World Bool), w :- World]
       (=> (= (gp Q w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
       (intro h) (exact (well-formed-parts w (gp-well-formed Q w h)))))

;; ===========================================================================
;; The tree's own declarations
;; ===========================================================================

;; Callees dispatched per row function (or per inserted row or edge), with that argument's position.
;; A part's fact or extra argument may then depend on the row: an inserted edge is a site so that a
;; bundle's `edge-new-ok` is rfl at a concrete edge (i7-idle).
(def dispatched '{well-formed-run-upd 2 well-formed-task-upd 2 well-formed-resource-upd 2 well-formed-source-upd 2 well-formed-scope-upd 2 well-formed-serve-or 3
                  well-formed-scope-ins-fresh 1 well-formed-comp-upd 2 well-formed-comp-ins-fresh 1 well-formed-insert-edge-fresh 1
                  well-formed-insert-edge-checked 1 well-formed-cleanup-upd 2 well-formed-act-upd 2 well-formed-edge-upd 2
                  well-formed-source-ins-fresh 1 well-formed-task-ins-fresh 1 well-formed-edge-set-phase 2 well-formed-run-ins-fresh 1})

;; A computation edit is one site per row function: its arguments are the site's parameters
;; (`site-gen`, named as the binders of the function's id lemma `<f>-comp-id` / `<f>-id`), so a part
;; states it once, e.g. [well-formed-comp-upd (comp-start-row rid)]. A row function the base proof leaves to
;; unification (`_`) is read off that id lemma, its next argument, as the copier's bundles did.
(defn- id-lemma-row [sufs hid]
  (let [h (if (seq? hid) (first hid) hid) n (name h)
        base (some #(when (str/ends-with? n %) (subs n 0 (- (count n) (count %)))) sufs)]
    (when (and base (base-theorem-source h)) [(symbol base) h])))

(defn- gen? [F] (and (seq? F) (= 'site-gen (first F))))
(def ^:private comp-upd-binders '#{w x f hid hp})

(defn- generic-row
  "F as a site generic in its arguments: (site-gen [params] (f params) args), params named as f's id
  lemma's binders (renamed apart from inv-comp-upd's)."
  [F hid]
  (if-let [[f idl] (id-lemma-row ["-comp-id" "-id"] hid)]
    (let [args (cond (seq? F) (vec (rest F)) (= '_ F) (if (seq? hid) (vec (rest hid)) []) :else [])
          [_ _ bs] (base-theorem-source idl)
          ps (vec (take (* 3 (count args)) bs))
          ps (vec (map-indexed (fn [i y] (if (and (zero? (mod i 3)) (comp-upd-binders y)) (symbol (str (name y) "0")) y)) ps))]
      (if (seq args) (list* 'site-gen ps (apply list f (take-nth 3 ps)) args) f))
    F))

(defn- fill-rows [form]
  (walk/prewalk (fn [y] (cond (not (seq? y)) y
                              (and (= 'well-formed-comp-upd (first y)) (or (= '_ (nth y 3 nil)) (seq? (nth y 3 nil))) (not (gen? (nth y 3 nil))))
                              (apply list (assoc (vec y) 3 (generic-row (nth y 3) (nth y 4 nil))))
                              :else y))
                form))

;; transition by item. raw0-inv's base proof is one `cases it` over the 49 items, each branch the item's
;; guard (if any) and its transition. A part that passes a fact into one transition would need its
;; own copy of the whole dispatcher; so the tree cuts raw0's base proof into one lemma per item,
;; `raw0-<item>-inv` (the branch's tactics, found by counting the goals they open and close), checks
;; each for well-formed, and proves well-formed-transition by dispatching to them (`sources`). A part then gets its
;; own lemma only for the branches it passes into. raw0-inv's statement is the base one.
(defn- item-ctors []
  (let [[_ _ _ & ctors] (first (filter #(and (seq? %) (= 'a/inductive (first %)) (= 'Item (second %)))
                                       (@#'c/ns-source-forms 'spindel.v2.step)))]
    (for [[nm & fields] ctors] [nm (mapv (fn [[f t]] [f t]) fields)])))

(defn- raw0-branches
  "[ctor fields segment] per item: raw0-inv's tactics for that item, rename_i dropped (its names
  become the fields' names)."
  []
  (let [[_ _ _ _ & proof] (base-theorem-source 'well-formed-transition)
        _ (assert (= (take 3 proof) '((intro h) (cases it) (all_goals (simp only [transition])))))]
    (loop [tacs (drop 3 proof) ctors (item-ctors) acc []]
      (if-let [[nm fields] (first ctors)]
        (let [[seg rest-tacs]
              (loop [ts tacs open 1 seg []]
                (if (zero? open) [seg ts]
                    (let [[t & more] ts]
                      (recur more (case (first t) cases (inc open) exact (dec open) open) (conj seg t)))))
              ren (some #(when (= 'rename_i (first %)) (rest %)) seg)
              fields (if ren (mapv (fn [n [_ ty]] [n ty]) ren fields) fields)]
          (recur rest-tacs (rest ctors) (conj acc [nm fields (remove #(= 'rename_i (first %)) seg)])))
        (do (assert (empty? tacs)) acc)))))

(defn- transition-branch-name [ctor] (symbol (str "well-formed-transition-" (name ctor))))

(defn- raw0-branch-form [[ctor fields seg]]
  (let [item (if (seq fields) (apply list (symbol (str "Item." (name ctor))) (map first fields)) (symbol (str "Item." (name ctor))))]
    (apply list 'a/theorem (transition-branch-name ctor) (vec (concat '[w :- World] (mapcat (fn [[f t]] [f :- t]) fields)))
           (list '=> '(= (well-formed w) true) (list '= (list 'well-formed (list :world (list 'transition 'w item))) true))
           '(intro h) '(simp only [transition]) seg)))

(defn- raw0-dispatch [branches]
  (let [[hd nm binders stmt] (base-theorem-source 'well-formed-transition)]
    (apply list hd nm binders stmt '(intro h) '(cases it)
           (for [[ctor fields] branches]
             (list 'exact (apply list (transition-branch-name ctor) (concat ['w] (repeat (count fields) '_) ['h])))))))

(def ^:private raw0-split
  (let [bs (raw0-branches)]
    (reset! derived (into {} (for [b bs] [(transition-branch-name (first b)) (raw0-branch-form b)])))
    {:branches bs :dispatch (raw0-dispatch bs)}))

;; Sources: nodes whose generic proof is not their base proof: a row function (or a cascade's job
;; list) the base proof leaves to unification is named. One that mentions a local of the proof is generalized (`site-gen`: the
;; site is stated for every value of the parameter: T-open-scope's parent, T-finally-enter's
;; finalizer).
(defn- name-row-fn [x p F]
  (let [i (inc (dispatched p))]
    (walk/prewalk (fn [y] (if (and (seq? y) (= p (first y)) (= '_ (nth y i nil))) (apply list (assoc (vec y) i F)) y))
                  (theorem-source x))))

;; a cascade of one retire or close job: the base proof leaves the job list (and sometimes the world) to
;; unification; named, so that a part's job condition can be passed by computation (g10's `job-ok`)
(defn- name-cascade [x w js]
  (walk/prewalk (fn [y] (if (and (seq? y) (= 'well-formed-run-cascade (first y))) (let [[hd _ _ h] y] (list hd w js h)) y))
                (theorem-source x)))

(def sources
  {'well-formed-transition (:dispatch raw0-split)
   'well-formed-t16-close-scope (name-cascade 'well-formed-t16-close-scope 'w '(List.cons Job (Job.jclose s) (List.nil Job)))
   'well-formed-t15-resource-ack (name-cascade 'well-formed-t15-resource-ack '(ack-raw w z (:owner zr)) '(List.cons Job (Job.jretire (:owner zr)) (List.nil Job)))
   'well-formed-t-slice-exit (name-cascade 'well-formed-t-slice-exit '(run-upd w rid run-fin-pop-end) '(List.cons Job (Job.jretire rid) (List.nil Job)))
   'well-formed-t21-release-world (name-cascade 'well-formed-t21-release-world '(zero-handles (revoke-roots w)) '(List.cons Job (Job.jclose root-scope-id) (List.nil Job)))
   'well-formed-retire-one (name-cascade 'well-formed-retire-one '(retire-pre w r) '(List.cons Job (Job.jretire rid) (List.nil Job)))
   'well-formed-link-demand-raw (name-row-fn 'well-formed-link-demand-raw 'well-formed-source-upd '(link-set-rtask (:next-id w)))
   'well-formed-take-park (name-row-fn 'well-formed-take-park 'well-formed-insert-edge-checked '(take-edge r (:next-id w) x))
   'well-formed-react-add (name-row-fn 'well-formed-react-add 'well-formed-insert-edge-checked '(valid-edge w c v))
   'well-formed-await-step (name-row-fn 'well-formed-await-step 'well-formed-insert-edge-checked '(await-edge (:world acc) r a mode k d))
   'well-formed-t-open-scope
   (walk/postwalk-replace
    {'(ScopeRow.mk s (cur-scope w r) scope-explicit true)
     '(site-gen [p :- Nat] (ScopeRow.mk s p scope-explicit true) (cur-scope w r))}
    (theorem-source 'well-formed-t-open-scope))
   'well-formed-t-finally-enter
   (walk/postwalk-replace
    {'(well-formed-run-upd w (:id r) _ (run-fin-push-id _) h)
     '(well-formed-run-upd w (:id r) (site-gen [fz :- Finalizer] (run-fin-push fz) (Finalizer.mk 0 (:effect-index r) (List.nil Nat)))
        (run-fin-push-id (Finalizer.mk 0 (:effect-index r) (List.nil Nat))) h)}
    (theorem-source 'well-formed-t-finally-enter))})

;; Gates: a node whose last premise is a continuation (the item's world) that runs only past a
;; guard. For a part that takes the gate, the continuation receives the guard's fact: the gate's
;; statement and proof are :src, and its callers' continuations become `(fn [name :- _] ...)`.
(def gates
  '{well-formed-require-root-open
    {:src (a/theorem well-formed-require-root-open [w :- World, b :- Bool, o :- Outcome]       ; C0: transition runs a link-creating
            (=> (= (well-formed w) true) (=> (= (root-open-if b w) true) (= (well-formed (:world o)) true))  ; item only
                (= (well-formed (:world (require-root-open w b o))) true))               ; while the root scope is open
            (intros h ho)
            (cases hg (root-open-if b w))
            (simp only [require-root-open hg refuse]) (exact h)
            (simp only [require-root-open hg]) (exact (ho hg)))}})

;; ===========================================================================
;; Generation
;; ===========================================================================

(def ^:private S0 (delay (set (keep (fn [[n g]] (when (@#'c/statement-mentions-inv? g) n)) @@#'c/source-theorems))))
(def ^:private S (delay (into @S0 (keys @derived))))
;; the lemmas in load order: the base sources, raw0's branches just before well-formed-transition
(def ^:private order
  (delay (vec (mapcat (fn [[n _]] (if (= n 'well-formed-transition) (concat (map first (sort-by key @derived)) [n]) [n]))
                      @@#'c/source-theorems))))

;; pred -> the part's table (see part!)
(defonce parts (atom {}))
(defn- pt [B k] (when B (get-in @parts [(:pred B) k])))

(defn- insert-before-inv [stmt prems]
  (let [[_ & xs] stmt ps (butlast xs)
        i (first (keep-indexed (fn [i p] (when (inv-premise? p) i)) ps))]
    (concat ['=>] (take i ps) prems (drop i ps) [(last xs)])))

;; a site's row function: a form, or (site-gen [params] pattern value...) when it mentions a local of
;; the proof (the site is then stated for every value of the params)
(defn- site-key [F] (if (gen? F) (nth F 2) F))
(defn- site-params [F] (if (gen? F) (second F) []))
(defn- site-vals [F] (if (gen? F) (drop 3 F) []))
(defn- sanitize [F] (-> (pr-str F) (str/replace #"[()\[\]:]" "") (str/replace #"\s+" "-") (str/replace #"[^A-Za-z0-9-]" "")))
(defn- hyp-name [c] (symbol (str "pc-" (name c))))
(defn- site-name [p F] (symbol (str "pc-" (name p) "@" (sanitize (site-key F)))))

(defn- gated? [B x] (contains? (pt B :gates) x))

;; ---- forwarding, inferred: a node that calls a callee taking B's fact P, with no :pass for it,
;; and whose call's arguments that P mentions are its own binders, takes P itself (a fresh name)
;; and passes it on; its callers repeat. An explicit :pass stops it. (proof-layout.md §5g)

(declare tree)
(defn- base-form [x] (or (get sources x) (theorem-source x)))
(defn- binder-names-of [c] (bnames (nth (theorem-source c) 2)))

(defn- calls-in
  "The calls in x's base proof: [key args], key a callee or [p F] for a site."
  [x]
  (let [out (atom [])]
    (walk/prewalk (fn [y]
                    (when (and (seq? y) (symbol? (first y)))
                      (let [h (first y)]
                        (cond (dispatched h) (swap! out conj [[h (site-key (nth (rest y) (dispatched h) nil))] (vec (rest y))])
                              (and (@S h) (not= h x) (not= h 'well-formed-parts)) (swap! out conj [h (vec (rest y))]))))
                    y)
                  (drop 4 (base-form x)))
    @out))

(defn- instantiate
  "Fact P of callee key, at a call with args, in x's binders; nil when P mentions an argument that
  is not a binder of x."
  [x key args P]
  (let [c (if (vector? key) (first key) key)
        bs (binder-names-of c)
        xs (set (binder-names-of x))
        m (zipmap bs args)
        used (filter #(contains? m %) (distinct (filter symbol? (flatten (list P)))))]
    (when (every? #(and (symbol? (m %)) (xs (m %))) used)
      (walk/postwalk-replace (select-keys m used) P))))

(defn- infer
  "B's own facts and passes, the declared ones with the inferred forwarding: {:own {x [h P ..]} :pass {x {key [h ..]}}}."
  [B]
  (let [own (atom (into {} (for [[x v] (pt B :own)] [x (vec v)])))
        pass (atom (into {} (pt B :pass)))
        facts-of (fn [k] (or (get (pt B :ctx) k) (when-let [o (get @own k)] (vec (take-nth 2 (rest o))))))
        skip? (fn [x] (or (contains? (pt B :over) x) (contains? (pt B :src) x) (gated? B x)))
        changed (atom true)]
    (while @changed
      (reset! changed false)
      (doseq [x (:nodes @tree) :when (not (skip? x))
              [key calls] (group-by first (calls-in x))
              :let [ps (facts-of key)]
              :when (and (seq ps) (not (contains? (get @pass x) key)))
              :let [all (distinct (map (fn [[_ args]] (mapv #(instantiate x key args %) ps)) calls))
                    insts (first all)]
              :when (and (= 1 (count all)) (every? some? insts))]   ; every call: the same facts, in x's binders
        (let [o (get @own x [])
              have (zipmap (take-nth 2 (rest o)) (take-nth 2 o))
              used (set (concat (filter symbol? (flatten (base-form x))) (take-nth 2 o)))
              fresh (fn [o] (first (remove (set (concat used (take-nth 2 o))) (map #(symbol (str "hi" %)) (range)))))
              [o names] (reduce (fn [[o ns] P] (if-let [h (have P)] [o (conj ns h)]
                                                  (let [h (fresh o)] [(conj o h P) (conj ns h)])))
                                [o []] insts)]
          (swap! own assoc x o)
          (swap! pass assoc-in [x key] names)
          (reset! changed true))))
    {:own @own :pass @pass}))

(defonce ^:private effective (atom {}))
(defn- eff [B k]
  (when B
    (get (or (get @effective (:pred B)) (get (swap! effective assoc (:pred B) (infer B)) (:pred B))) k)))
(defn table-own "B's own facts, inferred ones included." [B] (eff B :own))
(defn table-pass "B's passes, inferred ones included." [B] (eff B :pass))

(defn- own-names [B x] (vec (take-nth 2 (get (eff B :own) x))))
(defn- facts
  "The facts B's lemma for x (a node, or [p F] for a site) takes: its :ctx or :own premises."
  [B x]
  (or (get (pt B :ctx) x) (when-let [o (get (eff B :own) x)] (vec (take-nth 2 (rest o))))))

(defn- node-stmt
  "x's binders and statement for part B (nil: the shared, bare statement)."
  [B x]
  (if (gated? B x)
    (let [[_ _ bs st] (:src (get gates x))] [bs st])
    (let [[_ _ bs st] (theorem-source x) ps (facts B x)]
      [bs (if (seq ps) (insert-before-inv st ps) st)])))

(defn- site-binders
  "p's binders (renamed apart, suffix _) with its row function := F, and p's statement for B (with
  B's facts at [p F]): [binders stmt index-of-the-row-function]."
  [B p F]
  (let [[binders stmt] (node-stmt nil p)
        ns (bnames binders)
        ;; a variable bound inside p's binder types (forall [e :- EdgeRow] ...) that F mentions is renamed
        ;; apart too, or it would capture F's (well-formed-edge-upd at a row function of the edge e)
        fsyms (set (filter symbol? (flatten (list (site-key F)))))
        inner (filter fsyms (mapcat (fn [y] (when (and (seq? y) (= 'forall (first y)) (vector? (second y))) (bnames (second y))))
                                    (tree-seq coll? seq binders)))
        m (zipmap (concat ns inner) (map #(symbol (str % "_")) (concat ns inner)))
        i (dispatched p)
        sub (fn [x] (walk/postwalk-replace {(m (nth ns i)) (site-key F)} (walk/postwalk-replace m x)))
        bs (sub (vec (concat (subvec binders 0 (* 3 i)) (subvec binders (* 3 (inc i))))))
        ps (facts B [p (site-key F)])]
    [(vec (concat (site-params F) bs)) (sub (if (seq ps) (insert-before-inv stmt ps) stmt)) i]))

(defn- gpify [Q form]
  (walk/postwalk (fn [y] (cond (and (seq? y) (= 'well-formed (first y))) (list 'gp Q (second y))
                               (= y 'well-formed-parts) (list 'gp-parts Q)
                               (= y 'base-of) (list 'gp-well-formed Q)
                               :else y))
                 form))
(defn- stated [Q binders stmt] (gpify Q (if (seq binders) (list 'forall binders stmt) stmt)))

;; ---- a part's proof of a node: its source, own facts, passes and gates

(defn- with-own
  "x's own facts: they join the statement before the well-formed premise; the first intro names them."
  [B x [hd nm binders stmt & proof]]
  (let [i (first (keep-indexed (fn [i p] (when (inv-premise? p) i)) (butlast (rest stmt))))
        [pre [intro & post]] (split-with #(not (and (seq? %) ('#{intro intros} (first %)))) proof)
        names (rest intro)]
    (when-not (< i (count names)) (throw (ex-info (str x ": the first intro does not name the well-formed premise") {})))
    (apply list hd nm binders (insert-before-inv stmt (facts B x))
           (concat pre [(apply list 'intros (concat (take i names) (own-names B x) (drop i names)))] post))))

(defn- pass-key [y]
  (let [h (first y)]
    (if-let [i (dispatched h)] [h (site-key (nth (rest y) i nil))] h)))

(defn- with-passes
  "Insert the passes m at the calls in a proof, before the well-formed argument."
  [m form]
  (if (empty? m)
    form
    (walk/prewalk (fn [y] (if-let [ts (and (seq? y) (symbol? (first y)) (get m (pass-key y)))]
                            (let [args (vec (rest y))]
                              (apply list (first y) (concat (butlast args) ts [(last args)])))
                            y))
                  form)))

(defn- with-gates
  "The continuation of every call of a gate B takes receives the gate's fact."
  [B form]
  (if (empty? (pt B :gates))
    form
    (walk/prewalk (fn [y] (if-let [nm (and (seq? y) (get (pt B :gates) (first y)))]
                            (concat (butlast y) [(list 'fn [nm :- '_] (last y))])
                            y))
                  form)))

(defn proof-form
  "x's proof in the tree for part B (nil: the shared proof), in base vocabulary."
  [B x]
  (let [f (or (get (pt B :src) x) (when (gated? B x) (:src (get gates x))) (get sources x) (theorem-source x))
        f (if (and (get (eff B :own) x) (not (get (pt B :src) x))) (with-own B x f) f)   ; a :src states its own facts
        [hd nm binders stmt & proof] f]
    (apply list hd nm binders stmt (map #(with-gates B (with-passes (get (eff B :pass) x) %)) proof))))

(defn- proof-callees [x proof]
  (let [out (atom [])]
    (walk/prewalk (fn [y]
                    (cond (and (seq? y) (dispatched (first y))) (do (swap! out conj [:site (first y) (nth y (inc (dispatched (first y))))]) y)
                          (and (symbol? y) (@S y) (not= y x) (not (dispatched y)) (not= y 'well-formed-parts)) (do (swap! out conj [:node y]) y)
                          :else y))
                  proof)
    (vec (distinct @out))))

(defn callees
  "The callees of x's proof for part B (nil: the shared proof): [:node c] for a lemma, [:site p F]
  for a dispatched callee."
  [B x]
  (proof-callees x (drop 4 (proof-form B x))))

(defn site-keys
  "The row functions (site keys) of callee p's sites in the shared proofs, for a part's :sites."
  [p]
  (vec (distinct (for [x (:nodes @tree) [k a b] (callees nil x) :when (and (= k :site) (= a p))] (site-key b)))))
(defn row-sites
  "A part's :sites entries {[p F] (entry F)} for the sites of p whose row function's head (a symbol)
  satisfies pred: one rule for a family of row functions, as the copier's patches had."
  [p pred entry]
  (into {} (for [F (site-keys p) :when (pred (if (seq? F) (first F) F))] [[p F] (entry F)])))

(defn variant?
  "Does part B prove node x by its own generic lemma pres-x@B? When x passes or takes B's facts, B
  has a source for it, x is a gate B takes, or x calls one."
  [B x]
  (boolean (and B (not (contains? (pt B :over) x))
                (or (contains? (eff B :own) x) (contains? (eff B :pass) x) (contains? (pt B :src) x) (gated? B x)
                    (some (fn [[k c]] (and (= k :node) (gated? B c))) (callees nil x))))))

(defn pres-name
  ([x] (pres-name nil x))
  ([B x]
   (let [s (name x)
         base (str "pres-" (-> s (str/replace-first "well-formed-" "") (str/replace-first "-well-formed" "")))]
     (symbol (if B (str base "@" (name (:pred B))) base)))))

(defn pres-form
  "The generic lemma of node x (for part B: pres-x@B; nil: the shared one), as a theorem form."
  [B x]
  (let [[_ _ binders _ & proof] (proof-form B x)
        [_ stmt] (node-stmt B x)
        hyps (vec (mapcat (fn [[k a b]] (case k
                                          :node [(hyp-name a) :- (let [[bs st] (node-stmt B a)] (stated 'Q bs st))]
                                          :site [(site-name a b) :- (let [[bs st] (site-binders B a b)] (stated 'Q bs st))]))
                          (callees B x)))
        sub (fn sub [y]
              (cond (and (seq? y) (dispatched (first y)))
                    (let [args (vec (rest y)) i (dispatched (first y)) F (nth args i)]
                      (when (= '_ F) (throw (ex-info (str x ": a site with an implicit row function (add a source)") {})))
                      (apply list (site-name (first y) F)
                             (map sub (concat (site-vals F) (subvec args 0 i) (subvec args (inc i))))))
                    (seq? y) (apply list (map sub y))
                    (vector? y) (mapv sub y)
                    (and (symbol? y) (@S y) (not= y 'well-formed-parts) (not= y x)) (hyp-name y)
                    :else y))]
    (apply list 'a/theorem (pres-name B x) (vec (concat '[Q :- (=> World Bool)] (when B (:params B)) (gpify 'Q binders) hyps))
           (gpify 'Q stmt) (map (comp #(gpify 'Q %) sub) proof))))

;; {:nodes [the lemmas with a generic lemma, in load order] :prims #{base lemmas of the primitive edits}}
(defonce tree (atom nil))

(defn build!
  "Check the shared generic lemma of every lemma of the step's closure that calls others (including
  a primitive proved through others, e.g. insert-edge-checked)."
  []
  (let [prims (set (keys @frames/footprints))
        ;; the lemmas step-inv's base proof depends on (well-formed-parts is a leaf)
        closure (loop [todo ['step-well-formed] seen #{}]
                  (if-let [n (first todo)]
                    (if (or (seen n) (= n 'well-formed-parts))
                      (recur (rest todo) (conj seen n))
                      (recur (concat (rest todo) (filter @S0 (filter symbol? (flatten (drop 4 (base-theorem-source n))))))
                             (conj seen n)))
                    seen))
        derived? (fn [p] (let [cs (callees nil p)] (and (seq cs) (not-any? #(= 'well-formed-intro (second %)) cs))))
        nodes (vec (filter #(and (or (closure %) (contains? @derived %)) (not ('#{well-formed-parts well-formed-intro} %))
                                 (or (not (prims %)) (derived? %)))
                            @order))]
    (doseq [[_ f] (sort-by key @derived)] (ev f))   ; raw0's branches, checked for well-formed
    (doseq [x nodes] (ev (pres-form nil x)))
    (reset! tree {:nodes nodes :prims prims})))

;; ===========================================================================
;; Parts
;; ===========================================================================

;; A :ctx or :pass row keyed by a dispatched callee itself (not by one site [p F]) holds at every
;; site of it: the facts are over the callee's binders, the row among them (i8-closed: a new source's owner
;; is not closed, whichever row is inserted).
(defn- per-site [table]
  (let [whole? (fn [k] (and (symbol? k) (dispatched k)))
        ctx (:ctx table)]
    (cond-> table
      (some whole? (keys ctx))
      (assoc :ctx (into {} (mapcat (fn [[k v]] (if (whole? k)
                                                 (for [F (site-keys k) :when (not (contains? ctx [k F]))] [[k F] v])
                                                 [[k v]]))
                                   ctx)))
      (some #(some whole? (keys %)) (vals (:pass table)))
      (assoc :pass (into {} (for [[x m] (:pass table)]
                              [x (into {} (mapcat (fn [[k v]] (if (whole? k)
                                                                (for [[kk] (calls-in x) :when (and (vector? kk) (= k (first kk)) (not (contains? m kk)))] [kk v])
                                                                [[k v]]))
                                                  m))]))))))

(defn part!
  "Declare B's table in the tree (keys: see the namespace docstring). The table may precede the
  lemmas it names: a lemma must exist when a node calling it is restated. The copier's name of an
  overridden node becomes an alias of B's lemma (`restate!`)."
  [B & {:as table}]
  (swap! parts assoc (:pred B) (per-site table))
  (swap! effective dissoc (:pred B))
  (doseq [[x l] (:over table)] (swap! (:renames B) assoc x l))
  B)

(defn- aliases!
  "The copier's names of B's overridden nodes, as aliases of B's lemmas that exist by now."
  [B]
  (doseq [[x l] (sort-by key (pt B :over))
          :let [nm (copy-name B x)]
          :when (and (not= nm l) (declared? l) (not (declared? nm)))]
    (exempt/alias! nm l)
    (swap! (:copied B) conj nm)))

(defn- papp [B head] (let [pn (bnames (:params B))] (if (seq pn) (apply list head pn) head)))
(defn- qterm [B] (papp B (symbol (str (name (:pred B)) "-rest"))))

(defn- site-term [B p F]
  (let [[bs stmt i] (site-binders B p F)
        prem (butlast (rest stmt))
        hs (vec (map-indexed (fn [j _] (symbol (str "h" j))) prem))
        Q (qterm B)
        lam (fn [body] (list 'fn (vec (concat (gpify Q bs) (mapcat (fn [h q] [h :- (gpify Q q)]) hs prem))) body))
        pnames (vec (drop (count (bnames (site-params F))) (bnames bs)))
        unsuffix (zipmap (map #(symbol (str/replace (name %) #"_$" "")) pnames) pnames)]
    (if-let [t (get (pt B :sites) [p (site-key F)])]
      ;; the entry names the site's binders; the row function inside it keeps the caller's names
      (let [k (site-key F) ph (gensym "row")]
        (lam (walk/postwalk-replace {ph k} (walk/postwalk-replace unsuffix (walk/postwalk-replace {k ph} t)))))
      ;; no entry: the part's cell, at the site's premises in order (its facts before the inv premise)
      (let [cell (or (get @(:renames B) p)
                     (if (contains? (set (:nodes @tree)) p)
                       (throw (ex-info (str (:pred B) ": " p " (a site) is not restated yet") {}))
                       (do (c/prim! B p nil) (get @(:renames B) p))))
            args (vec (concat (subvec pnames 0 i) [(site-key F)] (subvec pnames i) hs))
            args (if-let [[e k] ((:extra-args B) p)] (vec (concat (take k args) [e] (drop k args))) args)]
        (lam (apply list (papp B cell) args))))))

(defn- child-term [B [k a b]]
  (case k
    :site (site-term B a b)
    :node (let [l (or (get @(:renames B) a) (throw (ex-info (str (:pred B) ": no lemma for " a) {})))]
            (when-not (declared? l) (throw (ex-info (str (:pred B) ": " l " (its proof of " a ") is not defined yet") {})))
            (let [[e k] ((:extra-args B) a) h (papp B l)]
              (cond (nil? e) h
                    ;; an extra argument in first position instantiates a parameter of the cell: a part
                    ;; that is another part at fixed parameters uses that part's lemmas (i1-runs = i1-runs-exempt [])
                    (= k 0) (if (seq? h) (apply list (first h) e (rest h)) (list h e))
                    :else (throw (ex-info (str (:pred B) ": its cell for " a " takes an extra argument: dispatch " a " per row (`dispatched`)") {})))))))

(defn- check-passes!
  "Every callee of x that takes B's facts gets them: x passes them, or B has a source for x."
  [B x v?]
  (doseq [[k a b] (callees (when v? B) x)
          :let [key (if (= k :site) [a (site-key b)] a)]
          :when (facts B key)
          :when (not (contains? (pt B :src) x))
          :when (not (contains? (get (eff B :pass) x) key))]
    (throw (ex-info (str (:pred B) ": " x " calls " key ", which takes facts in this part: give "
                         x " a :pass for it (or :over " x ")") {}))))

(defn- restate-one! [B x]
  (let [nm (copy-name B x)
        v? (variant? B x)
        _ (check-passes! B x v?)
        _ (when (and v? (not (declared? (pres-name B x)))) (ev (pres-form B x)))
        [hd] (theorem-source x)
        [binders stmt] (node-stmt B x)
        [_ _ binders stmt] (copy-form B (list hd x binders stmt) nm {})]
    (ev (list 'a/theorem nm binders stmt
              (list 'exact (apply list (pres-name (when v? B) x) (qterm B)
                                  (concat (when v? (bnames (:params B)))
                                          (drop (count (bnames (:params B))) (bnames binders))
                                          (map #(child-term B %) (callees (when v? B) x)))))))
    (swap! (:renames B) assoc x nm)
    (swap! (:copied B) conj nm)
    nm))

(defn restate!
  "Restate every lemma of B's closure from `roots` that B has no lemma for yet, under the copier's
  name and statement: the generic lemma (B's own on its context paths) applied to B's lemmas for its
  callees. A primitive B has no cell for is restated from its generic lemma if it has one, else gets
  an `rfl` frame cell (prim!). Returns the number of lemmas added."
  [B roots]
  (aliases! B)
  (let [{:keys [nodes]} @tree
        node? (set nodes)
        deps (fn [n] (keep (fn [[k a b]] (cond (= k :node) a
                                               (and (node? a) (not (get (pt B :sites) [a (site-key b)]))) a))
                           (callees (when (variant? B n) B) n)))
        need (loop [todo (vec roots) seen #{}]
               (if-let [n (first todo)]
                 (if (or (seen n) (contains? @(:renames B) n))
                   (recur (subvec todo 1) seen)
                   (recur (into (subvec todo 1) (when (node? n) (deps n))) (conj seen n)))
                 seen))]
    (count (doall (for [x (filter need @order)
                        :when (not (contains? @(:renames B) x))]
                    (if (node? x) (restate-one! B x) (c/prim! B x nil)))))))

(build!)
