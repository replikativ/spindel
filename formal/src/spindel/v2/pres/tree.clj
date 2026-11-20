(ns spindel.v2.pres.tree
  "The generic step tree (formal/notes/proof-layout.md §5c, §5d), kernel-checked (Init only).

  Every composite lemma x of the base proof is checked once, over an abstract rest part Q, by open
  recursion: `pres-x` takes one hypothesis per lemma x's proof calls (S c over Q: c's statement with
  inv-sample replaced by `gp Q`, Base and Q) and proves S x over Q by x's base proof. A part restates
  each lemma the copier used to generate for it, under the old name and statement, as pres-x applied
  to the part's lemma for every callee (`restate!`). Its table (`part!`) says where that is not
  enough:

    :over   x -> the part's own proof of x (content: a deferred violation, an argument over edits).
    :sites  an update primitive, or a composite taking a row function (`serve-or`), is one callee
            per row function; [p F] -> the part's proof there (default: its cell, with the bundle's
            extra argument).
    :ctx    x or [p F] -> the facts from the path the part's own proof (or site entry) takes there.
    :own    x -> facts a node takes from above it and passes on, named: [h fact ...].
    :pass   caller -> callee or [p F] -> the terms the caller passes for those facts, over its locals.
    :gates  a gate node (`gates`) whose continuation takes the gate's fact, named.
    :src    x -> the part's proof of x where passes are not enough (base vocabulary).

  The facts are the part's, in its own vocabulary. A node whose proof passes or takes such facts
  (or calls a gate the part takes) gets the part's own generic lemma `pres-x@<part>`, generated from
  the base proof with the part's passes; every other node uses the shared `pres-x`. So a part's
  facts reach only its own lemmas, and a reader finds all of them in the part's table."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.inv.copier :as c]
            [spindel.v2.pres.frames :as frames]
            [spindel.v2.pres.exempt :as exempt]))

(def ^:private theorem-source @#'c/theorem-source)
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

(ev '(a/defn gp [Q :- (=> World Bool), w :- World] Bool (Bool.and (inv-sample w) (Q w))))
(ev '(a/theorem gp-sample [Q :- (=> World Bool), w :- World] (=> (= (gp Q w) true) (= (inv-sample w) true))
       (intro h) (simp only [gp Bool.and_eq_true] at h) (exact (And.left h))))
(ev '(a/theorem gp-parts [Q :- (=> World Bool), w :- World]
       (=> (= (gp Q w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
       (intro h) (exact (inv-parts w (gp-sample Q w h)))))

;; ===========================================================================
;; The tree's own declarations
;; ===========================================================================

;; Callees dispatched per row function, with the row function's argument position.
(def dispatched '{inv-run-upd 2 inv-task-upd 2 inv-resource-upd 2 inv-source-upd 2 inv-scope-upd 2 inv-serve-or 3})

;; Sources: nodes whose generic proof is not their base proof: a row function the base proof leaves
;; to unification is named. T-finally-enter's mentions a local of the proof (`site-gen`: the site is
;; stated for every value of the finalizer it pushes).
(defn- name-row-fn [x p F]
  (let [i (inc (dispatched p))]
    (walk/prewalk (fn [y] (if (and (seq? y) (= p (first y)) (= '_ (nth y i nil))) (apply list (assoc (vec y) i F)) y))
                  (theorem-source x))))

(def sources
  {'inv-link-demand-raw (name-row-fn 'inv-link-demand-raw 'inv-source-upd '(link-set-rtask (:next-id w)))
   't-finally-enter-inv
   (walk/postwalk-replace
    {'(inv-run-upd w (:id r) _ (run-fin-push-id _) h)
     '(inv-run-upd w (:id r) (site-gen [fz :- Finalizer] (run-fin-push fz) (Finalizer.mk 0 (:effect-index r) (List.nil Nat)))
        (run-fin-push-id (Finalizer.mk 0 (:effect-index r) (List.nil Nat))) h)}
    (theorem-source 't-finally-enter-inv))})

;; Gates: a node whose last premise is a continuation (the item's world) that runs only past a
;; guard. For a part that takes the gate, the continuation receives the guard's fact: the gate's
;; statement and proof are :src, and its callers' continuations become `(fn [name :- _] ...)`.
(def gates
  '{c0-gate-inv
    {:src (a/theorem c0-gate-inv [w :- World, b :- Bool, o :- Outcome]       ; C0: raw0 runs a link-creating
            (=> (= (inv-sample w) true) (=> (= (root-ok-if b w) true) (= (inv-sample (:world o)) true))  ; item only
                (= (inv-sample (:world (c0-gate w b o))) true))               ; while the root scope is open
            (intros h ho)
            (cases hg (root-ok-if b w))
            (simp only [c0-gate hg refuse]) (exact h)
            (simp only [c0-gate hg]) (exact (ho hg)))}})

;; ===========================================================================
;; Generation
;; ===========================================================================

(def ^:private S (delay (set (keep (fn [[n g]] (when (@#'c/statement-mentions-inv? g) n)) @@#'c/source-theorems))))

;; pred -> the part's table (see part!)
(defonce parts (atom {}))
(defn- pt [B k] (when B (get-in @parts [(:pred B) k])))

(defn- insert-before-inv [stmt prems]
  (let [[_ & xs] stmt ps (butlast xs)
        i (first (keep-indexed (fn [i p] (when (inv-premise? p) i)) ps))]
    (concat ['=>] (take i ps) prems (drop i ps) [(last xs)])))

;; a site's row function: a form, or (site-gen [params] pattern value...) when it mentions a local of
;; the proof (the site is then stated for every value of the params)
(defn- gen? [F] (and (seq? F) (= 'site-gen (first F))))
(defn- site-key [F] (if (gen? F) (nth F 2) F))
(defn- site-params [F] (if (gen? F) (second F) []))
(defn- site-vals [F] (if (gen? F) (drop 3 F) []))
(defn- sanitize [F] (-> (pr-str F) (str/replace #"[()\[\]:]" "") (str/replace #"\s+" "-") (str/replace #"[^A-Za-z0-9-]" "")))
(defn- hyp-name [c] (symbol (str "pc-" (name c))))
(defn- site-name [p F] (symbol (str "pc-" (name p) "@" (sanitize (site-key F)))))

(defn- own-names [B x] (vec (take-nth 2 (get (pt B :own) x))))
(defn- facts
  "The facts B's lemma for x (a node, or [p F] for a site) takes: its :ctx or :own premises."
  [B x]
  (or (get (pt B :ctx) x) (when-let [o (get (pt B :own) x)] (vec (take-nth 2 (rest o))))))
(defn- gated? [B x] (contains? (pt B :gates) x))

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
        ns (bnames binders) m (zipmap ns (map #(symbol (str % "_")) ns))
        i (dispatched p)
        sub (fn [x] (walk/postwalk-replace {(m (nth ns i)) (site-key F)} (walk/postwalk-replace m x)))
        bs (sub (vec (concat (subvec binders 0 (* 3 i)) (subvec binders (* 3 (inc i))))))
        ps (facts B [p (site-key F)])]
    [(vec (concat (site-params F) bs)) (sub (if (seq ps) (insert-before-inv stmt ps) stmt)) i]))

(defn- gpify [Q form]
  (walk/postwalk (fn [y] (cond (and (seq? y) (= 'inv-sample (first y))) (list 'gp Q (second y))
                               (= y 'inv-parts) (list 'gp-parts Q)
                               (= y 'base-of) (list 'gp-sample Q)
                               :else y))
                 form))
(defn- stated [Q binders stmt] (gpify Q (if (seq binders) (list 'forall binders stmt) stmt)))

;; ---- a part's proof of a node: its source, own facts, passes and gates

(defn- with-own
  "x's own facts: they join the statement before the inv-sample premise; the first intro names them."
  [B x [hd nm binders stmt & proof]]
  (let [i (first (keep-indexed (fn [i p] (when (inv-premise? p) i)) (butlast (rest stmt))))
        [pre [intro & post]] (split-with #(not (and (seq? %) ('#{intro intros} (first %)))) proof)
        names (rest intro)]
    (when-not (< i (count names)) (throw (ex-info (str x ": the first intro does not name the inv-sample premise") {})))
    (apply list hd nm binders (insert-before-inv stmt (facts B x))
           (concat pre [(apply list 'intros (concat (take i names) (own-names B x) (drop i names)))] post))))

(defn- pass-key [y]
  (let [h (first y)]
    (if-let [i (dispatched h)] [h (site-key (nth (rest y) i nil))] h)))

(defn- with-passes
  "Insert the passes m at the calls in a proof, before the inv-sample argument."
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
        f (if (and (get (pt B :own) x) (not (get (pt B :src) x))) (with-own B x f) f)   ; a :src states its own facts
        [hd nm binders stmt & proof] f]
    (apply list hd nm binders stmt (map #(with-gates B (with-passes (get (pt B :pass) x) %)) proof))))

(defn- proof-callees [x proof]
  (let [out (atom [])]
    (walk/prewalk (fn [y]
                    (cond (and (seq? y) (dispatched (first y))) (do (swap! out conj [:site (first y) (nth y (inc (dispatched (first y))))]) y)
                          (and (symbol? y) (@S y) (not= y x) (not (dispatched y)) (not= y 'inv-parts)) (do (swap! out conj [:node y]) y)
                          :else y))
                  proof)
    (vec (distinct @out))))

(defn callees
  "The callees of x's proof for part B (nil: the shared proof): [:node c] for a lemma, [:site p F]
  for a dispatched callee."
  [B x]
  (proof-callees x (drop 4 (proof-form B x))))

(defn variant?
  "Does part B prove node x by its own generic lemma pres-x@B? When x passes or takes B's facts, B
  has a source for it, x is a gate B takes, or x calls one."
  [B x]
  (boolean (and B (not (contains? (pt B :over) x))
                (or (contains? (pt B :own) x) (contains? (pt B :pass) x) (contains? (pt B :src) x) (gated? B x)
                    (some (fn [[k c]] (and (= k :node) (gated? B c))) (callees nil x))))))

(defn pres-name
  ([x] (pres-name nil x))
  ([B x]
   (let [s (name x)
         base (str "pres-" (cond (str/starts-with? s "inv-") (subs s 4)
                                 (str/ends-with? s "-inv-sample") (subs s 0 (- (count s) 11))
                                 (str/ends-with? s "-inv") (subs s 0 (- (count s) 4))
                                 :else s))]
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
                    (and (symbol? y) (@S y) (not= y 'inv-parts) (not= y x)) (hyp-name y)
                    :else y))]
    (apply list 'a/theorem (pres-name B x) (vec (concat '[Q :- (=> World Bool)] (gpify 'Q binders) hyps))
           (gpify 'Q stmt) (map (comp #(gpify 'Q %) sub) proof))))

;; {:nodes [the lemmas with a generic lemma, in load order] :prims #{base lemmas of the primitive edits}}
(defonce tree (atom nil))

(defn build!
  "Check the shared generic lemma of every lemma of the step's closure that calls others (including
  a primitive proved through others, e.g. insert-edge-checked)."
  []
  (let [prims (set (keys @frames/footprints))
        probe (c/mk-bundle 'gpprobe '[] "gpprobe-" {})
        _ (swap! (:renames probe) assoc 'inv-parts 'inv-parts)
        closure (set (@#'c/closure probe 'step-inv))
        derived? (fn [p] (let [cs (callees nil p)] (and (seq cs) (not-any? #(= 'inv-intro (second %)) cs))))
        nodes (vec (filter #(and (closure %) (not ('#{inv-parts inv-intro} %)) (or (not (prims %)) (derived? %)))
                            (map first @@#'c/source-theorems)))]
    (doseq [x nodes] (ev (pres-form nil x)))
    (reset! tree {:nodes nodes :prims prims})))

;; ===========================================================================
;; Parts
;; ===========================================================================

(defn part!
  "Declare B's table in the tree (keys: see the namespace docstring). The table may precede the
  lemmas it names: a lemma must exist when a node calling it is restated. The copier's name of an
  overridden node becomes an alias of B's lemma (`restate!`)."
  [B & {:as table}]
  (swap! parts assoc (:pred B) table)
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
      (lam (walk/postwalk-replace unsuffix t))
      (let [_ (when (facts B [p (site-key F)])
                (throw (ex-info (str (:pred B) ": site " [p (site-key F)] " takes facts: give its :sites entry") {})))
            cell (or (get @(:renames B) p)
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
            (papp B l))))

(defn- check-passes!
  "Every callee of x that takes B's facts gets them: x passes them, or B has a source for x."
  [B x v?]
  (doseq [[k a b] (callees (when v? B) x)
          :let [key (if (= k :site) [a (site-key b)] a)]
          :when (facts B key)
          :when (not (contains? (pt B :src) x))
          :when (not (contains? (get (pt B :pass) x) key))]
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
                                  (concat (drop (count (bnames (:params B))) (bnames binders))
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
    (count (doall (for [x (filter need (map first @@#'c/source-theorems))
                        :when (not (contains? @(:renames B) x))]
                    (if (node? x) (restate-one! B x) (c/prim! B x nil)))))))

(build!)
