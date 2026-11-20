(ns spindel.v2.pres.tree
  "The generic step tree (formal/notes/proof-layout.md, options A and A+), kernel-checked (Init only).

  The copier re-checks the base proof once per part. Here every composite lemma of the base proof is
  checked once, over an abstract rest part Q, by open recursion: the generic lemma of a composite x
  takes one hypothesis per lemma x's proof calls and proves x from them,

    pres-x : forall Q, x's binders, (S c over Q, for every callee c) -> (S x over Q)

  where `S c over Q` is c's statement with `inv-sample` replaced by `gp Q` (Base and Q). The proof of
  pres-x is the base proof of x with every callee replaced by its hypothesis. A part restates each
  lemma the copier used to generate for it, under the old name and statement, as one application:
  pres-x applied to the part's own lemma for every callee (`restate!`). A part's own proof of a
  composite (its content: a deferred violation, or an argument over several edits) replaces the
  generic one at that node (`part!` :over); every other node takes the generic lemma.

  Two kinds of callees need more than the bare statement (proof-layout.md section 5c):

    sites     an update primitive (`run-upd`, `task-upd`, `resource-upd`) is one hypothesis per row
              function: `run-upd` at f := run-wake is a different hypothesis from f := run-tick. A
              part whose cell needs a fact about the row function (gl: f keeps the run key) proves
              each site: from its cell with the bundle's extra argument (`rfl` at most sites), or
              from its table entry.
    contexts  facts the base proof checks on the path but does not pass, because inv-sample does not
              need them. `contexts` declares, per callee, the premises a part may use there; the tree
              passes them at every call site (`passes`, `sources`). For a part that does not need them
              they are dropped (`ctx-<x>`, proved once).

  Stage 2 used two total structures (Leaf, Over) instead. They cannot carry a part that breaks its
  invariant inside a transition (gl kills a run in T14 and repairs it in the same composite): every
  Leaf field had to be proved by every part, and the default of an outer override point re-proved
  the inner one from the leaves. With open recursion a part proves exactly the callees of the nodes
  it does not override."
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
;; What the tree passes that the base proof drops (proof-layout.md section 5c)
;; ===========================================================================

;; Contexts: per callee, the premises a part may use there. Each is the difference between a part's
;; override and the base lemma (N). `:own?`: the node's own proof uses them, so they are premises of
;; its own statement too, and its source below passes them on.
(def contexts
  '{inv-cancel-run-local {:prems [(List.Mem r (:runs w))]}                        ; the cancelled run is a row (gl, g9)
    inv-retire-local     {:prems [(List.Mem r (:runs w)) (= (run-alive r) false)]} ; the retired run is a dead row (gl)
    inv-complete-raw     {:prems [(List.Mem r (:runs w))                           ; the completed run is a row and
                                  (= (Nat.beq (:tag res) res-none) false)]}        ;   its result is not none (gl)
    inv-start-raw        {:prems [(= (comp-has w (:id c)) true)]}                  ; the new run's `of` is a computation (gl)
    inv-new-run-of       {:prems [(= (comp-has w (:id c)) true)]}                  ; same (gl)
    t12-inv              {:prems [(= (res-tag-ok tag) true)] :own? true}           ; complete is not refused for its tag
    inv-dispatch-raw     {:prems [(= (comp-has w (:id c)) true)] :own? true}})     ; T11's computation exists

;; Passes (H): at a call of `callee` in `caller`, the facts inserted before the inv-sample argument, in
;; base vocabulary over the caller's locals at that call.
(def passes
  '{inv-job-apply  {inv-cancel-run-local [(tbl-find-mem RunRow run-id rid r (:runs w) hf)]            ; run-find found it
                    inv-retire-local     [(tbl-find-mem RunRow run-id rid r (:runs w) hf)
                                          (retirable-dead r ha)]}                                     ; retirable: done
    raw0-inv       {t12-inv              [(refused-tag-ok w st tag hc)]}                              ; the refusal guard
    inv-retire-one {inv-complete-raw     [(retire-r1-mem w r r1 rid hf1) (task-final-res-tag _ _ v)]} ; found; err result
    t5-inv         {inv-start-raw        [(find-comp-has w cid c hc)]}                                ; comp-find found it
    t11-inv        {inv-dispatch-raw     [(find-comp-has w cid c hc)]}})                              ; same

;; Sources (H): nodes whose tree proof is not the base proof, in base vocabulary (`base-of` is the
;; inv-sample half of the world's proof). t12 and dispatch-raw use their contexts; T-finally-enter
;; names its row function, which the base proof leaves to unification.
(def sources
  {'t12-inv
   '(a/theorem t12-inv [w :- World, st :- Nat, tag :- Nat, v :- Nat]
      (=> (= (res-tag-ok tag) true) (= (inv-sample w) true) (= (inv-sample (:world (t12-complete w st tag v))) true))
      (intros hg h)
      (cases ht (tok-run w st)) (case' [some r]) (case' [none])
      (simp only [t12-complete ht refuse]) (exact h)
      (cases hn (run-normal r))
      (simp only [t12-complete ht hn refuse]) (exact h)
      (simp only [t12-complete ht hn accept])
      (exact (inv-complete-raw w r (RunResult.mk tag v) (And.left (tok-facts w st r ht)) (tag-ok-none tag hg) h)))
   ;; comp-has (:id c) survives cancel-pred, cut-suffix and consume-entry: they keep the computation
   ;; ids (the bundle `ch` of spindel.v2.inv.copier: a frame of the comps table at column level)
   'inv-dispatch-raw
   '(a/theorem inv-dispatch-raw [w :- World, c :- CompRow]
      (=> (= (comp-has w (:id c)) true) (= (inv-sample w) true) (= (inv-sample (dispatch-raw w c)) true))
      (intros hc h)
      (have h1 := (inv-cancel-pred w c h))
      (have k1 := (ch-cancel-pred (:id c) w c (ch-intro (:id c) w (base-of w h) hc)))
      (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
      (simp only [dispatch-raw he])
      (exact (inv-new-run-of _ c 0 (ch-rest-of (:id c) _ (ch-cut-suffix (:id c) _ (:id c) false 0 0 k1))
               (inv-cut-suffix _ (:id c) false 0 0 h1)))
      (simp only [dispatch-raw he])
      (exact (inv-new-run-of _ c _
               (ch-rest-of (:id c) _ (ch-consume-entry (:id c) _ e (ch-cut-suffix (:id c) _ (:id c) true (:at e) (:id e) k1)))
               (inv-consume-entry _ e (inv-cut-suffix _ (:id c) true (:at e) (:id e) h1)))))
   't-finally-enter-inv
   (walk/postwalk-replace
    {'(inv-run-upd w (:id r) _ (run-fin-push-id _) h)
     '(inv-run-upd w (:id r) (site-gen [fz :- Finalizer] (run-fin-push fz) (Finalizer.mk 0 (:effect-index r) (List.nil Nat)))
        (run-fin-push-id (Finalizer.mk 0 (:effect-index r) (List.nil Nat))) h)}
    (theorem-source 't-finally-enter-inv))})

;; ===========================================================================
;; Generation
;; ===========================================================================

(def ^:private S (delay (set (keep (fn [[n g]] (when (@#'c/statement-mentions-inv? g) n)) @@#'c/source-theorems))))
(def ^:private dispatched '#{inv-run-upd inv-task-upd inv-resource-upd})
(def ^:private fpos 2)   ; the row function's position among a dispatched primitive's arguments

(defn- insert-before-inv [stmt prems]
  (let [[_ & xs] stmt ps (butlast xs)
        i (first (keep-indexed (fn [i p] (when (inv-premise? p) i)) ps))]
    (concat ['=>] (take i ps) prems (drop i ps) [(last xs)])))

(defn- with-passes [x form]
  (if-let [m (get passes x)]
    (walk/prewalk (fn [y] (if (and (seq? y) (contains? m (first y)))
                            (let [args (vec (rest y))]
                              (apply list (first y) (concat (butlast args) (get m (first y)) [(last args)])))
                            y))
                  form)
    form))

(defn tree-source
  "x's proof in the tree (base vocabulary): its source override, or the base proof with the passes."
  [x]
  (or (get sources x)
      (let [[hd nm binders stmt & proof] (theorem-source x)]
        (apply list hd nm binders stmt (map #(with-passes x %) proof)))))

(defn- node-stmt
  "x's binders and statement in the tree; with its context premises when `ctx?` (what callers see)."
  [x ctx?]
  (let [[_ _ binders stmt] (or (get sources x) (theorem-source x))
        ps (get-in contexts [x :prems])]
    [binders (if (and ctx? ps (not (get sources x))) (insert-before-inv stmt ps) stmt)]))

(defn- gpify [Q form]
  (walk/postwalk (fn [y] (cond (and (seq? y) (= 'inv-sample (first y))) (list 'gp Q (second y))
                               (= y 'inv-parts) (list 'gp-parts Q)
                               (= y 'base-of) (list 'gp-sample Q)
                               :else y))
                 form))

;; a site's row function: a form, or (site-gen [params] pattern value...) when it mentions a local of
;; the proof (the site is then stated for every value of the params)
(defn- gen? [F] (and (seq? F) (= 'site-gen (first F))))
(defn- site-key [F] (if (gen? F) (nth F 2) F))
(defn- site-params [F] (if (gen? F) (second F) []))
(defn- site-vals [F] (if (gen? F) (drop 3 F) []))
(defn- sanitize [F] (-> (pr-str F) (str/replace #"[()\[\]:]" "") (str/replace #"\s+" "-") (str/replace #"[^A-Za-z0-9-]" "")))
(defn- hyp-name [c] (symbol (str "pc-" (name c))))
(defn- site-name [p F] (symbol (str "pc-" (name p) "@" (sanitize (site-key F)))))

(defn- site-binders
  "p's binders (renamed apart, suffix _) with f := F, and p's statement: [binders stmt index-of-f]."
  [p F]
  (let [[binders stmt] (node-stmt p false)
        ns (bnames binders) m (zipmap ns (map #(symbol (str % "_")) ns))
        i (.indexOf ^java.util.List ns 'f)
        sub (fn [x] (walk/postwalk-replace {(m 'f) (site-key F)} (walk/postwalk-replace m x)))
        bs (sub (vec (concat (subvec binders 0 (* 3 i)) (subvec binders (* 3 (inc i))))))]
    [(vec (concat (site-params F) bs)) (sub stmt) i]))

(defn- stated [Q binders stmt] (gpify Q (if (seq binders) (list 'forall binders stmt) stmt)))
(defn- hyp-type [Q c] (let [[b s] (node-stmt c true)] (stated Q b s)))
(defn- site-type [Q p F] (let [[b s] (site-binders p F)] (stated Q b s)))

(defn callees
  "The callees of x's tree proof: [:node c] for a lemma, [:site p F] for a dispatched primitive."
  [x]
  (let [[_ _ _ _ & proof] (tree-source x) out (atom [])]
    (walk/prewalk (fn [y]
                    (cond (and (seq? y) (dispatched (first y))) (do (swap! out conj [:site (first y) (nth y (inc fpos))]) y)
                          (and (symbol? y) (@S y) (not= y x) (not (dispatched y)) (not= y 'inv-parts)) (do (swap! out conj [:node y]) y)
                          :else y))
                  proof)
    (vec (distinct @out))))

(defn pres-name [x]
  (let [s (name x)]
    (symbol (str "pres-" (cond (str/starts-with? s "inv-") (subs s 4)
                               (str/ends-with? s "-inv-sample") (subs s 0 (- (count s) 11))
                               (str/ends-with? s "-inv") (subs s 0 (- (count s) 4))
                               :else s)))))

(defn pres-form
  "The generic lemma of node x, as a theorem form."
  [x]
  (let [[_ _ binders _ & proof] (tree-source x)
        [_ stmt] (node-stmt x (get-in contexts [x :own?]))
        cs (callees x)
        hyps (vec (mapcat (fn [[k a b]] (case k :node [(hyp-name a) :- (hyp-type 'Q a)]
                                                  :site [(site-name a b) :- (site-type 'Q a b)]))
                          cs))
        sub (fn sub [y]
              (cond (and (seq? y) (dispatched (first y)))
                    (let [args (vec (rest y)) F (nth args fpos)]
                      (when (= '_ F) (throw (ex-info (str x ": a site with an implicit row function (add a source)") {})))
                      (apply list (site-name (first y) F)
                             (map sub (concat (site-vals F) (subvec args 0 fpos) (subvec args (inc fpos))))))
                    (seq? y) (apply list (map sub y))
                    (vector? y) (mapv sub y)
                    (and (symbol? y) (@S y) (not= y 'inv-parts) (not= y x)) (hyp-name y)
                    :else y))]
    (apply list 'a/theorem (pres-name x) (vec (concat '[Q :- (=> World Bool)] (gpify 'Q binders) hyps))
           (gpify 'Q stmt) (map (comp #(gpify 'Q %) sub) proof))))

(defn- ctx-name [c] (symbol (str "ctx-" (subs (name (pres-name c)) 5))))

(defn- ctx-default!
  "ctx-<c> : forall Q, (S c over Q) -> (S c over Q with its context premises): the context dropped."
  [c]
  (let [[binders stmt] (node-stmt c false)
        ps (get-in contexts [c :prems])
        prem (butlast (rest stmt))
        hs (vec (map-indexed (fn [i _] (symbol (str "h" i))) prem))
        ks (vec (map-indexed (fn [i _] (symbol (str "k" i))) ps))
        i (first (keep-indexed (fn [i p] (when (inv-premise? p) i)) prem))]
    (ev (list 'a/theorem (ctx-name c) '[Q :- (=> World Bool)] (list '=> (stated 'Q binders stmt) (hyp-type 'Q c))
              '(intro hb) (concat ['intros] (bnames binders) (take i hs) ks (drop i hs))
              (list 'exact (apply list 'hb (concat (bnames binders) hs)))))))

;; {:nodes [the lemmas with a generic lemma, in load order] :prims #{base lemmas of the primitive edits}}
(defonce tree (atom nil))

(defn build!
  "Check the generic lemma of every lemma of the step's closure that calls others (including a
  primitive proved through others, e.g. insert-edge-checked), and the context defaults."
  []
  (let [prims (set (keys @frames/footprints))
        probe (c/mk-bundle 'gpprobe '[] "gpprobe-" {})
        _ (swap! (:renames probe) assoc 'inv-parts 'inv-parts)
        closure (set (@#'c/closure probe 'step-inv))
        derived? (fn [p] (let [cs (callees p)] (and (seq cs) (not-any? #(= 'inv-intro (second %)) cs))))
        nodes (vec (filter #(and (closure %) (not ('#{inv-parts inv-intro} %)) (or (not (prims %)) (derived? %)))
                            (map first @@#'c/source-theorems)))]
    (doseq [x nodes] (ev (pres-form x)))
    (doseq [c (sort (keys contexts)) :when (not (get-in contexts [c :own?]))] (ctx-default! c))
    (reset! tree {:nodes nodes :prims prims})))

;; ===========================================================================
;; Parts
;; ===========================================================================

;; pred -> {:sites {[primitive row-function] form}, :over {node lemma}, :bare #{node}}
(defonce parts (atom {}))

(defn part!
  "Declare B's own entries in the tree:
    :sites {[primitive row-function] form}  B's proof of an update primitive at one row function: a
            form over the primitive's binder names and h0.. (its premises), like prim!'s cells.
            A site not listed takes B's cell with the bundle's extra argument.
    :over  {node lemma}  B's own proof of a composite, used instead of the generic one. For a node
            with a context the lemma takes the context premises, unless the node is in :bare.
  The table may precede the lemmas it names: a lemma must exist when a node calling it is restated.
  The copier's name of an overridden node becomes an alias of the lemma (`restate!`)."
  [B & {:keys [sites over bare]}]
  (swap! parts assoc (:pred B) {:sites sites :over over :bare (set bare)})
  (doseq [[x l] over] (swap! (:renames B) assoc x l))
  B)

(defn- aliases!
  "The copier's names of B's overridden nodes, as aliases of B's lemmas that exist by now."
  [B]
  (doseq [[x l] (sort-by key (get-in @parts [(:pred B) :over]))
          :let [nm (copy-name B x)]
          :when (and (not= nm l) (declared? l) (not (declared? nm)))]
    (exempt/alias! nm l)
    (swap! (:copied B) conj nm)))

(defn- papp [B head] (let [pn (bnames (:params B))] (if (seq pn) (apply list head pn) head)))
(defn- qterm [B] (papp B (symbol (str (name (:pred B)) "-rest"))))

(defn- site-term [B p F]
  (let [[bs stmt i] (site-binders p F)
        prem (butlast (rest stmt))
        hs (vec (map-indexed (fn [j _] (symbol (str "h" j))) prem))
        Q (qterm B)
        lam (fn [body] (list 'fn (vec (concat (gpify Q bs) (mapcat (fn [h q] [h :- (gpify Q q)]) hs prem))) body))
        pnames (vec (drop (count (bnames (site-params F))) (bnames bs)))
        unsuffix (zipmap (map #(symbol (str/replace (name %) #"_$" "")) pnames) pnames)]
    (if-let [t (get-in @parts [(:pred B) :sites [p (site-key F)]])]
      (lam (walk/postwalk-replace unsuffix t))
      (let [cell (or (get @(:renames B) p) (do (c/prim! B p nil) (get @(:renames B) p)))
            args (vec (concat (subvec pnames 0 i) [(site-key F)] (subvec pnames i) hs))
            args (if-let [[e k] ((:extra-args B) p)] (vec (concat (take k args) [e] (drop k args))) args)]
        (lam (apply list (papp B cell) args))))))

(defn- child-term [B [k a b]]
  (case k
    :site (site-term B a b)
    :node (let [l (or (get @(:renames B) a) (throw (ex-info (str (:pred B) ": no lemma for " a) {})))
                _ (when-not (declared? l) (throw (ex-info (str (:pred B) ": " l " (its proof of " a ") is not defined yet") {})))
                t (papp B l)
                over? (contains? (get-in @parts [(:pred B) :over]) a)
                bare? (contains? (get-in @parts [(:pred B) :bare]) a)]
            (if (and (get-in contexts [a :prems]) (not (get-in contexts [a :own?])) (or (not over?) bare?))
              (list (ctx-name a) (qterm B) t)
              t))))

(defn- restate-one! [B x]
  (let [nm (copy-name B x)
        [hd _ binders] (tree-source x)
        [_ stmt] (node-stmt x (get-in contexts [x :own?]))
        [_ _ binders stmt] (copy-form B (list hd x binders stmt) nm {})]
    (ev (list 'a/theorem nm binders stmt
              (list 'exact (apply list (pres-name x) (qterm B)
                                  (concat (drop (count (bnames (:params B))) (bnames binders))
                                          (map #(child-term B %) (callees x)))))))
    (swap! (:renames B) assoc x nm)
    (swap! (:copied B) conj nm)
    nm))

(defn restate!
  "Restate every lemma of B's closure from `roots` that B has no lemma for yet, under the copier's
  name and statement: the generic lemma applied to B's lemmas for its callees. A primitive B has no
  cell for is restated from its generic lemma if it has one, else gets an `rfl` frame cell (prim!).
  Returns the number of lemmas added."
  [B roots]
  (aliases! B)
  (let [{:keys [nodes]} @tree
        node? (set nodes)
        need (loop [todo (vec roots) seen #{}]
               (if-let [n (first todo)]
                 (if (or (seen n) (contains? @(:renames B) n))
                   (recur (subvec todo 1) seen)
                   (recur (into (subvec todo 1) (when (node? n) (keep (fn [[k a]] (when (= k :node) a)) (callees n))))
                          (conj seen n)))
                 seen))]
    (count (doall (for [x (filter need (map first @@#'c/source-theorems))
                        :when (not (contains? @(:renames B) x))]
                    (if (node? x) (restate-one! B x) (c/prim! B x nil)))))))

(build!)
