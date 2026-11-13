(ns spindel.v2.lit
  "The spec's literal layer-1 invariants (§6) as theorems through the model's step `world-step`,
  kernel-checked (Init only). Predicates: spindel.v2.inv's `lit-*` and `inv-i10-task`.

  Bundles (inv-sample plus a rest part; every composite inv-sample lemma of `step-inv` is
  re-checked for the bundle by `lcopy!` from primitive lemmas and overrides, as spindel.v2.acts;
  `patch!` rewrites a source proof before the copy where a call needs an extra fact):
    gl   I10, task part: every run's `of` is below the allocator, every run of a task K is K.run,
         a task without result has its run, not done. Stated over key projections of the run and
         task rows (`rkeys`, `tkeys`), so an edit that keeps the keys is a frame. Overrides: a run
         made alive (resume, park: `gl-run-upd-up`), T14's local part and T12 (the run is done,
         its task gets its result: the exempt rest `glx`), T13 (`retire-rest`), run creation
         (T4 `gl-spawn-rows`, T5/T11 `gl-comp-run-o`), the Rule R filter (alive runs are kept:
         `normalized` of every round, from P2 with acts-alive).
    ch   T11 keeps C: computation cx exists through the predecessor's cancel and the cut.
    g9   I9, resources: every resource's owner is below the allocator and listed in its run's
         `resources`, phases are valid, and `lit-i9-res`. Overrides: T14's cancel-res
         (`g9-cancel-mid`), T17 arm (not in a cleanup slice, Z#40), T15 ack.

  Theorems:
    step-gl            ga w, gl w, rule-r-safe raw -> gl (world-step w it)
    step-lit-i10-task  ... -> inv-i10-task (world-step w it)   (literal I10, task part)
    step-g9            g9 w, rule-r-safe raw -> g9 (world-step w it)
    step-lit-i9-res    ... -> lit-i9-res (world-step w it)      (literal I9, resources)
    filter-safe-of-refs   P3 core: inv-sample, acts-alive, normalized and `p3-refs` (dep edges have
                       non-idle creditors, activations' runs exist, marked edges are dep edges, no
                       edge id is a cleanup row or storage ref) -> filter-safe. Their preservation
                       through the step is open (notes/ansatz-fixes.md P3); `p3-refs` runs as a
                       tripwire in lit-test.
  Model changes made for these proofs (spec-faithful, no reachable behaviour changes): `complete`
  with a result tag other than ok/err is refused (`complete-refused`; it let a task end with
  result none: inv_test complete-tag-none-refused), and cancel(R, replace) skips the debtor side
  only for a computation run (`cancel-debtor`)."
  (:require [ansatz.core :as a]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.rank :refer :all]
            [spindel.v2.casc :refer :all]
            [spindel.v2.acts :refer :all]
            [spindel.v2.inv :refer :all]))

;; ===========================================================================
;; Part A. Keys and the invariant
;; ===========================================================================

(a/structure RKey [] (id Nat) (of Nat) (alive Bool))
(a/defn rkey [r :- RunRow] RKey (RKey.mk (:id r) (:of r) (run-alive r)))
(a/defn rkey-id [k :- RKey] Nat (:id k))
(a/defn task-done [t :- TaskRow] Bool (Bool.not (Nat.beq (:tag (:result t)) res-none)))
(a/structure TKey [] (id Nat) (run Nat) (done Bool))
(a/defn tkey [t :- TaskRow] TKey (TKey.mk (:id t) (:run t) (task-done t)))
(a/defn tkey-id [k :- TKey] Nat (:id k))
(a/defn rkeys [rs :- (List RunRow)] (List RKey)
  (match rs [nil (List.nil RKey)] [(cons h t) (List.cons RKey (rkey h) (rkeys t))]))
(a/defn tkeys [ts :- (List TaskRow)] (List TKey)
  (match ts [nil (List.nil TKey)] [(cons h t) (List.cons TKey (tkey h) (tkeys t))]))

(a/defn of-below-k [n :- Nat, r :- RKey] Bool (Nat.blt (:of r) n))
;; every task with id r.of has run r.id
(a/defn trun-one [r :- RKey, t :- TKey] Bool (Bool.or (Bool.not (Nat.beq (:id t) (:of r))) (Nat.beq (:run t) (:id r))))
(a/defn trun-ok [tks :- (List TKey), r :- RKey] Bool (tbl-all (trun-one r) tks))
;; a run with id t.run, of t.id, not done
(a/defn run-for [t :- TKey, r :- RKey] Bool
  (Bool.and (Nat.beq (:id r) (:run t)) (Bool.and (Nat.beq (:of r) (:id t)) (:alive r))))
(a/defn thas-ok [rks :- (List RKey), t :- TKey] Bool (Bool.or (:done t) (tbl-any (run-for t) rks)))
(a/defn l10k [rks :- (List RKey), tks :- (List TKey), n :- Nat] Bool
  (Bool.and (tbl-all (of-below-k n) rks) (Bool.and (tbl-all (trun-ok tks) rks) (tbl-all (thas-ok rks) tks))))
(a/defn gl-rest [w :- World] Bool (l10k (rkeys (:runs w)) (tkeys (:tasks w)) (:next-id w)))
(a/defn gl [w :- World] Bool (Bool.and (inv-sample w) (gl-rest w)))

(a/theorem gl-sample [w :- World] (=> (= (gl w) true) (= (inv-sample w) true))
  (intro h) (simp only [gl Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem gl-rest-of [w :- World] (=> (= (gl w) true) (= (gl-rest w) true))
  (intro h) (simp only [gl Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem gl-intro [w :- World] (=> (= (inv-sample w) true) (= (gl-rest w) true) (= (gl w) true))
  (intros h1 h2) (simp only [gl h1 h2 Bool.and_self]))
(a/theorem gl-parts [w :- World]
  (=> (= (gl w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (gl-sample w h))))

;; ---- key lists under the table edits

(a/theorem rkeys-upd [x :- Nat, f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (rkey (f r)) (rkey r))),
                      rs :- (List RunRow)]
  (= (rkeys (tbl-upd run-id x f rs)) (rkeys rs))
  (induction rs)
  (case [nil] (simp only [tbl-upd rkeys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (run-id h) x))
    (case [false] (simp only [tbl-upd hx rkeys ih]))
    (case [true] (simp only [tbl-upd hx rkeys ih (hk h)]))))

(a/theorem tkeys-upd [x :- Nat, f :- (=> TaskRow TaskRow), hk :- (forall [t :- TaskRow] (= (tkey (f t)) (tkey t))),
                      ts :- (List TaskRow)]
  (= (tkeys (tbl-upd task-id x f ts)) (tkeys ts))
  (induction ts)
  (case [nil] (simp only [tbl-upd tkeys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (task-id h) x))
    (case [false] (simp only [tbl-upd hx tkeys ih]))
    (case [true] (simp only [tbl-upd hx tkeys ih (hk h)]))))

(a/theorem of-below-one [n :- Nat, m :- Nat, r :- RKey]
  (=> (<= n m) (= (of-below-k n r) true) (= (of-below-k m r) true))
  (intros hn hr)
  (simp only [of-below-k Nat.blt_eq] at hr) (simp only [of-below-k Nat.blt_eq])
  (exact (Nat.lt_of_lt_of_le hr hn)))

(a/theorem of-below-mono [n :- Nat, m :- Nat, rks :- (List RKey)]
  (=> (<= n m) (= (tbl-all (of-below-k n) rks) true) (= (tbl-all (of-below-k m) rks) true))
  (intros hn h)
  (exact (tbl-all-mono RKey (of-below-k n) (of-below-k m)
           (fn [r :- RKey, hr :- (= (of-below-k n r) true)] (of-below-one n m r hn hr)) rks h)))

(a/theorem gl-rest-next [w :- World, v :- Nat]
  (=> (= (gl-rest w) true) (<= (:next-id w) v) (= (gl-rest (set-next-id w v)) true))
  (intros h hv)
  (simp only [gl-rest l10k Bool.and_eq_true] at h)
  (have e1 (= (:runs (set-next-id w v)) (:runs w))) (rfl)
  (have e2 (= (:tasks (set-next-id w v)) (:tasks w))) (rfl)
  (have e3 (= (:next-id (set-next-id w v)) v)) (rfl)
  (simp only [gl-rest l10k Bool.and_eq_true e1 e2 e3])
  (exact (And.intro (of-below-mono (:next-id w) v (rkeys (:runs w)) hv (And.left h)) (And.right h))))

(a/theorem gl-rest-bump [w :- World] (=> (= (gl-rest w) true) (= (gl-rest (bump w)) true))
  (intro h) (simp only [bump]) (exact (gl-rest-next w (+ (:next-id w) 1) h (Nat.le_succ (:next-id w)))))

;; ===========================================================================
;; Part B. The bundle copier (spindel.v2.acts' copy!, with source patches)
;; ===========================================================================

(def ^:private lit-ns *ns*)

(defn- ns-source-forms [ns-sym]
  (let [path (str (-> (name ns-sym) (str/replace "." "/") (str/replace "-" "_")) ".clj")]
    (binding [*ns* (the-ns ns-sym)]
      (with-open [r (java.io.PushbackReader. (io/reader (io/resource path)))]
        (loop [acc []]
          (let [f (read {:eof ::eof} r)]
            (if (= f ::eof) acc (recur (conj acc f)))))))))

(defn- theorem-form? [f] (and (seq? f) (contains? #{'a/theorem 'ansatz.core/theorem} (first f))))

(defn- expand-top [ns-sym f]
  (cond
    (and (seq? f) (= 'do (first f))) (mapcat #(expand-top ns-sym %) (rest f))
    (and (seq? f) (symbol? (first f)) (not (theorem-form? f)))
    (let [v (binding [*ns* (the-ns ns-sym)] (resolve (first f)))]
      (if (and (var? v) (:macro (meta v)) (= (the-ns ns-sym) (:ns (meta v))))
        (expand-top ns-sym (binding [*ns* (the-ns ns-sym)] (macroexpand-1 f)))
        [f]))
    :else [f]))

(def lit-source-nss '[spindel.v2.edits spindel.v2.step spindel.v2.rule spindel.v2.engine])

(def ^:private source-theorems
  (delay (vec (for [nsym lit-source-nss, f (ns-source-forms nsym), g (expand-top nsym f) :when (theorem-form? g)]
                [(second g) g]))))

(defn- theorem-source [nm]
  (or (some (fn [[n g]] (when (= n nm) g)) @source-theorems)
      (throw (ex-info (str "no source for theorem " nm) {:name nm}))))

(defn- binder-names [binders] (vec (take-nth 3 binders)))
(defn- inv-premise? [p] (and (seq? p) (= '= (first p)) (seq? (second p)) (= 'inv-sample (first (second p)))))

;; REPL iteration only: skip a generated theorem whose name is already in the env
(defonce ^:dynamic *lit-dev-skip* false)
(defn- declared? [s] (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str s)))))

(defn- eval-theorem! [form]
  (try (when-not (and *lit-dev-skip* (declared? (second form))) (binding [*ns* lit-ns] (eval form)))
       (catch Throwable t
         (throw (ex-info (str "lit: theorem " (second form) " failed: " (ex-message t)) {:form form} t)))))

;; a bundle: :pred, :params [sym type ...], :prefix, :extra-args {lemma [form position]},
;; :renames/:overrides/:patches/:copied atoms
(defn mk-bundle [pred params prefix extra]
  {:pred pred :params params :prefix prefix :extra-args extra
   :renames (atom {}) :overrides (atom {}) :patches (atom {}) :copied (atom [])})

(defn- pargs [B] (binder-names (:params B)))
(defn- papp [B head & args] (apply list head (concat (pargs B) args)))
(defn- bsym [B suffix] (symbol (str (name (:pred B)) suffix)))

(defn- pred-subst [B x]
  (walk/postwalk (fn [y] (if (and (seq? y) (= 'inv-sample (first y))) (papp B (:pred B) (second y)) y)) x))

;; a primitive: the inv-sample lemma plus a proof of the bundle's rest part; `rest-f` is a form
;; over the binder names, premise names h0..hn and R = the rest part of the input world; nil = frame
(defn- prim-form [B orig nm rest-f]
  (let [[_ _ binders stmt] (theorem-source orig)
        prems (butlast (rest stmt))
        concl (last stmt)
        hs (vec (map-indexed (fn [i _] (symbol (str "h" i))) prems))
        i (first (keep-indexed (fn [i p] (when (inv-premise? p) i)) prems))
        w (second (second (nth prems i)))
        w2 (second (second concl))
        hi (nth hs i)
        args (concat (binder-names binders) (assoc hs i (papp B (bsym B "-sample") w hi)))
        R (papp B (bsym B "-rest-of") w hi)
        rest-term (if rest-f (walk/postwalk-replace {'R R} rest-f) (list 'Eq.trans 'e-frame R))]
    (concat
     (list 'a/theorem nm (into (vec (:params B)) binders) (pred-subst B stmt) (cons 'intros hs))
     (when-not rest-f [(list 'have 'e-frame (list '= (papp B (bsym B "-rest") w2) (papp B (bsym B "-rest") w))) '(rfl)])
     [(list 'exact (papp B (bsym B "-intro") w2 (cons orig args) rest-term))])))

(defn- copy-name [B sym]
  (let [s (name sym) p (:prefix B)]
    (symbol (cond (str/starts-with? s "inv-") (str p (subs s 4))
                  (str/ends-with? s "-inv-sample") (str (subs s 0 (- (count s) 11)) "-" (name (:pred B)))
                  (str/ends-with? s "-inv") (str (subs s 0 (- (count s) 4)) "-" (name (:pred B)))
                  :else (str s "-" (name (:pred B)))))))

(defn prim! [B orig rest-f]
  (eval-theorem! (apply list (prim-form B orig (copy-name B orig) rest-f)))
  (swap! (:renames B) assoc orig (copy-name B orig)))

(defn- copy-subst [B x rn]
  (cond
    (and (seq? x) (= 'inv-sample (first x))) (papp B (:pred B) (copy-subst B (second x) rn))
    (and (seq? x) (symbol? (first x)) (contains? rn (first x)))
    (let [h (first x)
          args (map #(copy-subst B % rn) (rest x))
          args (if-let [[e k] ((:extra-args B) h)]
                 (do (assert (>= (count args) k) (str h " applied to too few arguments: " (pr-str x)))
                     (concat (take k args) [e] (drop k args)))
                 args)]
      (apply papp B (rn h) args))
    (seq? x) (apply list (map #(copy-subst B % rn) x))
    (vector? x) (mapv #(copy-subst B % rn) x)
    (symbol? x) (cond (contains? (:extra-args B) x) (throw (ex-info (str x " used as a value") {}))
                      (contains? rn x) (papp B (rn x))
                      :else x)
    :else x))

(defn- copy-form [B form nm rn]
  (let [[head _ binders stmt & proof] form]
    (apply list head nm (into (vec (:params B)) (copy-subst B binders rn)) (copy-subst B stmt rn)
           (map #(copy-subst B % rn) proof))))

(defn- statement-mentions-inv? [form]
  (let [[_ _ binders stmt] form] (boolean (some #{'inv-sample} (flatten (list (seq binders) stmt))))))

(defn- source-of [B n]
  (let [f (theorem-source n)] (if-let [p (get @(:patches B) n)] (p f) f)))

(defn- closure [B root]
  (let [thms @source-theorems
        S (set (keep (fn [[n g]] (when (statement-mentions-inv? g) n)) thms))
        deps (fn [n]
               (cond (contains? @(:renames B) n) []
                     (contains? @(:overrides B) n) (:deps (get @(:overrides B) n))
                     :else (let [[_ _ _ _ & proof] (source-of B n)]
                             (filter S (filter symbol? (flatten proof))))))]
    (loop [todo [root] seen #{}]
      (if-let [n (first todo)]
        (if (seen n) (recur (rest todo) seen) (recur (concat (rest todo) (deps n)) (conj seen n)))
        (filterv seen (map first thms))))))

(defn- copy-one-form [B n]
  (if-let [o (get @(:overrides B) n)]
    (:form o)
    (copy-form B (source-of B n) (copy-name B n) @(:renames B))))

(defn lcopy!
  "Check the bundle version of every inv-sample lemma `root` depends on, in load order."
  [B root]
  (doseq [n (closure B root) :when (not (contains? @(:renames B) n))]
    (let [form (copy-one-form B n)]
      (eval-theorem! form)
      (swap! (:renames B) assoc n (second form))
      (swap! (:copied B) conj (second form)))))

(defn lcopy-try!
  "REPL exploration: like lcopy!, but go on after a failure; returns the failed originals (a
  failure makes its dependents fail as well)."
  [B root]
  (vec (for [n (closure B root) :when (not (contains? @(:renames B) n))
             :let [form (copy-one-form B n)
                   err (try (eval-theorem! form) nil (catch Throwable t (ex-message (or (ex-cause t) t))))]
             :when (or err (do (swap! (:renames B) assoc n (second form)) (swap! (:copied B) conj (second form)) false))]
         [n (subs err 0 (min 300 (count err)))])))

(defn override! [B orig deps form] (swap! (:overrides B) assoc orig {:deps deps :form form}))
(defn patch! [B orig f] (swap! (:patches B) assoc orig f))

;; replace every subform for which (pred form) holds by (f form)
(defn subst-forms [pred f x]
  (walk/prewalk (fn [y] (if (pred y) (f y) y)) x))
(defn app-of? [head] (fn [y] (and (seq? y) (= head (first y)))))

;; a hand-written bundle proof: `$name` is the bundle's lemma <prefix>name applied to the
;; bundle's parameters, `(%G w)` the bundle predicate of w
(defn inst [B form]
  (letfn [(dsym? [x] (and (symbol? x) (str/starts-with? (name x) "$")))
          (dname [x] (symbol (str (:prefix B) (subs (name x) 1))))
          (walk [x]
            (cond
              (and (seq? x) (= '%G (first x))) (papp B (:pred B) (walk (second x)))
              (and (seq? x) (dsym? (first x))) (apply papp B (dname (first x)) (map walk (rest x)))
              (seq? x) (apply list (map walk x))
              (vector? x) (mapv walk x)
              (dsym? x) (papp B (dname x))
              :else x))]
    (let [[head nm binders & more] form]
      (apply list head (if (dsym? nm) (dname nm) nm) (into (vec (:params B)) (walk binders)) (map walk more)))))

(def GL (mk-bundle 'gl [] "gl-"
          {'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (rkey r))) 4]
           'inv-task-upd ['(fn [t :- TaskRow] (Eq.refl (tkey t))) 4]}))
(swap! (:renames GL) assoc 'inv-parts 'gl-parts)

;; ---- the primitives

(a/theorem gl-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (rkey (f r)) (rkey r)))]
  (=> (= (gl w) true) (= (gl (run-upd w x f)) true))
  (intro h)
  (have e (= (gl-rest (run-upd w x f)) (gl-rest w)))
  (simp only [gl-rest run-upd set-runs (rkeys-upd x f hk (:runs w))])
  (exact (gl-intro _ (inv-run-upd w x f hf (gl-sample w h)) (Eq.trans e (gl-rest-of w h)))))

(a/theorem gl-task-upd [w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                        hf :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                        hk :- (forall [t :- TaskRow] (= (tkey (f t)) (tkey t)))]
  (=> (= (gl w) true) (= (gl (task-upd w x f)) true))
  (intro h)
  (have e (= (gl-rest (task-upd w x f)) (gl-rest w)))
  (simp only [gl-rest task-upd set-tasks (tkeys-upd x f hk (:tasks w))])
  (exact (gl-intro _ (inv-task-upd w x f hf (gl-sample w h)) (Eq.trans e (gl-rest-of w h)))))

(swap! (:renames GL) assoc 'inv-run-upd 'gl-run-upd 'inv-task-upd 'gl-task-upd)

(a/theorem gl-rest-mark-edge [w :- World, x :- Nat] (= (gl-rest (mark-edge w x)) (gl-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem gl-rest-unmark-edge [w :- World, x :- Nat] (= (gl-rest (unmark-edge w x)) (gl-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem gl-rest-remove-edge [w :- World, x :- Nat] (= (gl-rest (remove-edge w x)) (gl-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))

(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del
            inv-set-pins inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd
            inv-edge-upd inv-drop-cred inv-drop-edges inv-comp-del-unref inv-comp-upd inv-drop-act]]
  (prim! GL o nil))
(doseq [o '[inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-comp-ins-fresh inv-act-ins-fresh]]
  (prim! GL o (list 'gl-rest-bump (list (symbol (str/replace (subs (name o) 4) "-fresh" "")) 'w 'r)
                    (list 'Eq.trans '(rfl) 'R))))
(prim! GL 'inv-bump '(gl-rest-bump w R))
(prim! GL 'mark-edge-inv-sample '(Eq.trans (gl-rest-mark-edge w x) R))
(prim! GL 'unmark-edge-inv-sample '(Eq.trans (gl-rest-unmark-edge w x) R))
(prim! GL 'inv-remove-edge '(Eq.trans (gl-rest-remove-edge w x) R))
(prim! GL 'insert-edge-fresh-inv-sample '(gl-rest-bump (insert-edge w (edge-set-id (:next-id w) e)) (Eq.trans (rfl) R)))

;; ===========================================================================
;; Part C. The invariant under key changes
;; ===========================================================================

;; ---- generic list lemmas

(a/theorem any-upd-mono [A :- Type, idf :- (=> A Nat), x :- Nat, g :- (=> A A), p :- (=> A Bool),
                         hg :- (forall [a :- A] (=> (= (p a) true) (= (p (g a)) true))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-any p (tbl-upd idf x g xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (cases hp (p h))
    (case [false]
      (simp only [tbl-any hp Bool.false_or] at ha)
      (cases hx (Nat.beq (idf h) x))
      (all_goals (simp only [tbl-upd hx tbl-any (ih ha) Bool.or_true])))
    (case [true]
      (cases hx (Nat.beq (idf h) x))
      (case [false] (simp only [tbl-upd hx tbl-any hp Bool.true_or]))
      (case [true] (simp only [tbl-upd hx tbl-any (hg h hp) Bool.true_or])))))

(a/theorem any-upd-off [A :- Type, idf :- (=> A Nat), x :- Nat, g :- (=> A A), p :- (=> A Bool),
                        hoff :- (forall [a :- A] (=> (= (p a) true) (= (Nat.beq (idf a) x) false))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-any p (tbl-upd idf x g xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (cases hp (p h))
    (case [false]
      (simp only [tbl-any hp Bool.false_or] at ha)
      (cases hx (Nat.beq (idf h) x))
      (all_goals (simp only [tbl-upd hx tbl-any (ih ha) Bool.or_true])))
    (case [true] (simp only [tbl-upd (hoff h hp) tbl-any hp Bool.true_or]))))

(a/theorem any-del-off [A :- Type, idf :- (=> A Nat), x :- Nat, p :- (=> A Bool),
                        hoff :- (forall [a :- A] (=> (= (p a) true) (= (Nat.beq (idf a) x) false))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-any p (tbl-del idf x xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (cases hp (p h))
    (case [false]
      (simp only [tbl-any hp Bool.false_or] at ha)
      (cases hx (Nat.beq (idf h) x))
      (all_goals (simp only [tbl-del hx tbl-any (ih ha) Bool.or_true])))
    (case [true] (simp only [tbl-del (hoff h hp) tbl-any hp Bool.true_or]))))

(a/theorem any-keep-on [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), p :- (=> A Bool),
                        hon :- (forall [a :- A] (=> (= (p a) true) (= (K (idf a)) true))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-any p (tbl-keep K idf xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (cases hp (p h))
    (case [false]
      (simp only [tbl-any hp Bool.false_or] at ha)
      (cases hk (K (idf h)))
      (all_goals (simp only [tbl-keep hk tbl-any (ih ha) Bool.or_true])))
    (case [true] (simp only [tbl-keep (hon h hp) tbl-any hp Bool.true_or]))))

;; ---- the rest under key edits

;; a task without result does not have run x
(a/defn off-run [x :- Nat, t :- TKey] Bool (Bool.or (:done t) (Bool.not (Nat.beq (:run t) x))))

(a/theorem trun-one-eq [k2 :- RKey, k :- RKey, t :- TKey]
  (=> (= (:id k2) (:id k)) (= (:of k2) (:of k)) (= (trun-one k2 t) (trun-one k t)))
  (intros h1 h2) (simp only [trun-one h1 h2]))
(a/theorem trun-one-teq [k :- RKey, t2 :- TKey, t :- TKey]
  (=> (= (:id t2) (:id t)) (= (:run t2) (:run t)) (= (trun-one k t2) (trun-one k t)))
  (intros h1 h2) (simp only [trun-one h1 h2]))

(a/theorem run-for-up [t :- TKey, k :- RKey, k2 :- RKey]
  (=> (= (:id k2) (:id k)) (= (:of k2) (:of k)) (= (:alive k2) true) (= (run-for t k) true) (= (run-for t k2) true))
  (intros h1 h2 h3 h)
  (simp only [run-for Bool.and_eq_true] at h)
  (simp only [run-for h1 h2 h3 Bool.and_eq_true])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h)) True.intro))))

(a/theorem run-for-off [x :- Nat, t :- TKey, k :- RKey]
  (=> (= (off-run x t) true) (= (:done t) false) (= (run-for t k) true) (= (Nat.beq (rkey-id k) x) false))
  (intros ho hd h)
  (simp only [off-run hd Bool.false_or] at ho)
  (simp only [run-for Bool.and_eq_true] at h)
  (have e (= (:id k) (:run t))) (exact (Nat.eq_of_beq_eq_true (And.left h)))
  (simp only [rkey-id e]) (exact (bnot-true _ ho)))

(a/theorem l10k-up [rks :- (List RKey), tks :- (List TKey), n :- Nat, x :- Nat, g :- (=> RKey RKey),
                    hid :- (forall [k :- RKey] (= (:id (g k)) (:id k))),
                    hof :- (forall [k :- RKey] (= (:of (g k)) (:of k))),
                    hal :- (forall [k :- RKey] (= (:alive (g k)) true))]
  (=> (= (l10k rks tks n) true) (= (l10k (tbl-upd rkey-id x g rks) tks n) true))
  (intro h)
  (simp only [l10k Bool.and_eq_true] at h)
  (have e1 (forall [k :- RKey] (= (of-below-k n (g k)) (of-below-k n k)))) (intro k) (simp only [of-below-k (hof k)])
  (have e2 (forall [k :- RKey] (= (trun-ok tks (g k)) (trun-ok tks k))))
  (intro k) (simp only [trun-ok])
  (exact (tbl-all-congr TKey (trun-one (g k)) (trun-one k) (fn [t :- TKey] (trun-one-eq (g k) k t (hid k) (hof k))) tks))
  (have e3 (forall [t :- TKey] (=> (= (thas-ok rks t) true) (= (thas-ok (tbl-upd rkey-id x g rks) t) true))))
  (intros t ht)
  (cases hd (:done t))
  (case [true] (simp only [thas-ok hd Bool.true_or]))
  (case [false]
    (simp only [thas-ok hd Bool.false_or] at ht)
    (simp only [thas-ok hd Bool.false_or])
    (exact (any-upd-mono RKey rkey-id x g (run-for t)
             (fn [k :- RKey, hk :- (= (run-for t k) true)] (run-for-up t k (g k) (hid k) (hof k) (hal k) hk)) rks ht)))
  (simp only [l10k Bool.and_eq_true (tbl-all-upd-same RKey rkey-id x g (of-below-k n) e1 rks)
              (tbl-all-upd-same RKey rkey-id x g (trun-ok tks) e2 rks)])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (tbl-all-mono TKey (thas-ok rks) (thas-ok (tbl-upd rkey-id x g rks)) e3 tks (And.right (And.right h)))))))

(a/theorem l10k-down [rks :- (List RKey), tks :- (List TKey), n :- Nat, x :- Nat, g :- (=> RKey RKey),
                      hid :- (forall [k :- RKey] (= (:id (g k)) (:id k))),
                      hof :- (forall [k :- RKey] (= (:of (g k)) (:of k)))]
  (=> (= (l10k rks tks n) true) (= (tbl-all (off-run x) tks) true) (= (l10k (tbl-upd rkey-id x g rks) tks n) true))
  (intros h hx)
  (simp only [l10k Bool.and_eq_true] at h)
  (have e1 (forall [k :- RKey] (= (of-below-k n (g k)) (of-below-k n k)))) (intro k) (simp only [of-below-k (hof k)])
  (have e2 (forall [k :- RKey] (= (trun-ok tks (g k)) (trun-ok tks k))))
  (intro k) (simp only [trun-ok])
  (exact (tbl-all-congr TKey (trun-one (g k)) (trun-one k) (fn [t :- TKey] (trun-one-eq (g k) k t (hid k) (hof k))) tks))
  (have e3 (forall [t :- TKey] (=> (= (off-run x t) true) (= (thas-ok rks t) true) (= (thas-ok (tbl-upd rkey-id x g rks) t) true))))
  (intros t ho ht)
  (cases hd (:done t))
  (case [true] (simp only [thas-ok hd Bool.true_or]))
  (case [false]
    (simp only [thas-ok hd Bool.false_or] at ht)
    (simp only [thas-ok hd Bool.false_or])
    (exact (any-upd-off RKey rkey-id x g (run-for t)
             (fn [k :- RKey, hk :- (= (run-for t k) true)] (run-for-off x t k ho hd hk)) rks ht)))
  (simp only [l10k Bool.and_eq_true (tbl-all-upd-same RKey rkey-id x g (of-below-k n) e1 rks)
              (tbl-all-upd-same RKey rkey-id x g (trun-ok tks) e2 rks)])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (tbl-all-mono2 TKey (off-run x) (thas-ok rks) (thas-ok (tbl-upd rkey-id x g rks)) e3 tks hx (And.right (And.right h)))))))

(a/theorem l10k-del [rks :- (List RKey), tks :- (List TKey), n :- Nat, x :- Nat]
  (=> (= (l10k rks tks n) true) (= (tbl-all (off-run x) tks) true) (= (l10k (tbl-del rkey-id x rks) tks n) true))
  (intros h hx)
  (simp only [l10k Bool.and_eq_true] at h)
  (have e3 (forall [t :- TKey] (=> (= (off-run x t) true) (= (thas-ok rks t) true) (= (thas-ok (tbl-del rkey-id x rks) t) true))))
  (intros t ho ht)
  (cases hd (:done t))
  (case [true] (simp only [thas-ok hd Bool.true_or]))
  (case [false]
    (simp only [thas-ok hd Bool.false_or] at ht)
    (simp only [thas-ok hd Bool.false_or])
    (exact (any-del-off RKey rkey-id x (run-for t)
             (fn [k :- RKey, hk :- (= (run-for t k) true)] (run-for-off x t k ho hd hk)) rks ht)))
  (simp only [l10k Bool.and_eq_true])
  (exact (And.intro
           (tbl-all-del RKey rkey-id x (of-below-k n) (of-below-k n)
             (fn [k :- RKey, h1 :- (= (of-below-k n k) true), h2 :- (= (Nat.beq (rkey-id k) x) false)] h1) rks (And.left h))
           (And.intro
             (tbl-all-del RKey rkey-id x (trun-ok tks) (trun-ok tks)
               (fn [k :- RKey, h1 :- (= (trun-ok tks k) true), h2 :- (= (Nat.beq (rkey-id k) x) false)] h1) rks (And.left (And.right h)))
             (tbl-all-mono2 TKey (off-run x) (thas-ok rks) (thas-ok (tbl-del rkey-id x rks)) e3 tks hx (And.right (And.right h)))))))

;; a task gets its result (its id and run are kept)
(a/theorem l10k-done [rks :- (List RKey), tks :- (List TKey), n :- Nat, x :- Nat, g :- (=> TKey TKey),
                      hid :- (forall [t :- TKey] (= (:id (g t)) (:id t))),
                      hrun :- (forall [t :- TKey] (= (:run (g t)) (:run t))),
                      hd :- (forall [t :- TKey] (= (:done (g t)) true))]
  (=> (= (l10k rks tks n) true) (= (l10k rks (tbl-upd tkey-id x g tks) n) true))
  (intro h)
  (simp only [l10k Bool.and_eq_true] at h)
  (have e2 (forall [k :- RKey] (= (trun-ok (tbl-upd tkey-id x g tks) k) (trun-ok tks k))))
  (intro k) (simp only [trun-ok])
  (exact (tbl-all-upd-same TKey tkey-id x g (trun-one k)
           (fn [t :- TKey] (trun-one-teq k (g t) t (hid t) (hrun t)))
           tks))
  (have hin (forall [t :- TKey] (=> (= (thas-ok rks t) true) (= (Nat.beq (tkey-id t) x) true) (= (thas-ok rks (g t)) true))))
  (intros t h1 h2) (simp only [thas-ok (hd t) Bool.true_or])
  (have hout (forall [t :- TKey] (=> (= (thas-ok rks t) true) (= (Nat.beq (tkey-id t) x) false) (= (thas-ok rks t) true))))
  (intros t h1 h2) (exact h1)
  (simp only [l10k Bool.and_eq_true (tbl-all-congr RKey (trun-ok (tbl-upd tkey-id x g tks)) (trun-ok tks) e2 rks)])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (tbl-all-upd TKey tkey-id x g (thas-ok rks) (thas-ok rks) hin hout tks (And.right (And.right h)))))))

;; ---- unique ids

(a/defn same-id-then [A :- Type :implicit, idf :- (=> A Nat), x :- Nat, Q :- (=> A Bool), b :- A] Bool
  (Bool.or (Bool.not (Nat.beq (idf b) x)) (Q b)))

(a/theorem mem-ids-has [A :- Type, idf :- (=> A Nat), a :- A, xs :- (List A)]
  (=> (List.Mem a xs) (= (nat-mem (idf a) (tbl-ids idf xs)) true))
  (induction xs)
  (case [nil] (intro hm) (cases hm))
  (case [cons h t ih]
    (intro hm)
    (cases hm)
    (simp [nat-mem tbl-ids])
    (rename_i hm2)
    (cases hx (Nat.beq (idf h) (idf a)))
    (all_goals (simp only [nat-mem tbl-ids hx]))
    (exact (ih hm2))))

(a/theorem absent-then [A :- Type, idf :- (=> A Nat), x :- Nat, Q :- (=> A Bool), xs :- (List A)]
  (=> (= (nat-mem x (tbl-ids idf xs)) false) (= (tbl-all (same-id-then idf x Q) xs) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-all]))
  (case [cons h t ih]
    (intro hn)
    (cases hx (Nat.beq (idf h) x))
    (case [true] (simp [nat-mem tbl-ids hx] at hn))
    (case [false]
      (simp only [nat-mem tbl-ids hx] at hn)
      (simp only [tbl-all same-id-then hx Bool.not_false Bool.true_or Bool.true_and])
      (exact (ih hn)))))

;; with unique ids, every row with a's id satisfies Q when a does
(a/theorem uniq-all [A :- Type, idf :- (=> A Nat), Q :- (=> A Bool), a :- A, xs :- (List A)]
  (=> (= (nat-nodup (tbl-ids idf xs)) true) (List.Mem a xs) (= (Q a) true)
      (= (tbl-all (same-id-then idf (idf a) Q) xs) true))
  (induction xs)
  (case [nil] (intros hn hm hq) (cases hm))
  (case [cons h t ih]
    (intros hn hm hq)
    (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
    (have hn1 := (bnot-true _ (And.left hn)))
    (cases hm)
    (case [head]
      (simp only [tbl-all same-id-then hq Bool.or_true Bool.true_and])
      (exact (absent-then _ idf _ Q _ hn1)))
    (case [tail]
      (rename_i hm2)
      (have hne (= (Nat.beq (idf h) (idf a)) false))
      (cases he (Nat.beq (idf h) (idf a)))
      (rfl)
      (have e (= (idf h) (idf a))) (exact (Nat.eq_of_beq_eq_true he))
      (have hm3 := (mem-ids-has _ idf a _ hm2))
      (rw [← e] at hm3) (rw [hm3] at hn1) (cases hn1)
      (simp only [tbl-all same-id-then hne Bool.not_false Bool.true_or Bool.true_and])
      (exact (ih (And.right hn) hm2 hq)))))

(a/theorem nodup-app-disj [x :- Nat, xs :- (List Nat), ys :- (List Nat)]
  (=> (= (nat-nodup (nat-app xs ys)) true) (= (nat-mem x xs) true) (= (nat-mem x ys) false))
  (induction xs)
  (case [nil] (intros hn hm) (simp [nat-mem] at hm))
  (case [cons h t ih]
    (intros hn hm)
    (simp only [nat-app nat-nodup Bool.and_eq_true] at hn)
    (cases hx (Nat.beq h x))
    (case [false] (simp only [nat-mem hx] at hm) (exact (ih (And.right hn) hm)))
    (case [true]
      (have e (= h x)) (exact (Nat.eq_of_beq_eq_true hx))
      (have h1 := (bnot-true _ (And.left hn)))
      (simp only [nat-mem-app Bool.or_eq_false_iff] at h1)
      (rw [e] at h1) (exact (And.right h1)))))

(a/theorem ids-unique-of [w :- World]
  (=> (= (inv-sample w) true) (= (nat-nodup (all-ids w)) true))
  (intro h)
  (have hi := (And.right (And.right (inv-parts w h))))
  (simp only [ids-ok ids-unique Bool.and_eq_true] at hi)
  (exact (And.left hi)))

(a/theorem lit-runs-nodup [w :- World]
  (=> (= (inv-sample w) true) (= (nat-nodup (tbl-ids run-id (:runs w))) true))
  (intro h)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (exact (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u))))))

(a/theorem tasks-nodup [w :- World]
  (=> (= (inv-sample w) true) (= (nat-nodup (tbl-ids task-id (:tasks w))) true))
  (intro h)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (exact (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u)))))

;; a computation id is no task id
(a/theorem comp-not-task [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (comp-has w x) true) (= (nat-mem x (tbl-ids task-id (:tasks w))) false))
  (intros h hc)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have u2 := (nat-nodup-app-right _ _ u))
  (have hm (= (nat-mem x (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hc)
  (have d := (nodup-app-disj x _ _ u2 hm))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
  (exact (And.left d)))

;; ---- key lists of the rows

(a/defn on-rkey [P :- (=> RKey Bool), r :- RunRow] Bool (P (rkey r)))
(a/defn on-tkey [P :- (=> TKey Bool), t :- TaskRow] Bool (P (tkey t)))
(a/theorem all-rkeys [P :- (=> RKey Bool), rs :- (List RunRow)] (= (tbl-all P (rkeys rs)) (tbl-all (on-rkey P) rs))
  (induction rs) (case [nil] (simp only [rkeys tbl-all])) (case [cons h t ih] (simp only [rkeys tbl-all on-rkey ih])))
(a/theorem all-tkeys [P :- (=> TKey Bool), ts :- (List TaskRow)] (= (tbl-all P (tkeys ts)) (tbl-all (on-tkey P) ts))
  (induction ts) (case [nil] (simp only [tkeys tbl-all])) (case [cons h t ih] (simp only [tkeys tbl-all on-tkey ih])))

(a/defn not-id [x :- Nat, t :- TKey] Bool (Bool.not (Nat.beq (:id t) x)))
(a/theorem not-id-tasks [x :- Nat, ts :- (List TaskRow)]
  (=> (= (nat-mem x (tbl-ids task-id ts)) false) (= (tbl-all (not-id x) (tkeys ts)) true))
  (induction ts)
  (case [nil] (intro h) (simp [tkeys tbl-all]))
  (case [cons h t ih]
    (intro hn)
    (cases hx (Nat.beq (task-id h) x))
    (case [true] (simp [nat-mem tbl-ids hx] at hn))
    (case [false]
      (simp only [nat-mem tbl-ids hx] at hn)
      (have hx2 (= (Nat.beq (:id h) x) false)) (exact hx)
      (simp only [tkeys tbl-all not-id tkey hx2 Bool.not_false Bool.true_and])
      (exact (ih hn)))))

(a/theorem find-none-tasks [x :- Nat, ts :- (List TaskRow)]
  (=> (= (tbl-find task-id x ts) (Option.none TaskRow)) (= (tbl-all (not-id x) (tkeys ts)) true))
  (induction ts)
  (case [nil] (intro h) (simp [tkeys tbl-all]))
  (case [cons h t ih]
    (intro hn)
    (cases hx (Nat.beq (task-id h) x))
    (case [true] (simp [tbl-find hx] at hn))
    (case [false]
      (simp only [tbl-find hx] at hn)
      (have hx2 (= (Nat.beq (:id h) x) false)) (exact hx)
      (simp only [tkeys tbl-all not-id tkey hx2 Bool.not_false Bool.true_and])
      (exact (ih hn)))))

(a/defn of-is [k :- Nat, b :- RunRow] Bool (Nat.beq (:of b) k))
(a/defn of-at [x :- Nat, k :- Nat, r :- RKey] Bool (Bool.or (Bool.not (Nat.beq (:id r) x)) (Nat.beq (:of r) k)))
(a/defn not-alive [b :- RunRow] Bool (Bool.not (run-alive b)))
(a/defn dead-at [x :- Nat, r :- RKey] Bool (Bool.or (Bool.not (Nat.beq (:id r) x)) (Bool.not (:alive r))))

(a/theorem of-at-runs [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (List.Mem r (:runs w)) (= (tbl-all (of-at (:id r) (:of r)) (rkeys (:runs w))) true))
  (intros h hm)
  (have u := (uniq-all RunRow run-id (of-is (:of r)) r (:runs w) (lit-runs-nodup w h) hm (Nat.beq_refl (:of r))))
  (rw [all-rkeys])
  (exact (Eq.trans (tbl-all-congr RunRow (on-rkey (of-at (:id r) (:of r))) (same-id-then run-id (run-id r) (of-is (:of r)))
                     (fn [b :- RunRow] (Eq.refl (on-rkey (of-at (:id r) (:of r)) b))) (:runs w)) u)))

(a/theorem dead-at-runs [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (List.Mem r (:runs w)) (= (run-alive r) false)
      (= (tbl-all (dead-at (:id r)) (rkeys (:runs w))) true))
  (intros h hm ha)
  (have hq (= (not-alive r) true)) (simp only [not-alive ha Bool.not_false])
  (have u := (uniq-all RunRow run-id not-alive r (:runs w) (lit-runs-nodup w h) hm hq))
  (rw [all-rkeys])
  (exact (Eq.trans (tbl-all-congr RunRow (on-rkey (dead-at (:id r))) (same-id-then run-id (run-id r) not-alive)
                     (fn [b :- RunRow] (Eq.refl (on-rkey (dead-at (:id r)) b))) (:runs w)) u)))

(a/defn both [A :- Type :implicit, p :- (=> A Bool), q :- (=> A Bool), a :- A] Bool (Bool.and (p a) (q a)))
(a/theorem both-left [A :- Type, p :- (=> A Bool), q :- (=> A Bool), a :- A] (=> (= (both p q a) true) (= (p a) true))
  (intro h) (simp only [both Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem both-right [A :- Type, p :- (=> A Bool), q :- (=> A Bool), a :- A] (=> (= (both p q a) true) (= (q a) true))
  (intro h) (simp only [both Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem any-and-all [A :- Type, p :- (=> A Bool), q :- (=> A Bool), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-all q xs) true) (= (tbl-any (both p q) xs) true))
  (induction xs)
  (case [nil] (intros h1 h2) (simp [tbl-any] at h1))
  (case [cons h t ih]
    (intros h1 h2)
    (simp only [tbl-all Bool.and_eq_true] at h2)
    (cases hp (p h))
    (case [true] (simp only [tbl-any both hp (And.left h2) Bool.and_self Bool.true_or]))
    (case [false]
      (simp only [tbl-any hp Bool.false_or] at h1)
      (simp only [tbl-any (ih h1 (And.right h2)) Bool.or_true]))))

;; ---- the exempt rest: task k may be without result and run

(a/defn thas-x [k :- Nat, rks :- (List RKey), t :- TKey] Bool (Bool.or (Nat.beq (:id t) k) (thas-ok rks t)))
(a/defn l10kx [k :- Nat, rks :- (List RKey), tks :- (List TKey), n :- Nat] Bool
  (Bool.and (tbl-all (of-below-k n) rks) (Bool.and (tbl-all (trun-ok tks) rks) (tbl-all (thas-x k rks) tks))))

(a/theorem run-for-at [x :- Nat, k :- Nat, t :- TKey, kk :- RKey]
  (=> (= (of-at x k kk) true) (= (Nat.beq (:id t) k) false) (= (run-for t kk) true) (= (Nat.beq (rkey-id kk) x) false))
  (intros ho hk hr)
  (simp only [run-for Bool.and_eq_true] at hr)
  (have e (= (:of kk) (:id t))) (exact (Nat.eq_of_beq_eq_true (And.left (And.right hr))))
  (simp only [rkey-id])
  (cases hx (Nat.beq (:id kk) x))
  (case [false] (rfl))
  (case [true]
    (simp only [of-at hx Bool.not_true Bool.false_or] at ho)
    (have e2 (= (:of kk) k)) (exact (Nat.eq_of_beq_eq_true ho))
    (rw [e] at e2) (rw [e2] at hk) (simp at hk)))

(a/theorem l10k-kill [rks :- (List RKey), tks :- (List TKey), n :- Nat, x :- Nat, k :- Nat, g :- (=> RKey RKey),
                      hid :- (forall [kk :- RKey] (= (:id (g kk)) (:id kk))),
                      hof :- (forall [kk :- RKey] (= (:of (g kk)) (:of kk)))]
  (=> (= (l10k rks tks n) true) (= (tbl-all (of-at x k) rks) true) (= (l10kx k (tbl-upd rkey-id x g rks) tks n) true))
  (intros h hx)
  (simp only [l10k Bool.and_eq_true] at h)
  (have e1 (forall [kk :- RKey] (= (of-below-k n (g kk)) (of-below-k n kk)))) (intro kk) (simp only [of-below-k (hof kk)])
  (have e2 (forall [kk :- RKey] (= (trun-ok tks (g kk)) (trun-ok tks kk))))
  (intro kk) (simp only [trun-ok])
  (exact (tbl-all-congr TKey (trun-one (g kk)) (trun-one kk) (fn [t :- TKey] (trun-one-eq (g kk) kk t (hid kk) (hof kk))) tks))
  (have e3 (forall [t :- TKey] (=> (= (thas-ok rks t) true) (= (thas-x k (tbl-upd rkey-id x g rks) t) true))))
  (intros t ht)
  (cases hk (Nat.beq (:id t) k))
  (case [true] (simp only [thas-x hk Bool.true_or]))
  (case [false]
    (simp only [thas-x hk Bool.false_or])
    (cases hd (:done t))
    (case [true] (simp only [thas-ok hd Bool.true_or]))
    (case [false]
      (simp only [thas-ok hd Bool.false_or] at ht)
      (simp only [thas-ok hd Bool.false_or])
      (have hb := (any-and-all RKey (run-for t) (of-at x k) rks ht hx))
      (have hoff (forall [kk :- RKey] (=> (= (both (run-for t) (of-at x k) kk) true) (= (Nat.beq (rkey-id kk) x) false))))
      (intros kk hkk) (simp only [both Bool.and_eq_true] at hkk) (exact (run-for-at x k t kk (And.right hkk) hk (And.left hkk)))
      (exact (tbl-any-mono RKey (both (run-for t) (of-at x k)) (run-for t) (both-left RKey (run-for t) (of-at x k)) _
               (any-upd-off RKey rkey-id x g (both (run-for t) (of-at x k)) hoff rks hb)))))
  (simp only [l10kx Bool.and_eq_true (tbl-all-upd-same RKey rkey-id x g (of-below-k n) e1 rks)
              (tbl-all-upd-same RKey rkey-id x g (trun-ok tks) e2 rks)])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (tbl-all-mono TKey (thas-ok rks) (thas-x k (tbl-upd rkey-id x g rks)) e3 tks (And.right (And.right h)))))))

(a/theorem l10kx-done [rks :- (List RKey), tks :- (List TKey), n :- Nat, k :- Nat, g :- (=> TKey TKey),
                       hid :- (forall [t :- TKey] (= (:id (g t)) (:id t))),
                       hrun :- (forall [t :- TKey] (= (:run (g t)) (:run t))),
                       hd :- (forall [t :- TKey] (= (:done (g t)) true))]
  (=> (= (l10kx k rks tks n) true) (= (l10k rks (tbl-upd tkey-id k g tks) n) true))
  (intro h)
  (simp only [l10kx Bool.and_eq_true] at h)
  (have e2 (forall [kk :- RKey] (= (trun-ok (tbl-upd tkey-id k g tks) kk) (trun-ok tks kk))))
  (intro kk) (simp only [trun-ok])
  (exact (tbl-all-upd-same TKey tkey-id k g (trun-one kk) (fn [t :- TKey] (trun-one-teq kk (g t) t (hid t) (hrun t))) tks))
  (have hin (forall [t :- TKey] (=> (= (thas-x k rks t) true) (= (Nat.beq (tkey-id t) k) true) (= (thas-ok rks (g t)) true))))
  (intros t h1 h2) (simp only [thas-ok (hd t) Bool.true_or])
  (have hout (forall [t :- TKey] (=> (= (thas-x k rks t) true) (= (Nat.beq (tkey-id t) k) false) (= (thas-ok rks t) true))))
  (intros t h1 h2)
  (have h3 (= (Nat.beq (:id t) k) false)) (exact h2)
  (simp only [thas-x h3 Bool.false_or] at h1) (exact h1)
  (simp only [l10k Bool.and_eq_true (tbl-all-congr RKey (trun-ok (tbl-upd tkey-id k g tks)) (trun-ok tks) e2 rks)])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (tbl-all-upd TKey tkey-id k g (thas-x k rks) (thas-ok rks) hin hout tks (And.right (And.right h)))))))

(a/theorem l10kx-none [rks :- (List RKey), tks :- (List TKey), n :- Nat, k :- Nat]
  (=> (= (l10kx k rks tks n) true) (= (tbl-all (not-id k) tks) true) (= (l10k rks tks n) true))
  (intros h hn)
  (simp only [l10kx Bool.and_eq_true] at h)
  (have hpq (forall [t :- TKey] (=> (= (not-id k t) true) (= (thas-x k rks t) true) (= (thas-ok rks t) true))))
  (intros t h1 h2)
  (simp only [not-id] at h1)
  (simp only [thas-x (bnot-true _ h1) Bool.false_or] at h2) (exact h2)
  (simp only [l10k Bool.and_eq_true])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (tbl-all-mono2 TKey (not-id k) (thas-x k rks) (thas-ok rks) hpq tks hn (And.right (And.right h)))))))

(a/defn const-b [b :- Bool, kk :- RKey] Bool b)
(a/theorem any-const [b :- Bool, xs :- (List RKey)] (=> (= (tbl-any (const-b b) xs) true) (= b true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (simp only [tbl-any const-b Bool.or_eq_true] at ha)
    (cases ha)
    (case [inl h1] (exact h1))
    (case [inr h2] (exact (ih h2)))))
(a/theorem any-all-imp [A :- Type, p :- (=> A Bool), q :- (=> A Bool), r :- (=> A Bool),
                        h :- (forall [a :- A] (=> (= (p a) true) (= (q a) true) (= (r a) true))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-all q xs) true) (= (tbl-any r xs) true))
  (intros h1 h2)
  (exact (tbl-any-mono A (both p q) r
           (fn [a :- A, ha :- (= (both p q a) true)]
             (h a (both-left A p q a ha) (both-right A p q a ha)))
           xs (any-and-all A p q xs h1 h2))))

(a/theorem dead-run [t :- TKey, x :- Nat, kk :- RKey]
  (=> (= (run-for t kk) true) (= (dead-at x kk) true) (= (const-b (Bool.not (Nat.beq (:run t) x)) kk) true))
  (intros h1 h2)
  (simp only [run-for Bool.and_eq_true] at h1)
  (have e (= (:id kk) (:run t))) (exact (Nat.eq_of_beq_eq_true (And.left h1)))
  (simp only [dead-at (And.right (And.right h1)) Bool.not_true Bool.or_false] at h2)
  (rw [e] at h2) (simp only [const-b]) (exact h2))

;; all rows with id x are done: no task without result has run x
(a/theorem dead-off [rks :- (List RKey), tks :- (List TKey), n :- Nat, x :- Nat]
  (=> (= (l10k rks tks n) true) (= (tbl-all (dead-at x) rks) true) (= (tbl-all (off-run x) tks) true))
  (intros h hd)
  (simp only [l10k Bool.and_eq_true] at h)
  (have hin (forall [t :- TKey] (=> (= (thas-ok rks t) true) (= (off-run x t) true))))
  (intros t ht)
  (cases hdn (:done t))
  (case [true] (simp only [off-run hdn Bool.true_or]))
  (case [false]
    (simp only [thas-ok hdn Bool.false_or] at ht)
    (have hc := (any-all-imp RKey (run-for t) (dead-at x) (const-b (Bool.not (Nat.beq (:run t) x)))
                  (fn [kk :- RKey, h1 :- (= (run-for t kk) true), h2 :- (= (dead-at x kk) true)] (dead-run t x kk h1 h2)) rks ht hd))
    (simp only [off-run hdn Bool.false_or])
    (exact (any-const _ rks hc)))
  (exact (tbl-all-mono TKey (thas-ok rks) (off-run x) hin tks (And.right (And.right h)))))

(a/defn clr [t :- TKey] TKey (TKey.mk (:id t) 0 (:done t)))
(a/defn run-is-if [k :- Nat, x :- Nat, t :- TKey] Bool (Bool.or (Bool.not (Nat.beq (:id t) k)) (Nat.beq (:run t) x)))
(a/defn done-if-id [k :- Nat, t :- TKey] Bool (Bool.or (Bool.not (Nat.beq (:id t) k)) (:done t)))

(a/theorem all-upd2 [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), P :- (=> A Bool), R :- (=> A Bool), Q :- (=> A Bool),
                     hin :- (forall [r :- A] (=> (= (P r) true) (= (R r) true) (= (Nat.beq (idf r) x) true) (= (Q (f r)) true))),
                     hout :- (forall [r :- A] (=> (= (P r) true) (= (R r) true) (= (Nat.beq (idf r) x) false) (= (Q r) true))),
                     xs :- (List A)]
  (=> (= (tbl-all P xs) true) (= (tbl-all R xs) true) (= (tbl-all Q (tbl-upd idf x f xs)) true))
  (induction xs)
  (case [nil] (intros h1 h2) (simp [tbl-all tbl-upd]))
  (case [cons h t ih]
    (intros h1 h2)
    (simp only [tbl-all Bool.and_eq_true] at h1)
    (simp only [tbl-all Bool.and_eq_true] at h2)
    (have r := (ih (And.right h1) (And.right h2)))
    (cases hx (Nat.beq (idf h) x))
    (case [false] (simp only [tbl-upd hx tbl-all (hout h (And.left h1) (And.left h2) hx) r Bool.and_self]))
    (case [true] (simp only [tbl-upd hx tbl-all (hin h (And.left h1) (And.left h2) hx) r Bool.and_self]))))

(a/theorem trun-clear [k :- Nat, x :- Nat, kk :- RKey, t :- TKey]
  (=> (= (trun-one kk t) true) (= (run-is-if k x t) true) (= (Nat.beq (tkey-id t) k) true) (= (Nat.beq (rkey-id kk) x) false)
      (= (trun-one kk (clr t)) true))
  (intros h1 h2 h3 h4)
  (have e (= (:id t) k)) (exact (Nat.eq_of_beq_eq_true h3))
  (have h3b (= (Nat.beq (:id t) k) true)) (exact h3)
  (simp only [run-is-if h3b Bool.not_true Bool.false_or] at h2)
  (have ex (= (:run t) x)) (exact (Nat.eq_of_beq_eq_true h2))
  (cases ho (Nat.beq (:id t) (:of kk)))
  (case [false] (simp only [trun-one clr ho Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [trun-one ho Bool.not_true Bool.false_or] at h1)
    (have e2 (= (:run t) (:id kk))) (exact (Nat.eq_of_beq_eq_true h1))
    (rw [ex] at e2)
    (simp only [rkey-id] at h4) (rw [← e2] at h4) (simp at h4)))

(a/theorem thas-clr [k :- Nat, rks :- (List RKey), t :- TKey]
  (=> (= (done-if-id k t) true) (= (Nat.beq (tkey-id t) k) true) (= (thas-ok rks (clr t)) true))
  (intros h1 h2)
  (have h3 (= (Nat.beq (:id t) k) true)) (exact h2)
  (simp only [done-if-id h3 Bool.not_true Bool.false_or] at h1)
  (simp only [thas-ok clr h1 Bool.true_or]))

(a/theorem l10k-clear-del [rks :- (List RKey), tks :- (List TKey), n :- Nat, x :- Nat, k :- Nat]
  (=> (= (l10k rks tks n) true) (= (tbl-all (dead-at x) rks) true) (= (tbl-all (run-is-if k x) tks) true)
      (= (l10k (tbl-del rkey-id x rks) (tbl-upd tkey-id k clr tks) n) true))
  (intros h hd hr)
  (have hoff := (dead-off rks tks n x h hd))
  (have h1 := (l10k-del rks tks n x h hoff))
  (simp only [l10k Bool.and_eq_true] at h1)
  (simp only [l10k Bool.and_eq_true] at h)
  (have hkeep (forall [kk :- RKey] (=> (= (trun-ok tks kk) true) (= (Nat.beq (rkey-id kk) x) false)
                                       (= (trun-ok (tbl-upd tkey-id k clr tks) kk) true))))
  (intros kk ht hx)
  (simp only [trun-ok] at ht) (simp only [trun-ok])
  (exact (all-upd2 TKey tkey-id k clr (trun-one kk) (run-is-if k x) (trun-one kk)
           (fn [t :- TKey, a1 :- (= (trun-one kk t) true), a2 :- (= (run-is-if k x t) true), a3 :- (= (Nat.beq (tkey-id t) k) true)]
             (trun-clear k x kk t a1 a2 a3 hx))
           (fn [t :- TKey, a1 :- (= (trun-one kk t) true), a2 :- (= (run-is-if k x t) true), a3 :- (= (Nat.beq (tkey-id t) k) false)] a1)
           tks ht hr))
  (have htr := (tbl-all-del RKey rkey-id x (trun-ok tks) (trun-ok (tbl-upd tkey-id k clr tks)) hkeep rks (And.left (And.right h))))
  (have hdi (forall [t :- TKey] (=> (= (run-is-if k x t) true) (= (off-run x t) true) (= (done-if-id k t) true))))
  (intros t a1 a2)
  (cases hk (Nat.beq (:id t) k))
  (case [false] (simp only [done-if-id hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [run-is-if hk Bool.not_true Bool.false_or] at a1)
    (simp only [off-run a1 Bool.not_true Bool.or_false] at a2)
    (simp only [done-if-id hk a2 Bool.or_true]))
  (have hd2 := (tbl-all-mono2 TKey (run-is-if k x) (off-run x) (done-if-id k) hdi tks hr hoff))
  (have hth := (all-upd2 TKey tkey-id k clr (thas-ok (tbl-del rkey-id x rks)) (done-if-id k) (thas-ok (tbl-del rkey-id x rks))
                 (fn [t :- TKey, a1 :- (= (thas-ok (tbl-del rkey-id x rks) t) true), a2 :- (= (done-if-id k t) true),
                      a3 :- (= (Nat.beq (tkey-id t) k) true)]
                   (thas-clr k (tbl-del rkey-id x rks) t a2 a3))
                 (fn [t :- TKey, a1 :- (= (thas-ok (tbl-del rkey-id x rks) t) true), a2 :- (= (done-if-id k t) true),
                      a3 :- (= (Nat.beq (tkey-id t) k) false)] a1)
                 tks (And.right (And.right h1)) hd2))
  (simp only [l10k Bool.and_eq_true])
  (exact (And.intro (And.left h1) (And.intro htr hth))))

;; ---- new rows

(a/theorem not-id-trun [o :- Nat, m :- Nat, t :- TKey]
  (=> (= (not-id o t) true) (= (trun-one (RKey.mk m o true) t) true))
  (intro h) (simp only [not-id] at h) (simp only [trun-one h Bool.true_or]))

(a/theorem thas-cons [rks :- (List RKey), kk :- RKey, t :- TKey]
  (=> (= (thas-ok rks t) true) (= (thas-ok (List.cons RKey kk rks) t) true))
  (intro h)
  (cases hd (:done t))
  (case [true] (simp only [thas-ok hd Bool.true_or]))
  (case [false]
    (simp only [thas-ok hd Bool.false_or] at h)
    (simp only [thas-ok hd Bool.false_or tbl-any h Bool.or_true])))

(a/theorem l10k-ins-run [rks :- (List RKey), tks :- (List TKey), n :- Nat, n2 :- Nat, m :- Nat, o :- Nat]
  (=> (= (l10k rks tks n) true) (<= n n2) (< o n2) (= (tbl-all (not-id o) tks) true)
      (= (l10k (List.cons RKey (RKey.mk m o true) rks) tks n2) true))
  (intros h hn ho hnt)
  (simp only [l10k Bool.and_eq_true] at h)
  (have h1 (= (of-below-k n2 (RKey.mk m o true)) true)) (simp only [of-below-k Nat.blt_eq]) (exact ho)
  (have h2 (= (trun-ok tks (RKey.mk m o true)) true))
  (simp only [trun-ok])
  (exact (tbl-all-mono TKey (not-id o) (trun-one (RKey.mk m o true)) (not-id-trun o m) tks hnt))
  (have h3 := (tbl-all-mono TKey (thas-ok rks) (thas-ok (List.cons RKey (RKey.mk m o true) rks))
                (thas-cons rks (RKey.mk m o true)) tks (And.right (And.right h))))
  (simp only [l10k tbl-all Bool.and_eq_true h1 h2 Bool.true_and])
  (exact (And.intro (of-below-mono n n2 rks hn (And.left h)) (And.intro (And.left (And.right h)) h3))))

(a/theorem trun-new-task [n :- Nat, m :- Nat, kk :- RKey]
  (=> (= (of-below-k n kk) true) (= (trun-one kk (TKey.mk n m false)) true))
  (intro h)
  (simp only [of-below-k Nat.blt_eq] at h)
  (have hne (= (Nat.beq n (:of kk)) false))
  (cases hb (Nat.beq n (:of kk)))
  (rfl)
  (have e (= n (:of kk))) (exact (Nat.eq_of_beq_eq_true hb))
  (rw [e] at h) (omega)
  (simp only [trun-one hne Bool.not_false Bool.true_or]))

(a/theorem l10k-ins-task [rks :- (List RKey), tks :- (List TKey), n :- Nat, n2 :- Nat, m :- Nat]
  (=> (= (l10k rks tks n) true) (< n n2) (= (tbl-all (not-id n) tks) true)
      (= (l10k (List.cons RKey (RKey.mk m n true) rks) (List.cons TKey (TKey.mk n m false) tks) n2) true))
  (intros h hn hnt)
  (simp only [l10k Bool.and_eq_true] at h)
  (have h1 (= (of-below-k n2 (RKey.mk m n true)) true)) (simp only [of-below-k Nat.blt_eq]) (exact hn)
  (have h2 (= (trun-ok (List.cons TKey (TKey.mk n m false) tks) (RKey.mk m n true)) true))
  (simp only [trun-ok tbl-all trun-one Nat.beq_refl Bool.not_true Bool.false_or Bool.true_and])
  (exact (tbl-all-mono TKey (not-id n) (trun-one (RKey.mk m n true)) (not-id-trun n m) tks hnt))
  (have h2b (forall [kk :- RKey] (=> (= (of-below-k n kk) true) (= (trun-ok tks kk) true)
                                     (= (trun-ok (List.cons TKey (TKey.mk n m false) tks) kk) true))))
  (intros kk a1 a2)
  (simp only [trun-ok] at a2)
  (simp only [trun-ok tbl-all (trun-new-task n m kk a1) a2 Bool.and_self])
  (have h3 (= (thas-ok (List.cons RKey (RKey.mk m n true) rks) (TKey.mk n m false)) true))
  (simp only [thas-ok tbl-any run-for Nat.beq_refl Bool.and_self Bool.true_or Bool.or_true])
  (have h4 := (tbl-all-mono TKey (thas-ok rks) (thas-ok (List.cons RKey (RKey.mk m n true) rks))
                (thas-cons rks (RKey.mk m n true)) tks (And.right (And.right h))))
  (have nle (<= n n2)) (omega)
  (simp only [l10k tbl-all Bool.and_eq_true h1 h2 h3 Bool.true_and])
  (exact (And.intro (of-below-mono n n2 rks nle (And.left h))
           (And.intro (tbl-all-mono2 RKey (of-below-k n) (trun-ok tks) (trun-ok (List.cons TKey (TKey.mk n m false) tks)) h2b rks
                        (And.left h) (And.left (And.right h)))
                      h4))))

;; ---- facts from inv-sample

(a/theorem ids-below-of [w :- World]
  (=> (= (inv-sample w) true) (= (tbl-all (id-in-range (:next-id w)) (all-ids w)) true))
  (intro h)
  (have hi := (And.right (And.right (inv-parts w h))))
  (simp only [ids-ok ids-below Bool.and_eq_true] at hi)
  (exact (And.right (And.right hi))))

(a/theorem range-not-id [n :- Nat, ts :- (List TaskRow)]
  (=> (= (tbl-all (id-in-range n) (tbl-ids task-id ts)) true) (= (tbl-all (not-id n) (tkeys ts)) true))
  (induction ts)
  (case [nil] (intro h) (simp [tkeys tbl-all]))
  (case [cons h t ih]
    (intro ha)
    (simp only [tbl-ids tbl-all Bool.and_eq_true] at ha)
    (have h1 := (And.left ha))
    (simp only [id-in-range task-id Bool.and_eq_true Nat.blt_eq] at h1)
    (have hne (= (Nat.beq (:id h) n) false))
    (cases hb (Nat.beq (:id h) n))
    (rfl)
    (have e (= (:id h) n)) (exact (Nat.eq_of_beq_eq_true hb))
    (rw [e] at h1) (omega)
    (simp only [tkeys tbl-all not-id tkey hne Bool.not_false Bool.true_and])
    (exact (ih (And.right ha)))))

(a/theorem tasks-below [w :- World]
  (=> (= (inv-sample w) true) (= (tbl-all (not-id (:next-id w)) (tkeys (:tasks w))) true))
  (intro h)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (exact (range-not-id (:next-id w) (:tasks w) (And.left (And.right (And.right hb))))))

(a/theorem all-nat-mem [p :- (=> Nat Bool), x :- Nat, xs :- (List Nat)]
  (=> (= (tbl-all p xs) true) (= (nat-mem x xs) true) (= (p x) true))
  (induction xs)
  (case [nil] (intros h1 h2) (simp [nat-mem] at h2))
  (case [cons h t ih]
    (intros h1 h2)
    (simp only [tbl-all Bool.and_eq_true] at h1)
    (cases hx (Nat.beq h x))
    (case [true] (have e (= h x)) (exact (Nat.eq_of_beq_eq_true hx)) (rw [← e]) (exact (And.left h1)))
    (case [false] (simp only [nat-mem hx] at h2) (exact (ih (And.right h1) h2)))))

(a/theorem comp-below [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (comp-has w x) true) (< x (:next-id w)))
  (intros h hc)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have hm (= (nat-mem x (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hc)
  (have r := (all-nat-mem (id-in-range (:next-id w)) x _ (And.left (And.right hb)) hm))
  (simp only [id-in-range Bool.and_eq_true Nat.blt_eq] at r)
  (exact (And.right r)))

;; ---- frames: edits that keep the run and task keys and the allocator

(a/structure KW [] (rks (List RKey)) (tks (List TKey)) (n Nat))
(a/defn kw [w :- World] KW (KW.mk (rkeys (:runs w)) (tkeys (:tasks w)) (:next-id w)))

(a/theorem gl-rest-kw [w :- World, w2 :- World]
  (=> (= (kw w2) (kw w)) (= (gl-rest w2) (gl-rest w)))
  (intro e)
  (have e1 (= (rkeys (:runs w2)) (rkeys (:runs w)))) (exact (congrArg (fn [k :- KW] (:rks k)) e))
  (have e2 (= (tkeys (:tasks w2)) (tkeys (:tasks w)))) (exact (congrArg (fn [k :- KW] (:tks k)) e))
  (have e3 (= (:next-id w2) (:next-id w))) (exact (congrArg (fn [k :- KW] (:n k)) e))
  (simp only [gl-rest e1 e2 e3]))

(a/theorem kw-fold [f :- (=> World Nat World), hf :- (forall [w :- World, x :- Nat] (= (kw (f w x)) (kw w))), xs :- (List Nat)]
  (forall [w :- World] (= (kw (nat-fold f w xs)) (kw w)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons h t ih] (intro w) (simp only [nat-fold]) (exact (Eq.trans (ih (f w h)) (hf w h)))))

(a/theorem kw-fin-loop [fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat)] (= (kw (:world (fin-loop fuel w ds))) (kw w)))
  (induction fuel)
  (case [nil] (intros w ds) (simp only [fin-loop]))
  (case [cons h f ih]
    (intros w ds)
    (cases ds)
    (simp only [fin-loop])
    (rename_i d t)
    (simp only [fin-loop])
    (exact (ih (finalize-one w d) _))))

;; Z#53: closing a source wakes its waiters (T9): a fill may wake a parked run (still alive), so
;; the run keys stay
(a/theorem rkey-run-wake [r :- RunRow] (= (rkey (run-wake r)) (rkey r)) (simp only [rkey run-wake-alive]))
(a/theorem kw-resume [w :- World, a :- ActRow] (= (kw (resume w a)) (kw w))
  (simp only [resume kw run-upd set-runs])
  (rw [(rkeys-upd (:run a) run-wake rkey-run-wake (:runs w))]))
(a/theorem kw-fill-slot [w :- World, a :- ActRow, y :- Nat, v :- RunResult] (= (kw (fill-slot w a y v)) (kw w))
  (cases hm (act-ready (act-fill y v a)))
  (simp only [fill-slot hm])
  (simp only [fill-slot hm]) (exact (kw-resume w a)))
(a/theorem kw-remove-edge [w :- World, y :- Nat] (= (kw (remove-edge w y)) (kw w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [remove-edge hf hm])))
(a/theorem kw-fire-dep [w :- World, e :- EdgeRow] (= (kw (fire-dep w e)) (kw w))
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha invalidate])
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc invalidate])
  (simp only [fire-dep ha hc deliver-dep])
  (have e1 (= (kw (dep-consumed w e)) (kw w)))
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf])
  (simp only [dep-consumed hf]) (exact (kw-remove-edge w (:id e)))
  (exact (Eq.trans (kw-fill-slot _ a _ _) e1)))
(a/theorem kw-fire-wait [res :- RunResult, w :- World, e :- EdgeRow] (= (kw (fire-wait res w e)) (kw w))
  (cases hc (Nat.beq (:creditor e) 0))
  (case [true] (simp only [fire-wait hc]) (exact (kw-remove-edge w (:id e))))
  (case [false]
    (simp only [fire-wait hc])
    (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
    (simp only [fire-wait-act ha])
    (cases hr (run-current w (:run a)))
    (simp only [fire-wait-act ha hr])
    (simp only [fire-wait-act ha hr]) (exact (kw-fill-slot _ a _ _))))
(a/theorem kw-fire-edge [res :- RunResult, w :- World, y :- Nat] (= (kw (fire-edge res w y)) (kw w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [fire-edge hf])
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [fire-edge hf hp])
  (cases hk1 (Nat.beq (:kind e) ek-dep))
  (cases hk2 (Nat.beq (:kind e) ek-wait))
  (cases hk3 (Nat.beq (:kind e) ek-observe))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-savepoint-todo])
  (cases ho (observe-new e (deb-version w (:debtor e))))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-observe ho])
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-observe ho])
  (simp only [fire-edge hf hp hk1 hk2]) (exact (kw-fire-wait res w e))
  (simp only [fire-edge hf hp hk1]) (exact (kw-fire-dep w e)))
(a/theorem kw-wake-closed [w :- World, x :- Nat] (= (kw (wake-closed w x)) (kw w))
  (simp only [wake-closed])
  (exact (kw-fold (fire-edge (deb-result w x)) (kw-fire-edge (deb-result w x)) _ w)))

(a/theorem kw-close-source [w :- World, x :- Nat] (= (kw (close-source w x)) (kw w))
  (simp only [close-source finalize-debtor])
  (exact (Eq.trans (kw-fin-loop _ (wake-closed (source-upd w x source-close-row) x) _)
                   (kw-wake-closed (source-upd w x source-close-row) x))))
(a/theorem kw-close-scope-id [w :- World, x :- Nat] (= (kw (close-scope-id w x)) (kw w)) (rfl))
(a/theorem kw-close-local [w :- World, sub :- (List Nat)] (= (kw (close-local w sub)) (kw w))
  (simp only [close-local])
  (exact (Eq.trans (kw-fold close-source kw-close-source _ _) (kw-fold close-scope-id kw-close-scope-id sub w))))
(a/theorem kw-scope-del [w :- World, x :- Nat] (= (kw (scope-del w x)) (kw w)) (rfl))
(a/theorem kw-remove-if-empty [w :- World, sub :- (List Nat)] (= (kw (remove-if-empty w sub)) (kw w))
  (cases he (subtree-empty w sub))
  (case [false] (simp only [remove-if-empty he]))
  (case [true] (simp only [remove-if-empty he]) (exact (kw-fold scope-del kw-scope-del sub w))))
(a/theorem kw-drop-act [w :- World, x :- Nat] (= (kw (drop-act w x)) (kw w)) (rfl))
(a/theorem kw-res-cancel [w :- World, x :- Nat] (= (kw (res-cancel w x)) (kw w)) (rfl))

;; ---- key lists under row functions

(a/defn rk-up [k :- RKey] RKey (RKey.mk (:id k) (:of k) true))
(a/defn rk-down [k :- RKey] RKey (RKey.mk (:id k) (:of k) false))
(a/defn tk-done [t :- TKey] TKey (TKey.mk (:id t) (:run t) true))

(a/theorem rkeys-upd-g [x :- Nat, f :- (=> RunRow RunRow), g :- (=> RKey RKey),
                        hc :- (forall [r :- RunRow] (= (rkey (f r)) (g (rkey r)))), rs :- (List RunRow)]
  (= (rkeys (tbl-upd run-id x f rs)) (tbl-upd rkey-id x g (rkeys rs)))
  (induction rs)
  (case [nil] (simp only [tbl-upd rkeys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (run-id h) x))
    (case [false]
      (have hx2 (= (Nat.beq (rkey-id (rkey h)) x) false)) (exact hx)
      (simp only [tbl-upd hx rkeys hx2 ih]))
    (case [true]
      (have hx2 (= (Nat.beq (rkey-id (rkey h)) x) true)) (exact hx)
      (simp only [tbl-upd hx rkeys hx2 ih (hc h)]))))

(a/theorem tkeys-upd-g [x :- Nat, f :- (=> TaskRow TaskRow), g :- (=> TKey TKey),
                        hc :- (forall [t :- TaskRow] (= (tkey (f t)) (g (tkey t)))), ts :- (List TaskRow)]
  (= (tkeys (tbl-upd task-id x f ts)) (tbl-upd tkey-id x g (tkeys ts)))
  (induction ts)
  (case [nil] (simp only [tbl-upd tkeys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (task-id h) x))
    (case [false]
      (have hx2 (= (Nat.beq (tkey-id (tkey h)) x) false)) (exact hx)
      (simp only [tbl-upd hx tkeys hx2 ih]))
    (case [true]
      (have hx2 (= (Nat.beq (tkey-id (tkey h)) x) true)) (exact hx)
      (simp only [tbl-upd hx tkeys hx2 ih (hc h)]))))

(a/theorem rkeys-del [x :- Nat, rs :- (List RunRow)] (= (rkeys (tbl-del run-id x rs)) (tbl-del rkey-id x (rkeys rs)))
  (induction rs)
  (case [nil] (simp only [tbl-del rkeys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (run-id h) x))
    (case [false]
      (have hx2 (= (Nat.beq (rkey-id (rkey h)) x) false)) (exact hx)
      (simp only [tbl-del hx rkeys hx2 ih]))
    (case [true]
      (have hx2 (= (Nat.beq (rkey-id (rkey h)) x) true)) (exact hx)
      (simp only [tbl-del hx rkeys hx2 ih]))))

(a/theorem tkey-cancel-result [t :- TaskRow] (= (tkey (task-cancel-result t)) (tk-done (tkey t)))
  (cases hn (Nat.beq (:tag (:result t)) res-none))
  (case [true] (simp only [task-cancel-result hn]))
  (case [false] (simp only [task-cancel-result hn tkey tk-done task-done Bool.not_false])))

(a/theorem tkey-result-row [res :- RunResult, t :- TaskRow]
  (=> (= (Nat.beq (:tag res) res-none) false) (= (tkey (task-result-row res t)) (tk-done (tkey t))))
  (intro hn) (simp only [tkey task-result-row tk-done task-done hn Bool.not_false]))

;; ---- run rows made alive (resume, park)

(a/theorem gl-run-upd-up [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                          hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                          hk :- (forall [r :- RunRow] (= (rkey (f r)) (RKey.mk (:id r) (:of r) true)))]
  (=> (= (gl w) true) (= (gl (run-upd w x f)) true))
  (intro h)
  (have e := (rkeys-upd-g x f rk-up hk (:runs w)))
  (have hr (= (gl-rest (run-upd w x f)) true))
  (simp only [gl-rest run-upd set-runs e])
  (exact (l10k-up _ _ _ x rk-up (fn [k :- RKey] (Eq.refl (:id k))) (fn [k :- RKey] (Eq.refl (:of k))) (fn [k :- RKey] (Eq.refl true))
           (gl-rest-of w h)))
  (exact (gl-intro _ (inv-run-upd w x f hf (gl-sample w h)) hr)))

(defn- up-patch [form]
  (subst-forms (app-of? 'inv-run-upd)
               (fn [[_ w x f hid & more]]
                 (apply list 'gl-run-upd-up w x f hid '(fn [r :- RunRow] (Eq.refl (RKey.mk (:id r) (:of r) true))) more))
               form))
(doseq [o '[inv-park-if inv-take-park]] (patch! GL o up-patch))

;; Z#50: resume wakes only a parked run (alive before and after), so it keeps the run keys
(a/theorem run-wake-rkey [r :- RunRow] (= (rkey (run-wake r)) (rkey r))
  (simp only [rkey run-wake-alive]))
(patch! GL 'inv-resume
  (fn [form] (subst-forms (app-of? 'inv-run-upd)
                          (fn [[_ w x f hid & more]] (apply list 'gl-run-upd w x f hid 'run-wake-rkey more))
                          form)))

;; ---- the exempt world predicate

(a/defn glx [k :- Nat, w :- World] Bool (l10kx k (rkeys (:runs w)) (tkeys (:tasks w)) (:next-id w)))

(a/theorem glx-kw [k :- Nat, w :- World, w2 :- World] (=> (= (kw w2) (kw w)) (= (glx k w2) (glx k w)))
  (intro e)
  (have e1 (= (rkeys (:runs w2)) (rkeys (:runs w)))) (exact (congrArg (fn [q :- KW] (:rks q)) e))
  (have e2 (= (tkeys (:tasks w2)) (tkeys (:tasks w)))) (exact (congrArg (fn [q :- KW] (:tks q)) e))
  (have e3 (= (:next-id w2) (:next-id w))) (exact (congrArg (fn [q :- KW] (:n q)) e))
  (simp only [glx e1 e2 e3]))

;; a run row made done: only its own task (r.of) may lack a run
(a/theorem glx-kill [w :- World, r :- RunRow, f :- (=> RunRow RunRow),
                     hk :- (forall [q :- RunRow] (= (rkey (f q)) (rk-down (rkey q))))]
  (=> (= (inv-sample w) true) (List.Mem r (:runs w)) (= (gl w) true) (= (glx (:of r) (run-upd w (:id r) f)) true))
  (intros hs hm h)
  (have e := (rkeys-upd-g (:id r) f rk-down hk (:runs w)))
  (simp only [glx run-upd set-runs e])
  (exact (l10k-kill _ _ _ (:id r) (:of r) rk-down (fn [k :- RKey] (Eq.refl (:id k))) (fn [k :- RKey] (Eq.refl (:of k)))
           (gl-rest-of w h) (of-at-runs w r hs hm))))

(a/theorem gl-of-glx-comp [w :- World, k :- Nat]
  (=> (= (inv-sample w) true) (= (glx k w) true) (= (comp-has w k) true) (= (gl w) true))
  (intros hs hx hc)
  (exact (gl-intro w hs (l10kx-none _ _ _ k hx (not-id-tasks k (:tasks w) (comp-not-task w k hs hc))))))

(a/theorem gl-of-glx-find [w :- World, k :- Nat]
  (=> (= (inv-sample w) true) (= (glx k w) true) (= (task-find w k) (Option.none TaskRow)) (= (gl w) true))
  (intros hs hx hf)
  (exact (gl-intro w hs (l10kx-none _ _ _ k hx (find-none-tasks k (:tasks w) hf)))))

(a/theorem gl-task-done-x [w :- World, k :- Nat, f :- (=> TaskRow TaskRow),
                           hf :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                           hk :- (forall [t :- TaskRow] (= (tkey (f t)) (tk-done (tkey t))))]
  (=> (= (inv-sample w) true) (= (glx k w) true) (= (gl (task-upd w k f)) true))
  (intros hs hx)
  (have e := (tkeys-upd-g k f tk-done hk (:tasks w)))
  (have hr (= (gl-rest (task-upd w k f)) true))
  (simp only [gl-rest task-upd set-tasks e])
  (exact (l10kx-done _ _ _ k tk-done (fn [t :- TKey] (Eq.refl (:id t))) (fn [t :- TKey] (Eq.refl (:run t)))
           (fn [t :- TKey] (Eq.refl true)) hx))
  (exact (gl-intro _ (inv-task-upd w k f hf hs) hr)))

;; ---- T14's local part (cancel): the run is done, its task gets err ::cancelled

(a/defn cancel-mid [w :- World, r :- RunRow] World
  (cleanup-set (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r) (:id r) (cleanup-rows-of w r)))

(a/theorem cancel-mid-sample [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (= (inv-sample (cancel-mid w r)) true))
  (intro h)
  (exact (inv-cleanup-set _ (:id r) (cleanup-rows-of w r)
           (inv-cancel-res _ r (inv-cancel-acts _ (:id r) (inv-run-upd w (:id r) run-cancel-row run-cancel-row-id h))))))

(a/theorem cancel-mid-kw [w :- World, r :- RunRow] (= (kw (cancel-mid w r)) (kw (run-upd w (:id r) run-cancel-row)))
  (simp only [cancel-mid cancel-res cancel-acts])
  (exact (Eq.trans (Eq.trans (Eq.refl _) (kw-fold res-cancel kw-res-cancel (:resources r) _))
                   (kw-fold drop-act kw-drop-act _ _))))

(lcopy! GL 'inv-fire-task-cancelled)
(lcopy! GL 'inv-invalidate-dependents)
(lcopy! GL 'inv-fire-waits-cancelled)

(a/theorem gl-cancel-run-local-o [w :- World, r :- RunRow, rep :- Bool]
  (=> (List.Mem r (:runs w)) (= (gl w) true) (= (gl (cancel-run-local w r rep)) true))
  (intros hm h)
  (have hs := (gl-sample w h))
  (have hms := (cancel-mid-sample w r hs))
  (have hx (= (glx (:of r) (cancel-mid w r)) true))
  (rw [(glx-kw (:of r) _ _ (cancel-mid-kw w r))])
  (exact (glx-kill w r run-cancel-row (fn [q :- RunRow] (Eq.refl (rk-down (rkey q)))) hs hm h))
  (have e (= (cancel-run-local w r rep) (cancel-debtor rep (cancel-mid w r) r))) (rfl)
  (rw [e])
  (cases hc (Bool.and rep (comp-has (cancel-mid w r) (:of r))))
  (case [true]
    (simp only [cancel-debtor hc])
    (simp only [Bool.and_eq_true] at hc)
    (exact (gl-of-glx-comp _ (:of r) hms hx (And.right hc))))
  (case [false]
    (simp only [cancel-debtor hc])
    (cases hf (comp-find (cancel-mid w r) (:of r)))
    (case [none]
      (simp only [debtor-side hf])
      (exact (gl-fire-task-cancelled _ (:of r)
               (gl-task-done-x _ (:of r) task-cancel-result task-cancel-result-id tkey-cancel-result hms hx))))
    (case [some c]
      (have hg := (gl-of-glx-comp _ (:of r) hms hx (tbl-find-has CompRow comp-id (:of r) c _ hf)))
      (cases he (Nat.beq (:epoch r) (:epoch c)))
      (case [false] (simp only [debtor-side hf he]) (exact hg))
      (case [true]
        (simp only [debtor-side hf he])
        (exact (gl-invalidate-dependents _ (:of r) (gl-fire-waits-cancelled _ (:of r) hg)))))))

(override! GL 'inv-cancel-run-local '[inv-fire-task-cancelled inv-invalidate-dependents inv-fire-waits-cancelled]
  '(a/theorem gl-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
     (=> (List.Mem r (:runs w)) (= (gl w) true) (= (gl (cancel-run-local w r rep)) true))
     (intros hm h) (exact (gl-cancel-run-local-o w r rep hm h))))

;; ---- T13 (retire): the run row goes, its task's run is cleared (the task has its result)

(a/theorem kw-run-del-congr [w :- World, w2 :- World, x :- Nat]
  (=> (= (kw w2) (kw w)) (= (kw (run-del w2 x)) (kw (run-del w x))))
  (intro e)
  (have e1 (= (rkeys (:runs w2)) (rkeys (:runs w)))) (exact (congrArg (fn [q :- KW] (:rks q)) e))
  (have e2 (= (tkeys (:tasks w2)) (tkeys (:tasks w)))) (exact (congrArg (fn [q :- KW] (:tks q)) e))
  (have e3 (= (:next-id w2) (:next-id w))) (exact (congrArg (fn [q :- KW] (:n q)) e))
  (simp only [kw run-del set-runs rkeys-del e1 e2 e3]))

(a/theorem kw-retire-with [w :- World, r :- RunRow, sub :- (List Nat)]
  (= (kw (retire-with w r sub)) (kw (run-del (clear-comp-run w r) (:id r))))
  (simp only [retire-with])
  (have e1 := (kw-remove-if-empty (cleanup-del (run-del (close-local (clear-comp-run w r) sub) (:id r)) (:id r)) sub))
  (have e2 (= (kw (cleanup-del (run-del (close-local (clear-comp-run w r) sub) (:id r)) (:id r)))
              (kw (run-del (close-local (clear-comp-run w r) sub) (:id r)))))
  (rfl)
  (have e3 := (kw-run-del-congr (clear-comp-run w r) (close-local (clear-comp-run w r) sub) (:id r)
                (kw-close-local (clear-comp-run w r) sub)))
  (exact (Eq.trans e1 (Eq.trans e2 e3))))

(a/defn run-of-is [x :- Nat, t :- TaskRow] Bool (Nat.beq (:run t) x))

(a/theorem retire-rest [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (List.Mem r (:runs w)) (= (run-alive r) false) (= (gl-rest w) true)
      (= (gl-rest (run-del (clear-comp-run w r) (:id r))) true))
  (intros hs hm ha h)
  (have hd := (dead-at-runs w r hs hm ha))
  (have plain (= (gl-rest (run-del w (:id r))) true))
  (simp only [gl-rest run-del set-runs rkeys-del])
  (exact (l10k-del _ _ _ (:id r) h (dead-off _ _ _ (:id r) h hd)))
  (cases hc (comp-find w (:of r)))
  (case [some c]
    (cases hr (Nat.beq (:run c) (:id r)))
    (case [false] (simp only [clear-comp-run hc hr]) (exact plain))
    (case [true] (simp only [clear-comp-run hc hr]) (exact plain)))
  (case [none]
    (simp only [clear-comp-run hc])
    (cases hk (task-find w (:of r)))
    (case [none] (simp only [clear-task-run hk]) (exact plain))
    (case [some t]
      (cases hr (Nat.beq (:run t) (:id r)))
      (case [false] (simp only [clear-task-run hk hr]) (exact plain))
      (case [true]
        (simp only [clear-task-run hk hr])
        (have ek (= (task-id t) (:of r))) (exact (tbl-find-id TaskRow task-id (:of r) t (:tasks w) hk))
        (have u := (uniq-all TaskRow task-id (run-of-is (:id r)) t (:tasks w) (tasks-nodup w hs)
                     (tbl-find-mem TaskRow task-id (:of r) t (:tasks w) hk) hr))
        (rw [ek] at u)
        (have hri (= (tbl-all (run-is-if (:of r) (:id r)) (tkeys (:tasks w))) true))
        (rw [all-tkeys])
        (exact (Eq.trans (tbl-all-congr TaskRow (on-tkey (run-is-if (:of r) (:id r))) (same-id-then task-id (:of r) (run-of-is (:id r)))
                           (fn [b :- TaskRow] (Eq.refl (on-tkey (run-is-if (:of r) (:id r)) b))) (:tasks w)) u))
        (have e := (tkeys-upd-g (:of r) task-clear-run clr (fn [q :- TaskRow] (Eq.refl (clr (tkey q)))) (:tasks w)))
        (simp only [gl-rest run-del set-runs task-upd set-tasks rkeys-del e])
        (exact (l10k-clear-del _ _ _ (:id r) (:of r) h hd hri))))))

(a/theorem gl-retire-local-o [w :- World, r :- RunRow]
  (=> (List.Mem r (:runs w)) (= (run-alive r) false) (= (gl w) true) (= (gl (retire-local w r)) true))
  (intros hm ha h)
  (have hs := (gl-sample w h))
  (have hr (= (gl-rest (retire-local w r)) true))
  (simp only [retire-local])
  (rw [(gl-rest-kw _ _ (kw-retire-with w r (scope-subtree w (:scope r))))])
  (exact (retire-rest w r hs hm ha (gl-rest-of w h)))
  (exact (gl-intro _ (inv-retire-local w r hs) hr)))

(override! GL 'inv-retire-local '[]
  '(a/theorem gl-retire-local [w :- World, r :- RunRow]
     (=> (List.Mem r (:runs w)) (= (run-alive r) false) (= (gl w) true) (= (gl (retire-local w r)) true))
     (intros hm ha h) (exact (gl-retire-local-o w r hm ha h))))

(a/theorem retirable-dead [r :- RunRow] (=> (= (retirable r) true) (= (run-alive r) false))
  (intro h)
  (simp only [retirable Bool.and_eq_true] at h)
  (have e (= (:act r) act-done)) (exact (Nat.eq_of_beq_eq_true (And.left h)))
  (simp only [run-alive e Nat.beq_refl Bool.not_true]))

(patch! GL 'inv-job-apply
  (fn [form]
    (->> form
         (subst-forms (app-of? 'inv-cancel-run-local)
                      (fn [[hd w r rep h]] (list hd w r rep '(tbl-find-mem RunRow run-id rid r (:runs w) hf) h)))
         (subst-forms (app-of? 'inv-retire-local)
                      (fn [[hd w r h]] (list hd w r '(tbl-find-mem RunRow run-id rid r (:runs w) hf) '(retirable-dead r ha) h))))))

;; ---- T12 (complete): the run is done, its task gets the result (ok/err, never none)

(lcopy! GL 'inv-settle)
(lcopy! GL 'inv-cancel-res)
(lcopy! GL 'inv-fire-edge)

(a/theorem gl-complete-body-mid [w :- World, r :- RunRow, res :- RunResult]
  (=> (List.Mem r (:runs w)) (= (Nat.beq (:tag res) res-none) false) (= (gl w) true)
      (= (gl (:world (complete-body (run-upd w (:id r) run-complete-row) r res))) true))
  (intros hm ht h)
  (have hs := (gl-sample w h))
  (have hs1 := (inv-run-upd w (:id r) run-complete-row run-complete-row-id hs))
  (have hx := (glx-kill w r run-complete-row (fn [q :- RunRow] (Eq.refl (rk-down (rkey q)))) hs hm h))
  (cases hc (comp-find (run-upd w (:id r) run-complete-row) (:of r)))
  (case [none]
    (cases hk (task-find (run-upd w (:id r) run-complete-row) (:of r)))
    (case [none] (simp only [complete-body hc hk]) (exact (gl-of-glx-find _ (:of r) hs1 hx hk)))
    (case [some k]
      (simp only [complete-body hc hk complete-task])
      (have ek (= (task-id k) (:of r))) (exact (tbl-find-id TaskRow task-id (:of r) k _ hk))
      (have hx2 (= (glx (:id k) (run-upd w (:id r) run-complete-row)) true))
      (have ek2 (= (:id k) (:of r))) (exact ek)
      (rw [ek2]) (exact hx)
      (exact (nat-fold-gl (fire-edge res) (gl-fire-edge res) _ _
               (gl-cancel-res _ r (gl-task-done-x _ (:id k) (task-result-row res) (task-result-row-id res)
                                    (fn [q :- TaskRow] (tkey-result-row res q ht)) hs1 hx2))))))
  (case [some c]
    (have hg := (gl-of-glx-comp _ (:of r) hs1 hx (tbl-find-has CompRow comp-id (:of r) c _ hc)))
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [complete-body hc he]) (exact hg))
    (case [true]
      (simp only [complete-body hc he complete-comp])
      (exact (gl-settle _ (:id c) _ (gl-cancel-res _ r
               (gl-comp-upd _ (:id c) (comp-result-row res (:epoch r)) (comp-result-row-id res (:epoch r))
                 (comp-result-row-pending res (:epoch r)) hg)))))))

(lcopy! GL 'inv-retire-after)
(lcopy! GL 'inv-run-cascade)
(lcopy! GL 'inv-fin-if-final)

(a/theorem gl-complete-raw-o [w :- World, r :- RunRow, res :- RunResult]
  (=> (List.Mem r (:runs w)) (= (Nat.beq (:tag res) res-none) false) (= (gl w) true) (= (gl (complete-raw w r res)) true))
  (intros hm ht h)
  (simp only [complete-raw])
  (exact (gl-fin-if-final _ (:of r) (gl-run-cascade _ _ (gl-retire-after _ (:id r) (gl-complete-body-mid w r res hm ht h))))))

(override! GL 'inv-complete-raw '[]
  '(a/theorem gl-complete-raw [w :- World, r :- RunRow, res :- RunResult]
     (=> (List.Mem r (:runs w)) (= (Nat.beq (:tag res) res-none) false) (= (gl w) true) (= (gl (complete-raw w r res)) true))
     (intros hm ht h) (exact (gl-complete-raw-o w r res hm ht h))))

(a/theorem tag-ok-none [tag :- Nat] (=> (= (res-tag-ok tag) true) (= (Nat.beq tag res-none) false))
  (intro h)
  (cases hb (Nat.beq tag res-none))
  (case [false] (rfl))
  (case [true]
    (have e (= tag res-none)) (exact (Nat.eq_of_beq_eq_true hb))
    (simp [res-tag-ok e res-none res-ok res-err] at h)))

(a/theorem refused-tag-ok [w :- World, st :- Nat, tag :- Nat]
  (=> (= (complete-refused w st tag) false) (= (res-tag-ok tag) true))
  (intro h)
  (simp only [complete-refused Bool.or_eq_false_iff] at h)
  (have h2 := (And.right h))
  (cases hb (res-tag-ok tag))
  (case [true] (rfl))
  (case [false] (simp [hb] at h2)))

(override! GL 't12-inv '[inv-complete-raw]
  '(a/theorem t12-gl [w :- World, st :- Nat, tag :- Nat, v :- Nat]
     (=> (= (res-tag-ok tag) true) (= (gl w) true) (= (gl (:world (t12-complete w st tag v))) true))
     (intros hg h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t12-complete ht refuse]) (exact h)
     (cases hn (run-normal r))
     (simp only [t12-complete ht hn refuse]) (exact h)
     (simp only [t12-complete ht hn accept])
     (exact (gl-complete-raw w r (RunResult.mk tag v) (And.left (tok-facts w st r ht)) (tag-ok-none tag hg) h))))

(patch! GL 'raw0-inv
  (fn [form] (subst-forms #(= % '(t12-inv w _ _ _ h)) (fn [_] '(t12-inv w _ _ _ (refused-tag-ok w st tag hc) h)) form)))

;; ---- T4/T5/T11: the new run (and T4's task)

(a/theorem gl-spawn-rows-o [w :- World, owner :- Nat, inputs :- (List Nat)]
  (=> (= (gl w) true) (= (gl (spawn-rows w owner inputs)) true))
  (intro h)
  (have hs := (gl-sample w h))
  (have lt (< (:next-id w) (+ (:next-id w) 3))) (omega)
  (have hr (= (gl-rest (spawn-rows w owner inputs)) true))
  (exact (l10k-ins-task (rkeys (:runs w)) (tkeys (:tasks w)) (:next-id w) (+ (:next-id w) 3) (+ (:next-id w) 1)
           (gl-rest-of w h) lt (tasks-below w hs)))
  (exact (gl-intro _ (inv-spawn-rows w owner inputs hs) hr)))

(override! GL 'inv-spawn-rows '[]
  '(a/theorem gl-spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat)]
     (=> (= (gl w) true) (= (gl (spawn-rows w owner inputs)) true))
     (intro h) (exact (gl-spawn-rows-o w owner inputs h))))

;; a computation's new run: of = an existing computation (no task id, below the allocator)
(a/theorem gl-comp-run-o [w :- World, cid :- Nat, ep :- Nat, ei :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c)))]
  (=> (= (comp-has w cid) true) (= (gl w) true) (= (gl (comp-upd (add-run-scope w cid ep 0 ei) cid f)) true))
  (intros hc h)
  (have hs := (gl-sample w h))
  (have lt := (comp-below w cid hs hc))
  (have le (<= (:next-id w) (+ (:next-id w) 2))) (omega)
  (have lt2 (< cid (+ (:next-id w) 2))) (omega)
  (have hr (= (gl-rest (comp-upd (add-run-scope w cid ep 0 ei) cid f)) true))
  (exact (l10k-ins-run (rkeys (:runs w)) (tkeys (:tasks w)) (:next-id w) (+ (:next-id w) 2) (:next-id w) cid
           (gl-rest-of w h) le lt2 (not-id-tasks cid (:tasks w) (comp-not-task w cid hs hc))))
  (exact (gl-intro _ (inv-comp-upd _ cid f hid hp (inv-add-run-scope w cid ep 0 ei hs)) hr)))

(override! GL 'inv-start-raw '[]
  '(a/theorem gl-start-raw [w :- World, c :- CompRow]
     (=> (= (comp-has w (:id c)) true) (= (gl w) true) (= (gl (start-raw w c)) true))
     (intros hc h)
     (simp only [start-raw])
     (exact (gl-comp-run-o w (:id c) (start-epoch c) 0 (comp-start-row (:next-id w)) (comp-start-row-id (:next-id w))
              (comp-start-row-pending (:next-id w)) hc h))))

(override! GL 'inv-new-run-of '[]
  '(a/theorem gl-new-run-of [w :- World, c :- CompRow, ei :- Nat]
     (=> (= (comp-has w (:id c)) true) (= (gl w) true) (= (gl (new-run-of w c ei)) true))
     (intros hc h)
     (simp only [new-run-of])
     (exact (gl-comp-run-o w (:id c) (:epoch c) ei (comp-set-run (:next-id w)) (comp-set-run-id (:next-id w))
              (comp-set-run-pending (:next-id w)) hc h))))

(a/theorem find-comp-has [w :- World, cid :- Nat, c :- CompRow]
  (=> (= (comp-find w cid) (Option.some CompRow c)) (= (comp-has w (:id c)) true))
  (intro hf)
  (have e (= (comp-id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hf))
  (have e2 (= (:id c) cid)) (exact e)
  (rw [e2]) (exact (tbl-find-has CompRow comp-id cid c (:comps w) hf)))

(patch! GL 't5-inv
  (fn [form] (subst-forms #(= % '(inv-start-raw w c h)) (fn [_] '(inv-start-raw w c (find-comp-has w cid c hc) h)) form)))

;; ---- T11 keeps C: bundle `ch cx` = inv-sample and computation cx exists, through the
;; predecessor's cancel and the cut (no computation is removed there)

(a/defn ch-rest [cx :- Nat, w :- World] Bool (comp-has w cx))
(a/defn ch [cx :- Nat, w :- World] Bool (Bool.and (inv-sample w) (ch-rest cx w)))
(a/theorem ch-sample [cx :- Nat, w :- World] (=> (= (ch cx w) true) (= (inv-sample w) true))
  (intro h) (simp only [ch Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem ch-rest-of [cx :- Nat, w :- World] (=> (= (ch cx w) true) (= (ch-rest cx w) true))
  (intro h) (simp only [ch Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem ch-intro [cx :- Nat, w :- World] (=> (= (inv-sample w) true) (= (ch-rest cx w) true) (= (ch cx w) true))
  (intros h1 h2) (simp only [ch h1 h2 Bool.and_self]))
(a/theorem ch-parts [cx :- Nat, w :- World]
  (=> (= (ch cx w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (ch-sample cx w h))))

(def CH (mk-bundle 'ch '[cx :- Nat] "ch-" {}))
(swap! (:renames CH) assoc 'inv-parts 'ch-parts)

(a/theorem ch-eq-comp-upd-eq [w :- World, y :- Nat, f :- (=> CompRow CompRow),
                           hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))), cx :- Nat]
  (= (ch-rest cx (comp-upd w y f)) (ch-rest cx w))
  (simp only [ch-rest comp-has comp-upd set-comps])
  (exact (tbl-has-upd CompRow comp-id y cx f hid (:comps w))))
(a/theorem ch-eq-drop-cred [w :- World, a :- Nat, cx :- Nat] (= (ch-rest cx (drop-cred-edges w a)) (ch-rest cx w))
  (simp only [drop-cred-edges])
  (exact (ch-eq-comp-upd-eq _ a (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (comp-id c))) cx)))
(a/theorem lit-resync-has [es :- (List EdgeRow), cs :- (List CompRow), cx :- Nat]
  (= (tbl-has comp-id cx (comps-resync es cs)) (tbl-has comp-id cx cs))
  (induction cs)
  (case [nil] (simp only [comps-resync]))
  (case [cons h t ih]
    (have e (= (comp-id (comp-resync es h)) (comp-id h))) (rfl)
    (simp only [comps-resync tbl-has e ih])))
(a/theorem ch-eq-drop-edges [w :- World, p :- (=> EdgeRow Bool), cx :- Nat] (= (ch-rest cx (drop-edges w p)) (ch-rest cx w))
  (simp only [ch-rest comp-has drop-edges set-comps set-edges lit-resync-has]))
(a/theorem ch-eq-mark-edge [w :- World, x :- Nat, cx :- Nat] (= (ch-rest cx (mark-edge w x)) (ch-rest cx w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]))
    (case [false] (simp only [mark-edge hf hm]) (exact (ch-eq-comp-upd-eq _ (:creditor e) comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) cx)))))
(a/theorem ch-eq-unmark-edge [w :- World, x :- Nat, cx :- Nat] (= (ch-rest cx (unmark-edge w x)) (ch-rest cx w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]))
    (case [true] (simp only [unmark-edge hf hm]) (exact (ch-eq-comp-upd-eq _ (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) cx)))))
(a/theorem ch-eq-remove-edge [w :- World, x :- Nat, cx :- Nat] (= (ch-rest cx (remove-edge w x)) (ch-rest cx w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]))
    (case [true] (simp only [remove-edge hf hm]) (exact (ch-eq-comp-upd-eq _ (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) cx)))))
(a/theorem ch-comp-ins [w :- World, r :- CompRow, cx :- Nat]
  (=> (= (ch-rest cx w) true) (= (ch-rest cx (bump (comp-ins w r))) true))
  (intro h)
  (simp only [ch-rest comp-has] at h)
  (cases hx (Nat.beq (comp-id r) cx))
  (all_goals (simp only [ch-rest comp-has bump comp-ins set-next-id set-comps tbl-ins tbl-has hx h])))

(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del
            inv-set-pins inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-edge-upd inv-run-upd inv-task-upd
            inv-run-del inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-act-ins-fresh
            inv-run-ins-fresh inv-task-ins-fresh inv-bump insert-edge-fresh-inv-sample]]
  (prim! CH o nil))
(prim! CH 'inv-comp-upd '(Eq.trans (ch-eq-comp-upd-eq w x f hid cx) R))
(prim! CH 'inv-drop-cred '(Eq.trans (ch-eq-drop-cred w a cx) R))
(prim! CH 'inv-drop-act '(Eq.trans (ch-eq-drop-cred w a cx) R))
(prim! CH 'inv-drop-edges '(Eq.trans (ch-eq-drop-edges w p cx) R))
(prim! CH 'mark-edge-inv-sample '(Eq.trans (ch-eq-mark-edge w x cx) R))
(prim! CH 'unmark-edge-inv-sample '(Eq.trans (ch-eq-unmark-edge w x cx) R))
(prim! CH 'inv-remove-edge '(Eq.trans (ch-eq-remove-edge w x cx) R))
(prim! CH 'inv-comp-ins-fresh '(ch-comp-ins w r cx R))

(lcopy! CH 'inv-cancel-pred)
(lcopy! CH 'inv-cut-suffix)
(lcopy! CH 'inv-consume-entry)
(lcopy! GL 'inv-cancel-pred)
(lcopy! GL 'inv-cut-suffix)
(lcopy! GL 'inv-consume-entry)

(override! GL 'inv-dispatch-raw '[inv-new-run-of]
  '(a/theorem gl-dispatch-raw [w :- World, c :- CompRow]
     (=> (= (comp-has w (:id c)) true) (= (gl w) true) (= (gl (dispatch-raw w c)) true))
     (intros hc h)
     (have h1 := (gl-cancel-pred w c h))
     (have k1 := (ch-cancel-pred (:id c) w c (ch-intro (:id c) w (gl-sample w h) hc)))
     (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
     (simp only [dispatch-raw he])
     (exact (gl-new-run-of _ c 0 (ch-rest-of (:id c) _ (ch-cut-suffix (:id c) _ (:id c) false 0 0 k1))
              (gl-cut-suffix _ (:id c) false 0 0 h1)))
     (simp only [dispatch-raw he])
     (exact (gl-new-run-of _ c _
              (ch-rest-of (:id c) _ (ch-consume-entry (:id c) _ e (ch-cut-suffix (:id c) _ (:id c) true (:at e) (:id e) k1)))
              (gl-consume-entry _ e (gl-cut-suffix _ (:id c) true (:at e) (:id e) h1))))))

(patch! GL 't11-inv
  (fn [form] (subst-forms #(= % '(inv-dispatch-raw w c h)) (fn [_] '(inv-dispatch-raw w c (find-comp-has w cid c hc) h)) form)))

;; ---- Rule R: the filter keeps every run that is not done (normalized: they are live)

(a/defn alive-kept [K :- (=> Nat Bool), k :- RKey] Bool (Bool.or (Bool.not (:alive k)) (K (:id k))))

(a/theorem run-for-kept [K :- (=> Nat Bool), t :- TKey, k :- RKey]
  (=> (= (both (run-for t) (alive-kept K) k) true) (= (K (rkey-id k)) true))
  (intro h)
  (simp only [both run-for Bool.and_eq_true] at h)
  (have h2 := (And.right h))
  (simp only [alive-kept (And.right (And.right (And.left h))) Bool.not_true Bool.false_or] at h2)
  (exact h2))

(a/theorem l10k-keep [rks :- (List RKey), tks :- (List TKey), n :- Nat, K :- (=> Nat Bool)]
  (=> (= (l10k rks tks n) true) (= (tbl-all (alive-kept K) rks) true)
      (= (l10k (tbl-keep K rkey-id rks) (tbl-keep K tkey-id tks) n) true))
  (intros h hk)
  (simp only [l10k Bool.and_eq_true] at h)
  (have h2 (forall [kk :- RKey] (=> (= (trun-ok tks kk) true) (= (trun-ok (tbl-keep K tkey-id tks) kk) true))))
  (intros kk a1) (simp only [trun-ok] at a1) (simp only [trun-ok])
  (exact (tbl-all-keep-same TKey K tkey-id (trun-one kk) tks a1))
  (have h3 (forall [t :- TKey] (=> (= (thas-ok rks t) true) (= (thas-ok (tbl-keep K rkey-id rks) t) true))))
  (intros t a1)
  (cases hd (:done t))
  (case [true] (simp only [thas-ok hd Bool.true_or]))
  (case [false]
    (simp only [thas-ok hd Bool.false_or] at a1)
    (simp only [thas-ok hd Bool.false_or])
    (exact (tbl-any-mono RKey (both (run-for t) (alive-kept K)) (run-for t) (both-left RKey (run-for t) (alive-kept K)) _
             (any-keep-on RKey K rkey-id (both (run-for t) (alive-kept K)) (run-for-kept K t) rks
               (any-and-all RKey (run-for t) (alive-kept K) rks a1 hk)))))
  (simp only [l10k Bool.and_eq_true])
  (exact (And.intro (tbl-all-keep-same RKey K rkey-id (of-below-k n) rks (And.left h))
           (And.intro (tbl-all-keep-same RKey K rkey-id (trun-ok (tbl-keep K tkey-id tks))
                        rks (tbl-all-mono RKey (trun-ok tks) (trun-ok (tbl-keep K tkey-id tks)) h2 rks (And.left (And.right h))))
                      (tbl-all-keep-same TKey K tkey-id (thas-ok (tbl-keep K rkey-id rks))
                        tks (tbl-all-mono TKey (thas-ok rks) (thas-ok (tbl-keep K rkey-id rks)) h3 tks (And.right (And.right h))))))))

(a/theorem rkeys-keep [K :- (=> Nat Bool), rs :- (List RunRow)] (= (rkeys (tbl-keep K run-id rs)) (tbl-keep K rkey-id (rkeys rs)))
  (induction rs)
  (case [nil] (simp only [tbl-keep rkeys]))
  (case [cons h t ih]
    (have e (= (K (rkey-id (rkey h))) (K (run-id h)))) (rfl)
    (cases hk (K (run-id h)))
    (all_goals (simp only [tbl-keep rkeys e hk ih]))))
(a/theorem tkeys-keep [K :- (=> Nat Bool), ts :- (List TaskRow)] (= (tkeys (tbl-keep K task-id ts)) (tbl-keep K tkey-id (tkeys ts)))
  (induction ts)
  (case [nil] (simp only [tbl-keep tkeys]))
  (case [cons h t ih]
    (have e (= (K (tkey-id (tkey h))) (K (task-id h)))) (rfl)
    (cases hk (K (task-id h)))
    (all_goals (simp only [tbl-keep tkeys e hk ih]))))

(a/theorem all-of-mem [A :- Type, P :- (=> A Bool), xs :- (List A),
                       h :- (forall [x :- A] (=> (List.Mem x xs) (= (P x) true)))]
  (= (tbl-all P xs) true)
  (induction xs)
  (case [nil] (simp [tbl-all]))
  (case [cons hd t ih]
    (have h1 (= (P hd) true)) (exact (h hd (List.Mem.head t)))
    (have h2 (= (tbl-all P t) true))
    (apply ih) (intros x hm) (exact (h x (List.Mem.tail hd hm)))
    (simp only [tbl-all h1 h2 Bool.and_self])))

(a/theorem alive-kept-of [w :- World, K :- (=> Nat Bool),
                          hK :- (forall [r :- RunRow] (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (K (:id r)) true)))]
  (= (tbl-all (alive-kept K) (rkeys (:runs w))) true)
  (rw [all-rkeys])
  (apply all-of-mem)
  (intros r hm)
  (cases ha (run-alive r))
  (case [false] (simp only [on-rkey alive-kept rkey ha Bool.not_false Bool.true_or]))
  (case [true] (simp only [on-rkey alive-kept rkey ha (hK r hm ha) Bool.or_true])))

(a/theorem gl-filter-world-o [w :- World, K :- (=> Nat Bool),
                              hK :- (forall [r :- RunRow] (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (K (:id r)) true)))]
  (=> (= (gl w) true) (= (filter-safe-k K w) true) (= (gl (filter-world K w)) true))
  (intros h hf)
  (have hr (= (gl-rest (filter-world K w)) true))
  (simp only [gl-rest filter-world rkeys-keep tkeys-keep])
  (exact (l10k-keep _ _ _ K (gl-rest-of w h) (alive-kept-of w K hK)))
  (exact (gl-intro _ (inv-filter-world w K (gl-sample w h) hf) hr)))

(a/theorem gl-rule-r-filter-o [w :- World]
  (=> (= (normalized w) true) (= (gl w) true) (= (filter-safe w) true) (= (gl (rule-r-filter w)) true))
  (intros hn h hf)
  (rw [rule-r-filter-eq])
  (exact (gl-filter-world-o w (keep-fn w)
           (fn [r :- RunRow, hm :- (List.Mem r (:runs w)), ha :- (= (run-alive r) true)]
             (keep-of-live w (:id r) (normalized-runs w r hn hm ha)))
           h hf)))

(lcopy! GL 'inv-normalize)

(a/theorem gl-rule-r-round [w :- World]
  (=> (= (acts-alive w) true) (= (gl w) true) (= (filter-safe (normalize w)) true) (= (gl (rule-r-round w)) true))
  (intros ha h hf)
  (simp only [rule-r-round])
  (exact (gl-rule-r-filter-o (normalize w) (normalized-ok w (gl-sample w h) ha) (gl-normalize w h) hf)))

(a/theorem gl-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (acts-alive w0) true) (= (gl w0) true) (= (rr-safe fuel w0) true)
                            (= (gl (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 ha h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (gl-rule-r-round w0 ha h hs)))
  (case [cons x f ih]
    (intros w0 ha h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (gl-rule-r-round w0 ha h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false]
      (simp only [ho] at hs) (simp only [rr-loop ho])
      (exact (ih (rule-r-round w0) (acts-alive-round w0 (gl-sample w0 h) ha) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))

(a/theorem gl-rule-r [w :- World]
  (=> (= (acts-alive w) true) (= (gl w) true) (= (rule-r-safe w) true) (= (gl (rule-r w)) true))
  (intros ha h hs)
  (simp only [rule-r-safe] at hs) (simp only [rule-r])
  (exact (gl-rr-loop (rr-fuel w) w ha h hs)))

(lcopy! GL 'raw-inv)

;; the bundle is preserved by every step (hypotheses of step-acts)
(a/theorem step-gl [w :- World, it :- Item]
  (=> (= (ga w) true) (= (gl w) true) (= (rule-r-safe (:world (raw w it))) true) (= (gl (:world (world-step w it))) true))
  (intros hg h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (exact (gl-rule-r (:world (raw w it)) (raw-acts-alive w it hg) (raw-gl w it h) hs))))

(a/theorem gl-empty [] (= (gl empty-world) true) (rfl))

;; ---- the literal I10 (task part)

(a/theorem any-rkeys [P :- (=> RKey Bool), rs :- (List RunRow)] (= (tbl-any P (rkeys rs)) (tbl-any (on-rkey P) rs))
  (induction rs) (case [nil] (simp only [rkeys tbl-any])) (case [cons h t ih] (simp only [rkeys tbl-any on-rkey ih])))

(a/theorem any-run-for-mem [tk :- TKey, rs :- (List RunRow)]
  (=> (= (tbl-any (on-rkey (run-for tk)) rs) true) (= (nat-mem (:run tk) (tbl-ids run-id rs)) true))
  (induction rs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (cases hx (Nat.beq (run-id h) (:run tk)))
    (case [true] (simp only [nat-mem tbl-ids hx]))
    (case [false]
      (have hp (= (on-rkey (run-for tk) h) false))
      (have hx2 (= (Nat.beq (:id h) (:run tk)) false)) (exact hx)
      (simp only [on-rkey run-for rkey hx2 Bool.false_and])
      (simp only [tbl-any hp Bool.false_or] at ha)
      (simp only [nat-mem tbl-ids hx])
      (exact (ih ha)))))

(a/theorem find-witness [tk :- TKey, r0 :- RunRow, rs :- (List RunRow)]
  (=> (= (nat-nodup (tbl-ids run-id rs)) true) (= (tbl-any (on-rkey (run-for tk)) rs) true)
      (= (tbl-find run-id (:run tk) rs) (Option.some RunRow r0))
      (= (Bool.and (Nat.beq (:of r0) (:id tk)) (run-alive r0)) true))
  (induction rs)
  (case [nil] (intros hn ha hf) (simp [tbl-find] at hf))
  (case [cons h t ih]
    (intros hn ha hf)
    (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
    (cases hx (Nat.beq (run-id h) (:run tk)))
    (case [true]
      (simp only [tbl-find hx Option.some.injEq] at hf)
      (cases hp (on-rkey (run-for tk) h))
      (case [true]
        (simp only [on-rkey run-for rkey Bool.and_eq_true] at hp)
        (simp only [hf] at hp)
        (simp only [(And.left (And.right hp)) (And.right (And.right hp)) Bool.and_self]))
      (case [false]
        (simp only [tbl-any hp Bool.false_or] at ha)
        (have hm := (any-run-for-mem tk t ha))
        (have e (= (run-id h) (:run tk))) (exact (Nat.eq_of_beq_eq_true hx))
        (have h1 := (bnot-true _ (And.left hn)))
        (rw [e] at h1) (rw [hm] at h1) (cases h1)))
    (case [false]
      (simp only [tbl-find hx] at hf)
      (have hp (= (on-rkey (run-for tk) h) false))
      (have hx2 (= (Nat.beq (:id h) (:run tk)) false)) (exact hx)
      (simp only [on-rkey run-for rkey hx2 Bool.false_and])
      (simp only [tbl-any hp Bool.false_or] at ha)
      (exact (ih (And.right hn) ha hf)))))

(a/theorem gl-task-run-is [w :- World, r :- RunRow]
  (=> (= (gl w) true) (List.Mem r (:runs w)) (= (task-run-is w r) true))
  (intros h hm)
  (have hr := (gl-rest-of w h))
  (simp only [gl-rest l10k Bool.and_eq_true all-rkeys] at hr)
  (have h1 := (tbl-all-mem RunRow (on-rkey (trun-ok (tkeys (:tasks w)))) r (:runs w) (And.left (And.right hr)) hm))
  (simp only [on-rkey trun-ok all-tkeys] at h1)
  (cases hf (task-find w (:of r)))
  (case [none] (simp only [task-run-is hf]))
  (case [some t]
    (have h2 := (tbl-all-mem TaskRow (on-tkey (trun-one (rkey r))) t (:tasks w) h1 (tbl-find-mem TaskRow task-id (:of r) t (:tasks w) hf)))
    (have e (= (task-id t) (:of r))) (exact (tbl-find-id TaskRow task-id (:of r) t (:tasks w) hf))
    (have e2 (= (:id t) (:of r))) (exact e)
    (simp only [on-tkey trun-one tkey rkey e2 Nat.beq_refl Bool.not_true Bool.false_or] at h2)
    (simp only [task-run-is hf h2])))

(a/theorem tbl-find-none-has [A :- Type, idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (=> (= (tbl-find idf x xs) (Option.none A)) (= (tbl-has idf x xs) false))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-has]))
  (case [cons h t ih]
    (intro hf)
    (cases hx (Nat.beq (idf h) x))
    (case [true] (simp [tbl-find hx] at hf))
    (case [false] (simp only [tbl-find hx] at hf) (simp only [tbl-has hx]) (exact (ih hf)))))

(a/theorem gl-task-has-run [w :- World, t :- TaskRow]
  (=> (= (gl w) true) (List.Mem t (:tasks w)) (= (task-has-run w t) true))
  (intros h hm)
  (have hr := (gl-rest-of w h))
  (simp only [gl-rest l10k Bool.and_eq_true all-tkeys] at hr)
  (have h1 := (tbl-all-mem TaskRow (on-tkey (thas-ok (rkeys (:runs w)))) t (:tasks w) (And.right (And.right hr)) hm))
  (simp only [on-tkey thas-ok] at h1)
  (cases hd (task-done t))
  (case [true] (simp only [task-done] at hd) (simp only [task-has-run hd Bool.true_or]))
  (case [false]
    (have hd2 (= (:done (tkey t)) false)) (exact hd)
    (simp only [hd2 Bool.false_or any-rkeys] at h1)
    (have hd3 (= (Bool.not (Nat.beq (:tag (:result t)) res-none)) false)) (exact hd)
    (simp only [task-has-run hd3 Bool.false_or])
    (cases hf (run-find w (:run t)))
    (case [none]
      (have hm2 := (any-run-for-mem (tkey t) (:runs w) h1))
      (have hh (= (tbl-has run-id (:run t) (:runs w)) true)) (rw [← nat-mem-ids]) (exact hm2)
      (have hn := (tbl-find-none-has RunRow run-id (:run t) (:runs w) hf))
      (rw [hh] at hn) (cases hn))
    (case [some r0]
      (exact (find-witness (tkey t) r0 (:runs w) (lit-runs-nodup w (gl-sample w h)) h1 hf)))))

(a/theorem gl-i10-task [w :- World] (=> (= (gl w) true) (= (inv-i10-task w) true))
  (intro h)
  (simp only [inv-i10-task Bool.and_eq_true])
  (exact (And.intro (all-of-mem RunRow (task-run-is w) (:runs w) (fn [r :- RunRow, hm :- (List.Mem r (:runs w))] (gl-task-run-is w r h hm)))
                    (all-of-mem TaskRow (task-has-run w) (:tasks w) (fn [t :- TaskRow, hm :- (List.Mem t (:tasks w))] (gl-task-has-run w t h hm))))))

;; Theorem: literal I10, task part (every run of a task K is K.run; a task without result has
;; its run, not done), through every step
(a/theorem step-lit-i10-task [w :- World, it :- Item]
  (=> (= (ga w) true) (= (gl w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (inv-i10-task (:world (world-step w it))) true))
  (intros hg h hs) (exact (gl-i10-task _ (step-gl w it hg h hs))))

;; ===========================================================================
;; Part D. I9, resources: an unwinding run's resources are cancelling or fired
;;
;; Bundle `g9` = inv-sample, every resource's owner is below the allocator, every run row with a
;; resource's owner id lists it in `resources` (so T14's cancel-res reaches every resource the
;; run owns), and `lit-i9-res`.
;; ===========================================================================

(a/defn res-below-z [n :- Nat, z :- ResRow] Bool (Nat.blt (:owner z) n))
(a/defn phase-ok [z :- ResRow] Bool
  (Bool.or (Nat.beq (:phase z) rp-armed) (Bool.or (Nat.beq (:phase z) rp-fired) (Nat.beq (:phase z) rp-cancelling))))
(a/defn res-good [n :- Nat, z :- ResRow] Bool (Bool.and (res-below-z n z) (phase-ok z)))
(a/defn listed-in [z :- ResRow, r :- RunRow] Bool
  (Bool.or (Bool.not (Nat.beq (:id r) (:owner z))) (nat-mem (:id z) (:resources r))))
(a/defn res-listed [rs :- (List RunRow), z :- ResRow] Bool (tbl-all (listed-in z) rs))
(a/defn g9-rest [w :- World] Bool
  (Bool.and (tbl-all (res-good (:next-id w)) (:res w))
            (Bool.and (tbl-all (res-listed (:runs w)) (:res w)) (lit-i9-res w))))
(a/defn g9 [w :- World] Bool (Bool.and (inv-sample w) (g9-rest w)))

(a/theorem g9-sample [w :- World] (=> (= (g9 w) true) (= (inv-sample w) true))
  (intro h) (simp only [g9 Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem g9-rest-of [w :- World] (=> (= (g9 w) true) (= (g9-rest w) true))
  (intro h) (simp only [g9 Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem g9-intro [w :- World] (=> (= (inv-sample w) true) (= (g9-rest w) true) (= (g9 w) true))
  (intros h1 h2) (simp only [g9 h1 h2 Bool.and_self]))
(a/theorem g9-parts [w :- World]
  (=> (= (g9 w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (g9-sample w h))))

(a/structure RK9 [] (id Nat) (mode Nat) (resources (List Nat)))
(a/defn rk9 [r :- RunRow] RK9 (RK9.mk (:id r) (:mode r) (:resources r)))
(def G9 (mk-bundle 'g9 [] "g9-" {'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (rk9 r))) 4]}))
(swap! (:renames G9) assoc 'inv-parts 'g9-parts)

;; the pieces of g9-rest under a run-table change that keeps id, mode and resources
(a/theorem listed-same [z :- ResRow, r2 :- RunRow, r :- RunRow]
  (=> (= (:id r2) (:id r)) (= (:resources r2) (:resources r)) (= (listed-in z r2) (listed-in z r)))
  (intros h1 h2) (simp only [listed-in h1 h2]))
(a/theorem unw-same [w :- World, r2 :- RunRow, r :- RunRow]
  (=> (= (:id r2) (:id r)) (= (:mode r2) (:mode r)) (= (unwinding-res-ok w r2) (unwinding-res-ok w r)))
  (intros h1 h2) (simp only [unwinding-res-ok h1 h2]))

(a/theorem g9-runs-same [w :- World, rs :- (List RunRow),
                         hl :- (forall [z :- ResRow] (= (res-listed rs z) (res-listed (:runs w) z))),
                         hu :- (= (tbl-all (unwinding-res-ok w) rs) (tbl-all (unwinding-res-ok w) (:runs w)))]
  (= (g9-rest (set-runs w rs)) (g9-rest w))
  (have e1 (= (tbl-all (res-listed rs) (:res w)) (tbl-all (res-listed (:runs w)) (:res w))))
  (exact (tbl-all-congr ResRow (res-listed rs) (res-listed (:runs w)) hl (:res w)))
  (have e2 (= (lit-i9-res (set-runs w rs)) (tbl-all (unwinding-res-ok w) rs))) (rfl)
  (simp only [g9-rest e1 e2 hu]))

(a/theorem g9-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (rk9 (f r)) (rk9 r)))]
  (=> (= (g9 w) true) (= (g9 (run-upd w x f)) true))
  (intro h)
  (have hid (forall [r :- RunRow] (= (:id (f r)) (:id r)))) (intro r) (exact (congrArg (fn [k :- RK9] (:id k)) (hk r)))
  (have hm (forall [r :- RunRow] (= (:mode (f r)) (:mode r)))) (intro r) (exact (congrArg (fn [k :- RK9] (:mode k)) (hk r)))
  (have hr (forall [r :- RunRow] (= (:resources (f r)) (:resources r)))) (intro r) (exact (congrArg (fn [k :- RK9] (:resources k)) (hk r)))
  (have hl (forall [z :- ResRow] (= (res-listed (tbl-upd run-id x f (:runs w)) z) (res-listed (:runs w) z))))
  (intro z) (simp only [res-listed])
  (exact (tbl-all-upd-same RunRow run-id x f (listed-in z) (fn [r :- RunRow] (listed-same z (f r) r (hid r) (hr r))) (:runs w)))
  (have hu (= (tbl-all (unwinding-res-ok w) (tbl-upd run-id x f (:runs w))) (tbl-all (unwinding-res-ok w) (:runs w))))
  (exact (tbl-all-upd-same RunRow run-id x f (unwinding-res-ok w) (fn [r :- RunRow] (unw-same w (f r) r (hid r) (hm r))) (:runs w)))
  (have e := (g9-runs-same w (tbl-upd run-id x f (:runs w)) hl hu))
  (exact (g9-intro _ (inv-run-upd w x f hf (g9-sample w h)) (Eq.trans e (g9-rest-of w h)))))

(a/theorem res-below-one [n :- Nat, m :- Nat, z :- ResRow]
  (=> (<= n m) (= (res-below-z n z) true) (= (res-below-z m z) true))
  (intros hn hz)
  (simp only [res-below-z Nat.blt_eq] at hz) (simp only [res-below-z Nat.blt_eq])
  (exact (Nat.lt_of_lt_of_le hz hn)))

(a/theorem res-good-one [n :- Nat, m :- Nat, z :- ResRow]
  (=> (<= n m) (= (res-good n z) true) (= (res-good m z) true))
  (intros hn hz)
  (simp only [res-good Bool.and_eq_true] at hz) (simp only [res-good Bool.and_eq_true])
  (exact (And.intro (res-below-one n m z hn (And.left hz)) (And.right hz))))

(a/theorem g9-rest-next [w :- World, v :- Nat]
  (=> (= (g9-rest w) true) (<= (:next-id w) v) (= (g9-rest (set-next-id w v)) true))
  (intros h hv)
  (simp only [g9-rest Bool.and_eq_true] at h)
  (have e1 (= (lit-i9-res (set-next-id w v)) (lit-i9-res w))) (rfl)
  (have e2 (= (:res (set-next-id w v)) (:res w))) (rfl)
  (have e3 (= (:runs (set-next-id w v)) (:runs w))) (rfl)
  (have e4 (= (:next-id (set-next-id w v)) v)) (rfl)
  (simp only [g9-rest Bool.and_eq_true e1 e2 e3 e4])
  (exact (And.intro (tbl-all-mono ResRow (res-good (:next-id w)) (res-good v)
                      (fn [z :- ResRow, hz :- (= (res-good (:next-id w) z) true)] (res-good-one (:next-id w) v z hv hz))
                      (:res w) (And.left h))
                    (And.right h))))
(a/theorem g9-rest-bump [w :- World] (=> (= (g9-rest w) true) (= (g9-rest (bump w)) true))
  (intro h) (simp only [bump]) (exact (g9-rest-next w (+ (:next-id w) 1) h (Nat.le_succ (:next-id w)))))

(a/theorem g9-rest-mark-edge [w :- World, x :- Nat] (= (g9-rest (mark-edge w x)) (g9-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem g9-rest-unmark-edge [w :- World, x :- Nat] (= (g9-rest (unmark-edge w x)) (g9-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem g9-rest-remove-edge [w :- World, x :- Nat] (= (g9-rest (remove-edge w x)) (g9-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))

(a/theorem g9-unw-res-del [x :- Nat, w :- World, r :- RunRow]
  (=> (= (unwinding-res-ok w r) true) (= (unwinding-res-ok (resource-del w x) r) true))
  (intro h)
  (cases hu (Nat.beq (:mode r) mode-unwinding))
  (case [false] (simp only [unwinding-res-ok hu Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [unwinding-res-ok hu Bool.not_true Bool.false_or] at h)
    (simp only [unwinding-res-ok hu Bool.not_true Bool.false_or resource-del set-res])
    (exact (tbl-all-del ResRow resource-id x (res-of-quiet (:id r)) (res-of-quiet (:id r))
             (fn [z :- ResRow, h1 :- (= (res-of-quiet (:id r) z) true), h2 :- (= (Nat.beq (resource-id z) x) false)] h1)
             (:res w) h))))

(a/theorem g9-rest-resource-del [w :- World, x :- Nat]
  (=> (= (g9-rest w) true) (= (g9-rest (resource-del w x)) true))
  (intro h)
  (simp only [g9-rest lit-i9-res Bool.and_eq_true] at h)
  (have e1 (= (:res (resource-del w x)) (tbl-del resource-id x (:res w)))) (rfl)
  (have e2 (= (:runs (resource-del w x)) (:runs w))) (rfl)
  (have e3 (= (:next-id (resource-del w x)) (:next-id w))) (rfl)
  (simp only [g9-rest lit-i9-res Bool.and_eq_true e1 e2 e3])
  (exact (And.intro
           (tbl-all-del ResRow resource-id x (res-good (:next-id w)) (res-good (:next-id w))
             (fn [z :- ResRow, h1 :- (= (res-good (:next-id w) z) true), h2 :- (= (Nat.beq (resource-id z) x) false)] h1) (:res w) (And.left h))
           (And.intro
             (tbl-all-del ResRow resource-id x (res-listed (:runs w)) (res-listed (:runs w))
               (fn [z :- ResRow, h1 :- (= (res-listed (:runs w) z) true), h2 :- (= (Nat.beq (resource-id z) x) false)] h1) (:res w) (And.left (And.right h)))
             (tbl-all-mono RunRow (unwinding-res-ok w) (unwinding-res-ok (resource-del w x)) (g9-unw-res-del x w) (:runs w)
               (And.right (And.right h)))))))

(a/theorem g9-rest-run-del [w :- World, x :- Nat]
  (=> (= (g9-rest w) true) (= (g9-rest (run-del w x)) true))
  (intro h)
  (simp only [g9-rest lit-i9-res Bool.and_eq_true] at h)
  (have hl (forall [z :- ResRow] (=> (= (res-listed (:runs w) z) true) (= (res-listed (tbl-del run-id x (:runs w)) z) true))))
  (intros z hz) (simp only [res-listed] at hz) (simp only [res-listed])
  (exact (tbl-all-del RunRow run-id x (listed-in z) (listed-in z)
           (fn [r :- RunRow, h1 :- (= (listed-in z r) true), h2 :- (= (Nat.beq (run-id r) x) false)] h1) (:runs w) hz))
  (have e1 (= (:runs (run-del w x)) (tbl-del run-id x (:runs w)))) (rfl)
  (have e2 (= (:res (run-del w x)) (:res w))) (rfl)
  (have e3 (= (:next-id (run-del w x)) (:next-id w))) (rfl)
  (have e4 (forall [r :- RunRow] (= (unwinding-res-ok (run-del w x) r) (unwinding-res-ok w r)))) (intro r) (rfl)
  (simp only [g9-rest lit-i9-res Bool.and_eq_true e1 e2 e3 (tbl-all-congr RunRow (unwinding-res-ok (run-del w x)) (unwinding-res-ok w) e4)])
  (exact (And.intro (And.left h)
           (And.intro (tbl-all-mono ResRow (res-listed (:runs w)) (res-listed (tbl-del run-id x (:runs w))) hl (:res w) (And.left (And.right h)))
             (tbl-all-del RunRow run-id x (unwinding-res-ok w) (unwinding-res-ok w)
               (fn [r :- RunRow, h1 :- (= (unwinding-res-ok w r) true), h2 :- (= (Nat.beq (run-id r) x) false)] h1) (:runs w)
               (And.right (And.right h)))))))

(a/theorem owner-ne-next [n :- Nat, z :- ResRow] (=> (= (res-good n z) true) (= (Nat.beq n (:owner z)) false))
  (intro h)
  (simp only [res-good res-below-z Bool.and_eq_true Nat.blt_eq] at h)
  (cases hb (Nat.beq n (:owner z)))
  (case [false] (rfl))
  (case [true] (have e (= n (:owner z))) (exact (Nat.eq_of_beq_eq_true hb)) (rw [e] at h) (omega)))

(a/theorem g9-run-ins [w :- World, r :- RunRow]
  (=> (= (run-id r) (:next-id w)) (= (g9-rest w) true) (= (g9-rest (bump (run-ins w r))) true))
  (intros hr h)
  (have h0 (= (g9-rest (run-ins w r)) true))
  (simp only [g9-rest lit-i9-res Bool.and_eq_true] at h)
  (have hid (= (:id r) (:next-id w))) (exact hr)
  (have hl (forall [z :- ResRow] (=> (= (res-good (:next-id w) z) true) (= (res-listed (:runs w) z) true)
                                     (= (res-listed (List.cons RunRow r (:runs w)) z) true))))
  (intros z a1 a2)
  (simp only [res-listed tbl-all listed-in hid (owner-ne-next (:next-id w) z a1) Bool.not_false Bool.true_or Bool.true_and])
  (exact a2)
  (have hq (= (tbl-all (res-of-quiet (:id r)) (:res w)) true))
  (exact (tbl-all-mono ResRow (res-good (:next-id w)) (res-of-quiet (:id r))
           (fn [z :- ResRow, a1 :- (= (res-good (:next-id w) z) true)]
             (Eq.trans (congrArg (fn [b :- Bool] (Bool.or (Bool.not b) (res-quiet z)))
                         (Eq.trans (beq-comm (:owner z) (:id r)) (Eq.trans (congrArg (fn [m :- Nat] (Nat.beq m (:owner z))) hid) (owner-ne-next (:next-id w) z a1))))
                       (Eq.refl true)))
           (:res w) (And.left h)))
  (have e1 (= (:runs (run-ins w r)) (List.cons RunRow r (:runs w)))) (rfl)
  (have e2 (= (:res (run-ins w r)) (:res w))) (rfl)
  (have e3 (= (:next-id (run-ins w r)) (:next-id w))) (rfl)
  (have e4 (forall [q :- RunRow] (= (unwinding-res-ok (run-ins w r) q) (unwinding-res-ok w q)))) (intro q) (rfl)
  (simp only [g9-rest lit-i9-res Bool.and_eq_true e1 e2 e3 tbl-all (tbl-all-congr RunRow (unwinding-res-ok (run-ins w r)) (unwinding-res-ok w) e4)])
  (have hu (= (unwinding-res-ok w r) true)) (simp only [unwinding-res-ok hq Bool.or_true])
  (exact (And.intro (And.left h)
           (And.intro (tbl-all-mono2 ResRow (res-good (:next-id w)) (res-listed (:runs w)) (res-listed (List.cons RunRow r (:runs w))) hl
                        (:res w) (And.left h) (And.left (And.right h)))
                      (And.intro hu (And.right (And.right h))))))
  (exact (g9-rest-bump _ h0)))

(a/theorem g9-filter [w :- World, K :- (=> Nat Bool)]
  (=> (= (g9-rest w) true) (= (g9-rest (filter-world K w)) true))
  (intro h)
  (simp only [g9-rest lit-i9-res Bool.and_eq_true] at h)
  (have hl (forall [z :- ResRow] (=> (= (res-listed (:runs w) z) true) (= (res-listed (tbl-keep K run-id (:runs w)) z) true))))
  (intros z a1) (simp only [res-listed] at a1) (simp only [res-listed])
  (exact (tbl-all-keep-same RunRow K run-id (listed-in z) (:runs w) a1))
  (have hu (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (unwinding-res-ok (filter-world K w) q) true))))
  (intros q a1)
  (cases hm (Nat.beq (:mode q) mode-unwinding))
  (case [false] (simp only [unwinding-res-ok hm Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [unwinding-res-ok hm Bool.not_true Bool.false_or] at a1)
    (simp only [unwinding-res-ok hm Bool.not_true Bool.false_or filter-world])
    (exact (tbl-all-keep-same ResRow K resource-id (res-of-quiet (:id q)) (:res w) a1)))
  (simp only [g9-rest lit-i9-res Bool.and_eq_true filter-world])
  (exact (And.intro (tbl-all-keep-same ResRow K resource-id (res-good (:next-id w)) (:res w) (And.left h))
           (And.intro (tbl-all-keep-same ResRow K resource-id (res-listed (tbl-keep K run-id (:runs w)))
                        (:res w) (tbl-all-mono ResRow (res-listed (:runs w)) (res-listed (tbl-keep K run-id (:runs w))) hl (:res w) (And.left (And.right h))))
                      (tbl-all-keep-same RunRow K run-id (unwinding-res-ok (filter-world K w))
                        (:runs w) (tbl-all-mono RunRow (unwinding-res-ok w) (unwinding-res-ok (filter-world K w)) hu (:runs w) (And.right (And.right h))))))))

(a/theorem res-good-f [n :- Nat, z :- ResRow, z2 :- ResRow]
  (=> (= (:owner z2) (:owner z)) (=> (= (phase-ok z) true) (= (phase-ok z2) true)) (= (res-good n z) true) (= (res-good n z2) true))
  (intros ho hp h)
  (simp only [res-good res-below-z Bool.and_eq_true] at h)
  (simp only [res-good res-below-z Bool.and_eq_true ho])
  (exact (And.intro (And.left h) (hp (And.right h)))))
(a/theorem listed-in-eq [z :- ResRow, z2 :- ResRow, r :- RunRow]
  (=> (= (:id z2) (:id z)) (= (:owner z2) (:owner z)) (= (listed-in z2 r) (listed-in z r)))
  (intros h1 h2) (simp only [listed-in h1 h2]))
(a/theorem listed-f [rs :- (List RunRow), z :- ResRow, z2 :- ResRow]
  (=> (= (:id z2) (:id z)) (= (:owner z2) (:owner z)) (= (res-listed rs z2) (res-listed rs z)))
  (intros h1 h2)
  (simp only [res-listed])
  (exact (tbl-all-congr RunRow (listed-in z2) (listed-in z) (fn [r :- RunRow] (listed-in-eq z z2 r h1 h2)) rs)))
(a/theorem quiet-f [x :- Nat, z :- ResRow, z2 :- ResRow]
  (=> (= (:owner z2) (:owner z)) (=> (= (res-quiet z) true) (= (res-quiet z2) true)) (= (res-of-quiet x z) true) (= (res-of-quiet x z2) true))
  (intros ho hq h)
  (cases hx (Nat.beq (:owner z) x))
  (case [false] (simp only [res-of-quiet ho hx Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [res-of-quiet hx Bool.not_true Bool.false_or] at h)
    (simp only [res-of-quiet ho hx Bool.not_true Bool.false_or (hq h)])))

;; a resource row change that keeps id and owner, keeps the phase valid and never un-quiets
(a/theorem g9-res-upd-q [w :- World, x :- Nat, f :- (=> ResRow ResRow),
                         hid :- (forall [z :- ResRow] (= (resource-id (f z)) (resource-id z))),
                         ho :- (forall [z :- ResRow] (= (:owner (f z)) (:owner z))),
                         hp :- (forall [z :- ResRow] (=> (= (phase-ok z) true) (= (phase-ok (f z)) true))),
                         hq :- (forall [z :- ResRow] (=> (= (res-quiet z) true) (= (res-quiet (f z)) true)))]
  (=> (= (g9 w) true) (= (g9 (resource-upd w x f)) true))
  (intro h)
  (have hr := (g9-rest-of w h))
  (simp only [g9-rest lit-i9-res Bool.and_eq_true] at hr)
  (have hid2 (forall [z :- ResRow] (= (:id (f z)) (:id z)))) (intro z) (exact (hid z))
  (have h1 (= (tbl-all (res-good (:next-id w)) (tbl-upd resource-id x f (:res w))) true))
  (exact (tbl-all-upd ResRow resource-id x f (res-good (:next-id w)) (res-good (:next-id w))
           (fn [z :- ResRow, a1 :- (= (res-good (:next-id w) z) true), a2 :- (= (Nat.beq (resource-id z) x) true)]
             (res-good-f (:next-id w) z (f z) (ho z) (hp z) a1))
           (fn [z :- ResRow, a1 :- (= (res-good (:next-id w) z) true), a2 :- (= (Nat.beq (resource-id z) x) false)] a1)
           (:res w) (And.left hr)))
  (have h2 (= (tbl-all (res-listed (:runs w)) (tbl-upd resource-id x f (:res w))) true))
  (rw [(tbl-all-upd-same ResRow resource-id x f (res-listed (:runs w))
         (fn [z :- ResRow] (listed-f (:runs w) z (f z) (hid2 z) (ho z))) (:res w))])
  (exact (And.left (And.right hr)))
  (have h3 (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (unwinding-res-ok (resource-upd w x f) q) true))))
  (intros q a1)
  (cases hm (Nat.beq (:mode q) mode-unwinding))
  (case [false] (simp only [unwinding-res-ok hm Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [unwinding-res-ok hm Bool.not_true Bool.false_or] at a1)
    (simp only [unwinding-res-ok hm Bool.not_true Bool.false_or resource-upd set-res])
    (exact (tbl-all-upd ResRow resource-id x f (res-of-quiet (:id q)) (res-of-quiet (:id q))
             (fn [z :- ResRow, b1 :- (= (res-of-quiet (:id q) z) true), b2 :- (= (Nat.beq (resource-id z) x) true)]
               (quiet-f (:id q) z (f z) (ho z) (hq z) b1))
             (fn [z :- ResRow, b1 :- (= (res-of-quiet (:id q) z) true), b2 :- (= (Nat.beq (resource-id z) x) false)] b1)
             (:res w) a1)))
  (have e1 (= (:res (resource-upd w x f)) (tbl-upd resource-id x f (:res w)))) (rfl)
  (have e2 (= (:runs (resource-upd w x f)) (:runs w))) (rfl)
  (have e3 (= (:next-id (resource-upd w x f)) (:next-id w))) (rfl)
  (have hr2 (= (g9-rest (resource-upd w x f)) true))
  (simp only [g9-rest lit-i9-res Bool.and_eq_true e1 e2 e3])
  (exact (And.intro h1 (And.intro h2 (tbl-all-mono RunRow (unwinding-res-ok w) (unwinding-res-ok (resource-upd w x f)) h3 (:runs w)
                                       (And.right (And.right hr))))))
  (exact (g9-intro _ (inv-resource-upd w x f hid (g9-sample w h)) hr2)))

;; ---- T14's cancel-res over the run's resource list

(a/theorem cancel-row-phase [z :- ResRow] (=> (= (phase-ok z) true) (= (phase-ok (res-cancel-row z)) true))
  (intro h)
  (cases hb (Nat.beq (:phase z) rp-armed))
  (case [false] (simp only [res-cancel-row hb]) (exact h))
  (case [true] (simp only [res-cancel-row hb])))
(a/theorem cancel-row-quiet [z :- ResRow] (=> (= (res-quiet z) true) (= (res-quiet (res-cancel-row z)) true))
  (intro h)
  (cases hb (Nat.beq (:phase z) rp-armed))
  (case [false] (simp only [res-cancel-row hb]) (exact h))
  (case [true] (simp only [res-cancel-row hb])))
(a/theorem cancel-row-quiets [z :- ResRow] (=> (= (phase-ok z) true) (= (res-quiet (res-cancel-row z)) true))
  (intro h)
  (cases hb (Nat.beq (:phase z) rp-armed))
  (case [true] (simp only [res-cancel-row hb]))
  (case [false]
    (simp only [res-cancel-row hb])
    (simp only [phase-ok hb Bool.false_or] at h)
    (simp only [res-quiet])
    (cases hf (Nat.beq (:phase z) rp-fired))
    (case [true] (simp only [hf Bool.or_true]))
    (case [false] (simp only [hf Bool.false_or] at h) (simp only [h Bool.true_or]))))

(a/defn rcl [L :- (List Nat), rs :- (List ResRow)] (List ResRow)
  (match L [nil rs] [(cons x t) (rcl t (tbl-upd resource-id x res-cancel-row rs))]))

(a/theorem res-cancel-fold [L :- (List Nat)]
  (forall [V :- World] (= (:res (nat-fold res-cancel V L)) (rcl L (:res V))))
  (induction L)
  (case [nil] (intro V) (simp only [nat-fold rcl]))
  (case [cons x t ih] (intro V) (simp only [nat-fold rcl]) (exact (ih (res-cancel V x)))))
(a/theorem runs-cancel-fold [L :- (List Nat)]
  (forall [V :- World] (= (:runs (nat-fold res-cancel V L)) (:runs V)))
  (induction L)
  (case [nil] (intro V) (simp only [nat-fold]))
  (case [cons x t ih] (intro V) (simp only [nat-fold]) (exact (ih (res-cancel V x)))))
(a/theorem next-cancel-fold [L :- (List Nat)]
  (forall [V :- World] (= (:next-id (nat-fold res-cancel V L)) (:next-id V)))
  (induction L)
  (case [nil] (intro V) (simp only [nat-fold]))
  (case [cons x t ih] (intro V) (simp only [nat-fold]) (exact (ih (res-cancel V x)))))
(a/theorem runs-acts-fold [L :- (List Nat)]
  (forall [V :- World] (And (= (:runs (nat-fold drop-act V L)) (:runs V))
                            (And (= (:res (nat-fold drop-act V L)) (:res V)) (= (:next-id (nat-fold drop-act V L)) (:next-id V)))))
  (induction L)
  (case [nil] (intro V) (exact (And.intro (Eq.refl (:runs V)) (And.intro (Eq.refl (:res V)) (Eq.refl (:next-id V))))))
  (case [cons x t ih] (intro V) (simp only [nat-fold]) (exact (ih (drop-act V x)))))

(a/theorem rcl-all [P :- (=> ResRow Bool), hp :- (forall [z :- ResRow] (=> (= (P z) true) (= (P (res-cancel-row z)) true))), L :- (List Nat)]
  (forall [rs :- (List ResRow)] (=> (= (tbl-all P rs) true) (= (tbl-all P (rcl L rs)) true)))
  (induction L)
  (case [nil] (intros rs h) (simp only [rcl]) (exact h))
  (case [cons x t ih]
    (intros rs h) (simp only [rcl])
    (exact (ih _ (tbl-all-upd ResRow resource-id x res-cancel-row P P
                   (fn [z :- ResRow, a1 :- (= (P z) true), a2 :- (= (Nat.beq (resource-id z) x) true)] (hp z a1))
                   (fn [z :- ResRow, a1 :- (= (P z) true), a2 :- (= (Nat.beq (resource-id z) x) false)] a1) rs h)))))

(a/defn quiet-in [L :- (List Nat), z :- ResRow] Bool (Bool.or (Bool.not (nat-mem (:id z) L)) (res-quiet z)))

(a/theorem quiet-in-step [x :- Nat, M :- (List Nat), L :- (List Nat), z :- ResRow]
  (= (quiet-in (nat-app (List.cons Nat x M) L) z) (quiet-in (nat-app M (List.cons Nat x L)) z))
  (simp only [quiet-in nat-app nat-mem-app nat-mem])
  (cases h1 (Nat.beq x (:id z))) (all_goals (cases h2 (nat-mem (:id z) M))) (all_goals (simp only [h1 h2 Bool.true_or Bool.or_true Bool.false_or Bool.or_false])))

(a/theorem cancel-row-owner [z :- ResRow] (= (:owner (res-cancel-row z)) (:owner z))
  (cases hb (Nat.beq (:phase z) rp-armed)) (all_goals (simp only [res-cancel-row hb])))
(a/theorem quiet-in-nil [M :- (List Nat), z :- ResRow] (= (quiet-in (nat-app M (List.nil Nat)) z) (quiet-in M z))
  (simp only [quiet-in nat-mem-app nat-mem Bool.or_false]))
(a/theorem quiet-in-hit [x :- Nat, M :- (List Nat), n :- Nat, z :- ResRow]
  (=> (= (res-good n z) true) (= (quiet-in (List.cons Nat x M) (res-cancel-row z)) true))
  (intro h)
  (simp only [res-good Bool.and_eq_true] at h)
  (simp only [quiet-in (cancel-row-quiets z (And.right h)) Bool.or_true]))
(a/theorem quiet-in-miss [x :- Nat, M :- (List Nat), z :- ResRow]
  (=> (= (Nat.beq (resource-id z) x) false) (= (quiet-in M z) true) (= (quiet-in (List.cons Nat x M) z) true))
  (intros h1 h2)
  (have h3 (= (Nat.beq x (:id z)) false)) (rw [beq-comm]) (exact h1)
  (simp only [quiet-in nat-mem h3] ) (exact h2))

(a/theorem rcl-quiet [n :- Nat, L :- (List Nat)]
  (forall [M :- (List Nat), rs :- (List ResRow)]
    (=> (= (tbl-all (res-good n) rs) true) (= (tbl-all (quiet-in M) rs) true)
        (= (tbl-all (quiet-in (nat-app M L)) (rcl L rs)) true)))
  (induction L)
  (case [nil]
    (intros M rs h1 h2) (simp only [rcl])
    (exact (Eq.trans (tbl-all-congr ResRow (quiet-in (nat-app M (List.nil Nat))) (quiet-in M)
                       (fn [z :- ResRow] (quiet-in-nil M z)) rs) h2)))
  (case [cons x t ih]
    (intros M rs h1 h2) (simp only [rcl])
    (have g1 := (tbl-all-upd ResRow resource-id x res-cancel-row (res-good n) (res-good n)
                  (fn [z :- ResRow, a1 :- (= (res-good n z) true), a2 :- (= (Nat.beq (resource-id z) x) true)]
                    (res-good-f n z (res-cancel-row z) (cancel-row-owner z) (cancel-row-phase z) a1))
                  (fn [z :- ResRow, a1 :- (= (res-good n z) true), a2 :- (= (Nat.beq (resource-id z) x) false)] a1) rs h1))
    (have g2 := (all-upd2 ResRow resource-id x res-cancel-row (res-good n) (quiet-in M) (quiet-in (List.cons Nat x M))
                  (fn [z :- ResRow, a1 :- (= (res-good n z) true), a2 :- (= (quiet-in M z) true), a3 :- (= (Nat.beq (resource-id z) x) true)]
                    (quiet-in-hit x M n z a1))
                  (fn [z :- ResRow, a1 :- (= (res-good n z) true), a2 :- (= (quiet-in M z) true), a3 :- (= (Nat.beq (resource-id z) x) false)]
                    (quiet-in-miss x M z a3 a2))
                  rs h1 h2))
    (have r := (ih (List.cons Nat x M) _ g1 g2))
    (exact (Eq.trans (tbl-all-congr ResRow (quiet-in (nat-app M (List.cons Nat x t))) (quiet-in (nat-app (List.cons Nat x M) t))
                       (fn [z :- ResRow] (Eq.symm (quiet-in-step x M t z))) _) r))))

(a/defn listed-by [r :- RunRow, z :- ResRow] Bool (listed-in z r))

(a/theorem quiet-own [r :- RunRow, x :- Nat, z :- ResRow]
  (=> (= x (:id r)) (= (quiet-in (:resources r) z) true) (= (listed-by r z) true) (= (res-of-quiet x z) true))
  (intros hx h1 h2)
  (cases ho (Nat.beq (:owner z) x))
  (case [false] (simp only [res-of-quiet ho Bool.not_false Bool.true_or]))
  (case [true]
    (have ho2 (= (Nat.beq (:id r) (:owner z)) true)) (rw [beq-comm]) (rw [← hx]) (exact ho)
    (simp only [listed-by listed-in ho2 Bool.not_true Bool.false_or] at h2)
    (simp only [quiet-in h2 Bool.not_true Bool.false_or] at h1)
    (simp only [res-of-quiet ho h1 Bool.or_true])))

(a/theorem cancel-row-id [z :- ResRow] (= (:id (res-cancel-row z)) (:id z))
  (cases hb (Nat.beq (:phase z) rp-armed)) (all_goals (simp only [res-cancel-row hb])))
(a/theorem all-quiet-nil [rs :- (List ResRow)] (= (tbl-all (quiet-in (List.nil Nat)) rs) true)
  (induction rs)
  (case [nil] (simp only [tbl-all]))
  (case [cons h t ih] (simp only [tbl-all quiet-in nat-mem Bool.not_false Bool.true_or ih Bool.and_self])))

(a/theorem g9-cancel-mid [w :- World, r :- RunRow]
  (=> (List.Mem r (:runs w)) (= (g9 w) true) (= (g9 (cancel-mid w r)) true))
  (intros hm h)
  (have hs := (g9-sample w h))
  (have hr := (g9-rest-of w h))
  (simp only [g9-rest lit-i9-res Bool.and_eq_true] at hr)
  (have fa := (runs-acts-fold (tbl-scan act-id (act-of-run (:id r)) (:acts (run-upd w (:id r) run-cancel-row)))
                (run-upd w (:id r) run-cancel-row)))
  (have e-runs (= (:runs (cancel-mid w r)) (tbl-upd run-id (:id r) run-cancel-row (:runs w))))
  (simp only [cancel-mid cleanup-set cleanup-ins cleanup-del set-cleanup cancel-res cancel-acts runs-cancel-fold])
  (exact (And.left fa))
  (have e-res (= (:res (cancel-mid w r)) (rcl (:resources r) (:res w))))
  (simp only [cancel-mid cleanup-set cleanup-ins cleanup-del set-cleanup cancel-res cancel-acts res-cancel-fold])
  (rw [(And.left (And.right fa))])
  (have e-next (= (:next-id (cancel-mid w r)) (:next-id w)))
  (simp only [cancel-mid cleanup-set cleanup-ins cleanup-del set-cleanup cancel-res cancel-acts next-cancel-fold])
  (exact (And.right (And.right fa)))
  (have p1 := (rcl-all (res-good (:next-id w))
                (fn [z :- ResRow, a1 :- (= (res-good (:next-id w) z) true)]
                  (res-good-f (:next-id w) z (res-cancel-row z) (cancel-row-owner z) (cancel-row-phase z) a1))
                (:resources r) (:res w) (And.left hr)))
  (have p2a := (rcl-all (res-listed (:runs w))
                 (fn [z :- ResRow, a1 :- (= (res-listed (:runs w) z) true)]
                   (Eq.trans (listed-f (:runs w) z (res-cancel-row z) (cancel-row-id z) (cancel-row-owner z)) a1))
                 (:resources r) (:res w) (And.left (And.right hr))))
  (have hl (forall [z :- ResRow] (= (res-listed (tbl-upd run-id (:id r) run-cancel-row (:runs w)) z) (res-listed (:runs w) z))))
  (intro z) (simp only [res-listed])
  (exact (tbl-all-upd-same RunRow run-id (:id r) run-cancel-row (listed-in z)
           (fn [q :- RunRow] (listed-same z (run-cancel-row q) q (Eq.refl (:id q)) (Eq.refl (:resources q)))) (:runs w)))
  (have p2 (= (tbl-all (res-listed (tbl-upd run-id (:id r) run-cancel-row (:runs w))) (rcl (:resources r) (:res w))) true))
  (rw [(tbl-all-congr ResRow (res-listed (tbl-upd run-id (:id r) run-cancel-row (:runs w))) (res-listed (:runs w)) hl _)])
  (exact p2a)
  (have q1 := (rcl-quiet (:next-id w) (:resources r) (List.nil Nat) (:res w) (And.left hr) (all-quiet-nil (:res w))))
  (have q2 (= (tbl-all (listed-by r) (rcl (:resources r) (:res w))) true))
  (exact (tbl-all-mono ResRow (res-listed (:runs w)) (listed-by r)
           (fn [z :- ResRow, a1 :- (= (res-listed (:runs w) z) true)] (tbl-all-mem RunRow (listed-in z) r (:runs w) a1 hm))
           _ p2a))
  (have hin (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (Nat.beq (run-id q) (:id r)) true)
                                      (= (unwinding-res-ok (cancel-mid w r) (run-cancel-row q)) true))))
  (intros q a1 a2)
  (have eq (= (:id q) (:id r))) (exact (Nat.eq_of_beq_eq_true a2))
  (have hq (= (tbl-all (res-of-quiet (:id q)) (rcl (:resources r) (:res w))) true))
  (exact (tbl-all-mono2 ResRow (quiet-in (:resources r)) (listed-by r) (res-of-quiet (:id q))
           (fn [z :- ResRow, b1 :- (= (quiet-in (:resources r) z) true), b2 :- (= (listed-by r z) true)] (quiet-own r (:id q) z eq b1 b2))
           _ q1 q2))
  (simp only [unwinding-res-ok e-res run-cancel-row hq Bool.or_true])
  (have hout (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (Nat.beq (run-id q) (:id r)) false)
                                       (= (unwinding-res-ok (cancel-mid w r) q) true))))
  (intros q a1 a2)
  (cases hu (Nat.beq (:mode q) mode-unwinding))
  (case [false] (simp only [unwinding-res-ok hu Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [unwinding-res-ok hu Bool.not_true Bool.false_or] at a1)
    (simp only [unwinding-res-ok hu Bool.not_true Bool.false_or e-res])
    (exact (rcl-all (res-of-quiet (:id q))
             (fn [z :- ResRow, b1 :- (= (res-of-quiet (:id q) z) true)]
               (quiet-f (:id q) z (res-cancel-row z) (cancel-row-owner z) (cancel-row-quiet z) b1))
             (:resources r) (:res w) a1)))
  (have p3 := (tbl-all-upd RunRow run-id (:id r) run-cancel-row (unwinding-res-ok w) (unwinding-res-ok (cancel-mid w r)) hin hout
                (:runs w) (And.right (And.right hr))))
  (have hr2 (= (g9-rest (cancel-mid w r)) true))
  (simp only [g9-rest lit-i9-res Bool.and_eq_true e-runs e-res e-next])
  (exact (And.intro p1 (And.intro p2 p3)))
  (exact (g9-intro _ (cancel-mid-sample w r hs) hr2)))

;; ---- T15 ack: the resource row goes and leaves its owner's list

(a/theorem nat-mem-del [y :- Nat, x :- Nat, xs :- (List Nat)]
  (=> (= (Nat.beq y x) false) (= (nat-mem y (nat-del x xs)) (nat-mem y xs)))
  (intro hne)
  (induction xs)
  (case [nil] (simp only [nat-del nat-mem]))
  (case [cons h t ih]
    (cases hx (Nat.beq h x))
    (case [true]
      (have e (= h x)) (exact (Nat.eq_of_beq_eq_true hx))
      (have hy (= (Nat.beq h y) false)) (rw [e]) (rw [beq-comm]) (exact hne)
      (simp only [nat-del hx nat-mem hy ih]))
    (case [false] (simp only [nat-del hx nat-mem ih]))))

(a/theorem listed-unres [z :- Nat, zz :- ResRow, q :- RunRow]
  (=> (= (Nat.beq (resource-id zz) z) false) (= (listed-in zz (run-unres z q)) (listed-in zz q)))
  (intro h)
  (have h2 (= (Nat.beq (:id zz) z) false)) (exact h)
  (simp only [listed-in run-unres (nat-mem-del (:id zz) z (:resources q) h2)]))

(a/theorem g9-ack-raw-o [w :- World, z :- Nat, owner :- Nat]
  (=> (= (tbl-all (no-debtor z) (:edges w)) true) (= (g9 w) true) (= (g9 (ack-raw w z owner)) true))
  (intros hu h)
  (have hr := (g9-rest-of w h))
  (simp only [g9-rest lit-i9-res Bool.and_eq_true] at hr)
  (have e1 (= (:runs (ack-raw w z owner)) (tbl-upd run-id owner (run-unres z) (:runs w)))) (rfl)
  (have e2 (= (:res (ack-raw w z owner)) (tbl-del resource-id z (:res w)))) (rfl)
  (have e3 (= (:next-id (ack-raw w z owner)) (:next-id w))) (rfl)
  (have p1 := (tbl-all-del ResRow resource-id z (res-good (:next-id w)) (res-good (:next-id w))
                (fn [zz :- ResRow, a1 :- (= (res-good (:next-id w) zz) true), a2 :- (= (Nat.beq (resource-id zz) z) false)] a1)
                (:res w) (And.left hr)))
  (have p2 := (tbl-all-del ResRow resource-id z (res-listed (:runs w)) (res-listed (tbl-upd run-id owner (run-unres z) (:runs w)))
                (fn [zz :- ResRow, a1 :- (= (res-listed (:runs w) zz) true), a2 :- (= (Nat.beq (resource-id zz) z) false)]
                  (Eq.trans (tbl-all-upd-same RunRow run-id owner (run-unres z) (listed-in zz) (fn [q :- RunRow] (listed-unres z zz q a2)) (:runs w)) a1))
                (:res w) (And.left (And.right hr))))
  (have hq (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (unwinding-res-ok (ack-raw w z owner) q) true))))
  (intros q a1)
  (cases hm (Nat.beq (:mode q) mode-unwinding))
  (case [false] (simp only [unwinding-res-ok hm Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [unwinding-res-ok hm Bool.not_true Bool.false_or] at a1)
    (simp only [unwinding-res-ok hm Bool.not_true Bool.false_or e2])
    (exact (tbl-all-del ResRow resource-id z (res-of-quiet (:id q)) (res-of-quiet (:id q))
             (fn [zz :- ResRow, b1 :- (= (res-of-quiet (:id q) zz) true), b2 :- (= (Nat.beq (resource-id zz) z) false)] b1) (:res w) a1)))
  (have hq2 (forall [q :- RunRow] (= (unwinding-res-ok (ack-raw w z owner) (run-unres z q)) (unwinding-res-ok (ack-raw w z owner) q))))
  (intro q) (rfl)
  (have p3 (= (tbl-all (unwinding-res-ok (ack-raw w z owner)) (tbl-upd run-id owner (run-unres z) (:runs w))) true))
  (rw [(tbl-all-upd-same RunRow run-id owner (run-unres z) (unwinding-res-ok (ack-raw w z owner)) hq2 (:runs w))])
  (exact (tbl-all-mono RunRow (unwinding-res-ok w) (unwinding-res-ok (ack-raw w z owner)) hq (:runs w) (And.right (And.right hr))))
  (have hr2 (= (g9-rest (ack-raw w z owner)) true))
  (simp only [g9-rest lit-i9-res Bool.and_eq_true e1 e2 e3])
  (exact (And.intro p1 (And.intro p2 p3)))
  (exact (g9-intro _ (inv-ack-raw w z owner hu (g9-sample w h)) hr2)))

;; ---- T17 arm (not in a cleanup slice, Z#40): a new armed resource of a normal run

(a/defn not-unw [b :- RunRow] Bool (Bool.not (run-unwinding b)))
(a/defn tt-run [q :- RunRow] Bool true)
(a/theorem all-tt [rs :- (List RunRow)] (= (tbl-all tt-run rs) true)
  (induction rs) (case [nil] (simp only [tbl-all])) (case [cons h t ih] (simp only [tbl-all tt-run ih Bool.and_self])))

(a/theorem listed-arm [n :- Nat, zz :- ResRow, q :- RunRow]
  (=> (= (listed-in zz q) true) (= (listed-in zz (run-arm n q)) true))
  (intro h)
  (cases ho (Nat.beq (:id q) (:owner zz)))
  (case [false] (simp only [listed-in run-arm ho Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [listed-in ho Bool.not_true Bool.false_or] at h)
    (cases hn (Nat.beq n (:id zz)))
    (all_goals (simp only [listed-in run-arm ho nat-mem hn h Bool.not_true Bool.false_or]))))

(a/theorem listed-new [n :- Nat, o :- Nat, kind :- Nat, ei :- Nat, q :- RunRow]
  (=> (= (Nat.beq (run-id q) o) true) (= (listed-in (ResRow.mk n o kind ei rp-armed) (run-arm n q)) true))
  (intro h) (simp only [listed-in run-arm nat-mem Nat.beq_refl Bool.or_true]))
(a/theorem listed-other [n :- Nat, o :- Nat, kind :- Nat, ei :- Nat, q :- RunRow]
  (=> (= (Nat.beq (run-id q) o) false) (= (listed-in (ResRow.mk n o kind ei rp-armed) q) true))
  (intro h) (have h2 (= (Nat.beq (:id q) o) false)) (exact h) (simp only [listed-in h2 Bool.not_false Bool.true_or]))
(a/theorem inv-arm-raw-of [w :- World, r :- RunRow, kind :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (arm-raw w r kind)) true))
  (intro h)
  (simp only [arm-raw])
  (exact (inv-run-upd _ (:id r) (run-arm (:next-id w)) (run-arm-run-id _)
           (inv-resource-ins-fresh w (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (rfl) h))))

(a/theorem arm-good [n :- Nat, o :- Nat, kind :- Nat, ei :- Nat]
  (=> (< o (+ n 1)) (= (res-good (+ n 1) (ResRow.mk n o kind ei rp-armed)) true))
  (intro h)
  (have h2 (= (Nat.blt o (+ n 1)) true)) (simp only [Nat.blt_eq]) (exact h)
  (simp only [res-good res-below-z phase-ok h2 Bool.true_and]))

(a/theorem g9-arm-o [w :- World, r :- RunRow, kind :- Nat]
  (=> (List.Mem r (:runs w)) (= (run-unwinding r) false) (= (g9 w) true) (= (g9 (arm-raw w r kind)) true))
  (intros hm hu h)
  (have hs := (g9-sample w h))
  (have hr := (g9-rest-of w h))
  (simp only [g9-rest lit-i9-res Bool.and_eq_true] at hr)
  (have hlt := (run-below w r hs hm))
  (have hnu (= (not-unw r) true)) (simp only [not-unw hu Bool.not_false])
  (have u := (uniq-all RunRow run-id not-unw r (:runs w) (lit-runs-nodup w hs) hm hnu))
  (have e1 (= (:runs (arm-raw w r kind)) (tbl-upd run-id (:id r) (run-arm (:next-id w)) (:runs w)))) (rfl)
  (have e2 (= (:res (arm-raw w r kind))
              (List.cons ResRow (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (:res w)))) (rfl)
  (have e3 (= (:next-id (arm-raw w r kind)) (+ (:next-id w) 1))) (rfl)
  ;; part 1
  (have g0 (= (res-good (+ (:next-id w) 1) (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed)) true))
  (have lt2 (< (:id r) (+ (:next-id w) 1))) (omega)
  (exact (arm-good (:next-id w) (:id r) kind (:effect-index r) lt2))
  (have le (<= (:next-id w) (+ (:next-id w) 1))) (omega)
  (have p1 (= (tbl-all (res-good (+ (:next-id w) 1)) (List.cons ResRow (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (:res w))) true))
  (simp only [tbl-all g0 Bool.true_and])
  (exact (tbl-all-mono ResRow (res-good (:next-id w)) (res-good (+ (:next-id w) 1))
           (fn [zz :- ResRow, a1 :- (= (res-good (:next-id w) zz) true)] (res-good-one (:next-id w) (+ (:next-id w) 1) zz le a1)) (:res w) (And.left hr)))
  ;; part 2
  (have pz (= (res-listed (tbl-upd run-id (:id r) (run-arm (:next-id w)) (:runs w)) (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed)) true))
  (simp only [res-listed])
  (exact (tbl-all-upd RunRow run-id (:id r) (run-arm (:next-id w)) tt-run (listed-in (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed))
           (fn [q :- RunRow, a1 :- (= (tt-run q) true), a2 :- (= (Nat.beq (run-id q) (:id r)) true)] (listed-new (:next-id w) (:id r) kind (:effect-index r) q a2))
           (fn [q :- RunRow, a1 :- (= (tt-run q) true), a2 :- (= (Nat.beq (run-id q) (:id r)) false)] (listed-other (:next-id w) (:id r) kind (:effect-index r) q a2))
           (:runs w) (all-tt (:runs w))))
  (have p2 (= (tbl-all (res-listed (tbl-upd run-id (:id r) (run-arm (:next-id w)) (:runs w)))
                       (List.cons ResRow (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (:res w))) true))
  (simp only [tbl-all pz Bool.true_and])
  (exact (tbl-all-mono ResRow (res-listed (:runs w)) (res-listed (tbl-upd run-id (:id r) (run-arm (:next-id w)) (:runs w)))
           (fn [zz :- ResRow, a1 :- (= (res-listed (:runs w) zz) true)]
             (tbl-all-upd RunRow run-id (:id r) (run-arm (:next-id w)) (listed-in zz) (listed-in zz)
               (fn [q :- RunRow, b1 :- (= (listed-in zz q) true), b2 :- (= (Nat.beq (run-id q) (:id r)) true)] (listed-arm (:next-id w) zz q b1))
               (fn [q :- RunRow, b1 :- (= (listed-in zz q) true), b2 :- (= (Nat.beq (run-id q) (:id r)) false)] b1)
               (:runs w) a1))
           (:res w) (And.left (And.right hr))))
  ;; part 3
  (have hin (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (same-id-then run-id (run-id r) not-unw q) true)
                                      (= (Nat.beq (run-id q) (:id r)) true)
                                      (= (unwinding-res-ok (arm-raw w r kind) (run-arm (:next-id w) q)) true))))
  (intros q a1 a2 a3)
  (have a3b (= (Nat.beq (run-id q) (run-id r)) true)) (exact a3)
  (simp only [same-id-then a3b Bool.not_true Bool.false_or not-unw run-unwinding] at a2)
  (simp only [unwinding-res-ok run-arm a2 Bool.true_or])
  (have hout (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (same-id-then run-id (run-id r) not-unw q) true)
                                       (= (Nat.beq (run-id q) (:id r)) false)
                                       (= (unwinding-res-ok (arm-raw w r kind) q) true))))
  (intros q a1 a2 a3)
  (cases hmq (Nat.beq (:mode q) mode-unwinding))
  (case [false] (simp only [unwinding-res-ok hmq Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [unwinding-res-ok hmq Bool.not_true Bool.false_or] at a1)
    (have a4 (= (Nat.beq (:id r) (:id q)) false)) (rw [beq-comm]) (exact a3)
    (simp only [unwinding-res-ok hmq Bool.not_true Bool.false_or e2 tbl-all res-of-quiet a4 Bool.not_false Bool.true_or Bool.true_and])
    (exact a1))
  (have p3 := (all-upd2 RunRow run-id (:id r) (run-arm (:next-id w)) (unwinding-res-ok w) (same-id-then run-id (run-id r) not-unw)
                (unwinding-res-ok (arm-raw w r kind)) hin hout (:runs w) (And.right (And.right hr)) u))
  (have hr2 (= (g9-rest (arm-raw w r kind)) true))
  (simp only [g9-rest lit-i9-res Bool.and_eq_true e1 e2 e3])
  (exact (And.intro p1 (And.intro p2 p3)))
  (exact (g9-intro _ (inv-arm-raw-of w r kind hs) hr2)))

;; ---- the G9 copy

(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-task-upd inv-cleanup-upd inv-cleanup-del inv-set-pins inv-scope-del
            inv-cleanup-ins inv-act-upd inv-edge-upd inv-drop-cred inv-drop-edges inv-comp-del-unref inv-comp-upd inv-drop-act]]
  (prim! G9 o nil))
(doseq [o '[inv-source-ins-fresh inv-scope-ins-fresh inv-comp-ins-fresh inv-act-ins-fresh inv-task-ins-fresh]]
  (prim! G9 o (list 'g9-rest-bump (list (symbol (str/replace (subs (name o) 4) "-fresh" "")) 'w 'r)
                    (list 'Eq.trans '(rfl) 'R))))
(prim! G9 'inv-bump '(g9-rest-bump w R))
(prim! G9 'mark-edge-inv-sample '(Eq.trans (g9-rest-mark-edge w x) R))
(prim! G9 'unmark-edge-inv-sample '(Eq.trans (g9-rest-unmark-edge w x) R))
(prim! G9 'inv-remove-edge '(Eq.trans (g9-rest-remove-edge w x) R))
(prim! G9 'insert-edge-fresh-inv-sample '(g9-rest-bump (insert-edge w (edge-set-id (:next-id w) e)) (Eq.trans (rfl) R)))
(prim! G9 'inv-run-ins-fresh '(g9-run-ins w r h0 R))
(prim! G9 'inv-run-del '(g9-rest-run-del w x R))
(prim! G9 'inv-resource-del '(g9-rest-resource-del w x R))
(prim! G9 'inv-filter-world '(g9-filter w K R))
(swap! (:renames G9) assoc 'inv-run-upd 'g9-run-upd)

(patch! G9 'inv-res-cancel
  (fn [form] (subst-forms (app-of? 'inv-resource-upd)
                          (fn [_] '(g9-res-upd-q w z res-cancel-row res-cancel-row-id cancel-row-owner cancel-row-phase cancel-row-quiet h))
                          form)))
(patch! G9 't18-inv
  (fn [form] (subst-forms (app-of? 'inv-resource-upd)
                          (fn [_] '(g9-res-upd-q w z (res-set-phase rp-fired) (res-set-phase-resource-id rp-fired)
                                     (fn [q :- ResRow] (Eq.refl (:owner q)))
                                     (fn [q :- ResRow, hq :- (= (phase-ok q) true)] (Eq.refl true))
                                     (fn [q :- ResRow, hq :- (= (res-quiet q) true)] (Eq.refl true)) h))
                          form)))
(patch! G9 'inv-job-apply
  (fn [form] (subst-forms (app-of? 'inv-cancel-run-local)
                          (fn [[hd w r rep h]] (list hd w r rep '(tbl-find-mem RunRow run-id rid r (:runs w) hf) h)) form)))
(patch! G9 'raw0-inv
  (fn [form] (subst-forms #(= % '(t17-inv w _ _ _ _ h)) (fn [_] '(t17-inv w _ _ _ _ hc h)) form)))

(lcopy! G9 'inv-cancel-debtor)

(override! G9 'inv-cancel-run-local '[inv-cancel-debtor]
  '(a/theorem g9-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
     (=> (List.Mem r (:runs w)) (= (g9 w) true) (= (g9 (cancel-run-local w r rep)) true))
     (intros hm h)
     (have e (= (cancel-run-local w r rep) (cancel-debtor rep (cancel-mid w r) r))) (rfl)
     (rw [e])
     (exact (g9-cancel-debtor rep _ r (g9-cancel-mid w r hm h)))))

(override! G9 'inv-ack-raw '[]
  '(a/theorem g9-ack-raw [w :- World, z :- Nat, owner :- Nat]
     (=> (= (tbl-all (no-debtor z) (:edges w)) true) (= (g9 w) true) (= (g9 (ack-raw w z owner)) true))
     (intros hu h) (exact (g9-ack-raw-o w z owner hu h))))

(a/theorem cleanup-not-unw [w :- World, st :- Nat, r :- RunRow]
  (=> (= (in-cleanup w st) false) (= (tok-run w st) (Option.some RunRow r)) (= (run-unwinding r) false))
  (intros hc ht) (simp only [in-cleanup ht opt-test] at hc) (exact hc))

(override! G9 'inv-arm-park '[inv-take-park]
  '(a/theorem g9-arm-park [w :- World, r :- RunRow, kind :- Nat, k :- Nat]
     (=> (List.Mem r (:runs w)) (= (run-unwinding r) false) (= (g9 w) true) (= (g9 (arm-park w r kind k)) true))
     (intros hm hu h)
     (simp only [arm-park])
     (exact (g9-take-park _ (run-arm (:next-id w) r) (:next-id w) k (g9-arm-o w r kind hm hu h)))))

(override! G9 't17-inv '[inv-arm-park]
  '(a/theorem t17-g9 [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
     (=> (= (in-cleanup w st) false) (= (g9 w) true) (= (g9 (:world (t17-arm w st kind k fresh))) true))
     (intros hc h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t17-arm ht refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
     (simp only [t17-arm ht hg refuse]) (exact h)
     (simp only [t17-arm ht hg accept])
     (exact (g9-arm-park w r kind k (And.left (tok-facts w st r ht)) (cleanup-not-unw w st r hc ht) h))))

(lcopy! G9 'step-inv)

(a/theorem g9-empty [] (= (g9 empty-world) true) (rfl))

;; Theorem: literal I9, resources (an unwinding run's resources are cancelling or fired),
;; through every step
(a/theorem step-lit-i9-res [w :- World, it :- Item]
  (=> (= (g9 w) true) (= (rule-r-safe (:world (raw w it))) true) (= (lit-i9-res (:world (world-step w it))) true))
  (intros h hs)
  (have h2 := (g9-rest-of _ (step-g9 w it h hs)))
  (simp only [g9-rest Bool.and_eq_true] at h2)
  (exact (And.right (And.right h2))))

;; ===========================================================================
;; Part E. P3, the core: the Rule R filter is edge-safe in a normalized world with the
;; reference invariants below (no transition reasoning; their preservation is open, see
;; notes/ansatz-fixes.md P3)
;;
;;   dep-active   the creditor of a dep edge is a computation that is not idle (I7's edge part)
;;   acts-run     every activation's run row exists (with acts-alive: it is not done)
;;   marked-dep   a marked edge is a dep edge
;;   edge-sep     no edge id is a cleanup row or a storage ref (kind separation)
;; ===========================================================================

(a/defn not-idle-if-id [x :- Nat, c :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id c) x)) (Bool.not (:idle c))))
(a/defn dep-active [cs :- (List CompRow), e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep)) (tbl-all (not-idle-if-id (:creditor e)) cs)))
(a/defn act-run-has [rs :- (List RunRow), a :- ActRow] Bool (tbl-has run-id (:run a) rs))
(a/defn marked-dep [e :- EdgeRow] Bool (Bool.or (Bool.not (:marked e)) (Nat.beq (:kind e) ek-dep)))
(a/defn edge-sep [w :- World, e :- EdgeRow] Bool
  (Bool.and (Bool.not (reach-mem (:id e) (cleanup-rows w))) (Bool.not (reach-mem (:id e) (storage w)))))
(a/defn p3-refs [w :- World] Bool
  (Bool.and (tbl-all (dep-active (:comps w)) (:edges w))
  (Bool.and (tbl-all (act-run-has (:runs w)) (:acts w))
  (Bool.and (tbl-all marked-dep (:edges w)) (tbl-all (edge-sep w) (:edges w))))))

;; ---- live is closed under the §3.2 successors

(a/theorem live-close [w :- World, x :- Nat, y :- Nat]
  (=> (= (in-live w x) true) (= (reach-mem y (retain-succ w x)) true) (= (in-live w y) true))
  (intros hx hy)
  (have hc := (live-converged-all w))
  (have rx := (Iff.mp (in-live-iff w x hc) hx))
  (exact (Iff.mpr (in-live-iff w y hc) (Reach.step x y rx (Iff.mp (reach-mem-iff y (retain-succ w x)) hy)))))

(a/theorem rm-app-l [x :- Nat, a :- (List Nat), b :- (List Nat)]
  (=> (= (reach-mem x a) true) (= (reach-mem x (List.append Nat a b)) true))
  (intro h) (simp only [reach-mem-append h Bool.true_or]))
(a/theorem rm-app-r [x :- Nat, a :- (List Nat), b :- (List Nat)]
  (=> (= (reach-mem x b) true) (= (reach-mem x (List.append Nat a b)) true))
  (intro h) (simp only [reach-mem-append h Bool.or_true]))
(a/theorem rm-nz [x :- Nat] (=> (= (Nat.beq x 0) false) (= (reach-mem x (nz x)) true))
  (intro h) (simp only [nz h reach-mem Nat.beq_refl]))

(a/theorem succ-edge [w :- World, e :- EdgeRow]
  (=> (List.Mem e (:edges w)) (= (Nat.beq (:debtor e) 0) false) (= (reach-mem (:debtor e) (retain-succ w (:id e))) true))
  (intros hm hd)
  (simp only [retain-succ])
  (apply rm-app-r) (apply rm-app-r) (apply rm-app-r) (apply rm-app-r) (apply rm-app-r) (apply rm-app-l)
  (exact (gather-mem EdgeRow (id-is edge-id (:id e)) edge-contrib e (:debtor e) (:edges w) hm
           (Nat.beq_refl (:id e)) (rm-nz (:debtor e) hd))))

(a/theorem succ-act [w :- World, r :- RunRow, a :- ActRow]
  (=> (List.Mem r (:runs w)) (= (run-alive r) true) (List.Mem a (:acts w)) (= (Nat.beq (:run a) (:id r)) true)
      (= (reach-mem (:id a) (retain-succ w (:id r))) true))
  (intros hr ha hm he)
  (simp only [retain-succ])
  (apply rm-app-r) (apply rm-app-r) (apply rm-app-r) (apply rm-app-l)
  (apply (gather-mem RunRow (id-is run-id (:id r)) (run-contrib w) r (:id a) (:runs w) hr (Nat.beq_refl (:id r))))
  (simp only [run-contrib ha])
  (apply rm-app-r) (apply rm-app-r) (apply rm-app-l)
  (exact (scan-mem ActRow act-id (act-of-run (:id r)) a (:acts w) hm he)))

(a/theorem succ-dep [w :- World, c :- CompRow, e :- EdgeRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) false) (List.Mem e (:edges w)) (= (dep-of (:id c) e) true)
      (= (reach-mem (:id e) (retain-succ w (:id c))) true))
  (intros hc hi hm hd)
  (simp only [retain-succ])
  (apply rm-app-r) (apply rm-app-l)
  (apply (gather-mem CompRow (id-is comp-id (:id c)) (comp-contrib w) c (:id e) (:comps w) hc (Nat.beq_refl (:id c))))
  (simp only [comp-contrib hi])
  (apply rm-app-r) (apply rm-app-l)
  (exact (scan-mem EdgeRow edge-id (dep-of (:id c)) e (:edges w) hm hd)))

;; ---- ids: an edge's debtor is a row id (> 0); an edge id is admitted by nothing

(a/theorem has-pos [A :- Type, idf :- (=> A Nat), d :- Nat, n :- Nat, xs :- (List A)]
  (=> (= (tbl-all (id-in-range n) (tbl-ids idf xs)) true) (= (tbl-has idf d xs) true) (= (Nat.beq d 0) false))
  (intros hr hh)
  (have hm (= (nat-mem d (tbl-ids idf xs)) true)) (rw [nat-mem-ids]) (exact hh)
  (have r := (all-nat-mem (id-in-range n) d _ hr hm))
  (simp only [id-in-range Bool.and_eq_true Nat.blt_eq] at r)
  (cases hb (Nat.beq d 0))
  (case [false] (rfl))
  (case [true] (have e (= d 0)) (exact (Nat.eq_of_beq_eq_true hb)) (rw [e] at r) (omega)))

(a/theorem deb-nz [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (List.Mem e (:edges w)) (= (Nat.beq (:debtor e) 0) false))
  (intros h hm)
  (have ho := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                (And.left (And.right (inv-parts w h))) hm))
  (simp only [edge-ok deb-ok Bool.and_eq_true Bool.or_eq_true] at ho)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have hdo := (And.right ho))
  (cases hdo)
  (case [inl h1] (exact (has-pos CompRow comp-id (:debtor e) (:next-id w) (:comps w) (And.left (And.right hb)) h1)))
  (case [inr h2]
    (cases h2)
    (case [inl h3] (exact (has-pos TaskRow task-id (:debtor e) (:next-id w) (:tasks w) (And.left (And.right (And.right hb))) h3)))
    (case [inr h4]
      (cases h4)
      (case [inl h5] (exact (has-pos SourceRow source-id (:debtor e) (:next-id w) (:sources w)
                              (And.left (And.right (And.right (And.right (And.right hb))))) h5)))
      (case [inr h6] (exact (has-pos ResRow resource-id (:debtor e) (:next-id w) (:res w)
                              (And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right hb)))))))) (And.right h6)))))))

(a/theorem any-has-id [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), y :- Nat,
                       h :- (forall [a :- A] (=> (= (p a) true) (= (Nat.beq (idf a) y) true))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (nat-mem y (tbl-ids idf xs)) true))
  (induction xs)
  (case [nil] (intro ha) (simp [tbl-any] at ha))
  (case [cons hd t ih]
    (intro ha)
    (cases hp (p hd))
    (case [true] (simp only [tbl-ids nat-mem (h hd hp)]))
    (case [false]
      (simp only [tbl-any hp Bool.false_or] at ha)
      (cases hx (Nat.beq (idf hd) y))
      (all_goals (simp only [tbl-ids nat-mem hx (ih ha)])))))

(a/theorem and-beq [b :- Nat, y :- Nat, c :- Bool] (=> (= (Bool.and (Nat.beq b y) c) true) (= (Nat.beq b y) true))
  (intro h) (simp only [Bool.and_eq_true] at h) (exact (And.left h)))

(a/theorem mem-app-l [x :- Nat, xs :- (List Nat), ys :- (List Nat)]
  (=> (= (nat-mem x xs) true) (= (nat-mem x (nat-app xs ys)) true))
  (intro h) (simp only [nat-mem-app h Bool.true_or]))
(a/theorem mem-app-r [x :- Nat, xs :- (List Nat), ys :- (List Nat)]
  (=> (= (nat-mem x ys) true) (= (nat-mem x (nat-app xs ys)) true))
  (intro h) (simp only [nat-mem-app h Bool.or_true]))

(a/theorem not-both [x :- Nat, xs :- (List Nat), ys :- (List Nat)]
  (=> (= (nat-nodup (nat-app xs ys)) true) (= (nat-mem x xs) true) (= (nat-mem x ys) true) False)
  (intros hn h1 h2)
  (have d := (nodup-app-disj x xs ys hn h1))
  (rw [h2] at d) (cases d))

(a/theorem edge-not-admitted [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (List.Mem e (:edges w)) (= (admitted w (:id e)) false))
  (intros h hm)
  (have he := (mem-ids-has EdgeRow edge-id e (:edges w) hm))
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have u1 := (nat-nodup-app-right _ _ u))
  (have u2 := (nat-nodup-app-right _ _ u1))
  (have u3 := (nat-nodup-app-right _ _ u2))
  (have u4 := (nat-nodup-app-right _ _ u3))
  (have u5 := (nat-nodup-app-right _ _ u4))
  (cases a1 (tbl-any (adm-comp (:id e)) (:comps w)))
  (case [true]
    (have m := (any-has-id CompRow comp-id (adm-comp (:id e)) (:id e)
                 (fn [c :- CompRow, hc :- (= (adm-comp (:id e) c) true)] (and-beq (:id c) (:id e) _ hc)) (:comps w) a1))
    (exact (False.elim (not-both (edge-id e) _ _ u1 m (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-l _ _ _ he))))))))
  (case [false]
    (cases a2 (tbl-any (adm-source (:id e)) (:sources w)))
    (case [true]
      (have m := (any-has-id SourceRow source-id (adm-source (:id e)) (:id e)
                   (fn [c :- SourceRow, hc :- (= (adm-source (:id e) c) true)] (and-beq (:id c) (:id e) _ hc)) (:sources w) a2))
      (exact (False.elim (not-both (edge-id e) _ _ u4 m (mem-app-l _ _ _ he)))))
    (case [false]
      (cases a3 (tbl-any (adm-task (:id e)) (:tasks w)))
      (case [true]
        (have m := (any-has-id TaskRow task-id (adm-task (:id e)) (:id e)
                     (fn [c :- TaskRow, hc :- (= (adm-task (:id e) c) true)] (and-beq (:id c) (:id e) _ hc)) (:tasks w) a3))
        (exact (False.elim (not-both (edge-id e) _ _ u2 m (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-l _ _ _ he)))))))
      (case [false]
        (cases a4 (tbl-any (adm-pub (:id e)) (:pubs w)))
        (case [true]
          (have m := (any-has-id PubRow pub-id (adm-pub (:id e)) (:id e)
                       (fn [c :- PubRow, hc :- (= (adm-pub (:id e) c) true)] (and-beq (:id c) (:id e) _ hc)) (:pubs w) a4))
          (exact (False.elim (not-both (edge-id e) _ _ u5 he (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-l _ _ _ m)))))))
        (case [false] (simp only [admitted a1 a2 a3 a4 Bool.or_self]))))))

(a/theorem p3-parts [w :- World]
  (=> (= (p3-refs w) true)
      (And (= (tbl-all (dep-active (:comps w)) (:edges w)) true)
      (And (= (tbl-all (act-run-has (:runs w)) (:acts w)) true)
      (And (= (tbl-all marked-dep (:edges w)) true) (= (tbl-all (edge-sep w) (:edges w)) true)))))
  (intro h) (simp only [p3-refs Bool.and_eq_true] at h) (exact h))

;; a dep edge's creditor is live
(a/theorem bool-contra [b :- Bool] (=> (= b true) (= b false) False)
  (intros h1 h2) (rw [h1] at h2) (cases h2))

(a/theorem dep-cred-live [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (normalized w) true) (= (p3-refs w) true) (List.Mem e (:edges w))
      (= (Nat.beq (:kind e) ek-dep) true)
      (And (= (in-live w (:creditor e)) true)
           (forall [c :- CompRow] (=> (= (tbl-find comp-id (:creditor e) (:comps w)) (Option.some CompRow c))
                                      (And (List.Mem c (:comps w)) (And (= (:idle c) false) (= (:id c) (:creditor e))))))))
  (intros h hn hp hm hk)
  (have ho := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                (And.left (And.right (inv-parts w h))) hm))
  (simp only [edge-ok cred-ok hk Bool.and_eq_true] at ho)
  (have hda := (tbl-all-mem EdgeRow (dep-active (:comps w)) e (:edges w) (And.left (p3-parts w hp)) hm))
  (simp only [dep-active hk Bool.not_true Bool.false_or] at hda)
  (have hc (forall [c :- CompRow] (=> (= (tbl-find comp-id (:creditor e) (:comps w)) (Option.some CompRow c))
                                      (And (List.Mem c (:comps w)) (And (= (:idle c) false) (= (:id c) (:creditor e)))))))
  (intros c hf)
  (have cm := (tbl-find-mem CompRow comp-id (:creditor e) c (:comps w) hf))
  (have ci (= (:id c) (:creditor e))) (exact (tbl-find-id CompRow comp-id (:creditor e) c (:comps w) hf))
  (have cn := (tbl-all-mem CompRow (not-idle-if-id (:creditor e)) c (:comps w) hda cm))
  (have ci2 (= (Nat.beq (:id c) (:creditor e)) true)) (rw [ci]) (exact (Nat.beq_refl (:creditor e)))
  (simp only [not-idle-if-id ci2 Bool.not_true Bool.false_or] at cn)
  (exact (And.intro cm (And.intro (bnot-true _ cn) ci)))
  (have hlive (= (in-live w (:creditor e)) true))
  (cases hf (tbl-find comp-id (:creditor e) (:comps w)))
  (case [none] (have hn2 := (tbl-find-none-has CompRow comp-id (:creditor e) (:comps w) hf)) (exact (False.elim (bool-contra _ (And.left ho) hn2))))
  (case [some c]
    (have p := (hc c hf))
    (have hl := (normalized-comps w c hn (And.left p) (And.left (And.right p))))
    (exact (Eq.trans (congrArg (fn [x :- Nat] (in-live w x)) (Eq.symm (And.right (And.right p)))) hl)))
  (exact (And.intro hlive hc)))

(a/theorem cred-kept [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (normalized w) true) (= (p3-refs w) true) (List.Mem e (:edges w))
      (= (Bool.or (host-cred e) (keep-fn w (:creditor e))) true))
  (intros h ha hn hp hm)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [true]
    (simp only [(keep-of-live w (:creditor e) (And.left (dep-cred-live w e h hn hp hm hk))) Bool.or_true]))
  (case [false]
    (cases hh (host-cred e))
    (case [true] (simp only [Bool.true_or]))
    (case [false]
      (have ho := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                    (And.left (And.right (inv-parts w h))) hm))
      (simp only [edge-ok cred-ok hk hh Bool.and_eq_true] at ho)
      (cases hf (tbl-find act-id (:creditor e) (:acts w)))
      (case [none] (have hn2 := (tbl-find-none-has ActRow act-id (:creditor e) (:acts w) hf)) (exact (False.elim (bool-contra _ (And.left ho) hn2))))
      (case [some a]
        (have am := (tbl-find-mem ActRow act-id (:creditor e) a (:acts w) hf))
        (have ai (= (:id a) (:creditor e))) (exact (tbl-find-id ActRow act-id (:creditor e) a (:acts w) hf))
        (have hrh := (tbl-all-mem ActRow (act-run-has (:runs w)) a (:acts w) (And.left (And.right (p3-parts w hp))) am))
        (simp only [act-run-has] at hrh)
        (cases hr (tbl-find run-id (:run a) (:runs w)))
        (case [none] (have hn3 := (tbl-find-none-has RunRow run-id (:run a) (:runs w) hr)) (exact (False.elim (bool-contra _ hrh hn3))))
        (case [some r]
          (have rm := (tbl-find-mem RunRow run-id (:run a) r (:runs w) hr))
          (have ri (= (:id r) (:run a))) (exact (tbl-find-id RunRow run-id (:run a) r (:runs w) hr))
          (have hok := (tbl-all-mem RunRow (run-ok-for (:run a)) r (:runs w) (tbl-all-mem ActRow (act-run-ok (:runs w)) a (:acts w) ha am) rm))
          (have ri2 (= (Nat.beq (:id r) (:run a)) true)) (rw [ri]) (exact (Nat.beq_refl (:run a)))
          (simp only [run-ok-for ri2 Bool.not_true Bool.false_or] at hok)
          (have rl := (normalized-runs w r hn rm hok))
          (have ar (= (Nat.beq (:run a) (:id r)) true)) (rw [ri]) (exact (Nat.beq_refl (:run a)))
          (have al := (live-close w (:id r) (:id a) rl (succ-act w r a rm hok am ar)))
          (have al2 := (Eq.trans (congrArg (fn [x :- Nat] (in-live w x)) (Eq.symm ai)) al))
          (simp only [(keep-of-live w (:creditor e) al2) Bool.or_true]))))))

(a/theorem fs-ref-ok [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (normalized w) true) (= (p3-refs w) true) (List.Mem e (:edges w))
      (= (fs-ref (keep-fn w) e) true))
  (intros h ha hn hp hm)
  (cases hl (in-live w (:id e)))
  (case [true]
    (have dl := (live-close w (:id e) (:debtor e) hl (succ-edge w e hm (deb-nz w e h hm))))
    (simp only [fs-ref (cred-kept w e h ha hn hp hm) (keep-of-live w (:debtor e) dl) Bool.and_self Bool.or_true]))
  (case [false]
    (have hs := (tbl-all-mem EdgeRow (edge-sep w) e (:edges w) (And.right (And.right (And.right (p3-parts w hp)))) hm))
    (simp only [edge-sep Bool.and_eq_true] at hs)
    (have hl2 (= (reach-mem (:id e) (live-list w)) false)) (exact hl)
    (have k0 (= (keep-fn w (:id e)) false))
    (simp only [keep-fn keep-with hl2 (bnot-true _ (And.left hs)) (bnot-true _ (And.right hs)) (edge-not-admitted w e h hm) Bool.or_self])
    (simp only [fs-ref k0 Bool.not_false Bool.true_or])))

(a/theorem fs-mark-ok [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (normalized w) true) (= (p3-refs w) true) (List.Mem e (:edges w))
      (= (fs-mark (keep-fn w) e) true))
  (intros h hn hp hm)
  (cases hk (:marked e))
  (case [false] (simp only [fs-mark hk Bool.false_and Bool.not_false Bool.true_or]))
  (case [true]
    (have hd := (tbl-all-mem EdgeRow marked-dep e (:edges w) (And.left (And.right (And.right (p3-parts w hp)))) hm))
    (simp only [marked-dep hk Bool.not_true Bool.false_or] at hd)
    (have q := (dep-cred-live w e h hn hp hm hd))
    (cases hf (tbl-find comp-id (:creditor e) (:comps w)))
    (case [none]
      (have ho := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                    (And.left (And.right (inv-parts w h))) hm))
      (simp only [edge-ok cred-ok hd Bool.and_eq_true] at ho)
      (have hn2 := (tbl-find-none-has CompRow comp-id (:creditor e) (:comps w) hf)) (exact (False.elim (bool-contra _ (And.left ho) hn2))))
    (case [some c]
      (have p := ((And.right q) c hf))
      (have cl := (Eq.trans (congrArg (fn [x :- Nat] (in-live w x)) (And.right (And.right p))) (And.left q)))
      (have dep (= (dep-of (:id c) e) true)) (simp only [dep-of hd (And.right (And.right p)) Nat.beq_refl Bool.and_self])
      (have el := (live-close w (:id c) (:id e) cl (succ-dep w c e (And.left p) (And.left (And.right p)) hm dep)))
      (simp only [fs-mark (keep-of-live w (:id e) el) Bool.or_true]))))

;; Theorem (P3 core): in a normalized world with the reference invariants, the filter is edge-safe
(a/theorem filter-safe-of-refs [w :- World]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (normalized w) true) (= (p3-refs w) true)
      (= (filter-safe w) true))
  (intros h ha hn hp)
  (simp only [filter-safe filter-safe-k Bool.and_eq_true])
  (exact (And.intro
           (all-of-mem EdgeRow (fs-ref (keep-fn w)) (:edges w) (fn [e :- EdgeRow, hm :- (List.Mem e (:edges w))] (fs-ref-ok w e h ha hn hp hm)))
           (all-of-mem EdgeRow (fs-mark (keep-fn w)) (:edges w) (fn [e :- EdgeRow, hm :- (List.Mem e (:edges w))] (fs-mark-ok w e h hn hp hm))))))
