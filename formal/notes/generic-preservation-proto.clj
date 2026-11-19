;; Prototype for notes/generic-preservation.md: one generic copy of part of the step-inv proof tree over an
;; abstract rest part Q and a structure GPrim Q of per-primitive obligations, instantiated for the bundle gl.
;;
;; Not part of the model (nothing loads it). To reproduce, from formal/ in a REPL (clojure -M:repl):
;;   (require 'spindel.v2.inv.copier)          ; about 3 minutes
;;   (load-file "notes/generic-preservation-proto.clj")
;; It defines GPrim, gq (the generic bundle), the gq-* generic lemmas, pgl : GPrim gl-rest, and the chk-*
;; restatements of gl's copies proved from the generic lemmas, then prints the timings. It uses the copier's
;; private functions, so it runs inside spindel.v2.inv.copier.

(in-ns 'spindel.v2.inv.copier)

;; ---- the source lemmas that mention inv-sample (S) and their proof dependencies
(def S (set (keep (fn [[n g]] (when (statement-mentions-inv? g) n)) @source-theorems)))
(defn pdeps [n] (let [[_ _ _ _ & proof] (theorem-source n)] (distinct (filter S (filter symbol? (flatten proof))))))
;; ---- gl's primitives, overrides and patches; roots whose closure (stopping at gl's primitives and
;; overrides) contains no patched lemma
(def copied (set @(:copied GL)))
(def gl-prims (set (keep (fn [[o n]] (when-not (copied n) o)) @(:renames GL))))
(def gl-ovr (set (keys @(:overrides GL))))
(def gl-pat (set (keys @(:patches GL))))
(defn clos2 [root stop] (loop [todo [root] seen #{}]
   (if-let [n (first todo)] (if (seen n) (recur (rest todo) seen)
     (recur (concat (rest todo) (if (and (stop n) (not= n root)) [] (pdeps n))) (conj seen n))) seen)))
(def stop (fn [n] (or (gl-prims n) (gl-ovr n))))
(def cands2 (->> S (remove stop) (remove gl-pat)
   (map (fn [n] (let [c (clos2 n stop)] [n (count (remove stop c)) (count (filter gl-prims c)) (count (filter gl-ovr c)) (count (filter gl-pat c))])))
   (remove (fn [[_ _ _ _ p]] (pos? p)))
   (sort-by second >)))
;; ---- the patch-free part of gl's tree, and its maximal roots
(def clean-roots (map first cands2))
(def clean-union (set (mapcat #(clos2 % stop) clean-roots)))
(def clean-comp (set (remove stop clean-union)))
(def clean-prims (set (filter gl-prims clean-union)))
(def all-comp (set (remove stop (clos2 'step-inv stop))))
(println "gl composite lemmas:" (count all-comp) "patch-free:" (count clean-comp) "primitives used:" (count clean-prims))
;; maximal clean roots (not inside another clean root's closure)
(def maximal (remove (fn [r] (some #(and (not= % r) ((clos2 % stop) r)) clean-roots)) clean-roots))
;; ---- the prototype's roots: no run-upd / task-upd (their side conditions are bundle-specific)
(def bad '#{inv-run-upd inv-task-upd})
(def proto-roots (filter (fn [r] (not-any? bad (clos2 r stop))) maximal))
(def proto-union (set (mapcat #(clos2 % stop) proto-roots)))
(def proto-comp (set (remove stop proto-union)))
(def proto-prims (sort (filter gl-prims proto-union)))
;; ---- the obligation structure GPrim Q (one field per primitive) and the generic bundle gq
;; generic preservation, prototype: obligations of a rest part Q at the primitives of a closure
(defn leaf-info [orig]
  (let [[_ _ binders stmt] (theorem-source orig) prems (vec (butlast (rest stmt))) concl (last stmt)
        i (first (keep-indexed (fn [i p] (when (inv-premise? p) i)) prems))]
    {:binders binders :prems prems :i i :w (second (second (nth prems i))) :w2 (second (second concl))}))
(defn fname [orig] (symbol (str "o-" (name orig))))
(defn field-form [orig]
  (let [{:keys [binders prems w w2]} (leaf-info orig)]
    (list (fname orig) (list 'forall binders (concat ['=>] prems [(list '= (list 'Q w) true) (list '= (list 'Q w2) true)])))))
(defn hsyms [prems] (vec (map-indexed (fn [i _] (symbol (str "h" i))) prems)))
;; rest-f of the generic primitive: the field applied to the binders, the premises, R
(defn gq-rest-f [orig]
  (let [{:keys [binders prems i w]} (leaf-info orig) hs (hsyms prems)]
    (apply list (list (symbol (str "GPrim." (name (fname orig)))) 'P)
           (concat (binder-names binders) (assoc hs i (list 'gq-sample 'Q 'P w (nth hs i))) ['R]))))
;; the field proof for a concrete bundle B (its prim copy of orig)
(defn field-proof [B orig]
  (let [{:keys [binders prems i w w2]} (leaf-info orig) hs (hsyms prems) bc (get @(:renames B) orig)
        b (fn [s] (symbol (str (name (:pred B)) s)))]
    (list 'fn (vec (concat binders (mapcat (fn [h p] [(symbol (str h)) :- p]) hs prems) ['hq :- (list '= (list (b "-rest") w) true)]))
          (list (b "-rest-of") w2 (apply list bc (concat (binder-names binders) (assoc hs i (list (b "-intro") w (nth hs i) 'hq))))))))
(def fields (vec (remove #{'inv-parts} proto-prims)))
(eval (apply list 'a/structure 'GPrim '[Q (=> World Bool)] (map field-form fields)))
(eval '(a/defn gq [Q :- (=> World Bool), P :- (GPrim Q), w :- World] Bool (Bool.and (inv-sample w) (Q w))))
(eval '(a/defn gq-rest [Q :- (=> World Bool), P :- (GPrim Q), w :- World] Bool (Q w)))
(eval '(a/theorem gq-sample [Q :- (=> World Bool), P :- (GPrim Q), w :- World] (=> (= (gq Q P w) true) (= (inv-sample w) true))
         (intro h) (simp only [gq Bool.and_eq_true] at h) (exact (And.left h))))
(eval '(a/theorem gq-rest-of [Q :- (=> World Bool), P :- (GPrim Q), w :- World] (=> (= (gq Q P w) true) (= (gq-rest Q P w) true))
         (intro h) (simp only [gq Bool.and_eq_true] at h) (simp only [gq-rest]) (exact (And.right h))))
(eval '(a/theorem gq-intro [Q :- (=> World Bool), P :- (GPrim Q), w :- World] (=> (= (inv-sample w) true) (= (gq-rest Q P w) true) (= (gq Q P w) true))
         (intros h1 h2) (simp only [gq-rest] at h2) (simp only [gq h1 h2 Bool.and_self])))
(eval '(a/theorem gq-parts [Q :- (=> World Bool), P :- (GPrim Q), w :- World]
         (=> (= (gq Q P w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
         (intro h) (exact (inv-parts w (gq-sample Q P w h)))))
(def GQ (mk-bundle 'gq '[Q :- (=> World Bool), P :- (GPrim Q)] "gq-" {}))
(swap! (:renames GQ) assoc 'inv-parts 'gq-parts)
(doseq [o fields] (prim! GQ o (gq-rest-f o)))
;; ---- the generic copy (lcopy! over gq); keep the roots whose whole closure copies
(def roots2 (remove #{'inv-sample-empty} proto-roots))
(def fails (vec (mapcat #(lcopy-try! GQ %) roots2)))
(def failset (set (map first fails)))
(def ok-roots (filter (fn [r] (and (not (failset r)) (not-any? failset (closure GQ r)))) roots2))
(def inv-of (into {} (map (fn [[o n]] [n o]) @(:renames GQ))))
(def gen-origs (vec (keep inv-of @(:copied GQ))))
(defn inst-bundle! [B pname]
  (let [t0 (System/nanoTime)]
    (try (eval (list 'a/theorem pname [] (list 'GPrim (symbol (str (name (:pred B)) "-rest"))) (list 'exact (apply list 'GPrim.mk (map #(field-proof B %) fields)))))
         (catch Throwable e (println "theorem failed:" (subs (ex-message e) 0 (min 200 (count (ex-message e)))))
           (eval (list 'a/defn pname [] (list 'GPrim (symbol (str (name (:pred B)) "-rest"))) (apply list 'GPrim.mk (map #(field-proof B %) fields))))))
    (/ (- (System/nanoTime) t0) 1e9)))
;; ---- instantiation: pgl : GPrim gl-rest from gl's primitive lemmas (a structure in Type, hence a/defn)
;; restate B's copy of orig and prove it from the generic lemma
(defn check-form [B pname orig]
  (let [[_ _ binders stmt] (copy-form B (source-of B orig) 'x @(:renames B))]
    (list 'a/theorem (symbol (str "chk-" (name (get @(:renames B) orig)))) binders stmt
          (list 'exact (apply list (get @(:renames GQ) orig) (symbol (str (name (:pred B)) "-rest")) pname (binder-names binders))))))
(defn check-bundle! [B pname]
  (let [skip (set (concat (keys @(:overrides B)) (keys @(:patches B))))
        os (remove skip gen-origs)
        t0 (System/nanoTime)
        res (vec (for [o os] (try (binding [*ns* lit-ns] (eval (check-form B pname o))) nil
                                  (catch Throwable e [o (subs (ex-message e) 0 (min 160 (count (ex-message e))))]))))]
    {:checked (count os) :failed (vec (remove nil? res)) :s (/ (- (System/nanoTime) t0) 1e9)}))
(def pgl-s (inst-bundle! GL (quote pgl)))
(def gl-check (check-bundle! GL (quote pgl)))
(defn mk-defs! [p params pargs body-rest]
  (let [s #(symbol (str p %)) pv (vec params)]
    (eval (list 'a/defn (s "-rest") (conj pv 'w :- 'World) 'Bool body-rest))
    (eval (list 'a/defn (symbol p) (conj pv 'w :- 'World) 'Bool (list 'Bool.and '(inv-sample w) (concat (list (s "-rest")) pargs ['w]))))
    (eval (list 'a/theorem (s "-sample") (conj pv 'w :- 'World) (list '=> (list '= (concat (list (symbol p)) pargs ['w]) true) '(= (inv-sample w) true))
                '(intro h) (list 'simp 'only [(symbol p) 'Bool.and_eq_true] 'at 'h) '(exact (And.left h))))
    (eval (list 'a/theorem (s "-rest-of") (conj pv 'w :- 'World) (list '=> (list '= (concat (list (symbol p)) pargs ['w]) true) (list '= (concat (list (s "-rest")) pargs ['w]) true))
                '(intro h) (list 'simp 'only [(symbol p) 'Bool.and_eq_true] 'at 'h) '(exact (And.right h))))
    (eval (list 'a/theorem (s "-intro") (conj pv 'w :- 'World) (list '=> '(= (inv-sample w) true) (list '= (concat (list (s "-rest")) pargs ['w]) true) (list '= (concat (list (symbol p)) pargs ['w]) true))
                '(intros h1 h2) (list 'simp 'only [(symbol p) 'h1 'h2 'Bool.and_self])))
    (eval (list 'a/theorem (s "-parts") (conj pv 'w :- 'World) (list '=> (list '= (concat (list (symbol p)) pargs ['w]) true) '(And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
                '(intro h) (list 'exact (list 'inv-parts 'w (concat (list (s "-sample")) pargs ['w 'h])))))))
(defn timed-copy! [B prim-f]
  (swap! (:renames B) assoc 'inv-parts (symbol (str (name (:pred B)) "-parts")))
  (let [t0 (System/nanoTime)]
    (doseq [o fields] (prim! B o (prim-f o)))
    (let [t1 (System/nanoTime)]
      (doseq [r ok-roots] (lcopy! B r))
      {:prims-s (/ (- t1 t0) 1e9) :copy-s (/ (- (System/nanoTime) t1) 1e9) :copied (count @(:copied B))})))
;; ---- timing: a concrete bundle gt with a trivial rest part (the cost of one per-bundle copy of these
;; lemmas) against a second generic bundle gq2 (the one-time cost of the generic proofs)
(eval '(a/defn gt-rest [w :- World] Bool true))
(eval '(a/defn gt [w :- World] Bool (Bool.and (inv-sample w) (gt-rest w))))
(eval '(a/theorem gt-sample [w :- World] (=> (= (gt w) true) (= (inv-sample w) true)) (intro h) (simp only [gt Bool.and_eq_true] at h) (exact (And.left h))))
(eval '(a/theorem gt-rest-of [w :- World] (=> (= (gt w) true) (= (gt-rest w) true)) (intro h) (rfl)))
(eval '(a/theorem gt-intro [w :- World] (=> (= (inv-sample w) true) (= (gt-rest w) true) (= (gt w) true)) (intros h1 h2) (simp only [gt gt-rest h1 Bool.and_self])))
(eval '(a/theorem gt-parts [w :- World] (=> (= (gt w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true)))) (intro h) (exact (inv-parts w (gt-sample w h)))))
(def GT (mk-bundle 'gt [] "gt-" {}))
(def gt-res (timed-copy! GT (fn [_] 'R)))
(mk-defs! "gq2" '[Q :- (=> World Bool), P :- (GPrim Q)] '[Q P] '(Q w))
(def GQ2 (mk-bundle 'gq2 '[Q :- (=> World Bool), P :- (GPrim Q)] "gq2-" {}))
(def gq2-res (timed-copy! GQ2 (fn [o] (walk/postwalk-replace {'gq-sample 'gq2-sample} (gq-rest-f o)))))
(println "generic lemmas" (count @(:copied GQ)) "pgl s" pgl-s "gl restatements" (select-keys gl-check [:checked :s])
         "per-bundle copy (gt)" gt-res "generic copy (gq2)" gq2-res)
