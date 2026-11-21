(ns spindel.v2.pres.part
  "Part definitions: what a part of the invariant is made of, for the generic step tree
  (spindel.v2.pres.tree).

    source-theorems   the base proof as data: every theorem of the step's namespaces
                      (`lit-source-nss`), read from the source files (`theorem-source`).
    mk-bundle         a part's record: its predicate (inv-sample and a rest part), parameters, name
                      prefix, the extra arguments of its cells, and its lemma per base lemma
                      (`:renames`).
    prim!             a cell: the part's lemma for a primitive edit, from the base lemma and a proof
                      of the rest part (a form, an `rfl` frame, or a frame from the footprint).
    defpart, frame!   the declaration front end: a part's view (the World fields its rest part
                      reads) and its cells; every primitive whose footprint misses the view gets a
                      generated frame cell (spindel.v2.pres.frames).
    copy-name, copy-form   a base lemma's name and statement for a part.
    inst              a hand-written proof generic in the bundle (`$name`, `%G`).

  Until stage 4 of the proof layout (formal/notes/proof-layout.md §5l-§5y) this namespace also held
  the copier (`lcopy!`, `override!`, `patch!`), which re-checked the base proof's text for every
  part. Every part's composite lemmas now come from the tree.

  Generated theorems are evaluated in this namespace. It holds no theorem of its own."
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
            [spindel.v2.inv.rank :refer :all]
            [spindel.v2.progress.casc :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.pres.frames :as frames]))

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
;; :renames (base lemma -> the part's lemma) and :copied (the generated names) atoms
(defn mk-bundle [pred params prefix extra]
  {:pred pred :params params :prefix prefix :extra-args extra
   :renames (atom {}) :copied (atom [])})

(defn- pargs [B] (binder-names (:params B)))
(defn- papp [B head & args] (apply list head (concat (pargs B) args)))
(defn- bsym [B suffix] (symbol (str (name (:pred B)) suffix)))

(defn- pred-subst [B x]
  (walk/postwalk (fn [y] (if (and (seq? y) (= 'inv-sample (first y))) (papp B (:pred B) (second y)) y)) x))

;; a primitive: the inv-sample lemma plus a proof of the bundle's rest part; `rest-f` is a form
;; over the binder names, premise names h0..hn and R = the rest part of the input world; nil = frame
;; by `rfl`; :frame = frame from the primitive's footprint and the part's declared view
;; (spindel.v2.pres.frames/frame-term)
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
        rest-term (cond
                    (= rest-f :frame)
                    (let [used (set (filter symbol? (flatten (list w2))))
                          t (frames/frame-term (bsym B "-rest") (pargs B) orig w w2
                                               (filter used (binder-names binders)))]
                      (when-not t (throw (ex-info (str orig " is not a frame of " (bsym B "-rest")) {})))
                      (list 'Eq.trans t R))
                    rest-f (walk/postwalk-replace {'R R} rest-f)
                    :else (list 'Eq.trans 'e-frame R))]
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

;; ---------------------------------------------------------------------------
;; Parts: the declaration front end (formal/notes/proof-layout.md, stage 1)
;;
;; A part declares what its rest predicate reads (its view) and only the primitive cells that need an
;; argument. Every other primitive is a frame of the view, and its cell is generated from the
;; primitive's footprint and the view (spindel.v2.pres.frames). `defpart` emits the cells (prim!,
;; renames) under the names and statements they always had.

;; pred -> {:reads #{fields}, :cells [base lemmas given by hand], :frames [base lemmas generated]}
(defonce parts (atom {}))

(defn frame!
  "The frame cell of primitive `orig` for bundle B, from the footprint and B's declared view."
  [B orig] (prim! B orig :frame))

(defn defpart
  "Declare a part's view and its primitive cells, and emit the cells:
    :reads  the World fields the rest predicate reads (`spindel.v2.pres.frames/defview` states and
            checks `<pred>-rest-frame-<f>` for every other field f).
    :cells  {base-lemma cell} for the primitives whose footprint meets the view. A cell is a symbol
            (a hand lemma with the bundle's statement, used as the copy), a form (prim!'s rest form,
            over the binders and R, the rest part of the input world), or nil (prim!'s `rfl` frame:
            the edit keeps the columns the part reads).
  Every primitive not in :cells whose footprint misses the view gets a generated frame cell, unless
  the bundle already has a copy of it."
  [B & {:keys [reads cells]}]
  (let [rest-sym (bsym B "-rest")]
    (frames/defview rest-sym (:params B) reads)
    (doseq [[p c] (sort-by key cells)]
      (if (symbol? c) (swap! (:renames B) assoc p c) (prim! B p c)))
    (let [fs (vec (for [p (sort (keys @frames/footprints))
                        :when (and (not (contains? cells p)) (not (contains? @(:renames B) p))
                                   (frames/frame? rest-sym p))]
                    (do (when (contains? (:extra-args B) p)
                          (throw (ex-info (str (:pred B) ": " p " has extra args but is a frame of the view") {})))
                        p)))]
      (doseq [p fs] (frame! B p))
      (swap! parts assoc (:pred B) {:reads (set reads) :cells (vec (sort (keys cells))) :frames fs})
      B)))
