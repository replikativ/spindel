(ns org.replikativ.spindel.dom.differential-fuzz
  "Program model for the differential DOM fuzzer
   (`dom/differential_fuzz_test.cljs`): random component trees as DATA, an
   interpreter that renders them with the real element/spin/ifor-each
   machinery, the reference state model the op sequences run against, and a
   printer that turns a (shrunk) program back into readable spindel code.

   Why programs are data. test.check shrinks values, not code. A program here
   is a small tree of nodes; one interpreter renders any of them. Every node
   carries its own synthetic source location (`{:file \"differential-fuzz\"
   :line <node-id>}`), so two nodes are two distinct call sites exactly as two
   `el/div` forms in a real file are — the interpreter's own call sites never
   leak into the addresses.

   Node kinds (after `normalize`):

     {:op :spin :id i :tracks [s ...] :dfr d|nil :body n}
         a nested spin: `track`s 0-2 signals AT THE TOP (the documented
         track-placement rule), optionally then `await`s a deferred, then
         renders its body
     {:op :el :id i :tag t :attr a :key? k :item-root? r :children [n ...]}
         an element with 0-3 child slots; `:attr` is nil, [:sig s] (a
         `data-n` and a present/absent `title` from that signal) or [:item]
     {:op :if :id i :sig s :then n :else n|nil}
         a conditional on a signal's `:b` — flips a subtree, or the spin's
         root when it is a spin's body
     {:op :for :id i :sig s :item n}
         `for-each*` (what `ifor-each` expands to) over the signal's `:xs`
         keyed by `:id`; `:item` is the per-item template, always an element
         stamped with `data-fk` so the harness can find it by key
     {:op :text :id i :src [:lit] | [:n s] | [:item-v] | [:item-id] | [:dval d]}

   Scoping, enforced by `normalize` so every shrink is still a valid program:
   a node may read a signal only below a spin that tracks it, a deferred's
   value only below the spin that awaited it, and an ifor-each item template
   sees ONLY its item (sharp edge #2: per-key renders are memoised on item
   equality, so a closure value would legitimately go stale — that is the
   documented contract, not a bug the oracle should report).

   Async-ness is static: an element whose child may be a spin is built inside
   its own spin and `await`s that child in its slot (the await-inside-element
   shape), exactly as a component returning a spin would be."
  (:refer-clojure :exclude [await])
  (:require [clojure.string :as str]
            [clojure.test.check.generators :as gen]
            [org.replikativ.spindel.dom.addressing :as addr]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.dom.addressing]
                            [org.replikativ.spindel.dom.differential-fuzz :refer [await-if]])))

;; =============================================================================
;; Shape of the world
;; =============================================================================

(def n-signals
  "Signals every program and op sequence range over. Each holds
   `{:b bool :n int :xs [{:id k :v int} ...]}`."
  3)

(def n-deferreds 2)

(def ^:private tags [:div :span :ul :li :section :p])

;; =============================================================================
;; Generators — raw trees, shrunk by test.check, made valid by `normalize`
;; =============================================================================

(def ^:private gen-sig (gen/choose 0 (dec n-signals)))
(def ^:private gen-dfr (gen/choose 0 (dec n-deferreds)))

(def ^:private gen-leaf
  (gen/fmap (fn [[k s]] {:op :text :kind k :ref s})
            (gen/tuple (gen/elements [:lit :n :item-v :item-id :dval])
                       (gen/choose 0 (dec n-signals)))))

(defn- gen-container [inner]
  (gen/frequency
   [[6 (gen/fmap (fn [[tag attr children]]
                   {:op :el :tag tag :attr attr :children children})
                 (gen/tuple (gen/elements tags)
                            (gen/one-of [(gen/return nil)
                                         (gen/fmap (fn [s] [:sig s]) gen-sig)
                                         (gen/return [:item])])
                            (gen/bind (gen/frequency [[1 (gen/return 0)] [2 (gen/return 1)]
                                                      [3 (gen/return 2)] [3 (gen/return 3)]])
                                      #(gen/vector inner %))))]
    [2 (gen/fmap (fn [[s then else]] {:op :if :sig s :then then :else else})
                 (gen/tuple gen-sig inner (gen/one-of [(gen/return nil) inner])))]
    [3 (gen/fmap (fn [[tracks dfr body]] {:op :spin :tracks tracks :dfr dfr :body body})
                 (gen/tuple (gen/vector gen-sig 0 2)
                            (gen/frequency [[3 (gen/return nil)] [1 gen-dfr]])
                            inner))]
    [3 (gen/fmap (fn [[s key? item]] {:op :for :sig s :key? key? :item item})
                 (gen/tuple gen-sig gen/boolean inner))]]))

(def max-depth
  "Depth cap of generated program trees. With at most 3 children per
   element a tree stays under a few hundred nodes; every node is a mounted
   subtree in two contexts per observation."
  5)

(defn- gen-node
  "A raw tree of at most `depth` levels; containers get likelier the more
   depth is left. (`gen/recursive-gen` spends its size budget across
   levels and mostly yields leaves — measured ~2 elements per compared
   DOM.)"
  [depth]
  (if (zero? depth)
    gen-leaf
    (gen/frequency [[1 gen-leaf]
                    [(* 2 depth) (gen-container (gen-node (dec depth)))]])))

(def gen-raw-program
  "A raw root: always a spin (render-spin! mounts a spin). Depth grows with
   the generator size up to `max-depth`; shrinks toward a spin around a
   leaf."
  (gen/sized
   (fn [size]
     (gen/fmap (fn [[tracks dfr body]] {:op :spin :tracks tracks :dfr dfr :body body})
               ;; the root tracks at least one signal: with nothing in
               ;; scope every :if/:for below it would collapse
               (gen/tuple (gen/vector gen-sig 1 2)
                          (gen/frequency [[3 (gen/return nil)] [1 gen-dfr]])
                          (gen-node (min max-depth (inc (quot size 5)))))))))

(def ^:private gen-items
  "A keyed list: distinct ids from a small pool, so inserts collide with
   existing keys and deletes/reorders hit live ones."
  (gen/fmap (fn [pairs]
              (->> pairs
                   (reduce (fn [[seen acc] [id v]]
                             (if (seen id) [seen acc] [(conj seen id) (conj acc {:id id :v v})]))
                           [#{} []])
                   second))
            (gen/vector (gen/tuple (gen/choose 0 7) (gen/choose 0 4)) 0 6)))

(def gen-init
  "Initial values of the `n-signals` signals."
  (gen/vector (gen/hash-map :b gen/boolean :n (gen/choose 0 4) :xs gen-items)
              n-signals))

(def gen-op
  (gen/frequency
   [[3 (gen/fmap (fn [s] [:flip s]) gen-sig)]
    [2 (gen/fmap (fn [[s n]] [:set-n s n]) (gen/tuple gen-sig (gen/choose 0 4)))]
    [4 (gen/fmap (fn [[s id pos v]] [:ins s id pos v])
                 (gen/tuple gen-sig (gen/choose 0 7) gen/nat (gen/choose 0 4)))]
    [3 (gen/fmap (fn [[s pos]] [:del s pos]) (gen/tuple gen-sig gen/nat))]
    [3 (gen/fmap (fn [[s from to]] [:move s from to]) (gen/tuple gen-sig gen/nat gen/nat))]
    [3 (gen/fmap (fn [[s pos v]] [:upd s pos v]) (gen/tuple gen-sig gen/nat (gen/choose 0 4)))]
    [1 (gen/fmap (fn [[d v]] [:deliver d v]) (gen/tuple gen-dfr (gen/choose 0 9)))]
    [2 (gen/return [:tick])]
    [3 (gen/return [:settle])]]))

(def gen-case
  "One fuzz case: a program, initial signal values, and the ops to run.
   `[:settle]` ops mark quiescent observation points; ops between two settles
   land in flight, without the engine settling in between. `[:tick]` yields
   ONE event-loop task — partial progress, so later ops interleave with a
   half-processed cascade."
  (gen/hash-map :program gen-raw-program
                :init gen-init
                :ops (gen/vector gen-op 0 30)))

;; =============================================================================
;; Normalization — any raw tree becomes a valid, uniquely-numbered program
;; =============================================================================

(defn- ensure-el
  "Coerce a normalized node into one that renders an ELEMENT (a spin's root
   must be an element: `render-spin!` mounts it, and a nil frame is kept)."
  [node next-id!]
  (case (:op node)
    :el node
    :if (-> node
            (update :then ensure-el next-id!)
            (update :else #(if % (ensure-el % next-id!)
                               {:op :el :id (next-id!) :tag :div :attr nil :children []})))
    :spin (update node :body ensure-el next-id!)
    {:op :el :id (next-id!) :tag :div :attr nil :children [node]}))

(defn- pick
  "Resolve a generated signal/deferred reference against what is in scope:
   itself if available, else a deterministic in-scope substitute, else nil.
   (Dropping every out-of-scope reference starves the tree of reactive
   nodes; substituting keeps the shape the generator chose.)"
  [ref avail]
  (cond (contains? avail ref) ref
        (seq avail) (nth (sort avail) (mod ref (count avail)))
        :else nil))

(defn- norm [raw {:keys [avail davail item?] :as scope} next-id!]
  (let [id (next-id!)]
    (case (:op raw)
      :text
      (let [{:keys [kind ref]} raw
            src (cond
                  (and (= kind :n) (pick ref avail)) [:n (pick ref avail)]
                  (and (= kind :item-v) item?) [:item-v]
                  (and (= kind :item-id) item?) [:item-id]
                  (and (= kind :dval) (pick ref davail)) [:dval (pick ref davail)]
                  :else [:lit])]
        {:op :text :id id :src src})

      :el
      {:op :el :id id :tag (:tag raw)
       :attr (let [a (:attr raw)]
               (cond (and (= :sig (first a)) (pick (second a) avail)) [:sig (pick (second a) avail)]
                     (and (= :item (first a)) item?) a
                     :else nil))
       :children (mapv #(norm % scope next-id!) (take 3 (:children raw)))}

      :if
      (if-let [s (pick (:sig raw) avail)]
        {:op :if :id id :sig s
         :then (norm (:then raw) scope next-id!)
         :else (some-> (:else raw) (norm scope next-id!))}
        (norm (:then raw) scope next-id!))

      :spin
      (let [tracks (vec (distinct (:tracks raw)))
            dfr (when-not (contains? (:profile scope) :no-await) (:dfr raw))]
        {:op :spin :id id :tracks tracks :dfr dfr
         :body (norm (:body raw)
                     (cond-> (update scope :avail into tracks)
                       dfr (update :davail conj dfr))
                     next-id!)})

      :for
      (if-let [s (pick (:sig raw) avail)]
        (let [key? (or (not (contains? (:profile scope) :unkeyed)) (boolean (:key? raw)))
              tpl (ensure-el (norm (:item raw)
                                   (assoc scope :avail #{} :davail #{} :item? true)
                                   next-id!)
                             next-id!)
              ;; the template's root is what a key identifies — it must be
              ;; an element of its own, not a pass-through spin/if
              item (if (= :el (:op tpl))
                     (assoc tpl :item-root? true :key? key?)
                     {:op :el :id (next-id!) :tag :div :attr nil :children [tpl]
                      :item-root? true :key? key?})
              for-node {:op :for :id id :sig s :item item}]
          (if (contains? (:profile scope) :siblings)
            for-node
            ;; contract: the fragment is the SOLE child of its own element
            {:op :el :id (next-id!) :tag :ul :attr nil :children [for-node]}))
        ;; no list in scope: keep the subtree, rendered once, unkeyed
        (norm (:item raw) scope next-id!)))))

(defn normalize
  "Raw generated tree → valid program with unique node ids (preorder).

   By default the program honours the documented ifor-each contract
   (docs/api-reference.md): every item root carries `:key`, and every
   fragment is the sole child of its own element. `profile` (a set) changes
   that: `:unkeyed` lets the generator decide whether an item root has
   `:key` and `:siblings` lets a fragment sit among sibling nodes (both
   OUTSIDE the contract); `:no-await` drops every deferred await, to fuzz
   past a known await-related defect."
  ([raw] (normalize raw #{}))
  ([raw profile]
   (let [counter (volatile! 0)
         next-id! #(vswap! counter inc)
         root (norm (if (= :spin (:op raw)) raw {:op :spin :tracks [] :body raw})
                    {:avail #{} :davail #{} :item? false :profile (set profile)}
                    next-id!)]
     (update root :body ensure-el next-id!))))

(defn deferreds-used [program]
  (into #{} (keep #(when (= :spin (:op %)) (:dfr %)))
        (tree-seq map? #(remove nil? (concat (:children %) [(:body %) (:then %) (:else %) (:item %)]))
                  program)))

(defn for-guards
  "for-node id → the conditions its rendered items depend on staying put:
   `:ifs` — signals whose `:b` gates an ancestor `:if`; `:fors` — the list
   signals of enclosing ifor-each's, outermost first (paired with the item
   key path the item is rendered under); `:sig` — its own list signal."
  [program]
  (let [acc (volatile! {})]
    ((fn walk [node {:keys [ifs fors] :as g}]
       (when node
         (case (:op node)
           :spin (walk (:body node) g)
           :el (doseq [c (:children node)] (walk c g))
           :if (let [g' (update g :ifs conj (:sig node))]
                 (walk (:then node) g') (walk (:else node) g'))
           :for (do (vswap! acc assoc (:id node) (assoc g :sig (:sig node)))
                    (walk (:item node) (update g :fors conj (:sig node))))
           :text nil)))
     program {:ifs [] :fors []})
    @acc))

;; =============================================================================
;; Reference model of the op sequence
;; =============================================================================

(defn- clamp-pos [pos n] (if (zero? n) 0 (mod pos n)))

(defn- vremove [v i] (into (subvec v 0 i) (subvec v (inc i))))
(defn- vinsert [v i x] (into (conj (subvec v 0 i) x) (subvec v i)))

(defn apply-op
  "Model: apply one op to `{:vals [..] :delivered {d v}}`. Also returns what
   the op DISTURBED, for the key-identity oracle: flipped `:b` signals and
   removed `[sig key]` memberships."
  [{:keys [vals delivered] :as state} [kind s a b c]]
  (case kind
    :flip [(update-in state [:vals s :b] not) {:flipped #{s}}]
    :set-n [(assoc-in state [:vals s :n] a) {}]
    :ins (let [xs (get-in vals [s :xs])
               id a
               at (if (some #(= id (:id %)) xs) nil (mod b (inc (count xs))))]
           (if at
             [(assoc-in state [:vals s :xs] (vinsert xs at {:id id :v c})) {}]
             [(assoc-in state [:vals s :xs]
                        (mapv #(if (= id (:id %)) (assoc % :v c) %) xs)) {}]))
    :del (let [xs (get-in vals [s :xs])]
           (if (empty? xs)
             [state {}]
             (let [i (clamp-pos a (count xs))]
               [(assoc-in state [:vals s :xs] (vremove xs i))
                {:removed #{[s (:id (nth xs i))]}}])))
    :move (let [xs (get-in vals [s :xs])]
            (if (empty? xs)
              [state {}]
              (let [from (clamp-pos a (count xs))
                    to (clamp-pos b (count xs))
                    x (nth xs from)]
                [(assoc-in state [:vals s :xs] (vinsert (vremove xs from) to x)) {}])))
    :upd (let [xs (get-in vals [s :xs])]
           (if (empty? xs)
             [state {}]
             [(assoc-in state [:vals s :xs (clamp-pos a (count xs)) :v] b) {}]))
    :deliver (if (contains? delivered s)
               [state {}]
               [(assoc-in state [:delivered s] a) {}])
    (:settle :tick) [state {}]))

;; =============================================================================
;; Interpreter
;; =============================================================================

#?(:clj
   (defmacro await-if
     "Inside a spin body: await `x` if it evaluated to a spin, else use it."
     [x]
     `(let [x# ~x]
        (if (instance? org.replikativ.spindel.spin.core.Spin x#)
          (await x#)
          x#))))

(defn- spin? [x] (instance? org.replikativ.spindel.spin.core.Spin x))

(defn- loc [id] {:file "differential-fuzz" :line id :column 0})

(defn async?
  "Can rendering `node` produce a spin? Static over-approximation: an
   ifor-each with an async template over an EMPTY list returns a plain
   fragment, which `await-if` passes through."
  [node]
  (case (:op node)
    (:spin) true
    :el (boolean (some async? (:children node)))
    :if (or (async? (:then node)) (some-> (:else node) async?) false)
    :for (async? (:item node))
    :text false))

(defn fk
  "The `data-fk` stamp of an item root: for-node id + the key path."
  [for-id kpath]
  (str/join "|" (cons for-id kpath)))

(defn parse-fk [s]
  (let [[for-id & kpath] (str/split s #"\|")]
    {:for-id #?(:clj (Long/parseLong for-id) :cljs (js/parseInt for-id 10))
     :kpath (mapv #?(:clj #(Long/parseLong %) :cljs #(js/parseInt % 10)) kpath)}))

(defn- attrs-of [node env]
  (let [[kind s] (:attr node)
        base {:class (str "n" (:id node))}]
    (cond-> base
      (= kind :sig) (assoc :data-n (str (get-in env [:vals s :n]))
                           :title (when (get-in env [:vals s :b]) "on"))
      (= kind :item) (assoc :data-v (str (get-in env [:item :v])))
      (:item-root? node) (assoc :data-fk (fk (:for-id env) (:kpath env)))
      (and (:item-root? node) (:key? node)) (assoc :key (get-in env [:item :id]))
      ;; the harness's mount-ref probe, ONE fn for every element so the vnode
      ;; stays equal across renders; not printed by `->code`
      (:ref env) (assoc :ref (:ref env)))))

(declare render)

(defn- eff-addr [my-addr attrs]
  (if-let [k (:key attrs)] (addr/keyed-child-address my-addr k) my-addr))

(defn- el-sync
  "What an `el/<tag>` macro expands to, as a function of a synthetic call
   site. Children are evaluated under the element's address, one slot each."
  [loc tag attrs thunks]
  (let [my-addr (addr/current-element-address loc)]
    (addr/with-parent-addr-fn
      (eff-addr my-addr attrs)
      (fn []
        (el/build-element tag my-addr attrs
                          (vec (map-indexed (fn [i t] (addr/with-slot-fn i t)) thunks)))))))

(defn- el-async
  "The same element when a child may be a spin: built inside a spin, each
   slot awaiting its child — the await-inside-element-build shape. One branch
   per arity because the await must be lexical (Rule 2)."
  [loc tag attrs thunks]
  (spin
   (let [my-addr (addr/current-element-address loc)]
     (addr/with-parent-addr (eff-addr my-addr attrs)
       (case (count thunks)
         0 (el/build-element tag my-addr attrs [])
         1 (let [c0 (addr/with-slot 0 (await-if ((nth thunks 0))))]
             (el/build-element tag my-addr attrs [c0]))
         2 (let [c0 (addr/with-slot 0 (await-if ((nth thunks 0))))
                 c1 (addr/with-slot 1 (await-if ((nth thunks 1))))]
             (el/build-element tag my-addr attrs [c0 c1]))
         3 (let [c0 (addr/with-slot 0 (await-if ((nth thunks 0))))
                 c1 (addr/with-slot 1 (await-if ((nth thunks 1))))
                 c2 (addr/with-slot 2 (await-if ((nth thunks 2))))]
             (el/build-element tag my-addr attrs [c0 c1 c2])))))))

(defn- spin-node
  "A nested spin: tracks at the TOP, then an optional await, then the body.
   One branch per shape so each `track`/`await` is lexical."
  [{:keys [tracks dfr body]} env]
  (let [sigs (:sigs env)
        [i0 i1] tracks
        d (when dfr (nth (:dfrs env) dfr))
        with-vals (fn [m] (update env :vals merge m))
        with-d (fn [e v] (assoc-in e [:dvals dfr] v))]
    (case [(count tracks) (some? dfr)]
      [0 false] (spin (await-if (render body env)))
      [0 true] (spin (let [dv (await d)]
                       (await-if (render body (with-d env dv)))))
      [1 false] (spin (let [{v0 :new} (track (nth sigs i0))]
                        (await-if (render body (with-vals {i0 v0})))))
      [1 true] (spin (let [{v0 :new} (track (nth sigs i0))
                           dv (await d)]
                       (await-if (render body (with-d (with-vals {i0 v0}) dv)))))
      [2 false] (spin (let [{v0 :new} (track (nth sigs i0))
                            {v1 :new} (track (nth sigs i1))]
                        (await-if (render body (with-vals {i0 v0 i1 v1})))))
      [2 true] (spin (let [{v0 :new} (track (nth sigs i0))
                           {v1 :new} (track (nth sigs i1))
                           dv (await d)]
                       (await-if (render body (with-d (with-vals {i0 v0 i1 v1}) dv))))))))

(defn render
  "Render a normalized program node under `env`
   (`{:sigs [SignalRef] :dfrs [Deferred] :vals {s v} :dvals {d v}
      :item item :kpath [k ...] :for-id id :ref ref-fn}`; `:ref`, optional,
   becomes every element's `:ref`). Returns a vnode, a text
   string, nil, a KeyedFragment, or a spin resolving to one of those."
  [node env]
  (case (:op node)
    :text (let [[kind s] (:src node)]
            (case kind
              :lit (str "t" (:id node))
              :n (str "n" (get-in env [:vals s :n]))
              :item-v (str "v" (get-in env [:item :v]))
              :item-id (str "k" (get-in env [:item :id]))
              :dval (str "d" (get-in env [:dvals s]))))
    :el (let [attrs (attrs-of node env)
              thunks (mapv (fn [c] #(render c env)) (:children node))]
          (if (async? node)
            (el-async (loc (:id node)) (:tag node) attrs thunks)
            (el-sync (loc (:id node)) (:tag node) attrs thunks)))
    :if (if (get-in env [:vals (:sig node) :b])
          (render (:then node) env)
          (some-> (:else node) (render env)))
    :spin (spin-node node env)
    :for (let [xs (get-in env [:vals (:sig node) :xs])
               tpl (:item node)
               base (select-keys env [:sigs :dfrs :ref])
               kpath (:kpath env [])]
           (foreach/for-each* (loc (:id node)) :id
                              ;; ONLY the item (plus the static key path, a
                              ;; function of the key) reaches the template
                              (fn [item]
                                (render tpl (assoc base
                                                   :vals {} :dvals {}
                                                   :item item
                                                   :for-id (:id node)
                                                   :kpath (conj kpath (:id item)))))
                              xs))))

;; =============================================================================
;; Printer — a shrunk program as the spindel code it stands for
;; =============================================================================

(defn- sym [prefix i] (symbol (str prefix i)))

(defn ->code
  "The program as the spindel source it is equivalent to. Signal `i` is
   `sig<i>`, its tracked value `s<i>`; deferred `d` is `dfr<d>`, its awaited
   value `dv<d>`. Elements show their `:class` (= node id, so DOM diffs in a
   failure report point back here)."
  [node]
  (let [wrap-await (fn [n form] (if (async? n) (list 'await form) form))]
    (case (:op node)
      :text (let [[kind s] (:src node)]
              (case kind
                :lit (str "t" (:id node))
                :n (list 'str "n" (list :n (sym "s" s)))
                :item-v (list 'str "v" '(:v item))
                :item-id (list 'str "k" '(:id item))
                :dval (list 'str "d" (sym "dv" s))))
      :el (let [[kind s] (:attr node)
                attrs (cond-> {:class (str "n" (:id node))}
                        (= kind :sig) (assoc :data-n (list 'str (list :n (sym "s" s)))
                                             :title (list 'when (list :b (sym "s" s)) "on"))
                        (= kind :item) (assoc :data-v '(str (:v item)))
                        (:item-root? node) (assoc :data-fk '<key-path>)
                        (and (:item-root? node) (:key? node)) (assoc :key '(:id item)))]
            (apply list (symbol "el" (name (:tag node))) attrs
                   (map (fn [c] (wrap-await c (->code c))) (:children node))))
      :if (list 'if (list :b (sym "s" (:sig node)))
                (->code (:then node))
                (some-> (:else node) ->code))
      :spin (let [binds (vec (concat
                              (mapcat (fn [s] [{(sym "s" s) :new} (list 'track (sym "sig" s))])
                                      (:tracks node))
                              (when-let [d (:dfr node)]
                                [(sym "dv" d) (list 'await (sym "dfr" d))])))
                  body (wrap-await (:body node) (->code (:body node)))]
              (if (seq binds)
                (list 'spin (list 'let binds body))
                (list 'spin body)))
      :for (list 'ifor-each :id (list :xs (sym "s" (:sig node)))
                 (list 'fn '[item] (->code (:item node)))))))
