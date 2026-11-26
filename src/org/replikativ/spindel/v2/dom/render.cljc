(ns org.replikativ.spindel.v2.dom.render
  "Rendering on engine v2 (phase-d design §3.5, §5; addendum §3.8).

  `render!` observes a root handle and commits its deliveries to a
  container through a discharge. The observe callback does not commit: it
  stores the delivery and posts one flush item to the root's world
  (`send-world!`), and the flush commits the newest delivery the mount
  holds when it runs. So a mount commits at most once per flush, every
  delivery is committed or superseded, and after exhaustion the committed
  tree is the newest delivery. Ordinary observers keep \"each change\";
  only the mount coalesces.

  Every lifecycle step runs under the world's gate: the flush, the
  commit, a stop and a teardown. A mount's host state, never world state:

  - :phase    :pending :committing :mounted :failed :stopped
              :tearing-down :unmounted
  - :request  nil, :stop or :unmount, asked for while the mount runs user
              code (:busy); taken when that code returns
  - :ledger   addr -> {kind {:cleanup c :seq n}}: the successful setups
              whose cleanup has not yet been claimed. A claim dissocs the
              entry, then calls the cleanup, so none runs twice
  - :store    the commit caches (v2.dom.cache), and the discharge with its
              element registry
  - :current  addr -> {kind f}: the :on-commit and :on-commit-deferred
              fns of the committed tree, whether their setup ran, threw or
              is still queued
  - :deferred the queued deferred setups [{:addr :f :el}], in enqueue order
  - :next :posted?  the stored delivery and whether a flush is posted
  - :rev      an atom {:revision n :deferred n :waiters [...]}: the
              committed render revision, bumped once per commit, the count
              of deferred flushes, and their waiters

  Commit effects (addendum §3.8.2-§3.8.6), each (fn [el]) that may return
  a cleanup:
  - `:ref` is the lifetime hook: it runs when its element is created, once
    the commit's DOM writes have landed, post-order; it is read only then.
    If it returns no cleanup, its cleanup is `(f nil)` with the `f` that ran.
  - `:on-commit` runs after the commit's refs, in the walk's post-order. It
    re-runs when the fn committed at its address is not identical to the
    last one: identity, not deps.
  - `:on-commit-deferred` is the same in a later macrotask (the
    discharge's `defer!`), in enqueue order; a replaced entry moves to the
    end. It yields the task first; it promises no paint.
  Cleanups run in passes, each newest first by setup history: one pass per
  removed subtree, in walk order, while it is still attached; then one for
  the hooks that re-run. All cleanups of a commit run before any setup of
  it. A setup or cleanup that throws is reported (:dom/effect-error) and the
  commit goes on; a throwing setup registers no cleanup and is retried only
  for a new fn. Effects run with v2/*world* bound to the mount's world and
  may write its sources; the writes propagate after the item.

  Event handlers (addendum §3.8.9-§3.8.10): the mount registers every
  :on-* handler wrapped so that it runs with v2/*world* bound to the
  mount's world (what `batch` captures); the attr cache keeps the raw fn
  for diffing. After a handler on a controlled element (committed :value or
  :checked) returns, the wrapper restores the element's DOM property to the
  committed attr, but only when the root has settled and the mount has
  committed its newest delivery before the wrapper returns (an inline world
  within the budget); otherwise an expiry token makes the late paths do
  nothing.

  A commit that fails in the walk (a DOM or cache failure) runs no new
  setup, claims the ledger, clears the container and leaves the mount
  :failed; the next delivery mounts from scratch."
  (:require [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.dom.core :as core]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.v2.dom.cache :as cache]
            [org.replikativ.spindel.v2.dom.commit :as commit]
            [clojure.string :as str]
            [replikativ.logging :as log])
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.dom.render])))

;; ---------------------------------------------------------------------------
;; What a mount needs of its discharge besides PDischarge

(defprotocol PMountHost
  (defer! [d f]
    "Runs `f` later, in a macrotask of its own.")
  (clear-container! [d container]
    "Removes every child of `container`.")
  (dom-prop [d el k]
    "The live DOM property `k` (:value, :checked) of `el`.")
  (set-dom-prop! [d el k v]
    "Writes the DOM property `k` of `el`."))

(extend-protocol PMountHost
  #?(:clj Object :cljs default)
  (defer! [_ f]
    #?(:clj (hs/execute! (hs/executor) f)
       :cljs (hs/macrotask! f))
    nil)
  (clear-container! [_ container]
    #?(:clj nil
       :cljs (when container (set! (.-innerHTML container) "")))
    nil)
  (dom-prop [_ el k]
    #?(:clj nil
       :cljs (case k :value (.-value el) :checked (.-checked el))))
  (set-dom-prop! [_ el k v]
    #?(:clj nil
       :cljs (case k :value (set! (.-value el) v) :checked (set! (.-checked el) v)))
    nil))

;; ---------------------------------------------------------------------------
;; The render revision (§5.3): register-or-return and bump-and-take are
;; each one swap on one atom, so no wakeup is lost

(defn- new-rev [] (atom {:revision 0 :deferred 0 :waiters []}))

(defn- on-rev!
  "Calls `(f :ok)` once `(kind @rev)` reaches `n`, at once when it has;
   `(f ::unmounted)` when the mount is torn down first."
  [rev kind n f]
  (let [[old _] (swap-vals! rev (fn [r]
                                  (if (or (::closed r) (>= (get r kind 0) n))
                                    r
                                    (update r :waiters conj [kind n f]))))]
    (cond (::closed old) (f ::unmounted)
          (>= (get old kind 0) n) (f :ok)))
  nil)

(defn- bump-rev! [rev kind]
  (let [due? (fn [r [k n _]] (and (= k kind) (<= n (get r kind))))
        [old new] (swap-vals! rev (fn [r]
                                    (let [r (update r kind (fnil inc 0))]
                                      (assoc r :waiters (filterv #(not (due? r %)) (:waiters r))))))]
    (doseq [[_ _ f :as w] (:waiters old) :when (due? new w)]
      (f :ok))))

(defn- close-rev! [rev]
  (let [[old _] (swap-vals! rev assoc ::closed true :waiters [])]
    (doseq [[_ _ f] (:waiters old)] (f ::unmounted))))

;; ---------------------------------------------------------------------------
;; Reading a mount (tests, tooling)

(defn phase "The mount's lifecycle phase." [state] (:phase @state))
(defn committed "The committed vdom, nil before a commit and after teardown." [state] (:current-vdom @state))
(defn ledger "The ledger: addr -> {kind {:cleanup :seq}}." [state] (:ledger @state))
(defn error "The last error delivery shown, nil after a successful commit." [state] (:error @state))
(defn store "The mount's commit store." [state] (:store @state))
(defn revision "The committed render revision." [state] (:revision @(:rev @state)))
(defn deferred-revision "How many deferred-effect flushes have ended." [state] (:deferred @(:rev @state)))

(defn clean?
  "Whether the mount holds no committed tree, caches or effects."
  [state]
  (let [s @state]
    (and (nil? (:current-vdom s))
         (empty? (:ledger s))
         (empty? (:current s))
         (empty? (:deferred s))
         (cache/store-empty? (:store s)))))

(defn on-revision
  "Calls `(cb :ok)` once the mount's render revision is at least `n` (at
   once when it is), or `(cb ::unmounted)` when it is torn down first. The
   callback runs on the thread that commits, under the world's gate."
  [state n cb]
  (on-rev! (:rev @state) :revision n cb))

(defn on-deferred
  "As `on-revision`, for the count of ended deferred-effect flushes (the
   completion barrier of `:on-commit-deferred`)."
  [state n cb]
  (on-rev! (:rev @state) :deferred n cb))

#?(:clj
   (defn await-revision
     "Blocks until the render revision is at least `n`: :ok, ::unmounted, or
      ::timeout after `timeout-ms`."
     [state n timeout-ms]
     (let [p (promise)]
       (on-revision state n #(deliver p %))
       (deref p timeout-ms ::timeout))))

#?(:clj
   (defn await-deferred
     "Blocks until `n` deferred-effect flushes have ended: :ok, ::unmounted,
      or ::timeout after `timeout-ms`."
     [state n timeout-ms]
     (let [p (promise)]
       (on-deferred state n #(deliver p %))
       (deref p timeout-ms ::timeout))))

;; ---------------------------------------------------------------------------
;; Running user code

(defn- released? [x] (boolean (:spindel/released (ex-data x))))

(defn- run-user!
  "Calls `(f)`, user code of the mount, with v2/*world* bound to the
   mount's world. A throw is reported (:dom/effect-error) and recorded
   under test collection. Returns [true value] or [false nil]."
  [m addr kind f]
  (try [true (binding [v2/*world* (:world @m)] (f))]
       (catch #?(:clj Throwable :cljs :default) t
         (log/error :dom/effect-error {:addr addr :kind kind :error t})
         (disch/record-violation! :effect-error {:addr addr :kind kind :error t})
         [false nil])))

;; ---------------------------------------------------------------------------
;; The ledger

(defn- register! [m addr kind cleanup]
  (swap! m (fn [s] (let [n (inc (:seq s))]
                     (-> s (assoc :seq n) (assoc-in [:ledger addr kind] {:cleanup cleanup :seq n}))))))

(defn- claim!
  "Claims the ledger entry of `addr` `kind`, if it is still there: dissocs
   it, then calls its cleanup."
  [m addr kind]
  (let [[old _] (swap-vals! m (fn [s]
                                (let [es (dissoc (get-in s [:ledger addr]) kind)]
                                  (if (empty? es)
                                    (update s :ledger dissoc addr)
                                    (assoc-in s [:ledger addr] es)))))]
    (when-let [{:keys [cleanup]} (get-in old [:ledger addr kind])]
      (when cleanup (run-user! m addr kind cleanup)))))

(defn- cleanup-pass!
  "One cleanup pass: claims the ledger entries of `addrs` (all when nil),
   newest first."
  [m addrs]
  (let [l (:ledger @m)
        es (for [[a kinds] (if addrs (select-keys l addrs) l)
                 [k {:keys [seq]}] kinds]
             [a k seq])]
    (doseq [[a k] (sort-by #(nth % 2) > es)]
      (claim! m a k))))

(defn- setup!
  "Runs setup `f` of `addr` `kind` on `el` and registers its cleanup if it
   succeeds."
  [m addr kind f el]
  (let [[ok? c] (run-user! m addr kind #(f el))]
    (when ok?
      (register! m addr kind (cond (fn? c) c
                                   (= kind :ref) #(f nil)
                                   :else nil)))))

(defn- unmount-requested? [m] (= :unmount (:request @m)))

(defn- removal-pass!
  "The cleanup pass of a removed subtree with addresses `addrs`, run while
   it is still attached: its queued deferred setups are dropped and its
   committed hooks forgotten, then its entries are claimed newest first."
  [m addrs]
  (let [as (set addrs)]
    (swap! m (fn [s] (-> s
                         (update :deferred (fn [q] (filterv #(not (as (:addr %))) q)))
                         (update :current #(apply dissoc % as)))))
    (cleanup-pass! m as)))

;; ---------------------------------------------------------------------------
;; Mount, update, teardown

(defn ^:no-doc root-identity-changed?
  "Whether the new root is another DOM node than the mounted one (a
   conditional at the top of the root): then the whole tree is replaced."
  [current-vdom new-vdom]
  (boolean
   (when (and current-vdom new-vdom)
     (let [ca (:addr current-vdom) na (:addr new-vdom)]
       (if (and ca na) (not= ca na) (not= (:tag current-vdom) (:tag new-vdom)))))))

(defn- attach! [d container root]
  (when (and container root)
    (if (vector? root)
      (doseq [r root] (disch/append-child! d container r))
      (disch/append-child! d container root))))

(defn- mount-initial! [m v]
  (let [{:keys [discharge container store]} @m]
    (clear-container! discharge container)
    (attach! discharge container (disch/render-initial! discharge v))
    (commit/seed-subtree-caches! store v)))

(defn- mount-update! [m v]
  (let [{:keys [discharge container store current-vdom]} @m]
    (if (root-identity-changed? current-vdom v)
      (do (disch/call-refs-on-unmount! current-vdom)
          (let [root (disch/render-initial! discharge v)]
            (clear-container! discharge container)
            (attach! discharge container root))
          (commit/seed-subtree-caches! store v)
          (commit/retire-dead! discharge store current-vdom v))
      (commit/commit-update! discharge store current-vdom v))))

(defn- unobserve!
  "Withdraws the mount's observation, exactly once (render! may store the
   unobserve fn after a first commit already stopped the mount)."
  [m]
  (let [[old _] (swap-vals! m assoc :unobserved? true :unobserve nil)]
    (when-let [u (:unobserve old)] (u))))

(defn- stop-now! [m]
  (swap! m assoc :phase :stopped :next nil)
  (unobserve! m))

(defn- teardown!
  "Unmounts (§3.5): the phase is :tearing-down before any user code runs,
   so a cleanup that asks for a stop or unmount finds nothing to do."
  [m]
  (when-not (#{:tearing-down :unmounted} (:phase @m))
    (swap! m assoc :phase :tearing-down :next nil :request nil :deferred [] :restore-pending [])
    (try
      (unobserve! m)
      (let [addrs (keys (:ledger @m))]
        (cleanup-pass! m nil)
        (let [{:keys [discharge container store current-vdom]} @m]
          (doseq [a (into (commit/tree-addrs current-vdom) addrs)]
            (disch/remove-element! discharge a))
          (clear-container! discharge container)
          (cache/reset-store! store)))
      (swap! m assoc :ledger {} :current {} :current-vdom nil :root nil)
      (close-rev! (:rev @m))
      (finally (swap! m assoc :phase :unmounted)))))

(defn- request!
  "A stop or unmount (§3.5, addendum §3.8.4), under the gate. While the
   mount runs user code it is held in the request slot (:unmount replaces a
   held :stop, never the reverse); otherwise it runs at once."
  [m kind]
  (let [{:keys [phase busy]} @m]
    (cond
      (#{:tearing-down :unmounted} phase) nil
      busy (swap! m update :request #(if (= % :unmount) :unmount kind))
      (= kind :unmount) (teardown! m)
      (= phase :stopped) nil
      :else (stop-now! m))))

(defn- finish!
  "The end of a commit: takes the request slot."
  [m ok?]
  (let [[old _] (swap-vals! m assoc :busy false :request nil)]
    (case (:request old)
      :unmount (teardown! m)
      :stop (stop-now! m)
      (swap! m assoc :phase (if ok? :mounted :failed)))))

#?(:cljs
   (defn- show-overlay!
     "Dev builds (goog.DEBUG): a visible surface for an error delivery, which
      otherwise freezes the UI at the last frame with one log line."
     [container error]
     (when (and ^boolean js/goog.DEBUG container (.-querySelector container))
       (let [existing (.querySelector container "[data-spindel-render-error]")
             el (or existing (.createElement (.-ownerDocument container) "div"))]
         (set! (.-cssText (.-style el))
               (str "position:fixed;left:8px;right:8px;bottom:8px;z-index:99999;"
                    "background:#3b0d0d;color:#ffb4b4;border:1px solid #a33;"
                    "border-radius:6px;padding:10px 14px;font:12px/1.5 monospace;"
                    "max-height:40vh;overflow:auto;white-space:pre-wrap;"))
         (.setAttribute el "data-spindel-render-error" "true")
         (set! (.-textContent el)
               (str "spindel render error: the UI shows the last committed frame\n"
                    (or (some-> error .-message) error)
                    (when-let [st (some-> error .-stack)] (str "\n\n" st))))
         (when-not existing (.appendChild container el))))))

#?(:cljs
   (defn- clear-overlay! [container]
     (when-let [el (and container (.-querySelector container)
                        (.querySelector container "[data-spindel-render-error]"))]
       (.remove el))))

(defn- show-error! [m e]
  (log/error :render/error {:error e})
  (swap! m assoc :error e)
  #?(:cljs (show-overlay! (:container @m) e)))

(defn- fail!
  "Failure cleanup (§3.5): the walk threw. No new setup has run. The phase
   is still :committing, so a request a cleanup makes is held."
  [m e rendered]
  (log/error :render/commit-failed {:error e})
  (let [addrs (keys (:ledger @m))]
    (cleanup-pass! m nil)
    (let [{:keys [discharge container store current-vdom]} @m]
      (doseq [a (concat (commit/tree-addrs current-vdom) (keys @rendered) addrs)]
        (disch/remove-element! discharge a))
      (clear-container! discharge container)
      (cache/reset-store! store)))
  (swap! m assoc :ledger {} :current {} :deferred [] :current-vdom nil :error e))

(defn- walk-hooks
  "The discharge hooks of one commit: a created element is collected for
   its setups after the walk; a removed subtree gets its cleanup pass now,
   while it is still attached."
  [m ctx]
  {:created (fn [vnode el] (vswap! ctx (fn [c] (-> c
                                                    (update :created conj [vnode el])
                                                    (update :visits conj [vnode el true])))))
   :removed (fn [vnode] (removal-pass! m (commit/tree-addrs vnode)))})

(defn- leave-hook
  "commit/*leave* for one commit: an element reconciled in place is visited
   when the walk leaves it."
  [m ctx]
  (fn [vnode]
    (vswap! ctx update :visits conj
            [vnode (disch/get-element (:discharge @m) (:addr vnode)) false])))

(def ^:private commit-kinds [:on-commit :on-commit-deferred])

(defn- hooks-of [vnode] (into {} (keep (fn [k] (when-let [f (get vnode k)] [k f]))) commit-kinds))

(declare flush-deferred!)

(defn- defer-flush!
  "Schedules the mount's deferred flush, once while one is pending."
  [m]
  (let [[old _] (swap-vals! m assoc :defer-posted? true)]
    (when-not (:defer-posted? old)
      (let [{:keys [discharge world]} old]
        (defer! discharge
          (fn []
            (try (v2/host! world #(flush-deferred! m))
                 (catch #?(:clj Throwable :cljs :default) t
                   (when-not (released? t) (log/error :render/deferred-refused {:error t}))))))))))

(defn- run-effects!
  "Steps 2-5 of a commit that succeeded (addendum §3.8.3): the re-run pass,
   the refs of the created elements, the on-commit setups, and the deferred
   queue. An unmount requested by a cleanup lets the pass finish and stops
   every later setup."
  [m {:keys [created visits]}]
  (let [created-addrs (into #{} (keep (comp :addr first)) created)
        visits (filterv (fn [[vn _ new?]] (and (:addr vn) (or new? (not (created-addrs (:addr vn)))))) visits)
        cur (:current @m)
        rerun (for [[vn _ new?] visits :when (not new?)
                    k commit-kinds
                    :when (not (identical? (get vn k) (get-in cur [(:addr vn) k])))]
                [(:addr vn) k])
        rerun-set (set rerun)
        runs? (fn [[vn _ new?] k] (and (get vn k) (or new? (rerun-set [(:addr vn) k]))))]
    ;; every committed hook is recorded, whether its setup runs, throws or waits
    (swap! m update :current
           (fn [c] (reduce (fn [c [vn]] (let [hs (hooks-of vn)]
                                          (if (seq hs) (assoc c (:addr vn) hs) (dissoc c (:addr vn)))))
                           c visits)))
    ;; 2. the re-run pass: queued deferred setups that never ran are dropped
    (swap! m update :deferred (fn [q] (filterv #(not (rerun-set [(:addr %) :on-commit-deferred])) q)))
    (let [l (:ledger @m)]
      (doseq [[a k] (sort-by #(get-in l (conj % :seq)) > (filter #(get-in l %) rerun))]
        (claim! m a k)))
    ;; 3. the refs of the created elements, in creation order
    (doseq [[vnode el] created
            :let [f (:ref vnode)]
            :when f
            :while (not (unmount-requested? m))]
      (setup! m (:addr vnode) :ref f el))
    ;; 4. on-commit, post-order of the walk
    (doseq [[vn el :as v] visits
            :when (runs? v :on-commit)
            :while (not (unmount-requested? m))]
      (setup! m (:addr vn) :on-commit (:on-commit vn) el))
    ;; 5. on-commit-deferred: queued, a replaced entry at the end
    (when-not (unmount-requested? m)
      (let [es (for [[vn el :as v] visits :when (runs? v :on-commit-deferred)]
                 {:addr (:addr vn) :f (:on-commit-deferred vn) :el el})]
        (when (seq es)
          (let [as (set (map :addr es))]
            (swap! m update :deferred (fn [q] (into (filterv #(not (as (:addr %))) q) es))))
          (defer-flush! m))))))

(defn- commit! [m v]
  (let [initial? (contains? #{:pending :failed} (:phase @m))
        rendered (atom {})
        ctx (volatile! {:created [] :visits []})]
    (swap! m assoc :phase :committing :busy true)
    (if (try
          (binding [disch/*rendered-addrs* rendered
                    disch/*mount-hooks* (walk-hooks m ctx)
                    commit/*leave* (leave-hook m ctx)]
            (when-let [dead (if initial? (mount-initial! m v) (mount-update! m v))]
              (swap! m update :current #(apply dissoc % dead))))
          true
          (catch #?(:clj Throwable :cljs :default) e
            (fail! m e rendered)
            false))
      (do (swap! m assoc :current-vdom v :error nil)
          #?(:cljs (clear-overlay! (:container @m)))
          (run-effects! m @ctx)
          (bump-rev! (:rev @m) :revision)
          (finish! m true))
      (do #?(:cljs (show-overlay! (:container @m) (:error @m)))
          (finish! m false)))))

;; ---------------------------------------------------------------------------
;; Controlled-input restore, the synchronous subset (addendum §3.8.10)

(defn- calling-thread [] #?(:clj (Thread/currentThread) :cljs true))
(defn- on-thread? [t] #?(:clj (identical? t (Thread/currentThread)) :cljs true))

(defn- live? [[_ _ _ token owner]]
  (and (= :live @token) (on-thread? owner)))

(defn- restore!
  "Restores the DOM property of entry [a el k token owner] to the committed
   attr, when the token is live (its wrapper has not returned), the mount is
   :mounted and the registry still maps `a` to `el`."
  [m [a el k token :as entry]]
  (let [{:keys [phase discharge store]} @m]
    (when (and (live? entry) (= :mounted phase) (identical? el (disch/get-element discharge a)))
      (let [v (get (cache/get-attr-cache store a) k)
            want (if (= k :value) (str (if (nil? v) "" v)) (boolean v))]
        (when (not= want (dom-prop discharge el k))
          (set-dom-prop! discharge el k want))
        (reset! token :done)))))

(defn- restore-pending!
  "After a flush: the restores the wait's callback left for it."
  [m]
  (let [[old _] (swap-vals! m assoc :restore-pending [])]
    (doseq [entry (:restore-pending old)] (restore! m entry))))

(defn- settled-cb
  "The wait's callback, under the gate: restores at once, or after the
   flush of the delivery the mount still holds."
  [m entry]
  (fn [_ _]
    (when (live? entry)
      (if (some? (:next @m))
        (swap! m update :restore-pending conj entry)
        (restore! m entry)))))

(defn- event-target [e el]
  #?(:clj (if (map? e) (get e :target el) el)
     :cljs (or (some-> e .-target) el)))

(defn- restore-controlled!
  "After a handler returned: if its event targeted a controlled element of
   the mount, waits for the root and restores the element, synchronously
   only (token :live -> :done); a wait not done before this returns is
   expired and withdrawn."
  [m e el]
  (let [{:keys [phase discharge store root]} @m
        target (event-target e el)
        a (some-> (:el->addr discharge) (hs/mget target))
        attrs (when a (cache/get-attr-cache store a))
        k (cond (contains? attrs :value) :value (contains? attrs :checked) :checked)]
    (when (and k root (= :mounted phase))
      (let [token (atom :live)
            withdraw (v2/value-async root (settled-cb m [a target k token (calling-thread)]))]
        (when (compare-and-set! token :live :expired)
          (withdraw))))))

(defn- handler? [k v]
  (and (fn? v) (keyword? k) (str/starts-with? (name k) "on")))

(defn- wrap-handler
  "A handler as the mount registers it: run with the mount's world bound,
   then the controlled-input restore."
  [m el f]
  (fn [e]
    (let [r (binding [v2/*world* (:world @m)] (f e))]
      (restore-controlled! m e el)
      r)))

(deftype MountDischarge [d m el->addr]
  disch/PDischarge
  (create-element! [_ vnode] (disch/create-element! d vnode))
  (create-text! [_ text] (disch/create-text! d text))
  (set-attribute! [_ el k v] (disch/set-attribute! d el k (if (handler? k v) (wrap-handler m el v) v)))
  (remove-attribute! [_ el k] (disch/remove-attribute! d el k))
  (append-child! [_ p c] (disch/append-child! d p c))
  (insert-child! [_ p c i] (disch/insert-child! d p c i))
  (remove-child! [_ p i] (disch/remove-child! d p i))
  (replace-child! [_ p c i] (disch/replace-child! d p c i))
  (move-child! [_ p from to] (disch/move-child! d p from to))
  (child-index-of [_ p c] (disch/child-index-of d p c))
  (set-text-content! [_ el text] (disch/set-text-content! d el text))
  (get-element [_ addr] (disch/get-element d addr))
  (set-element! [_ addr el]
    (when-let [old (disch/get-element d addr)] (hs/mdel! el->addr old))
    (hs/mput! el->addr el addr)
    (disch/set-element! d addr el))
  (remove-element! [_ addr]
    (when-let [old (disch/get-element d addr)] (hs/mdel! el->addr old))
    (disch/remove-element! d addr))
  (remove-children-range! [_ p start n] (disch/remove-children-range! d p start n))
  (insert-children! [_ p cs start] (disch/insert-children! d p cs start))

  PMountHost
  (defer! [_ f] (defer! d f))
  (clear-container! [_ container] (clear-container! d container))
  (dom-prop [_ el k] (dom-prop d el k))
  (set-dom-prop! [_ el k v] (set-dom-prop! d el k v))

  #?(:clj clojure.lang.ILookup :cljs ILookup)
  (#?(:clj valAt :cljs -lookup) [_ k] (when (= k :el->addr) el->addr))
  (#?(:clj valAt :cljs -lookup) [_ k nf] (if (= k :el->addr) el->addr nf)))

(defn- mount-discharge
  "The mount's view of `d`: handlers wrapped, and an element -> address
   index next to the registry."
  [d m]
  (->MountDischarge d m #?(:clj (java.util.Collections/synchronizedMap (java.util.IdentityHashMap.))
                           :cljs (js/Map.))))

;; ---------------------------------------------------------------------------
;; The deferred flush (addendum §3.8.2-§3.8.4)

(defn- finish-deferred!
  "The deferred flush's epilogue, run unconditionally: takes the request
   slot, so no request is left behind."
  [m]
  (let [[old _] (swap-vals! m assoc :busy false :request nil)]
    (case (:request old)
      :unmount (teardown! m)
      :stop (when-not (= :stopped (:phase @m)) (stop-now! m))
      nil)))

(defn- flush-deferred!
  "The mount's deferred flush, a host item of its world: runs the queued
   deferred setups in enqueue order. After :stop! it still runs (its frame
   is on screen); after a teardown the queue is empty. A request a setup
   makes is held until that setup returns; an unmount stops the rest."
  [m]
  (swap! m assoc :defer-posted? false)
  (let [{:keys [phase busy deferred]} @m]
    (cond
      ;; a commit's effect ran the deferred work synchronously: after it
      busy (when (seq deferred) (defer-flush! m))
      (contains? #{:mounted :stopped} phase)
      (do (swap! m assoc :busy true)
          (try
            (loop []
              (when-not (unmount-requested? m)
                (let [[old _] (swap-vals! m update :deferred #(if (seq %) (subvec % 1) %))]
                  (when-let [{:keys [addr f el]} (first (:deferred old))]
                    (setup! m addr :on-commit-deferred f el)
                    (recur)))))
            (finally (finish-deferred! m))))))
  (bump-rev! (:rev @m) :deferred))

;; ---------------------------------------------------------------------------
;; Deliveries and the flush (addendum §3.8.8)

(defn- ignores? [phase] (contains? #{:stopped :tearing-down :unmounted} phase))

(defn- flush!
  "The mount's flush, a host item of its world: commits the newest stored
   delivery, or shows an error delivery."
  [m]
  (let [[old _] (swap-vals! m assoc :posted? false :next nil)]
    (when-let [[v err?] (:next old)]
      (when-not (ignores? (:phase old))
        (binding [v2/*world* (:world old)]
          (cond err? (show-error! m v)
                (some? v) (commit! m v)))))
    (restore-pending! m)))

(defn- deliver!
  "The observe callback, under the gate: stores the delivery and posts one
   flush unless one is posted."
  [m v err?]
  (cond
    (and err? (released? v)) (do (swap! m assoc :next nil) (request! m :stop))
    (ignores? (:phase @m)) nil
    :else
    (let [[old _] (swap-vals! m assoc :next [v err?] :posted? true)]
      (when-not (:posted? old)
        (try (v2/send-world! (:world old) #(flush! m))
             (catch #?(:clj Throwable :cljs :default) t
               (when-not (released? t) (log/error :render/flush-refused {:error t}))
               (swap! m assoc :next nil :posted? false)
               (request! m :stop)))))))

(defn- in-world!
  "Runs `(f)` as a host item of the mount's world: at once inside it, the
   JVM caller waits otherwise. A released world takes no host item; its
   mount is stopped, so the request runs on the caller's thread."
  [m f]
  (let [w (:world @m)]
    (try #?(:clj (v2/host-call! w f) :cljs (v2/host! w f))
         (catch #?(:clj Throwable :cljs :default) t
           (if (released? t) (f) (throw t))))
    nil))

(defn render!
  "Renders root handle `h` (a computation or source whose value is a vnode)
   into `container` through `discharge`, in the world `(:world opts)` or
   `(v2/current-world)`. Returns {:state s :stop! f :unmount! g}.

   `:stop!` ends the updates and keeps the DOM; `:unmount!` tears the mount
   down: the cleanups run, the container is cleared. Both run under the
   world's gate; asked for while the mount runs user code (a ref, a
   cleanup), they wait until that code returns."
  ([container h discharge] (render! container h discharge {}))
  ([container h discharge {:keys [world]}]
   (let [w (or world (v2/current-world)
               (throw (ex-info "render!: no world (bind v2/*world* or pass :world)" {})))
         m (atom {:world w :root h :container container
                  :phase :pending :request nil :busy false
                  :current-vdom nil :store (cache/new-store)
                  :ledger {} :current {} :deferred [] :seq 0
                  :next nil :posted? false :restore-pending []
                  :rev (new-rev)})
         _ (swap! m assoc :discharge (mount-discharge discharge m))
         u (binding [v2/*world* w] (v2/observe! h (fn [v err?] (deliver! m v err?))))
         ;; the fn holds the root's row (through its edge): dropped once used
         [old _] (swap-vals! m #(if (:unobserved? %) % (assoc % :unobserve u)))]
     (when (:unobserved? old) (u))
     {:state m
      :stop! (fn [] (in-world! m #(request! m :stop)))
      :unmount! (fn [] (in-world! m #(request! m :unmount)))})))

#?(:clj
   (defmacro batch
     "Runs `body` as one host item of the world current at the call, with
      that world bound inside: its writes nest, so nothing propagates between
      them; observation and rendering follow through normal processing. Not
      one turn or one commit: on an inline world within the budget, with no
      asynchronous dependency, two writes give one commit before `batch`
      returns. Inside a world's item (an effect, another batch) it runs at
      once. On a world that is not inline it returns nil at once and the body
      runs later: do event-object work (preventDefault, reading .-value)
      before it. If the body throws, its earlier writes stay."
     [& body]
     `(let [w# (v2/current-world)]
        (v2/host! w# (fn [] (binding [v2/*world* w#] ~@body))))))
