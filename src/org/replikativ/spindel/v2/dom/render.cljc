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
  - :next :posted?  the stored delivery and whether a flush is posted
  - :rev      an atom {:revision n :waiters [...]}: the committed render
              revision, bumped once per commit, and its waiters

  A `:ref` (fn [el]) runs once its element is created and the commit's DOM
  writes have landed, post-order. It may return a cleanup; if it returns
  none, its cleanup is `(f nil)` with the `f` that ran. A setup or cleanup
  that throws is reported (:dom/effect-error) and the commit goes on; a
  throwing setup registers no cleanup.

  A commit that fails in the walk (a DOM or cache failure) runs no new
  setup, claims the ledger, clears the container and leaves the mount
  :failed; the next delivery mounts from scratch."
  (:require [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.dom.core :as core]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.v2.dom.cache :as cache]
            [org.replikativ.spindel.v2.dom.commit :as commit]
            [replikativ.logging :as log]))

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

(defn- new-rev [] (atom {:revision 0 :waiters []}))

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

(defn clean?
  "Whether the mount holds no committed tree, caches or effects."
  [state]
  (let [s @state]
    (and (nil? (:current-vdom s))
         (empty? (:ledger s))
         (cache/store-empty? (:store s)))))

(defn on-revision
  "Calls `(cb :ok)` once the mount's render revision is at least `n` (at
   once when it is), or `(cb ::unmounted)` when it is torn down first. The
   callback runs on the thread that commits, under the world's gate."
  [state n cb]
  (on-rev! (:rev @state) :revision n cb))

#?(:clj
   (defn await-revision
     "Blocks until the render revision is at least `n`: :ok, ::unmounted, or
      ::timeout after `timeout-ms`."
     [state n timeout-ms]
     (let [p (promise)]
       (on-revision state n #(deliver p %))
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
    (swap! m assoc :phase :tearing-down :next nil :request nil)
    (try
      (unobserve! m)
      (let [addrs (keys (:ledger @m))]
        (cleanup-pass! m nil)
        (let [{:keys [discharge container store current-vdom]} @m]
          (doseq [a (into (commit/tree-addrs current-vdom) addrs)]
            (disch/remove-element! discharge a))
          (clear-container! discharge container)
          (cache/reset-store! store)))
      (swap! m assoc :ledger {} :current-vdom nil :root nil)
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
  (swap! m assoc :ledger {} :current-vdom nil :error e))

(defn- walk-hooks
  "The discharge hooks of one commit: created elements are collected for
   their setups after the walk; a removed subtree gets its cleanup pass now,
   while it is still attached."
  [m ctx]
  {:created (fn [vnode el] (vswap! ctx update :created conj [vnode el]))
   :removed (fn [vnode] (cleanup-pass! m (commit/tree-addrs vnode)))})

(defn- run-setups!
  "The setups of a commit that succeeded, in order, until an unmount is
   requested: the refs of the created elements."
  [m {:keys [created]}]
  (doseq [[vnode el] created
          :let [f (:ref vnode)]
          :when f
          :while (not (unmount-requested? m))]
    (setup! m (:addr vnode) :ref f el)))

(defn- commit! [m v]
  (let [initial? (contains? #{:pending :failed} (:phase @m))
        rendered (atom {})
        ctx (volatile! {:created []})]
    (swap! m assoc :phase :committing :busy true)
    (if (try
          (binding [disch/*rendered-addrs* rendered
                    disch/*mount-hooks* (walk-hooks m ctx)]
            (if initial? (mount-initial! m v) (mount-update! m v)))
          true
          (catch #?(:clj Throwable :cljs :default) e
            (fail! m e rendered)
            false))
      (do (swap! m assoc :current-vdom v :error nil)
          #?(:cljs (clear-overlay! (:container @m)))
          (run-setups! m @ctx)
          (bump-rev! (:rev @m) :revision)
          (finish! m true))
      (do #?(:cljs (show-overlay! (:container @m) (:error @m)))
          (finish! m false)))))

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
                (some? v) (commit! m v)))))))

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
         m (atom {:world w :root h :container container :discharge discharge
                  :phase :pending :request nil :busy false
                  :current-vdom nil :store (cache/new-store)
                  :ledger {} :seq 0
                  :next nil :posted? false
                  :rev (new-rev)})
         u (binding [v2/*world* w] (v2/observe! h (fn [v err?] (deliver! m v err?))))
         ;; the fn holds the root's row (through its edge): dropped once used
         [old _] (swap-vals! m #(if (:unobserved? %) % (assoc % :unobserve u)))]
     (when (:unobserved? old) (u))
     {:state m
      :stop! (fn [] (in-world! m #(request! m :stop)))
      :unmount! (fn [] (in-world! m #(request! m :unmount)))})))
