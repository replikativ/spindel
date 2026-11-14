(ns org.replikativ.spindel.v2.savepoint
  "Savepoint sessions on engine v2 (§8.2): the old session API over
   publications.

   A *savepoint* `sp` is a map
     {:savepoint/world w :savepoint/site s :savepoint/payload p
      :savepoint/address a :savepoint/seq n}
   naming one publication in one world. It is *pending* while it can be
   continued: its own publication is armed, or `w` is an instance of it that
   has not been activated yet.

     (resume sp v)   continue sp's world with v
     (fork sp)       sp in a new world, an instance of the publication
     (copy sp k)     sp only in k new worlds, never in its own (S8)
     (abandon sp)    unwind the computation suspended at sp

   A publication keeps its basis after it is resumed, so an anchor (the state
   at a site, to replay from) is the savepoint itself; `dispose` drops it.

   A *session* owns the worlds it makes: their root is the session's root
   world, so they outlive the worlds they were forked from. Handlers run as
   host code after the publishing commit (H3, `off-world`), not inside the
   effect.

   Addresses: `(savepoint site payload)` in a task body publishes at
   `[frame key]` (§8.2 addresses), or at `(:id opts)` with
   `(savepoint site payload opts)`."
  (:require [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.engine.hash :as h]))

(defn off-world
  "`f` as a callback that runs as host code: called inside a world (a slice
   or a callback under its gate), it runs `(f x)` later on the host executor,
   where it may call into any world (B7); otherwise at once. CPS operations
   of this layer and of `v2.trace` deliver through it."
  [f]
  (fn [x]
    (if (v2/cw)
      (hs/execute! (hs/executor) #(f x))
      (f x))))

(def any-site
  "Handler-table key matching every site that has no entry of its own."
  :default)

(def result-site
  "Site of the terminal event of a computation that returned; its payload is
   the result."
  :savepoint/result)

(def error-site
  "Site of the terminal event of a computation that threw; its payload is the
   error."
  :savepoint/error)

(def abandoned-site
  "Site of the terminal event of a computation that was abandoned or
   cancelled; its payload is the cancellation."
  :savepoint/abandoned)

;; ---------------------------------------------------------------------------
;; The effect: a savepoint with an address

(defn savepoint
  "`(savepoint site payload)` / `(savepoint site payload {:id address})` in a
   task body: publishes to the world's handler for `site` and evaluates to
   what it is resumed with; to `payload` when no handler is installed."
  [& _]
  (throw (ex-info "savepoint outside a body" {})))

(defn address
  "The address of an effect occurrence: an explicit `id`, else `[frame key]`
   from the effect's context (§8.2 addresses)."
  [id {:keys [frame key]}]
  (or id [frame key]))

(defn publish-op
  "The op a registered effect's handler returns to publish a savepoint at
   `address` (`v2/register-effect!`)."
  [site payload address]
  [:savepoint site {::payload payload ::address address}])

(v2/register-effect!
 `savepoint
 (fn [[site payload opts] ctx]
   (publish-op site payload (address (:id opts) ctx))))

(defn- unwrap
  "The payload a handler or a no-handler run sees."
  [p]
  (if (and (map? p) (contains? p ::payload)) (::payload p) p))

;; ---------------------------------------------------------------------------
;; Savepoints over publications

(defn- sp-of [session w pub seq]
  (let [p (:payload pub)]
    {:savepoint/world w
     :savepoint/site (:site pub)
     :savepoint/payload (unwrap p)
     :savepoint/address (when (map? p) (::address p))
     :savepoint/seq seq
     ::seed (v2/get-in-world w [:savepoint/seed])
     ::pub pub
     ::session session}))

(defn- instance-sp? [sp] (some? (::instance sp)))

(defn pending?
  "True while `sp` may still be resumed, forked, copied or abandoned."
  [sp]
  (if (instance-sp? sp)
    (= :unborn @(::instance sp))
    (= :pending @(:state (::pub sp)))))

(defn- live-pub
  "The publication of a pending `sp`, else throws."
  [sp op]
  (when-not (pending? sp)
    (throw (ex-info (str "Cannot " (name op) " a savepoint that is not pending")
                    {:type ::not-pending :operation op :savepoint/address (:savepoint/address sp)})))
  (::pub sp))

;; ---------------------------------------------------------------------------
;; Seeds

(defn derive-seed
  "A child's seed from its parent's, the site address and the fork index, so
   reruns agree."
  [parent-seed address index]
  (h/content-hash [:savepoint/seed parent-seed address index]))

(defn seed
  "The random seed of world `w`, or nil outside a session."
  [w]
  (v2/get-in-world w [:savepoint/seed]))

;; ---------------------------------------------------------------------------
;; Sessions

(defrecord Session [root task worlds fork-indices closing? waiting])

(defn session
  "The session owning world `w`, or nil."
  [w]
  (v2/get-in-world w [:savepoint/session]))

(defn- dispatch-terminal! [w site payload]
  (when-let [h (get (v2/get-in-world w [:savepoint/handlers]) site)]
    (try (h {:savepoint/site site :savepoint/payload payload :savepoint/world w :savepoint/terminal? true})
         (catch #?(:clj Throwable :cljs :default) _ nil))))

(defn- watch-end!
  "Delivers the terminal event of the session's task as `w` sees it, once,
   as host code (`off-world`)."
  [s w]
  (let [t (v2/in-world w (:task s))
        done (atom false)
        f (off-world (fn [[v err?]]
                       (when (compare-and-set! done false true)
                         (dispatch-terminal! w
                                             (cond (not err?) result-site
                                                   (v2/cancelled? v) abandoned-site
                                                   :else error-site)
                                             v))))]
    (v2/observe! t (fn [v err?] (f [v err?])))))

(defn- publication-handler
  "The engine handler of world `w`: wraps the publication into a savepoint
   and calls the user's handler for its site as host code (`off-world`): a
   handler may fork, copy and resume, and read or write any world, while
   the run waits at its savepoint."
  [s]
  (fn [pub]
    (let [w (:world pub)
          site (:site pub)
          hs (v2/get-in-world w [:savepoint/handlers])
          h (or (get hs site) (get hs :default))
          seq (:savepoint/seq (v2/update-in-world! w [:savepoint/seq] (fnil inc 0)))]
      (if h
        ((off-world h) (sp-of s w pub seq))
        ;; Law 1: no handler, no savepoint: continue with the payload
        (v2/resume! pub (unwrap (:payload pub)))))))

(defn- merge-handlers [cur table]
  (reduce-kv (fn [m site f] (if f (assoc m site f) (dissoc m site))) (or cur {}) table))

(defn install-handlers!
  "Merges `table` ({site (fn [sp])}) into `w`'s handlers; a nil handler
   removes its entry. Forks inherit them."
  [w table]
  (v2/update-in-world! w [:savepoint/handlers] merge-handlers table)
  w)

(defn handled?
  "Whether `w` has a handler for `site`, its own or `:default`."
  [w site]
  (let [hs (v2/get-in-world w [:savepoint/handlers])]
    (some? (or (get hs site) (get hs :default)))))

(defn open!
  "Opens a session rooted at `w`. Options: `:handlers` {site handler},
   `:seed` (default: a random uuid). The caller must `close!` it."
  ([w] (open! w nil))
  ([w {:keys [handlers seed]}]
   (when (session w)
     (throw (ex-info "World already belongs to a savepoint session" {:type ::session-exists})))
   (let [s (->Session w (atom nil) (atom #{}) (atom {}) (atom false) (atom []))]
     (v2/assoc-in-world! w [:savepoint/session] s)
     (v2/assoc-in-world! w [:savepoint/seed] (or seed (random-uuid)))
     (install-handlers! w (or handlers {}))
     ;; every site reaches the session's dispatcher; Law 1 inside it
     (v2/install-handlers! w {:default (publication-handler s)})
     s)))

(defn start!
  "Runs `(f)` (which creates a task) in the session's root world. Its
   savepoints reach the handlers; its end reaches a terminal site, in every
   world that continues it. Returns the task handle."
  [s f]
  (when-not (compare-and-set! (:task s) nil ::starting)
    (throw (ex-info "A savepoint session runs one computation" {:type ::already-started})))
  (let [t (binding [v2/*world* (:root s)] (f))]
    (reset! (:task s) t)
    (watch-end! (assoc s :task t) (:root s))
    ;; worlds that started continuing it while it was being created
    (doseq [w (first (reset-vals! (:waiting s) nil))] (watch-end! (assoc s :task t) w))
    t))

(defn- watch-world-end!
  "Observes the end of the session's computation in `w`, now if its task is
   known, else once `start!` knows it (a handler may resume a fork while the
   task is still being created)."
  [s w]
  (let [t @(:task s)]
    (if (v2/handle? t)
      (watch-end! (assoc s :task t) w)
      (let [[old _] (swap-vals! (:waiting s) #(when % (conj % w)))]
        (when (nil? old) (watch-end! (assoc s :task @(:task s)) w))))))

(defn- instance-state
  "The initial state of an instance forked from `sp`: its seed (derived, or
   `child-seed`) and `handlers` merged over the inherited ones."
  [sp index child-seed handlers]
  (let [parent-seed (::seed sp)]
    (fn [state]
      (cond-> (assoc-in state [:savepoint/seed]
                        (or child-seed (derive-seed parent-seed (:savepoint/address sp) index)))
        handlers (update :savepoint/handlers merge-handlers handlers)))))

(defn- next-index! [s sp]
  (let [k [(:savepoint/world sp) (:savepoint/address sp) (:savepoint/seq sp)]]
    (dec (get (swap! (:fork-indices s) update k (fnil inc 0)) k))))

(defn- instance-sp [s sp w]
  (assoc sp :savepoint/world w ::instance (atom :unborn)))

(defn anchor?
  "Whether `sp` can still be forked: its publication keeps its basis (it was
   not disposed), whether or not it was resumed."
  [sp]
  (some? (:basis (::pub sp))))

(defn fork
  "`sp` in a new world that starts as `sp`'s world was at the site: an
   instance of its publication, owned by the session's root. Options:
   `:handlers` merged over the inherited ones, `:seed` the child's seed.
   `sp` need not be pending: a resumed savepoint is an anchor until it is
   disposed (S9). Returns the child savepoint, pending."
  ([sp] (fork sp nil))
  ([sp {:keys [handlers] child-seed :seed}]
   (let [s (::session sp)
         pub (if (anchor? sp)
               (::pub sp)
               (throw (ex-info "Cannot fork a disposed savepoint"
                               {:type ::not-pending :operation :fork :savepoint/address (:savepoint/address sp)})))
         w (v2/instantiate pub (:root s) (instance-state sp (next-index! s sp) child-seed handlers))]
     (swap! (:worlds s) conj w)
     (instance-sp s sp w))))

(defn copy
  "`k` copies of the pending `sp`, consuming it (S8): its computation
   continues only in the copies. Returns their savepoints, in order."
  [sp k]
  (let [s (::session sp)
        pub (live-pub sp :copy)
        _ (when (instance-sp? sp)
            (throw (ex-info "Cannot copy an unactivated fork: fork it instead" {:type ::not-pending :operation :copy})))
        idx (vec (repeatedly k #(next-index! s sp)))
        ws (v2/consume pub k (:root s) (fn [i] (instance-state sp (nth idx i) nil nil)))]
    (mapv (fn [w] (swap! (:worlds s) conj w) (instance-sp s sp w)) ws)))

(defn resume
  "Continues the computation suspended at `sp`, in `sp`'s world, with `v`.
   Consumes `sp`."
  [sp v]
  (let [s (::session sp)
        pub (live-pub sp :resume)]
    (when @(:closing? s)
      (throw (ex-info "Cannot resume in a closing session" {:type ::session-closing})))
    (if (instance-sp? sp)
      (when (compare-and-set! (::instance sp) :unborn :born)
        (let [w (:savepoint/world sp)]
          (v2/activate! w v)
          ;; observable once born (an unborn world takes only writes)
          (watch-world-end! s w)))
      (v2/resume! pub v))
    nil))

(defn abandon
  "Unwinds the computation suspended at `sp` (S7); an unactivated fork is
   discarded without running anything. Consumes `sp`."
  [sp]
  (let [pub (live-pub sp :abandon)]
    (if (instance-sp? sp)
      (when (compare-and-set! (::instance sp) :unborn :abandoned)
        (v2/release-world! (:savepoint/world sp)))
      (v2/abandon! pub))
    nil))

(defn dispose
  "Drops the anchor `sp` (S9): its publication's basis is freed once no
   other reference holds it; a pending one is abandoned first."
  [sp]
  (v2/dispose! (::pub sp)))

(defn spend-key
  "An identity for what is spent continuing from `sp`: per world and
   publication occurrence."
  [sp]
  [(:savepoint/world sp) (:savepoint/address sp) (:savepoint/seq sp)])

(defn release-world!
  "Gives back a world the session made."
  [s w]
  (swap! (:worlds s) disj w)
  (v2/release-world! w)
  nil)

(defn close!
  "Ends the session: stops accepting resumes, abandons pending
  publications of the worlds it made and releases them. Returns a CPS
  operation `(fn [resolve reject])` that closes when invoked and resolves
  once the releases are requested (engine v2 has no world join yet, so it
  does not wait for their cleanup)."
  [s]
  (fn [resolve reject]
    (let [resolve (off-world resolve) reject (off-world reject)]
      (try
        (reset! (:closing? s) true)
        (doseq [w @(:worlds s)] (v2/release-world! w))
        (reset! (:worlds s) #{})
        (v2/assoc-in-world! (:root s) [:savepoint/session] nil)
        (resolve nil)
        (catch #?(:clj Throwable :cljs :default) e (reject e))))))
