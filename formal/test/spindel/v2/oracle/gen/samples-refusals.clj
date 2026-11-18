;; Refusal-focused log samples for the oracle (samples 43-50), from the formal reviewer's coverage
;; report of 2026-11-18 (few refused items, item kinds never driven, pins never populated).
;;
;; 43  T21 with host items queued before it (worlds :root, :hostfork = (fork! root), :effect = the
;;     `(fork)` child of a root task). Sixteen host operations are admitted while the root's gate
;;     is held, then T21 runs first (`release-world*` under the gate, as formal_review_test
;;     host-items-queued-before-release-are-refused). Refused in the root's log, one each:
;;     write, spawn-top, create-comp-top, deliver, post, release, append, close, cancel (the task's
;;     run retired at T21), unpin (T21 dropped the pins), handle-drop (T21 zeroed the handles).
;;     A queued pin and observe are revoked without an item (shut-roots!), a value-async gets
;;     ::released without an item. NOT included: a queued `(signal ..)` / host `(aseq ..)`; the
;;     engine accepts those after T21 (.internal/repro-create-source-after-release.clj).
;; 44  await cycle: computation a awaits b, b awaits a (b's await closes the cycle). Refused:
;;     await x1 (b's run; `[:await r ds mode a]`, the activation id the refused T6 would have taken);
;;     both fail with ::cycle.
;; 45  a blocked chain deeper than 64: 66 tasks, each awaiting the next, the last a deferred,
;;     then the delivery. No refusal. (66, not 100: every entry carries the projection, so the
;;     log grows quadratically; this log is written compactly, one entry per line.)
;; 46  pins and handles: pin x2 / unpin x2 / unpin at count 0 (refused unpin x1) on a computation,
;;     pin / unpin of a signal, host-unawait (value-async withdrawn before the deferred is
;;     delivered), handle-drop by `release!` (a second release! makes no item), and handle-new:
;;     a computation body's inner `(spin ..)` handle is collected (handle-drop by the Cleaner),
;;     the outer computation reruns and readopts it (`[:handle-new c]` then `[:create-comp r c ..]`).
;;     The forced collections also drop host handles no longer used (more handle-drop items).
;; 47  creations inside bodies: create-comp in a task body (owned by the run scope), create-link in a
;;     task body (an aseq and a seq/amap over it), create-link in a computation body; link-demand
;;     and link-realize as the elements are read. No refusal.
;; 48  resources and the semaphore: timer, offload and external fire (resource-fire + resource-ack);
;;     an external cancelled while its operation ignores the cancel (cancel fn returns nil): its
;;     late completion is refused (refused resource-fire x1); a semaphore served to a parked
;;     acquirer by a release, a release back to the maximum, and one over the maximum (refused
;;     release x1, sem-release! throws ::over-release, Z#62).
;; 49  await-all fail-fast (Z#61): `(await-all [ok slow bad])`, bad fails while slow is pending:
;;     the awaiting task fails at once with bad's error; slow is delivered afterwards. No refusal.
;; 50  one slice holder at a time (D0, engine 47f0609): (a) a task body awaits an idle computation
;;     that needs a run (c ran while observed, was unobserved, then its signal was written: idle and
;;     invalid), so the await starts c's run (`[:start c r]`: the engine's dispatch item, T5 for an
;;     idle computation) after the task's run parked, then `[:schedule r]`; (b) a task body calls
;;     observe! on one fresh computation and value-async on another of its own world: both are
;;     demanded while the task's run holds the slice, so their runs are queued and start
;;     (`[:start ..]` + `[:schedule ..]`) only after the task's `[:complete ..]`. No refusal.
;;
;; Not generated (unreachable through the public API as logs):
;;   B8 creations in a cancelled run's cleanup slice: spawn and create-comp return nil and a
;;     body create-source throws, all before any item (valid-run is nil once the run is done);
;;     track/await/take there fail through `unwinding-finalizer-refusal`, also without an item.
;;     So in-cleanup / cur-closed never see an item.
;;   stale effect tokens: every effect checks `valid-run` on the running thread; a run that moved
;;     on is not the active run, and a done run drops the effect (unwind!) without an item.
;;   [:fire e tag val] (T9): the engine never emits it (cross-world fires are resource fires).
;;   pubs / pending-act: no layer-1 item populates them (a savepoint is an `arm`, layer 2 keeps the
;;     publication); the engine projection has `:pubs {}` and `:pending-act nil`.
;;
;; Sidecar (every sample, `log-sample-N-observations.edn`): a vector of checkpoints
;;   {:step kw :log-length {world n} :obs {world obs}}; each world is read under its gate without a
;;   turn (as samples-c1c-b.clj). Per world, obs:
;;     :complete? :released? :runs :kids :token   as samples-c1c-b.clj (C1)
;;     :tasks :scopes :pending-joins             as samples-c1c-b.clj (C1c stage A; every task and
;;                                               scope met at an earlier checkpoint stays listed)
;;     :owned :normalize                         as samples-c1c-b.clj (C1c stage B)
;;     :owned-by  the id of the world whose obligation this world is (its accepted kid token's
;;                owner, `owner-world`), nil for a root world. Once the token is :done (the world
;;                completed) the owner is no longer readable: the last value read at an earlier
;;                checkpoint is carried.
;;     :holders   {owner-scope-id n}: W-OWNED, the live fork holders (not released, child not
;;                collected) per owner scope of this world; scopes with n = 0 are left out.
;;     :comps     {comp-id {:epoch :done-epoch :idle? :validity}} for every computation row present:
;;                C-EPOCH, C-DONE-EPOCH (nil = never completed), C-IDLE, and C-VALIDITY
;;                (nil, :invalid, or [[debtor-id version] ...] of an idle computation).
;;
;; Generated on fix/v2-no-nested-host-slice (47f0609: a host operation inside a slice starts no
;; nested slice). From the worktree root (one -Xmx1g JVM):
;;   clojure -J-Xmx1g -M:bench -i formal/test/spindel/v2/oracle/gen/samples-refusals.clj
(ns samples-refusals
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task spin await await-all track acquire!]]
            [org.replikativ.spindel.v2.seq :as aseq]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]
            [clojure.pprint]))

(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l & [compact?]]
  (spit path (if compact? (str "[" (apply str (map #(str (pr-str %) "\n") l)) "]\n") (with-out-str (clojure.pprint/pprint l))))
  [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld [acc] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))}))
(defn- f [^objects row i] (aget row (int i)))
(defn- wait-until [g] (loop [n 400] (or (g) (when (pos? n) (Thread/sleep 5) (recur (dec n))))))
(defn- queued [w] (count (seq (f w rw/W-INGRESS))))
(defn- try-val [h] (try (v2/value h 2000 :timeout) (catch Throwable e [:err (ex-message e)])))
(defn- refused [w] (mapv :item (remove :accepted (verify/log w))))

(defn- under-gate
  "`(g)` while holding `w`'s gate, without running a turn; queued work is
   handed off afterwards (H2)."
  [w g]
  (let [lk (f w rw/W-LOCK)]
    (hs/lock! lk)
    (try (g) (finally (hs/unlock! lk) (#'v2/handoff! w)))))

(defn- validity [v]
  (if (sequential? v) (mapv (fn [[d ver]] [(f d rw/ID) ver]) v) v))

(defn- obs
  "The world's observations. `seen` (an atom {world-id {id row}}) keeps every task and scope row
   met so far; `owners` (an atom {world-id owner-id}) the last owner read."
  [^objects w seen owners]
  (under-gate
   w
   (fn []
     (let [live (into {} (f w rw/W-REG))
           wid (f w rw/ID)
           _ (swap! seen update wid merge
                    (into {} (filter (fn [[_ row]] (#{rw/T-TASK rw/T-SCOPE} (f row rw/TYPE)))) live))
           rows (into {} (map (fn [[id row]] [id (#'v2/peek-row w row)])) (get @seen wid))
           present? (fn [row] (contains? live (f row rw/ID)))
           _ (when-let [o (#'v2/owner-world w)] (swap! owners assoc wid (f o rw/ID)))]
       {:complete? (v2/complete? w)
        :released? (boolean (f w rw/W-RELEASED))
        :runs (long (or (f w rw/W-RUNS) 0))
        :kids (when-let [k (f w rw/W-KIDS)] (hs/kids-count k))
        :token (when-let [^java.util.concurrent.atomic.AtomicReference c (f w rw/W-KID-TOKEN)]
                 (let [v (.get c)] (cond (nil? v) :none (= :done v) :done :else :installed)))
        :tasks (into (sorted-map)
                     (for [[id row] rows :when (= rw/T-TASK (f row rw/TYPE))]
                       [id {:done? (boolean (f row rw/K-DONE))
                            :retired? (nil? (f row rw/K-RUN))
                            :materialized? (some? (f row rw/K-SROW))
                            :srow-present? (boolean (when-let [s (f row rw/K-SROW)] (present? s)))
                            :complete? (boolean (f row rw/K-COMPLETE))}]))
        :scopes (into (sorted-map)
                      (for [[id row] rows :when (= rw/T-SCOPE (f row rw/TYPE))]
                        [id {:open? (boolean (f row rw/S-OPEN))
                             :present? (present? row)
                             :complete? (boolean (f row rw/S-COMPLETE))}]))
        :pending-joins (count (filter (comp hs/flag? first) (mapcat val (f w rw/W-JOIN-SUBS))))
        :owned (into (sorted-map) (map (fn [[sid [_ n]]] [sid n])) (f w rw/W-OWNED-N))
        :normalize (into (sorted-set) (keys (f w rw/W-NORMALIZE)))
        :owned-by (get @owners wid)
        :holders (into (sorted-map)
                       (keep (fn [[sid ^objects e]]
                               (let [n (count (remove #'v2/holder-dead? (aget e 0)))]
                                 (when (pos? n) [sid n]))))
                       (some-> (f w rw/W-OWNED) hs/mentries))
        :comps (into (sorted-map)
                     (for [[id row0] live :when (= rw/T-COMP (f row0 rw/TYPE))
                           :let [row (#'v2/peek-row w row0)]]
                       [id {:epoch (f row rw/C-EPOCH) :done-epoch (f row rw/C-DONE-EPOCH)
                            :idle? (boolean (f row rw/C-IDLE)) :validity (validity (f row rw/C-VALIDITY))}]))}))))

(defn- sidecar [] {:sc (atom []) :seen (atom {}) :owners (atom {})})

(defn checkpoint! [{:keys [sc seen owners]} worlds step]
  (Thread/sleep 60)
  (swap! sc conj {:step step
                  :log-length (into (sorted-map) (map (fn [[n w]] [n (count (verify/log w))])) worlds)
                  :obs (into (sorted-map) (map (fn [[n w]] [n (obs w seen owners)])) worlds)}))

(defn finish! [n worlds {:keys [sc]} acc & [compact?]]
  (doseq [[nm w] worlds]
    (prn (dump! (str dir "log-sample-" n "-" (name nm) ".edn") (verify/log w) compact?))
    (prn :sample n nm :refused (refused w)))
  (spit (str dir "log-sample-" n "-observations.edn") (with-out-str (clojure.pprint/pprint @sc)))
  (prn :sample n :divergences @acc))

;; 43
(let [acc (atom []) sc (sidecar) w (vworld acc) kid (promise)]
  (binding [v2/*world* w]
    (let [s (v2/signal 1) d (v2/deferred) m (v2/mailbox) sem (v2/semaphore 1)
          st (v2/stream) h2 (v2/signal 5) c (spin 7)
          t (task (await (v2/deferred)))
          hostfork (v2/fork! w)
          ft (task (let [[side child] (v2/fork)]
                     (if (= side :child)
                       (await (v2/deferred))
                       (do (deliver kid child) (await (v2/deferred))))))
          effect (deref kid 2000 nil)
          ws {:root w :hostfork hostfork :effect effect}
          _ (v2/pin! s)
          _ (checkpoint! sc ws :before)
          lk (f w rw/W-LOCK)
          n (atom 0)
          q! (fn [g] (let [fu (future (binding [v2/*world* w] (try (g) nil (catch Throwable e (ex-message e)))))]
                       (swap! n inc)
                       (when-not (wait-until #(= @n (queued w))) (prn :43-not-queued @n))
                       fu))]
      (hs/lock! lk)
      (let [ops [(q! #(v2/write! s 2))
                 (q! #(task :never))
                 (q! #(spin 9))
                 (q! #(v2/deliver! d 1))
                 (q! #(v2/post! m 1))
                 (q! #(v2/sem-release! sem))
                 (q! #(v2/append! st 1))
                 (q! #(v2/close! st))
                 (q! #(v2/cancel-task! t))
                 (q! #(v2/unpin! s))
                 (q! #(v2/release! h2))
                 (q! #(v2/pin! c))
                 (q! #(v2/observe! c (fn [_ _])))
                 (q! #(v2/value-async c (fn [_ _])))]]
        (#'v2/release-world* w)                  ; T21 first
        (hs/unlock! lk)
        (#'v2/process! w)
        (prn :43-ops (mapv #(deref % 2000 :timeout) ops)))
      (prn :43-complete (mapv #(v2/await-complete % 2000 :timeout) [effect hostfork w]))
      (checkpoint! sc ws :released)
      (prn :43 (try-val ft))
      (finish! 43 ws sc acc))))

;; 44
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (binding [v2/*world* w]
    (let [cell (clojure.core/atom nil)
          a (spin (await (clojure.core/deref cell)))
          b (spin (inc (await a)))
          _ (reset! cell b)
          ws {:w w}]
      (checkpoint! sc ws :created)
      (prn :44 (try-val a) (try-val b))
      (checkpoint! sc ws :failed)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! 44 ws sc acc))))

;; 45
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (binding [v2/*world* w]
    (let [gate (v2/deferred)
          ts (loop [i 0 prev gate acc []]
               (if (= i 66) acc
                   (let [t (let [p prev] (task (await p)))] (recur (inc i) t (conj acc t)))))
          top (peek ts)
          ws {:w w}]
      (prn :45-blocked (wait-until #(v2/call-in! w (fn [] (#'v2/blocked? w (#'v2/row-of top) 0)))))
      (checkpoint! sc ws :blocked)
      (v2/deliver! gate :go)
      (prn :45 (try-val top))
      (checkpoint! sc ws :delivered)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! 45 ws sc acc true))))

;; 46
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (binding [v2/*world* w]
    (let [s (v2/signal 1)
          c (spin (* 2 (iv/get-new (track s))))
          d (v2/deferred)
          got (promise)
          ws {:w w}]
      (v2/pin! c) (v2/pin! c)
      (checkpoint! sc ws :pinned)
      (v2/unpin! c) (v2/unpin! c) (v2/unpin! c)            ; the third at count 0: refused
      (v2/pin! s)
      (let [un (v2/value-async d (fn [v e] (deliver got [v e])))]
        (un)                                              ; host-unawait before the delivery
        (v2/deliver! d 5))
      (let [h (v2/signal 9)] (v2/release! h) (v2/release! h))
      (checkpoint! sc ws :dropped)
      (v2/unpin! s)
      (prn :46-unawaited (deref got 100 :none) :c (try-val c))
      ;; handle-new: p's inner computation keeps its row (p's basis) but its body handle is collected
      (let [x (v2/signal 1)
            p (spin (let [n (iv/get-new (track x))
                          inner (spin 10)]
                      (+ n (await inner))))
            stop (v2/observe! p (fn [_ _]))]
        (try-val p)
        (let [inner (nth (:item (last (filter #(= :create-comp (first (:item %))) (verify/log w)))) 2)]
          (prn :46-inner-dropped inner
               (loop [i 0]
                 (verify/gc-settle! w)
                 (cond (some #(= [:handle-drop inner] (:item %)) (verify/log w)) true
                       (> i 20) false
                       :else (recur (inc i))))))
        (checkpoint! sc ws :inner-dropped)
        (v2/write! x 2)
        (prn :46-p (try-val p))
        (checkpoint! sc ws :readopted)
        (stop))
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! 46 ws sc acc))))

;; 47
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (binding [v2/*world* w]
    (let [t (task (let [c (spin 41)
                        xs (v2/aseq [n 0] (when (< n 2) [n (inc n)]))
                        ys (aseq/amap inc xs)
                        [y0 nx] (await ys)
                        [y1 _] (await nx)]
                    [(await c) y0 y1]))
          q (spin (let [zs (v2/aseq [n 5] (when (< n 6) [n (inc n)]))]
                    (first (await zs))))
          ws {:w w}]
      (prn :47 (try-val t) (try-val q))
      (checkpoint! sc ws :read)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! 47 ws sc acc))))

;; 48
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (binding [v2/*world* w]
    (let [sem (v2/semaphore 1)
          cp (promise)
          t (task [(v2/sleep 20)
                   (v2/offload (fn [] :off))
                   (v2/external (fn [complete!] (deliver cp complete!) nil))])
          _ (future ((deref cp 2000 nil) :ext))
          _ (prn :48-resources (try-val t))
          late (promise)
          u (task (v2/external (fn [complete!] (deliver late complete!) (fn [] nil))))
          ws {:w w}
          _ (deref late 2000 nil)
          _ (checkpoint! sc ws :external-armed)
          _ (v2/cancel-task! u)
          _ (checkpoint! sc ws :cancelling)
          _ ((deref late 2000 nil) :too-late)            ; refused fire, then the ack
          _ (prn :48-cancelled (try-val u))
          t1 (task (acquire! sem) :t1)
          _ (try-val t1)
          t2 (task (acquire! sem) :t2)
          _ (wait-until #(= 2 (count (filter (fn [e] (= :take (first (:item e)))) (verify/log w)))))
          _ (checkpoint! sc ws :acquirer-parked)
          _ (v2/sem-release! sem)                         ; served to t2
          _ (prn :48-t2 (try-val t2))
          _ (v2/sem-release! sem)                         ; back to the maximum
          over (try (v2/sem-release! sem) :no-throw (catch Throwable e (:spindel/invalid (ex-data e))))]
      (prn :48-over over :permits (v2/permits sem))
      (checkpoint! sc ws :over-released)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! 48 ws sc acc))))

;; 49
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (binding [v2/*world* w]
    (let [gate (v2/deferred) slow (v2/deferred)
          bad (task (await gate) (throw (ex-info "boom" {})))
          ok (task :ok)
          t (task (await-all [ok slow bad]))
          ws {:w w}]
      (wait-until #(some (fn [e] (= :all (nth (:item e) 3 nil))) (verify/log w)))
      (checkpoint! sc ws :awaiting)
      (v2/deliver! gate :go)
      (prn :49 (try-val t))
      (checkpoint! sc ws :failed-fast)
      (v2/deliver! slow :late)
      (checkpoint! sc ws :slow-delivered)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! 49 ws sc acc))))

;; 50
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (binding [v2/*world* w]
    (let [s (v2/signal 1)
          c (spin (* 2 (iv/get-new (track s))))
          stop (v2/observe! c (fn [_ _]))
          _ (try-val c)
          _ (stop)                                        ; c idle
          _ (v2/write! s 2)                               ; ... and invalid: it needs a run
          ws {:w w}
          _ (checkpoint! sc ws :idle-invalid)
          t (task (inc (await c)))
          _ (prn :50a (try-val t))
          _ (checkpoint! sc ws :awaited)
          seen-o (promise) seen-v (promise)
          d1 (spin 10) d2 (spin 20)
          u (task (let [stop (v2/observe! d1 (fn [v _] (deliver seen-o v)))
                        un (v2/value-async d2 (fn [v _] (deliver seen-v v)))]
                    [stop un]))
          [stop-o _] (try-val u)]
      (prn :50b (deref seen-o 2000 :timeout) (deref seen-v 2000 :timeout))
      (checkpoint! sc ws :observed-from-body)
      (stop-o)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! 50 ws sc acc))))

(shutdown-agents)
