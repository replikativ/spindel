(ns org.replikativ.spindel.dom.differential-fuzz-harness
  "The jsdom side of the differential DOM fuzzer: run one case
   (`run-case`), the async quick-check driver with greedy shrinking
   (`quick-check-async`), and the failure report. The oracle is described
   in `differential_fuzz_test.cljs`; the program model in
   `differential_fuzz.cljc`."
  (:require [cljs.pprint :as pp]
            [clojure.string :as str]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.random :as random]
            [clojure.test.check.rose-tree :as rose]
            [org.replikativ.spindel.dom.browser :as browser]
            [org.replikativ.spindel.dom.differential-fuzz :as fz]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.sync :as sync]
            [taoensso.trove :as trove]
            ["jsdom" :refer [JSDOM]])
  (:require-macros [org.replikativ.spindel.signal]))

(def coverage
  "What the trials actually exercised — a passing run that compared nothing
   proves nothing. Printed with SPINDEL_FUZZ_VERBOSE=1."
  (atom {}))

(defn- count! [k n] (swap! coverage update k (fnil + 0) n))

;; =============================================================================
;; Coordination
;; =============================================================================

(defn- next-task
  "A promise that resolves after the event-loop tasks queued before it ran.
   The EventLoopExecutor schedules every drain and spin execution as one
   such task, so this is the engine's own unit of progress."
  []
  (js/Promise. (fn [resolve _] (js/setTimeout resolve 0))))

(def ^:private max-settle-tasks
  "How many event-loop tasks a context may stay busy before `settle!` calls
   it a livelock. A healthy trial settles in tens."
  5000)

(defn settle!
  "Resolve once `c` is quiescent: no event queued or draining, and its state
   value unchanged across a whole event-loop task. Rejects on livelock."
  [c]
  (js/Promise.
   (fn [resolve reject]
     ((fn step [prev n]
        (if (> n max-settle-tasks)
          (reject (ex-info "context did not quiesce" {:tasks n}))
          (.then (next-task)
                 (fn []
                   (let [now (rtp/get-state c [])]
                     (if (and (simple/events-settled? c) (identical? now prev))
                       (resolve n)
                       (step now (inc n))))))))
      nil 0))))

;; =============================================================================
;; Observation
;; =============================================================================

(def ^:private document
  "ONE jsdom document per process. Every mount gets its own container
   element in it: a jsdom window per mount is retained long after `.close`
   (measured: ~1000 windows alive after 200 trials, 2 GB heap exhausted by
   trial ~1000), and nothing here needs document isolation — contexts,
   discharges and element registries are per mount."
  (delay (.-document (.-window (JSDOM. "<!DOCTYPE html><html><body></body></html>")))))

(def ^:private open-containers (atom []))

(defn fresh-body
  "A new, empty container element attached to the shared document. Removed
   by the next `release-containers!`."
  []
  (let [^js doc @document
        el (.createElement doc "div")]
    (.appendChild (.-body doc) el)
    (swap! open-containers conj el)
    el))

(defn release-containers!
  "Detach every container `fresh-body` handed out since the last call."
  []
  (let [[els _] (swap-vals! open-containers (constantly []))]
    (doseq [^js el els] (.remove el))))

(defn- canonical
  "The DOM as data: [tag sorted-attrs & children], adjacent text merged and
   empty text dropped (text-node splitting is invisible)."
  [^js node]
  (letfn [(kids [^js n]
            (->> (array-seq (.-childNodes n))
                 (keep (fn [^js c]
                         (case (.-nodeType c)
                           1 (canonical c)
                           3 (.-data c)
                           nil)))
                 (partition-by string?)
                 (mapcat (fn [run] (if (string? (first run)) [(apply str run)] run)))
                 (remove #(= "" %))))]
    (into [(str/lower-case (.-tagName node))
           (into (sorted-map) (map (fn [^js a] [(.-name a) (.-value a)]))
                 (array-seq (.-attributes node)))]
          (kids node))))

(defn- fk-snapshot [^js body]
  (into {} (map (fn [^js n] [(.getAttribute n "data-fk") n]))
        (array-seq (.querySelectorAll body "[data-fk]"))))

(defn quiet-logs!
  "Pass only :warn and above to the current trove backend. Returns the fn
   that restores it."
  []
  (let [saved trove/*log-fn*]
    (set! trove/*log-fn*
          (fn [ns coords level id lazy_]
            (when (and saved (#{:warn :error :fatal} level))
              (saved ns coords level id lazy_))))
    #(set! trove/*log-fn* saved)))

(defn- capture-logs!
  "Route trove to a recorder for the trial: :error and :warn entries are kept
   (errors fail the trial), everything below is dropped — the engine traces
   every event, which would both flood the output and dominate the runtime."
  [sink]
  (set! trove/*log-fn*
        (fn [ns _coords level id lazy_]
          (when (#{:warn :error :fatal} level)
            (swap! sink conj {:level level :ns ns :id id
                              :data (:data (force lazy_))})))))

;; =============================================================================
;; Mount refs (engine-formalism §3.9 R5)
;; =============================================================================
;;
;; Every element of every mount carries `ref-probe` as its `:ref`. A mount call
;; must find its element attached (`.isConnected` — every container is in the
;; document) and must be the element's first; at each observation point every
;; element in the container must have had exactly one. Unmount calls (nil) are
;; not checked here.

(def ^:private ref-counts
  "element → mount calls received. Weak: elements die with their trial."
  (js/WeakMap.))

(def ^:private ref-violations
  "Fire-time violations since the last `drain-ref-failures!`."
  (atom []))

(defn- describe-el [^js el]
  {:class (.getAttribute el "class") :data-fk (.getAttribute el "data-fk")})

(defn ref-probe [^js el]
  (when el
    (count! :refs-fired 1)
    (let [n (inc (or (.get ref-counts el) 0))]
      (.set ref-counts el n)
      (when-not (.-isConnected el)
        (swap! ref-violations conj (assoc (describe-el el) :problem :detached-at-fire)))
      (when (= n 2)
        (swap! ref-violations conj (assoc (describe-el el) :problem :fired-twice))))))

(defn- drain-ref-failures!
  "Fire-time violations so far, plus every element under `body` that never
   received a mount call. Nil when there are none."
  [^js body]
  (let [[fired _] (reset-vals! ref-violations [])
        unfired (for [^js el (array-seq (.querySelectorAll body "*"))
                      :when (not (.hasAttribute el "data-spindel-render-error"))
                      :when (zero? (or (.get ref-counts el) 0))]
                  (assoc (describe-el el) :problem :never-fired))
        all (into (vec fired) unfired)]
    (when (seq all)
      [{:check :mount-refs :violations all}])))

;; =============================================================================
;; One trial
;; =============================================================================

(defn- mount!
  "Create signals + deferreds in `c` from model `state`, mount `program`.
   Returns {:body :sigs :dfrs :stop!}."
  [c program {:keys [vals delivered]}]
  (set! ec/*execution-context* c)
  (let [sigs (mapv (fn [v] (sig/signal c v)) vals)
        ;; only the deferreds the program awaits: a context that holds a
        ;; Deferred is never collected (regressions ns, defect 4)
        used (fz/deferreds-used program)
        dfrs (mapv (fn [d] (when (used d) (sync/create-deferred c))) (range fz/n-deferreds))
        _ (doseq [[d v] delivered :when (nth dfrs d)] (sync/deliver! (nth dfrs d) v))
        body (fresh-body)
        handle (render/render-spin! body
                                    (fz/render program {:sigs sigs :dfrs dfrs :vals {} :dvals {}
                                                        :ref ref-probe})
                                    (browser/make-dom-discharge (.-ownerDocument body)))]
    {:body body :sigs sigs :dfrs dfrs :stop! (:stop! handle)}))

(defn- fresh-canonical
  "Canonical DOM of `program` mounted from scratch at model `state`, in a NEW
   execution context. Resolves to {:dom :html :violations}."
  [program state]
  (let [c (ctx/create-execution-context)
        {:keys [body]} (mount! c program state)]
    (-> (settle! c)
        (.then (fn [_]
                 (let [r {:dom (when-let [root (.-firstElementChild body)] (canonical root))
                          :html (.-innerHTML body)
                          :violations (disch/drain-violations!)
                          :ref-failures (drain-ref-failures! body)}]
                   (ctx/stop-context! c)
                   r))))))

(defn- apply-to-engine!
  "Mirror one model transition onto the mounted signals/deferreds. A
   deferred is delivered once — a repeated delivery is a model no-op."
  [{:keys [sigs dfrs]} state state' [kind s]]
  (case kind
    (:flip :set-n :ins :del :move :upd) (reset! (nth sigs s) (get-in state' [:vals s]))
    :deliver (when (and (nth dfrs s) (not (contains? (:delivered state) s)))
               (sync/deliver! (nth dfrs s) (get-in state' [:delivered s])))
    nil))

(defn- identity-failures
  "Item roots that survived the step by key but were re-created."
  [program prev now {:keys [flipped removed]}]
  (let [guards (fz/for-guards program)]
    (for [[fk node] now
          :let [old (get prev fk)]
          :when (and old (not (identical? old node)))
          :let [{:keys [for-id kpath]} (fz/parse-fk fk)
                {:keys [ifs fors sig]} (get guards for-id)
                memberships (map vector (conj fors sig) kpath)]
          :when (and (not-any? #(contains? flipped %) ifs)
                     (not-any? #(contains? removed %) memberships))]
      {:check :key-identity :data-fk fk
       :note "item key persisted, no ancestor flipped, yet the DOM node was re-created"})))

(defn- observe!
  "All checks at one quiescent point. Resolves to the failures found."
  [program state {:keys [body] :as mounted} prev-fks disturbed logs]
  (let [violations (disch/drain-violations!)
        errors (filter #(#{:error :fatal} (:level %)) @logs)
        _ (reset! logs [])
        now-fks (fk-snapshot body)
        _ (count! :observations 1)
        _ (count! :identity-pairs (count (filter #(contains? prev-fks %) (keys now-fks))))
        base (concat
              (when (seq violations) [{:check :integrity :violations violations}])
              (when (seq errors) [{:check :errors-logged :entries (vec errors)}])
              (drain-ref-failures! body)
              (when (.querySelector body "[data-spindel-render-error]")
                [{:check :render-rejected
                  :text (.-textContent (.querySelector body "[data-spindel-render-error]"))}])
              (when prev-fks (identity-failures program prev-fks now-fks disturbed)))
        all-delivered? (every? #(contains? (:delivered state) %) (fz/deferreds-used program))]
    (if-not all-delivered?
      (js/Promise.resolve {:failures (vec base) :fks now-fks})
      (let [_ (count! :differential-checks 1)
            _ (count! :elements-compared (.-length (.querySelectorAll body "*")))
            mounted-ctx ec/*execution-context*
            inc-dom (when-let [root (.-firstElementChild body)] (canonical root))
            inc-html (.-innerHTML body)]
        (-> (fresh-canonical program state)
            (.then (fn [{:keys [dom html violations ref-failures]}]
                     (set! ec/*execution-context* mounted-ctx)
                     {:fks now-fks
                      :failures (vec (concat
                                      base
                                      (when (not= inc-dom dom)
                                        [{:check :differential
                                          :incremental inc-html
                                          :fresh html}])
                                      (when (seq violations)
                                        [{:check :integrity-fresh-mount :violations violations}])
                                      (map #(assoc % :check :mount-refs-fresh-mount) ref-failures)))})))))))

(defn- run-steps
  "Apply `steps` from index `i` on, observing at every `[:settle]`. Resolves
   to the trial result."
  [c program mounted logs n-ops steps]
  ((fn step [i state fks disturbed]
     (if (= i (count steps))
       (js/Promise.resolve {:pass? true})
       (let [op (nth steps i)
             [state' d] (fz/apply-op state op)
             disturbed' (merge-with into disturbed d)
             at (if (< i n-ops) i :final)]
         (apply-to-engine! mounted state state' op)
         (case (first op)
           :tick (.then (next-task) (fn [_] (step (inc i) state' fks disturbed')))
           :settle (-> (settle! c)
                       (.then (fn [_] (observe! program state' mounted fks disturbed' logs)))
                       (.then (fn [{:keys [failures fks]}]
                                (if (seq failures)
                                  {:pass? false :failures failures :at at}
                                  (step (inc i) state' fks {})))))
           (step (inc i) state' fks disturbed')))))
   0 (:state0 mounted) (:fks0 mounted) {}))

(defn run-case
  "Run one fuzz case `{:program raw :init vals :ops [...]}` end to end.
   Resolves to {:pass? bool :failures [...] :at <op index, :mount or
   :final>}; the first observation point with failures ends the trial."
  [{:keys [program init ops profile]}]
  (let [program (fz/normalize program profile)
        ;; every deferred still undelivered at the end is delivered (in index
        ;; order) before the final observation, so the final state is total
        tail (concat (map (fn [d] [:deliver d d]) (range fz/n-deferreds)) [[:settle]])
        steps (vec (concat ops tail))
        logs (atom [])
        saved-log-fn trove/*log-fn*
        c (ctx/create-execution-context)
        state0 {:vals init :delivered {}}
        finish (fn [r]
                 (ctx/stop-context! c)
                 (release-containers!)
                 (set! ec/*execution-context* nil)
                 (set! trove/*log-fn* saved-log-fn)
                 r)]
    (capture-logs! logs)
    (disch/collect-violations!)
    (reset! ref-violations [])
    (-> (js/Promise.resolve nil)
        (.then (fn [_]
                 (let [mounted (mount! c program state0)]
                   (-> (settle! c)
                       (.then (fn [_] (observe! program state0 mounted nil {} logs)))
                       (.then (fn [{:keys [failures fks]}]
                                (if (seq failures)
                                  {:pass? false :failures failures :at :mount}
                                  (run-steps c program
                                             (assoc mounted :state0 state0 :fks0 fks)
                                             logs (count ops) steps))))))))
        (.then finish
               (fn [e] (finish {:pass? false :at :exception
                                :failures [{:check :exception
                                            :message (or (.-message e) (str e))
                                            :stack (some-> (.-stack e) (str/split #"\n") (->> (take 12) vec))
                                            :data (ex-data e)}]}))))))

;; =============================================================================
;; Async quick-check: generate, run, shrink — on promises
;; =============================================================================
;;
;; test.check's `quick-check` needs a synchronous property; a trial here is a
;; chain of event-loop tasks. Generation and the shrink tree are test.check's
;; own (`call-gen` + rose trees); only the walk is re-done asynchronously:
;; greedy depth-first, the first failing child replaces the current case.

(defn- shrink!
  "Resolve to the smallest failing case reachable from `tree`, greedily.
   `with-opts` completes a generated value into a runnable case."
  [tree result budget with-opts]
  (js/Promise.
   (fn [resolve _]
     ((fn descend [tree result used]
        ((fn try-children [children used]
           (cond
             (or (>= used budget) (empty? children))
             (resolve {:case (with-opts (rose/root tree)) :result result :shrinks used})
             :else
             (let [child (first children)]
               (.then (run-case (with-opts (rose/root child)))
                      (fn [r]
                        (if (:pass? r)
                          (try-children (rest children) (inc used))
                          (descend child r (inc used))))))))
         (rose/children tree) used))
      tree result 0))))

(defn quick-check-async
  "Resolve to {:pass? true :trials n} or a failure report with the shrunk
   case."
  [{:keys [trials seed max-size max-shrinks profile]}]
  (js/Promise.
   (fn [resolve _]
     ((fn trial [i rnd]
        (if (= i trials)
          (resolve {:pass? true :trials trials :seed seed})
          (let [with-opts #(cond-> % (seq profile) (assoc :profile profile))
                [r1 r2] (random/split rnd)
                size (min max-size (+ 2 i))
                tree (gen/call-gen fz/gen-case r1 size)]
            (.then (run-case (with-opts (rose/root tree)))
                   (fn [r]
                     (if (:pass? r)
                       (trial (inc i) r2)
                       (.then (shrink! tree r max-shrinks with-opts)
                              (fn [shrunk]
                                (resolve (assoc shrunk :pass? false :seed seed
                                                :trial i
                                                :original (with-opts (rose/root tree))))))))))))
      0 (random/make-random seed)))))

(defn report
  "A failure as text: the minimal program as code, the ops, the evidence,
   and the EDN to pin."
  [{:keys [seed trial shrinks result] :as r}]
  (let [{:keys [program init ops profile]} (:case r)
        norm (fz/normalize program profile)]
    (str "\n==== differential DOM fuzz failure (seed " seed ", trial " trial
         ", " shrinks " shrink steps) ====\n"
         "-- program (as spindel code):\n"
         (with-out-str (pp/pprint (fz/->code norm)))
         "-- initial signal values (sig0..):\n"
         (with-out-str (pp/pprint init))
         "-- ops (then every deferred is delivered and the engine settled):\n"
         (with-out-str (pp/pprint ops))
         "-- failed at " (pr-str (:at result)) ":\n"
         (with-out-str (pp/pprint (:failures result)))
         "-- minimal case (EDN, for a pinned regression):\n"
         (pr-str (:case r)) "\n")))

