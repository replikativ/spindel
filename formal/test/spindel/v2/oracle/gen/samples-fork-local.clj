;; Z#77 fork-local tasks: oracle log samples 51-60 (`.internal/fork-local-design.md` §7, the scenario table), from
;; the engine branch feat/v2-fork-local (869bf29 and later: `task-with`, `[:retire-local]`, the trailing `true` of a
;; fork-local `[:spawn ..]` / `[:spawn-top ..]`).
;;
;; 51  root, fork-host: a local task is parked on a deferred and an unmarked task awaits it; the child is entered by a
;;     write. `[:retire-local]` is the child's first item; the waiter fills with err ::forked (:spindel/fork-local).
;; 52  root, fork-host: a local clock parked on a timer; after the first entry no timer of it is dormant, runs drop.
;; 53  root, fork-host: a local run mid-offload and an unmarked one mid-offload: `[:retire-local]`, then the unmarked
;;     dormant offload fires ::forked; the local one does not.
;; 54  root, fork-host: an untouched child is released: `[:retire-local]` precedes `[:release-world]`; no cleanup
;;     entry; complete (QD).
;; 55  root, fork: the `(fork)` effect of an unmarked run with a local sibling: the child's first turn retires the
;;     sibling, then the forker resumes `[:child nil]`. A `(fork)` in a local run is refused (no item).
;; 56  root, fork-host: an unmarked loop stays live and resumes in the child; a local loop is retired.
;; 57  root, instance: an instance of an unmarked publication with a local sibling is retired at its first entry,
;;     before the activation. `instantiate` of a local run's publication is refused (throws, no item).
;; 58  root, fork-host: detach of an unmarked task into a local scope is refused (`[:detach k s]` accepted false); a
;;     local task detached to root keeps its mark and is retired in the child.
;; 59  root, fork-host: a local scope owns a source (a mailbox with an unmarked taker) and a computation: in the child
;;     the source is closed and its taker woken (::closed); the computation's owner is ⊥ and it is still demanded.
;; 60  root, fork-host: `cancel-task!` of an inherited local task in a never-entered child (probe P1): `[:retire-local]`
;;     first, then the cancel is a no-op on the done task.
;;
;; Sidecar (every sample, `log-sample-N-observations.edn`): as samples-refusals.clj, plus per task `:local`
;; (K-LOCAL, the fork-local mark).
;;
;; From the repository root, with the engine branch's `src` first on the classpath (one -Xmx1g JVM), e.g.
;;   clojure -J-Xmx1g -Sdeps '{:paths ["../spindel-v2-aseq/src" "../spindel-v2-aseq/test"]}' -M \
;;     -i formal/test/spindel/v2/oracle/gen/samples-fork-local.clj
;; (no :bench alias: its extra path test/ would put this worktree's verify.clj, without the task's :local, ahead of
;; the engine's). Generated from e758834.
;; Generated logs are registered in oracle_test.clj (`fork-local-specs`).
(ns samples-fork-local
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task task-with spin await]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.verify :as verify]
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
                            :complete? (boolean (f row rw/K-COMPLETE))
                            :local (boolean (f row rw/K-LOCAL))}]))
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

(defn- settle [] (Thread/sleep 80))
(defn- in [w g] (binding [v2/*world* w] (g)))

;; 51
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (let [d (in w #(v2/deferred))
        s (in w #(v2/signal 0))
        lt (in w #(task-with {:fork-local true} (await d)))
        _ (in w #(task (try (await lt) (catch Throwable e (ex-data e)))))
        _ (settle)
        c (v2/fork! w)
        ws {:root w :child c}]
    (checkpoint! sc ws :forked)
    (v2/write! (v2/in-world c s) 1)
    (settle)
    (checkpoint! sc ws :entered)
    (v2/release-world! c) (v2/release-world! w)
    (settle)
    (checkpoint! sc ws :released)
    (finish! 51 ws sc acc)))

;; 52
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (let [s (in w #(v2/signal 0))
        _ (in w #(task-with {:fork-local true} (loop [] (v2/sleep 30) (recur))))
        _ (settle)
        c (v2/fork! w)
        ws {:root w :child c}]
    (checkpoint! sc ws :forked)
    (v2/write! (v2/in-world c s) 1)
    (settle)
    (checkpoint! sc ws :entered)
    (v2/release-world! c) (v2/release-world! w)
    (settle)
    (checkpoint! sc ws :released)
    (finish! 52 ws sc acc)))

;; 53
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (let [s (in w #(v2/signal 0))
        _ (in w #(task-with {:fork-local true} (v2/offload (fn [] (Thread/sleep 200) :local))))
        _ (in w #(task (try (v2/offload (fn [] (Thread/sleep 200) :plain)) (catch Throwable e (ex-data e)))))
        _ (settle)
        c (v2/fork! w)
        ws {:root w :child c}]
    (checkpoint! sc ws :forked)
    (v2/write! (v2/in-world c s) 1)
    (Thread/sleep 300)
    (checkpoint! sc ws :entered)
    (v2/release-world! c) (v2/release-world! w)
    (settle)
    (checkpoint! sc ws :released)
    (finish! 53 ws sc acc)))

;; 54
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (let [d (in w #(v2/deferred))
        _ (in w #(task-with {:fork-local true} (try (await d) (finally :cleanup))))
        _ (settle)
        c (v2/fork! w)
        ws {:root w :child c}]
    (checkpoint! sc ws :forked)
    (v2/release-world! c)
    (v2/await-complete c 2000 :timeout)
    (checkpoint! sc ws :child-released)
    (v2/deliver! d 1)
    (v2/release-world! w)
    (settle)
    (checkpoint! sc ws :released)
    (finish! 54 ws sc acc)))

;; 55
(let [acc (atom []) sc (sidecar) w (vworld acc) kid (promise) refused (promise)]
  (let [d (in w #(v2/deferred))
        _ (in w #(task-with {:fork-local true}
                   (try (v2/fork) (catch Throwable e (deliver refused (ex-data e))))
                   (await d)))
        _ (settle)
        _ (in w #(task (let [[side c] (v2/fork)]
                         (if (= :parent side) (do (deliver kid c) (await d)) :child-side))))
        c (deref kid 2000 nil)
        _ (settle)
        ws {:root w :child c}]
    (prn :55-refused (deref refused 2000 :none))
    (checkpoint! sc ws :forked)
    (v2/release-world! c)
    (v2/deliver! d 1)
    (v2/release-world! w)
    (settle)
    (checkpoint! sc ws :released)
    (finish! 55 ws sc acc)))

;; 56
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (let [s (in w #(v2/signal 0))
        d (in w #(v2/deferred))
        _ (in w #(task (await d) :plain-done))
        _ (in w #(task-with {:fork-local true} (await d) :local-done))
        _ (settle)
        c (v2/fork! w)
        ws {:root w :child c}]
    (checkpoint! sc ws :forked)
    (v2/deliver! (v2/in-world c d) 1)
    (settle)
    (checkpoint! sc ws :entered)
    (v2/release-world! c) (v2/deliver! d 2) (v2/release-world! w)
    (settle)
    (checkpoint! sc ws :released)
    (finish! 56 ws sc acc)))

;; 57
(let [acc (atom []) sc (sidecar) w (vworld acc) pubs (atom [])]
  (v2/install-handlers! w {:sp (fn [pub] (swap! pubs conj pub))})
  (let [d (in w #(v2/deferred))
        _ (in w #(task-with {:fork-local true} (try (await d) (finally :sibling-finally))))
        _ (settle)
        h (in w #(task (inc (v2/savepoint :sp 1))))
        _ (settle)
        pub (first @pubs)
        inst (v2/instantiate pub)
        ws {:root w :instance inst}]
    (checkpoint! sc ws :instantiated)
    (v2/activate! inst 10)
    (prn :57-instance-value (v2/value (v2/in-world inst h) 1000 :timeout))
    (settle)
    (checkpoint! sc ws :activated)
    ;; a fork-local run's publication: instantiate is refused (a throw, no item)
    (let [lh (in w #(task-with {:fork-local true} (inc (v2/savepoint :sp 2))))
          _ (settle)
          lpub (second @pubs)]
      (prn :57-local-instantiate (try (v2/instantiate lpub) :accepted (catch clojure.lang.ExceptionInfo e (ex-data e))))
      (v2/resume! lpub 41)
      (prn :57-local-in-place (v2/value lh 1000 :timeout)))
    (v2/release-world! inst)
    (v2/await-complete inst 2000 :timeout)
    (v2/resume! pub 1)
    (v2/deliver! d 1)
    (v2/release-world! w)
    (settle)
    (checkpoint! sc ws :released)
    (finish! 57 ws sc acc)))

;; 58
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (let [d (in w #(v2/deferred))
        s (in w #(v2/signal 0))
        scope (promise) inner (promise) linner (promise)
        _ (in w #(task-with {:fork-local true}
                   (let [x (v2/open-scope!)] (deliver scope x) (await d) (v2/close-scope-fx! x))))
        _ (in w #(task (deliver inner (task (await d))) (await d)))
        _ (in w #(task-with {:fork-local true} (deliver linner (task (await d))) (await d)))
        k (deref inner 1000 nil)
        lk (deref linner 1000 nil)
        _ (settle)
        _ (v2/detach! k (deref scope 1000 nil))
        _ (v2/detach! lk (v2/root-scope w))
        _ (settle)
        _ (prn :58-marks (v2/fork-local? k) (v2/fork-local? lk))
        c (v2/fork! w)
        ws {:root w :child c}]
    (checkpoint! sc ws :forked)
    (v2/write! (v2/in-world c s) 1)
    (settle)
    (checkpoint! sc ws :entered)
    (v2/release-world! c) (v2/deliver! d 1) (v2/release-world! w)
    (settle)
    (checkpoint! sc ws :released)
    (finish! 58 ws sc acc)))

;; 59
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (let [d (in w #(v2/deferred))
        s (in w #(v2/signal 0))
        mb (promise) cp (promise)
        _ (in w #(task-with {:fork-local true} (deliver mb (v2/mailbox)) (deliver cp (spin 7)) (await d)))
        m (deref mb 1000 nil)
        cmp (deref cp 1000 nil)
        taker (in w #(task (try (v2/take! m) (catch Throwable e (ex-data e)))))
        _ (v2/observe! cmp (fn [_ _]))
        _ (settle)
        c (v2/fork! w)
        ws {:root w :child c}]
    (checkpoint! sc ws :forked)
    (v2/write! (v2/in-world c s) 1)
    (settle)
    (prn :59-child-taker (v2/value (v2/in-world c taker) 1000 :timeout))
    (checkpoint! sc ws :entered)
    (v2/release-world! c)
    (v2/post! m :x)
    (v2/deliver! d 1)
    (v2/release-world! w)
    (settle)
    (checkpoint! sc ws :released)
    (finish! 59 ws sc acc)))

;; 60
(let [acc (atom []) sc (sidecar) w (vworld acc)]
  (let [d (in w #(v2/deferred))
        lh (in w #(task-with {:fork-local true} (try (await d) (finally :loop-finally))))
        _ (in w #(task (try (await lh) (catch Throwable e (ex-data e)))))
        _ (settle)
        c (v2/fork! w)
        ws {:root w :child c}]
    (checkpoint! sc ws :forked)
    (v2/cancel-task! (v2/in-world c lh))
    (settle)
    (checkpoint! sc ws :cancelled)
    (v2/release-world! c) (v2/deliver! d 1) (v2/release-world! w)
    (settle)
    (checkpoint! sc ws :released)
    (finish! 60 ws sc acc)))
