;; Adoption follows the model (phase-d design §1.2 R2/R3): oracle log samples 68-72.
;;
;; 68  w: two interrupted reruns that do not re-create. Run 1 spawns two tasks; runs 2 and 3 do not, and park on
;;     an empty mailbox (a wait edge: no baseline). The second cut replaces the adoption basis with the empty
;;     suffix: the task nothing else retains is cancelled in that dispatch item (Rule R); the one another
;;     computation awaits keeps running.
;; 69  w: a kind mismatch then a rerun. Body sources share site -1: run 1 creates a signal (ord 0) and a mailbox
;;     (ord 1); run 2 creates only the mailbox, at ord 0, which rejects the signal (T1: same kind) and is a new
;;     source; the signal stays in the adoption basis until the run's T12. Run 3 readopts the mailbox. The runs
;;     complete (no await after the re-entry site: an awaited deferred there leaves an engine baseline the model
;;     does not have, a separate divergence).
;; 70  w: a task with changed captures and a sequence with a changed initial state: the spawn and the link
;;     creation are fresh rows; the predecessors stay in the adoption basis (no cancel in the spawn's item) until
;;     the run's T12 (its complete item) cancels the task and releases both.
;; 71  w: the cut keeps baselines only for edges that have one (`bases-of` over `has-base`: tracks, awaits of
;;     signals and cells, delivered awaits re-armed with their result). Run 1 awaits a computation (delivered),
;;     tracks a signal and awaits a deferred (pending) after its re-entry site; run 2 does none of it and parks on a
;;     mailbox take (a wait edge). The dispatch item keeps the baselines of the signal and the computation only.
;; 72  w: demotion of parked computations that never completed and have a handle (§3.3): observe, then unobserve.
;;     x awaits a deferred: its run retires at the cancel, the epoch does not step, the validity fails (the
;;     edge never consumed a version). z tracks a signal and parks on a mailbox take: its validity is the
;;     consumed track. (A run kept in cleanup is left out: the engine keeps C.run on the idle computation,
;;     the model clears it, a separate divergence.)
;;
;; From the repository root (one -Xmx1g JVM):
;;   clojure -J-Xmx1g -Sdeps '{:paths ["src" "test"]}' -M -i formal/test/spindel/v2/oracle/gen/samples-adoption.clj
;; Generated logs are registered in oracle_test.clj (`adoption-specs`).
(ns samples-adoption
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await aseq take!]]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]
            [clojure.pprint]))

(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l]
  (spit path (with-out-str (clojure.pprint/pprint l)))
  [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld [acc] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))}))
(defn- in [w g] (binding [v2/*world* w] (g)))

(defn finish! [n w acc]
  (v2/release-world! w)
  (assert (true? (v2/await-complete w 2000 :timeout)) "the world completes")
  (prn (dump! (str dir "log-sample-" n "-w.edn") (verify/log w)))
  (prn :sample n :divergences @acc))

;; 68
(let [acc (atom []) w (vworld acc) held (atom nil)
      [s c o] (in w #(let [s (v2/signal 0)
                           mb (v2/mailbox)
                           c (spin (let [v (iv/get-new (track s))]
                                     (when (zero? v)
                                       (task (take! mb))
                                       (reset! held (task (take! mb))))
                                     (take! mb)))]
                       (v2/observe! c (fn [_ _]))
                       [s c (spin (await @held))]))]
  (v2/observe! o (fn [_ _]))
  (v2/write! s 1)
  (v2/write! s 2)
  (finish! 68 w acc))

;; 69
(let [acc (atom []) w (vworld acc)
      [s c] (in w #(let [s (v2/signal 0)]
                     [s (spin (let [v (iv/get-new (track s))
                                    a (when (zero? v) (v2/signal 0))
                                    m (v2/mailbox)]
                                v))]))]
  (v2/observe! c (fn [_ _]))
  (v2/write! s 1)
  (v2/write! s 2)
  (finish! 69 w acc))

;; 70
(let [acc (atom []) w (vworld acc)
      [s c] (in w #(let [s (v2/signal 0)
                         never (v2/deferred)]
                     [s (spin (let [v (iv/get-new (track s))
                                    k (task (await never) v)
                                    xs (aseq [n v] [n (inc n)])]
                                v))]))]
  (v2/observe! c (fn [_ _]))
  (v2/write! s 1)
  (finish! 70 w acc))

;; 71
(let [acc (atom []) w (vworld acc)
      s (in w #(let [s (v2/signal 0)
                     t (v2/signal 0)
                     d (v2/deferred)
                     mb (v2/mailbox)
                     y (spin (iv/get-new (track t)))
                     c (spin (let [v (iv/get-new (track s))]
                               (when (zero? v)
                                 (await y)
                                 (iv/get-new (track t))
                                 (await d))
                               (take! mb)))]
                 (v2/observe! c (fn [_ _]))
                 s))]
  (v2/write! s 1)
  (finish! 71 w acc))

;; 72
(let [acc (atom []) w (vworld acc)
      [x z] (in w #(let [d (v2/deferred)
                         t (v2/signal 0)
                         mb (v2/mailbox)]
                     [(spin (await d))
                      (spin (iv/get-new (track t)) (take! mb))]))]
  (doseq [c [x z]] ((v2/observe! c (fn [_ _]))))
  (finish! 72 w acc)
  (prn :kept (every? some? [x z])))
