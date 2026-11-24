;; Adoption follows the model (phase-d design §1.2 R2/R3): oracle log samples 69-70.
;;
;; 69  w: a kind mismatch then a rerun. Body sources share site -1: run 1 creates a signal (ord 0) and a mailbox
;;     (ord 1); run 2 creates only the mailbox, at ord 0, which rejects the signal (T1: same kind) and is a new
;;     source; the signal stays in the adoption basis until the run's T12. Run 3 readopts the mailbox. The runs
;;     complete (no await after the re-entry site: an awaited deferred there leaves an engine baseline the model
;;     does not have, a separate divergence).
;; 70  w: a task with changed captures and a sequence with a changed initial state: the spawn and the link
;;     creation are fresh rows; the predecessors stay in the adoption basis (no cancel in the spawn's item) until
;;     the run's T12 (its complete item) cancels the task and releases both.
;;
;; From the repository root (one -Xmx1g JVM):
;;   clojure -J-Xmx1g -Sdeps '{:paths ["src" "test"]}' -M -i formal/test/spindel/v2/oracle/gen/samples-adoption.clj
;; Generated logs are registered in oracle_test.clj (`adoption-specs`).
(ns samples-adoption
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await aseq]]
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
