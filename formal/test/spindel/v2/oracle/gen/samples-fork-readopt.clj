;; Readoption in a fork (Z#29, §8.1): oracle log sample 80.
;;
;; 80  root, child: the root's computation tracks a signal and awaits a child computation `a`. A host fork; the
;;     child observes its copy and writes the signal: its rerun readopts the inherited `a`. The copy has no handle
;;     object in the child (handles are per world), so the child's readoption makes one, which takes over the
;;     inherited count: `a` keeps one handle and no `[:handle-new]` item. The child then writes a value at which
;;     the computation no longer creates `a`: T12 releases it, and once the child's handle is collected
;;     (`[:handle-drop a]`) it is removed in the child. The root keeps its own `a`.
;;
;; From the repository root (one -Xmx1g JVM):
;;   clojure -J-Xmx1g -Sdeps '{:paths ["src" "test"]}' -M -i formal/test/spindel/v2/oracle/gen/samples-fork-readopt.clj
;; Generated logs are registered in oracle_test.clj (`sample-80-fork-readoption`).
(ns samples-fork-readopt
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [spin track await]]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]
            [clojure.pprint]))

(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l]
  (spit path (with-out-str (clojure.pprint/pprint l)))
  [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld [acc] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))}))

;; 80
(let [acc (atom []) w (vworld acc)
      [s c] (binding [v2/*world* w]
              (let [s (v2/signal 0)]
                [s (spin (let [v (iv/get-new (track s))]
                           (if (< v 2) (+ v (await (spin 1))) v)))]))]
  (v2/observe! c (fn [_ _]))
  (assert (= 1 (v2/value c 2000 :timeout)))
  (let [child (v2/fork! w)
        cc (v2/in-world child c)]
    (v2/observe! cc (fn [_ _]))
    (v2/write! (v2/in-world child s) 1)
    (assert (= 2 (v2/value cc 2000 :timeout)))
    (v2/write! (v2/in-world child s) 2)
    (assert (= 2 (v2/value cc 2000 :timeout)))
    (verify/gc-settle! child)
    (v2/release-world! child)
    (assert (true? (v2/await-complete child 2000 :timeout)) "the child completes")
    (v2/release-world! w)
    (assert (true? (v2/await-complete w 2000 :timeout)) "the world completes")
    (prn (dump! (str dir "log-sample-80-root.edn") (verify/log w)))
    (prn (dump! (str dir "log-sample-80-child.edn") (verify/log child)))
    (prn :sample 80 :divergences @acc)))
