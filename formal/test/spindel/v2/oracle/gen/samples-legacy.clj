;; Sample 7 (Z#48/Z#49), regenerated for C1 A5 (`[:finally-leave r]`, spindel PR #268): the scenario
;; of ../spindel-v2/.internal/oracle/samples.clj. Samples 4 and 5 have no generator (engine
;; a28563d, hand-driven); the oracle reads their clauses as ending within the exit's commit.
;; From the repository root: clojure -M:bench -i formal/test/spindel/v2/oracle/gen/samples-legacy.clj
(require 'org.replikativ.spindel.v2.group-test 'clojure.pprint)
(in-ns 'org.replikativ.spindel.v2.group-test)
(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l] (spit path (with-out-str (clojure.pprint/pprint l))) [path (count l) (frequencies (map (comp first :item) l))])

;; 7: Z#48 track on a closed source; Z#49 slice-exit of a cancelled run unwinding its finally
;; (retired within the item, Z#51)
(let [acc (atom [])
      w (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))})]
  (binding [v2/*world* w]
    (let [out (atom nil)
          t (task (reset! out (v2/signal 1)) :made)
          _ (v2/value t 1000 :timeout)
          s @out
          c (spin (* 2 (iv/get-new (track s))))
          u (v2/observe! c (fn [_ _]))
          d (v2/deferred)
          k (task (try (await d) (finally nil)))]
      (v2/cancel-task! k)
      (v2/value (v2/signal 0) 100 nil)
      (u)))
  (prn (dump! (str dir "log-sample-7.edn") (verify/log w)))
  (prn :divergences @acc))
