;; Merge log sample for the layer-2 oracle (sample 17): the parent's log and the child's own log.
;; From the repository root: clojure -M:bench -i formal/test/spindel/v2/oracle/gen/samples-merge.clj
(require 'org.replikativ.spindel.v2.group-test 'clojure.pprint)
(in-ns 'org.replikativ.spindel.v2.group-test)
(def dir (or (System/getenv "SAMPLE_DIR") "formal/test/spindel/v2/oracle/"))
(defn dump! [path l] (spit path (with-out-str (clojure.pprint/pprint l))) [path (count l) (frequencies (map (comp first :item) l))])

;; 17: a mergeable host fork. The child writes signals s (twice) and t; the parent writes u; the
;; merge adopts s and t as two host writes in the parent, whose observed computation reruns; the
;; child is released.
(let [acc (atom [])
      w (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))})]
  (binding [v2/*world* w]
    (let [s (v2/signal 1) t (v2/signal 2) u (v2/signal 3)
          c (spin (+ (iv/get-new (track s)) (iv/get-new (track t))))
          stop (v2/observe! c (fn [_ _]))
          child (v2/fork! w {:mergeable? true})]
      (v2/write! (v2/in-world child s) 10)
      (v2/write! (v2/in-world child s) 11)
      (v2/write! (v2/in-world child t) 20)
      (binding [v2/*world* child] (v2/value (v2/in-world child c) 1000 :timeout))
      (v2/write! u 30)
      (let [cl (verify/log child)]
        (prn :merged (v2/merge! w child))
        (v2/value c 1000 :timeout)
        (Thread/sleep 100)
        (prn (dump! (str dir "log-sample-17-parent.edn") (verify/log w)))
        (prn (dump! (str dir "log-sample-17-child.edn") cl))
        (prn :divergences @acc)))))
(shutdown-agents)
