;; Naming pass, the gate (babashka): compare two outputs of fingerprint.clj.
;;
;;   cd formal && bb dev/naming/compare.clj OLD.edn NEW.edn
;;
;; OLD was written before the substitution, NEW after it. OLD's names are mapped through
;; notes/renames.edn (a dotted name by its first component). The gate holds when both then name
;; the same constants with the same fingerprints.
(require '[clojure.edn :as edn] '[clojure.set :as set] '[clojure.string :as str])
(let [[fo fn-] *command-line-args*
      old (edn/read-string (slurp fo)) new (edn/read-string (slurp fn-))
      ren (edn/read-string (slurp "notes/renames.edn"))
      m (into {} (for [k [:definitions :theorems :generated] [a b] (ren k)] [(str a) (str b)]))
      rn (fn [s] (let [i (.indexOf ^String s ".")]
                   (if (neg? i) (m s s) (str (m (subs s 0 i) (subs s 0 i)) (subs s i)))))
      deleted (set (map str (:deleted ren)))
      o (into {} (for [[k v] (:fp old) :when (not (deleted k))] [(rn k) v])) n (:fp new)
      _ (println "deleted:" (count deleted) "| names merged by the map:" (- (count (remove deleted (keys (:fp old)))) (count o)))
      missing (sort (remove n (keys o))) extra (sort (remove o (keys n)))
      differ (sort (for [[k v] o :when (and (contains? n k) (not= v (n k)))] k))
      predicted (set (map str (vals (:generated ren))))
      headline ["inv-step" "reach-inv" "inv-empty" "sys-reach-inv" "l5-safety-total"
                (rn "step-p3m") "mv-refinement"]]
  (println "constants: before" (:count old) "after" (:count new) "| load seconds: before" (:load-seconds old) "after" (:load-seconds new))
  (println "fingerprint multiset identical:" (= (frequencies (vals o)) (frequencies (vals n))))
  (println "names expected but missing after:" (count missing) (pr-str (take 40 missing)))
  (println "names after that were not expected:" (count extra) (pr-str (take 40 extra)))
  (println "same name, different fingerprint:" (count differ) (pr-str (take 40 differ)))
  (println "predicted generated names:" (count predicted) "| present after:" (count (filter n predicted))
           "| absent:" (pr-str (take 40 (sort (remove n predicted)))))
  (doseq [h headline] (println "  headline" h (cond (not (contains? n h)) "MISSING" (= (o h) (n h)) "unchanged" :else "CHANGED")))
  (let [ok (and (empty? missing) (empty? extra) (empty? differ) (= (count o) (count (remove deleted (keys (:fp old))))))]
    (println (if ok "GATE: pass" "GATE: FAIL"))
    (System/exit (if ok 0 1))))
