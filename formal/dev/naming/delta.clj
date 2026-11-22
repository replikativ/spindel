;; The gate for a change after the naming pass (babashka): the difference between two outputs of
;; fingerprint.clj, constant by constant.
;;
;;   cd formal && bb dev/naming/delta.clj OLD.edn NEW.edn [MAP.edn]
;;
;; MAP.edn is an optional {old-name new-name} for a rename (a dotted name follows its first
;; component, as in compare.clj). Without it the names are compared as they are. Prints the
;; constants removed, added and changed (same name, other fingerprint), the removed and added
;; ones grouped by their first component, and the headline theorems. A pure rename shows nothing
;; removed, added or changed; a deletion shows exactly the deleted constants removed.
(require '[clojure.edn :as edn] '[clojure.string :as str])
(let [[fo fn- fm] *command-line-args*
      old (edn/read-string (slurp fo)) new (edn/read-string (slurp fn-))
      m (if fm (into {} (for [[a b] (edn/read-string (slurp fm))] [(str a) (str b)])) {})
      head (fn [s] (let [i (.indexOf ^String s ".")] (if (neg? i) s (subs s 0 i))))
      rn (fn [s] (let [h (head s)] (str (m h h) (subs s (count h)))))
      o (into {} (for [[k v] (:fp old)] [(rn k) v])) n (:fp new)
      removed (sort (remove n (keys o))) added (sort (remove o (keys n)))
      changed (sort (for [[k v] o :when (and (contains? n k) (not= v (n k)))] k))
      groups (fn [xs] (str/join " " (for [[h ys] (sort-by key (group-by head xs))]
                                      (if (= [h] ys) h (str h "(+" (count (remove #{h} ys)) (when-not (some #{h} ys) ", not itself") ")")))))
      headline ["inv-step" "reach-inv" "inv-empty" "sys-reach-inv" "l5-safety-total" "step-chain" "mv-refinement"]]
  (println "constants: before" (:count old) "after" (:count new) "| load seconds: before" (:load-seconds old) "after" (:load-seconds new))
  (println "renamed by the map:" (count (filter #(not= % (rn %)) (keys (:fp old)))) "| names merged by the map:" (- (count (:fp old)) (count o)))
  (println "removed:" (count removed) "in" (count (distinct (map head removed))) "groups:" (groups removed))
  (println "added:" (count added) "in" (count (distinct (map head added))) "groups:" (groups added))
  (println "same name, different fingerprint:" (count changed) (pr-str (take 60 changed)))
  (doseq [h headline] (println "  headline" h (cond (not (contains? n h)) "MISSING" (= (o h) (n h)) "unchanged" :else "CHANGED"))))
