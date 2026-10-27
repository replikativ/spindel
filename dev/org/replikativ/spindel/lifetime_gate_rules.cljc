(ns org.replikativ.spindel.lifetime-gate-rules
  "Pure gate comparisons, runnable with Babashka. Thresholds are plan §2.3.")

(defn validate! [baseline candidate]
  (doseq [data [baseline candidate]]
    (when-not (and (= #{:L0 :L-child :L2-await :L2-track} (set (map :lifecycle (:lifecycle data))))
                   (= 4 (count (:lifecycle data)))
                   (= 3 (count (:fork data)))
                   (= #{:fork :spin} (set (map :kind (:enumeration data))))
                   (= 2 (count (:enumeration data)))
                   (every? #(= [10000 100000] (mapv :cycles (:points %))) (:enumeration data)))
      (throw (ex-info "Incomplete benchmark report" {:type ::incomplete}))))
  (doseq [field [:machine :max-heap-bytes :executor :allocation :gc]]
    (when-not (= (field baseline) (field candidate))
      (throw (ex-info "Incomparable benchmark metadata" {:type ::incomparable :field field})))))

(defn ratio-gate [name value limit]
  {:gate name :value value :limit limit :pass? (<= value limit)})

(defn evaluate [baseline candidate]
  (validate! baseline candidate)
  (let [base-life (into {} (map (juxt :lifecycle identity) (:lifecycle baseline)))
        forks (:fork candidate)
        small (first forks) large (second forks) populated (nth forks 2)
        base-enum (into {} (map (juxt :kind identity) (:enumeration baseline)))]
    (vec
     (concat
      (mapcat (fn [row]
                (let [k (:lifecycle row) b (base-life k)]
                  [(ratio-gate [k :time-ratio] (/ (:us-per-spin row) (:us-per-spin b)) 1.10)
                   (ratio-gate [k :extra-bytes] (* 1024 (- (:kb-per-spin row) (:kb-per-spin b))) 64)]))
              (:lifecycle candidate))
      (for [metric [:ns-per-op :bytes-per-op]]
        (ratio-gate [:fork :world-scaling metric] (/ (metric large) (metric small)) 1.5))
      ;; The plan says "or growing with parent size" without a numeric noise
      ;; allowance. Apply the stated condition literally, and show the ratio.
      (for [metric [:ns-per-op :bytes-per-op]]
        (ratio-gate [:fork :parent-scaling metric] (/ (metric populated) (metric small)) 1.0))
      (mapcat (fn [{:keys [kind points cycles-per-second]}]
                [{:gate [kind :gc-stable] :pass? (every? :gc-stable? points)}
                 (ratio-gate [kind :retained-ratio]
                             (/ (double (:retained-bytes (second points)))
                                (:retained-bytes (first points))) 1.05)
                 (ratio-gate [kind :throughput-ratio]
                             (/ (:cycles-per-second (base-enum kind)) cycles-per-second)
                             (/ 1.0 0.9))]) (:enumeration candidate))))))
