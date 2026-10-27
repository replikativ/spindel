(ns org.replikativ.spindel.lifetime-gate-rules
  "Pure gate comparisons, runnable with Babashka. Thresholds are plan §2.3.")

(def fixture-dimensions
  {:small {:live-worlds 1000 :entities 0 :parked-runs 0}
   :large {:live-worlds 5000 :entities 0 :parked-runs 0}
   :populated {:live-worlds 1000 :entities 10000 :parked-runs 1000}})

(def census-paths
  [[:nodes] [:atoms] [:spins-meta] [:await-conts] [:track-subscriptions]
   [:subscriptions] [:spin-tracking] [:incremental] [:pending-callbacks] [:run-callbacks]
   [:engine/spawned] [:engine/pending] [:engine/delayed-spins] [:engine/timer-handles]
   [:engine/retired-conts] [:addressing :chain-heads] [:addressing :occurrences]
   [:following-worlds-live]])

(def required-empty
  (set (remove #{[:addressing :chain-heads] [:addressing :occurrences]} census-paths)))

(def protocol-version 2)
(def measurement-protocol
  {:fork {:warmup 200 :operations 1000 :samples 3
          :order [:small :large :populated :large :populated :small :populated :small :large]}
   :lifecycle {:warm-shapes 1000 :warmup 2000 :operations 5000 :samples 3}
   :enumeration {:warmup 2000 :checkpoints [10000 100000]}
   :gc {:stable-samples 3 :sample-pause-ms 500 :deadline-ms 30000 :heap-tolerance 0.005
        :census-paths census-paths :required-empty required-empty}})

(def metadata-fields
  [:machine :max-heap-bytes :executor :allocation :java :java-vendor :os :os-version :arch
   :processors :jvm-options :protocol-version :measurement-protocol :admission])

(defn stable-observations? [observations required-empty]
  (let [last-three (take-last 3 observations)
        heaps (map :heap-bytes last-three)]
    (and (= 3 (count last-three))
         (every? :gc-completed? last-three)
         (every? #(every? (fn [k] (= 0 (get (:census %) k))) required-empty) last-three)
         (apply = (map :census last-three))
         (<= (- (apply max heaps) (apply min heaps))
             (* (get-in measurement-protocol [:gc :heap-tolerance]) (apply max heaps))))))

(defn measurement-stable? [point required]
  (and (:gc-stable? point) (:gc-completed? point) (:cleanup-complete? point)
       (= required (:expected-empty point))
       (stable-observations? (:observations point) required)))

(defn validate! [baseline candidate]
  (doseq [data [baseline candidate]]
    (when-not (and (= protocol-version (:protocol-version data))
                   (= measurement-protocol (:measurement-protocol data))
                   (every? #(and (contains? data %) (some? (get data %))) metadata-fields)
                   (= #{:L0 :L-child :L2-await :L2-track} (set (map :lifecycle (:lifecycle data))))
                   (= 4 (count (:lifecycle data)))
                   (map? (:fork data)) (= (set (keys fixture-dimensions)) (set (keys (:fork data))))
                   (every? (fn [[id dimensions]]
                             (let [row (get-in data [:fork id])]
                               (and (= id (:fixture row)) (= dimensions (select-keys row (keys dimensions)))
                                    (= 3 (count (:samples row)))
                                    (every? #(and (= id (:fixture %))
                                                  (= dimensions (select-keys % (keys dimensions)))
                                                  (= 1000 (:operations %))) (:samples row))))) fixture-dimensions)
                   (= #{:fork :spin} (set (map :kind (:enumeration data))))
                   (= 2 (count (:enumeration data)))
                   (every? #(= [10000 100000] (mapv :cycles (:points %))) (:enumeration data))
                   (every? #(and (seq (:observations %)) (contains? % :cleanup-complete?)
                                 (contains? % :gc-wait-ms) (contains? % :gc-completed?))
                           (mapcat :points (:enumeration data))))
      (throw (ex-info "Incomplete benchmark report or wrong measurement protocol" {:type ::incomplete}))))
  (doseq [field metadata-fields]
    (when-not (= (get baseline field) (get candidate field))
      (throw (ex-info "Incomparable benchmark metadata" {:type ::incomparable :field field})))))

(defn ratio-gate [name value limit]
  {:gate name :value value :limit limit :pass? (<= value limit)})

(defn evaluate [baseline candidate]
  (validate! baseline candidate)
  (let [base-life (into {} (map (juxt :lifecycle identity) (:lifecycle baseline)))
        forks (:fork candidate)
        small (:small forks) large (:large forks) populated (:populated forks)
        base-enum (into {} (map (juxt :kind identity) (:enumeration baseline)))]
    (vec
     (concat
      (mapcat (fn [row]
                (let [k (:lifecycle row) b (base-life k)]
                  [(ratio-gate [k :time-ratio] (/ (:us-per-spin row) (:us-per-spin b)) 1.10)
                   (ratio-gate [k :extra-bytes] (* 1024 (- (:kb-per-spin row) (:kb-per-spin b))) 64)]))
              (:lifecycle candidate))
      [{:gate [:fork :gc-stable]
        :pass? (every? #(measurement-stable? (:post-fixture-gc %) #{}) (mapcat :samples (vals forks)))}]
      (for [metric [:ns-per-op :bytes-per-op]]
        (ratio-gate [:fork :world-scaling metric] (/ (metric large) (metric small)) 1.5))
      ;; The plan says "or growing with parent size" without a numeric noise
      ;; allowance. Apply the stated condition literally, and show the ratio.
      (for [metric [:ns-per-op :bytes-per-op]]
        (ratio-gate [:fork :parent-scaling metric] (/ (metric populated) (metric small)) 1.0))
      (mapcat (fn [{:keys [kind points cycles-per-second]}]
                [{:gate [kind :gc-stable] :pass? (every? #(measurement-stable? % required-empty) points)}
                 (ratio-gate [kind :retained-ratio]
                             (/ (double (:retained-bytes (second points)))
                                (:retained-bytes (first points))) 1.05)
                 (ratio-gate [kind :throughput-ratio]
                             (/ (:cycles-per-second (base-enum kind)) cycles-per-second)
                             (/ 1.0 0.9))]) (:enumeration candidate))))))
