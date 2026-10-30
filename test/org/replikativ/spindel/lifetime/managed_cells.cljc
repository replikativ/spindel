(ns org.replikativ.spindel.lifetime.managed-cells
  "Host collection receipts for ordinary managed atom storage. A receipt means
  every supported wrapper of this allocation is unreachable, not just its creator.")

(defn current? [s {:keys [w e allocation]}]
  (let [row (get-in s [:worlds w :entities e])]
    (and (#{:atom :deferred} (:kind row)) (some? allocation)
         (= allocation (:allocation row)))))

(defn unreachable [s {:keys [w e allocation] :as action}]
  (if (current? s action)
    (assoc-in s [:env :source-gc [w e allocation]] true) s))

(defn- backing-world [s v e]
  (loop [v v seen #{}]
    (when (and v (not (seen v)))
      (let [world (get-in s [:worlds v])]
        (cond
          (get-in world [:entities e]) v
          (= :following (get-in world [:lineage :mode]))
          (recur (get-in world [:lineage :parent]) (conj seen v)))))))

(defn in-use? [s w e allocation]
  (or (contains? (get-in s [:worlds w :pins]) e)
      (seq (get-in s [:env :cell-claims [w e allocation]]))
      (some (fn [[reg {:keys [operation sequence]}]]
              (let [ticket (get-in s [:env :native (first operation)])
                    participant (:operation ticket)]
                (and (= operation (:id participant)) (= :open (:state participant))
                     (= sequence (:sequence ticket))
                     (= :pending (get-in participant [:registrations reg :state])))))
            (get-in s [:worlds w :entities e :deferred :protected]))
      (some (fn [[v world]]
              (or (some #(= [:entity w e] (:debtor %)) (vals (:obligations world)))
                  (some #(or (and (= e (:completion %)) (= w (get % :debtor-world v)))
                             (and (= w v) (= e (:deferred-assignment %)) (= allocation (:allocation %))))
                        (concat (:queue world)
                                (map :event (filter #(= v (:w %)) (get-in s [:env :outside])))))
                  ;; Fdeps live on the debtor world; bundles name debtor IDs.
                  (and (= v w)
                       (some (fn [[x _ debtors]] (if (= :bundle x) (contains? debtors e) (= x e)))
                             (:fdeps world)))
                  ;; A local source copy is independent, even when inherited.
                  (and (not= v w) (not= :released (:status world))
                       (= w (backing-world s v e)))))
            (:worlds s))))

(defn reap [s {:keys [w e allocation] :as action}]
  (let [receipt [w e allocation]]
    (if-not (get-in s [:env :source-gc receipt]) s
            (if-not (current? s action)
              (update-in s [:env :source-gc] dissoc receipt)
              (do
                (when (in-use? s w e allocation)
                  (throw (ex-info "source-in-use"
                                  {:error :org.replikativ.spindel.lifetime.model/source-in-use
                                   :w w :e e :allocation allocation})))
                (-> s
                    (update-in [:env :source-gc] dissoc receipt)
                    (update-in [:worlds w :entities] dissoc e)
                    (update-in [:worlds w :runs]
                               #(into {} (map (fn [[r row]] [r (update row :creations disj e)]) %)))))))))
