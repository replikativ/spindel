(ns org.replikativ.spindel.versioned-store-spike
  "Physical publication probe: one immutable store head for related worlds.
  Rows are generic; this does not implement the lifetime transitions."
  (:require [org.replikativ.spindel.lifetime.model :as model]))

(def ^:private deleted ::deleted)

(defn new-store []
  (atom {:epoch 0 :worlds {[:w 0] {:mode :root :rows {}}}}))

(defn- pin-view [head world-id]
  (let [world (get-in head [:worlds world-id])]
    (case (:mode world)
      :root world
      :following (assoc world :mode :frozen
                        :basis (pin-view head (:parent world)))
      :frozen world)))

(defn fork!
  "Publish a child. Frozen bases pin only their read-through lineage."
  [store parent-id child-id mode]
  (swap! store
         (fn [head]
           (let [child (case mode
                         :frozen {:mode mode :rows {}
                                  :basis (pin-view head parent-id)}
                         :following {:mode mode :rows {}
                                     :parent parent-id})]
             (-> head
                 (assoc-in [:worlds child-id] child)
                 (update :epoch inc))))))

(defn- read-view [head world id]
  (let [rows (:rows world)]
    (if (contains? rows id)
      (let [value (get rows id)]
        (when-not (= deleted value) value))
      (case (:mode world)
        :root nil
        :following (read-view head (get-in head [:worlds (:parent world)]) id)
        :frozen (read-view head (:basis world) id)))))

(defn read-row
  "Pass one committed store head to make a multi-row read consistent."
  [head world-id id]
  (read-view head (get-in head [:worlds world-id]) id))

(defn- edit-rows [world edits]
  (let [rows (:rows world)
        root? (= :root (:mode world))]
    (if (= 1 (count edits))
      (let [[op id value] (first edits)]
        (assoc world :rows (case op
                             :put (assoc rows id value)
                             :delete (if root? (dissoc rows id)
                                         (assoc rows id deleted)))))
      (assoc world :rows
             (persistent!
              (reduce (fn [draft [op id value]]
                        (case op
                          :put (assoc! draft id value)
                          :delete (if root? (dissoc! draft id)
                                      (assoc! draft id deleted))))
                      (transient rows) edits))))))

(defn transact!
  "One publication for all edited worlds. Edits are generic row operations."
  [store edits-by-world]
  (swap! store
         (fn [head]
           (reduce-kv (fn [head world-id edits]
                        (update-in head [:worlds world-id] edit-rows edits))
                      (update head :epoch inc)
                      edits-by-world))))

(defn verify!
  "Check frozen, following, nested, shadow and atomic multi-world publication."
  []
  (let [store (new-store)
        w [:w 0]
        v [:w 1]
        f [:w 2]
        _ (transact! store {w [[:put :a 1] [:put :b 2]]})
        before @store]
    (fork! store w v :following)
    (fork! store v f :frozen)
    (transact! store {w [[:put :a 3] [:put :c 4]]
                      v [[:put :a 5] [:delete :b nil]]})
    (let [after @store]
      (assert (= 1 (read-row before w :a)))
      (assert (= 3 (read-row after w :a)))
      (assert (= 5 (read-row after v :a)))
      (assert (nil? (read-row after v :b)))
      (assert (= 1 (read-row after f :a)))
      (assert (= 2 (read-row after f :b)))
      (assert (= 4 (read-row after v :c)))
      (assert (= (+ 3 (:epoch before)) (:epoch after))))
    true))

(defn verify-model!
  "Compare T2/T19/signal-write following read-through with the model."
  []
  (let [store (new-store)
        w [:w 0]
        v [:w 1]
        e [:signal 0]
        _ (transact! store {w [[:put e 1]]})
        s0 (model/step (model/init-state) {:t :t02 :w w :e e :value 1})
        _ (fork! store w v :following)
        s1 (model/step s0 {:t :t19 :w w :v v :k [:k 0]
                           :scope [:root w] :systems #{}})
        model-read (fn [s]
                     (get-in s [:worlds (model/read-source s v e)
                                :entities e :result]))]
    (assert (= (model-read s1) (read-row @store v e)))
    (transact! store {w [[:put e 2]]})
    (let [s2 (model/step s1 {:t :signal-write :w w :e e :value 2})]
      (assert (= (model-read s2) (read-row @store v e)))
      (transact! store {v [[:put e 3]]})
      (let [s3 (model/step s2 {:t :t02 :w v :e e :value 3})]
        (assert (= (model/read-source s3 v e) v))
        (assert (= (model-read s3) (read-row @store v e)))))
    true))

(defn verify-foreign-model!
  "Check that T5's creditor obligation and foreign debtor retention can be
  published together, with neither half visible in the preceding revision."
  []
  (let [w [:w 0]
        v [:w 1]
        e [:signal 0]
        p [:spin 0]
        o [:o 1]
        fdep [e v o]
        s0 (model/step (model/init-state) {:t :t02 :w w :e e :value 1})
        s1 (model/step s0 {:t :t19 :w w :v v :k [:k 0]
                           :scope [:root w] :systems #{}})
        s2 (model/step s1 {:t :t04 :w v :e p :mode :callback})
        s3 (model/step s2 {:t :t05 :w v :r [p 1] :kind :track
                           :debtor [:entity w e]})
        store (new-store)
        _ (fork! store w v :following)
        before @store
        _ (transact! store {v [[:put [:obligation o]
                                (get-in s3 [:worlds v :obligations o])]]
                            w [[:put [:fdep fdep] true]]})
        after @store]
    (assert (contains? (get-in s3 [:worlds w :fdeps]) fdep))
    (assert (nil? (read-row before v [:obligation o])))
    (assert (nil? (read-row before w [:fdep fdep])))
    (assert (= (get-in s3 [:worlds v :obligations o])
               (read-row after v [:obligation o])))
    (assert (true? (read-row after w [:fdep fdep])))
    true))
