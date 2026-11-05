(ns org.replikativ.spindel.v2.lifetime-model-test
  "Finite ownership/sweep model, independent of host GC and implementation."
  (:require [clojure.test :refer [deftest is]]
            [clojure.set :as set]))

(defn- reachable [roots strong]
  (loop [seen #{} todo (set roots)]
    (if (empty? todo) seen
        (recur (into seen todo) (set/difference (into #{} (mapcat strong) todo) seen todo)))))

(deftest object-owned-callback-cycles-have-no-metadata-root
  ;; Two aliases strongly own a capsule; a callback can capture either alias.
  ;; Family/index/Cleaner edges are weak and therefore absent from `strong`.
  (let [strong {:alias-a #{:capsule} :alias-b #{:capsule}
                :capsule #{:callback} :callback #{:alias-a}
                :atom #{:atom-owner} :atom-owner #{:atom-capsule}
                :atom-capsule #{:atom-callback} :atom-callback #{:atom}}]
    (is (contains? (reachable #{:alias-b} strong) :callback))
    (is (empty? (reachable #{} strong)))
    (is (not (contains? (reachable #{:family :index :cleaner} strong) :capsule)))
    (is (not (contains? (reachable #{:family :index :cleaner} strong) :atom)))))

(defn- permutations [xs]
  (if (empty? xs) [[]]
      (for [x xs more (permutations (remove #{x} xs))] (cons x more))))

(defn- request [s w]
  (if (get-in s [:worlds w :released?]) s
      (assoc-in s [:worlds w :pending?] true)))

(defn- transition [s op]
  (case op
    :collect (-> s (update :dead conj :a) (update :generation inc))
    :snapshot (assoc s :snapshot (set (keys (:worlds s))))
    :deliver (reduce request s (:snapshot s))
    :fork-snapshot (assoc s :fork (get-in s [:worlds :parent]))
    :fork-register (if-let [f (:fork s)] (assoc-in s [:worlds :fork] (assoc f :pending? false :scan nil)) s)
    :fork-check (if (and (get-in s [:worlds :fork])
                         (< (get-in s [:worlds :fork :last]) (:generation s)))
                  (request s :fork) s)
    :reset (if (get-in s [:worlds :idle :pending?])
             (-> s (assoc-in [:worlds :idle :pending?] false)
                 (assoc-in [:worlds :idle :scan] :reading)) s)
    :read (if (= :reading (get-in s [:worlds :idle :scan]))
            (assoc-in s [:worlds :idle :scan] (:generation s)) s)
    :finish (let [g (get-in s [:worlds :idle :scan])]
              (if (number? g)
                (-> s (update-in [:worlds :idle :entries] set/difference (:dead s))
                    (assoc-in [:worlds :idle :last] g) (assoc-in [:worlds :idle :scan] nil)) s))
    :release (assoc-in s [:worlds :parent] {:released? true :entries #{} :last (:generation s)})
    s))

(defn- fair-drain [s]
  ;; Finish only scans/requests already present. Fairness must not invent a
  ;; new request that could conceal a lost registration/collection wakeup.
  (reduce-kv (fn [s w row]
               (if (or (:released? row) (not (or (:pending? row) (:scan row)))) s
                   (assoc-in s [:worlds w]
                             (assoc row :entries (set/difference (:entries row) (:dead s))
                                    :last (:generation s) :pending? false :scan nil))))
             s (:worlds s)))

(defn- interleavings [a b]
  (cond (empty? a) [b]
        (empty? b) [a]
        :else (concat (map #(cons (first a) %) (interleavings (rest a) b))
                      (map #(cons (first b) %) (interleavings a (rest b))))))

(deftest finite-collection-registration-and-scan-interleavings
  (let [row {:entries #{:a :b} :last 0 :pending? false :scan nil}
        initial {:generation 0 :dead #{} :worlds {:parent row :idle row}
                 :runnable [:dormant-resource] :callbacks 0 :gates 0}]
    ;; Independently interleave collector, fork publication/check, and scan.
    (doseq [ops (mapcat #(interleavings % [:reset :read :finish])
                        (interleavings [:collect :snapshot :deliver]
                                       [:fork-snapshot :fork-register :fork-check]))]
      (let [s (reduce transition initial ops)
            s (fair-drain s)]
        (is (= [:dormant-resource] (:runnable s)))
        (is (= 0 (:callbacks s) (:gates s)))
        (is (every? #(= #{:b} (:entries %)) (vals (:worlds s))))
        (is (every? #(not (:pending? %)) (vals (:worlds s))))))
    (let [s (fair-drain (reduce transition initial
                                [:collect :snapshot :release :deliver :fork-snapshot :fork-register :fork-check]))]
      (is (empty? (get-in s [:worlds :parent :entries])))
      (is (= #{:b} (get-in s [:worlds :idle :entries]))))))

(deftest capsule-replacement-and-owner-world-death-interleavings
  (doseq [ops (permutations [:old-dead :replace :old-cleaner :owner-dead :world-dead])
          :let [position (zipmap ops (range))]
          :when (< (position :old-dead) (position :old-cleaner))]
    (loop [s {:index :old :owner? true :world? true :members #{:old}}
           ops ops]
      (when-let [op (first ops)]
        (let [before s
              s (case op
                  :old-dead (update s :members disj :old)
                  :replace (if (and (:owner? s) (:world? s))
                             (assoc s :index :new :members #{:new}) s)
                  :old-cleaner (if (= :old (:index s)) (assoc s :index nil) s)
                  :owner-dead (assoc s :owner? false :members #{})
                  :world-dead (assoc s :world? false :index nil :members #{}))]
          (when (and (= op :old-cleaner) (= :new (:index before)))
            (is (= :new (:index s)) "delayed collection cannot delete a replacement"))
          (when-not (:world? s) (is (nil? (:index s))))
          (when-not (and (:owner? s) (:world? s)) (is (empty? (:members s))))
          (recur s (rest ops)))))))
