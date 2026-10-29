(ns org.replikativ.spindel.lifetime.cleanup
  "Protected CPS exit authority. Ordinary graph rows never root cleanup.
  Continuations are symbolic here; actual closures belong to the runtime."
  (:refer-clojure :exclude [deliver]))

(defn ticket [w r] [:cps-exit w r])
(defn protected? [row] (= :cps-exit (:kind row)))
(defn active-slice? [s w r]
  (some #(and (= w (:world %)) (= r (:run %))) (vals (get-in s [:env :threads]))))

(defn reserve
  "Reserve before logical teardown. A body that never entered has no CPS exit.
  Completion means finally already returned, so completed caches add no ticket."
  [s w r anchor]
  (let [rr (get-in s [:worlds w :runs r]) n (ticket w r)]
    (if (and (get-in s [:model :cps-exit?]) (:cps-entered? rr)
             (#{:running :parked :stale} (:status rr))
             (nil? (get-in s [:env :native n])))
      (assoc-in s [:env :native n]
                {:kind :cps-exit :owner [w r] :state :running :phase :ready
                 :sequence 0 :retired? true :anchor anchor}) s)))

(defn retain-subtree
  "Capture source payloads before ownership teardown. Participants share each
  retained cell; no graph, body, historical world or continuation is copied.
  Keys include the original owner, fencing a later adopted generation."
  [s w root anchors]
  (if-not (get-in s [:model :cps-exit?]) s
          (let [world (get-in s [:worlds w])
                owners (loop [found #{root}]
                         (let [next (into found (concat
                                                 (for [[r rr] (:runs world) :when (found (:owner rr))] r)
                                                 (for [[id scope] (:scopes world) :when (found (:parent scope))] id)))]
                           (if (= found next) found (recur next))))
                s (reduce (fn [s [r anchor]]
                            (if (owners r) (reserve s w r anchor) s)) s anchors)
                participants (set (for [[n row] (get-in s [:env :native])
                                        :when (and (protected? row) (= w (first (:owner row)))
                                                   (some owners (:anchor row)))] n))
                new-cells (for [[e row] (:entities world)
                                :when (and (owners (:owner row)) (#{:signal :atom} (:kind row)))]
                            [[w (:owner row) e] (select-keys row [:kind :result])])
                old-cells (for [key (set (mapcat #(get-in s [:env :native % :cells]) participants))]
                            [key (get-in s [:env :cleanup-cells key])])
                cells (concat new-cells old-cells)]
            (if (empty? participants) s
                (reduce (fn [s [key payload]]
                          (let [existing (get-in s [:env :cleanup-cells key])
                                row (assoc (or existing payload) :holders (into (:holders existing #{}) participants))]
                            (reduce #(update-in %1 [:env :native %2 :cells] (fnil conj #{}) key)
                                    (assoc-in s [:env :cleanup-cells key] row) participants))) s cells)))))

(defn release-cells [s n]
  (let [keys (get-in s [:env :native n :cells])]
    (reduce (fn [s key]
              (let [holders (disj (get-in s [:env :cleanup-cells key :holders]) n)]
                (if (seq holders) (assoc-in s [:env :cleanup-cells key :holders] holders)
                    (update-in s [:env :cleanup-cells] dissoc key)))) s keys)))

(defn require! [condition error data]
  (when-not condition (throw (ex-info (name error) (assoc data :error error)))))

(defn claim [s {:keys [n th]}]
  (let [{:keys [owner phase] :as row} (get-in s [:env :native n]) [w r] owner]
    (require! (and (protected? row) (= :ready phase)) ::not-ready {:n n})
    (require! (nil? (get-in s [:env :threads th :run])) ::thread-busy {:th th})
    ;; A callback can arrive before the suspending slice physically returns.
    (require! (not (active-slice? s w r)) ::slice-busy {:w w :r r})
    (-> s (assoc-in [:env :native n :phase] :claimed)
        (assoc-in [:env :threads th]
                  (merge (get-in s [:env :threads th])
                         {:world w :scope r :run r :executing? true :retired? true
                          :obligation-world w :anchor (:anchor row) :cleanup-ticket n})))))

(defn adopt
  "Transfer exit authority to the generation's existing physical frame.
  No dispatch, re-entry or second frame is created."
  [s {:keys [n th]}]
  (let [{:keys [owner phase] :as row} (get-in s [:env :native n])
        thread (get-in s [:env :threads th])]
    (require! (and (protected? row) (= :ready phase)) ::not-ready {:n n})
    (require! (and (:executing? thread) (= owner [(:world thread) (:run thread)])
                   (nil? (:cleanup-ticket thread))) ::wrong-slice {:n n :th th})
    (-> s (assoc-in [:env :native n :phase] :claimed)
        (update-in [:env :threads th] assoc :cleanup-ticket n
                   :retired? true :anchor (:anchor row)))))

(defn suspend [s {:keys [th]}]
  (let [n (get-in s [:env :threads th :cleanup-ticket]) row (get-in s [:env :native n])]
    (require! (and n (= :claimed (:phase row))) ::not-claimed {:th th})
    (update-in s [:env :native n]
               #(-> % (assoc :phase :waiting) (update :sequence inc) (dissoc :delivery)))))

(defn deliver
  "One callback slot per suspension. Unknown, old and duplicate callbacks are inert."
  [s {:keys [n sequence value]}]
  (let [row (get-in s [:env :native n])]
    (if (and (protected? row) (= :waiting (:phase row)) (= sequence (:sequence row)))
      (update-in s [:env :native n] assoc :phase :ready :delivery value) s)))

(defn returning [s {:keys [th]}]
  (let [n (get-in s [:env :threads th :cleanup-ticket]) row (get-in s [:env :native n])]
    (require! (and n (= :claimed (:phase row))) ::not-claimed {:th th})
    (update-in s [:env :native n] #(-> % (assoc :phase :returning) (dissoc :delivery)))))

(defn slice-exit
  "A returning cleanup ticket is released only at actual physical return."
  [s thread]
  (if-let [n (:cleanup-ticket thread)]
    (let [phase (get-in s [:env :native n :phase])]
      (require! (#{:ready :waiting :returning} phase) ::missing-cleanup-boundary {:n n :phase phase})
      (if (= :returning phase) (update-in (release-cells s n) [:env :native] dissoc n) s)) s))

(defn access
  "Cleanup reads/writes existing retained cells only. No construction or
  notification is admitted through this private payload view."
  [s {:keys [th cell value] :as action}]
  (let [n (get-in s [:env :threads th :cleanup-ticket]) row (get-in s [:env :native n])]
    (require! (and n (= :claimed (:phase row)) (contains? (:cells row) cell))
              ::missing-cleanup-cell {:th th :cell cell})
    (if (contains? action :value) (assoc-in s [:env :cleanup-cells cell :result] value) s)))

(defn errors
  "Independent local conservation: one ticket per generation; claimed/returning
  tickets have exactly one cleanup frame. Waiting/ready may retain a suspending
  frame until its physical return. Ordinary frames cannot own cleanup authority."
  [s]
  (vec
   (concat
    (for [[n row] (get-in s [:env :native]) :when (protected? row)
          :let [[w r] (:owner row)
                frames (filter #(= n (:cleanup-ticket %)) (vals (get-in s [:env :threads])))
                all-frames (filter #(and (= w (:world %)) (= r (:run %)))
                                   (vals (get-in s [:env :threads])))]
          :when (or (not= n (ticket w r)) (not= :running (:state row))
                    (not (:retired? row)) (not (#{:ready :waiting :claimed :returning} (:phase row)))
                    (not (and (integer? (:sequence row)) (<= 0 (:sequence row))))
                    (not= r (first (:anchor row))) (not= w (last (:anchor row)))
                    (> (count all-frames) 1)
                    (and (#{:claimed :returning} (:phase row)) (not= 1 (count frames)))
                    (some #(not= (:owner row) [(:world %) (:run %)]) frames))]
      {:n n :ticket row :frames (vec frames)})
    (for [[key cell] (get-in s [:env :cleanup-cells])
          :let [expected (set (for [[n row] (get-in s [:env :native])
                                    :when (contains? (:cells row) key)] n))]
          :when (or (empty? expected) (not= expected (:holders cell))
                    (not (#{:signal :atom} (:kind cell)))
                    (seq (remove #{:kind :result :holders} (keys cell))))]
      {:cell key :payload cell :expected-holders expected})
    (for [[n row] (get-in s [:env :native]) key (:cells row)
          :when (not (contains? (get-in s [:env :cleanup-cells key :holders] #{}) n))]
      {:n n :missing-cell key})
    (for [[th thread] (get-in s [:env :threads])
          :let [n (:cleanup-ticket thread)]
          :when (and n (not (protected? (get-in s [:env :native n]))))]
      {:thread th :orphan-cleanup-ticket n}))))

(defn enabled [s]
  (when (get-in s [:model :cps-exit?])
    (concat
     (for [[n row] (get-in s [:env :native]) :when (and (protected? row) (= :ready (:phase row)))
           th [:host :foreign] :when (and (nil? (get-in s [:env :threads th :run]))
                                          (not (apply active-slice? s (:owner row))))]
       {:t :cleanup-claim :n n :th th})
     (for [[n row] (get-in s [:env :native]) :when (and (protected? row) (= :ready (:phase row)))
           [th thread] (get-in s [:env :threads])
           :when (and (:executing? thread) (= (:owner row) [(:world thread) (:run thread)])
                      (nil? (:cleanup-ticket thread)))]
       {:t :cleanup-adopt :n n :th th})
     (for [[n row] (get-in s [:env :native]) :when (and (protected? row) (= :waiting (:phase row)))]
       {:t :cleanup-deliver :n n :sequence (:sequence row) :value :cleanup-value})
     (for [[th thread] (get-in s [:env :threads])
           :let [n (:cleanup-ticket thread)]
           :when (and n (= :claimed (get-in s [:env :native n :phase])))
           t [:cleanup-park :cleanup-return]]
       {:t t :th th}))))
