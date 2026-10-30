(ns org.replikativ.spindel.lifetime.cleanup
  "Protected CPS exit authority. Ordinary graph rows never root cleanup.
  Continuations are symbolic here; actual closures belong to the runtime."
  (:refer-clojure :exclude [deliver]))

(defn ticket [w r] [:cps-exit w r])
(defn exit? [row] (= :cps-exit (:kind row)))
(defn finalizing? [row] (= :cps-finalization (:kind row)))
(defn protected? [row] (or (exit? row) (finalizing? row)))
(defn active-slice? [s w r]
  (some #(and (= w (:world %)) (= r (:run %))) (vals (get-in s [:env :threads]))))

(defn update-deferred-resource
  "Live and retained views name one world-local single-assignment resource."
  [s w e allocation f]
  (let [source (get-in s [:worlds w :entities e])
        source? (and (= :deferred (:kind source)) (= allocation (:allocation source)))
        cells (for [[key row] (get-in s [:env :cleanup-cells])
                    :when (and (= w (first key)) (= e (nth key 2 nil))
                               (= :deferred (:kind row)) (= allocation (:allocation row)))] key)
        row (if source? source (get-in s [:env :cleanup-cells (first cells)]))
        resource (cond-> (assoc (:deferred row) :value (:result row))
                   source? (assoc :assigned? (boolean (:completed? source))))
        resource (f resource)
        s (if source?
            (-> s (assoc-in [:worlds w :entities e :result] (:value resource))
                (assoc-in [:worlds w :entities e :completed?] (:assigned? resource))
                (assoc-in [:worlds w :entities e :deferred] (dissoc resource :value :assigned?))) s)]
    (reduce (fn [s key]
              (-> s (assoc-in [:env :cleanup-cells key :result] (:value resource))
                  (assoc-in [:env :cleanup-cells key :deferred] (dissoc resource :value)))) s cells)))

(defn clear-deferred-wait
  "Remove the exact registration owned by this ticket before its slot changes."
  [s n]
  (if-let [{:keys [w e allocation cell sequence]} (get-in s [:env :native n :deferred-wait])]
    (let [source (get-in s [:worlds w :entities e])
          live? (and (= :deferred (:kind source)) (= allocation (:allocation source)) (:owner source))
          cell (or cell (first (filter (fn [key]
                                         (and (= w (first key)) (= e (nth key 2 nil))
                                              (= allocation (get-in s [:env :cleanup-cells key :allocation]))))
                                       (get-in s [:env :native n :cells]))))
          retained? (and cell (= sequence (get-in s [:env :cleanup-cells cell :deferred :protected n])))
          path (cond retained? [:env :cleanup-cells cell]
                     live? [:worlds w :entities e])
          s (if (and path (= sequence (get-in s (conj path :deferred :protected n))))
              (update-deferred-resource s w e allocation #(update % :protected dissoc n)) s)]
      (update-in s [:env :native n] dissoc :deferred-wait)) s))

(defn reserve
  "Reserve before logical teardown. A body that never entered has no CPS exit.
  Completion means finally already returned, so completed caches add no ticket."
  [s w r anchor]
  (let [rr (get-in s [:worlds w :runs r]) n (ticket w r)]
    (if (and (get-in s [:model :cps-exit?]) (:cps-entered? rr)
             (#{:running :parked :stale} (:status rr))
             (not (exit? (get-in s [:env :native n]))))
      ;; A finalizer already waiting keeps the same callback slot on retirement.
      (update-in s [:env :native n]
                 #(assoc (or % {:owner [w r] :state :running :phase :ready
                                :sequence (:finalization-sequence rr 0)})
                         :kind :cps-exit :retired? true :anchor anchor)) s)))

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
                                        :when (and (exit? row) (= w (first (:owner row)))
                                                   (some owners (:anchor row)))] n))
                new-cells (for [[e row] (:entities world)
                                :when (and (owners (:owner row)) (#{:signal :atom :deferred} (:kind row)))]
                            [[w (:owner row) e]
                             (cond-> (select-keys row [:kind :result])
                               (= :deferred (:kind row))
                               (assoc :allocation (:allocation row)
                                      :deferred (assoc (:deferred row) :assigned? (boolean (:completed? row)))))])
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
  (let [s (clear-deferred-wait s n) keys (get-in s [:env :native n :cells])]
    (reduce (fn [s key]
              (let [holders (disj (get-in s [:env :cleanup-cells key :holders]) n)]
                (if (seq holders) (assoc-in s [:env :cleanup-cells key :holders] holders)
                    (update-in s [:env :cleanup-cells] dissoc key)))) s keys)))

(defn require! [condition error data]
  (when-not condition (throw (ex-info (name error) (assoc data :error error)))))

(defn begin-finalization [s {:keys [th anchor current?]}]
  (let [{:keys [world run executing?]} (get-in s [:env :threads th])
        rr (get-in s [:worlds world :runs run]) n (ticket world run)
        sequence (inc (:finalization-sequence rr 0))]
    (require! (get-in s [:model :cps-exit?]) ::profile-disabled {})
    (require! (and executing? (:cps-entered? rr) (= :running (:status rr))
                   current?)
              ::not-current-slice {:th th})
    (require! (nil? (get-in s [:env :native n])) ::already-waiting {:n n})
    (-> s (assoc-in [:worlds world :runs run :status] :parked)
        (assoc-in [:worlds world :runs run :finalization-sequence] sequence)
        (assoc-in [:env :native n]
                  {:kind :cps-finalization :owner [world run] :state :running
                   :phase :waiting :sequence sequence :retired? false :anchor anchor}))))

(defn resume-finalization [s {:keys [n th current?] :as action}]
  (let [{:keys [owner phase] :as row} (get-in s [:env :native n]) [w r] owner
        rr (get-in s [:worlds w :runs r]) thread (get-in s [:env :threads th])
        inline? (and (:executing? thread) (= owner [(:world thread) (:run thread)]))]
    (require! (and (finalizing? row) (= :ready phase)) ::not-ready {:n n})
    (require! (= w (:w action)) ::wrong-world {:n n :w (:w action)})
    (require! (and (= :parked (:status rr))
                   current?)
              ::not-current-slice {:n n})
    (require! (or inline? (nil? (:run thread))) ::thread-busy {:th th})
    (require! (or inline? (not (active-slice? s w r))) ::slice-busy {:w w :r r})
    (-> (release-cells s n) (update-in [:env :native] dissoc n)
        (assoc-in [:worlds w :runs r :status] :running)
        (cond-> (not inline?)
          (assoc-in [:env :threads th]
                    (merge thread {:world w :scope r :run r :obligation-world w :executing? true}))))))

(defn claim [s {:keys [n th]}]
  (let [{:keys [owner phase] :as row} (get-in s [:env :native n]) [w r] owner]
    (require! (and (exit? row) (= :ready phase)) ::not-ready {:n n})
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
    (require! (and (exit? row) (= :ready phase)) ::not-ready {:n n})
    (require! (and (:executing? thread) (= owner [(:world thread) (:run thread)])
                   (nil? (:cleanup-ticket thread))) ::wrong-slice {:n n :th th})
    (-> s (assoc-in [:env :native n :phase] :claimed)
        (update-in [:env :threads th] assoc :cleanup-ticket n
                   :retired? true :anchor (:anchor row)))))

(defn suspend [s {:keys [th]}]
  (let [n (get-in s [:env :threads th :cleanup-ticket]) row (get-in s [:env :native n])]
    (require! (and n (= :claimed (:phase row))) ::not-claimed {:th th})
    (update-in (clear-deferred-wait s n) [:env :native n]
               #(-> % (assoc :phase :waiting) (update :sequence inc) (dissoc :delivery)))))

(defn deliver
  "One callback slot per suspension. Unknown, old and duplicate callbacks are inert."
  [s {:keys [n sequence value]}]
  (let [row (get-in s [:env :native n])]
    (if (and (protected? row) (= :waiting (:phase row)) (= sequence (:sequence row)))
      (update-in (clear-deferred-wait s n) [:env :native n] assoc :phase :ready :delivery value) s)))

(defn returning [s {:keys [th]}]
  (let [n (get-in s [:env :threads th :cleanup-ticket]) row (get-in s [:env :native n])]
    (require! (and n (= :claimed (:phase row))) ::not-claimed {:th th})
    (update-in (clear-deferred-wait s n) [:env :native n] #(-> % (assoc :phase :returning) (dissoc :delivery)))))

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
    (require! (not (and (contains? action :value)
                        (= :deferred (get-in s [:env :cleanup-cells cell :kind]))))
              ::not-mutable-cleanup-cell {:th th :cell cell})
    (if (contains? action :value) (assoc-in s [:env :cleanup-cells cell :result] value) s)))

(defn errors
  "Independent local conservation: one ticket per generation; claimed/returning
  tickets have exactly one cleanup frame. Waiting/ready may retain a suspending
  frame until its physical return. Ordinary frames cannot own cleanup authority."
  [s]
  (vec
   (concat
    (for [[w world] (:worlds s) [e row] (:entities world) :when (= :deferred (:kind row))
          :when (or (not= e (:allocation row)) (not (boolean? (:completed? row)))
                    (not (boolean? (get-in row [:deferred :claimed?])))
                    (not (map? (get-in row [:deferred :protected])))
                    (seq (remove #{:claimed? :protected} (keys (:deferred row)))))]
      {:w w :e e :invalid-deferred-source row})
    (for [[w e allocation key row assigned?]
          (concat (for [[w world] (:worlds s) [e row] (:entities world) :when (= :deferred (:kind row))]
                    [w e (:allocation row) nil row (:completed? row)])
                  (for [[key row] (get-in s [:env :cleanup-cells]) :when (= :deferred (:kind row))]
                    [(first key) (nth key 2) (:allocation row) key row (get-in row [:deferred :assigned?])]))
          [n sequence] (get-in row [:deferred :protected])
          :let [ticket (get-in s [:env :native n]) link (:deferred-wait ticket)
                linked (get-in s [:env :cleanup-cells (:cell link)])]
          :when (or assigned? (not (protected? ticket)) (not= :waiting (:phase ticket))
                    (not= sequence (:sequence ticket)) (not= [w e allocation sequence]
                                                             [(:w link) (:e link) (:allocation link) (:sequence link)])
                    (not (contains? (:cells ticket #{}) (:cell link)))
                    (not (contains? (:holders linked #{}) n))
                    (not= allocation (:allocation linked))
                    (not= sequence (get-in linked [:deferred :protected n])))]
      {:n n :orphan-deferred-registration {:w w :e e :cell key :sequence sequence}})
    (for [[key cell] (get-in s [:env :cleanup-cells]) :when (= :deferred (:kind cell))
          :let [w (first key) e (nth key 2 nil) allocation (:allocation cell)
                source (get-in s [:worlds w :entities e])
                canonical (if (and (= :deferred (:kind source)) (= allocation (:allocation source)))
                            {:result (:result source) :deferred (assoc (:deferred source) :assigned? (:completed? source))}
                            (select-keys
                             (some (fn [[other-key row]]
                                     (when (and (= w (first other-key)) (= e (nth other-key 2 nil))
                                                (= :deferred (:kind row)) (= allocation (:allocation row))) row))
                                   (get-in s [:env :cleanup-cells])) [:result :deferred]))]
          :when (not= canonical (select-keys cell [:result :deferred]))]
      {:cell key :inconsistent-deferred-resource {:expected canonical :actual cell}})
    (for [[n ticket] (get-in s [:env :native]) :let [link (:deferred-wait ticket)] :when link
          :let [{:keys [w e allocation cell sequence]} link
                source (get-in s [:worlds w :entities e])
                retained (get-in s [:env :cleanup-cells cell])
                target (if (and (= :deferred (:kind retained)) (= allocation (:allocation retained))
                                (= sequence (get-in retained [:deferred :protected n]))) retained source)]
          :when (or (not (protected? ticket)) (not= :waiting (:phase ticket))
                    (not= w (first (:owner ticket))) (not= sequence (:sequence ticket))
                    (not= :deferred (:kind target)) (not= allocation (:allocation target))
                    (not= sequence (get-in target [:deferred :protected n])))]
      {:n n :invalid-deferred-wait link})
    (for [[n row] (get-in s [:env :native]) :when (finalizing? row)
          :let [[w r] (:owner row) rr (get-in s [:worlds w :runs r])]
          :when (or (not= n (ticket w r)) (not= :running (:state row))
                    (not= false (:retired? row)) (not (#{:waiting :ready} (:phase row)))
                    (not (#{:parked :stale} (:status rr)))
                    (not (and (integer? (:sequence row)) (pos? (:sequence row))))
                    (not= (:sequence row) (:finalization-sequence rr))
                    (some #(not= :deferred (get-in s [:env :cleanup-cells % :kind])) (:cells row))
                    (not= r (first (:anchor row)))
                    (not= w (last (:anchor row))))]
      {:n n :invalid-live-finalization row})
    (for [[n row] (get-in s [:env :native]) :when (exit? row)
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
                    (not (#{:signal :atom :deferred} (:kind cell)))
                    (and (= :deferred (:kind cell))
                         (or (not= (:allocation cell) (nth key 2 nil))
                             (not (boolean? (get-in cell [:deferred :assigned?])))
                             (not (boolean? (get-in cell [:deferred :claimed?])))
                             (not (map? (get-in cell [:deferred :protected])))
                             (seq (remove #{:assigned? :claimed? :protected} (keys (:deferred cell))))))
                    (seq (remove (if (= :deferred (:kind cell))
                                   #{:kind :result :holders :allocation :deferred}
                                   #{:kind :result :holders}) (keys cell))))]
      {:cell key :payload cell :expected-holders expected})
    (for [[n row] (get-in s [:env :native]) key (:cells row)
          :when (not (contains? (get-in s [:env :cleanup-cells key :holders] #{}) n))]
      {:n n :missing-cell key})
    (for [[th thread] (get-in s [:env :threads])
          :let [n (:cleanup-ticket thread)]
          :when (and n (not (exit? (get-in s [:env :native n]))))]
      {:thread th :orphan-cleanup-ticket n}))))

(defn enabled [s]
  (when (get-in s [:model :cps-exit?])
    (concat
     (for [[th thread] (get-in s [:env :threads])
           :let [w (:world thread) r (:run thread) rr (get-in s [:worlds w :runs r])]
           :when (and (:executing? thread) (= :running (:status rr))
                      (nil? (get-in s [:env :native (ticket w r)])))]
       {:t :finalization-wait :w w :th th})
     (for [[n row] (get-in s [:env :native])
           :when (and (finalizing? row) (= :ready (:phase row)))
           th (set (concat [:host :foreign] (keys (get-in s [:env :threads]))))
           :let [[w r] (:owner row) thread (get-in s [:env :threads th])
                 inline? (and (:executing? thread) (= [w r] [(:world thread) (:run thread)]))]
           :when (or inline? (and (nil? (:run thread)) (not (active-slice? s w r))))]
       {:t :finalization-resume :w w :n n :th th})
     (for [[n row] (get-in s [:env :native]) :when (and (exit? row) (= :ready (:phase row)))
           th [:host :foreign] :when (and (nil? (get-in s [:env :threads th :run]))
                                          (not (apply active-slice? s (:owner row))))]
       {:t :cleanup-claim :n n :th th})
     (for [[n row] (get-in s [:env :native]) :when (and (exit? row) (= :ready (:phase row)))
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
