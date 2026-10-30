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

(declare operation-barrier?)

(defn clear-deferred-wait
  "Discard a consumed operation receipt only after its physical frames return.
  Acquired ticket cells remain held until the parent cleanup physically returns."
  [s n]
  (let [row (get-in s [:env :native n])]
    (assert (operation-barrier? row) "Operation still physically active")
    (update-in s [:env :native n] dissoc :operation)))

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

(declare operation-barrier?)

(defn release-cells [s n]
  (assert (operation-barrier? (get-in s [:env :native n])) "Operation still physically active")
  (let [s (clear-deferred-wait s n) keys (get-in s [:env :native n :cells])]
    (reduce (fn [s key]
              (let [holders (disj (get-in s [:env :cleanup-cells key :holders]) n)]
                (if (seq holders) (assoc-in s [:env :cleanup-cells key :holders] holders)
                    (update-in s [:env :cleanup-cells] dissoc key)))) s keys)))

(defn require! [condition error data]
  (when-not condition (throw (ex-info (name error) (assoc data :error error)))))

(defn protected-operation-id?
  "The reserved participant identity shape remains fenced after its row expires."
  [op]
  (and (vector? op) (= 2 (count op))
       (vector? (first op)) (= 3 (count (first op)))
       (= :cps-exit (ffirst op))))

(defn operation [s op]
  (let [row (when (vector? op) (get-in s [:env :native (first op) :operation]))]
    (when (= op (:id row)) row)))

(defn operation-barrier? [row]
  (let [op (:operation row)]
    (or (nil? op) (and (= :terminal (:state op)) (zero? (:physical op))))))

(defn- operation-path [op] [:env :native (first op) :operation])

(defn operation-frame! [s {:keys [op frame n sequence]}]
  (let [row (operation s op) ticket (get-in s [:env :native n])]
    (require! (and row (= n (first op)) (= sequence (second op) (:sequence ticket))
                   (protected? ticket) (= :open (:state row))
                   (contains? (:frames row) frame))
              ::not-operation-frame {:op op :frame frame})
    row))

(defn operation-start [s {:keys [op n sequence frame]}]
  (let [row (get-in s [:env :native n]) [w r] (:owner row)]
    (require! (and (protected? row) (= :waiting (:phase row)) (= sequence (:sequence row))
                   (= op [n sequence]) (nil? (:operation row)) (= frame [op 1])
                   (active-slice? s w r)) ::not-operation-start {:n n :op op})
    (assoc-in s [:env :native n :operation]
              {:id op :state :open :parent r :physical 1 :frames #{frame}
               :next-registration 0 :next-frame 1 :registrations {}})))

(defn unlink-registration [s op reg]
  (if-let [{:keys [cell allocation]} (get-in s (conj (operation-path op) :registrations reg))]
    (let [[w _ e] cell]
      (-> s (update-deferred-resource w e allocation #(update % :protected dissoc reg))
          (update-in (conj (operation-path op) :registrations) dissoc reg))) s))

(defn operation-deliver [s {:keys [op reg value]}]
  (let [row (operation s op) registration (get-in row [:registrations reg])]
    (if (and (= :open (:state row)) (= :pending (:state registration)))
      (let [[w _ e] (:cell registration)]
        (-> s (update-deferred-resource w e (:allocation registration) #(update % :protected dissoc reg))
            (update-in (conj (operation-path op) :registrations reg)
                       assoc :state :ready :delivery value))) s)))

(defn operation-claim [s {:keys [op reg frame inline?] :as action}]
  (let [row (operation s op) registration (get-in row [:registrations reg])
        ready (sort-by second (for [[id r] (:registrations row) :when (= :ready (:state r))] id))]
    (require! (and (or (= :open (:state row)) (and inline? (= :terminal (:state row))))
                   registration (false? (:entered? registration))
                   (if inline?
                     (and (= :claimed (:state registration)) (contains? (:frames row) frame))
                     (and (= :ready (:state registration)) (zero? (:physical row))
                          (= reg (first ready)) (= frame [op (inc (:next-frame row))]))))
              ::not-operation-ready {:op op :reg reg :frame frame})
    (-> (cond-> s
          (not inline?) (update-in (operation-path op) #(-> % (assoc :physical 1 :frames #{frame})
                                                            (update :next-frame inc))))
        (update-in (conj (operation-path op) :registrations reg) assoc :state :claimed :entered? true)
        (update :events conj {:event :continuation-entry :op op :reg reg :continuation reg
                              :variant :ok :value (:delivery registration)}))))

(defn operation-terminal [s {:keys [op n sequence value variant]}]
  (require! (#{:ok :error} variant) ::invalid-operation-variant {:op op :variant variant})
  (let [row (operation s op) ticket (get-in s [:env :native n])]
    (if (and (= n (first op)) (= sequence (second op) (:sequence ticket)) (= :open (:state row)))
      (let [s (reduce (fn [s [reg registration]]
                        (if (= :claimed (:state registration)) s (unlink-registration s op reg)))
                      s (:registrations row))]
        (-> s (update-in (operation-path op) assoc :state :terminal :variant variant)
            (update-in [:env :native n] assoc :phase :ready :delivery value)
            (update :events conj {:event :operation-terminal :op op :variant variant :value value}))) s)))

(defn operation-return [s {:keys [op frame reg inline?]}]
  (let [row (operation s op)
        claimed (when reg [reg])]
    (require! (and row (contains? (:frames row) frame)
                   (if reg (and (= :claimed (get-in row [:registrations reg :state]))
                                (true? (get-in row [:registrations reg :entered?])))
                       (and (not inline?) (= frame [op 1])))
                   (= 1 (:physical row))
                   (or inline?
                       (not-any? (fn [[id registration]]
                                   (and (= :claimed (:state registration)) (not= id reg)))
                                 (:registrations row))))
              ::not-operation-return {:op op :frame frame :reg reg})
    (let [s (reduce #(unlink-registration %1 op %2) s (if inline? [reg] claimed))]
      (if inline? s (update-in s (operation-path op) assoc :physical 0 :frames #{})))))

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
    (require! (and (finalizing? row) (= :ready phase) (operation-barrier? row)) ::not-ready {:n n})
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
    (require! (and (exit? row) (= :ready phase) (operation-barrier? row)) ::not-ready {:n n})
    (require! (nil? (get-in s [:env :threads th :run])) ::thread-busy {:th th})
    ;; A callback can arrive before the suspending slice physically returns.
    (require! (not (active-slice? s w r)) ::slice-busy {:w w :r r})
    (-> (clear-deferred-wait s n) (assoc-in [:env :native n :phase] :claimed)
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
    (require! (and (exit? row) (= :ready phase) (operation-barrier? row)) ::not-ready {:n n})
    (require! (and (:executing? thread) (= owner [(:world thread) (:run thread)])
                   (nil? (:cleanup-ticket thread))) ::wrong-slice {:n n :th th})
    (-> (clear-deferred-wait s n) (assoc-in [:env :native n :phase] :claimed)
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
    (if (and (protected? row) (nil? (:operation row)) (= :waiting (:phase row)) (= sequence (:sequence row)))
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
  "Exact retained payload rights; operation frames do not claim the outer ticket."
  [s {:keys [th cell value op frame] :as action}]
  (let [n (or (when op (first op)) (get-in s [:env :threads th :cleanup-ticket]))
        row (get-in s [:env :native n]) participant (operation s op)
        admitted? (if op
                    (and participant (contains? (:frames participant) frame))
                    (= :claimed (:phase row)))]
    (require! (and n admitted? (contains? (:cells row #{}) cell)
                   (contains? (get-in s [:env :cleanup-cells cell :holders] #{}) n))
              ::missing-cleanup-cell {:th th :cell cell :op op :frame frame})
    (require! (not (and (contains? action :value)
                        (= :deferred (get-in s [:env :cleanup-cells cell :kind]))))
              ::not-mutable-cleanup-cell {:th th :cell cell})
    (if (contains? action :value) (assoc-in s [:env :cleanup-cells cell :result] value) s)))

(defn operation-errors [s]
  (vec
   (concat
    (for [[n ticket] (get-in s [:env :native]) :let [op (:operation ticket)] :when op
          :when (or (not= (:id op) [n (:sequence ticket)])
                    (not= (:parent op) (second (:owner ticket)))
                    (not (#{:open :terminal} (:state op)))
                    (if (= :terminal (:state op)) (not (#{:ok :error} (:variant op)))
                        (contains? op :variant))
                    (not= (:physical op) (count (:frames op)))
                    (> (:physical op) 1)
                    (and (= :open (:state op))
                         (or (not= :waiting (:phase ticket)) (contains? ticket :delivery)))
                    (and (= :terminal (:state op))
                         (or (not= :ready (:phase ticket))
                             (some #(not= :claimed (:state %)) (vals (:registrations op))))))]
      {:n n :invalid-operation op})
    (for [[n ticket] (get-in s [:env :native]) :let [op (:operation ticket)]
          [reg row] (:registrations op)
          :let [[w _ e] (:cell row)
                retained (get-in s [:env :cleanup-cells (:cell row)])
                edge (get-in retained [:deferred :protected reg])
                expected {:operation (:id op) :sequence (:sequence ticket)}]
          :when (or (not= (:id op) (first reg))
                    (not (<= 1 (second reg) (:next-registration op)))
                    (not= reg (:continuation row))
                    (not (boolean? (:entered? row)))
                    (and (:entered? row) (not= :claimed (:state row)))
                    (not= [w e e] [(:w row) (:e row) (:allocation row)])
                    (not= (:allocation row) (:allocation retained))
                    (not (contains? (:cells ticket #{}) (:cell row)))
                    (not (contains? (:holders retained #{}) n))
                    (not (#{:pending :ready :claimed} (:state row)))
                    (if (= :pending (:state row))
                      (or (not= expected edge) (contains? row :delivery)
                          (get-in retained [:deferred :assigned?]))
                      (or edge (not (contains? row :delivery))))
                    (and (= :claimed (:state row)) (zero? (:physical op))))]
      {:n n :reg reg :invalid-operation-registration row})
    (for [[w e row assigned?]
          (concat (for [[w world] (:worlds s) [e row] (:entities world) :when (= :deferred (:kind row))]
                    [w e row (:completed? row)])
                  (for [[key row] (get-in s [:env :cleanup-cells]) :when (= :deferred (:kind row))]
                    [(first key) (nth key 2) row (get-in row [:deferred :assigned?])]))
          [reg edge] (get-in row [:deferred :protected])
          :let [op (operation s (:operation edge)) registration (get-in op [:registrations reg])]
          :when (or assigned? (not= :open (:state op))
                    (not= :pending (:state registration))
                    (not= [w e (:allocation row)] [(:w registration) (:e registration) (:allocation registration)])
                    (not= (:sequence edge) (second (:id op))))]
      {:reg reg :orphan-operation-source-edge edge}))))

(defn errors
  "Independent local conservation: one ticket per generation; claimed/returning
  tickets have exactly one cleanup frame. Waiting/ready may retain a suspending
  frame until its physical return. Ordinary frames cannot own cleanup authority."
  [s]
  (vec
   (concat
    (operation-errors s)
    (for [[w world] (:worlds s) [e row] (:entities world) :when (= :deferred (:kind row))
          :when (or (not= e (:allocation row)) (not (boolean? (:completed? row)))
                    (not (boolean? (get-in row [:deferred :claimed?])))
                    (not (map? (get-in row [:deferred :protected])))
                    (seq (remove #{:claimed? :protected} (keys (:deferred row)))))]
      {:w w :e e :invalid-deferred-source row})
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
           :when (and (finalizing? row) (= :ready (:phase row)) (operation-barrier? row))
           th (set (concat [:host :foreign] (keys (get-in s [:env :threads]))))
           :let [[w r] (:owner row) thread (get-in s [:env :threads th])
                 inline? (and (:executing? thread) (= [w r] [(:world thread) (:run thread)]))]
           :when (or inline? (and (nil? (:run thread)) (not (active-slice? s w r))))]
       {:t :finalization-resume :w w :n n :th th})
     (for [[n row] (get-in s [:env :native]) :when (and (exit? row) (= :ready (:phase row)) (operation-barrier? row))
           th [:host :foreign] :when (and (nil? (get-in s [:env :threads th :run]))
                                          (not (apply active-slice? s (:owner row))))]
       {:t :cleanup-claim :n n :th th})
     (for [[n row] (get-in s [:env :native]) :when (and (exit? row) (= :ready (:phase row)) (operation-barrier? row))
           [th thread] (get-in s [:env :threads])
           :when (and (:executing? thread) (= (:owner row) [(:world thread) (:run thread)])
                      (nil? (:cleanup-ticket thread)))]
       {:t :cleanup-adopt :n n :th th})
     (for [[n row] (get-in s [:env :native]) :when (and (protected? row) (nil? (:operation row)) (= :waiting (:phase row)))]
       {:t :cleanup-deliver :n n :sequence (:sequence row) :value :cleanup-value})
     (for [[th thread] (get-in s [:env :threads])
           :let [n (:cleanup-ticket thread)]
           :when (and n (= :claimed (get-in s [:env :native n :phase])))
           t [:cleanup-park :cleanup-return]]
       {:t t :th th}))))
