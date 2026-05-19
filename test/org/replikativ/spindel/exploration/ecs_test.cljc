(ns org.replikativ.spindel.exploration.ecs-test
  "Exploration: Entity-Component System with Deltaables

  Testing whether spindel's delta architecture suits game-like simulations:

  1. Entities as deltaable maps with component data
  2. World state as deltaable collection of entities
  3. Incremental derived views (visible entities, AI targets, etc.)
  4. Batch updates per 'tick'
  5. DOM rendering integration via ifor-each

  Key metrics we care about:
  - Delta count vs full re-render
  - Performance with N entities
  - Correctness of incremental updates"
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer-macros [deftest is testing use-fixtures]])
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.foreach :as foreach]
            #?(:clj [org.replikativ.spindel.test-async :refer [await-drain]])
            #?(:clj [org.replikativ.spindel.test-helpers :as th]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.dom.foreach :refer [ifor-each]])))

(use-fixtures :each
  (fn [f]
    (let [test-ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* test-ctx]
          (f))
        (finally
          (ctx/stop-context! test-ctx))))))

;; =============================================================================
;; Entity Helpers
;; =============================================================================

(defn make-entity
  "Create a game entity with standard components."
  [id & {:keys [position velocity health sprite ai-state]
         :or {position [0 0] velocity [0 0] health 100}}]
  {:id id
   :position position
   :velocity velocity
   :health health
   :sprite sprite
   :ai-state ai-state})

(defn make-world
  "Create initial world state with entities."
  [entities]
  (d/deltaable-map
   {:entities (d/deltaable-map
               (into {} (map (juxt :id identity) entities)))
    :tick 0}))

;; =============================================================================
;; World Mutation Helpers
;; =============================================================================

(defn add-entity
  "Add entity to world, returns new world."
  [world entity]
  (update world :entities assoc (:id entity) entity))

(defn remove-entity
  "Remove entity from world by id."
  [world entity-id]
  (update world :entities dissoc entity-id))

(defn update-entity
  "Update a specific entity's component."
  [world entity-id component-key new-value]
  (update world :entities
          (fn [entities]
            (assoc entities entity-id
                   (assoc (get entities entity-id) component-key new-value)))))

(defn update-position
  "Move entity by velocity (simple physics step)."
  [world entity-id]
  (let [entity (get-in world [:entities entity-id])
        [px py] (:position entity)
        [vx vy] (:velocity entity)]
    (update-entity world entity-id :position [(+ px vx) (+ py vy)])))

(defn tick-world
  "Advance world by one tick, updating all entity positions."
  [world]
  (let [entity-ids (keys (:entities world))]
    (-> (reduce update-position world entity-ids)
        (update :tick inc))))

;; =============================================================================
;; Basic ECS Tests
;; =============================================================================

#?(:clj
   (deftest test-entity-creation
     (testing "Entities can be created as maps"
       (let [e (make-entity "player-1"
                            :position [100 200]
                            :health 50
                            :sprite :warrior)]
         (is (= "player-1" (:id e)))
         (is (= [100 200] (:position e)))
         (is (= 50 (:health e)))
         (is (= :warrior (:sprite e)))))))

#?(:clj
   (deftest test-world-creation
     (testing "World contains entities as deltaable map"
       (let [world (make-world [(make-entity "e1" :position [0 0])
                                (make-entity "e2" :position [10 10])])]
         (is (d/deltaable? world) "World should be deltaable")
         (is (d/deltaable? (:entities world)) "Entities should be deltaable")
         (is (= 2 (count (:entities world))))
         (is (= 0 (:tick world)))))))

#?(:clj
   (deftest test-add-entity-produces-delta
     (testing "Adding entity produces :add delta on entities map"
       (let [world (make-world [(make-entity "e1")])
             world2 (add-entity world (make-entity "e2" :position [50 50]))]
         ;; World itself should have delta for :entities key
         (is (seq (d/get-deltas world2)) "World should have deltas")
         ;; The entities map should have an :add delta
         (let [entities-deltas (d/get-deltas (:entities world2))]
           (is (seq entities-deltas) "Entities should have deltas")
           (is (= :add (:delta (first entities-deltas)))))))))

#?(:clj
   (deftest test-remove-entity-produces-delta
     (testing "Removing entity produces :remove delta"
       (let [world (make-world [(make-entity "e1") (make-entity "e2")])
             world2 (remove-entity world "e2")]
         (let [entities-deltas (d/get-deltas (:entities world2))]
           (is (seq entities-deltas) "Should have deltas")
           (is (= :remove (:delta (first entities-deltas)))))))))

#?(:clj
   (deftest test-update-entity-produces-delta
     (testing "Updating entity component produces :update delta"
       (let [world (make-world [(make-entity "e1" :health 100)])
             world2 (update-entity world "e1" :health 80)]
         (let [entities-deltas (d/get-deltas (:entities world2))]
           (is (seq entities-deltas) "Should have deltas")
           (is (= :update (:delta (first entities-deltas)))))))))

;; =============================================================================
;; Physics Tick Tests
;; =============================================================================

#?(:clj
   (deftest test-tick-updates-positions
     (testing "Tick moves all entities by their velocity"
       (let [world (make-world [(make-entity "e1" :position [0 0] :velocity [1 2])
                                (make-entity "e2" :position [10 10] :velocity [-1 0])])
             world2 (tick-world world)]
         ;; Check positions updated
         (is (= [1 2] (get-in world2 [:entities "e1" :position])))
         (is (= [9 10] (get-in world2 [:entities "e2" :position])))
         ;; Check tick incremented
         (is (= 1 (:tick world2)))))))

#?(:clj
   (deftest test-tick-produces-deltas
     (testing "Tick produces update deltas for each moved entity"
       (let [world (make-world [(make-entity "e1" :velocity [1 0])
                                (make-entity "e2" :velocity [0 1])
                                (make-entity "e3" :velocity [0 0])])  ; Stationary
             world2 (tick-world world)]
         ;; Should have update deltas for entities
         (let [entity-deltas (d/get-deltas (:entities world2))]
           ;; All 3 entities get updated (even stationary one gets new position)
           (is (= 3 (count entity-deltas)) "Should have 3 entity update deltas"))))))

;; =============================================================================
;; Signal + Spin Integration
;; =============================================================================

#?(:clj
   (deftest test-signal-world-tracking
     (testing "World signal tracks changes via spin"
       (th/with-ctx [rt]
         (let [world-sig (sig/signal (make-world [(make-entity "e1" :health 100)]))
               captured-deltas (atom nil)
               captured-tick (atom nil)

               observer-spin (spin
                              (let [world-iv (track world-sig)
                                    world @world-iv
                                    deltas (iv/get-deltas world-iv)]
                                (reset! captured-deltas deltas)
                                (reset! captured-tick (:tick world))
                                world))]

           ;; Initial
           @observer-spin
           (is (= 0 @captured-tick))

           ;; Tick the world
           (swap! world-sig tick-world)
           (await-drain rt)

           (is (= 1 @captured-tick) "Should see updated tick")
           (is (seq @captured-deltas) "Should have deltas from tick"))))))

#?(:clj
   (deftest test-derived-view-entities-with-health
     (testing "Derived view filters entities incrementally"
       (th/with-ctx [rt]
         (let [world-sig (sig/signal (make-world [(make-entity "e1" :health 100)
                                                  (make-entity "e2" :health 0)   ; Dead
                                                  (make-entity "e3" :health 50)]))
               alive-count (atom 0)

               ;; Spin that computes alive entities
               alive-spin (spin
                           (let [world-iv (track world-sig)
                                 entities (:entities @world-iv)
                                 alive (filter #(pos? (:health (val %))) entities)]
                             (reset! alive-count (count alive))
                             (count alive)))]

           @alive-spin
           (is (= 2 @alive-count) "Should have 2 alive entities")

           ;; Kill e1
           (swap! world-sig update-entity "e1" :health 0)
           (await-drain rt)

           (is (= 1 @alive-count) "Should now have 1 alive entity"))))))

;; =============================================================================
;; Performance Exploration
;; =============================================================================

#?(:clj
   (deftest test-delta-count-scales-with-changes
     (testing "Delta count reflects actual changes, not entity count"
       (let [;; Create world with 100 entities
             entities (for [i (range 100)]
                        (make-entity (str "e" i) :position [i 0] :velocity [1 0]))
             world (make-world entities)]

         ;; Update just ONE entity
         (let [world2 (update-entity world "e50" :health 50)
               entity-deltas (d/get-deltas (:entities world2))]
           ;; Should have exactly 1 delta, not 100!
           (is (= 1 (count entity-deltas))
               "Updating one entity should produce one delta"))

         ;; Add ONE entity
         (let [world3 (add-entity world (make-entity "new-entity"))
               entity-deltas (d/get-deltas (:entities world3))]
           (is (= 1 (count entity-deltas))
               "Adding one entity should produce one delta"))))))

#?(:clj
   (deftest test-batch-tick-delta-count
     (testing "Batch tick produces delta per entity (expected)"
       (let [entities (for [i (range 10)]
                        (make-entity (str "e" i) :velocity [1 0]))
             world (make-world entities)
             world2 (tick-world world)
             entity-deltas (d/get-deltas (:entities world2))]
         ;; Tick updates ALL entities, so we expect N deltas
         (is (= 10 (count entity-deltas))
             "Ticking all entities produces delta for each")
         ;; But this is still better than diffing the whole structure!
         ))))

;; =============================================================================
;; Fork-Based AI Planning
;; =============================================================================
;; Demonstrate using runtime forking for speculative AI evaluation

(defn evaluate-world
  "Score a world state (simple heuristic: sum of all entity healths)."
  [world]
  (reduce + (map #(:health (val %)) (:entities world))))

(defn apply-action
  "Apply an AI action to the world."
  [world action]
  (case (:type action)
    :move (update-position world (:entity-id action))
    :attack (let [{:keys [target-id damage]} action
                  current-health (get-in world [:entities target-id :health])]
              (update-entity world target-id :health (max 0 (- current-health damage))))
    :heal (let [{:keys [entity-id amount]} action
                current-health (get-in world [:entities entity-id :health])]
            (update-entity world entity-id :health (min 100 (+ current-health amount))))
    world))

(defn simulate-future
  "Simulate N ticks into the future, return final world."
  [world n-ticks]
  (nth (iterate tick-world world) n-ticks))

#?(:clj
   (deftest test-fork-evaluates-without-mutation
     (testing "Forked context allows evaluation without mutating parent"
       (th/with-ctx [rt-main]
         (let [world-sig (sig/signal (make-world [(make-entity "player" :health 100)
                                                  (make-entity "enemy" :health 50)]))]
           ;; Initial score
           (is (= 150 (evaluate-world @world-sig)))

           ;; Fork and simulate damage in fork
           (let [rt-fork (ctx/fork-context rt-main)]
             (binding [ec/*execution-context* rt-fork]
               ;; Apply damage in fork
               (swap! world-sig apply-action {:type :attack
                                              :attacker-id "enemy"
                                              :target-id "player"
                                              :damage 30})
               ;; Fork sees damage
               (is (= 120 (evaluate-world @world-sig)) "Fork should see damage")))

           ;; Parent unchanged!
           (is (= 150 (evaluate-world @world-sig)) "Parent should be unchanged"))))))

#?(:clj
   (deftest test-fork-compare-strategies
     (testing "Fork enables comparing multiple AI strategies"
       (th/with-ctx [rt-main]
         (let [initial-world (make-world [(make-entity "ai" :health 50 :velocity [1 0])
                                          (make-entity "target" :health 100)])
               world-sig (sig/signal initial-world)

               ;; Strategy A: Attack
               score-attack (let [rt-fork (ctx/fork-context rt-main)]
                              (binding [ec/*execution-context* rt-fork]
                                (swap! world-sig apply-action {:type :attack
                                                               :attacker-id "ai"
                                                               :target-id "target"
                                                               :damage 20})
                                (evaluate-world @world-sig)))

               ;; Strategy B: Heal self
               score-heal (let [rt-fork (ctx/fork-context rt-main)]
                            (binding [ec/*execution-context* rt-fork]
                              (swap! world-sig apply-action {:type :heal
                                                             :entity-id "ai"
                                                             :amount 30})
                              (evaluate-world @world-sig)))]

           ;; Compare strategies
           (is (= 130 score-attack) "Attack reduces target health: 50 + 80 = 130")
           (is (= 180 score-heal) "Heal increases AI health: 80 + 100 = 180")

           ;; Parent world unchanged through all evaluations
           (is (= 150 (evaluate-world @world-sig)) "Original world unchanged"))))))

#?(:clj
   (deftest test-fork-lookahead-simulation
     (testing "Fork enables multi-step lookahead"
       (th/with-ctx [rt-main]
         (let [;; World where entity moves right each tick
               initial-world (make-world [(make-entity "mover" :position [0 0] :velocity [10 0])])
               world-sig (sig/signal initial-world)]

           ;; Simulate 5 ticks in a fork
           (let [rt-fork (ctx/fork-context rt-main)
                 future-pos (binding [ec/*execution-context* rt-fork]
                              ;; Tick 5 times
                              (dotimes [_ 5]
                                (swap! world-sig tick-world))
                              (get-in @world-sig [:entities "mover" :position]))]

             ;; Fork shows future position
             (is (= [50 0] future-pos) "After 5 ticks at velocity [10,0], position should be [50,0]"))

           ;; Parent still at initial position
           (is (= [0 0] (get-in @world-sig [:entities "mover" :position]))
               "Parent world unchanged"))))))

#?(:clj
   (deftest test-fork-is-lightweight
     (testing "Creating many forks is efficient"
       (th/with-ctx [rt-main]
         (let [world-sig (sig/signal (make-world
                                      (for [i (range 100)]
                                        (make-entity (str "e" i) :health (rand-int 100)))))]

           ;; Create 100 forks and evaluate each
           (let [start-time (System/nanoTime)
                 scores (doall
                         (for [_ (range 100)]
                           (let [rt-fork (ctx/fork-context rt-main)]
                             (binding [ec/*execution-context* rt-fork]
                                ;; Do some work in each fork - increment health
                               (let [current (get-in @world-sig [:entities "e0" :health])]
                                 (swap! world-sig update-entity "e0" :health (inc current)))
                               (evaluate-world @world-sig)))))
                 elapsed-ms (/ (- (System/nanoTime) start-time) 1e6)]

             ;; Should complete quickly (< 1 second for 100 forks)
             (is (< elapsed-ms 1000) (str "100 forks should be fast, took " elapsed-ms "ms"))
             ;; Each fork should produce a score
             (is (= 100 (count scores)) "Should have 100 scores")))))))

;; =============================================================================
;; Render Integration Tests
;; =============================================================================
;; Test that entity changes flow correctly through DOM rendering

(defn render-entity
  "Render a single entity as a DOM element."
  [entity]
  (el/div {:key (:id entity)
           :class (str "entity"
                       (when (zero? (:health entity)) " dead"))}
          (el/span {:class "id"} (:id entity))
          (el/span {:class "health"} (str "HP: " (:health entity)))
          (when-let [[x y] (:position entity)]
            (el/span {:class "position"} (str "(" x "," y ")")))))

(defn render-world-view
  "Render all entities in the world."
  [entities]
  (el/div {:class "game-world"}
          (el/h2 "Entities")
          (el/ul {:class "entity-list"}
                 (foreach/ifor-each :id (vals entities) render-entity))))

#?(:clj
   (deftest test-entity-render-produces-elements
     (testing "Entity rendering produces correct DOM structure"
       (let [entity (make-entity "player" :health 100 :position [50 50])
             vdom (render-entity entity)]
         (is (= :div (:tag vdom)))
         (is (= "player" (:key vdom)))
         ;; Should have 3 children: id, health, position
         (is (= 3 (count @(:children vdom))))))))

#?(:clj
   (deftest test-world-render-with-signal
     (testing "World renders correctly through signal + spin"
       (th/with-ctx [rt]
         (let [{:keys [discharge log]} (disch/make-mock-discharge)
               world-sig (sig/signal (make-world [(make-entity "e1" :health 100)
                                                  (make-entity "e2" :health 50)]))
               render-count (atom 0)

               app-spin (spin
                         (let [world-iv (track world-sig)
                               entities (:entities @world-iv)]
                           (swap! render-count inc)
                           (render-world-view entities)))]

           ;; Initial render
           (render/render-spin! nil app-spin discharge)
           @app-spin
           (is (= 1 @render-count))

           ;; Verify elements created
           (is (some #(= :div (:tag %)) @log) "Should create div elements")

           ;; Update one entity
           (reset! log [])
           (swap! world-sig update-entity "e1" :health 80)
           (await-drain rt)

           ;; Should have re-rendered
           (is (= 2 @render-count) "Should re-render after entity update"))))))

#?(:clj
   (deftest test-add-entity-triggers-render
     (testing "Adding entity triggers re-render"
       (th/with-ctx [rt]
         (let [{:keys [discharge]} (disch/make-mock-discharge)
               world-sig (sig/signal (make-world [(make-entity "e1" :health 100)]))
               entity-counts (atom [])

               app-spin (spin
                         (let [world-iv (track world-sig)
                               entities (:entities @world-iv)]
                           (swap! entity-counts conj (count entities))
                           (render-world-view entities)))]

           (render/render-spin! nil app-spin discharge)
           @app-spin
           (is (= [1] @entity-counts))

           ;; Add entity
           (swap! world-sig add-entity (make-entity "e2" :health 50))
           (await-drain rt)

           (is (= [1 2] @entity-counts) "Should render with 2 entities")

           ;; Add another
           (swap! world-sig add-entity (make-entity "e3" :health 75))
           (await-drain rt)

           (is (= [1 2 3] @entity-counts) "Should render with 3 entities"))))))

#?(:clj
   (deftest test-remove-entity-triggers-render
     (testing "Removing entity triggers re-render"
       (th/with-ctx [rt]
         (let [{:keys [discharge]} (disch/make-mock-discharge)
               world-sig (sig/signal (make-world [(make-entity "e1" :health 100)
                                                  (make-entity "e2" :health 50)
                                                  (make-entity "e3" :health 75)]))
               entity-counts (atom [])

               app-spin (spin
                         (let [world-iv (track world-sig)
                               entities (:entities @world-iv)]
                           (swap! entity-counts conj (count entities))
                           (render-world-view entities)))]

           (render/render-spin! nil app-spin discharge)
           @app-spin
           (is (= [3] @entity-counts))

           ;; Remove entity
           (swap! world-sig remove-entity "e2")
           (await-drain rt)

           (is (= [3 2] @entity-counts) "Should render with 2 entities"))))))

#?(:clj
   (deftest test-sparse-updates-efficient
     (testing "Updating 1 of 100 entities only re-renders once"
       (th/with-ctx [rt]
         (let [{:keys [discharge]} (disch/make-mock-discharge)
               ;; Create world with 100 entities
               initial-entities (for [i (range 100)]
                                  (make-entity (str "e" i) :health 100))
               world-sig (sig/signal (make-world initial-entities))
               render-count (atom 0)

               app-spin (spin
                         (let [world-iv (track world-sig)
                               entities (:entities @world-iv)]
                           (swap! render-count inc)
                           (render-world-view entities)))]

           (render/render-spin! nil app-spin discharge)
           @app-spin
           (is (= 1 @render-count))

           ;; Update just ONE entity
           (swap! world-sig update-entity "e50" :health 80)
           (await-drain rt)

           ;; Should only have rendered twice total (initial + one update)
           (is (= 2 @render-count) "Should only render once for single entity update"))))))

;; =============================================================================
;; Exploration Results & Findings
;; =============================================================================
;;
;; WHAT WORKS WELL:
;;
;; 1. DELTA SCALING
;;    - Updating 1 entity in 100-entity world produces 1 delta (verified)
;;    - Adding/removing entities produces single deltas
;;    - Consumers see only what changed
;;
;; 2. SIGNAL INTEGRATION
;;    - World state in signals works correctly
;;    - Spins track world changes via track effect
;;    - Deltas propagate through the reactive system
;;
;; 3. ENTITY CRUD
;;    - Add/remove/update entities all produce correct delta types
;;    - Nested deltaable structure (world -> entities -> entity) works
;;
;; ISSUES FOUND (AND FIXED):
;;
;; 1. DeltaableMap ITERATOR BUG (FIXED)
;;    - `keys` on DeltaableMap was failing - AbstractMethodError: iterator() is abstract
;;    - Fixed by adding java.lang.Iterable and IMapIterable to DeltaableMap
;;    - Now (keys deltaable-map) works correctly
;;
;; 2. ENTITY vs COMPONENT GRANULARITY
;;    - Updates happen at entity level, not component level
;;    - Updating :position replaces whole entity in the map
;;    - For finer granularity, would need component-level deltaables
;;
;; 3. TICK PRODUCES N DELTAS
;;    - Physics tick updates ALL entities -> N deltas
;;    - This is correct but means no savings for "everything moves"
;;    - Benefit is for partial updates (sparse changes)
;;
;; RECOMMENDATIONS FOR GAME USE:
;;
;; 1. USE FOR: Turn-based games, sparse updates, AI planning
;;    - Chess: only moved piece produces delta
;;    - Card games: hand changes produce targeted deltas
;;    - Strategy: selected units update, others static
;;
;; 2. LESS SUITED FOR: Physics-heavy real-time games
;;    - Everything moves every frame -> no delta savings
;;    - But could still use for non-physics state (inventory, UI, etc.)
;;
;; 3. FORKING IS POWERFUL
;;    - O(1) fork-context for speculative AI planning
;;    - Evaluate "what if I do X" without cloning world
;;    - Discard fork after evaluation
;;
;; NEXT EXPLORATION AREAS:
;;
;; 1. Spatial partitioning with deltas
;;    - Deltaable quadtree/grid
;;    - Movement -> update spatial index -> delta for affected cells
;;
;; 2. Component-level deltaables
;;    - Each component (position, health) as separate deltaable
;;    - More granular deltas but more complex structure
;;
;; 3. Render integration test
;;    - Entity deltas -> ifor-each -> vnode deltas
;;    - Verify only changed entities re-render
;;
;; 4. Fork-based AI planning
;;    - Fork world, simulate N moves, score, discard
;;    - Compare performance to full cloning
;;

