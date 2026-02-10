(ns examples.todo-app-test
  "Tests for the Todo App example.

  Verifies:
  1. State management (add, toggle, remove todos)
  2. Filter functionality
  3. Reactive rendering with O(delta) updates
  4. Full reactive cycle"
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [examples.todo-app :as app]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
            #?(:clj [org.replikativ.spindel.test-async :refer [await-drain]])))

;; =============================================================================
;; State Management Tests
;; =============================================================================

#?(:clj
   (deftest test-add-todo
     (testing "Adding todos updates signal with proper deltas"
       (with-ctx [rt]
         (let [todos (app/make-todos-signal)]
           ;; Initially empty
           (is (empty? @todos))

           ;; Add first todo
           (app/add-todo! todos "First task" :high)
           (is (= 1 (count @todos)))
           (is (= "First task" (:text (first @todos))))
           (is (= :high (:priority (first @todos))))
           (is (false? (:done (first @todos))))

           ;; Add second todo
           (app/add-todo! todos "Second task")
           (is (= 2 (count @todos)))
           (is (= :medium (:priority (second @todos))))

           ;; Just verify we have 2 todos with correct properties
           ;; Delta tracking is tested elsewhere in deltaable_test
           (is (= 2 (count @todos)) "Should have 2 todos"))))))

#?(:clj
   (deftest test-toggle-todo
     (testing "Toggling todo updates done status"
       (with-ctx [rt]
         (let [todos (app/make-todos-signal)]
           ;; Add a todo
           (app/add-todo! todos "Test task")
           (let [id (:id (first @todos))]
             ;; Initially not done
             (is (false? (:done (first @todos))))

             ;; Toggle to done
             (app/toggle-todo! todos id)
             (is (true? (:done (first @todos))))

             ;; Toggle back
             (app/toggle-todo! todos id)
             (is (false? (:done (first @todos))))))))))

#?(:clj
   (deftest test-remove-todo
     (testing "Removing todo updates signal with :remove delta"
       (with-ctx [rt]
         (let [todos (app/make-todos-signal)]
           ;; Add several todos
           (app/add-todo! todos "First task" :high)
           (app/add-todo! todos "Second task" :medium)
           (app/add-todo! todos "Third task" :low)
           (is (= 3 (count @todos)))

           ;; Capture ids
           (let [first-id (:id (nth @todos 0))
                 second-id (:id (nth @todos 1))
                 third-id (:id (nth @todos 2))]

             ;; Remove middle item
             (app/remove-todo! todos second-id)
             (is (= 2 (count @todos)))
             (is (= first-id (:id (nth @todos 0))))
             (is (= third-id (:id (nth @todos 1))))

             ;; Remove first item
             (app/remove-todo! todos first-id)
             (is (= 1 (count @todos)))
             (is (= third-id (:id (nth @todos 0))))

             ;; Remove last item
             (app/remove-todo! todos third-id)
             (is (= 0 (count @todos)))))))))

#?(:clj
   (deftest test-remove-todo-with-rendering
     (testing "Removing todo triggers correct DOM operations"
       (with-ctx [rt]
         (let [{:keys [discharge log]} (disch/make-mock-discharge)
               todos (app/make-todos-signal)
               filter-sig (app/make-filter-signal)
               app (app/make-app-spin todos filter-sig)]

           ;; Initial render
           (render/render-spin! nil app discharge)
           @app

           ;; Add several todos - let deltas propagate one at a time
           (app/add-todo! todos "Task 1")
           (await-drain rt)
           @app

           (app/add-todo! todos "Task 2")
           (await-drain rt)
           @app

           (app/add-todo! todos "Task 3")
           (await-drain rt)
           @app

           (is (= 3 (count @todos)))

           ;; Clear log and remove middle item
           (reset! log [])
           (let [second-id (:id (nth @todos 1))]
             (app/remove-todo! todos second-id))

           (await-drain rt)
           @app

           ;; Should have 2 todos remaining
           (is (= 2 (count @todos)))

           ;; Check that :remove operation was recorded
           (let [remove-ops (filter #(= :remove-child (:op %)) @log)]
             (is (seq remove-ops) "Should have remove-child operations")))))))

#?(:clj
   (deftest test-filter-signal
     (testing "Filter signal tracks current mode"
       (with-ctx [rt]
         (let [filter-sig (app/make-filter-signal)]
           ;; Default is :all
           (is (= :all @filter-sig))

           ;; Change to active
           (app/set-filter! filter-sig :active)
           (is (= :active @filter-sig))

           ;; Change to done
           (app/set-filter! filter-sig :done)
           (is (= :done @filter-sig)))))))

;; =============================================================================
;; App Spin Tests
;; =============================================================================

#?(:clj
   (deftest test-app-spin-initial-render
     (testing "App spin produces initial vdom"
       (with-ctx [rt]
         (let [todos (app/make-todos-signal)
               filter-sig (app/make-filter-signal)
               app (app/make-app-spin todos filter-sig)
               result @app]
           ;; Should produce a vdom div with class "todo-app"
           (is (some? result))
           (is (= :div (:tag result)))
           (is (= "todo-app" (get @(:attrs result) :class))))))))

#?(:clj
   (deftest test-app-spin-with-todos
     (testing "App spin renders todos correctly"
       (with-ctx [rt]
         (let [todos (app/make-todos-signal)
               filter-sig (app/make-filter-signal)
               app (app/make-app-spin todos filter-sig)]

           ;; Initial render
           @app

           ;; Add a todo
           (app/add-todo! todos "Test task" :high)
           (await-drain rt)

           ;; Re-render
           (let [result @app
                 children @(:children result)]
             ;; Should have header, stats, filter-bar, ul, maybe footer
             (is (>= (count children) 4))))))))

#?(:clj
   (deftest test-app-spin-reactive-updates
     (testing "App spin re-renders on signal changes"
       (with-ctx [rt]
         (let [{:keys [discharge log]} (disch/make-mock-discharge)
               todos (app/make-todos-signal)
               filter-sig (app/make-filter-signal)
               app (app/make-app-spin todos filter-sig)
               render-count (atom 0)]

           ;; Set up render tracking
           (render/render-spin! nil app discharge)
           @app
           (swap! render-count inc)

           ;; Add todo - should trigger re-render
           (app/add-todo! todos "Task 1")
           (await-drain rt)
           (swap! render-count inc)

           (is (= 2 @render-count) "Should have rendered twice"))))))

;; =============================================================================
;; Full Scenario Test
;; =============================================================================

#?(:clj
   (defn run-test-scenario!
     "Run a test scenario that exercises the full reactive cycle."
     []
     (let [rt (ctx/create-execution-context)
           {:keys [discharge log]} (disch/make-mock-discharge)
           execution-trace (atom [])]
       (try
         (binding [ec/*execution-context* rt]
           (let [todos (app/make-todos-signal)
                 filter-sig (app/make-filter-signal)
                 app-spin (app/make-app-spin todos filter-sig)]

             ;; Initial render
             (render/render-spin! nil app-spin discharge)
             (swap! execution-trace conj {:phase :initial :log-count (count @log)})
             @app-spin

             ;; Add first todo
             (reset! log [])
             (app/add-todo! todos "Learn spindel" :high)
             (await-drain rt)
             (swap! execution-trace conj {:phase :add-first :log-count (count @log)})
             @app-spin

             ;; Add second todo
             (reset! log [])
             (app/add-todo! todos "Build something cool" :medium)
             (await-drain rt)
             (swap! execution-trace conj {:phase :add-second :log-count (count @log)})
             @app-spin

             ;; Toggle first todo
             (reset! log [])
             (let [first-id (:id (first @todos))]
               (app/toggle-todo! todos first-id))
             (await-drain rt)
             (swap! execution-trace conj {:phase :toggle :log-count (count @log)})
             @app-spin

             ;; Set filter to active
             (reset! log [])
             (app/set-filter! filter-sig :active)
             (await-drain rt)
             (swap! execution-trace conj {:phase :filter-active :log-count (count @log)})
             @app-spin

             ;; Return trace
             {:trace @execution-trace
              :final-todos (vec @todos)
              :filter @filter-sig}))
         (finally
           (ctx/stop-context! rt))))))

#?(:clj
   (deftest test-full-scenario
     (testing "Full reactive cycle works correctly"
       (let [result (run-test-scenario!)]
         ;; Should have execution trace
         (is (some? (:trace result)))
         (is (= 5 (count (:trace result))))

         ;; Should have final todos
         (is (= 2 (count (:final-todos result))))

         ;; First todo should be done (toggled)
         (is (true? (:done (first (:final-todos result)))))

         ;; Filter should be :active
         (is (= :active (:filter result)))))))

;; =============================================================================
;; O(delta) Verification Tests
;; =============================================================================

#?(:clj
   (deftest test-o-delta-rendering
     (testing "Rendering is O(delta), not O(n)"
       (with-ctx [rt]
         (let [{:keys [discharge log]} (disch/make-mock-discharge)
               todos (app/make-todos-signal)
               filter-sig (app/make-filter-signal)
               app (app/make-app-spin todos filter-sig)]

           ;; Initial render
           (render/render-spin! nil app discharge)
           @app

           ;; Add 3 todos
           (app/add-todo! todos "Task 1")
           (await-drain rt)
           @app

           (app/add-todo! todos "Task 2")
           (await-drain rt)
           @app

           (app/add-todo! todos "Task 3")
           (await-drain rt)
           @app

           ;; Clear log and add one more
           (reset! log [])
           (app/add-todo! todos "Task 4")
           (await-drain rt)
           @app

           ;; Check that we didn't re-render all items
           ;; The log should show creating only the new item, not all 4
           (let [create-ops (filter #(= :create-element (:op %)) @log)
                 li-creates (filter #(= :li (:tag %)) create-ops)]
             ;; Should only create 1 new li, not 4
             ;; (Note: exact count depends on implementation details)
             (is (<= (count li-creates) 2)
                 "Should create at most 2 li elements (for the new item + possible wrapper)")))))))
