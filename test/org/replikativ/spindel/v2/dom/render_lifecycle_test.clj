(ns org.replikativ.spindel.v2.dom.render-lifecycle-test
  "The mount lifecycle on engine v2 (phase-d design §3.5, §3.6 M1-M10,
   §5.1-§5.3; addendum §3.8.4, §3.8.8): render! observes the root, its
   observe callback stores the delivery and posts one flush item to the
   world, and the flush commits the newest delivery the mount holds. A
   stop or unmount asked for while the mount runs user code is held in
   the request slot until that code returns. The ledger holds the
   successful setups whose cleanup has not yet been claimed. A failed
   commit runs no new setup and cleans up the ledger. Tests synchronize on
   the committed render revision."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track await]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(defn- ref-fn
  "A ref recording `[tag attached?]`; it returns no cleanup, so its
   cleanup is `(f nil)`."
  [log tag]
  (fn [el] (swap! log conj [tag (some? el)])))

(defn- once-each?
  "Whether every tag in `log` saw exactly one element call and one nil call."
  [log]
  (every? (fn [[_ calls]] (= #{[true 1] [false 1]} (set (frequencies (map second calls)))))
          (group-by first log)))

(defn- dom [env] (mock/dom (:discharge (:mock env)) :container))

(defn- clears
  "How many times the mock's container was cleared (initial mounts and
   teardowns)."
  [env]
  (count (filter #(= :clear-container (:op %)) @(:log (:mock env)))))

;; ---------------------------------------------------------------------------
;; Static root, updates, revision

(deftest static-root-render-and-unmount
  (fx/each-world
   (fn [env]
     (let [root (spin (el/div {:id "r"} (el/p "hello")))
           {:keys [state] :as ctl} (fx/render! env root)]
       (is (= :mounted (render/phase state)))
       (is (= 1 (render/revision state)))
       (is (= [[:div {:id "r"} [:p {} "hello"]]] (dom env)))
       (is (identical? (fx/read! env root) (render/committed state))
           "the committed vdom is the root's value")
       (fx/unmount! env ctl)
       (is (fx/closed? env state))
       (is (= ::render/unmounted (render/await-revision state 5 100)) "a later waiter is released")
       (testing "unmount is idempotent"
         (fx/unmount! env ctl)
         (is (= :unmounted (render/phase state)))
         (is (= 2 (clears env))))
       (is (empty? (fx/violations)))))))

(deftest updates-commit-through-the-store
  (fx/each-world
   (fn [env]
     (let [s (v2/signal 1)
           root (spin (let [x (iv/get-new (track s))]
                        (el/div {:class (str "c" x)} (str x))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (is (= [[:div {:class "c1"} "1"]] (dom env)))
       (fx/write! env s 2)
       (is (= [[:div {:class "c2"} "2"]] (dom env)))
       (is (= 2 (render/revision state)))
       (is (identical? (fx/read! env root) (render/committed state)))
       (fx/unmount! env ctl)
       (fx/write! env s 3)
       (is (= 2 (render/revision state)) "no commit after teardown")
       (is (fx/closed? env state))))))

(deftest the-revision-waiter
  (fx/with-world
    {}
    (fn [env]
      (let [s (v2/signal 1)
            root (spin (el/div (str (iv/get-new (track s)))))
            {:keys [state] :as ctl} (fx/render! env root)]
        (is (= :ok (render/await-revision state 1 10)) "reached: returns at once")
        (is (= ::render/timeout (render/await-revision state 2 10)))
        (let [f (future (render/await-revision state 2 5000))]
          (Thread/sleep 20)
          (fx/write! env s 2)
          (is (= :ok (deref f 5000 :hung)) "a commit wakes the waiter"))
        (let [f (future (render/await-revision state 10 5000))]
          (Thread/sleep 20)
          (fx/unmount! env ctl)
          (is (= ::render/unmounted (deref f 5000 :hung)) "teardown releases it"))
        (testing "on-revision calls back"
          (let [seen (atom nil)]
            (render/on-revision state 1 #(reset! seen %))
            (is (= ::render/unmounted @seen))))))))

;; ---------------------------------------------------------------------------
;; M1: a delivery queued before :stop!/:unmount! does not commit afterwards.
;; Another observer of the root makes the request in the same callback batch
;; as the mount's delivery: registered before the mount, its callback runs
;; first and the mount's delivery is still queued; registered after, the
;; mount has already posted its flush.

(deftest m1-a-queued-delivery-does-not-commit-after-a-request
  (doseq [request [:unmount! :stop!]
          order [:callback-queued :flush-posted]]
    (testing (str request " " order)
      (fx/with-world
        {:inline? false :budget 8}
        (fn [env]
          (let [s (v2/signal 1)
                root (spin (el/div (str (iv/get-new (track s)))))
                ctl (volatile! nil)
                other (fn [v _]
                        (when (= "2" (get-in v [:children 0 :content]))
                          ((get @ctl request))))
                _ (when (= order :callback-queued) (v2/observe! root other))
                {:keys [state] :as c} (fx/render! env root)]
            (vreset! ctl c)
            (when (= order :flush-posted) (v2/observe! root other))
            (fx/settle! env)
            (fx/write! env s 2)
            (is (= 1 (render/revision state)) "the queued delivery did not commit")
            (is (= (if (= request :unmount!) :unmounted :stopped) (render/phase state)))
            (if (= request :unmount!)
              (is (fx/closed? env state))
              (is (= [[:div {} "1"]] (dom env)) "a stopped mount keeps its DOM"))
            (fx/write! env s 3)
            (is (= 1 (render/revision state)) "and nothing later commits")))))))

;; ---------------------------------------------------------------------------
;; M2: :unmount! from a mount ref during the first commit

(deftest m2-unmount-from-a-ref-during-the-first-commit
  (fx/each-world
   (fn [env]
     (let [d (v2/deferred)
           log (atom [])
           ctl (volatile! nil)
           unmount! #((:unmount! @ctl))
           root (spin (let [x (await d)]
                        (el/div {:ref (ref-fn log :outer)}
                                (el/span {:ref (fn [el]
                                                 (swap! log conj [:inner (some? el)])
                                                 ;; twice during the commit, and once from its
                                                 ;; nil call during the teardown
                                                 (unmount!) (unmount!))}
                                         (str x)))))
           {:keys [state] :as c} (fx/render! env root)]
       (vreset! ctl c)
       (is (= :pending (render/phase state)))
       (v2/deliver! d "x")
       (fx/settle! env)
       (is (= :unmounted (render/phase state)) "the commit completed, then the teardown")
       (is (= [[:inner true] [:inner false]] @log)
           "the outer ref, after the request, never ran; the inner one is claimed once")
       (is (= 1 (render/revision state)) "the commit counted")
       (is (= 2 (clears env)) "one mount, one teardown")
       (is (fx/closed? env state))))))

(deftest m2-a-ref-writes-a-signal-of-its-world
  (fx/each-world
   (fn [env]
     (let [d (v2/deferred)
           s (v2/signal 1)
           wrote (atom nil)
           root (spin (let [_ (await d) x (iv/get-new (track s))]
                        (el/div {:ref (fn [el] (when el (reset! wrote (v2/write! s 5))))} (str x))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (v2/deliver! d true)
       (fx/settle! env)
       (is (= 5 @wrote) "the write ran at once")
       (is (= 2 (render/revision state)) "the next delivery committed after the first commit")
       (is (= [[:div {} "5"]] (dom env)))
       (fx/unmount! env ctl)
       (is (fx/closed? env state))))))

;; ---------------------------------------------------------------------------
;; M3: :unmount! from another thread during a slow commit waits for it

(deftest m3-unmount-from-another-thread-waits-for-a-slow-commit
  (fx/with-world
    {}
    (fn [env]
      (let [s (v2/signal 1)
            in-commit (promise)
            release (promise)
            root (spin (let [x (iv/get-new (track s))]
                         (el/div (if (= x 2)
                                   (el/span {:ref (fn [el] (when el (deliver in-commit true) @release nil))} "slow")
                                   (el/i "fast")))))
            {:keys [state] :as ctl} (fx/render! env root)
            writer (future (v2/write! s 2))]
        (is (true? (deref in-commit 5000 false)) "the slow commit runs")
        (let [unmounter (future ((:unmount! ctl)) :done)]
          (Thread/sleep 50)
          (is (not (realized? unmounter)) "the unmount waits for the commit")
          (deliver release true)
          (is (= :done (deref unmounter 5000 :hung))))
        (deref writer 5000 nil)
        (fx/settle! env)
        (is (= 2 (render/revision state)) "the slow commit completed; none after the teardown")
        (is (fx/closed? env state))))))

;; ---------------------------------------------------------------------------
;; M4: the control object kept after unmount holds no tree

(deftest m4-the-control-object-holds-no-tree-after-unmount
  (fx/with-world
    {:verify? false}
    (fn [env]
      (let [kept (atom nil)
            {:keys [state] :as ctl} (let [root (spin (let [child (spin (el/span "child"))]
                                                       (reset! kept child)
                                                       (el/div (await child))))
                                          c (fx/render! env root)]
                                      (v2/release! root)
                                      c)
            weak (java.lang.ref.WeakReference. (render/committed state))]
        (is (some? (.get weak)))
        (fx/unmount! env ctl)
        (is (nil? (render/committed state)))
        (verify/gc-settle! (:w env))
        (fx/settle! env)
        (verify/gc-settle! (:w env))
        (is (nil? (.get weak)) "the vnode tree is collectable")
        (is (some? @kept) "while a child computation is still kept")
        (is (= :unmounted (render/phase (:state ctl))))))))

;; ---------------------------------------------------------------------------
;; M5: two mounts of one world share nothing

(deftest m5-two-mounts-of-one-world
  (fx/each-world
   (fn [env]
     (let [s (v2/signal 1)
           log (atom [])
           r1 (spin (el/div {:id "a" :ref (ref-fn log :a)} (str (iv/get-new (track s)))))
           r2 (spin (el/div {:id "b" :ref (ref-fn log :b)} (str (iv/get-new (track s)))))
           m2 (mock/make-mock)
           c1 (fx/render! env r1)
           c2 (render/render! :container r2 (:discharge m2))]
       (fx/settle! env)
       (fx/unmount! env c1)
       (fx/write! env s 2)
       (is (fx/closed? env (:state c1)))
       (is (= [[:div {:id "b"} "2"]] (mock/dom (:discharge m2) :container)) "the other mount still commits")
       (is (= 2 (render/revision (:state c2))))
       (is (= 1 (count (render/ledger (:state c2)))))
       (is (= 1 (count @(:elements m2))))
       (is (= [[:a true] [:b true] [:a false]] @log))
       (fx/unmount! env c2)
       (is (once-each? @log))))))

;; ---------------------------------------------------------------------------
;; M6, M7: a failed commit

(defn- failing-root
  "A div with an optional `p` (ref :x) in slot 0 and, in slot 1, an `i`, or
   for x = 2 a `span` whose creation the mock fails when told to."
  [s log]
  (spin (let [x (iv/get-new (track s))]
          (el/div {:ref (ref-fn log :root)}
                  (when (>= x 2) (el/p {:ref (ref-fn log :x)} "x"))
                  (if (= x 2) (el/span "bad") (el/i (str x)))))))

(defn- fail-span! [env on?]
  (mock/fail-when! (:discharge (:mock env))
                   (when on? (fn [op] (and (= :create-element (:op op)) (= :span (:tag op)))))))

(deftest m6-m7-a-failed-commit-cleans-up-and-the-next-delivery-remounts
  (fx/each-world
   (fn [env]
     (let [s (v2/signal 1)
           log (atom [])
           {:keys [state] :as ctl} (fx/render! env (failing-root s log))]
       (fail-span! env true)
       (fx/write! env s 2)
       (is (= :failed (render/phase state)))
       (is (= [[:root true] [:root false]] @log)
           "M7: the ref of the subtree the failed commit attached never ran; the mounted ones are claimed")
       (is (empty? (render/ledger state)) "M6: the ledger is empty")
       (is (empty? @(:elements (:mock env))) "no stale registry entry")
       (is (empty? (mock/children (:discharge (:mock env)) :container)))
       (is (= 1 (render/revision state)) "a failed commit does not count")
       (is (some? (render/error state)))
       (fail-span! env false)
       (fx/write! env s 3)
       (is (= :mounted (render/phase state)) "the next delivery remounts")
       (is (= [[:div {} [:p {} "x"] [:i {} "3"]]] (dom env)))
       (is (nil? (render/error state)))
       (is (= [[:root true] [:root false] [:x true] [:root true]] @log))
       (fx/unmount! env ctl)
       (is (fx/closed? env state))))))

;; ---------------------------------------------------------------------------
;; M8: :stop! from a mount ref during a commit

(deftest m8-stop-from-a-ref-during-a-commit
  (fx/each-world
   (fn [env]
     (let [d (v2/deferred)
           s (v2/signal 1)
           log (atom [])
           ctl (volatile! nil)
           root (spin (let [_ (await d) x (iv/get-new (track s))]
                        (el/div {:ref (ref-fn log :outer)}
                                (el/span {:ref (fn [el]
                                                 (swap! log conj [:inner (some? el)])
                                                 (when el ((:stop! @ctl))))}
                                         (str x)))))
           {:keys [state] :as c} (fx/render! env root)]
       (vreset! ctl c)
       (v2/deliver! d true)
       (fx/settle! env)
       (is (= :stopped (render/phase state)))
       (is (= [[:inner true] [:outer true]] @log) "a stop lets the commit run everything")
       (fx/write! env s 2)
       (is (= 1 (render/revision state)) "no later commit")
       (is (= [[:div {} [:span {} "1"]]] (dom env)) "the DOM stays")
       (fx/unmount! env c)
       (is (fx/closed? env state))
       (is (once-each? @log))))))

;; ---------------------------------------------------------------------------
;; M9: a request from a removal cleanup, then the walk fails

(deftest m9-a-request-during-a-commit-that-then-fails
  (doseq [request [:unmount! :stop!]]
    (testing request
      (fx/each-world
       (fn [env]
         (let [s (v2/signal 1)
               ctl (volatile! nil)
               root (spin (let [x (iv/get-new (track s))]
                            (el/div (when (= x 1)
                                      (el/p {:ref (fn [_] #((get @ctl request)))} "p"))
                                    (if (= x 2) (el/span "bad") (el/i "ok")))))
               {:keys [state] :as c} (fx/render! env root)]
           (vreset! ctl c)
           (fail-span! env true)
           (fx/write! env s 2)
           (is (= (if (= request :unmount!) :unmounted :stopped) (render/phase state))
               "never :failed")
           (when (= request :stop!) (fx/unmount! env c))
           (is (fx/closed? env state))))))))

;; ---------------------------------------------------------------------------
;; M10: the observe error ::released

(deftest m10-a-released-world-stops-the-mount
  (fx/each-world
   (fn [env]
     (let [log (atom [])
           root (spin (el/div {:ref (ref-fn log :r)} "r"))
           {:keys [state] :as ctl} (fx/render! env root)]
       (v2/release-world! (:w env))
       (fx/settle! env)
       (is (= :stopped (render/phase state)))
       (is (= [[:div {} "r"]] (dom env)) "the DOM stays")
       (fx/unmount! env ctl)
       (is (fx/closed? env state) "a later :unmount! tears down")
       (is (once-each? @log))))))

;; ---------------------------------------------------------------------------
;; C2a: the mount coalesces its deliveries (addendum §3.8.8)

(defn- vnode [i] (el/div {:id (str "v" i)} (str i)))

(deftest cb3b-deliveries-stored-before-the-flush-commit-once
  (fx/each-world
   (fn [env]
     (let [v (v2/signal (vnode 0))
           {:keys [state] :as ctl} (fx/render! env v)]
       (v2/host! (:w env) #(do (reset! v (vnode 1)) (reset! v (vnode 2))))
       (fx/settle! env)
       (is (= 2 (render/revision state)) "two deliveries, one commit")
       (is (= [[:div {:id "v2"} "2"]] (dom env)) "of the newest")
       (fx/unmount! env ctl)))))

(deftest cb3c-a-write-queued-behind-the-flush-commits-in-a-second-flush
  (fx/each-world
   (fn [env]
     (let [s (v2/signal 1)
           w (:w env)
           root (spin (el/div (str (iv/get-new (track s)))))
           {:keys [state] :as ctl} (fx/render! env root)
           _ (v2/observe! root (fn [vn _]
                                 (when (= "2" (get-in vn [:children 0 :content]))
                                   (v2/send-world! w #(v2/write! s 3)))))]
       (fx/settle! env)
       (fx/write! env s 2)
       (is (= 3 (render/revision state)) "the flush committed the older delivery, a second one the newest")
       (is (= [[:div {} "3"]] (dom env)))
       (fx/unmount! env ctl)))))

(deftest cb3d-a-callback-batch-split-across-turns
  (fx/with-world
    {:inline? false :budget 8}
    (fn [env]
      (let [v (v2/signal (vnode 0))
            {:keys [state] :as ctl} (fx/render! env v)]
        (v2/host! (:w env) #(dotimes [i 10] (reset! v (vnode (inc i)))))
        (fx/settle! env)
        (is (= [[:div {:id "v10"} "10"]] (dom env)) "the final committed tree is the newest delivery")
        (is (<= 2 (render/revision state) 3)
            "split batches (#364): the flush can commit a delivery from the first part; at most two commits")
        (fx/unmount! env ctl)
        (v2/host! (:w env) #(dotimes [i 10] (reset! v (vnode (+ 20 i)))))
        (fx/settle! env)
        (is (fx/closed? env state) "no commit after :unmount!")))))

(deftest cb4-ordinary-observers-are-untouched
  (fx/each-world
   (fn [env]
     (let [s (v2/signal [])
           seen (atom [])
           deltas (atom [])
           root (spin (el/ul (str (iv/get-new (track s)))))
           dc (spin (:deltas (track s)))
           {:keys [state] :as ctl} (fx/render! env root)]
       (v2/observe! s (fn [x _] (swap! seen conj x)))
       (v2/observe! dc (fn [x _] (when x (swap! deltas conj x))))
       (fx/settle! env)
       (v2/host! (:w env) #(do (swap! s conj :a) (swap! s conj :b)))
       (fx/settle! env)
       (is (= [[] [:a] [:a :b]] @seen) "a plain observer sees each value")
       (is (= [[{:delta :add :path [0] :value :a} {:delta :add :path [1] :value :b}]] @deltas)
           "a delta-valued observer sees both deltas")
       (is (= [:a :b] (fx/read! env s)) "value-async is unchanged")
       (is (= 2 (render/revision state)) "the mount commits once")
       (fx/unmount! env ctl)))))

(deftest cb6-delivery-kinds
  (fx/each-world
   (fn [env]
     ;; the mount's observe callback fed synthetic deliveries, two per host item
     (let [v (v2/signal (vnode 0))
           w (:w env)]
       (let [{:keys [state] :as ctl} (fx/render! env v)
             deliver! (fn [x err?] (#'render/deliver! state x err?))
             boom (ex-info "boom" {})]
         (testing "error then success in one batch: a commit, no overlay"
           (v2/host! w #(do (deliver! boom true) (deliver! (vnode 1) false)))
           (fx/settle! env)
           (is (= 2 (render/revision state)))
           (is (nil? (render/error state))))
         (testing "success then error: the overlay, the last frame kept"
           (v2/host! w #(do (deliver! (vnode 2) false) (deliver! boom true)))
           (fx/settle! env)
           (is (= 2 (render/revision state)))
           (is (= boom (render/error state)))
           (is (= [[:div {:id "v1"} "1"]] (dom env)))
           (is (= :mounted (render/phase state))))
         (testing "::released with a flush posted: stopped, the flush does nothing"
           (v2/host! w #(do (deliver! (vnode 3) false) (deliver! (v2/released-ex) true)))
           (fx/settle! env)
           (is (= :stopped (render/phase state)))
           (is (= 2 (render/revision state))))
         (fx/unmount! env ctl)
         (is (fx/closed? env state)))))))

(deftest cb6-an-initial-delivery-and-writes-before-the-flush
  (fx/with-world
    {:inline? false :budget 8}
    (fn [env]
      (let [v (v2/signal (vnode 0))
            {:keys [state] :as ctl} (render/render! :container v (:discharge (:mock env)))]
        (v2/write! v (vnode 1))
        (v2/write! v (vnode 2))
        (fx/settle! env)
        (is (= 1 (render/revision state)) "one commit")
        (is (= [[:div {:id "v2"} "2"]] (dom env)) "the first commit shows the newest")
        (fx/unmount! env ctl)))))
