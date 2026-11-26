(ns org.replikativ.spindel.v2.dom.render-cljc-test
  "The mount lifecycle on both platforms (phase-d design §3.6, the CLJS
   subset of §8 P4: M1, M2, M8). M1 runs on a world that is not inline,
   so deliveries cross turns (macrotasks on JS); M2 and M8 on an inline
   world, where a commit lands before the operation that caused it
   returns."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing async]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track await]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]))

(defn- later
  "Runs `f` after `ms` milliseconds: a JVM future, a JS timer."
  [ms f]
  #?(:clj (future (Thread/sleep ms) (f))
     :cljs (js/setTimeout f ms)))

(defn- in-world
  "Calls `(f w done)` with a fresh world made with `opts` bound; the test
   ends at `(done)`."
  [opts f]
  #?(:clj (let [w (v2/world opts)
                p (promise)]
            (try (binding [v2/*world* w] (f w #(deliver p true)))
                 (is (true? (deref p 5000 false)) "the test completes")
                 (finally (v2/release-world! w))))
     :cljs (async done
                  (let [w (v2/world opts)]
                    (binding [v2/*world* w]
                      (f w (fn [] (v2/release-world! w) (js/setTimeout done 0))))))))

(defn- text [m] (mock/dom (:discharge m) :container))

(deftest m1-a-queued-delivery-does-not-commit-after-unmount
  ;; another observer, registered before the mount, unmounts it in the
  ;; callback batch that also holds the mount's delivery
  (in-world {:inline? false :budget 8}
            (fn [_w done]
              (let [m (mock/make-mock)
                    s (v2/signal 1)
                    root (spin (el/div (str (iv/get-new (track s)))))
                    ctl (volatile! nil)]
                (v2/observe! root (fn [vn _]
                                    (when (= "2" (get-in vn [:children 0 :content]))
                                      ((:unmount! @ctl)))))
                (let [{:keys [state] :as c} (render/render! :container root (:discharge m))]
                  (vreset! ctl c)
                  (render/on-revision state 1
                                      (fn [_]
                                        (v2/write! s 2)
                                        (later 50 (fn []
                                                    (is (= :unmounted (render/phase state)))
                                                    (is (= 1 (render/revision state)) "the queued delivery did not commit")
                                                    (is (empty? (text m)))
                                                    (is (render/clean? state))
                                                    (done))))))))))

(deftest m2-unmount-from-a-ref-during-the-first-commit
  (in-world {}
            (fn [_w done]
              (let [m (mock/make-mock)
                    d (v2/deferred)
                    log (atom [])
                    ctl (volatile! nil)
                    root (spin (let [x (await d)]
                                 (el/div {:ref (fn [el] (swap! log conj [:outer (some? el)]))}
                                         (el/span {:ref (fn [el]
                                                          (swap! log conj [:inner (some? el)])
                                                          ((:unmount! @ctl))
                                                          ((:unmount! @ctl)))}
                                                  (str x)))))
                    {:keys [state] :as c} (render/render! :container root (:discharge m))]
                (vreset! ctl c)
                (v2/deliver! d "x")
                (is (= :unmounted (render/phase state)) "the commit completed, then the teardown")
                (is (= [[:inner true] [:inner false]] @log))
                (is (= 1 (render/revision state)))
                (is (empty? (text m)))
                (is (render/clean? state))
                (done)))))

(deftest m8-stop-from-a-ref-during-a-commit
  (in-world {}
            (fn [_w done]
              (let [m (mock/make-mock)
                    d (v2/deferred)
                    s (v2/signal 1)
                    log (atom [])
                    ctl (volatile! nil)
                    root (spin (let [_ (await d) x (iv/get-new (track s))]
                                 (el/div {:ref (fn [el] (swap! log conj [:outer (some? el)]))}
                                         (el/span {:ref (fn [el]
                                                          (swap! log conj [:inner (some? el)])
                                                          (when el ((:stop! @ctl))))}
                                                  (str x)))))
                    {:keys [state] :as c} (render/render! :container root (:discharge m))]
                (vreset! ctl c)
                (v2/deliver! d true)
                (is (= :stopped (render/phase state)))
                (is (= [[:inner true] [:outer true]] @log))
                (v2/write! s 2)
                (is (= 1 (render/revision state)) "no later commit")
                (is (= [[:div {} [:span {} "1"]]] (text m)) "the DOM stays")
                ((:unmount! c))
                (is (= :unmounted (render/phase state)))
                (is (empty? (text m)))
                (is (render/clean? state))
                (is (= [[:inner true] [:outer true] [:outer false] [:inner false]] @log))
                (done)))))
