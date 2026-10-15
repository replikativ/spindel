(ns org.replikativ.spindel.dom.ref-linkage-test
  "Mount refs fire on ATTACHED elements (engine-formalism §3.9 R5).

   `render-initial!` builds a subtree detached; its parent attaches it only
   after it returns. Refs used to fire from inside it, so a `:ref` /
   `foreign-node` `:on-mount` saw a node with no parent — `.isConnected`
   false, `.closest` nil, no layout — and every consumer deferred with
   requestAnimationFrame. Mount refs are now a commit-time effect: queued
   during the commit, fired once its DOM writes have landed.

   These run on the real jsdom harness (same reasoning as
   `jsdom-final-state-test`: MockDischarge has no tree to be connected to).
   Each ref records what it can SEE at the moment it fires, and the
   assertions are on that observation, not on the final tree.

   Coordination: `comb/sleep` is how a CLJS test yields to the event loop
   the engine's own async ops resolve on — see `jsdom-final-state-test`."
  (:refer-clojure :exclude [await])
  (:require [cljs.test :refer-macros [is testing use-fixtures]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.browser :as browser]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.dom.foreign :as foreign :refer-macros [foreign-node]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.spin.cps :refer-macros [spin]]
            [org.replikativ.spindel.test-async :refer [<?] :refer-macros [deftest-async <?]]
            ["jsdom" :refer [JSDOM]]))

(def ^:private current-test-ctx (atom nil))

(use-fixtures :each
  {:before (fn [] (let [c (ctx/create-execution-context)]
                    (reset! current-test-ctx c)
                    (set! ec/*execution-context* c)
                    (disch/collect-violations!)))
   :after  (fn [] (when-let [c @current-test-ctx]
                    (ctx/stop-context! c)
                    (set! ec/*execution-context* nil)
                    (reset! current-test-ctx nil)))})

(defn- fresh-body []
  (let [dom (JSDOM. "<!DOCTYPE html><html><body></body></html>")]
    (.-body (.-document (.-window dom)))))

(defn- integrity-clean? []
  (let [vs (disch/drain-violations!)]
    (or (empty? vs) vs)))

(defn- recorder
  "A ref fn that appends, per mount, what the element can see right now:
   whether it is in the document, whether `.closest` reaches the app root,
   and whether its parent is set. Unmounts (nil) are recorded as such."
  [log label]
  (fn [el]
    (swap! log conj
           (if el
             {:label label
              :connected? (.-isConnected el)
              :closest? (some? (.closest el ".app-root"))
              :parent? (some? (.-parentNode el))}
             {:label label :unmount true}))))

(defn- mounts [log label]
  (filterv #(and (= label (:label %)) (not (:unmount %))) @log))

(defn- linked? [m]
  (and (:connected? m) (:closest? m) (:parent? m)))

;; =============================================================================
;; Initial mount — and the ordering contract
;; =============================================================================

(deftest-async initial-mount-refs-see-the-attached-tree
  (testing "refs on the initial mount fire connected, in post-order"
    (let [body (fresh-body)
          discharge (browser/make-dom-discharge (.-ownerDocument body))
          log (atom [])
          foreign-seen (atom nil)
          root (spin
                (el/div {:class "app-root" :ref (recorder log :root)}
                        (el/section {:ref (recorder log :section)}
                                    (el/span {:ref (recorder log :leaf-1)} "a")
                                    (el/span {:ref (recorder log :leaf-2)} "b"))
                        (foreign-node
                         {:class "foreign"
                          :on-mount (fn [el]
                                      (reset! foreign-seen
                                              {:connected? (.-isConnected el)
                                               :closest? (some? (.closest el ".app-root"))}))
                          :on-unmount (fn [_])})))]
      (render/render-spin! body root discharge)
      (<? (comb/sleep 50))
      (is (= [:leaf-1 :leaf-2 :section :root] (mapv :label @log))
          "post-order: descendants before their ancestor, siblings left to right")
      (is (every? linked? @log)
          (str "every ref saw an attached, connected element: " @log))
      (is (= {:connected? true :closest? true} @foreign-seen)
          "foreign-node :on-mount sees its ancestor")
      (is (true? (integrity-clean?))))))

;; =============================================================================
;; ifor-each item insert
;; =============================================================================

(deftest-async inserted-item-ref-sees-the-attached-tree
  (testing "a grown ifor-each item's ref fires on an element inside the list"
    (let [body (fresh-body)
          discharge (browser/make-dom-discharge (.-ownerDocument body))
          log (atom [])
          items (sig/signal [{:id "a"}])
          item-fn (fn [{:keys [id]}]
                    (spin (el/li {:key id :class "item"
                                  :ref (recorder log (keyword id))}
                                 id)))
          root (spin
                (let [{xs :new} (track items)
                      frag (await (foreach/for-each*
                                   {:file "ref-linkage" :line 1 :column 1}
                                   :id item-fn xs))]
                  (el/ul {:class "app-root"} frag)))]
      (render/render-spin! body root discharge)
      (<? (comb/sleep 50))
      (swap! items conj {:id "b"})
      (<? (comb/sleep 50))
      (swap! items #(into [{:id "c"}] %))
      (<? (comb/sleep 50))
      (is (= 3 (.-length (.querySelectorAll body ".item"))))
      (is (= 1 (count (mounts log :b))) "the appended item mounted once")
      (is (= 1 (count (mounts log :c))) "the prepended item mounted once")
      (is (every? linked? (mounts log :b)) (str (mounts log :b)))
      (is (every? linked? (mounts log :c)) (str (mounts log :c)))
      (is (every? linked? (mounts log :a)) (str (mounts log :a)))
      (is (true? (integrity-clean?))))))

;; =============================================================================
;; Conditional subtree flip (commit walk) and root replacement (re-mount)
;; =============================================================================

(deftest-async conditional-flip-ref-sees-the-attached-tree
  (testing "a subtree created by a conditional flip mounts attached"
    (let [body (fresh-body)
          discharge (browser/make-dom-discharge (.-ownerDocument body))
          log (atom [])
          open? (sig/signal false)
          root (spin
                (let [{o :new} (track open?)]
                  (el/div {:class "app-root"}
                          (if o
                            (el/section {:class "open" :ref (recorder log :open)}
                                        (el/em {:ref (recorder log :open-child)} "x"))
                            (el/p {:class "closed" :ref (recorder log :closed)} "-")))))]
      (render/render-spin! body root discharge)
      (<? (comb/sleep 50))
      (reset! open? true)
      (<? (comb/sleep 50))
      (reset! open? false)
      (<? (comb/sleep 50))
      (is (= 1 (count (mounts log :open))))
      (is (= 2 (count (mounts log :closed))) "initial mount + flip back")
      (is (every? linked? (concat (mounts log :open)
                                  (mounts log :open-child)
                                  (mounts log :closed)))
          (str @log))
      (is (= [:open-child :open]
             (->> @log (remove :unmount) (map :label)
                  (filter #{:open :open-child})))
          "post-order inside the flipped-in subtree")
      (is (true? (integrity-clean?))))))

(deftest-async root-replacement-ref-sees-the-attached-tree
  (testing "a changed root re-mounts, and its refs fire attached"
    (let [body (fresh-body)
          discharge (browser/make-dom-discharge (.-ownerDocument body))
          log (atom [])
          mode (sig/signal :a)
          root (spin
                (let [{m :new} (track mode)]
                  (if (= m :a)
                    (el/div {:class "app-root" :ref (recorder log :root-a)}
                            (el/span {:ref (recorder log :leaf-a)} "a"))
                    (el/main {:class "app-root" :ref (recorder log :root-b)}
                             (el/span {:ref (recorder log :leaf-b)} "b")))))]
      (render/render-spin! body root discharge)
      (<? (comb/sleep 50))
      (reset! mode :b)
      (<? (comb/sleep 50))
      (is (= 1 (count (mounts log :root-b))))
      (is (every? linked? (concat (mounts log :root-a) (mounts log :leaf-a)
                                  (mounts log :root-b) (mounts log :leaf-b)))
          (str @log))
      (is (true? (integrity-clean?))))))

;; =============================================================================
;; A superseded build fires no refs
;; =============================================================================
;;
;; Builds are pure values (R3): a vnode carrying a :ref is just data until a
;; commit renders it. The value 1 below is overwritten while its body slice is
;; still parked on the await, so the build for 1 is never what the DOM
;; receives — and its ref must never run.

(deftest-async superseded-build-fires-no-refs
  (testing "a build abandoned before commit never fires its refs"
    (let [body (fresh-body)
          discharge (browser/make-dom-discharge (.-ownerDocument body))
          log (atom [])
          v (sig/signal 0)
          started (atom [])
          root (spin
                (let [{x :new} (track v)]
                  (swap! started conj x)
                  (await (comb/sleep 20))
                  (el/div {:class "app-root"}
                          (el/span {:key (str "v" x) :class "val"
                                    :ref (recorder log x)}
                                   (str x)))))]
      (render/render-spin! body root discharge)
      (<? (comb/sleep 60))
      (reset! v 1)
      (<? (comb/sleep 1))
      (reset! v 2)
      (<? (comb/sleep 100))
      (is (some #{1} @started) "the build for 1 did start")
      (is (= "2" (.-textContent (.querySelector body ".val"))))
      (is (empty? (mounts log 1)) (str "superseded build fired refs: " @log))
      (is (= 1 (count (mounts log 2))))
      (is (every? linked? (mounts log 2)) (str (mounts log 2)))
      (is (true? (integrity-clean?))))))
