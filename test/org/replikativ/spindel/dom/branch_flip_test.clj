(ns org.replikativ.spindel.dom.branch-flip-test
  "Characterization: when does a conditional branch flip inside a spin body
  actually reach the DOM?

  Motivated by a simmis production bug: the wiki page editor rendered
  `<div class=\"block-editor loading\"><p>Loading database...</p></div>` forever.
  Its body re-ran with a real db (logged), but the DOM never changed — not even
  the class attribute. Shape (block_editor.cljs `render-page-editor`, a
  SELF-TRACKING child spin awaited by the column spin):

      (if-not db-value
        (el/div {:class \"block-editor loading\" :key K} (el/p \"Loading...\"))
        (el/div {:class \"block-editor\"         :key K} ...the editor...))

  Both branches emit the same tag and the SAME key. Rendering is delta-direct
  (no tree diff): `update-render!` discharges only `nodes-with-deltas`, and DOM
  elements are bound by address. A keyed element's address is
  `hash([base-addr :keyed key])`, so both branches collapse onto ONE address
  and the structural change produces no deltas at all — silently.

  Findings encoded below:
    A  branch at the root of the RENDER spin        -> 0 ops  (unsupported)
    B  branch nested under a stable root element    -> works
    C  same call site, only attrs/text differ       -> works
    D  child spin root flip, SAME key on branches   -> 0 ops  (the prod bug)
    D2 child spin root flip, DISTINCT keys          -> works
    E  child spin with stable root, branch inside   -> works

  A and D are the defects: a structural change is dropped with no error. Per
  the sharp-edges cross-cutting rule (\"anything the engine can detect as
  'probably not what the author meant' logs or throws in dev\"), these must
  either discharge or fail loudly."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-async :refer [await-drain]]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]))

(defn- flip!
  "Mount `mk`'s spin with the signal true, flip it to false, and report what the
  flip discharged. Returns {:ops n :texts [...] :parent n :child n}."
  [rt mk]
  (let [{:keys [discharge log]} (disch/make-mock-discharge)
        loading? (sig/signal true)
        parent-runs (atom 0)
        child-runs (atom 0)
        the-spin (mk loading? parent-runs child-runs)]
    (render/render-spin! nil the-spin discharge)
    @the-spin
    (is (some #{"LOADING"} (mapv :text (filter #(= :create-text (:op %)) @log)))
        "initial mount must render the loading branch")
    (reset! log [])
    (reset! loading? false)
    (await-drain rt)
    {:ops (count @log)
     :texts (mapv :text (filter #(= :create-text (:op %)) @log))
     :parent @parent-runs
     :child @child-runs}))

(defn- loading-branch [k] (el/div {:class "block-editor loading" :key k} (el/p "LOADING")))
(defn- loaded-branch  [k] (el/div {:class "block-editor" :key k}
                                  (el/div {:class "blocks-list"} "CONTENT")))

;; ---------------------------------------------------------------------------
;; Working shapes — these pin the behaviour we rely on.
;; ---------------------------------------------------------------------------

(deftest test-branch-nested-under-stable-root-discharges
  (testing "B: a branch below a stable root element discharges structurally"
    (with-ctx [rt]
      (let [{:keys [texts]} (flip! rt (fn [loading? parent-runs _]
                                        (spin (do (swap! parent-runs inc)
                                                  (el/div {:class "shell"}
                                                          (if @(track loading?)
                                                            (el/p "LOADING")
                                                            (el/div {:class "blocks-list"} "CONTENT")))))))]
        (is (some #{"CONTENT"} texts))))))

(deftest test-child-spin-with-stable-root-discharges
  (testing "E: self-tracking child spin, stable root, branch inside — the fix shape"
    (with-ctx [rt]
      (let [{:keys [texts parent child]}
            (flip! rt (fn [loading? parent-runs child-runs]
                        (spin (do (swap! parent-runs inc)
                                  (el/div {:class "column-content"}
                                          (await (spin (let [l? @(track loading?)]
                                                         (swap! child-runs inc)
                                                         (el/div {:class "block-editor" :key "page-view-abc"}
                                                                 (if l?
                                                                   (el/p "LOADING")
                                                                   (el/div {:class "blocks-list"} "CONTENT")))))))))))]
        (is (= 1 parent) "parent must not re-run; the child self-tracks")
        (is (= 2 child))
        (is (some #{"CONTENT"} texts))))))

(deftest test-child-spin-root-flip-distinct-keys-discharges
  (testing "D2: distinct keys give distinct addresses, so the swap discharges"
    (with-ctx [rt]
      (let [{:keys [texts]}
            (flip! rt (fn [loading? parent-runs child-runs]
                        (spin (do (swap! parent-runs inc)
                                  (el/div {:class "column-content"}
                                          (await (spin (let [l? @(track loading?)]
                                                         (swap! child-runs inc)
                                                         (if l?
                                                           (loading-branch "page-view-abc-loading")
                                                           (loaded-branch "page-view-abc-loaded"))))))))))]
        (is (some #{"CONTENT"} texts))))))

;; ---------------------------------------------------------------------------
;; Defects — currently silent no-ops.
;; ---------------------------------------------------------------------------

(deftest test-child-spin-root-flip-same-key-discharges
  (testing "D: THE PRODUCTION BUG — same key on both branches, change dropped"
    (with-ctx [rt]
      (let [{:keys [ops texts parent child]}
            (flip! rt (fn [loading? parent-runs child-runs]
                        (spin (do (swap! parent-runs inc)
                                  (el/div {:class "column-content"}
                                          (await (spin (let [l? @(track loading?)]
                                                         (swap! child-runs inc)
                                                         (if l?
                                                           (loading-branch "page-view-abc")
                                                           (loaded-branch "page-view-abc"))))))))))]
        (is (= 1 parent))
        (is (= 2 child) "the child body DID re-run")
        (is (pos? ops)
            "a structural change under one key must discharge (or throw), not vanish")
        (is (some #{"CONTENT"} texts))))))

(deftest test-render-spin-root-flip-discharges
  (testing "A: a branch at the ROOT of the render spin cannot swap the mounted node"
    (with-ctx [rt]
      (let [{:keys [ops texts]}
            (flip! rt (fn [loading? parent-runs _]
                        (spin (do (swap! parent-runs inc)
                                  (if @(track loading?)
                                    (loading-branch "page-view-abc")
                                    (loaded-branch "page-view-abc"))))))]
        (is (pos? ops) "root swap must discharge (or throw), not vanish")
        (is (some #{"CONTENT"} texts))))))
