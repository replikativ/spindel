(ns org.replikativ.spindel.engine.continuation-split-test
  "Regression for the continuation-table split (engine-sharpening Step C).

  Continuations used to live in one flat map `[:continuations spin-id
  cont-id]`, tagged by `:kind`, and four engine functions re-derived the
  comonad / monad split at runtime by filtering that tag. Step C splits
  them into two structures:

    [:track-subscriptions spin-id]  — the comonadic, persistent track
                                      conts (:kind :track).
    [:await-conts spin-id]          — the monadic await conts
                                      (:await-reactive / :await-once /
                                      :external-await).

  The invariant these tests pin: a track operation cannot reach an
  await continuation and vice versa — the split is structural, not a
  runtime predicate. `:order` remains a single monotone sequence across
  BOTH structures so truncation can still compare a track cont's order
  against an await cont's."
  (:refer-clojure :exclude [await])
  #?(:clj
     (:require [clojure.test :refer [deftest is testing]]
               [org.replikativ.spindel.engine.protocols :as rtp]
               [org.replikativ.spindel.spin.core :as spin-core]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.effects.track :refer [track]]
               [org.replikativ.spindel.effects.await :refer [await]]
               [org.replikativ.spindel.signal :refer [signal]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]]
               [org.replikativ.spindel.engine.protocols :as rtp]
               [org.replikativ.spindel.spin.core :as spin-core]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.effects.track :refer [track]]
               [org.replikativ.spindel.effects.await :refer [await]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.signal :refer [signal]])))

(defn- track-conts [ctx spin-id]
  (vals (rtp/get-state ctx [:track-subscriptions spin-id])))

(defn- await-conts [ctx spin-id]
  (vals (rtp/get-state ctx [:await-conts spin-id])))

(deftest track-conts-land-only-in-track-subscriptions
  (testing "a (track sig) cont is stored in :track-subscriptions, never :await-conts"
    (async done
           (with-ctx [ctx]
             (let [sig (signal 1)
                   s   (spin (let [{:keys [new]} (track sig)] new))
                   sid (spin-core/spin-id s)]
               (run-spin! s
                          (fn [_]
                            (let [tracks (track-conts ctx sid)
                                  awaits (await-conts ctx sid)]
                              (is (= 1 (count tracks))
                                  "the track cont is in :track-subscriptions")
                              (is (every? #(= :track (:kind %)) tracks)
                                  ":track-subscriptions holds only :track conts")
                              (is (empty? awaits)
                                  "a tracking spin has no await conts"))
                            (done))
                          (fn [e] (is false (str "spin failed: " e)) (done))))))))

(deftest await-conts-land-only-in-await-conts
  (testing "an (await child) cont is stored in :await-conts, never :track-subscriptions"
    (async done
           (with-ctx [ctx]
             ;; A child that itself tracks a signal is reactive, so the
             ;; parent's await cont is :kind :await-reactive — still an
             ;; await cont, still in :await-conts.
             (let [sig    (signal 7)
                   child  (spin (let [{:keys [new]} (track sig)] new))
                   parent (spin (await child))
                   pid    (spin-core/spin-id parent)]
               (run-spin! parent
                          (fn [_]
                            (let [tracks (track-conts ctx pid)
                                  awaits (await-conts ctx pid)]
                              (is (empty? tracks)
                                  "the parent registered no track cont")
                              (is (= 1 (count awaits))
                                  "the await cont is in :await-conts")
                              (is (every? #(contains? #{:await-reactive :await-once :external-await}
                                                      (:kind %))
                                          awaits)
                                  ":await-conts holds only await-kinded conts"))
                            (done))
                          (fn [e] (is false (str "spin failed: " e)) (done))))))))

(deftest order-is-monotone-across-both-structures
  (testing ":order spans track + await conts so truncation can compare across kinds"
    (async done
           (with-ctx [ctx]
             ;; Body: (track A) then (await child) — a track cont then an
             ;; await cont in one spin. With the child reactive (it
             ;; tracks a signal) the await cont persists, so both conts
             ;; are live at once and their :order values must form one
             ;; shared 1-based sequence, not two independent counters.
             (let [sig-a  (signal 0)
                   sig-b  (signal 0)
                   child  (spin (let [{:keys [new]} (track sig-b)] new))
                   s      (spin (let [{a :new} (track sig-a)
                                      b (await child)]
                                  (+ a b)))
                   sid    (spin-core/spin-id s)]
               (run-spin! s
                          (fn [_]
                            (let [tracks (track-conts ctx sid)
                                  awaits (await-conts ctx sid)
                                  orders (sort (concat (map :order tracks)
                                                       (map :order awaits)))]
                              (is (= 1 (count tracks)) "one track cont")
                              (is (= 1 (count awaits)) "one await cont")
                              (is (= [1 2] orders)
                                  ":order is a single shared 1-based sequence across both structures"))
                            (done))
                          (fn [e] (is false (str "spin failed: " e)) (done))))))))

(deftest unknown-cont-kind-is-rejected
  (testing "add-continuation! throws on a cont with no / unrecognised :kind"
    (with-ctx [ctx]
      ;; The routing predicate is a closed `case` with no `:else`: a cont
      ;; that is neither track nor await cannot be silently mis-filed.
      (is (thrown? #?(:clj IllegalArgumentException :cljs js/Error)
                   (rtp/add-continuation! ctx :bad-spin
                                          {:id :bad-cont :event-key nil}))
          "a kindless cont is rejected, not mis-routed")
      (is (thrown? #?(:clj IllegalArgumentException :cljs js/Error)
                   (rtp/add-continuation! ctx :bad-spin
                                          {:id :bad-cont2 :kind :not-a-kind}))
          "an unrecognised :kind is rejected"))))
