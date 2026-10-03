(ns org.replikativ.spindel.effects.cancel-token-test
  "An await cancelled while it registers retires its cancel token (#102):
  claiming the just-added continuation arms the token, and the reader is
  never handed to the resource, so no delivery would retire it."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.effects.await :as aw :refer [await]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]))

(deftest an-await-cancelled-while-registering-leaves-no-token
  (let [c (ctx/create-execution-context)]
    (try
      (binding [ec/*execution-context* c]
        (let [d (sync/deferred)
              s (spin (await d))]
          (future (try @s (catch Throwable _ nil)))
          (Thread/sleep 50)
          (spin-core/cancel-spin! s)
          (Thread/sleep 50)
          ;; the registration path, for a spin already cancelled: it claims
          ;; its own continuation and rejects synchronously
          (let [[_ _ token cancellation]
                (#'aw/cancellable-external-pair (spin-core/spin-id s) (fn [_]) (fn [_] :rejected) ::tag {:line 1})]
            (is (some? cancellation))
            (is (not (contains? (ec/get-state [:engine/cancelled-tokens]) token))))))
      (finally (ctx/stop-context! c)))))
