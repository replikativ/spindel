(ns org.replikativ.spindel.spin.mailbox-cancel-waiter-test
  "Regression: a cancelled external-await cont must never SILENTLY ABSORB a
  producer's post.

  `post-inline!` can skip a cancelled waiter *without consuming the message*
  only if it can recognise the waiter as cancelled. It recognises it by the
  `:cancel-token` stored on the waiter struct, which the Mailbox 2-arity
  reads from `ec/*external-await-cancel-token*`.

  That var is bound only by `await-handler`'s **Mailbox** dispatch branch.
  But `(aseq/anext mbx)` returns a plain CPS *closure*, not the Mailbox, so
  awaiting a mailbox through the PAsyncSeq protocol — which is what
  `pubsub.mult`'s source pump does — lands in the generic `ifn?` branch,
  where the cancel-token is discarded and the var is never bound.

  Consequence: the waiter carries `:cancel-token nil`. When the cont is later
  cancelled (e.g. `spin/core`'s `:external-await` reject path arms the gate
  and drops the cont), `post-inline!` cannot tell the waiter is dead. It pops
  the waiter, hands the message to the gated resolve, and the gate no-ops.
  The message is gone, the waiter is gone, the consumer never re-arms.

  Observed in production as a permanently deaf dvergr room bus:
  `{:queue N :waiters 0}` with a live `:external-await` cont on the pump.
  See ../dvergr/doc/bug-bus-source-pump-lost-waiter.md.

  The tests drive the drain synchronously (`enqueue-event!` + `drain-events!`
  rather than `post!`, which triggers an async drain) so there is no timing
  dependence."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [is.simm.partial-cps.sequence :as aseq]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]))

(defn- mbox-state
  "Mailbox state is ctx-backed — read it under the owning context."
  [context mbx]
  (binding [ec/*execution-context* context]
    @(.-state-atom mbx)))

(defn- external-await-conts [context spin-id]
  (binding [ec/*execution-context* context]
    (->> (ec/get-state [:await-conts spin-id])
         (filter (fn [[_id c]] (= :external-await (:kind c))))
         (into {}))))

(defn- cancel-all-external-awaits!
  "Simulate any engine truncation site that arms the cancellation gate:
  `spin/core`'s :external-await reject path, `truncate-stale-conts!`, or
  `add-continuation!` displacing a cont at the same deterministic cont-id."
  [context spin-id]
  (doseq [[_id c] (external-await-conts context spin-id)]
    ((:cancel! c) context)))

(defn- post-synchronously!
  "Post + drain on the calling thread. `sync/post!` enqueues and fires an
  async drain on the executor; here we want the drain to have happened by the
  time we assert."
  [context mbx msg]
  (simple/enqueue-event! context {:type :mailbox-post :mailbox mbx :msg msg})
  (binding [ec/*execution-context* context]
    (simple/drain-events! context (:executor context))))

(defn- start-consumer!
  "Invoke `spin` inline so it runs to its first suspend point, registering the
  mailbox waiter synchronously. Returns the spin-id."
  [context s]
  (binding [ec/*execution-context* context]
    (s (fn [_] nil) (fn [_] nil))
    (spin-core/spin-id s)))

(deftest test-anext-await-registers-untokened-waiter
  (testing "awaiting a Mailbox through anext loses the cancel-token, awaiting it directly keeps it"
    (let [context (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* context]
          (let [via-anext (sync/create-mailbox context)
                direct    (sync/create-mailbox context)
                _ (start-consumer! context (spin (await (aseq/anext via-anext))))
                _ (start-consumer! context (spin (await direct)))
                anext-waiter  (first (:waiters (mbox-state context via-anext)))
                direct-waiter (first (:waiters (mbox-state context direct)))]

            (is (some? anext-waiter) "anext consumer should be parked on the mailbox")
            (is (some? direct-waiter) "direct consumer should be parked on the mailbox")

            (is (some? (:cancel-token direct-waiter))
                "direct Mailbox await threads its cancel-token onto the waiter")

          ;; This is the defect. Both consumers end up in the SAME mailbox
          ;; waiter list, but only one of them is identifiable as cancellable.
            (is (some? (:cancel-token anext-waiter))
                "anext-await must ALSO thread its cancel-token onto the waiter")))
        (finally (ctx/stop-context! context))))))

(deftest test-cancelled-anext-waiter-absorbs-and-loses-message
  (testing "a cancelled anext-await waiter swallows a post: message lost, consumer never resumes"
    (let [context (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* context]
          (let [mbx      (sync/create-mailbox context)
                received (atom ::none)
                sid      (start-consumer!
                          context
                          (spin (let [[msg _] (await (aseq/anext mbx))]
                                  (reset! received msg))))]

            (is (= 1 (count (:waiters (mbox-state context mbx)))) "consumer parked")
            (is (seq (external-await-conts context sid)) "external-await cont registered")

            (cancel-all-external-awaits! context sid)
            (post-synchronously! context mbx :m1)

            (let [{:keys [queue waiters]} (mbox-state context mbx)]
              (is (= ::none @received) "gated resolve no-ops — consumer does not resume")
              (is (empty? waiters) "the dead waiter was popped")

            ;; THE BUG: the message was consumed by a waiter that could not act
            ;; on it. It is neither delivered nor queued — it is gone.
              (is (= [:m1] (vec queue))
                  "a cancelled waiter must NOT consume the message; it must stay queued"))))
        (finally (ctx/stop-context! context))))))

(deftest test-cancelled-direct-waiter-preserves-message
  (testing "control: the Mailbox dispatch branch protects the message (post-inline! skips)"
    (let [context (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* context]
          (let [mbx      (sync/create-mailbox context)
                received (atom ::none)
                sid      (start-consumer!
                          context
                          (spin (reset! received (await mbx))))]

            (cancel-all-external-awaits! context sid)
            (post-synchronously! context mbx :m1)

            (let [{:keys [queue]} (mbox-state context mbx)]
              (is (= ::none @received) "cancelled consumer does not resume")
              (is (= [:m1] (vec queue))
                  "post-inline! skips the tokened waiter WITHOUT consuming the message"))))
        (finally (ctx/stop-context! context))))))

(deftest test-wedge-shape-matches-production
  (testing "after the absorbed post, further posts queue behind a pump that never re-arms"
    (let [context (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* context]
          (let [mbx (sync/create-mailbox context)
                sid (start-consumer! context (spin (await (aseq/anext mbx))))]
            (cancel-all-external-awaits! context sid)
            (post-synchronously! context mbx :lost)
            (post-synchronously! context mbx :q1)
            (post-synchronously! context mbx :q2)
            (post-synchronously! context mbx :q3)

            (let [{:keys [queue waiters]} (mbox-state context mbx)]
            ;; The production signature: {:queue N :waiters 0}, N messages
            ;; stuck, one silently dropped.
              (is (zero? (count waiters)) "no waiter — the bus is deaf")
              (is (= [:lost :q1 :q2 :q3] (vec queue))
                  "no message may be dropped; :lost is absorbed by the dead waiter"))))
        (finally (ctx/stop-context! context))))))
