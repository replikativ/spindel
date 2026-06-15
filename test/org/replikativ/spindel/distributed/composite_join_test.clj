(ns org.replikativ.spindel.distributed.composite-join-test
  "L4 step (i), ygg-signal model: two PEER spindel contexts converge by joining
   their per-system ygg-signal VALUES — no parent, no new interface, no privileged
   workspace. Each registered system is a convergent value (PConvergent); merging
   two peers is `(-join (system a) (system b))` per system, seated back into both
   contexts' ygg-signals. `merge-to-parent!` not involved."
  (:require [clojure.test :refer [deftest testing is]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.yggdrasil :as yg]
            [yggdrasil.convergent :as c]
            [yggdrasil.convergent.gset :as gs]))

(defn- peer-with-gset
  "A fresh peer context holding a G-Set ygg-signal `id` seeded with `elems`."
  [id elems]
  (let [c (ctx/create-execution-context)]
    (binding [ec/*execution-context* c]
      ;; value-semantic: build the seeded G-Set value, register it once (the CRDT
      ;; is an immutable value; mutating a fetched handle in place is a no-op now).
      (yg/register! (reduce gs/add (gs/gset id) elems)))
    c))

(defn- system-in [c id]
  (binding [ec/*execution-context* c]
    (yg/system id)))

(defn- seat! [c id v]
  ;; seat a converged value into the peer's ygg-signal (reset! on the SignalRef)
  (binding [ec/*execution-context* c]
    (reset! (yg/system-signal id) v)))

(defn- kb-in [c id]
  (binding [ec/*execution-context* c]
    (gs/elements (yg/system id))))

(deftest test-two-peer-contexts-converge
  (testing "two independent peer contexts, each with a G-Set ygg-signal, converge
            by joining their per-system values — symmetric, no parent"
    (let [a (peer-with-gset "kb" [:a1 :shared])
          b (peer-with-gset "kb" [:b1 :shared])]
      (testing "each peer sees only its own writes before merge (isolated)"
        (is (= #{:a1 :shared} (kb-in a "kb")))
        (is (= #{:b1 :shared} (kb-in b "kb"))))

      (let [merged (c/-join (system-in a "kb") (system-in b "kb"))]
        (testing "the joined G-Set is the union"
          (is (= #{:a1 :b1 :shared} (gs/elements merged))))
        (testing "symmetric: join(a,b) ≡ join(b,a)"
          (is (= (gs/elements (c/-join (system-in a "kb") (system-in b "kb")))
                 (gs/elements (c/-join (system-in b "kb") (system-in a "kb"))))))

        (testing "seat the join back into BOTH peers → both converge (no parent)"
          (seat! a "kb" merged)
          (seat! b "kb" merged)
          (is (= #{:a1 :b1 :shared} (kb-in a "kb")))
          (is (= #{:a1 :b1 :shared} (kb-in b "kb")))
          (is (= (kb-in a "kb") (kb-in b "kb"))))))))

(deftest test-multi-system-peer-contexts
  (testing "peers with two systems each — every matching system joins per-signal"
    (let [a (let [c (ctx/create-execution-context)]
              (binding [ec/*execution-context* c]
                (yg/register! (gs/add (gs/gset "kb") :a))
                (yg/register! (gs/add (gs/gset "tags") :red)))
              c)
          b (let [c (ctx/create-execution-context)]
              (binding [ec/*execution-context* c]
                (yg/register! (gs/add (gs/gset "kb") :b))
                (yg/register! (gs/add (gs/gset "tags") :blue)))
              c)]
      (is (= #{:a :b} (gs/elements (c/-join (system-in a "kb") (system-in b "kb")))))
      (is (= #{:red :blue} (gs/elements (c/-join (system-in a "tags") (system-in b "tags"))))))))
