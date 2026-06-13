(ns org.replikativ.spindel.distributed.composite-join-test
  "L4 step (i): two PEER spindel contexts converge by joining their workspace
   composites — no parent, no new interface. A workspace is a CompositeSystem;
   a composite is PConvergent; so merging two contexts is just (-join ws-a ws-b)
   on the value at [:external-refs ::workspace]. `merge-to-parent!` not involved."
  (:require [clojure.test :refer [deftest testing is]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.yggdrasil :as yg]
            [yggdrasil.convergent :as c]
            [yggdrasil.convergent.composite] ;; loads the CompositeSystem PConvergent impl
            [yggdrasil.convergent.gset :as gs]
            [yggdrasil.composite :as comp]))

(defn- peer-with-gset
  "A fresh peer context whose workspace holds a G-Set `id` seeded with `elems`."
  [id elems]
  (let [c (ctx/create-execution-context)]
    (binding [ec/*execution-context* c]
      (yg/register! (gs/gset id))
      (let [g (yg/system id)]
        (doseq [e elems] (gs/add g e))))
    c))

(defn- workspace [c]
  (binding [ec/*execution-context* c]
    (ec/get-state [:external-refs yg/workspace-key])))

(defn- seat! [c ws]
  (binding [ec/*execution-context* c]
    (ec/swap-state! [:external-refs yg/workspace-key] (constantly ws))))

(defn- kb-in [c id]
  (binding [ec/*execution-context* c]
    (gs/elements (yg/system id))))

(deftest test-two-peer-contexts-converge
  (testing "two independent peer contexts, each with a G-Set, converge by joining
            their workspace composites — symmetric, no parent"
    (let [a (peer-with-gset "kb" [:a1 :shared])
          b (peer-with-gset "kb" [:b1 :shared])]
      (testing "each peer sees only its own writes before merge (isolated)"
        (is (= #{:a1 :shared} (kb-in a "kb")))
        (is (= #{:b1 :shared} (kb-in b "kb"))))

      (let [merged (c/-join (workspace a) (workspace b))]
        (testing "the joined workspace's G-Set is the union"
          (is (= #{:a1 :b1 :shared}
                 (gs/elements (comp/get-subsystem merged "kb")))))
        (testing "symmetric: join(a,b) ≡ join(b,a)"
          (is (= (gs/elements (comp/get-subsystem (c/-join (workspace a) (workspace b)) "kb"))
                 (gs/elements (comp/get-subsystem (c/-join (workspace b) (workspace a)) "kb")))))

        (testing "seat the join back into BOTH peers → both converge (no parent)"
          (seat! a merged)
          (seat! b merged)
          (is (= #{:a1 :b1 :shared} (kb-in a "kb")))
          (is (= #{:a1 :b1 :shared} (kb-in b "kb")))
          (is (= (kb-in a "kb") (kb-in b "kb"))))))))

(deftest test-multi-system-peer-contexts
  (testing "peers with two systems each — every matching sub-system joins"
    (let [a (let [c (ctx/create-execution-context)]
              (binding [ec/*execution-context* c]
                (yg/register! (gs/gset "kb"))
                (yg/register! (gs/gset "tags"))
                (gs/add (yg/system "kb") :a)
                (gs/add (yg/system "tags") :red))
              c)
          b (let [c (ctx/create-execution-context)]
              (binding [ec/*execution-context* c]
                (yg/register! (gs/gset "kb"))
                (yg/register! (gs/gset "tags"))
                (gs/add (yg/system "kb") :b)
                (gs/add (yg/system "tags") :blue))
              c)
          merged (c/-join (workspace a) (workspace b))]
      (is (= #{:a :b} (gs/elements (comp/get-subsystem merged "kb"))))
      (is (= #{:red :blue} (gs/elements (comp/get-subsystem merged "tags")))))))
