(ns org.replikativ.spindel.v2.sci.world-test
  "Which heap SCI code resumes against (R4, option A with H-body): the
   resolver names the interpreter for the world a slice runs in; inherited
   SCI work in a fork resumes against the fork's interpreter. Ports
   sci/{world,boundary}_test to v2."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.sci :as v2sci]
            [org.replikativ.spindel.v2.sci.support :as s :refer [checked ev v outcome]]
            [sci.core :as sci]))

(defn- registry-resolver
  "dvergr's registry in small: the interpreter registered for a world, else
   `fallback` (nil refuses)."
  [registry fallback]
  (fn [w _interpreter] (get @registry w fallback)))

(deftest a-resumed-body-runs-against-the-interpreter-selected-for-its-world
  ;; a staged replacement (dvergr's extension install) publishes a fork of the
  ;; interpreter for the same world while a body is parked: the body resumes
  ;; against the replacement's heap
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         p (s/interpreter {:bindings {'d d}})
         registry (atom {w p})
         _ (v2sci/set-resolver! p (registry-resolver registry nil))
         t (ev w p "(def state (atom [:original]))
                    (task (let [x (await d)] (swap! state conj x) @state))")
         staged (sci/fork p)]
     (sci/eval-string* staged "(swap! state conj :staged)")
     (swap! registry assoc w staged)
     (v2/deliver! d :resumed)
     (is (= [:original :staged :resumed] (v t)) "the body resumed against the staged heap")
     (is (= [:original] (sci/eval-string* p "@state")) "the replaced heap is untouched")
     (v2/release-world! w))))

(deftest an-inherited-sci-task-resumes-against-the-forks-interpreter
  ;; port of suspended-sci-spin-resumes-independently-in-forked-worlds
  (doseq [order [[:child :parent] [:parent :child]]]
    (testing (str "delivered " order)
      (checked
       (let [w (s/vworld)
             d (binding [v2/*world* w] (v2/deferred))
             p (s/interpreter {:bindings {'d d}})
             registry (atom {w p})
             _ (v2sci/set-resolver! p (registry-resolver registry nil))
             t (ev w p "(def state (atom []))
                        (def ^:dynamic *scope* :root)
                        (task (binding [*scope* :bound]
                                (let [x (await d)]
                                  (swap! state conj [*scope* x])
                                  @state)))")
             child (v2/fork! w)
             c (sci/fork p)]
         (swap! registry assoc child c)
         (doseq [side order]
           (if (= side :child)
             (v2/deliver! (v2/in-world child d) :child)
             (v2/deliver! d :parent)))
         (is (= [[:bound :child]] (v (v2/in-world child t))) "the child's copy resumed in the child's heap")
         (is (= [[:bound :parent]] (v t)))
         (is (= [[:bound :child]] (sci/eval-string* c "@state")))
         (is (= [[:bound :parent]] (sci/eval-string* p "@state")) "the heaps diverge")
         (v2/release-world! child)
         (v2/release-world! w))))))

(deftest an-unmanaged-fork-reads-through-to-its-ancestors-interpreter
  ;; Q2 (a): a fork dvergr did not make (foerster particles, `(fork)`,
  ;; savepoint instances) gets no interpreter of its own; the resolver names
  ;; the nearest managed ancestor's, and the body sees the room's vars
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         p (s/interpreter {:bindings {'d d}})
         registry (atom {w p})
         _ (v2sci/set-resolver! p (registry-resolver registry p))
         t (ev w p "(def factor 3) (task (* factor (await d)))")
         particle (v2/fork! w)]
     (sci/eval-string* p "(def factor 5)")
     (v2/deliver! (v2/in-world particle d) 2)
     (is (= 10 (v (v2/in-world particle t))) "the particle read the room interpreter's var")
     (v2/release-world! particle)
     (v2/release-world! w))))

(deftest a-resolver-refusal-fails-the-run-without-running-sci-code
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         p (s/interpreter {:bindings {'d d}})
         registry (atom {w p})
         _ (v2sci/set-resolver! p (registry-resolver registry nil))
         t (ev w p "(def ran (atom 0)) (task (try (await d) (swap! ran inc) (finally (swap! ran inc))))")
         child (v2/fork! w)]
     (v2/deliver! (v2/in-world child d) :x)
     (is (= ::v2sci/no-interpreter (:type (second (outcome (v2/in-world child t))))))
     (is (= 0 (sci/eval-string* p "@ran")) "no SCI code ran for the refused world")
     (v2/deliver! d :y)
     (is (= 1 (v t)) "the parent is unaffected")
     (is (= 2 (sci/eval-string* p "@ran")) "its body and finally ran once")
     (v2/release-world! child)
     (v2/release-world! w))))

(deftest code-acts-in-the-world-the-host-selects
  ;; port of spins-register-in-the-selected-world: the interpreter holds no
  ;; world; each evaluation's tasks belong to the world bound around it
  (checked
   (let [a (s/vworld) b (s/vworld)
         ctx (s/interpreter)
         src "(def gate-cleaned (atom 0)) (task (try (sleep 60000) (finally (swap! gate-cleaned inc))))"
         ta (ev a ctx src)
         tb (ev b ctx "(task (try (sleep 60000) (finally (swap! gate-cleaned inc))))")]
     (v2/release-world! a)
     (is (s/wait-until #(= 1 (sci/eval-string* ctx "@gate-cleaned"))) "releasing a cancels a's task")
     (is (= ::pending (v2/value tb 50 ::pending)) "b's task is untouched")
     (is (thrown? Exception (sci/eval-string* ctx (str s/prelude "(task 1)"))) "no world, no task")
     (v2/release-world! b)
     (is (some? ta)))))

(deftest a-nested-interpreter-built-from-sci-runs-in-a-child-world
  ;; port of sci-program-can-construct-and-run-a-spindel-sci-child-world:
  ;; recursive construction through explicit host capabilities
  (checked
   (let [root (s/vworld)
         children (atom {})
         capabilities
         {'fork! (fn [] (let [id (random-uuid)] (swap! children assoc id (v2/fork! root)) id))
          'eval-task (fn [id source]
                       (let [inner (sci/with-detached-context #(s/interpreter))]
                         (ev (get @children id) inner source)))}
         outer (s/interpreter {:namespaces {'host capabilities}})
         {:keys [id value]} (ev root outer "(let [child (host/fork!)
                                                 nested (host/eval-task child \"(task (sleep 1) 41)\")]
                                             {:id child :value (inc @nested)})")]
     (is (= 42 value) "the nested interpreter's task ran in the child world")
     (is (uuid? id) "SCI holds an opaque id, never the world")
     (v2/release-world! (get @children id))
     (v2/release-world! root))))

(deftest savepoint-instances-resume-against-their-own-interpreters
  ;; multi-shot (S4): one parked SCI continuation resumes in every instance
  ;; world, each against the interpreter registered for it, each with its
  ;; own copy of the SCI bindings live at the savepoint
  (checked
   (let [w (s/vworld)
         pubs (atom [])
         _ (v2/install-handlers! w {:choose (fn [p] (swap! pubs conj p))})
         p (s/interpreter)
         registry (atom {w p})
         _ (v2sci/set-resolver! p (registry-resolver registry nil))
         t (ev w p "(def ^:dynamic *b* :root)
                    (def log (atom []))
                    (task (binding [*b* :bound]
                            (let [v (savepoint :choose nil)]
                              (swap! log conj [v *b*])
                              @log)))")]
     (is (s/wait-until #(seq @pubs)))
     (let [pub (first @pubs)
           instances (mapv (fn [x]
                             (let [iw (v2/instantiate pub)
                                   heap (sci/fork p)]
                               (swap! registry assoc iw heap)
                               (v2/activate! iw x)
                               [iw heap]))
                           [1 2 3])]
       (is (= [[[1 :bound]] [[2 :bound]] [[3 :bound]]] (mapv (fn [[iw _]] (v (v2/in-world iw t))) instances)))
       (is (= [[[1 :bound]] [[2 :bound]] [[3 :bound]]] (mapv (fn [[_ heap]] (sci/eval-string* heap "@log")) instances))
           "each instance wrote its own heap")
       (is (= [] (sci/eval-string* p "@log")) "the source heap is untouched")
       (v2/abandon! pub)
       (doseq [[iw _] instances] (v2/release-world! iw)))
     (v2/release-world! w))))

(deftest a-refused-run-with-open-finally-regions-retires
  ;; a refusal drops the run's open regions (their finalizers are SCI code
  ;; that cannot run), so the run retires and its world completes; before,
  ;; it stayed unretired and the fork never completed
  (doseq [path [:resume :cancel]]
    (testing (str "refused on " path)
      (checked
       (let [w (s/vworld)
             d (binding [v2/*world* w] (v2/deferred))
             p (s/interpreter {:bindings {'d d}})
             _ (v2sci/set-resolver! p (registry-resolver (atom {w p}) nil))
             t (ev w p "(def ran (atom 0)) (task (try (await d) (swap! ran inc) (finally (swap! ran inc))))")
             child (v2/fork! w)]
         (when (= path :resume)
           (v2/deliver! (v2/in-world child d) :x)
           (is (= ::v2sci/no-interpreter (:type (second (outcome (v2/in-world child t)))))))
         (v2/release-world! child)
         (is (not= ::timeout (v2/await-complete child 2000 ::timeout)) "the fork completes: its run retired")
         (is (= 0 (sci/eval-string* p "@ran")) "no SCI code ran for the refused world")
         (v2/deliver! d :y)
         (is (= 1 (v t)))
         (v2/release-world! w)
         (is (not= ::timeout (v2/await-complete w 2000 ::timeout))))))))
