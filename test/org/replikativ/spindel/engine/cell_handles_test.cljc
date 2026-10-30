(ns org.replikativ.spindel.engine.cell-handles-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [async deftest is testing]])
            [org.replikativ.spindel.engine.cell-handles :as handles]))

(defn- ignore-reap [_target _id])

(deftest aliases-share-the-allocation-anchor
  (let [id (random-uuid)
        target #?(:clj (Object.) :cljs (js-obj))
        receipt (handles/allocate! id target ignore-reap)
        alias (handles/anchor id)]
    (is (identical? receipt alias))
    (is (identical? alias (handles/anchor id)))))

(deftest duplicate-allocation-does-not-replace-live-anchor
  (let [id (random-uuid)
        target #?(:clj (Object.) :cljs (js-obj))
        receipt (handles/allocate! id target ignore-reap)]
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                          #"already registered"
                          (handles/allocate! id target ignore-reap)))
    (is (identical? receipt (handles/anchor id)))))

(deftest lookup-never-allocates-an-anchor
  (let [id (random-uuid)]
    (dotimes [_ 2]
      (try
        (handles/anchor id)
        (is false "Unknown cell must not acquire a new anchor")
        (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) error
          (is (= {:type ::handles/released :id id} (ex-data error))))))))

#?(:clj
   (deftest stale-finalizer-claims-preserve-other-registrations
     (let [id (random-uuid)
           token (Object.)
           entry {:token token}
           entries {id entry}
           claim #'handles/claim-entry]
       (testing "only the original registration can be claimed"
         (is (identical? entries (claim entries id (Object.))))
         (is (empty? (claim entries id token)))
         (is (empty? (claim {} id token)))))))

#?(:clj
   (deftest registry-retains-only-weak-anchor-and-target-references
     (let [id (random-uuid)
           target (Object.)
           receipt (handles/allocate! id target ignore-reap)
           entry (get @@#'handles/registrations id)]
       (is (instance? java.lang.ref.WeakReference (:anchor entry)))
       (is (instance? java.lang.ref.WeakReference (:target entry)))
       (is (identical? receipt (.get ^java.lang.ref.WeakReference (:anchor entry))))
       (is (identical? target (.get ^java.lang.ref.WeakReference (:target entry))))
       (is (identical? ignore-reap (:reap-fn entry))))))

#?(:cljs
   (do
     (defn- host-gc-available? []
       (fn? (.-gc js/globalThis)))

     (defn- eventually-after-gc!
       "Bounded heap probe. Collection and WeakRef inspection occur in distinct
       jobs: deref keeps a JS weak referent alive until its current job ends."
       [ready? complete!]
       (letfn [(attempt! [remaining]
                 (js/setTimeout
                  (fn []
                    (.gc js/globalThis)
                    (js/setTimeout
                     (fn []
                       (if (ready?)
                         (complete! true)
                         (if (pos? remaining)
                           (attempt! (dec remaining))
                           (complete! false))))
                     10))
                  0))]
         (attempt! 100)))

     (defn- collect-jobs! [remaining complete!]
       (js/setTimeout
        (fn []
          (.gc js/globalThis)
          (if (pos? remaining)
            (collect-jobs! (dec remaining) complete!)
            (js/setTimeout complete! 0)))
        0))

     (defn- count-reap! [target id]
       ;; Global dispatcher: no target, wrapper, or anchor capture.
       (swap! target conj id))

     (defn- make-host-aliases [id target]
       ;; This helper returns no closure over the original or its receipt.
       ;; Plain wrappers isolate anchor liveness from runtime cell operations.
       (let [receipt (handles/allocate! id target count-reap!)
             original #js {:anchor receipt}
             alias #js {:anchor (handles/anchor id)}]
         {:original (js/WeakRef. original)
          :alias-holder (volatile! alias)}))

     (defn- make-weak-target-allocation [id]
       (let [target (js-obj)]
         {:receipt (handles/allocate! id target ignore-reap)
          :target (js/WeakRef. target)}))

     (deftest shared-anchor-survives-original-wrapper-collection
       (if-not (host-gc-available?)
         (println "Skipping shared-anchor heap probe: Node --expose-gc is required")
         (async done
                (let [id (random-uuid)
                      calls (atom [])
                      target calls
                      {:keys [original alias-holder]} (make-host-aliases id target)]
                  (eventually-after-gc!
                   #(nil? (.deref original))
                   (fn [collected?]
                     (is collected? "The original wrapper can die while an untouched alias remains")
                     (is (some? @alias-holder) "The alias has remained strongly reachable")
                     (is (empty? @calls) "Collecting the original must not reap its live alias")
                     (vreset! alias-holder nil)
                     (eventually-after-gc!
                      #(= [id] @calls)
                      (fn [reaped?]
                        (is reaped? "Dropping the final alias eventually reaps the allocation")
                        (collect-jobs!
                         4
                         (fn []
                      ;; Retain target through every cleanup job without making
                      ;; the registered global dispatcher capture it.
                           (is (identical? calls target))
                           (is (= [id] @calls) "Cleanup dispatch occurs exactly once")
                           (is (thrown-with-msg? js/Error #"released" (handles/anchor id)))
                           (done)))))))))))

     (deftest live-anchor-does-not-retain-cleanup-target
       (if-not (host-gc-available?)
         (println "Skipping weak-target heap probe: Node --expose-gc is required")
         (async done
                (let [id (random-uuid)
                      {:keys [receipt target]} (make-weak-target-allocation id)]
                  (eventually-after-gc!
                   #(nil? (.deref target))
                   (fn [collected?]
                     (is collected? "A target can die while its allocation anchor is alive")
                     (is (identical? receipt (handles/anchor id))
                         "The strong receipt remains the canonical live anchor")
                     (done)))))))))
