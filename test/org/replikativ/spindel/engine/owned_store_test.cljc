(ns org.replikativ.spindel.engine.owned-store-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.owned-store :as store]))

(deftest immutable-bases-and-independent-writers
  (let [parent (store/create-store {:parent {:entities {:a 1 :b nil}}})
        basis (store/snapshot parent)
        child (store/create-store basis)]
    (store/transact! parent #(store/put-row! % :parent :entities :a 2))
    (store/transact! child #(store/delete-row! % :parent :entities :a))
    (is (= 1 (get-in basis [:parent :entities :a])))
    (is (= 2 (get-in (store/snapshot parent) [:parent :entities :a])))
    (is (= {:b nil} (get-in (store/snapshot child) [:parent :entities])))
    (store/transact! parent
                     #(is (nil? (store/read-row % :parent :entities :b ::absent))))))

(deftest refusal-restores-all-worlds-and-new-tables
  (let [s (store/create-store {:a {:rows {:x 1 :nil nil}}})
        basis (store/snapshot s)]
    (is (thrown? #?(:clj Exception :cljs js/Error)
                 (store/transact!
                  s (fn [tx]
                      (store/put-row! tx :a :rows :x 2)
                      (store/put-row! tx :a :rows :x 3)
                      (store/delete-row! tx :a :rows :nil)
                      (store/put-row! tx :b :new-table :new 4)
                      (throw (ex-info "refused" {}))))))
    (is (= basis (store/snapshot s)))))

(deftest transaction-boundaries
  (let [s (store/create-store)
        escaped (store/transact! s identity)]
    (is (thrown? #?(:clj Exception :cljs js/Error)
                 (store/put-row! escaped :a :rows :x 1)))
    (is (thrown? #?(:clj Exception :cljs js/Error)
                 (store/transact! s #(do (store/put-row! % :a :rows :x 1)
                                         (store/snapshot s)))))
    (is (thrown? #?(:clj Exception :cljs js/Error)
                 (store/transact! s #(do (store/put-row! % :a :rows :x 1)
                                         (store/transact! s identity)))))
    (is (= {} (store/snapshot s)))))

#?(:clj
   (deftest handoff-and-multiworld-reader-isolation
     (let [s (store/create-store {:a {:rows {:balance 0}}
                                  :b {:rows {:balance 0}}})
           transfer (fn []
                      (store/transact!
                       s (fn [tx]
                           (store/put-row! tx :a :rows :balance
                                           (inc (store/read-row tx :a :rows :balance)))
                           (store/put-row! tx :b :rows :balance
                                           (dec (store/read-row tx :b :rows :balance))))))
           writers (mapv (fn [_] (future (dotimes [_ 250] (transfer)))) (range 2))
           reader (future
                    (dotimes [_ 250]
                      (let [view (store/snapshot s)]
                        (assert (zero? (+ (get-in view [:a :rows :balance])
                                          (get-in view [:b :rows :balance])))))))]
       (doseq [f (conj writers reader)]
         (is (nil? (deref f 10000 ::timeout))))
       (is (= 500 (get-in (store/snapshot s) [:a :rows :balance]))))))
