(ns org.replikativ.spindel.v2.ygg-support
  "Fixtures for the yggdrasil-on-v2 layer tests: in-memory datahike and
   geschichte stores, worlds, and polling for the layer's lifecycle work."
  (:require [clojure.test :refer [is]]
            [datahike.api :as d]
            [geschichte.bytes :as bytes]
            [geschichte.repo :as repo]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.yggdrasil :as ygg]
            [yggdrasil.adapters.datahike :as ydh]
            [yggdrasil.adapters.geschichte :as ygs]
            [yggdrasil.protocols :as yp]))

(def ^:dynamic *configs* nil)

(def schema
  [{:db/ident :item/k :db/valueType :db.type/keyword :db/unique :db.unique/identity
    :db/cardinality :db.cardinality/one}
   {:db/ident :item/v :db/valueType :db.type/string :db/cardinality :db.cardinality/one}])

(defn- config []
  (let [cfg {:store {:backend :memory :id (random-uuid)} :schema-flexibility :write
             :keep-history? true :commit-graph? true}]
    (when *configs* (swap! *configs* conj cfg))
    cfg))

(defn dh-system
  "A datahike system with the item schema."
  [name]
  (let [cfg (config)]
    (d/create-database cfg)
    (let [conn (d/connect cfg)]
      (d/transact conn schema)
      (ydh/create conn {:system-name name}))))

(defn put! [sys k v] (d/transact (:conn sys) [{:item/k k :item/v v}]) nil)

(defn val-in
  "The value of item `k` in a datahike system or a read-only db value."
  [x k]
  (let [db (if (satisfies? yp/SystemIdentity x) @(:conn x) x)]
    (d/q '[:find ?v . :in $ ?k :where [?e :item/k ?k] [?e :item/v ?v]] db k)))

(defn gs-system
  "A geschichte repository with one commit."
  [name]
  (let [cfg (config)]
    (d/create-database cfg)
    (let [conn (d/connect cfg)]
      (repo/init! conn)
      (repo/write! conn "base.txt" (bytes/utf8 "base"))
      (repo/stage-all! conn)
      (repo/commit! conn {:message "base" :author "test"})
      (ygs/create conn {:system-name name}))))

(defn write!
  "Writes `path` in a geschichte system's workspace, committed unless
   `:dirty`."
  ([sys path text] (write! sys path text true))
  ([sys path text commit?]
   (let [conn (ygs/connection sys)]
     (repo/write! conn path (bytes/utf8 text))
     (when commit?
       (repo/stage-all! conn)
       (repo/commit! conn {:message path :author "test"}))
     nil)))

(defn text-in [sys path]
  (some-> (repo/read (ygs/connection sys) path) bytes/decode-utf8))

(defn tree-has? [tree path] (contains? (set (map :path (:files tree))) path))

(defmacro with-stores
  "Runs `body`, then releases and deletes the stores it created."
  [& body]
  `(binding [*configs* (atom [])]
     (try ~@body
          (finally
            (doseq [cfg# @*configs*]
              (try (d/delete-database cfg#) (catch Throwable _#)))))))

(defn done!
  "Releases worlds and waits for them to complete."
  [& ws]
  (doseq [w ws] (v2/release-world! w))
  (doseq [w ws] (is (true? (v2/await-complete w 5000 ::timeout)) "the world completes")))

(defn close-world!
  "A fork room's close: the runtime ends, the record stays (F11)."
  [w]
  (v2/release-world! w)
  (is (true? (v2/await-complete w 5000 ::timeout))))

(defn eventually
  "Polls `(f)` until truthy, up to `ms`; returns its last value."
  ([f] (eventually f 5000))
  ([f ms]
   (let [end (+ (System/currentTimeMillis) ms)]
     (loop []
       (let [v (f)]
         (if (or v (> (System/currentTimeMillis) end)) v (do (Thread/sleep 10) (recur))))))))

(defn caught
  "The ex-data :type of what `(f)` throws, or ::no-throw."
  [f]
  (try (f) ::no-throw
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn st [fork] (:status (ygg/status fork)))

(defn root
  "A world with the given systems registered: [[sys opts] ...]."
  [& regs]
  (let [w (v2/world)]
    (doseq [[sys opts] regs] (ygg/register! w sys (or opts {})))
    w))
