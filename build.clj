(ns build
  (:require [clojure.tools.build.api :as b]
            [deps-deploy.deps-deploy :as dd]))

(def lib 'org.replikativ/spindel)
(def version "0.1.0")
(def class-dir "target/classes")
(def jar-file (format "target/%s-%s.jar" (name lib) version))
(def basis (delay (b/create-basis {:project "deps.edn"})))

(defn clean [_]
  (b/delete {:path "target"}))

(defn jar [_]
  (clean nil)
  (b/write-pom {:class-dir class-dir
                :lib lib
                :version version
                :basis @basis
                :src-dirs ["src"]
                :scm {:url "https://github.com/replikativ/spindel"
                      :connection "scm:git:git://github.com/replikativ/spindel.git"
                      :developerConnection "scm:git:ssh://git@github.com/replikativ/spindel.git"
                      :tag (b/git-process {:git-args "rev-parse HEAD"})}
                :pom-data [[:description "Incremental reactive computation system for Clojure/ClojureScript with cached spins, mutable signals, copy-on-write forking, and deterministic execution."]
                           [:url "https://github.com/replikativ/spindel"]
                           [:licenses
                            [:license
                             [:name "Apache License 2.0"]
                             [:url "https://www.apache.org/licenses/LICENSE-2.0"]]]]})
  (b/copy-dir {:src-dirs ["src" "resources"]
               :target-dir class-dir})
  (b/jar {:class-dir class-dir
          :jar-file jar-file})
  (println "JAR created:" jar-file))

(defn deploy [_]
  (jar nil)
  (dd/deploy {:installer :remote
              :artifact jar-file
              :pom-file (b/pom-path {:lib lib :class-dir class-dir})})
  (println "Deployed to Clojars!"))

(defn install [_]
  (jar nil)
  (b/install {:basis @basis
              :lib lib
              :version version
              :jar-file jar-file
              :class-dir class-dir})
  (println "Installed to local Maven repo"))
