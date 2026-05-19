(ns build
  (:require [clojure.tools.build.api :as b]
            [borkdude.gh-release-artifact :as gh]
            [deps-deploy.deps-deploy :as dd])
  (:import [clojure.lang ExceptionInfo]))

(def org "replikativ")
(def lib 'org.replikativ/spindel)
(def current-commit (b/git-process {:git-args "rev-parse HEAD"}))
(def version (format "0.1.%s" (b/git-count-revs nil)))
(def class-dir "target/classes")
(def basis (delay (b/create-basis {:project "deps.edn"})))
(def jar-file (format "target/%s-%s.jar" (name lib) version))

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
                      :tag (str "v" version)}
                :pom-data [[:description "Reactive computation you can fork. Incremental reactive computation for Clojure/ClojureScript with cached spins, mutable signals, copy-on-write forking, and a typed delta algebra."]
                           [:url "https://github.com/replikativ/spindel"]
                           [:licenses
                            [:license
                             [:name "Apache License 2.0"]
                             [:url "https://www.apache.org/licenses/LICENSE-2.0"]]]
                           [:developers
                            [:developer
                             [:id "whilo"]
                             [:name "Christian Weilbach"]
                             [:email "ch_weil@topiq.es"]]]]})
  (b/copy-dir {:src-dirs ["src" "resources"]
               :target-dir class-dir})
  (b/jar {:class-dir class-dir
          :jar-file jar-file})
  (println "JAR created:" jar-file))

(defn deploy
  "Deploy to Clojars. Requires CLOJARS_USERNAME and CLOJARS_PASSWORD env vars."
  [_]
  (jar nil)
  (dd/deploy {:installer :remote
              :artifact jar-file
              :pom-file (b/pom-path {:lib lib :class-dir class-dir})})
  (println "Deployed to Clojars:" lib version))

(defn install [_]
  (jar nil)
  (b/install {:basis @basis
              :lib lib
              :version version
              :jar-file jar-file
              :class-dir class-dir})
  (println "Installed to local Maven repo"))

;; ---------------------------------------------------------------------------
;; GitHub release — uses borkdude/gh-release-artifact.
;; Pattern from superficie / ansatz: build the JAR, then upload it as a
;; GitHub release asset on the matching tag (vX.Y.Z). Retries with a
;; Fibonacci backoff because GitHub's release API can be flaky during
;; high-traffic windows.
;; ---------------------------------------------------------------------------

(defn fib [a b]
  (lazy-seq (cons a (fib b (+ a b)))))

(defn retry-with-fib-backoff [retries exec-fn test-fn]
  (loop [idle-times (take retries (fib 1 2))]
    (let [result (exec-fn)]
      (if (test-fn result)
        (do (println "Returned: " result)
            (if-let [sleep-ms (first idle-times)]
              (do (println "Retrying with remaining back-off times (in s): " idle-times)
                  (Thread/sleep (* 1000 sleep-ms))
                  (recur (rest idle-times)))
              result))
        result))))

(defn try-release []
  (try (gh/overwrite-asset {:org org
                            :repo (name lib)
                            :tag (str "v" version)
                            :commit current-commit
                            :file jar-file
                            :content-type "application/java-archive"
                            :draft false})
       (catch ExceptionInfo e
         (assoc (ex-data e) :failure? true))))

(defn release
  "Create a GitHub release at tag vX.Y.Z and upload the built JAR as an
   asset. Requires GITHUB_TOKEN env var."
  [_]
  (jar nil)
  (println "Trying to release artifact at tag v" version)
  (let [ret (retry-with-fib-backoff 10 try-release :failure?)]
    (if (:failure? ret)
      (do (println "GitHub release failed!")
          (System/exit 1))
      (println (:url ret)))))
