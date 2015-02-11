(defproject sexp-tries "0.1.0-SNAPSHOT"
  :description "Lightweight, in-memory, database for asserting and querying s-expressions."
  ; It is loosly based on Peter Norvig's trie code.
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.7.0-alpha4"] ; required for ctries.
                 [pod-utils "0.1.0-SNAPSHOT"]
                 [ctries.clj "0.0.2"]]
  :repositories [["clojars" "https://clojars.org/repo/"]]
  :main ^:skip-aot trie-logic.core
  :target-path "target/%s"
  :profiles {:uberjar {:aot :all}})

