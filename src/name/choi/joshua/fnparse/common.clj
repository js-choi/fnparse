(ns name.choi.joshua.fnparse.common
  (:use clojure.template clojure.set clojure.contrib.def
        clojure.contrib.seq-utils)
  (:require [clojure.contrib.monads :as m])
  (:import [clojure.lang Sequential IPersistentMap IPersistentVector Var]))

(deftype Bulletin [message] IPersistentMap)

(deftype Expectation [label] IPersistentMap)

(deftype ParseError [position unexpected-token descriptors] IPersistentMap)

