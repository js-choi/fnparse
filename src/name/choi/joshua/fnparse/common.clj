(ns name.choi.joshua.fnparse.common
  (:use clojure.template clojure.set clojure.contrib.def
        clojure.contrib.seq-utils)
  (:require [clojure.contrib.monads :as m])
  (:import [clojure.lang Sequential IPersistentMap IPersistentVector Var]))

(deftype Bulletin [message] IPersistentMap)

(deftype Expectation [label] IPersistentMap)

(deftype ParseError [position unexpected-token descriptors] IPersistentMap)

(deftype Success [product state error] IPersistentMap)

(deftype Failure [error] IPersistentMap)

(do-template [fn-name type-name doc-string]
  (defn fn-name doc-string [result]
    (-> result type (isa? type-name)))
  failure? ::Failure "Is the given result a Failure?"
  success? ::Success "Is the given result is a Success?")

