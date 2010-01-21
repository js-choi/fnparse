(ns name.choi.joshua.fnparse.common
  (:use clojure.template clojure.set clojure.contrib.def
        clojure.contrib.seq-utils)
  (:require [clojure.contrib.monads :as m])
  (:import [clojure.lang Sequential IPersistentMap IPersistentVector Var]))

(defprotocol AState
  (remainder [state])
  (position [state]))

(deftype Bulletin [message] IPersistentMap)

(defprotocol AnErrorDescriptor
  (communique [descriptor]))

(deftype Expectation [label]
  AnErrorDescriptor
    (communique [] label)
  IPersistentMap)

(deftype ParseError [position unexpected-token descriptors] IPersistentMap)

(defprotocol AParseAnswer
  (answer-result [answer]))

(deftype Success [product state error] :as this
  IPersistentMap
  AParseAnswer (answer-result [] this))

(deftype Failure [error] :as this
  IPersistentMap
  AParseAnswer (answer-result [] this))

(do-template [fn-name type-name doc-string]
  (defn fn-name doc-string [result]
    (-> result type (isa? type-name)))
  failure? ::Failure "Is the given result a Failure?"
  success? ::Success "Is the given result is a Success?")

(defn parse
  [make-state input rule success-fn failure-fn]
  (let [result (-> input make-state rule answer-result)]
    (if (failure? result)
      (failure-fn (:error result))
      (success-fn (:product result) (-> result :state remainder)))))

(defn merge-parse-errors
  [{position-a :position, descriptors-a :descriptors :as error-a}
   {position-b :position, descriptors-b :descriptors :as error-b}]
  (cond
    (or (> position-b position-a) (empty? descriptors-a)) error-b
    (or (< position-b position-a) (empty? descriptors-b)) error-a
    true (assoc error-a :descriptors (union descriptors-a descriptors-b))))
