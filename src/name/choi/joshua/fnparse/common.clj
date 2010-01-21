(ns name.choi.joshua.fnparse.common
  (:use clojure.template clojure.set clojure.contrib.def
        clojure.contrib.seq-utils)
  (:require [clojure.contrib.str-utils2 :as str])
  (:import [clojure.lang Sequential IPersistentMap IPersistentVector Var]))

(defprotocol AState
  (remainder [state])
  (position [state]))

(deftype ErrorDescriptor [messages labels] IPersistentMap)

(deftype ParseError [position unexpected-token descriptor] IPersistentMap)

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
  [{position-a :position, descriptor-a :descriptor :as error-a}
   {position-b :position, descriptor-b :descriptor :as error-b}]
  (cond
    (or (> position-b position-a) (empty? descriptor-a)) error-b
    (or (< position-b position-a) (empty? descriptor-b)) error-a
    true (assoc error-a :descriptor (union descriptor-a descriptor-b))))

(defn- format-expectations [labels]
  (if-not (empty? labels)
    (->> labels (str/join " or ") (str "expected "))))

(defn- cons-expectations-to-messages [expectations labels]
  (if expectations (cons expectations labels) labels))

(defn format-parse-error [{:keys #{position descriptor}}]
  (let [expectations (->> descriptor :labels format-expectations)]
    (->> descriptor :messages
      (cons-expectations-to-messages expectations)
      (str/join "; ")
      (format "parse error at position %s: %s" position))))
