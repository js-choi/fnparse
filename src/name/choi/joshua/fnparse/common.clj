(ns name.choi.joshua.fnparse.common
  (:use clojure.template clojure.set clojure.test clojure.contrib.def
        clojure.contrib.seq-utils)
  (:require [clojure.contrib.str-utils2 :as str])
  (:import [clojure.lang Sequential IPersistentMap IPersistentVector Var]))

(defprotocol AState
  (remainder [state])
  (position [state]))

(deftype ErrorDescriptor [kind text] IPersistentMap)

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
  [make-state rule input success-fn failure-fn]
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

(defn format-parse-error [{:keys #{position descriptors}}]
  (let [{labels :label, messages :message} (group-by :kind descriptors)]
    (format "parse error at position %s: %s"
      position
      (if (empty? messages)
        (->> labels (map :text) (str/join ", or ") (str "expected "))
        (->> messages (map :text) (str/join "; "))))))

(defn report-this
  ([msg kind expected-arg actual-arg]
   (report {:type kind, :message msg, :expected expected-arg,
            :actual actual-arg}))
  ([msg kind] (report {:type kind, :message msg})))

(defn match-assert-expr
  [parse-fn msg rule input given-consume-num product-pred product-pred-args]
 `(let [input-size# (count ~input)
        consume-num# (or ~given-consume-num input-size#)]
    (~parse-fn ~rule ~input
      (fn success-match [actual-product# actual-remainder#]
        (let [actual-consume-num# (- input-size# (count actual-remainder#))]
          (if (not= actual-consume-num# consume-num#)
            (report-this ~msg :fail
              (format "%s tokens consumed by the rule" consume-num#)
              (format "%s tokens actually consumed" actual-consume-num#))
            (if (not (~product-pred actual-product# ~@product-pred-args))
              (report-this ~msg :fail
                (list '~product-pred '~'rule-product ~@product-pred-args)
                (list '~'not (list '~product-pred actual-product#
                                    ~@product-pred-args)))
              (report-this ~msg :pass)))))
      (fn failure-match [error#]
        (report-this ~msg :fail
          (format "a valid input for the given rule '%s'" '~rule)
          (format-parse-error error#))))))
