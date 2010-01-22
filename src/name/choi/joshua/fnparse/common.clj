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

(defn partial-match-assert-expr
  [parse-fn msg [_ rule input consumed-tokens-num product-pred
                 & product-pred-args]]
  (let [input-count (count input)]
   `(letfn [(report-this#
              ([kind# expected-arg# actual-arg#]
               (report {:type kind#, :message ~msg,
                        :expected expected-arg#,
                        :actual actual-arg#}))
              ([kind#] (report {:type kind#, :message ~msg})))]
      (~parse-fn ~rule ~input
        (fn [actual-product# actual-remainder#]
          (let [actual-consumed-tokens-num#
                 (- ~input-count (count actual-remainder#))]
            (if (not= actual-consumed-tokens-num# ~consumed-tokens-num)
              (report-this# :fail
                (format "%s tokens consumed by the rule" ~consumed-tokens-num)
                (format "%s tokens actually consumed"
                        actual-consumed-tokens-num#))
              (if (not (~product-pred actual-product# ~@product-pred-args))
                (report-this# :fail
                  (list* '~product-pred '~'rule-product '~product-pred-args)
                  (list '~'not (list* '~product-pred actual-product#
                                      '~product-pred-args)))
                (report-this# :pass)))))
        (fn [error#]
          (report-this# :fail
            (format "a valid input for the given rule '%s'" '~rule)
            (format-parse-error error#)))))))

(defn full-match-assert-expr
  [parse-fn msg [_ rule input product-pred & product-pred-args]]
  (partial-match-assert-expr
    parse-fn msg
    (apply vector _ rule input (count input) product-pred product-pred-args)))
