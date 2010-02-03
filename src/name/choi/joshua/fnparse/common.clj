(ns name.choi.joshua.fnparse.common
  (:use clojure.template clojure.set clojure.test clojure.contrib.def
        clojure.contrib.seq-utils)
  (:require [clojure.contrib.str-utils2 :as str])
  (:import [clojure.lang Sequential IPersistentMap IPersistentVector Var]))

(defprotocol AState
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

(defn apply-rule [state rule]
  ((force rule) state))

(defn parse [make-state rule input context success-fn failure-fn]
  (let [state (make-state input context)
        result (-> state (apply-rule rule) answer-result)]
    (if (failure? result)
      (failure-fn (:error result))
      (success-fn (:product result) (-> result :state position)))))

(defn merge-parse-errors
  [{position-a :position, descriptors-a :descriptors :as error-a}
   {position-b :position, descriptors-b :descriptors :as error-b}]
  (cond
    (or (> position-b position-a) (empty? descriptors-a)) error-b
    (or (< position-b position-a) (empty? descriptors-b)) error-a
    true (assoc error-a :descriptors (union descriptors-a descriptors-b))))

(defn format-parse-error-data [position descriptor-map]
  (let [{labels :label, messages :message} descriptor-map
        expectation-text (->> labels (str/join ", or ") (str "expected "))
        message-text (->> expectation-text list (concat messages)
                          (str/join "; "))]
    (format "parse error at position %s: %s" position message-text)))

(defn group-descriptors [descriptors]
  (->> descriptors (group-by :kind)
       (map #(vector (key %) (set (map :text (val %)))))
       (into {})))

(defn format-parse-error [{:keys #{position descriptors}}]
  (format-parse-error-data position (group-descriptors descriptors)))

(defn match-assert-expr
  [parse-fn msg rule {:keys #{position context} :or {context {}}} input
   product-pred product-pred-args]
 `(letfn [(report-this#
            ([kind# expected-arg# actual-arg#]
             (report {:type kind#, :message ~msg, :expected expected-arg#,
                      :actual actual-arg#}))
            ([kind#] (report {:type kind#, :message ~msg})))]
    (let [input-size# (count ~input)
          consume-num# (or ~position input-size#)]
      (~parse-fn ~rule ~input ~context
        (fn success-match [actual-product# actual-position#]
          (if (not= actual-position# consume-num#)
            (report-this# :fail
              (format "%s tokens consumed by the rule" consume-num#)
              (format "%s tokens actually consumed" actual-position#))
            (if (not (~product-pred actual-product# ~@product-pred-args))
              (report-this# :fail
                (list '~product-pred '~'rule-product ~@product-pred-args)
                (list '~'not (list '~product-pred actual-product#
                                    ~@product-pred-args)))
              (report-this# :pass))))
        (fn failure-match [error#]
          (report-this# :fail
            (format "a valid input for the given rule '%s'" '~rule)
            (format-parse-error error#)))))))

(defn non-match-assert-expr
  [parse-fn msg rule input position descriptor-map]
  {:pre #{(map? descriptor-map) (not (nil? position))}}
 `(letfn [(report-this#
            ([kind# expected-arg# actual-arg#]
             (report {:type kind#, :message ~msg, :expected expected-arg#,
                      :actual actual-arg#}))
            ([kind#] (report {:type kind#, :message ~msg})))]
    (let [expected-error-str# (format-parse-error-data 
                                ~position ~descriptor-map)]
      (~parse-fn ~rule ~input {}
        (fn success-nonmatch [actual-product# actual-position#]
          (report-this# :fail expected-error-str#
            (format "successful parse up to %s with a product of %s"
              actual-position# actual-product#)))
        (fn failure-nonmatch
          [{actual-position# :position, actual-descriptors# :descriptors}]
          (let [actual-descriptor-map# (group-descriptors actual-descriptors#)]
            (if (and (== ~position actual-position#)
                     (= ~descriptor-map actual-descriptor-map#))
              (report-this# :pass)
              (report-this# :fail expected-error-str#
                (format-parse-error-data
                  actual-position# actual-descriptor-map#)))))))))
