(ns name.choi.joshua.fnparse.common
  "This is the namespace containing stuff that both
  FnParse Cat and FnParse Hound use. The actual user of either
  library is recommended to *not use any of these functions*.
  Use the functions in Cat or Hound instead."
  {:author "Joshua Choi"}
  (:require [clojure.contrib.string :as str] [clojure.template :as temp]
            [clojure.set :as set] [clojure.test :as test]
            [clojure.contrib.seq :as seq])
  (:refer-clojure :rename {apply apply-seq})
  (:import [clojure.lang IPersistentMap]))

(defprotocol AState
  "The protocol of FnParse states, which must
  be able to return a position."
  (position [state]))

(deftype
  #^{:doc "Represents descriptors representing a single
   potential cause of a FnParse error.
  kind: Either of the keywords :message or :label.
        :message means that the descriptor is a
        generic message. :label means that it's
        the label of a rule that was expected at a
        certain position but was not found.
  text: A string. The text of the descriptor."}
  ErrorDescriptor [kind text]
  IPersistentMap)

(deftype
  #^{:doc "Represents FnParse errors.
  position: An integer. The position in the token
            sequence that the error was detected at.
  unexpected-token: A token—specifically, the token
                    at which the error was detected.
                    If the token is actually the end
                    of the input, then this is the
                    keyword ::common/end-of-input
                    instead.
  descriptors: The set of ErrorDescriptors that
               describe this error."}
  ParseError
  [position unexpected-token descriptors] IPersistentMap)

(defprotocol AParseAnswer
  "The protocol of FnParse Answers: what
  FnParse rules must return. Answers must
  contain a Result—i.e. a Success or Failure.
  This protocol is necessary for the parse
  function.
    FnParse Cat rules return Successes or
  Failures, which are their own Answers.
    FnParse Hound rules return Replies, which
  contain Results."
  (answer-result [answer]))

(deftype Success [product state error] :as this
  IPersistentMap
  AParseAnswer (answer-result [] this))

(deftype Failure [error] :as this
  IPersistentMap
  AParseAnswer (answer-result [] this))

(temp/do-template [fn-name type-name doc-string]
  (defn fn-name doc-string [result]
    (-> result type (isa? type-name)))
  failure? ::Failure "Is the given result a Failure?"
  success? ::Success "Is the given result is a Success?")

(defn apply
  "Applies the given rule to the given state."
  [state rule]
  ((force rule) state))

(defn parse
  "Parses the given input using the given rule.
  *Use the parse function in fnparse.cat or fnparse.hound
  in preference to this function.*
  make-state: A function to create a state for the rule
              from the given input and context.
  rule: The rule. It must accept whatever state that
        make-state returns.
  input: The sequence of tokens to parse.
  context: The initial context for the rule. Can be nil.
  success-fn: A function called when the rule matches
              the input.
              (success-fn final-product final-position) is
              called.
  failure-fn: A function called when the rule does not
              match the input.
              (failure-fn final-error) is called."
  [make-state rule input context success-fn failure-fn]
  (let [state (make-state input context)
        result (-> state (apply rule) answer-result)]
    (if (failure? result)
      (failure-fn (:error result))
      (success-fn (:product result) (-> result :state position)))))

(defn merge-parse-errors
  "Merges two Errors together. If the two errors are at the same
  position, their descriptors are combined. If one of the errors
  is at a further position than the other, than that first error
  is returned instead."
  [error-a error-b]
  (let [{position-a :position, descriptors-a :descriptors} error-a
        {position-b :position, descriptors-b :descriptors} error-b]
    (cond
      (or (> position-b position-a) (empty? descriptors-a)) error-b
      (or (< position-b position-a) (empty? descriptors-b)) error-a
      true (assoc error-a :descriptors
             (set/union descriptors-a descriptors-b)))))

(defn format-parse-error-data
  "Returns a formatted string with the given error data.
  The descriptor map should be returned from group-descriptors."
  [position descriptor-map]
  (let [{labels :label, messages :message} descriptor-map
        expectation-text (->> labels (str/join ", or ") (str "expected "))
        message-text (->> expectation-text list (concat messages)
                          (str/join "; "))]
    (format "parse error at position %s: %s" position message-text)))

(defn group-descriptors
  "From the given set of descriptors, returns a map with
  messages and labels respectively grouped together.
  If there are no descriptors of a certain descriptor kind,
  then the map's val for that kind is nil."
  [descriptors]
  (->> descriptors (seq/group-by :kind)
       (map #(vector (key %) (set (map :text (val %)))))
       (filter #(seq (get % 1)))
       (into {:message nil, :label nil})))

(defn format-parse-error
  "Returns a formatted string from the given error."
  [error]
  (let [{:keys #{position descriptors}} error]
    (format-parse-error-data position (group-descriptors descriptors))))

(defn match-assert-expr
  "The function that's used for (is (match? ...)) forms in
  fnparse.hound.test and fnparse.cat.test."
  [parse-fn msg rule input opts]
  (let [{:keys #{position context product?}
         :or {product? (list constantly true), position (count input),
              context {}}}
        (apply-seq hash-map opts)]
   `(letfn [(report-this#
              ([kind# expected-arg# actual-arg#]
               (test/report {:type kind#, :message ~msg,
                             :expected expected-arg#, :actual actual-arg#}))
              ([kind#]
               (test/report {:type kind#, :message ~msg})))]
      (~parse-fn ~rule ~input ~context
        (fn success-match [actual-product# actual-position#]
          (if (not= actual-position# ~position)
            (report-this# :fail
              (format "%s tokens consumed by the rule" ~position)
              (format "%s tokens actually consumed" actual-position#))
            (if (not (~product? actual-product#))
              (report-this# :fail
                (list '~'validate-with '~product?)
                (list '~'product-is actual-product#))
              (report-this# :pass))))
        (fn failure-match [error#]
          (report-this# :fail
            (format "a successful parse by the rule '%s' from the input '%s'"
              '~rule '~input)
            (format-parse-error error#)))))))

(defn non-match-assert-expr
  "The function that's used for (is (non-match? ...)) forms in
  fnparse.hound.test and fnparse.cat.test."
  [parse-fn msg rule input opts]
  (let [{:keys #{labels messages position context}} (apply-seq hash-map opts)
        descriptor-map {:label labels, :message messages}]
   `(letfn [(report-this#
              ([kind# expected-arg# actual-arg#]
               (test/report {:type kind#, :message ~msg,
                             :expected expected-arg#, :actual actual-arg#}))
              ([kind#]
               (test/report {:type kind#, :message ~msg})))]
      (let [expected-error-str# (format-parse-error-data 
                                  (or ~position "any") ~descriptor-map)]
        (~parse-fn ~rule ~input ~context
          (fn success-nonmatch [actual-product# actual-position#]
            (report-this# :fail expected-error-str#
              (format "successful parse up to %s with a product of %s"
                actual-position# actual-product#)))
          (fn failure-nonmatch
            [{actual-position# :position, actual-descriptors# :descriptors}]
            (let [actual-descriptor-map#
                   (group-descriptors actual-descriptors#)]
              (if (and (or (nil? ~position) (== ~position actual-position#))
                       (= ~descriptor-map actual-descriptor-map#))
                (report-this# :pass)
                (report-this# :fail expected-error-str#
                  (format-parse-error-data
                    actual-position# actual-descriptor-map#))))))))))
