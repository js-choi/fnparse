(ns edu.arizona.fnparse.base
  {:author "Joshua Choi"}
  (:require [clojure.contrib [string :as str] [seq :as seq]]
            [clojure.template :as temp])
  (:refer-clojure :rename {apply apply-seq}, :exclude #{find})
  (:import [clojure.lang IPersistentMap]))

(defprotocol AState
  "The protocol of FnParse states, which must
  be able to return a position."
  (get-remainder [state])
  (get-position [state])
  (make-another-state [state input context]))

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
  (rule state))

(defn format-remainder [string-input? subinput]
  (let [remainder-size (count subinput)
        subinput (cond (= remainder-size 0) "the end of input"
                       (> remainder-size 7) (concat (take 7 subinput) ["..."])
                       true subinput)
        subinput (seq subinput)]
    (if string-input?
      (->> subinput (apply-seq str) (format "'%s'"))
      subinput)))

(defn- format-parse-error-data
  "Returns a formatted string with the given error data.
  The descriptor map should be returned from group-descriptors."
  [position descriptor-map]
  (let [unexpected-tokens "TODO"
        {labels :label, messages :message} descriptor-map
        expectation-text (when (seq labels)
                           (->> labels (str/join ", or ") (str "expected ")
                                list))
        message-text (->> expectation-text (concat messages)
                          (str/join "; "))]
    (format "At position %s, %s: %s"
      position unexpected-tokens message-text)))

(defn- group-descriptors
  "From the given set of descriptors, returns a map with
  messages and labels respectively grouped together.
  If there are no descriptors of a certain descriptor kind,
  then the map's val for that kind is the empty set."
  [descriptors]
  (->> descriptors (seq/group-by :kind)
       (map #(vector (key %) (set (map :text (val %)))))
       (filter #(seq (get % 1)))
       (into {:message #{}, :label #{}})))

(defn format-parse-error
  "Returns a formatted string from the given error."
  [error]
  (let [{:keys #{position descriptors unexpected-token}} error]
    (format-parse-error-data position (group-descriptors descriptors))))

(defmulti parse
  "Use `match` instead of this multimethod.
  
  Creates a state from the given
  `context` and `input` and returns the raw
  `AParseAnswer` returned from applying that state
  to the given `rule`."
  (fn [rule context input] (type rule)))

