(ns edu.arizona.fnparse.core
  {:author "Joshua Choi"}
  (:require [clojure.contrib [string :as str] [seq :as seq] [def :as d]
                             [core :as cljcore]]
            [clojure.template :as temp]
            [edu.arizona.fnparse.common :as c])
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
  descriptors: The set of ErrorDescriptors that
               describe this error."}
  ParseError
  [position descriptors] IPersistentMap)

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

(defmacro defrule
  "Defines a rule var. You should use this instead of `def`,
  if only because it gives you cool shortcuts to write documentation.
  
  Metadata documentation options
  ==============================
  The `meta-opts` parameter expects a map argument,
  and makes it the new var's metadata. Giving certain
  options in the metadata also does appends certain
  things to the rule's `doc-string`.
  
  *  `:succeeds` expects a short description on when
     the rule succeeds.
  *  `:product` expects a short description on what
     products the rule gives when it succeeds.
  *  `:consumes` expects a short description on how
     many and what kinds of tokens the rule consumes
     when it succeeds.
  *  `:error` expects a short description on the
     error that the rule gives when it fails."
  ([rule-name form] `(defrule ~rule-name nil ~form))
  ([rule-name doc-string form] `(defrule ~rule-name ~doc-string nil ~form))
  ([rule-name doc-string meta-opts form]
  `(c/general-defrule ~rule-name ~doc-string ~meta-opts ~form)))

(defmacro defrule-
  "Like `defrule`, but also makes the var private."
  [fn-name & forms]
  (list* `defrule (vary-meta fn-name assoc :private true) forms))

(defmacro defmaker
  "Creates a rule-making function. Use this instead of
  `clojure.core/defn` whenever you make a rule-making
  function. (It does other stuff like memoization and
  and stuff.) Also see `defmaker-` and `defmaker-macro`.
  
  Arguments
  =========
  `defmaker` requires exactly the same arguments as
  `clojure.core/defn`. Particularly important is being
  able to give metadata easily.
  
  Metadata options
  ================
  `defmaker` accepts all special metadata options that
  `defrule` does; see `defrule` for more information.
  There is also a `:no-memoize?` option
  that does something special, detailed below.
  
  Memoization
  ===========
  `defmaker` rule-makers *memoize by default*. This means
  that they save the arguments they receive and their
  corresponding results in a cache, and search the cache
  every time they are called for equal arguments. See
  `clojure.k/memoize` for more information.
  
  95% of the time, you won't have to worry about the warning below.
  
  A warning: memoization uses *Clojure equality*. This
  means that giving vector arguments must always return the
  same rule as giving list arguments, because vectors can
  be equal to lists. If your function must return a different
  rule when given `[1 2 3]` versus `'(1 2 3)`, then you should
  give `{:no-memoize? true}` in your metadata."
  [fn-name & forms]
  (list* `c/general-defmaker `defn fn-name forms))

(defmacro defmaker-
  "Like `defmaker`, but also makes the var private."
  [fn-name & forms]
  (list* `defmaker (vary-meta fn-name assoc :private true) forms))

(defmacro defmaker-macro
  "Like `defmaker`, but makes a macro rule-maker
  instead of a function rule-maker."
  [fn-name & forms]
  (list* `c/general-defmaker `defmacro fn-name forms))

(d/defvar *format-remainder-limit*
  10
  "The limit at which `format-remainder`will cut off lengthy
  remainders at. Must be a positive integer.")

(defn format-remainder [string-input? subinput]
  {:pre #{(cljcore/seqable? subinput) (pos? *format-remainder-limit*)
          (integer? *format-remainder-limit*)}}
  (let [remainder-size (count subinput)
        subinput (cond (= remainder-size 0) "the end of input"
                       (> remainder-size *format-remainder-limit*)
                         (concat (take *format-remainder-limit* subinput)
                                 ["..."])
                       true subinput)
        subinput (seq subinput)]
    (if string-input?
      (->> subinput (apply-seq str) (format "'%s'"))
      subinput)))

(defn- join-labels [labels]
  {:pre (seq? labels)}
  (str (->> labels drop-last (str/join ", ")) ", or " (last labels)))

(defn- format-parse-error-data
  "Returns a formatted string with the given error data.
  The descriptor map should be returned from group-descriptors."
  [position descriptor-map]
  (let [{labels :label, messages :message} descriptor-map
        expectation-text (when-let [labels (seq labels)]
                           (->> labels join-labels (str "expected ") list))
        message-text (->> expectation-text (concat messages)
                          (str/join "; "))]
    (format "At position %s: %s" position message-text)))

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
  (let [{:keys #{position descriptors}} error]
    (format-parse-error-data position (group-descriptors descriptors))))

(defmulti parse
  "Use `match` instead of this multimethod.
  
  Creates a state from the given
  `context` and `input` and returns the raw
  `AParseAnswer` returned from applying that state
  to the given `rule`."
  (fn [rule context input & _] (type rule)))

(defn- print-complete [product]
  (printf
    "COMPLETE MATCH
==============
* Final product: %s
* Final product type: %s
"
    (pr-str product) (type product))
  true)

(defn- print-incomplete [string-input? product final-remainder]
  (printf
    "INCOMPLETE MATCH
================
* Final product: %s
* Final product type: %s
* Unmatched remainder: %s
"
    (pr-str product) (type product)
    (format-remainder string-input? final-remainder))
  false)

(defn- print-success [string-input? product final-remainder]
  (if (empty? final-remainder)
    (print-complete product)
    (print-incomplete string-input? product final-remainder)))

(defn- print-failure [error]
  (printf
    "FAILED MATCH
=============
%s
"
    (format-parse-error error))
  false)

(defn match
  "The general matching function of FnParse. Attempts to
  match the given rule to at least the beginning of the given input.
  
  *   `rule`: The rule to match with.
  *   `state`: The initial state.
  *   `success-fn`: An optional function called when the rule
      matches the input.
      `(complete-fn final-product final-remainder)` is called.
  *   `failure-fn`: An optional function called when the rule does not
      match the input. `(failure-fn final-error)` is called,
      where `final-error` is an object of type
      `:edu.arizona.fnparse.ParseError`.
    
  If `success-fn` and `failure-fn` aren't included, then
  `match` will print out a report of the parsing result."
  ([rule context success-fn failure-fn input]
   (let [result (->> input (parse rule context) answer-result)]
     (if (failure? result)
       (failure-fn (:error result))
       (success-fn (:product result) (-> result :state get-remainder)))))
  ([rule context input]
   (let [string-input? (string? input)]
     (match rule context
       (partial print-success string-input?)
       print-failure
       input))))

#_(defn find
  "Finds all occurrences of a rule in a sequence of tokens.
  Returns a lazy sequence of the rule's products at each
  occurence. The occurences do not overlap."
  [rule context input]
  (when-let [input (seq input)]
    (lazy-seq
      (match rule context
        (fn find-success [product remainder]
          (cons product (find rule context remainder)))
        (fn find-failure [e]
          (find rule context (rest input)))
        input))))

#_(defn substitute
  "Substitutes all occurences of a rule in a sequence of tokens
  with their respective products. Returns a lazy sequence of
  tokens and products.
  
  `flatten?` is a boolean. If it is true, then the substituting
  products will be flattened into the input sequence; in that
  case the products must always be Seqables."
  [rule flatten? state]
  (let [combining-fn (if flatten? concat cons)]
    (when-let [input (seq input)]
      (lazy-seq
        (match rule context
          (fn substitute-success [product remainder]
            (combining-fn product
              (substitute match-fn rule context flatten? remainder)))
          (fn substitute-failure [_]
            (cons (first input)
              (substitute match-fn rule context flatten? (rest input))))
          input)))))

#_(defn substitute-1
  "Substitutes the first occurence of a rule in a sequence of
  tokens with its respective product. Returns a lazy sequence
  of tokens and products.
  
  See `substitute`'s docs for information on `flatten?`."
  [rule context flatten? input]
  (let [combining-fn (if flatten? concat cons)]
    (when-let [input (seq input)]
      (lazy-seq
        (match-fn rule context
          (fn substitute-1-success [product remainder]
            (combining-fn product remainder))
          (fn substitute-1-failure [_]
            (cons (first input)
              (substitute-1 match-fn rule context flatten? (rest input))))
          input)))))
