(ns edu.arizona.fnparse.core
  {:author "Joshua Choi"}
  (:require [clojure.contrib [string :as str] [def :as d]
                             [core :as cljcore]]
            [clojure.template :as temp]
            [edu.arizona.fnparse.core-private :as cp])
  (:refer-clojure :rename {apply apply-seq}, :exclude #{find}))

(defprotocol AState
  "The protocol of FnParse states, which must
  be able to return a position."
  (get-remainder [state])
  (get-position [state])
  (next-state [state])
  (state-warnings [state])
  (state-location [state]))

(defrecord RuleMeta [type label unlabelled-rule])

(defn make-rule-meta [type]
  (RuleMeta. type nil nil))

(defrecord
  #^{:doc "Represents descriptors representing a single
   potential cause of a FnParse error.
  kind: Either of the keywords :message or :label.
        :message means that the descriptor is a
        generic message. :label means that it's
        the label of a rule that was expected at a
        certain position but was not found.
  text: A string. The text of the descriptor."}
  ErrorDescriptor [kind text])

(defn make-error-descriptor [kind text]
  (ErrorDescriptor. kind text))

(defrecord
  #^{:doc "Represents FnParse errors.
  position: An integer. The position in the token
            sequence that the error was detected at.
  descriptors: The set of ErrorDescriptors that
               describe this error."}
  ParseError
  [position location descriptors])

(defn make-parse-error [position location descriptors]
  (ParseError. position location descriptors))

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

(defrecord Success [product state error]
  AParseAnswer (answer-result [this] this))

(defrecord Failure [error]
  AParseAnswer (answer-result [this] this))

(defn make-success [product state error]
  (Success. product state error))

(defn make-failure [error]
  (Failure. error))

(temp/do-template [fn-name type-name doc-string]
  (defn fn-name doc-string [result]
    (-> result type (isa? type-name)))
  failure? Failure "Is the given result a Failure?"
  success? Success "Is the given result is a Success?")

(defrecord Warning [position location message])

(defn make-warning [state message]
  (Warning. (get-position state) (state-location state) message))

(defprotocol ALocation
  (location-code [location]))

(defn location? [obj]
  (extends? ALocation (type obj)))

(extend-protocol ALocation
  Integer (location-code [position] (format "position %s" position)))

(defprotocol ALineAndColumnLocation
  (location-inc-line [location])
  (location-inc-column [location]))

(defrecord StandardLocation [line column]
  ALocation
    (location-code [this] (format "line %s, column %s" line column))
  ALineAndColumnLocation
    (location-inc-line [this] (assoc this :line (inc line), :column 0))
    (location-inc-column [this] (assoc this :column (inc column))))

(defn make-standard-location [line column]
  {:pre #{(integer? line) (integer? column)}}
  (StandardLocation. line column))

(def standard-break-chars #{\newline \backspace \formfeed})

(defn standard-alter-location [character]
  {:pre #{(char? character)}}
  (if (standard-break-chars character)
    location-inc-line location-inc-column))

(defn format-warning [warning]
  (format "[%s] %s" (location-code (or (:location warning) (:position warning)))
                    (:message warning)))

(defn apply
  "Applies the given rule to the given state."
  [rule state]
  (rule state))

(defmacro defrule
  "Defines a rule var. You should use this instead of `def`
  whenever you define rules, because it gives you cool
  shortcuts to write rule-related documentation.
  
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
  `(cp/general-defrule ~rule-name ~doc-string ~meta-opts ~form)))

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
  (list* `cp/general-defmaker `defn fn-name forms))

(defmacro defmaker-
  "Like `defmaker`, but also makes the var private."
  [fn-name & forms]
  (list* `defmaker (vary-meta fn-name assoc :private true) forms))

(defmacro defmaker-macro
  "Like `defmaker`, but makes a macro rule-maker
  instead of a function rule-maker."
  [fn-name & forms]
  (list* `cp/general-defmaker `defmacro fn-name forms))

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
  (when-let [labels (sort labels)]
    (if-not (= (count labels) 1)
      (str (->> labels drop-last (str/join ", ")) ", or " (last labels))
      (first labels))))

(defn- format-parse-error-data
  "Returns a formatted string with the given error data.
  The descriptor map should be returned from group-descriptors."
  [position location descriptor-map]
  (let [{labels :label, messages :message} descriptor-map
        expectation-text (when-let [labels (seq labels)]
                           (->> labels join-labels (str "expected ") list))
        message-text (->> expectation-text (concat messages)
                          (str/join "; "))]
    (format "Error [%s]: %s."
      (location-code (or location position))
      message-text)))

(defn- group-descriptors
  "From the given set of descriptors, returns a map with
  messages and labels respectively grouped together.
  If there are no descriptors of a certain descriptor kind,
  then the map's val for that kind is the empty set."
  [descriptors]
  (->> descriptors (group-by :kind)
       (map #(vector (key %) (set (map :text (val %)))))
       (filter #(seq (get % 1)))
       (into {:message #{}, :label #{}})))

(defn format-parse-error
  "Returns a formatted string from the given error."
  [error]
  (let [{:keys #{position location descriptors}} error]
    (format-parse-error-data position location
      (group-descriptors descriptors))))

(defn- format-warning-set
  "Returns a formatted string from the given set of Warnings."
  [warnings]
  (if-let [warnings (seq warnings)]
    (->> warnings
      (map #(str "  - " (format-warning %))) (str/join "\n") (str "\n"))
    "None."))

(defn- print-complete [product state]
  (printf
    "COMPLETE MATCH
==============
* Final product: %s
* Final product type: %s
* Final location: %s
* Warnings: %s
"
    (pr-str product) (type product)
    (location-code (or (state-location state) (get-position state)))
    (format-warning-set (state-warnings state)))
  true)

(defn- print-incomplete [product state]
  (printf
    "INCOMPLETE MATCH
================
* Final product: %s
* Final product type: %s
* Unmatched remainder: %s
* Final location: %s
* Warnings: %s
"
    (pr-str product) (type product)
    (format-remainder true (get-remainder state))
    (location-code (or (state-location state) (get-position state)))
    (format-warning-set (state-warnings state)))
  false)

(defn- print-success [product final-state]
  (if (empty? (get-remainder final-state))
    (print-complete product final-state)
    (print-incomplete product final-state)))

(defn- print-failure [error]
  (printf
    "FAILED MATCH
=============
%s
"
    (format-parse-error error))
  false)

(defn rule-make-state [rule input location warnings context]
  ((-> rule meta :make-state) input location warnings context))

(defn- match*
  [rule success-fn failure-fn state]
  (let [result (-> rule (apply state) answer-result)]
    (if (failure? result)
      (failure-fn (:error result))
      (success-fn (:product result) (:state result)))))

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
  ([state rule &
    {:keys #{success-fn failure-fn}
     :or {success-fn print-success, failure-fn print-failure}}]
   (match* rule #(success-fn %1 %2) failure-fn state)))

(defn- get-combining-fn [flatten?]
  (if flatten? concat cons))

(defn- find* [rule combining-fn state]
  (lazy-seq
    (when (seq (get-remainder state))
      (match* rule
        (fn find-success [product new-state]
          (combining-fn product (find* rule combining-fn new-state)))
        (fn find-failure [e]
          (find* rule combining-fn (next-state state)))
        state))))

(defn find
  "Finds all occurrences of a rule in a sequence of tokens.
  Returns a lazy sequence of the rule's products at each
  occurence. The occurences do not overlap."
  [state rule & {:keys #{flatten?}}]
  (find* rule (get-combining-fn flatten?) state))

(defn- substitute* [rule combining-fn state]
  (lazy-seq
    (when-let [remainder (seq (get-remainder state))]
      (match* rule
        (fn substitute-success [product new-state]
          (combining-fn product (substitute* rule combining-fn new-state)))
        (fn substitute-failure [e]
          (cons (first remainder)
            (substitute* rule combining-fn (next-state state))))
        state))))

(defn substitute
  "Substitutes all occurences of a rule in a sequence of tokens
  with their respective products. Returns a lazy sequence of
  tokens and products.
  
  `flatten?` is a boolean. If it is true, then the substituting
  products will be flattened into the input sequence; in that
  case the products must always be Seqables."
  [state rule & {:keys #{flatten?}}]
  (substitute* rule (get-combining-fn flatten?) state))

(defn- substitute-1* [rule combining-fn state]
  (lazy-seq
    (when-let [remainder (seq (get-remainder state))]
      (match* rule
        (fn substitute-1-success [product new-state]
          (combining-fn product (get-remainder new-state)))
        (fn substitute-1-failure [e]
          (cons (first remainder)
            (substitute* rule combining-fn (next-state state))))
        state))))

(defn substitute-1
  "Substitutes the first occurence of a rule in a sequence of
  tokens with its respective product. Returns a lazy sequence
  of tokens and products.
  
  See `substitute`'s docs for information on `flatten?`."
  [state rule & {:keys #{flatten?}}]
  (substitute-1* rule (get-combining-fn flatten?) state))
