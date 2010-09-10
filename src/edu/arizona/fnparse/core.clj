(ns edu.arizona.fnparse.core
  "This is the core of FnParse, containing code that is
  common to both FnParse Hound and FnParse Cat. It is
  *not* intended for end-users' usage."
  {:author "Joshua Choi", :skip-wiki true}
  (:require [clojure.contrib [def :as d] [except :as except]]
            [clojure [string :as str] [template :as temp] [set :as set]]
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

(defprotocol Rule
  "A general FnParse rule, either Cat or Dog."
  (rule-type [<r>] "Returns a keyword denoting the rule's type: Cat or Hound.")
  (rule-labels [<r>] "Returns a set of `<r>`'s labels.")
  (rule-unlabelled-base [<r>]
    "Returns either `nil`, if the rule has not been labelled, or
    the base `Rule` inside `<r>` from before it was labelled.")
  (assoc-labels [<r> lbls <old>]
    "Given a newly made labelling rule `<r>`, and its
    previous and base version `<old>`, returns a
    new version of `<r>` associated with new data:
    `(rule-labels %)` will return `lbls` and
    `(rule-unlabelled-base %)` will return `<old>`.")
  (apply [<r> state]
    "Applies `<r>` to `state`, returning a `ParseAnswer` object.
    `state` must be must be compatible with `<r>`."))

(defn rule?
  "Returns true if `obj` satisfies the `Rule` protocol."
  [obj] (satisfies? Rule obj))

(defn rule-of-type?
  "Tests if `obj` is a `Rule` of the given `type` keyword."
  [type obj]
  {:pre [(keyword? type)]}
  (and (satisfies? Rule obj) (-> obj rule-type (= type))))

(defrecord NormalRule [wrapper-fn type labels unlabelled-rule]
  Rule
  (rule-type [<r>] type)
  (rule-labels [<r>] labels)
  (rule-unlabelled-base [<r>] unlabelled-rule)
  (assoc-labels [<r> lbls <old>]
    (assoc <r> :labels lbls, :unlabelled-rule <old>))
  (apply [<r> state] ((wrapper-fn) state)))

(defrecord NamedRule [wrapper-delay type]
  Rule
  (rule-type [<r>] type)
  (rule-labels [<r>] (rule-labels @wrapper-delay))
  (rule-unlabelled-base [<r>] (rule-unlabelled-base @wrapper-delay))
  (assoc-labels [<r> lbls <old>] (assoc-labels @wrapper-delay lbls <old>))
  (apply [<r> state] (apply @wrapper-delay state)))

(defn require-rule-labels
  "Throws an exception if the given `<r>` is not labelled."
  [<r>]
  (or (rule-labels <r>) (except/throw-arg "rule must be labelled")))

(defn- join-labels
  "Joins the given collection of `labels` into a single string."
  [labels]
  {:pre [(every? string? labels)]}
  (if-let [labels (seq labels)]
    (when-let [label-strs (->> labels sort)]
      (if-not (= (count label-strs) 1)
        (format "%s, or %s"
          (->> label-strs drop-last (str/join ", "))
          (last label-strs))
        (first labels)))
    "UNLABELED RULE"))

(defprotocol ErrorDescriptor
  "The protocol for descriptors of errors. A parse error
  consists of many descriptors, such as labels or generic messages."
  (descriptor-message [first-descriptor rest-descriptors]
    "Returns a message string from the given descriptors, which
    must be of the same type. The `first-descriptor` is separate from
    the `rest-descriptors` to dispatch on its type."))

(defrecord LabelDescriptor [lbl]
  ErrorDescriptor
  (descriptor-message [first-d rest-ds]
    (->> rest-ds (cons first-d) (map :lbl) join-labels (str "expected "))))

(defn make-label-descriptor
  "Returns a `LabelDescriptor`. The sort of parse error it
  represents is that a rule with the given label was expected
  to match at a certain place, but did not."
  [lbl]
  {:pre [(string? lbl)]}
  (LabelDescriptor. lbl))

(defn label-descriptor? [obj]
  (= (class obj) LabelDescriptor))

(defrecord MessageDescriptor [text]
  ErrorDescriptor
  (descriptor-message [first-d rest-ds]
    (->> rest-ds (cons first-d) (str/join "; "))))

(defn make-message-descriptor
  "Returns a `MessageDescriptor`. The sort of parse error
  it represents is a generic sort of error with a message,
  like '0/0 is an invalid fraction'."
  [text]
  (MessageDescriptor. text))

(defn- exception-descriptor-message [d]
  (format "%s is not allowed where %s should be"
    (join-labels (:subtrahend-lbls d))
    (:main-lbl d)))

(defrecord ExceptionDescriptor [main-lbl subtrahend-lbls]
  ErrorDescriptor
  (descriptor-message [first-d rest-ds]
    (->> rest-ds (cons first-d) (map exception-descriptor-message)
                 (str/join "; "))))

(defn make-exception-descriptor [main-lbl subtrahend-lbls]
  (ExceptionDescriptor. main-lbl subtrahend-lbls))

(defn exception-descriptor? [obj]
  (= (class obj) ExceptionDescriptor))

(defn- following-descriptor-message [d]
  (format "%s cannot be followed by %s"
    (:base-lbl d)
    (join-labels (:following-lbls d))))

(defrecord FollowingDescriptor [base-lbl following-lbls]
  ErrorDescriptor
  (descriptor-message [first-d rest-ds]
    (->> rest-ds (cons first-d) (map following-descriptor-message)
                 (str/join "; "))))

(defn make-following-descriptor [base-lbl subtrahend-lbls]
  {:pre [(set? subtrahend-lbls)]}
  (FollowingDescriptor. base-lbl subtrahend-lbls))

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

(defrecord LineLocation [line]
  ALocation (location-code [this] (format "line %s" line)))

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

(d/defvar *format-remainder-limit*
  10
  "The limit at which `format-remainder`will cut off lengthy
  remainders at. Must be a positive integer.")

(defn format-remainder [string-input? subinput]
  {:pre #{(seq subinput) (pos? *format-remainder-limit*)
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

(defn- format-parse-error-data
  "Returns a formatted string with the given error data.
  The descriptor map should be returned from group-descriptors."
  [position location grouped-descriptors]
  (format "[%s] %s."
    (location-code (or location position))
    (->> grouped-descriptors
      (map #(descriptor-message (first %) (next %)))
      (str/join "; "))))

(defn- group-descriptors
  "From the given set of descriptors, returns a map with
  messages and labels respectively grouped together.
  If there are no descriptors of a certain descriptor kind,
  then the map's val for that kind is the empty set."
  [descriptors]
  (vals (group-by class descriptors)))

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
Error: %s
"
    (format-parse-error error))
  false)

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
   (match* rule success-fn failure-fn state)))

(defn- get-combining-fn [flatten?]
  (if flatten? concat cons))

(defn- matches-seq* [rule combining-fn state]
  (lazy-seq
    (when (seq (get-remainder state))
      (match* rule
        (fn find-success [product new-state]
          (combining-fn product
            (matches-seq* rule combining-fn new-state)))
        identity state))))

(defn matches-seq
  "Finds all *consecutive* occurrences of a rule in a
  sequence of tokens.
  Returns a lazy sequence of the rule's products at each
  occurence. The occurrences must come one after another,
  or else the last element of the sequence will be a ParseError.
  The occurrences also do not overlap."
  [state rule & {:keys #{flatten?}}]
  (matches-seq* rule (get-combining-fn flatten?) state))

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

(d/defvar- rule-doc-summary-header
  "\n
  Rule Summary
  ============")

(d/defvar- rule-doc-info
  {:succeeds "Success"
   :product "Product"
   :consumes "Consumes"
   :error "Error"
   :description "Description"})

(defn rule-doc-str [doc-str meta-opts description]
  (let [doc-str (or doc-str "No description available.")
        doc-opts (select-keys meta-opts (keys rule-doc-info))
        opt-seq (seq doc-opts)
        doc-opts (assoc doc-opts :description description)]
    (if opt-seq
      (->> doc-opts sort
        (map #(format "  * %s: %s" (rule-doc-info (key %)) (val %)))
        (interpose "\n")
        (apply-seq str doc-str rule-doc-summary-header "\n"))
      doc-str)))

(defn label-rule-meta [ls <old> <r>]
  {:pre [(rule? <r>) (rule? <old>) (set? ls) (every? string? ls)]}
  (assoc-labels <r> ls <old>))

(defn self-label-rule-meta [subrules <r>]
  {:pre [(rule? <r>) (every? rule? subrules)]}
  (NamedRule.
    (delay (let [subrule-labels (->> subrules (map rule-labels) concat)]
             (if-not (some nil? subrule-labels) ; TODO Check if wrong.
               (assoc-labels <r> subrule-labels <r>)
               <r>)))
    (:type <r>)))

(defmacro make-normal-rule-wrapper
  "Creates a `NormalRule` instance. This is for rules
  that are not defined with `defrule` or `defmaker`,
  and thus cannot be recursive.
  
  The `wrapper-fn` must be a function with no parameters that returns a function
  that takes a `State` and returns an `Answer`."
  [type rule-symbol inner-fn-body]
  {:pre [(keyword? type) (symbol? rule-symbol)]}
 `(let [inner-body-delay# (delay ~inner-fn-body)]
    (NormalRule. (fn normal-rule [] @inner-body-delay#) ~type nil nil)))

(defmacro make-named-rule-wrapper [type rule-form]
  {:pre [(keyword? type)]}
 `(NamedRule. (delay ~rule-form) ~type))

(defmacro make-rule [type rule-symbol state-symbol & body]
  {:pre [(symbol? rule-symbol) (keyword? type)]}
 `(make-normal-rule-wrapper ~type ~rule-symbol
    (fn ~rule-symbol [~state-symbol] ~@body)))

(defmacro general-defrule
  [rule-sym description doc-string meta-opts type form]
  {:pre [(string? description)
         (or (string? doc-string) (nil? doc-string))
         (or (map? meta-opts) (nil? meta-opts))]}
 `(let [rule# (make-named-rule-wrapper ~type ~form)
        rule-var# (d/defvar ~rule-sym rule# ~doc-string)]
    (alter-meta! rule-var# update-in [:doc]
      rule-doc-str ~meta-opts ~description)
    rule-var#))

(defn named-rule-maker [rule-making-fn rule-type-kw]
  (fn named-rule-maker [& args]
    (NamedRule. (delay (apply-seq rule-making-fn args)) rule-type-kw)))

(defmacro general-defmaker [def-form description rule-type-kw fn-name & forms]
 `(let [maker-var# (~def-form ~fn-name ~@forms)]
    ; Wrap the rule-maker to return delayed NameRules
    ; in case of mutual recursion.
    (alter-var-root maker-var# named-rule-maker ~rule-type-kw)
    ; Add extended documentation.
    (alter-meta! maker-var# update-in [:doc]
      rule-doc-str (meta maker-var#) ~description)
    ; Memoize unless the :no-memoize? meta flag is true.
    (when-not (:no-memoize? (meta maker-var#))
      (alter-var-root maker-var# memoize))
    maker-var#))

(defn merge-parse-errors
  "Merges two ParseErrors together. If the two errors are at the same
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

(defn assoc-label-in-descriptors
  "Removes all labels from the given `descriptors` set, then adds the
  given `label-str`."
  [descriptors lbl]
  {:pre #{(set? descriptors)}, :post [(set? %)]}
  (let [descriptors (set/select (complement label-descriptor?) descriptors)
        new-label-descriptor (make-label-descriptor lbl)
        descriptors (conj descriptors new-label-descriptor)]
    descriptors))
