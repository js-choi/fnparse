(ns edu.arizona.fnparse.core
  {:author "Joshua Choi"}
  (:require [clojure.contrib [string :as str] [def :as d]
                             [core :as cljcore] [except :as except]]
            [clojure [template :as temp] [set :as set]]
            [edu.arizona.fnparse.core-private :as cp])
  (:refer-clojure :rename {apply apply-seq}, :exclude #{find}))

; (require '[clojure.stacktrace :as s] '[edu.arizona.fnparse :as fnparse] '[edu.arizona.fnparse [core :as c] [common :as k] [hound :as h] [json :as j] [cat :as cat] [clojure :as clj] [math :as math] [lojban :as l]] :reload)

(defprotocol AState
  "The protocol of FnParse states, which must
  be able to return a position."
  (get-remainder [state])
  (get-position [state])
  (next-state [state])
  (state-warnings [state])
  (state-location [state]))

(defprotocol RuleMeta
  (rule-meta-info [m]))

(defn rule-meta? [obj]
  (extends? RuleMeta (type obj)))

(defrecord NormalRuleMeta [type labels unlabelled-rule]
  RuleMeta (rule-meta-info [m] m))

(defn make-normal-rule-meta [type]
  (NormalRuleMeta. type nil nil))

(defrecord NamedRuleMeta [type info-delay]
  RuleMeta (rule-meta-info [m] (rule-meta-info (force info-delay))))

(defn make-named-rule-meta [type meta-delay]
  (NamedRuleMeta. type meta-delay))

(defn rule-labels [<r>]
  (-> <r> meta rule-meta-info :labels))

(defn require-rule-labels [<r>]
  (or (rule-labels <r>) (except/throw-arg "rule must be labelled")))

(defn rule-unlabelled-base [<r>]
  (-> <r> meta :unlabelled-rule))

(defprotocol ADescriptorContent
  (label-string [t]))

(extend-protocol ADescriptorContent
  String (label-string [s] s))

(defn descriptor-content? [object]
  (extends? ADescriptorContent (type object)))

(defn- join-labels [labels]
  {:pre (seq? labels)}
  (when-let [label-strs (->> labels (map label-string) sort)]
    (if-not (= (count label-strs) 1)
      (str (->> label-strs drop-last (str/join ", ")) ", or " (last label-strs))
      (first labels))))

(defprotocol ErrorDescriptor
  (descriptor-message [first-d rest-ds]))

(defrecord LabelDescriptor [lbl]
  ErrorDescriptor
  (descriptor-message [first-d rest-ds]
    (->> rest-ds (cons first-d) (map :lbl) join-labels (str "expected "))))

(defn make-label-descriptor [lbl]
  (LabelDescriptor. lbl))

(defn label-descriptor? [obj]
  (= (class obj) LabelDescriptor))

(defrecord MessageDescriptor [text]
  ErrorDescriptor
  (descriptor-message [first-d rest-ds]
    (->> rest-ds (cons first-d) (str/join "; "))))

(defn make-message-descriptor [text]
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
    (join-labels (:base-lbls d))
    (join-labels (:following-lbls d))))

(defrecord FollowingDescriptor [base-lbls following-lbls]
  ErrorDescriptor
  (descriptor-message [first-d rest-ds]
    (->> rest-ds (cons first-d) (map following-descriptor-message)
                 (str/join "; "))))

(defn make-following-descriptor [base-lbls subtrahend-lbls]
  {:pre [(set? base-lbls) (set? subtrahend-lbls)]}
  (FollowingDescriptor. base-lbls subtrahend-lbls))

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

(defn label-rule-meta [ls <old> <r>]
  {:pre [(rule-meta? (meta <r>))
         (or (nil? <old>) (rule-meta? (meta <old>)))
         (set? ls)]}
  (vary-meta <r> assoc :labels ls, :unlabelled-rule <old>))

(defn self-label-rule-meta [subrules <r>]
  (let [original-meta (meta <r>)]
    (with-meta <r>
      (NamedRuleMeta. (:type original-meta)
        (delay
          (let [subrule-labels (reduce set/union (map rule-labels subrules))]
            (if-not (some nil? subrule-labels)
              (assoc original-meta :labels subrule-labels)
              original-meta)))))))

(defn format-warning [warning]
  (format "[%s] %s" (location-code (or (:location warning) (:position warning)))
                    (:message warning)))

(defn apply
  "Applies the given rule to the given state."
  [rule state]
  ((rule) state))

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

(defn- xxx [obj] (prn obj) obj)

(defn- format-parse-error-data
  "Returns a formatted string with the given error data.
  The descriptor map should be returned from group-descriptors."
  [position location grouped-descriptors]
  (prn grouped-descriptors)
  (format "[%s] %s."
    (location-code (or location position))
    (->> grouped-descriptors
      (map #(descriptor-message (first %) (next %)))
      xxx
      (str/join "; "))))

(defn- group-descriptors
  "From the given set of descriptors, returns a map with
  messages and labels respectively grouped together.
  If there are no descriptors of a certain descriptor kind,
  then the map's val for that kind is the empty set."
  [descriptors]
  (vals (group-by class descriptors))
  #_(->> descriptors (group-by :kind)
       (map #(vector (key %) (set (map :content (val %)))))
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
Error: %s
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
