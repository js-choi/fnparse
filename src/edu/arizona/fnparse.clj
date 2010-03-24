(ns edu.arizona.fnparse
  "[left-recur]: http://en.wikipedia.org/wiki/Left_recursion
  [ll-1]: http://en.wikipedia.org/wiki/LL(1)
  
  _FnParse 3_ is a *pair* of libraries that can create
  *unambiguous parsers*.
  
  Overview: Would FnParse be useful for you?
  ==========================================
  _FnParse Hound_ and _FnParse Cat_ are two libraries that
  can both create *unambiguous parsers*, but of slightly
  different varieties.
  
  When does one need parsers? *Any time you need to turn
  text into information via a language.* Data is always
  stored in \"text\" of *some* kind, whether it be an English
  sentence, a DNA sequence, or an XML file.
  
  FnParse can write [PEGs](http://www.en.wikipedia.org/wiki/PEG),
  an easy way to write unambiguous grammars.
  This means that FnParse parsers can represent languages
  whose sentences always have one meaning. Examples of
  ambiguous languages include Clojure, XML, HTML5, YAML,
  JSON, Python, Markdown, and most other computer languages.
  FnParse can indeed parse data in all those languages above.
  I think. :)
  
  How to learn FnParse
  ====================
  TODO
  
  A note on this namespace's vars
  ===============================
  This namespace itself contains common stuff that both
  FnParse Cat and FnParse Hound use.
  It is not meant to be used by you; use FnParse Cat or Hound instead.
  
  However, this documentation here does contain basic information
  relevant to both libraries.
  
  Similarities between FnParse Hound and Cat
  ==========================================
  FnParse Hound and Cat share very similar APIs. In fact, with
  a couple of exceptions listed in the next section, their APIs
  seem identical.
  
  Both FnParse Hound and Cat create _rules_. Rule are
  functions that eat tokens and turn them into data.
  
  *  A _token_ is a unit of text. Tokens are usually characters,
     because that's easiest to do. (You might already have a
     lexer, however, that turns characters into other tokens,
     which FnParse parsers can use too. Just be consistent
     on what kind of tokens a parser can accept.)
  *  A rule accepts a _state object_, which contains
     a _sequence of tokens_ and a _context_, as an argument.
  *  A rule determines if the tokens are valid or not
     according to its definition; it either _succeeds_ or
     _fails_.
  *  When a rule succeeds, it _consumes_ some tokens (zero or more)
     and calculates the data that those tokens represent. This
     new data is called the _product_. The rule then
     returns an object called an _answer_, which contains
     both the product and the new state.
  *  When a rule fails, it creates an _error_ that contains
     information on why the tokens were invalid for that rule.
  *  Rules consume tokens from the beginning of the sequence.
  
  (FnParse Cat rules and FnParse Hound rules are *not*
  the same and are *incompatible* with each other. The
  same goes for Cat and Hound states and answers.)
  
  FnParse Cat and Hound both use the same _error_ type: the
  `:edu.arizona.fnparse/ParseError` type.
  
  Differences between FnParse Hound and Cat
  =========================================
  Overview with fancy terms
  -------------------------
  FnParse Hound creates [Parsec]
  (http://www.haskell.org/haskellwiki/Parsec)-like,
  [LL(1)][ll-1] or near-LL(1) parsers.
  FnParse Cat is a [packrat parser](http://en.wikipedia.org/Packrat parser).
  *All* other differences stem from these two fundamental ones.
  
  Overview with plainer language
  ------------------------------
  FnParse Hound's parsers try to save as much memory as possible.
  In general, as soon as a Hound parser consumes a token, that
  token is discarded forever. This means that you can't backtrack
  through your tokens if a rule fails. For some languages, you
  want this kind of parser, because those languages are designed
  to be able to be interpreted by looking at only one token at
  a time: a lookahead of one.
  
  FnParse Cat's parsers take up a lot of memory, but they can
  quickly parse more complex parsers. In general, when a Cat parser
  consumes tokens, it saves the parse result from those tokens
  in a cache. This means that there's unlimited backtracking
  and lookahead. In addition, Cat parsers support [left
  recursion](left-recur), a very useful way of expressing rules.
  You want this kind of languages for relatively complex grammars
  that require a lot of backtracking.
  
  When should you use which FnParse
  ---------------------------------
  Many computer data languages are LL(1) or near-LL(1). You
  should use _FnParse Hound_ for those. Examples include:
  
  *  [Clojure](http://www.clojure.org)
  *  [XML](http://www.w3.org/XML)
  *  [JSON](http://json.org)
  *  [YAML](http://yaml.org)
  *  [CSV](http://en.wikipedia.org/wiki/Comma-separated_values)
  
  Many other, more complex computer programming languages
  are not LL(1). Some of them involve left recursion.
  
  *  Standard mathematical expressions (like in [Google
     Calculator](http://www.google.com/calculator))
  *  [Python](http://www.python.org)
  *  [Java](http://www.java.com)
  *  Even [Lojban](http://en.wikipedia.org/wiki/Lojban)
  
  Detailed comparison between Hound and Cat
  =========================================
  You won't understand this chart until you've learned either Hound
  or Cat well.
  
                     | Hound                  | Cat
  ------------------ | ---------------------- | -------------------
  Better for         | Potentially large data | More complex data
  Backtracking[^0]   | None by default[^1]    | Unlimited
  Caching of results | No[^2]                 | Yes
  Greedy repetition  | Yes[^3]                | No[^4]
  Right recursion    | Yes                    | Yes
  Left recursion     | No                     | Yes
  Context alteration | Yes[^5]                | No[^6]
  
  [^0]:
      The differences in backtracking comes from the differences
      between the `+` operator in Hound and Cat.
  [^1]:
      Backtracking in Hound rules is possible using the `lex`
      rule-maker, but it should be minimized.
  [^2]:
      In fact, it does the opposite: it tries to prevent
      *any* caching of results to reduce memory.
  [^3]:
      Greedy repetition in Hound is done by the `rep` function
      and its friends. Of course, it can be always rewritten to use
      right-recursive rules instead.
  [^4]:
      In Cat, you want to use left or right recursion instead.
  [^5]:
      In Hound, contexts can be altered in-place using the
      `alter-context` rule-maker, but you should usually
      prefer using custom rule-makers with `defmaker` instead,
      which is just as powerful.
  [^6]:
      Use custom rule-makers with `defmaker` if your grammar
      is context-sensitive. TODO: Python example
  *[XML]: eXtensible Markup Language
  *[YAML]: Yet Another Markup Language
  *[JSON]: Javascript Object Notation
  *[CSV]: Comma-Separated Values"
  {:author "Joshua Choi"}
  (:require [clojure.contrib.string :as str] [clojure.template :as temp]
            [clojure.set :as set] [clojure.test :as test]
            [clojure.contrib.seq :as seq] [clojure.contrib.monads :as m]
            [clojure.contrib.def :as d])
  (:refer-clojure :rename {apply apply-seq}, :exclude #{find})
  (:import [clojure.lang IPersistentMap]))

(defprotocol AState
  "The protocol of FnParse states, which must
  be able to return a position."
  (remainder [state])
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
  (rule state))

(defn rule-doc-summary-header [obj-type-str]
  (format "\n
  Summary
  ======="
    obj-type-str))

(defn rule-doc-first-header [library-name obj-type-str]
  (format "%s %s.\n\n  " library-name obj-type-str))

(def rule-doc-info
  {:succeeds "Success"
   :product "Product"
   :consumes "Consumes"
   :error "Error"})

(defn rule-doc-str [doc-str library-name obj-type-str meta-opts]
  (let [doc-str (or doc-str "No description available.")
        doc-str (str (rule-doc-first-header library-name obj-type-str) doc-str)
        doc-opts (select-keys meta-opts (keys rule-doc-info))
        opt-seq (seq doc-opts)]
    (if opt-seq
      (->> doc-opts sort
        (map #(format "  * %s: %s" (rule-doc-info (key %)) (val %)))
        (interpose "\n")
        (apply-seq str doc-str (rule-doc-summary-header obj-type-str) "\n"))
      doc-str)))

(defmacro general-defrule [library-name rule-name doc-string meta-opts form]
 `(let [rule-var# (d/defvar ~rule-name ~form ~doc-string)]
    (alter-meta! rule-var# update-in [:doc] rule-doc-str
      ~library-name "rule" ~meta-opts)
    rule-var#))

(defmacro general-defmaker [library-name obj-type-str def-form fn-name & forms]
 `(let [maker-var# (~def-form ~fn-name ~@forms)]
    (alter-var-root maker-var# identity)
    ; Add extended documentation.
    (alter-meta! maker-var# update-in [:doc] rule-doc-str
      ~library-name ~obj-type-str (meta maker-var#))
    ; Memoize unless the :no-memoize meta flag is true.
    (if-not (:no-memoize? (meta maker-var#))
      (alter-var-root maker-var# memoize))
    maker-var#))

(defn- format-tokens [input position]
  (let [input-size (count input)
        remainder-size (- input-size position)
        subinput (drop position input)
        subinput (cond (= remainder-size 0) "the end of input"
                       (> remainder-size 7) (concat (take 7 subinput) ["..."])
                       true subinput)
        subinput (seq subinput)]
    (if (string? input)
      (->> subinput (apply-seq str) (format "'%s'"))
      subinput)))

(defn- format-remainder [string-input? subinput]
  (let [remainder-size (count subinput)
        subinput (cond (= remainder-size 0) "the end of input"
                       (> remainder-size 7) (concat (take 7 subinput) ["..."])
                       true subinput)
        subinput (seq subinput)]
    (if string-input?
      (->> subinput (apply-seq str) (format "'%s'"))
      subinput)))

(defn format-parse-error-data
  "Returns a formatted string with the given error data.
  The descriptor map should be returned from group-descriptors."
  [input position descriptor-map]
  (let [unexpected-tokens (format-tokens input position)
        {labels :label, messages :message} descriptor-map
        expectation-text (when (seq labels)
                           (->> labels (str/join ", or ") (str "expected ")
                                list))
        message-text (->> expectation-text (concat messages)
                          (str/join "; "))]
    (format "At position %s, %s: %s"
      position unexpected-tokens message-text)))

(defn group-descriptors
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
  [error input]
  (let [{:keys #{position descriptors unexpected-token}} error]
    (format-parse-error-data input position (group-descriptors descriptors))))

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

(defn print-success [string-input? product final-remainder]
  (if (empty? final-remainder)
    (print-complete product)
    (print-incomplete string-input? product final-remainder)))

(defn print-failure [input context error]
  (printf
    "FAILED MATCH
===========
* Input: %s
* Initial context: %s
* Error: %s
"
    (pr-str input) (pr-str context) (format-parse-error error input))
  false)

(defn match
  "Parses the given input using the given rule.
  *Use the match or find functions in fnparse.cat or fnparse.hound
  in preference to this function.*"
  [make-state rule context success-fn failure-fn input]
  (let [string-input? (string? input)
        success-fn (or success-fn (partial print-success string-input?))
        failure-fn (or failure-fn (partial print-failure input context))
        state (make-state input context)
        result (-> state (apply rule) answer-result)]
    (if (failure? result)
      (failure-fn (:error result))
      (success-fn (:product result) (-> result :state remainder)))))

(defn find [match-fn <rule> context input]
  (when-let [input (seq input)]
    (lazy-seq
      (match-fn <rule> context
        (fn find-success [product remainder]
          (cons product (find match-fn <rule> context remainder)))
        (fn find-failure [e]
          (find match-fn <rule> context (rest input)))
        input))))

(defn substitute [match-fn <rule> context flatten? input]
  (let [combining-fn (if flatten? concat cons)]
    (when-let [input (seq input)]
      (lazy-seq
        (match-fn <rule> context
          (fn substitute-success [product remainder]
            (combining-fn product
              (substitute match-fn <rule> context flatten? remainder)))
          (fn substitute-failure [_]
            (cons (first input)
              (substitute match-fn <rule> context flatten? (rest input))))
          input)))))

(defn substitute-1 [match-fn <rule> context flatten? input]
  (let [combining-fn (if flatten? concat cons)]
    (when-let [input (seq input)]
      (lazy-seq
        (match-fn <rule> context
          (fn substitute-1-success [product remainder]
            (combining-fn product remainder))
          (fn substitute-1-failure [_]
            (cons (first input)
              (substitute-1 match-fn <rule> context flatten? (rest input))))
          input)))))

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

(defn match-assert-expr
  "The function that's used for (is (match? ...)) forms in
  fnparse.hound.test and fnparse.cat.test."
  [match-fn msg rule input opts]
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
      (~match-fn ~rule ~input ~context
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
            (format "a successful match by the rule '%s' from the input '%s'"
              '~rule '~input)
            (format-parse-error error#)))))))

(defn nil-or-equal?
  "Tests if a is nil, or else if a equals b."
  [a b]
  (or (nil? a) (= a b)))

(defn non-match-assert-expr
  "The function that's used for (is (non-match? ...)) forms in
  fnparse.hound.test and fnparse.cat.test."
  [match-fn msg rule input opts]
  (let [{:keys #{labels messages position context}} (apply-seq hash-map opts)
        descriptor-map {:label labels, :message messages}]
   `(letfn [(report-this#
              ([kind# expected-arg# actual-arg#]
               (test/report {:type kind#, :message ~msg,
                             :expected expected-arg#, :actual actual-arg#}))
              ([kind#]
               (test/report {:type kind#, :message ~msg})))]
      (let [expected-error-str# (format-match-error-data 
                                  (or ~position "any") ~descriptor-map)]
        (~match-fn ~rule ~input ~context
          (fn success-nonmatch [actual-product# actual-position#]
            (report-this# :fail expected-error-str#
              (format "successful match up to %s with a product of %s"
                actual-position# actual-product#)))
          (fn failure-nonmatch
            [{actual-position# :position, actual-descriptors# :descriptors}]
            (let [{actual-labels# :label, actual-messages# :message
                   :as actual-descriptor-map#}
                     (group-descriptors actual-descriptors#)]
              (if (and (nil-or-equal? ~position actual-position#)
                       (nil-or-equal? ~labels actual-labels#)
                       (nil-or-equal? ~messages actual-messages#))
                (report-this# :pass)
                (report-this# :fail expected-error-str#
                  (format-parse-error-data
                    actual-position# actual-descriptor-map#))))))))))
