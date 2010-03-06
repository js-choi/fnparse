(ns name.choi.joshua.fnparse.clojure
  (:require [name.choi.joshua.fnparse.hound :as r]
            [clojure.template :as t] [clojure.set :as set]
            [clojure.contrib.seq :as seq]
            name.choi.joshua.fnparse.hound.test)
  (:use [clojure.test :only #{deftest is run-tests}])
  (:refer-clojure :exclude #{read-string})
  (:import [clojure.lang IPersistentMap]))

;;; HELPER FUNCTIONS AND TYPES.

(deftype ClojureContext [ns-name ns-aliases anonymous-fn-context reader-eval?]
  IPersistentMap)

(deftype AnonymousFnContext [normal-parameters slurping-parameter]
  IPersistentMap)

(defn prefix-list-fn [prefix-rule]
  (fn [product] (list prefix-rule product)))

(defn str* [chars]
  (apply str chars))

(defn expt-int [base pow]
  (loop [n (int pow), y 1, z base]
    (let [t (bit-and n 1), n (bit-shift-right n 1)]
      (cond
        (zero? t) (recur n y (* z z))
        (zero? n) (* z y)
        :else (recur n (* z y) (* z z))))))

(defn reduce-hexadecimal-digits [digits]
  (reduce #(+ (* 16 %1) %2) digits))

(def peculiar-symbols {"nil" nil, "true" true, "false" false})

(def ws-set (set " ,\t\n"))

(def indicator-set (set ";()[]{}\\\"'@^`#"))

(defn annotate-symbol-end [error]
  (if (= (:unexpected-token error) \/)
    "multiple slashes aren't allowed in symbols"))

(defn make-parameter-vector [{:keys #{normal-parameters slurping-parameter}}]
  {:pre #{(vector? normal-parameters)}}
  (if slurping-parameter
    (conj normal-parameters '& slurping-parameter)
    normal-parameters))

(defn get-already-existing-symbol [fn-context suffix]
  (cond
    (integer? suffix)
      (get (:normal-parameters fn-context) (dec suffix))
    (= suffix \&)
      (:slurping-parameter fn-context)))

(defn update-fn-context [context parameter-suffix parameter-symbol]
  (cond
    (integer? parameter-suffix)
      (update-in context [:anonymous-fn-context :normal-parameters] 
        conj parameter-symbol)
    (= parameter-suffix \&)
      (update-in context [:anonymous-fn-context]
        assoc :slurping-parameter parameter-symbol)))

;;; RULES START HERE.

(declare <form>)

;; Whitespace.

(def <comment-indicator> (r/+ (r/lit \;) (r/lex (r/phrase "#!"))))

(def <comment-char> (r/antilit \newline))

(def <comment> (r/cat <comment-indicator> (r/rep* <comment-char>)))

(def <discarded> (r/prefix (r/lex (r/phrase "#_")) #'<form>))

(def <normal-ws-char>
  (r/term "a whitespace character" ws-set))

(def <ws>
  (r/label "whitespace"
    (r/rep+ (r/+ <normal-ws-char> <comment> <discarded>))))

(def <opt-ws> (r/opt <ws>))

;; Indicators and form separators.

(def <indicator> (r/term "an indicator" indicator-set))

(def <separator> (r/+ <ws> <indicator>))

(def <form-end> (r/+ (r/peek <separator>) r/<end-of-input>))

;; Symbols.

(def <ns-separator> (r/lit \/))

(def <non-alphanumeric-symbol-char>
  (r/set-term "a non-alphanumeric symbol character" "*+!---?."))

(def <symbol-first-char>
  (r/+ r/<ascii-letter> <non-alphanumeric-symbol-char>))

(def <symbol-char>
  (r/label "a symbol character"
    (r/+ <symbol-first-char> r/<decimal-digit>)))

(def <symbol-char-series>
  (r/hook str* (r/rep+ <symbol-char>)))

(def <symbol-end>
  (r/annotate-error annotate-symbol-end <form-end>))

(def <slash-symbol-suffix>
  (r/chook "/" <ns-separator>))

(def <symbol-suffix>
  (r/prefix <ns-separator> (r/+ <symbol-char-series> <slash-symbol-suffix>)))

(def <symbol>
  (r/for "a symbol"
    [first-char <symbol-first-char>
     rest-pre-slash (r/opt <symbol-char-series>)
     post-slash (r/opt <symbol-suffix>)
     _ <symbol-end>]
    (let [pre-slash (str first-char rest-pre-slash)]
      (if post-slash
        (symbol pre-slash post-slash)
        (or (peculiar-symbols pre-slash) ; In case it's true, false, or nil
            (symbol pre-slash))))))

;; Keywords.

(def <keyword-indicator> (r/lit \:))

(def <normal-keyword>
  (r/for [_ <keyword-indicator>
          pre-slash (r/opt <symbol-char-series>)
          post-slash (r/opt <symbol-suffix>)
          _ <symbol-end>]
    (if post-slash
      (keyword pre-slash post-slash)
      (keyword pre-slash))))

(def <peek-ns-separator> (r/peek <ns-separator>))

(r/defn fetch-referred-namespace [context namespace-alias]
  (r/only-when (get-in context [:ns-aliases namespace-alias])
    (format "no namespace with alias '%s'" namespace-alias)))

(r/defn ns-qualified-keyword-end-with-slash [pre-slash]
  (r/for [_ <peek-ns-separator>
          context r/<fetch-context>
          prefix (fetch-referred-namespace context pre-slash)
          suffix <symbol-suffix>]
    [prefix suffix]))

(r/defn ns-qualified-keyword-empty-end [pre-slash]
  (r/for [context r/<fetch-context>]
    [(:ns-name context) pre-slash]))

(r/defn ns-resolved-keyword-end [pre-slash]
  (r/+ (ns-qualified-keyword-end-with-slash pre-slash)
       (ns-qualified-keyword-empty-end pre-slash)))

(def <ns-resolved-keyword>
  (r/for [_ (r/lex (r/factor= 2 <keyword-indicator>))
          pre-slash <symbol-char-series>
          [prefix suffix] (ns-resolved-keyword-end pre-slash)
          _ <form-end>]
    (keyword prefix suffix)))

(def <keyword>
  (r/label "a keyword"
    (r/+ <ns-resolved-keyword> <normal-keyword>)))

;; Numbers.

(r/defn radix-natural-number [base]
  (r/cascading-rep+ (r/radix-digit base) identity #(+ (* base %1) %2)))

(def <decimal-natural-number>
  (radix-natural-number 10))

(def <number-sign>
  (r/template-sum [label token product]
    (r/label label (r/chook product (r/lit token)))
    "positive sign" \+ 1, "negative sign" \- -1))

(def <empty-number-tail>
  (r/chook identity r/<emptiness>))

(def <imprecise-fractional-part>
  (r/prefix
    (r/lit \.)
    (r/+ (r/hook #(partial + %)
           (r/cascading-rep+ r/<decimal-digit> #(/ % 10) #(/ (+ %1 %2) 10)))
         <empty-number-tail>)))

(def <exponential-part>
  (r/prefix
    (r/set-term "exponent indicator" "eE")
      ; If I wasn't worrying about pure Clojure,
      ; use (r/case-insensitive-lit \e) above instead.
    (r/hook #(partial * (expt-int 10 %)) <decimal-natural-number>)))

(def <fractional-exponential-part>
  (r/for [frac-fn <imprecise-fractional-part>
          exp-fn (r/+ <exponential-part> <empty-number-tail>)]
    (comp exp-fn frac-fn)))

(def <imprecise-number-tail>
  (r/for [tail-fn (r/+ <fractional-exponential-part> <exponential-part>)
          big-dec? (r/opt (r/lit \M))]
    (comp (if big-dec? bigdec double) tail-fn)))

(def <fraction-denominator-tail>
  ; Product: a unary function on an integer.
  (r/prefix
    (r/lit \/)
    (r/hook (fn [denominator] #(/ % denominator))
      (r/antivalidate zero? "a fraction's denominator cannot be zero"
        <decimal-natural-number>))))

(r/defn radix-coefficient-tail [base]
  (r/hook constantly
    (r/prefix
      (r/set-term "radix indicator" "rR")
        ; If I wasn't worrying about pure Clojure,
        ; use (case-insensitive-r/lit \r) above instead.
      (radix-natural-number base))))

(r/defn number-tail [base]
  (r/+ <imprecise-number-tail> <fraction-denominator-tail>
       (radix-coefficient-tail base) <empty-number-tail>))

(def <number>
  (r/for "a number"
    [sign (r/opt <number-sign>)
     prefix-number <decimal-natural-number>
     tail-fn (number-tail prefix-number)
     _ <form-end>]
    (tail-fn (* (or sign 1) prefix-number))))

;; Unicode escape sequences for chars and strings.

(def <unicode-escape-sequence>
  (r/prefix (r/lit \u)
    (r/hook (comp char reduce-hexadecimal-digits)
      (r/factor= 4 r/<hexadecimal-digit>))))

;; Characters.

(def <character-indicator> (r/lit \\))

(def <character-name>
  (r/+ (r/mapsum #(r/chook (key %) (r/phrase (val %))) char-name-string)
       <unicode-escape-sequence>))

(def <character> (r/prefix <character-indicator> <character-name>))

;; Strings.

(def <string-delimiter> (r/lit \"))

(def <escaped-char>
  (r/prefix <character-indicator>
    (r/label "a valid escape sequence"
      (r/+ (r/template-sum [token character]
             (r/chook character (r/lit token))
             \t \tab, \n \newline, \\ \\, \" \")
           <unicode-escape-sequence>))))

(def <normal-string-char> (r/antilit \"))

(def <string-char> (r/+ <escaped-char> <normal-string-char>))

(def <string>
  (r/hook #(->> % seq/flatten str*)
    (r/circumfix <string-delimiter> (r/rep* <string-char>) <string-delimiter>)))

;; Circumflex compound forms: lists, vectors, maps, and sets.

(def <form-series> (r/suffix (r/rep* #'<form>) <opt-ws>))

(t/do-template [<rule> start-token end-token product-fn]
  (def <rule>
    (r/for [_ (r/lit start-token)
            contents <form-series>
            _ (r/lit end-token)]
      (product-fn contents)))
  <list> \( \) #(apply list %)
  <vector> \[ \] vec
  <map> \{ \} #(apply hash-map %)
  <set-inner> \{ \} set)

;; Simple prefix forms: syntax-quote, deref, etc.

(r/defn padded-lit [token]
  (r/prefix (r/lit token) <opt-ws>))

(t/do-template [<rule> prefix product-fn-symbol]
  (def <rule>
    (r/hook (prefix-list-fn product-fn-symbol)
      (r/prefix (r/cat (padded-lit prefix) <opt-ws>) #'<form>)))
  <quoted> \' `quote
  <syntax-quoted> \` `syntax-quote
  <unquoted> \~ `unquote
  <derefed> \@ `deref
  <var-inner> \' `var
  <deprecated-meta> \^ `meta)

(def <unquote-spliced>
  (r/hook (prefix-list-fn `unquote-splicing)
    (r/prefix (r/cat (r/lex (r/phrase "~@")) <opt-ws>) #'<form>)))

(def <deprecated-meta>
  (r/suffix <deprecated-meta>
    (r/effects println
      "WARNING: The ^ indicator is deprecated (since Clojure 1.1).")))

;; With-meta #^ forms.

(def <tag>
  (r/hook #(hash-map :tag %)
    (r/+ <keyword> <symbol>)))

(def <metadata>
  (r/+ <map> <tag>))

(def <with-meta-inner>
  (r/prefix (padded-lit \^)
    (r/for [metadata <metadata>, _ <opt-ws>, content #'<form>]
      (list `with-meta content metadata))))

;; Anonymous functions.

(def <anonymous-fn-parameter-suffix>
  (r/+ <decimal-natural-number> (r/lit \&) (r/chook 1 r/<emptiness>)))

(def <anonymous-fn-parameter>
  (r/for "a parameter"
    [_ (r/lit \%)
     context r/<fetch-context>
     :let [fn-context (:anonymous-fn-context context)]
     _ (r/only-when fn-context
         "a parameter literals must be inside an anonymous function")
     suffix <anonymous-fn-parameter-suffix>
     :let [already-existing-symbol (get-already-existing-symbol fn-context
                                                                suffix)
           parameter-symbol (or already-existing-symbol (gensym "parameter"))]
     _ (if (nil? already-existing-symbol)
         (r/alter-context update-fn-context suffix parameter-symbol)
         r/<emptiness>)]
    parameter-symbol))

(def <anonymous-fn-inner>
  (r/for [_ (r/lit \()
          pre-context r/<fetch-context>
          _ (r/only-when (not (:anonymous-fn-context pre-context))
              "nested anonymous functions are not allowed")
          _ (r/alter-context assoc
              :anonymous-fn-context (AnonymousFnContext [] nil))
          content <form-series>
          post-context r/<fetch-context>
          _ (r/alter-context assoc :anonymous-fn-context nil)
          _ (r/lit \))]
    (let [anonymous-fn-context (:anonymous-fn-context post-context)
          parameters (make-parameter-vector anonymous-fn-context)]
      (list `fn 'anonymous-fn parameters content))))

;; Regex patterns, EvalReaders, and unreadables.

(def <pattern-inner>
  (r/hook (comp re-pattern str*)
    (r/circumfix <string-delimiter>
                 (r/rep* <normal-string-char>)
                 <string-delimiter>)))

(def <evaluated-inner>
  (r/for [_ (r/lit \=)
          context r/<fetch-context>
          _ (r/only-when (:reader-eval? context)
              "EvalReader forms (i.e. #=(...)) have been prohibited.")
          content <list>]
    (eval content)))

(def <unreadable-inner>
  (r/for [_ (r/lit \<)
          content (r/rep* (r/antilit \>))
          _ (r/opt (r/lit \>))
          _ (r/with-error
              (format "the data in #<%s> is unrecoverable" (str* content)))]
    nil))

;; All forms put together. (Order matters for lexed rules.)

(def <dispatched-inner>
  (r/+ <anonymous-fn-inner> <set-inner> <var-inner> <with-meta-inner> <pattern-inner>
       <evaluated-inner> <unreadable-inner>))

(def <dispatched>
  (r/prefix (r/lit \#) <dispatched-inner>))

(def <form-content>
  (r/+ <list> <vector> <map> <dispatched> <string> <syntax-quoted>
       <unquote-spliced> <unquoted> <deprecated-meta> <character> <keyword>
       <anonymous-fn-parameter> <symbol> <number>))

(def <form>
  (r/label "a form" (r/prefix <opt-ws> <form-content>)))

;;; THE FINAL READ FUNCTION.

(defn read-string
  "Reads one object from the given string. Also can
  take the options below. If the reading is successful,
  the resulting object is returned. Otherwise, a Java
  Exception is thrown.
  ns-name: A string. The name of the namespace to
           interpret double-coloned keywords in.
           Defaults to (name *ns*).
  ns-aliases: A map of strings to strings. Keys are
              namespace aliases, and vals are
              corresponding namespace names. Defaults
              to (ns-aliases *ns*).
  reader-eval?: A boolean. If logical true, allows
                ReaderEval forms (i.e. #=(...)),
                which can be a security hole.
                Defaults to *read-eval*."
  [input & opts]
  (let [{:keys #{ns-name ns-aliases reader-eval?}} (apply hash-map opts)]
    (r/parse <form> input (ClojureContext ns-name ns-aliases nil reader-eval?)
      (fn [product position] product)
      (fn [error] (throw (Exception. (r/format-parse-error error)))))))  

;;; TESTS.

(deftest various-rules
  (is (match? <form> "55.2e2" :product? #(== % 5520.)))
  (is (match? <form> "16r3AF" :product? #(== % 943)))
  (is (match? <form> "16." :product? #(== % 16.)))
  (is (match? <form> "true" :product? true?))
  (is (= (with-out-str (r/parse <form> "^()" {} list list))
         "WARNING: The ^ indicator is deprecated (since Clojure 1.1).\n"))
  (is (match? <form> "[()]" :product? #(= % [()])))
  (is (match? <form> "\"\\na\\u3333\"" :product? #(= % "\na\u3333")))
  (is (non-match? <form> "([1 32]"
        :position 7
        :labels #{"a form" "')'" "whitespace"}))
  (is (non-match? <form> "a/b/c"
        :position 3
        :messages #{"multiple slashes aren't allowed in symbols"}
        :labels #{"an indicator" "the end of input"
                  "a symbol character" "whitespace"}))
  (is (match? <form> ":a/b" :product? #(= % :a/b)))
  (is (match? <form> "::b"
        :context (ClojureContext "user" nil nil nil)
        :product? #(= % :user/b)))
  (is (non-match? <form> "::z/abc"
        :position 3
        :messages #{"no namespace with alias 'z'"}
        :labels #{"the end of input" "a symbol character" "an indicator"
                  "whitespace"}))
  (is (match? <form> "+" :product? #(= % '+)))
  (is (match? <form> "clojure.core//" :product? #(= % 'clojure.core//)))
  (is (match? <form> "#!/usr/bin/clojure\n\"a\\n\"" :product? #(= % "a\n")))
  (is (match? <form> "[~@a ()]"
        :product? #(= % [(list 'clojure.core/unquote-splicing 'a) ()])))
  (is (match? <form> "[#(%) #(apply + % %2 %2 %&)]"
        :context (ClojureContext "user" nil nil nil)
        :product? #(= ((eval (second %)) 3 2 8 1) 16)))
  (is (match? <form> "#=(+ 3 2)" :context (ClojureContext nil nil nil true)
                                :product? #(= % 5)))
  (is (match? <form> "#\"\\w+\""
        :product? #(re-matches % "abc")))
  (is (non-match? <form> "17rAZ"
        :position 4
        :labels #{"a base-17 digit" "an indicator" "whitespace"
                  "the end of input"}))
  (is (non-match? <form> "#(% #(%))"
        :position 6
        :context (ClojureContext "user" nil nil nil)
        :messages #{"nested anonymous functions are not allowed"}))
  (is (non-match? <form> "3/0 3"
        :position 3
        :labels #{"a decimal digit"}
        :messages #{"a fraction's denominator cannot be zero"}))
  (is (non-match? <form> "#<java.lang.String@35235>"
        :position 25
        :labels #{}
        :messages #{"the data in #<java.lang.String@35235> is unrecoverable"}))
  (is (= (read-string "[3 2 5]") [3 2 5])))

(run-tests)
