(ns edu.arizona.fnparse.clojure-impure
  (:require [edu.arizona.fnparse [hound :as p] [core :as c]]
            [clojure [template :as t] [set :as set]]
            [clojure.contrib [seq :as seq] [except :as except]])
  (:refer-clojure :exclude #{read-string})
  (:import [clojure.lang IPersistentMap]))

; TODO: Fix implementation of decimal numbers.

;;; HELPER FUNCTIONS AND TYPES.

(deftype ClojureContext [ns-name ns-aliases anonymous-fn-context reader-eval?]
  IPersistentMap)

(deftype AnonymousFnContext [normal-parameters slurping-parameter]
  IPersistentMap)

(defn prefix-list-fn [prefix-rule]
  (fn [product] (list prefix-rule product)))

(defn str* [chars]
  (apply str chars))

(defn expt-int [core pow]
  (loop [n (int pow), y 1, z core]
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
  (when (= (:unexpected-token error) \/)
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

(def <comment-indicator> (p/+ (p/lit \;) (p/lex (p/phrase "#!"))))

(def <comment-char> (p/antilit \newline))

(def <comment> (p/cat <comment-indicator> (p/rep* <comment-char>)))

(def <discarded> (p/prefix (p/lex (p/phrase "#_")) #'<form>))

(def <normal-ws-char>
  (p/term "a whitespace character" ws-set))

(def <ws>
  (p/label "whitespace"
    (p/rep (p/+ <normal-ws-char> <comment> <discarded>))))

(def <opt-ws> (p/opt <ws>))

;; Indicators and form separators.

(def <indicator> (p/term "an indicator" indicator-set))

(def <separator> (p/+ <ws> <indicator>))

(def <form-end> (p/+ (p/peek <separator>) p/<end-of-input>))

;; Symbols.

(def <ns-separator> (p/lit \/))

(def <non-alphanumeric-symbol-char>
  (p/set-term "a non-alphanumeric symbol character" "*+!---?."))

(def <symbol-first-char>
  (p/+ p/<ascii-letter> <non-alphanumeric-symbol-char>))

(def <symbol-char>
  (p/label "a symbol character"
    (p/+ <symbol-first-char> p/<decimal-digit>)))

(def <symbol-char-series>
  (p/hook str* (p/rep <symbol-char>)))

(def <symbol-end>
  (p/annotate-error annotate-symbol-end <form-end>))

(def <slash-symbol-suffix>
  (p/chook "/" <ns-separator>))

(def <symbol-suffix>
  (p/prefix <ns-separator> (p/+ <symbol-char-series> <slash-symbol-suffix>)))

(def <symbol>
  (p/for "a symbol"
    [first-char <symbol-first-char>
     rest-pre-slash (p/opt <symbol-char-series>)
     post-slash (p/opt <symbol-suffix>)
     _ <symbol-end>]
    (let [pre-slash (str first-char rest-pre-slash)]
      (if post-slash
        (symbol pre-slash post-slash)
        (or (peculiar-symbols pre-slash) ; In case it's true, false, or nil
            (symbol pre-slash))))))

;; Keywords.

(def <keyword-indicator> (p/lit \:))

(def <normal-keyword>
  (p/for [_ <keyword-indicator>
          pre-slash (p/opt <symbol-char-series>)
          post-slash (p/opt <symbol-suffix>)
          _ <symbol-end>]
    (if post-slash
      (keyword pre-slash post-slash)
      (keyword pre-slash))))

(def <peek-ns-separator> (p/peek <ns-separator>))

(c/defmaker fetch-referred-namespace [context namespace-alias]
  (p/only-when (get-in context [:ns-aliases namespace-alias])
    (format "no namespace with alias '%s'" namespace-alias)))

(c/defmaker ns-qualified-keyword-end-with-slash [pre-slash]
  (p/for [_ <peek-ns-separator>
          context p/<fetch-context>
          prefix (fetch-referred-namespace context pre-slash)
          suffix <symbol-suffix>]
    [prefix suffix]))

(c/defmaker ns-qualified-keyword-empty-end [pre-slash]
  (p/for [context p/<fetch-context>]
    [(:ns-name context) pre-slash]))

(c/defmaker ns-resolved-keyword-end [pre-slash]
  (p/+ (ns-qualified-keyword-end-with-slash pre-slash)
       (ns-qualified-keyword-empty-end pre-slash)))

(def <ns-resolved-keyword>
  (p/for [_ (p/lex (p/factor= 2 <keyword-indicator>))
          pre-slash <symbol-char-series>
          [prefix suffix] (ns-resolved-keyword-end pre-slash)
          _ <form-end>]
    (keyword prefix suffix)))

(def <keyword>
  (p/label "a keyword"
    (p/+ <ns-resolved-keyword> <normal-keyword>)))

;; Numbers.

(c/defmaker radix-natural-number [core]
  (p/hooked-rep #(+ (* core %1) %2) 0 (p/radix-digit core)))

(def <decimal-natural-number>
  (radix-natural-number 10))

(def <number-sign>
  (p/template-sum [label token product]
    (p/label label (p/chook product (p/lit token)))
    "positive sign" \+ 1, "negative sign" \- -1))

(def <empty-number-tail>
  (p/chook identity p/<emptiness>))

(def <imprecise-fractional-part>
  (letfn [(reduce-digit-accumulator [[prev-num multiplier] next-digit]
            [(+ (* next-digit multiplier) prev-num) (/ multiplier 10)])]
    (p/prefix
      (p/lit \.)
      (p/+ (->> p/<decimal-digit>
             (p/hooked-rep reduce-digit-accumulator [0 0.1])
             (p/hook #(partial + (get % 0))))
           (p/hook #(partial + (/ % 10.)) <decimal-natural-number>)
           <empty-number-tail>))))

(def <exponential-part>
  (p/prefix
    (p/case-insensitive-lit \e)
    (p/hook #(partial * (expt-int 10 %)) <decimal-natural-number>)))

(def <fractional-exponential-part>
  (p/for [frac-fn <imprecise-fractional-part>
          exp-fn (p/+ <exponential-part> <empty-number-tail>)]
    (comp exp-fn frac-fn)))

(def <imprecise-number-tail>
  (p/for [tail-fn (p/+ <fractional-exponential-part> <exponential-part>)
          big-dec? (p/opt (p/lit \M))]
    (comp (if big-dec? bigdec double) tail-fn)))

(def <fraction-denominator-tail>
  ; Product: a unary function on an integer.
  (p/prefix
    (p/lit \/)
    (p/hook (fn [denominator] #(/ % denominator))
      (p/antivalidate zero? "a fraction's denominator cannot be zero"
        <decimal-natural-number>))))

(c/defmaker radix-coefficient-tail [core]
  (p/hook constantly
    (p/prefix
      (p/case-insensitive-lit \r)
      (radix-natural-number core))))

(c/defmaker number-tail [core]
  (p/+ <imprecise-number-tail> <fraction-denominator-tail>
       (radix-coefficient-tail core) <empty-number-tail>))

(def <number>
  (p/for "a number"
    [sign (p/opt <number-sign>)
     prefix-number <decimal-natural-number>
     tail-fn (number-tail prefix-number)
     _ <form-end>]
    (tail-fn (* (or sign 1) prefix-number))))

;; Unicode escape sequences for chars and strings.

(def <unicode-escape-sequence>
  (p/prefix (p/lit \u)
    (p/hook (comp char reduce-hexadecimal-digits)
      (p/factor= 4 p/<hexadecimal-digit>))))

;; Characters.

(def <character-indicator> (p/lit \\))

(def <character-name>
  (p/+ (p/mapsum #(p/chook (key %) (p/phrase (val %))) char-name-string)
       <unicode-escape-sequence>))

(def <character> (p/prefix <character-indicator> <character-name>))

;; Strings.

(def <string-delimiter> (p/lit \"))

(def <escaped-char>
  (p/prefix <character-indicator>
    (p/label "a valid escape sequence"
      (p/+ (p/template-sum [token character]
             (p/chook character (p/lit token))
             \t \tab, \n \newline, \\ \\, \" \")
           <unicode-escape-sequence>))))

(def <normal-string-char> (p/antilit \"))

(def <string-char> (p/+ <escaped-char> <normal-string-char>))

(def <string>
  (p/hook #(->> % seq/flatten str*)
    (p/circumfix <string-delimiter> (p/rep* <string-char>) <string-delimiter>)))

;; Circumflex compound forms: lists, vectors, maps, and sets.

(def <form-series> (p/suffix (p/rep* #'<form>) <opt-ws>))

(t/do-template [<rule> start-token end-token product-fn]
  (def <rule>
    (p/for [_ (p/lit start-token)
            contents <form-series>
            _ (p/lit end-token)]
      (product-fn contents)))
  <list> \( \) #(apply list %)
  <vector> \[ \] identity
  <map> \{ \} #(apply hash-map %)
  <set-inner> \{ \} set)

;; Simple prefix forms: syntax-quote, deref, etc.

(c/defmaker padded-lit [token]
  (p/prefix (p/lit token) <opt-ws>))

(t/do-template [<rule> prefix product-fn-symbol]
  (def <rule>
    (p/hook (prefix-list-fn product-fn-symbol)
      (p/prefix (p/cat (padded-lit prefix) <opt-ws>) #'<form>)))
  <quoted> \' `quote
  <syntax-quoted> \` `syntax-quote
  <unquoted> \~ `unquote
  <derefed> \@ `deref
  <var-inner> \' `var
  <deprecated-meta> \^ `meta)

(def <unquote-spliced>
  (p/hook (prefix-list-fn `unquote-splicing)
    (p/prefix (p/cat (p/lex (p/phrase "~@")) <opt-ws>) #'<form>)))

(def <deprecated-meta>
  (p/suffix <deprecated-meta>
    (p/effects println
      "WARNING: The ^ indicator is deprecated (since Clojure 1.1).")))

;; With-meta #^ forms.

(def <tag>
  (p/hook #(hash-map :tag %)
    (p/+ <keyword> <symbol>)))

(def <metadata>
  (p/+ <map> <tag>))

(def <with-meta-inner>
  (p/prefix (padded-lit \^)
    (p/for [metadata <metadata>, _ <opt-ws>, content #'<form>]
      (list `with-meta content metadata))))

;; Anonymous functions.

(def <anonymous-fn-parameter-suffix>
  (p/+ <decimal-natural-number> (p/lit \&) (p/chook 1 p/<emptiness>)))

(def <anonymous-fn-parameter>
  (p/for "a parameter"
    [_ (p/lit \%)
     context p/<fetch-context>
     :let [fn-context (:anonymous-fn-context context)]
     _ (p/only-when fn-context
         "a parameter literals must be inside an anonymous function")
     suffix <anonymous-fn-parameter-suffix>
     :let [already-existing-symbol (get-already-existing-symbol fn-context
                                                                suffix)
           parameter-symbol (or already-existing-symbol (gensym "parameter"))]
     _ (if (nil? already-existing-symbol)
         (p/alter-context update-fn-context suffix parameter-symbol)
         p/<emptiness>)]
    parameter-symbol))

(def <anonymous-fn-inner>
  (p/for [_ (p/lit \()
          pre-context p/<fetch-context>
          _ (p/only-when (not (:anonymous-fn-context pre-context))
              "nested anonymous functions are not allowed")
          _ (p/alter-context assoc
              :anonymous-fn-context (AnonymousFnContext [] nil))
          content <form-series>
          post-context p/<fetch-context>
          _ (p/alter-context assoc :anonymous-fn-context nil)
          _ (p/lit \))]
    (let [anonymous-fn-context (:anonymous-fn-context post-context)
          parameters (make-parameter-vector anonymous-fn-context)]
      (list `fn 'anonymous-fn parameters (apply list content)))))

;; Regex patterns, EvalReaders, and unreadables.

(def <pattern-inner>
  (p/hook (comp re-pattern str*)
    (p/circumfix <string-delimiter>
                 (p/rep* <normal-string-char>)
                 <string-delimiter>)))

(def <evaluated-inner>
  (p/for [_ (p/lit \=)
          context p/<fetch-context>
          _ (p/only-when (:reader-eval? context)
              "EvalReader forms (i.e. #=(...)) have been prohibited.")
          content <list>]
    (eval content)))

(def <unreadable-inner>
  (p/for [_ (p/lit \<)
          content (p/rep* (p/antilit \>))
          _ (p/opt (p/lit \>))
          _ (p/with-error
              (format "the data in #<%s> is unrecoverable" (str* content)))]
    nil))

;; All forms put together. (Order matters for lexed rules.)

(def <dispatched-inner>
  (p/+ <anonymous-fn-inner> <set-inner> <var-inner> <with-meta-inner>
       <pattern-inner> <evaluated-inner> <unreadable-inner>))

(def <dispatched>
  (p/prefix (p/lit \#) <dispatched-inner>))

(def <form-content>
  (p/+ <list> <vector> <map> <dispatched> <string> <syntax-quoted>
       <unquote-spliced> <unquoted> <deprecated-meta> <character> <keyword>
       <anonymous-fn-parameter> <symbol> <number>))

(def <form>
  (p/label "a form" (p/prefix <opt-ws> <form-content>)))

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
                which can create security holes.
                Defaults to *read-eval*."
  [input & opts]
  (let [{:keys #{ns-name ns-aliases reader-eval?}} (apply hash-map opts)]
    (p/match <form> input (ClojureContext ns-name ns-aliases nil reader-eval?)
      (fn [product position] product)
      (fn [error]
        (except/throwf "FnParse parsing error: %s"
          (c/format-parse-error error))))))
