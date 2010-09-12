; TODO Vary anonymous function label symbol

(ns edu.arizona.fnparse.clojure
  (:require [edu.arizona.fnparse [hound :as h] [core :as c]]
            [clojure [template :as t] [set :as set]]
            [clojure.contrib [except :as except]])
  (:refer-clojure :exclude #{read-string}))

; TODO: Fix implementation of decimal numbers.

;;; HELPER FUNCTIONS AND TYPES.

(defrecord ClojureContext
  [ns-name ns-aliases anonymous-fn-context reader-eval?])

(defrecord AnonymousFnContext [normal-parameters slurping-parameter])

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

(defn merge-form-meta [meta-1 meta-2]
  (assoc meta-1
    :anonymous-fn-parameter-n
    (max (or (:anonymous-fn-parameter-n meta-1) 0)
         (or (:anonymous-fn-parameter-n meta-2) 0))
    :anonymous-fn-slurping-parameter?
    (or (:anonymous-fn-slurping-parameter? meta-1)
        (:anonymous-fn-slurping-parameter? meta-2))))

(defn parameter-symbol [fn-sym suffix]
  (symbol (str fn-sym "-para-" suffix)))

;;; RULES START HERE.

(declare >form<)

;; Whitespace.

(h/defrule <comment-indicator>
  "There are two line comment indicators, `;` and `#!`.
  This rule consumes either of them."
  (h/+ (h/lit \;) (h/lex (h/phrase "#!"))))

(h/defrule <comment-char>
  "Consumes a character inside a line comment, i.e. any non-break character."
  (h/antilit \newline))

(h/defrule <comment>
  "Consumes a line comment."
  (h/cat <comment-indicator> (h/rep* <comment-char>)))

(h/defrule <discarded>
  "Consumes a discarded form (prefixed by `#_`), which counts as whitespace."
  (h/prefix (h/lex (h/phrase "#_")) (>form< nil)))

(h/defrule <normal-ws-char>
  "Consumes a normal whitespace character such as space or newline."
  (h/term "a whitespace character" ws-set))

(h/defrule <ws>
  "The general whitespace rule: spaces, line comments, and discarded forms."
  (h/label "whitespace"
    (h/rep (h/+ <normal-ws-char> <comment> <discarded>))))

(h/defrule <ws?>
  "Consumes optional whitespace."
  (h/opt <ws>))

;; Indicators and form separators.

(h/defrule <indicator>
  "Consumes a Clojure indicator character."
  (h/term "an indicator" indicator-set))

(h/defrule <separator>
  "Consumes a separator of Clojure forms: whitespace or an indicator."
  (h/+ <ws> <indicator>))

(h/defrule <form-end>
  "Peeks and checks for a separator or the end of input."
  {:consumes "No characters."}
  (h/+ (h/peek <separator>) h/<end-of-input>))

;; Symbols.

(h/defrule <ns-separator>
  "Consumes a forward slash: the separator of namespaces."
  (h/lit \/))

(h/defrule <non-alphanumeric-symbol-char>
  "Consumes a non-alphanumeric character allowed in Clojure symbols."
  (h/set-term "a non-alphanumeric symbol character" "*+!---?."))

(h/defrule <symbol-first-char>
  "Symbols' first symbols have special limitations to distinguish them
  from numbers, lists, etc."
  (h/+ h/<ascii-letter> <non-alphanumeric-symbol-char>))

(h/defrule <symbol-char>
  "Symbols can contain whatever symbols they can start with as well as numbers."
  (h/label "a symbol character"
    (h/+ <symbol-first-char> h/<decimal-digit>)))

(h/defrule <symbol-char-series>
  "A phrase of symbol characters. Its products are strings.
  It itself *cannot* contain slashes."
  {:product "A string."}
  (h/hook str* (h/rep <symbol-char>)))

(h/defrule <symbol-end>
  "Matches the end of a symbol, but does not consume any tokens.
  Equivalent to `<form-end>`, but annotates with special form-specific errors."
  (h/annotate-error annotate-symbol-end <form-end>))

(h/defrule <slash-symbol-suffix>
  "There is a special case for symbol suffixes: `namespace//`
  is a symbol of name '/'. (This made it possible for division to
  be represented by the `clojure.core/` function.)"
  (h/chook "/" <ns-separator>))

(h/defrule <symbol-suffix>
  "A symbol suffix, i.e. a slash followed by
  symbol characters or a single slash."
  (h/prefix <ns-separator> (h/+ <symbol-char-series> <slash-symbol-suffix>)))

(h/defrule <symbol>
  "A symbol character. No whitespace padding."
  (h/for "a symbol"
    [first-char <symbol-first-char>
     rest-pre-slash (h/opt <symbol-char-series>)
     post-slash (h/opt <symbol-suffix>)
     _ <symbol-end>]
    (let [pre-slash (str first-char rest-pre-slash)]
      (if post-slash
        (symbol pre-slash post-slash)
        (or (peculiar-symbols pre-slash) ; In case it's true, false, or nil
            (symbol pre-slash))))))

;; Keywords.

(def <keyword-indicator> (h/lit \:))

(def <normal-keyword>
  (h/for [_ <keyword-indicator>
          pre-slash (h/opt <symbol-char-series>)
          post-slash (h/opt <symbol-suffix>)
          _ <symbol-end>]
    (if post-slash
      (keyword pre-slash post-slash)
      (keyword pre-slash))))

(def <peek-ns-separator> (h/peek <ns-separator>))

(h/defmaker >fetch-referred-namespace< [context namespace-alias]
  (h/when (get-in context [:ns-aliases namespace-alias])
    (format "no namespace with alias '%s'" namespace-alias)))

(h/defmaker >ns-qualified-keyword-end-with-slash< [pre-slash]
  (h/for [_ <peek-ns-separator>
          context h/<fetch-context>
          prefix (>fetch-referred-namespace< context pre-slash)
          suffix <symbol-suffix>]
    [prefix suffix]))

(h/defmaker >ns-qualified-keyword-empty-end< [pre-slash]
  (h/for [context h/<fetch-context>]
    [(:ns-name context) pre-slash]))

(h/defmaker >ns-resolved-keyword-end< [pre-slash]
  (h/+ (>ns-qualified-keyword-end-with-slash< pre-slash)
       (>ns-qualified-keyword-empty-end< pre-slash)))

(def <ns-resolved-keyword>
  (h/for [_ (h/lex (h/factor= 2 <keyword-indicator>))
          pre-slash <symbol-char-series>
          [prefix suffix] (>ns-resolved-keyword-end< pre-slash)
          _ <form-end>]
    (keyword prefix suffix)))

(def <keyword>
  (h/label "a keyword"
    (h/+ <ns-resolved-keyword> <normal-keyword>)))

;; Numbers.

(h/defmaker >radix-natural-number< [core]
  (h/hooked-rep #(+ (* core %1) %2) 0 (h/radix-digit core)))

(def <decimal-natural-number>
  (>radix-natural-number< 10))

(def <number-sign>
  (h/template-sum [label token product]
    (h/label label (h/chook product (h/lit token)))
    "positive sign" \+ 1, "negative sign" \- -1))

(def <empty-number-tail>
  (h/chook identity h/<emptiness>))

(def <imprecise-fractional-part>
  (letfn [(reduce-digit-accumulator [[prev-num multiplier] next-digit]
            [(+ (* next-digit multiplier) prev-num) (/ multiplier 10)])]
    (h/prefix
      (h/lit \.)
      (h/+ (->> h/<decimal-digit>
             (h/hooked-rep reduce-digit-accumulator [0 0.1])
             (h/hook #(partial + (get % 0))))
           (h/hook #(partial + (/ % 10.)) <decimal-natural-number>)
           <empty-number-tail>))))

(def <exponential-part>
  (h/prefix
    (h/case-insensitive-lit \e)
    (h/hook #(partial * (expt-int 10 %)) <decimal-natural-number>)))

(def <fractional-exponential-part>
  (h/for [frac-fn <imprecise-fractional-part>
          exp-fn (h/+ <exponential-part> <empty-number-tail>)]
    (comp exp-fn frac-fn)))

(def <imprecise-number-tail>
  (h/for [tail-fn (h/+ <fractional-exponential-part> <exponential-part>)
          big-dec? (h/opt (h/lit \M))]
    (comp (if big-dec? bigdec double) tail-fn)))

(def <fraction-denominator-tail>
  ; Product: a unary function on an integer.
  (h/prefix
    (h/lit \/)
    (h/hook (fn [denominator] #(/ % denominator))
      (h/antivalidate zero? "a fraction's denominator cannot be zero"
        <decimal-natural-number>))))

(h/defmaker >radix-coefficient-tail< [core]
  (h/hook constantly
    (h/prefix
      (h/case-insensitive-lit \r)
      (>radix-natural-number< core))))

(h/defmaker >number-tail< [core]
  (h/+ <imprecise-number-tail> <fraction-denominator-tail>
       (>radix-coefficient-tail< core) <empty-number-tail>))

(def <number>
  (h/for "a number"
    [sign (h/opt <number-sign>)
     prefix-number <decimal-natural-number>
     tail-fn (>number-tail< prefix-number)
     _ <form-end>]
    (tail-fn (* (or sign 1) prefix-number))))

;; Unicode escape sequences for chars and strings.

(def <unicode-escape-sequence>
  (h/prefix (h/lit \u)
    (h/hook (comp char reduce-hexadecimal-digits)
      (h/factor= 4 h/<hexadecimal-digit>))))

;; Characters.

(def <character-indicator> (h/lit \\))

(def <character-name>
  (h/+ (h/mapsum #(h/chook (key %) (h/phrase (val %))) char-name-string)
       <unicode-escape-sequence>))

(def <character> (h/prefix <character-indicator> <character-name>))

;; Strings.

(def <string-delimiter> (h/lit \"))

(def <escaped-char>
  (h/prefix <character-indicator>
    (h/label "a valid escape sequence"
      (h/+ (h/template-sum [token character]
             (h/chook character (h/lit token))
             \t \tab, \n \newline, \\ \\, \" \")
           <unicode-escape-sequence>))))

(def <normal-string-char> (h/antilit \"))

(def <string-char> (h/+ <escaped-char> <normal-string-char>))

(def <string>
  (h/hook #(->> % flatten str*)
    (h/circumfix <string-delimiter> (h/rep* <string-char>) <string-delimiter>)))

;; Circumflex compound forms: lists, vectors, maps, and sets.

(h/defmaker >form-series< [fn-sym]
  (h/suffix
    (h/hook
      (fn [forms] (with-meta forms (reduce merge-form-meta (map meta forms))))
      (h/rep* (>form< fn-sym)))
    <ws?>))

(t/do-template [>rule-maker< start-token end-token product-fn]
  (h/defmaker >rule-maker< [fn-sym]
    (h/for [_ (h/lit start-token)
            contents (>form-series< fn-sym)
            _ (h/lit end-token)]
      (with-meta (product-fn contents) (meta contents))))
  >list< \( \) #(apply list %)
  >vector< \[ \] identity
  >map< \{ \} #(apply hash-map %)
  >set-inner< \{ \} set)

;; Simple prefix forms: syntax-quote, deref, etc.

(h/defmaker >padded-lit< [token]
  (h/suffix (h/lit token) <ws?>))

(t/do-template [>rule-maker< prefix product-fn-symbol]
  (h/defmaker >rule-maker< [fn-sym]
    (h/hook (prefix-list-fn product-fn-symbol)
      (h/prefix (h/cat (>padded-lit< prefix) <ws?>) (>form< fn-sym))))
  >quoted< \' `quote
  >syntax-quoted< \` `syntax-quote
  >unquoted< \~ `unquote
  >derefed< \@ `deref
  >var-inner< \' `var
  >deprecated-meta< \^ `meta)

(t/do-template [>rule-maker< prefix product-fn-symbol]
  (h/defmaker >rule-maker< [fn-sym]
    (h/hook (prefix-list-fn product-fn-symbol)
      (h/prefix (h/cat (>padded-lit< prefix) <ws?>) (>form< fn-sym))))
  >quoted< \' `quote
  >syntax-quoted< \` `syntax-quote
  >unquoted< \~ `unquote
  >derefed< \@ `deref
  >var-inner< \' `var)

(h/defmaker >unquote-spliced< [fn-sym]
  (h/hook (prefix-list-fn `unquote-splicing)
    (h/prefix (h/cat (h/lex (h/phrase "~@")) <ws?>) (>form< fn-sym))))

;; With-meta ^ forms.

(def <tag>
  (h/hook #(hash-map :tag %)
    (h/+ <keyword> <symbol>)))

(h/defmaker >metadata< [fn-sym]
  (h/+ (>map< fn-sym) <tag>))

(h/defmaker >meta< [fn-sym]
  (h/prefix (>padded-lit< \^)
    (h/for [metadata (>metadata< fn-sym), _ <ws?>, content (>form< fn-sym)]
      (list `with-meta content metadata))))

;; Anonymous functions.

(defrecord AnonymousFnParameter [suffix])

(def <anonymous-fn-parameter-suffix>
  (h/+ (h/except "non-negative number" <decimal-natural-number> (h/lit \0))
       (h/lit \&)
       (h/chook 1 h/<emptiness>)))

(h/defmaker >anonymous-fn-parameter< [fn-sym]
  (h/for "a parameter"
    [prefix (h/lit \%)
     _ (h/when fn-sym
         "parameter literals must be inside an anonymous function")
     suffix <anonymous-fn-parameter-suffix>]
    (with-meta (parameter-symbol fn-sym suffix)
      (cond
        (integer? suffix) {:anonymous-fn-parameter-n suffix}
        (= \& suffix) {:anonymous-fn-slurping-parameter? true}))))

(h/defmaker >anonymous-fn-inner< [surrounding-fn-sym]
  (h/for [_ (h/lit \()
          _ (h/when (not surrounding-fn-sym)
              "nested anonymous functions are not allowed") 
          :let [new-fn-sym (gensym "anonymous-fn")]
          content (>form-series< new-fn-sym)
          _ (h/lit \))
          :let [content-meta (meta content)
                parameter-n (:anonymous-fn-parameter-n content-meta)
                parameters-before-slurping
                (->> (range 1 (inc parameter-n))
                     (map #(symbol (str new-fn-sym "-para-" %)))
                     vec)
                parameters
                (if-not (:anonymous-fn-slurping-parameter? content-meta)
                  parameters-before-slurping
                  (conj parameters-before-slurping
                    '& (parameter-symbol new-fn-sym \&)))]]
    `(fn ~new-fn-sym ~parameters ~(apply list content))))

;; Regex patterns, EvalReaders, and unreadables.

(def <pattern-inner>
  (h/hook (comp re-pattern str*)
    (h/circumfix <string-delimiter>
                 (h/rep* <normal-string-char>)
                 <string-delimiter>)))

(h/defmaker >evaluated-inner< [fn-sym]
  (h/for [_ (h/lit \=)
          context h/<fetch-context>
          _ (h/when (:reader-eval? context)
              "EvalReader forms (i.e. #=(...)) have been prohibited.")
          content (>list< fn-sym)]
    (eval content)))

(def <unreadable-inner>
  (h/for [_ (h/lit \<)
          content (h/rep* (h/antilit \>))
          _ (h/opt (h/lit \>))
          _ (h/with-error
              (format "the data in #<%s> is unrecoverable" (str* content)))]
    nil))

(h/defmaker >dispatched-inner< [fn-sym]
  ;; All forms put together. (The order of sub-rules matters for lexed rules.)
  (h/+ (>anonymous-fn-inner< fn-sym) (>set-inner< fn-sym) (>var-inner< fn-sym)
       <pattern-inner> (>evaluated-inner< fn-sym) <unreadable-inner>))

(h/defmaker >dispatched< [fn-sym]
  (h/prefix (h/lit \#) (>dispatched-inner< fn-sym)))

(h/defmaker >form-content< [fn-sym]
  (h/+ (>list< fn-sym) (>vector< fn-sym) (>map< fn-sym) (>dispatched< fn-sym)
       <string> (>syntax-quoted< fn-sym)
       (>unquote-spliced< fn-sym) (>unquoted< fn-sym) (>meta< fn-sym) <character> <keyword>
       (>anonymous-fn-parameter< fn-sym) <symbol> <number>))

(h/defmaker >form< [fn-sym]
  (h/label "a form" (h/prefix <ws?> (>form-content< fn-sym))))

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
    (h/match
      (h/make-state input
        :context (ClojureContext. ns-name ns-aliases nil reader-eval?))
      (>form< nil)
      :success-fn (fn [product position] product)
      :failure-fn (fn [error]
                    (except/throwf "Clojure parsing error: %s"
                      (h/format-parse-error error))))))
