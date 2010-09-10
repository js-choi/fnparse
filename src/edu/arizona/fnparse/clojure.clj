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

(defn update-fn-context [context parameter-suffix parameter-symbol]
  (cond
    (integer? parameter-suffix)
      (update-in context [:anonymous-fn-context :normal-parameters] 
        conj parameter-symbol)
    (= parameter-suffix \&)
      (update-in context [:anonymous-fn-context]
        assoc :slurping-parameter parameter-symbol)))

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

(def <symbol-first-char>
  (h/+ h/<ascii-letter> <non-alphanumeric-symbol-char>))

(def <symbol-char>
  (h/label "a symbol character"
    (h/+ <symbol-first-char> h/<decimal-digit>)))

(def <symbol-char-series>
  (h/hook str* (h/rep <symbol-char>)))

(def <symbol-end>
  (h/annotate-error annotate-symbol-end <form-end>))

(def <slash-symbol-suffix>
  (h/chook "/" <ns-separator>))

(def <symbol-suffix>
  (h/prefix <ns-separator> (h/+ <symbol-char-series> <slash-symbol-suffix>)))

(def <symbol>
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

(h/defmaker >form-series< [fn-info]
  (h/suffix (h/rep* (>form< fn-info)) <ws?>))

(t/do-template [>rule-maker< start-token end-token product-fn]
  (h/defmaker >rule-maker< [fn-info]
    (h/for [_ (h/lit start-token)
            contents (>form-series< fn-info)
            _ (h/lit end-token)]
      (product-fn contents)))
  >list< \( \) #(apply list %)
  >vector< \[ \] identity
  >map< \{ \} #(apply hash-map %)
  >set-inner< \{ \} set)

;; Simple prefix forms: syntax-quote, deref, etc.

(h/defmaker >padded-lit< [token]
  (h/suffix (h/lit token) <ws?>))

(t/do-template [>rule-maker< prefix product-fn-symbol]
  (h/defmaker >rule-maker< [fn-info]
    (h/hook (prefix-list-fn product-fn-symbol)
      (h/prefix (h/cat (>padded-lit< prefix) <ws?>) (>form< fn-info))))
  >quoted< \' `quote
  >syntax-quoted< \` `syntax-quote
  >unquoted< \~ `unquote
  >derefed< \@ `deref
  >var-inner< \' `var
  >deprecated-meta< \^ `meta)

(t/do-template [>rule-maker< prefix product-fn-symbol]
  (h/defmaker >rule-maker< [fn-info]
    (h/hook (prefix-list-fn product-fn-symbol)
      (h/prefix (h/cat (>padded-lit< prefix) <ws?>) (>form< fn-info))))
  >quoted< \' `quote
  >syntax-quoted< \` `syntax-quote
  >unquoted< \~ `unquote
  >derefed< \@ `deref
  >var-inner< \' `var
  >deprecated-meta< \^ `meta)

(h/defmaker >unquote-spliced< []
  (h/hook (prefix-list-fn `unquote-splicing)
    (h/prefix (h/cat (h/lex (h/phrase "~@")) <ws?>) (>form< nil))))

#_(def <deprecated-meta>
  (h/prefix
    (h/add-warning
      "the '^' indicator has been deprecated since Clojure 1.1; use (meta ...) instead")
    <deprecated-meta>))

;; With-meta #^ forms.

(def <tag>
  (h/hook #(hash-map :tag %)
    (h/+ <keyword> <symbol>)))

(def <metadata>
  (h/+ (>map< nil) <tag>))

(h/defmaker >with-meta-inner< [fn-info]
  (h/prefix (>padded-lit< \^)
    (h/for [metadata <metadata>, _ <ws?>, content (>form< fn-info)]
      (list `with-meta content metadata))))

;; Anonymous functions.

(def <anonymous-fn-parameter-suffix>
  (h/+ <decimal-natural-number> (h/lit \&) (h/chook 1 h/<emptiness>)))

(h/defmaker >anonymous-fn-parameter< [fn-info]
  (h/for "a parameter"
    [_ (h/lit \%)
     context h/<fetch-context>
     :let [fn-context (:anonymous-fn-context context)]
     _ (h/when fn-context
         "parameter literals must be inside an anonymous function")
     suffix <anonymous-fn-parameter-suffix>
     :let [already-existing-symbol (get-already-existing-symbol fn-context
                                                                suffix)
           parameter-symbol (or already-existing-symbol (gensym "parameter"))]
     _ (if (nil? already-existing-symbol)
         (h/alter-context update-fn-context suffix parameter-symbol)
         h/<emptiness>)]
    parameter-symbol))

(h/defmaker >anonymous-fn-inner< [fn-info]
  (h/for [_ (h/lit \()
          pre-context h/<fetch-context>
          _ (h/when (not (:anonymous-fn-context pre-context))
              "nested anonymous functions are not allowed")
          _ (h/alter-context assoc
              :anonymous-fn-context (AnonymousFnContext. [] nil))
          content (>form-series< fn-info)
          post-context h/<fetch-context>
          _ (h/alter-context assoc :anonymous-fn-context nil)
          _ (h/lit \))]
    (let [anonymous-fn-context (:anonymous-fn-context post-context)
          parameters (make-parameter-vector anonymous-fn-context)]
      (list `fn 'anonymous-fn parameters (apply list content)))))

;; Regex patterns, EvalReaders, and unreadables.

(def <pattern-inner>
  (h/hook (comp re-pattern str*)
    (h/circumfix <string-delimiter>
                 (h/rep* <normal-string-char>)
                 <string-delimiter>)))

(def <evaluated-inner>
  (h/for [_ (h/lit \=)
          context h/<fetch-context>
          _ (h/when (:reader-eval? context)
              "EvalReader forms (i.e. #=(...)) have been prohibited.")
          content (>list< nil)]
    (eval content)))

(def <unreadable-inner>
  (h/for [_ (h/lit \<)
          content (h/rep* (h/antilit \>))
          _ (h/opt (h/lit \>))
          _ (h/with-error
              (format "the data in #<%s> is unrecoverable" (str* content)))]
    nil))

(h/defmaker >dispatched-inner< [fn-info]
  ;; All forms put together. (The order of sub-rules matters for lexed rules.)
  (h/+ (>anonymous-fn-inner< fn-info) (>set-inner< fn-info) (>var-inner< fn-info) (>with-meta-inner< fn-info)
       <pattern-inner> <evaluated-inner> <unreadable-inner>))

(h/defmaker >dispatched< [fn-info]
  (h/prefix (h/lit \#) (>dispatched-inner< fn-info)))

(h/defmaker >form-content< [fn-info]
  (h/+ (>list< fn-info) (>vector< fn-info) (>map< fn-info) (>dispatched< fn-info)
       <string> (>syntax-quoted< fn-info)
       (>unquote-spliced< fn-info) (>unquoted< fn-info) (>deprecated-meta< fn-info) <character> <keyword>
       (>anonymous-fn-parameter< fn-info) <symbol> <number>))

(h/defmaker >form< [fn-info]
  (h/label "a form" (h/prefix <ws?> (>form-content< fn-info))))

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
