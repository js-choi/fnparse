; TODO Vary anonymous function label symbol

(ns edu.arizona.fnparse.clojure
  "An almost pure Clojure parser in Clojure. The end result
  is the `read-string` function, which reads a `String` and
  returns the corresponding Clojure data structure or throws
  an error.
  
  Rule-makers that take a `fn-sym` parameter make rules
  that an anonymous function might contain. If `fn-sym`
  is nil, then there is no anonymous function surrounding
  the rule. If `fn-sym` is not nil, it must be the
  generated symbol of the surrounding anonymous function.
  
  Rules that end with '-inner' are rules inside the
  `<dispatch>` rule, and which lack the '#' that must
  precede them."
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
  "A symbol character. No whitespace padding. Note that it also
  matches `true`, `false`, and `nil`, the 'peculiar' symbols."
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

(h/defrule <keyword-indicator> "The colon." (h/lit \:))

(h/defrule <normal-keyword>
  "A normal keyword, e.g. `:integer` or `:com.tonio/strong`,
  i.e. a keyword that is not doubly coloned."
  (h/for [_ <keyword-indicator>
          pre-slash (h/opt <symbol-char-series>)
          post-slash (h/opt <symbol-suffix>)
          _ <symbol-end>]
    (if post-slash
      (keyword pre-slash post-slash)
      (keyword pre-slash))))

(h/defrule <peek-ns-separator> (h/peek <ns-separator>))

(h/defmaker >fetch-referred-namespace<
  "A rule that fetches from the context whatever namespace
  is referred to by the given `namespace-alias`, or else
  makes parsing fail."
  [namespace-alias]
  (h/for [context h/<fetch-context>
          ns-name (h/demand (get-in context [:ns-aliases namespace-alias])
                    (format "no namespace with alias '%s'" namespace-alias))]
    ns-name))

(h/defmaker >ns-qualified-keyword-end-with-slash<
  "Matches a namespace-qualified keyword ending with a slash, like `::a//`."
  [pre-slash]
  (h/for [_ <peek-ns-separator>
          prefix (>fetch-referred-namespace< pre-slash)
          suffix <symbol-suffix>]
    [prefix suffix]))

(h/defmaker >ns-qualified-keyword-empty-end<
  "Matches emptiness, and gives, as a product, a vector pair of
  the current namespace name (from the context) and whatever
  `pre-slash` is."
  [pre-slash]
  (h/for [context h/<fetch-context>]
    [(:ns-name context) pre-slash]))

(h/defmaker >ns-resolved-keyword-end<
  "Matches the two possible endings to a namespace-resolved keyword
  (something starting with a slash or nothing). Given the `pre-slash`,
  its product is a vector pair of the resolved namespace's name
  along with the name proper to the keyword."
  [pre-slash]
  (h/+ (>ns-qualified-keyword-end-with-slash< pre-slash)
       (>ns-qualified-keyword-empty-end< pre-slash)))

(h/defrule <ns-resolved-keyword>
  "Matches a namespace-resolved keyword, i.e. a keyword with two colons.
  If there is a slash, what comes before the slash is a namespace-alias
  that must be in the context."
  (h/for [_ (h/lex (h/factor= 2 <keyword-indicator>))
          pre-slash <symbol-char-series>
          [prefix suffix] (>ns-resolved-keyword-end< pre-slash)
          _ <form-end>]
    (keyword prefix suffix)))

(h/defrule <keyword>
  "Any keyword. No whitespace padding."
  (h/label "a keyword"
    (h/+ <ns-resolved-keyword> <normal-keyword>)))

;; Numbers.

(h/defmaker >radix-natural-number<
  "Matches a single natural number whose allowed digits (which are
  alphanumeric) are determined by the `core`, a positive integer.
  Its product is the integer represented."
  [core]
  (h/hooked-rep #(+ (* core %1) %2) 0 (h/radix-digit core)))

(h/defrule <decimal-natural-number>
  "A series of decimal digits; the product is the corresponding integer."
  (>radix-natural-number< 10))

(h/defrule <number-sign>
  "A number sign, positive or negative. Its product can be `+1` or `-1`."
  (h/template-sum [label token product]
    (h/label label (h/chook product (h/lit token)))
    "positive sign" \+ 1, "negative sign" \- -1))

(h/defrule <empty-number-tail>
  "An empty number tail. Returns the `identity` function."
  (h/chook identity h/<emptiness>))

(h/defrule <imprecise-fractional-part>
  "A '.' followed by an optional series of digits:
  a fractional part of a number.
  Its product is a function that takes a number and
  adds the number indicated by the series of digits to it."
  (letfn [(reduce-digit-accumulator [[prev-num multiplier] next-digit]
            [(+ (* next-digit multiplier) prev-num) (/ multiplier 10)])]
    (h/prefix
      (h/lit \.)
      (h/+ (->> h/<decimal-digit>
             (h/hooked-rep reduce-digit-accumulator [0 0.1])
             (h/hook #(partial + (get % 0))))
           (h/hook #(partial + (/ % 10.)) <decimal-natural-number>)
           <empty-number-tail>))))

(h/defrule <exponential-part>
  "An 'e' followed by a series of digits: the exponential part.
  Its product is a function that takes a number
  and raises it to whatever power indicated by the series of digits."
  (h/prefix
    (h/case-insensitive-lit \e)
    (h/hook #(partial * (expt-int 10 %)) <decimal-natural-number>)))

(h/defrule <fractional-exponential-part>
  "A fractional part followed by an optional exponential part.
  Its product is the functional composition of the two parts' products."
  (h/for [frac-fn <imprecise-fractional-part>
          exp-fn (h/+ <exponential-part> <empty-number-tail>)]
    (comp exp-fn frac-fn)))

(h/defrule <imprecise-number-tail>
  "The tail of an imprecise number: that is, a number
  that has a '.', 'e', or 'M'. Its product is a function that
  transforms an integer according to the tail and also
  turns it to a `double` (or a `BigDecimal` if it has an 'M')."
  (h/for [tail-fn (h/+ <fractional-exponential-part> <exponential-part>)
          big-dec? (h/opt (h/lit \M))]
    (comp (if big-dec? bigdec double) tail-fn)))

(h/defrule <fraction-denominator-tail>
  "The tail of a ratio number, i.e. a '/' followed by a denominator.
  The denominator cannot be zero. Its product is a function that
  takes an integer and divides it by the denominator."
  ; Product: a unary function on an integer.
  (h/prefix
    (h/lit \/)
    (h/hook (fn [denominator] #(/ % denominator))
      (h/antivalidate zero? "a fraction's denominator cannot be zero"
        <decimal-natural-number>))))

(h/defmaker >radix-coefficient-tail<
  "The tail of a radixed number. An integer prefixed with
  a series of digits (the radix) and an 'r' can be suffixed
  by a series of alphanumeric digits (the number's value);
  which alphanumeric digits are allowed is determined by the radix.
  
  The `core` argument is the value of the radix. It is
  required because it determines on the syntactic level
  what digits are allowed.
  The product is a function that constantly returns
  the number represented."
  [core]
  (h/hook constantly
    (h/prefix
      (h/case-insensitive-lit \r)
      (>radix-natural-number< core))))

(h/defmaker >number-tail<
  "The tail of a number. Its product is a function that takes
  the integer given by the number's core (the digits before
  any special character like '.' or 'r'), and returns a new
  number: the number represented by the core and tail together.
  
  This is a rule-maker that takes the `core` integer. This
  is necessary only because if the tail is a radix tail, then
  the core is needed at the syntactic level to determine what
  digits are allowed."
  [core]
  (h/+ <imprecise-number-tail> <fraction-denominator-tail>
       (>radix-coefficient-tail< core) <empty-number-tail>))

(h/defrule <number>
  "Any Clojure number. Its product is a `Number`."
  (h/for "a number"
    [sign (h/opt <number-sign>)
     prefix-number <decimal-natural-number>
     tail-fn (>number-tail< prefix-number)
     _ <form-end>]
    (tail-fn (* (or sign 1) prefix-number))))

;; Unicode escape sequences for chars and strings.

(h/defrule <unicode-escape-sequence>
  "A Unicode escape sequence: 'u' followed by four
  hexadecimal digits. Its product is the corresponding `Character`."
  (h/prefix (h/lit \u)
    (h/hook (comp char reduce-hexadecimal-digits)
      (h/factor= 4 h/<hexadecimal-digit>))))

;; Characters.

(h/defrule <character-indicator> (h/lit \\))

(h/defrule <character-name>
  "The Clojure name of a `Character`, like 'newline' or 'u12A3'.
  Uses `clojure.core/char-name-string` for special names. Also
  accepts Unicode espace sequences.
  Its product is the corresponding character."
  (h/+ (h/mapsum #(h/chook (key %) (h/phrase (val %))) char-name-string)
       <unicode-escape-sequence>))

(h/defrule <character> (h/prefix <character-indicator> <character-name>))

;; Strings.

(h/defrule <string-delimiter> (h/lit \"))

(h/defrule <escaped-char>
  "A String escaped character. Its product is the corresponding `Character`."
  (h/prefix <character-indicator>
    (h/label "a valid escape sequence"
      (h/+ (h/template-sum [token character]
             (h/chook character (h/lit token))
             \t \tab, \n \newline, \\ \\, \" \")
           <unicode-escape-sequence>))))

(h/defrule <normal-string-char> (h/antilit \"))

(h/defrule <string-char> (h/+ <escaped-char> <normal-string-char>))

(h/defrule <string>
  (h/hook #(->> % flatten str*)
    (h/circumfix <string-delimiter> (h/rep* <string-char>) <string-delimiter>)))

;; Circumflex compound forms: lists, vectors, maps, and sets.

(h/defmaker >form-series<
  "A series of forms, separated by whitespace or indicators.
  Takes an optional `fn-sym` argument. `fn-sym` must be `nil`
  if there is no surrounding anonymous function. `fn-sym`
  otherwise is the symbol of the surrounding anonymous function.
  Its product is a collection of the forms, with the metadata
  of the collection the combination of the forms' metadata (see
  `merge-form-meta`)."
  [fn-sym]
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

(h/defmaker >padded-lit<
  "Makes a literal from the given `token` suffixed with optional whitespace."
  [token]
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

(h/defrule <tag> "A metadata tag."
  (h/hook #(hash-map :tag %)
    (h/+ <keyword> <symbol>)))

(h/defmaker >metadata< "A metadata tag or map." [fn-sym]
  (h/+ (>map< fn-sym) <tag>))

(h/defmaker >with-meta< "Example: `^{:a 3} x`." [fn-sym]
  (h/prefix (>padded-lit< \^)
    (h/for [metadata (>metadata< fn-sym), _ <ws?>, content (>form< fn-sym)]
      (list `with-meta content metadata))))

;; Anonymous functions.

(h/defrule <anonymous-fn-parameter-suffix>
  "The optional suffix of an anonymous function parameter.
  The product is an integer or `\\&`."
  (h/+ (h/antivalidate zero?
         "anonymous function parameters cannot be suffixed with zero"
         <decimal-natural-number>)
       (h/lit \&)
       (h/chook 1 h/<emptiness>)))

(h/defmaker >anonymous-fn-parameter<
  "Examples: '%', '%3', '%&'. Fails if `fn-sym` is `nil`, which is
  tantamount to the absence of any surrounding anonymous function.
  Its product is the symbol determined by `fn-sym` and the
  parameter's suffix, with metadata expressing its presence."
  [fn-sym]
  (h/for "an anonymous function parameter"
    [prefix (h/lit \%)
     _ (h/demand fn-sym
         "parameter literals must be inside an anonymous function")
     suffix <anonymous-fn-parameter-suffix>]
    (with-meta (parameter-symbol fn-sym suffix)
      (cond
        (integer? suffix) {:anonymous-fn-parameter-n suffix}
        (= \& suffix) {:anonymous-fn-slurping-parameter? true}))))

(h/defmaker >anonymous-fn-inner<
  "Example: '#(+ % (- %& 3))'. Fails if `surrounding-fn-sym` is
  *not* nil. Its product is the list of the function's code."
  [surrounding-fn-sym]
  (h/for [_ (h/lit \()
          _ (h/demand (nil? surrounding-fn-sym)
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

(h/defrule <pattern-inner>
  "A regular expression `Pattern`."
  (h/hook (comp re-pattern str*)
    (h/circumfix <string-delimiter>
                 (h/rep* <normal-string-char>)
                 <string-delimiter>)))

(h/defmaker >evaluated-inner< [fn-sym]
  (h/for [_ (h/lit \=)
          context h/<fetch-context>
          _ (h/demand (:reader-eval? context)
              "EvalReader forms (i.e. #=(...)) have been prohibited.")
          content (>list< fn-sym)]
    (eval content)))

(h/defrule <unreadable-inner>
  "Example: `#<unreadable>`. Never succeeds."
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

(h/defmaker >dispatched<
  "Any form that starts with '#', like `#(%)` and `#{a b c}`,
  except the '#_', which counts as whitespace."
  [fn-sym]
  (h/prefix (h/lit \#) (>dispatched-inner< fn-sym)))

(h/defmaker >form-content<
  "Any form's content (without any preceding whitespace)."
  [fn-sym]
  (h/+ (>list< fn-sym) (>vector< fn-sym) (>map< fn-sym) (>dispatched< fn-sym)
       <string> (>syntax-quoted< fn-sym)
       (>unquote-spliced< fn-sym) (>unquoted< fn-sym) (>with-meta< fn-sym) <character> <keyword>
       (>anonymous-fn-parameter< fn-sym) <symbol> <number>))

(h/defmaker >form<
  "Any form, with optional preceding whitespace."
  [fn-sym]
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
