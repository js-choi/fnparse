(ns edu.arizona.fnparse.clojure-pure
  "This is a proof-of-concept Clojure parser implemented in *pure Clojure*.
  It, and all functions it uses in its referred libraries, except
  `clojure.core`, use *no* direct Java calls (with the exception
  of the Exception thrown in the final read-string function.)"
  (:require [edu.arizona.fnparse.hound :as p] [edu.arizona.fnparse :as c]
            [clojure [template :as t] [set :as set]]
            [clojure.contrib.seq :as seq]
            [clojure.contrib.except :as except]
            edu.arizona.fnparse.hound.test)
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

;;; HELPER RULES AND RULE-MAKERS
; These are reimplementations of rules and rule-makers that are already
; in `edu.arizona.fnparse.hound`, but have been rewritten to
; use pure Clojure only.

(def ascii-digits "0123456789")
(def lowercase-ascii-alphabet "abcdefghijklmnopqrstuvwxyz")
(def uppercase-ascii-alphabet
  (map #(Character/toUpperCase (char %)) lowercase-ascii-alphabet))
(def base-36-digits (concat ascii-digits lowercase-ascii-alphabet))
(def base-36-digit-map
  (letfn [(digit-entries [[index digit-char]]
            (let [digit-char (char digit-char)]
              [[(Character/toUpperCase digit-char) index]
               [(Character/toLowerCase digit-char) index]]))]
    (->> base-36-digits seq/indexed (mapcat digit-entries) (into {}))))

(defn radix-label
  "The function used by radix-digit to smartly
  create digit labels for the given `base`."
  [base]
  (case base
    10 "a decimal digit"
    16 "a hexadecimal digit"
    8 "an octal digit"
    2 "a binary digit"
    (format "a base-%s digit" base)))

(p/defmaker radix-digit
  "Returns a rule that accepts one digit character
  token in the number system with the given `base`.
  For instance, `(radix-digit 12)` is a rule
  of a single duodecimal digit.
  
  Digits past 9 are case-insensitive letters:
  11, for instance, is \\b or \\B. Bases above
  36 are accepted, but there's no way to use
  digits beyond \\Z (which corresponds to 36).
  
  The rules `<decimal-digit>` and
  `<hexadecimal-digit>` are already provided."
  {:succeeds "If the next token is a digit
    character in the given `base`'s number
    system."
   :product "The digit's corresponding integer."
   :consumes "One character."}
  [base]
  {:pre #{(integer? base) (> base 0)}}
  (->> base-36-digit-map (filter #(< (val %) base)) (into {})
    (p/term* (radix-label base))))

(p/defrule <decimal-digit>
  "A rule matching a single base-10 digit
  character token (i.e. \\0 through \\9)."
  {:product "The matching digit's corresponding Integer object, 0 through 9."
   :consumes "One character."}
  (radix-digit 10))

(p/defrule <hexadecimal-digit>
  "A rule matching a single base-16 digit
  character token (i.e. \\0 through \\F)."
  {:product "The matching digit's corresponding Integer object, 0 through 15."
   :consumes "One character."}
  (radix-digit 16))

(p/defrule <uppercase-ascii-letter>
  "A rule matching a single uppercase ASCII letter."
  {:product "The matching character itself."
   :consumes "One character."}
  (p/set-term "an uppercase ASCII letter" uppercase-ascii-alphabet))

(p/defrule <lowercase-ascii-letter>
  "A rule matching a single lowercase ASCII letter."
  {:product "The matching character itself."
   :consumes "One character."}
  (p/set-term "a lowercase ASCII letter" lowercase-ascii-alphabet))

(p/defrule <ascii-letter>
  "A rule matching a single uppercase or lowercase ASCII letter."
  {:product "The matching character itself."
   :consumes "One character."}
  (p/label "an ASCII letter"
    (p/+ <uppercase-ascii-letter> <lowercase-ascii-letter>)))

(p/defrule <ascii-digit>
  "A rule matching a single ASCII numeric digit. You may
  want to use instead `decimal-digit`, which automatically
  converts digits to Integer objects."
  {:product "The matching character itself."
   :consumes "One character."}
  (p/set-term "an ASCII digit" ascii-digits))

(p/defrule <ascii-alphanumeric>
  "A rule matching a single alphanumeric ASCII letter."
  {:product "The matching character itself."
   :consumes "One character."}
  (p/label "an alphanumeric ASCII character"
    (p/+ <ascii-letter> <ascii-digit>)))

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
  (p/+ <ascii-letter> <non-alphanumeric-symbol-char>))

(def <symbol-char>
  (p/label "a symbol character"
    (p/+ <symbol-first-char> <decimal-digit>)))

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

(p/defmaker fetch-referred-namespace [context namespace-alias]
  (p/only-when (get-in context [:ns-aliases namespace-alias])
    (format "no namespace with alias '%s'" namespace-alias)))

(p/defmaker ns-qualified-keyword-end-with-slash [pre-slash]
  (p/for [_ <peek-ns-separator>
          context p/<fetch-context>
          prefix (fetch-referred-namespace context pre-slash)
          suffix <symbol-suffix>]
    [prefix suffix]))

(p/defmaker ns-qualified-keyword-empty-end [pre-slash]
  (p/for [context p/<fetch-context>]
    [(:ns-name context) pre-slash]))

(p/defmaker ns-resolved-keyword-end [pre-slash]
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

(p/defmaker radix-natural-number [base]
  (p/hooked-rep #(+ (* base %1) %2) 0 (p/radix-digit base)))

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
      (p/+ (->> <decimal-digit>
             (p/hooked-rep reduce-digit-accumulator [0 0.1])
             (p/hook #(partial + (get % 0))))
           (p/hook #(partial + (/ % 10.)) <decimal-natural-number>)
           <empty-number-tail>))))

(def <exponential-part>
  (p/prefix
    (p/set-term "exponent indicator" "eE")
      ; If I wasn't worrying about pure Clojure,
      ; use (p/case-insensitive-lit \e) above instead.
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

(p/defmaker radix-coefficient-tail [base]
  (p/hook constantly
    (p/prefix
      (p/set-term "radix indicator" "rR")
        ; If I wasn't worrying about pure Clojure,
        ; use (case-insensitive-p/lit \r) above instead.
      (radix-natural-number base))))

(p/defmaker number-tail [base]
  (p/+ <imprecise-number-tail> <fraction-denominator-tail>
       (radix-coefficient-tail base) <empty-number-tail>))

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
      (p/factor= 4 <hexadecimal-digit>))))

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

(p/defmaker padded-lit [token]
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
