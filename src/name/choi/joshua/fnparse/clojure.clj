(ns name.choi.joshua.fnparse.clojure
  (:require [name.choi.joshua.fnparse.hound :as r]
            [clojure.template :as t] [clojure.set :as set]
            [clojure.contrib.seq :as seq]
            name.choi.joshua.fnparse.hound.test)
  (:use [clojure.test :only #{deftest is run-tests}])
  (:import [clojure.lang IPersistentMap]))

; TODO
; Unicode character codes.
; Keyword-specific restrictions.
; #=, #< reader macros

(defn prefix-list-fn [prefix-rule]
  (fn [product] (list prefix-rule product)))

(defn str* [chars]
  (apply str chars))

(defn expt-int [base pow]
  (loop [n pow, y 1, z base]
    (let [t (bit-and n 1), n (bit-shift-right n 1)]
      (cond
        (zero? t) (recur n y (* z z))
        (zero? n) (* z y)
        :else (recur n (* z y) (* z z))))))

(defn reduce-hexadecimal-digits [digits]
  (reduce #(+ (* 16 %1) %2) digits))

(deftype ClojureContext [ns-name ns-aliases anonymous-fn-context]
  IPersistentMap)

(deftype AnonymousFnContext [normal-parameters slurping-parameter]
  IPersistentMap)

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

(declare _form)

(def _comment-indicator (r/+ (r/lit \;) (r/lex (r/phrase "#!"))))

(def _comment-char (r/antilit \newline))

(def _comment (r/cat _comment-indicator (r/rep* _comment-char)))

(def _discarded (r/prefix (r/lex (r/phrase "#_")) #'_form))

(def _normal-ws-char
  (r/term "a whitespace character" ws-set))

(def _ws
  (r/label "whitespace"
    (r/rep+ (r/+ _normal-ws-char _comment _discarded))))

(def _opt-ws (r/opt _ws))

(def _keyword-indicator (r/lit \:))

(def _indicator (r/term "an indicator" indicator-set))

(def _separator (r/+ _ws _indicator))

(def _form-end (r/+ (r/followed-by _separator) r/_end-of-input))

(def _ns-separator (r/lit \/))

(def _non-alphanumeric-symbol-char
  (r/set-lit "a non-alphanumeric symbol character" "*+!_-?."))

(def _symbol-first-char
  (r/+ r/_ascii-letter _non-alphanumeric-symbol-char))

(def _symbol-char
  (r/label "a symbol character"
    (r/+ _symbol-first-char r/_decimal-digit)))

(def _symbol-char-series
  (r/hook str* (r/rep+ _symbol-char)))

(def _symbol-end
  (r/annotate-error annotate-symbol-end _form-end))

(def _slash-symbol-suffix
  (r/chook "/" _ns-separator))

(def _symbol-suffix
  (r/prefix _ns-separator (r/+ _symbol-char-series _slash-symbol-suffix)))

(def _symbol
  (r/for "a symbol"
    [first-char _symbol-first-char
     rest-pre-slash (r/opt _symbol-char-series)
     post-slash (r/opt _symbol-suffix)
     _ _symbol-end]
    (let [pre-slash (str first-char rest-pre-slash)]
      (if post-slash
        (symbol pre-slash post-slash)
        (or (peculiar-symbols pre-slash) ; In case it's true, false, or nil
            (symbol pre-slash))))))

(def _normal-keyword
  (r/for [_ _keyword-indicator
          pre-slash (r/opt _symbol-char-series)
          post-slash (r/opt _symbol-suffix)
          _ _symbol-end]
    (if post-slash
      (keyword pre-slash post-slash)
      (keyword pre-slash))))

(def _followed-by-ns-separator (r/followed-by _ns-separator))

(r/defn fetch-referred-namespace [context namespace-alias]
  (r/only-when (get-in context [:ns-aliases namespace-alias])
    (format "no namespace with alias '%s'" namespace-alias)))

(r/defn ns-qualified-keyword-end-with-slash [pre-slash]
  (r/for [_ _followed-by-ns-separator
          context r/_fetch-context
          prefix (fetch-referred-namespace context pre-slash)
          suffix _symbol-suffix]
    [prefix suffix]))

(r/defn ns-qualified-keyword-empty-end [pre-slash]
  (r/for [context r/_fetch-context]
    [(:ns-name context) pre-slash]))

(r/defn ns-resolved-keyword-end [pre-slash]
  (r/+ (ns-qualified-keyword-end-with-slash pre-slash)
       (ns-qualified-keyword-empty-end pre-slash)))

(def _ns-resolved-keyword
  (r/for [_ (r/lex (r/factor= 2 _keyword-indicator))
          pre-slash _symbol-char-series
          [prefix suffix] (ns-resolved-keyword-end pre-slash)
          _ _form-end]
    (keyword prefix suffix)))

(def _keyword
  (r/label "a keyword"
    (r/+ _ns-resolved-keyword _normal-keyword)))

(r/defn radix-natural-number [base]
  (r/cascading-rep+ (r/radix-digit (if (<= base 36) base 36))
    identity #(+ (* base %1) %2)))

(def _decimal-natural-number
  (radix-natural-number 10))

(def _number-sign
  (r/template-sum [label token product]
    (r/label label (r/chook product (r/lit token)))
    "positive sign" \+ 1, "negative sign" \- -1))

(def _empty-number-tail
  (r/chook identity r/_emptiness))

(def _imprecise-fractional-part
  (r/prefix
    (r/lit \.)
    (r/+ (r/hook #(partial + %)
           (r/cascading-rep+ r/_decimal-digit #(/ % 10) #(/ (+ %1 %2) 10)))
         _empty-number-tail)))

(def _exponential-part
  (r/prefix
    (r/set-lit "exponent indicator" "eE")
      ; If I wasn't worrying about pure Clojure,
      ; use (r/case-insensitive-lit \e) above instead.
    (r/hook #(partial * (expt-int 10 %)) _decimal-natural-number)))

(def _fractional-exponential-part
  (r/for [frac-fn _imprecise-fractional-part
          exp-fn (r/+ _exponential-part _empty-number-tail)]
    (comp exp-fn frac-fn)))

(def _imprecise-number-tail
  (r/for [tail-fn (r/+ _fractional-exponential-part _exponential-part)
          big-dec? (r/opt (r/lit \M))]
    (comp (if big-dec? bigdec double) tail-fn)))

(def _fraction-denominator-tail
  (r/prefix (r/lit \/)
    (r/hook (fn [denominator] #(/ % denominator))
      (r/anti-validate _decimal-natural-number zero?
        "a fraction's denominator cannot be zero"))))

(r/defn radix-coefficient-tail [base]
  (r/hook constantly
    (r/prefix
      (r/set-lit "radix indicator" "rR")
        ; If I wasn't worrying about pure Clojure,
        ; use (case-insensitive-r/lit \r) above instead.
      (radix-natural-number base))))

(r/defn number-tail [base]
  (r/+ _imprecise-number-tail _fraction-denominator-tail
       (radix-coefficient-tail base) _empty-number-tail))

(def _number
  (r/for "a number"
    [sign (r/opt _number-sign)
     prefix-number _decimal-natural-number
     tail-fn (number-tail prefix-number)
     _ _form-end]
    (tail-fn (* (or sign 1) prefix-number))))

(def _string-delimiter (r/lit \"))

(def _unicode-escape-sequence
  (r/prefix (r/lit \u)
    (r/hook (comp char reduce-hexadecimal-digits)
      (r/factor= 4 r/_hexadecimal-digit))))

(def _character-name
  (r/+ (r/mapsum #(r/chook (key %) (r/phrase (val %))) char-name-string)
       _unicode-escape-sequence))

(def _character (r/prefix (r/lit \\) _character-name))

(def _escaped-char
  (r/prefix (r/lit \\)
    (r/label "a valid escape sequence"
      (r/+ (r/template-sum [token character]
             (r/chook character (r/lit token))
             \t \tab, \n \newline, \\ \\, \" \")
           _unicode-escape-sequence))))

(def _string-char (r/+ _escaped-char (r/antilit \")))

(def _string
  (r/hook #(->> % seq/flatten str*)
    (r/circumfix _string-delimiter (r/rep* _string-char) _string-delimiter)))

(def _form-series (r/suffix (r/rep* #'_form) _opt-ws))

(t/do-template [_rule start-token end-token product-fn]
  (def _rule
    (r/for [_ (r/lit start-token)
            contents (r/opt _form-series)
            _ (r/lit end-token)]
      (product-fn contents)))
  _list \( \) #(apply list %)
  _vector \[ \] vec
  _map \{ \} #(apply hash-map %)
  _set-inner \{ \} set)

(r/defn padded-lit [token]
  (r/prefix (r/lit token) _opt-ws))

(t/do-template [_rule prefix product-fn-symbol]
  (def _rule
    (r/hook (prefix-list-fn product-fn-symbol)
      (r/prefix (r/cat (padded-lit prefix) _opt-ws) #'_form)))
  _quoted \' `quote
  _syntax-quoted \` `syntax-quote
  _unquoted \~ `unquote
  _derefed \@ `deref
  _var-inner \' `var
  _deprecated-meta \^ `meta)

(def _unquote-spliced
  (r/hook (prefix-list-fn `unquote-splicing)
    (r/prefix (r/cat (r/lex (r/phrase "~@")) _opt-ws) #'_form)))

(def _deprecated-meta
  (r/suffix _deprecated-meta
    (r/effects println
      "WARNING: The ^ indicator is deprecated (since Clojure 1.1).")))

(def _fn-inner
  (r/hook (prefix-list-fn `mini-fn)
    (r/circumfix (r/lit \() _form-series (r/lit \)))))

(def _tag
  (r/hook #(hash-map :tag %)
    (r/+ _keyword _symbol)))

(def _metadata
  (r/+ _map _tag))

(def _with-meta-inner
  (r/prefix (padded-lit \^)
    (r/for [metadata _metadata, _ _opt-ws, content #'_form]
      (list `with-meta content metadata))))

(def _anonymous-fn-parameter-suffix
  (r/+ _decimal-natural-number (r/lit \&) (r/chook 1 r/_emptiness)))

(def _anonymous-fn-parameter
  (r/for "a parameter"
    [_ (r/lit \%)
     context r/_fetch-context
     :let [fn-context (:anonymous-fn-context context)]
     _ (r/only-when fn-context
         "a parameter literals must be inside an anonymous function")
     suffix _anonymous-fn-parameter-suffix
     :let [already-existing-symbol (get-already-existing-symbol fn-context
                                                                suffix)
           parameter-symbol (or already-existing-symbol (gensym "parameter"))]
     _ (if (nil? already-existing-symbol)
         (r/alter-context update-fn-context suffix parameter-symbol)
         r/_emptiness)]
    parameter-symbol))

(def _anonymous-fn
  (r/for "an anonymous function"
    [_ (r/lit \()
     pre-context r/_fetch-context
     _ (r/only-when (not (:anonymous-fn-context pre-context))
         "nested anonymous functions are not allowed")
     _ (r/alter-context assoc :anonymous-fn-context (AnonymousFnContext [] nil))
     content _form-series
     post-context r/_fetch-context
     _ (r/alter-context assoc :anonymous-fn-context nil)
     _ (r/lit \))]
    (let [anonymous-fn-context (:anonymous-fn-context post-context)
          parameters (make-parameter-vector anonymous-fn-context)]
      (list `fn 'anonymous-fn parameters content))))

(def _dispatched-inner
  (r/+ _anonymous-fn _set-inner _fn-inner _var-inner _with-meta-inner))

(def _dispatched
  (r/prefix (r/lit \#) _dispatched-inner))

(def _form-content
  (r/+ _list _vector _map _dispatched _string _syntax-quoted
       _unquote-spliced _unquoted _deprecated-meta _character _keyword
       _anonymous-fn-parameter _symbol _number))

(def _form
  (r/label "a form" (r/prefix _opt-ws _form-content)))

(deftest various-rules
  (is (match? _form "55.2e2" :product? #(== % 5520.)))
  (is (match? _form "16rFF" :product? #(== % 255)))
  (is (match? _form "16." :product? #(== % 16.)))
  (is (match? _form "true" :product? true?))
  (is (= (with-out-str (r/parse _form "^()" {} list list))
         "WARNING: The ^ indicator is deprecated (since Clojure 1.1).\n"))
  (is (match? _form "[()]" :product? #(= % [()])))
  (is (match? _form "\"\\na\\u3333\"" :product? #(= % "\na\u3333")))
  (is (non-match? _form "([1 32]"
        :position 7
        :labels #{"a form" "')'" "whitespace"}))
  (is (non-match? _form "a/b/c"
        :position 3
        :messages #{"multiple slashes aren't allowed in symbols"}
        :labels #{"an indicator" "the end of input"
                  "a symbol character" "whitespace"}))
  (is (match? _form ":a/b" :product? #(= % :a/b)))
  (is (match? _form "::b"
        :context (ClojureContext "user" nil nil)
        :product? #(= % :user/b)))
  (is (non-match? _form "::z/abc"
        :position 3
        :messages #{"no namespace with alias 'z'"}
        :labels #{"the end of input" "a symbol character" "an indicator"
                  "whitespace"}))
  (is (match? _form "+" :product? #(= % '+)))
  (is (match? _form "clojure.core//" :product? #(= % 'clojure.core//)))
  (is (match? _form "#!/usr/bin/clojure\n\"a\\n\"" :product? #(= % "a\n")))
  (is (match? _form "[~@a ()]"
        :product? #(= % [(list 'clojure.core/unquote-splicing 'a) ()])))
  (is (match? _form "[#(%) #(apply + % %2 %2 %&)]"
        :context (ClojureContext "user" nil nil)
        :product? #(= ((eval (second %)) 3 2 8 1) 16)))
  (is (non-match? _form "17rAZ"
        :position 4
        :labels #{"a base-17 digit" "an indicator" "whitespace"
                  "the end of input"}))
  (is (non-match? _form "#(% #(%))"
        :position 6
        :context (ClojureContext "user" nil nil)
        :messages #{"nested anonymous functions are not allowed"}))
  (is (non-match? _form "3/0 3"
        :position 3
        :labels #{"a base-10 digit"}
        :messages #{"a fraction's denominator cannot be zero"})))

(run-tests)
