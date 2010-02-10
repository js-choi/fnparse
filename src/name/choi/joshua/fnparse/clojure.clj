(ns name.choi.joshua.fnparse.clojure
  (:require [name.choi.joshua.fnparse.hound :as p]
            [clojure.template :as template] [clojure.set :as set]
            [clojure.test :as test] [clojure.contrib.seq-utils :as seq]
            name.choi.joshua.fnparse.hound.test)
  (:use [clojure.test :only #{deftest is run-tests}])
  (:refer-clojure :exclude #{for})
  (:import [clojure.lang IPersistentMap]))

; TODO
; How does Clojure's reader figure out namespaces and namespace aliases?
; Unicode character codes.
; Keyword-specific restrictions.
; Anonymous functions.

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

(deftype ClojureContext [ns-name ns-aliases] IPersistentMap)

(def peculiar-symbols {"nil" nil, "true" true, "false" false})

(def ws-set (set " ,\t\n"))

(def indicator-set (set ";()[]{}\\\"'@^`#"))

;;; RULES START HERE.

(declare form)

(def comment-form (p/cat (p/lit \;) (p/rep* (p/antilit \newline))))

(def discarded-form (p/prefix (p/lex (p/mapcat "#_")) #'form))

(def ws
  (p/label "whitespace"
    (p/rep+ (p/+ (p/term "a whitespace character" ws-set)
               comment-form discarded-form))))

(def opt-ws (p/opt ws))

(def indicator (p/term "an indicator" indicator-set))

(def separator (p/+ ws indicator))

(def form-end (p/+ (p/followed-by separator) p/end-of-input))

(def ns-separator (p/lit \/))

(def non-alphanumeric-symbol-char
  (p/set-lit "a non-alphanumeric symbol character" "*+!-_?."))

(def symbol-char
  (p/label "a symbol character"
    (p/+ p/ascii-alphanumeric non-alphanumeric-symbol-char)))

(def symbol-char-series
  (p/hook str* (p/rep+ symbol-char)))

(def symbol-end
  (p/annotate-error form-end
    (fn [error]
      (if (= (:unexpected-token error) \/)
        "multiple slashes aren't allowed in symbols"))))

(def symbol-suffix
  (p/prefix ns-separator
    (p/+ symbol-char-series (p/chook "/" ns-separator))))

(def symbol-form
  (p/label "symbol"
    (p/for [first-char p/ascii-letter
              rest-pre-slash (p/opt symbol-char-series)
              post-slash (p/opt symbol-suffix)
              _ symbol-end]
      (let [pre-slash (str first-char rest-pre-slash)]
        (if post-slash
          (symbol pre-slash post-slash)
          (or (peculiar-symbols pre-slash) ; In case it's true, false, or nil
              (symbol pre-slash)))))))

(def keyword-indicator (p/lit \:))

(def normal-keyword
  (p/for [_ keyword-indicator
            pre-slash (p/opt symbol-char-series)
            post-slash (p/opt symbol-suffix)
            _ symbol-end]
    (if post-slash
      (keyword pre-slash post-slash)
      (keyword pre-slash))))

(p/defrm ns-resolved-keyword-end [pre-slash]
  (p/+ (p/for [_ (p/followed-by ns-separator)
                 context p/get-context
                 prefix (p/only-when (get-in context [:ns-aliases pre-slash])
                          (format "no namespace with alias '%s'" pre-slash))
                 suffix symbol-suffix]
         [prefix suffix])
       (p/for [context p/get-context]
         [(:ns-name context) pre-slash])))

(def ns-resolved-keyword
  (p/for [_ (p/lex (p/factor= 2 keyword-indicator))
            pre-slash symbol-char-series
            [prefix suffix] (ns-resolved-keyword-end pre-slash)
            _ form-end]
    (keyword prefix suffix)))

(def keyword-form
  (p/label "keyword" (p/+ ns-resolved-keyword normal-keyword)))

(p/defrm radix-natural-number [base]
  (p/cascading-rep+ (p/radix-digit (if (<= base 36) base 36))
    identity #(+ (* base %1) %2)))

(def decimal-natural-number
  (radix-natural-number 10))

(def number-sign
  (p/template-alt [label token product]
    (p/label label (p/chook product (p/lit token)))
    "positive sign" \+ 1, "negative sign" \- -1))

(def no-number-tail
  (p/chook identity p/emptiness))

(def imprecise-fractional-part
  (p/prefix (p/lit \.)
    (p/+ (p/hook #(partial + %)
           (p/cascading-rep+ p/decimal-digit #(/ % 10) #(/ (+ %1 %2) 10)))
         no-number-tail)))

(def exponential-part
  (p/prefix
    (p/set-lit "exponent indicator" "eE")
      ; If I wasn't worrying about pure Clojure,
      ; use (case-insensitive-p/lit \e) above instead.
    (p/hook #(partial * (expt-int 10 %)) decimal-natural-number)))

(def fractional-exponential-part
  (p/for [frac-fn imprecise-fractional-part
            exp-fn (p/+ exponential-part no-number-tail)]
    (comp exp-fn frac-fn)))

(def imprecise-number-tail
  (p/for [tail-fn (p/+ fractional-exponential-part exponential-part)
            big-dec? (p/opt (p/lit \M))]
    (comp (if big-dec? bigdec double) tail-fn)))

(def fraction-denominator-tail
  (p/prefix (p/lit \/)
    (p/hook (fn [denominator] #(/ % denominator))
      (p/anti-validate decimal-natural-number zero?
        "a fraction's denominator cannot be zero"))))

(p/defrm radix-coefficient-tail [base]
  (p/hook constantly
    (p/prefix
      (p/set-lit "radix indicator" "rR")
        ; If I wasn't worrying about pure Clojure,
        ; use (case-insensitive-p/lit \r) above instead.
      (radix-natural-number base))))

(p/defrm number-tail [base]
  (p/+ imprecise-number-tail fraction-denominator-tail
       (radix-coefficient-tail base) no-number-tail))

(def number
  (p/for [sign (p/opt number-sign)
            prefix-number decimal-natural-number
            tail-fn (number-tail prefix-number)
            _ form-end]
    (tail-fn (* (or sign 1) prefix-number))))

(def string-delimiter (p/lit \"))

(def unicode-escape-sequence
  (p/prefix (p/lit \u)
    (p/hook (comp char reduce-hexadecimal-digits)
      (p/factor= 4 p/hexadecimal-digit))))

(def character-name
  (p/+ (p/mapalt #(p/chook (key %) (p/mapcat (val %))) char-name-string)
       unicode-escape-sequence))

(def character (p/prefix (p/lit \\) character-name))

(def escaped-char
  (p/prefix (p/lit \\)
    (p/label "a valid escape sequence"
      (p/+ (p/template-alt [token character]
             (p/chook character (p/lit token))
             \t \tab, \n \newline, \\ \\, \" \")
           unicode-escape-sequence))))

(def string-char (p/+ escaped-char (p/antilit \")))

(def string
  (p/hook #(->> % seq/flatten (apply str))
    (p/circumfix string-delimiter (p/rep* string-char) string-delimiter)))

(def form-series (p/suffix (p/rep* #'form) opt-ws))

(template/do-template [rule-name start-token end-token product-fn]
  (def rule-name
    (p/for [_ (p/lit start-token)
              contents (p/opt form-series)
              _ (p/lit end-token)]
      (product-fn contents)))
  list-form \( \) #(apply list %)
  vector-form \[ \] vec
  map-form \{ \} #(apply hash-map %)
  set-inner-r \{ \} set)

(p/defrm padded-lit [token]
  (p/prefix (p/lit token) opt-ws))

(template/do-template [rule-name prefix product-fn-symbol prefix-is-rule?]
  (def rule-name
    (p/hook (prefix-list-fn product-fn-symbol)
      (p/prefix (p/cat ((if prefix-is-rule? identity padded-lit) prefix) opt-ws)
                   #'form)))
  quoted-r \' `quote false
  syntax-quoted-form \` `syntax-quote false
  unquote-spliced-form (p/lex (p/mapcat "~@")) `unquote-splicing true
  unquoted-form \~ `unquote false
  derefed-r \@ `deref false
  var-inner-r \' `var false
  deprecated-meta-r \^ `meta false)

(def deprecated-meta-r
  (p/suffix deprecated-meta-r
    (p/effects println
      "WARNING: The ^ indicator is deprecated (since Clojure 1.1).")))

(def fn-inner-r
  (p/hook (prefix-list-fn `mini-fn)
    (p/circumfix (p/lit \() form-series (p/lit \)))))

(def metadata-r
  (p/+ map-form (p/hook (p/+ keyword-form symbol-form) #(hash-map :tag %))))

(def with-meta-inner-r
  (p/prefix (padded-lit \^)
    (p/for [metadata metadata-r, _ opt-ws, content #'form]
      (list `with-meta content metadata))))

; TODO Implement context

(def anonymous-fn-parameter
  (p/for [_ (p/lit \%), number (p/opt decimal-natural-number)]
    (or number 1)))

(def anonymous-fn-interior
  p/nothing)

(def anonymous-fn-r
  (p/circumfix
    (p/lit \()
    anonymous-fn-interior
    (p/lit \))))

(def dispatched-form
  (p/prefix (p/lit \#)
    (p/+ anonymous-fn-r set-inner-r fn-inner-r var-inner-r with-meta-inner-r)))

(def form-content
  (p/+ list-form vector-form map-form dispatched-form string
         syntax-quoted-form unquote-spliced-form unquoted-form
         deprecated-meta-r character keyword-form symbol-form number))

(def form (p/label "a form" (p/prefix opt-ws form-content)))

(def document
  (p/suffix form-series p/end-of-input))

(deftest various-rules
  (let [form form]
    (is (match? form {} "55.2e2" == 5520.))
    (is (match? form {} "16rFF" == 255))
    (is (match? form {} "16." == 16.))
    (is (match? form {} "true" true?))
    (is (= (with-out-str (p/parse form "^()" {} list list))
           "WARNING: The ^ indicator is deprecated (since Clojure 1.1).\n"))
    (is (match? form {} "[()]" = [()]))
    (is (match? form {} "\"\\na\\u3333\"" = "\na\u3333"))
    (is (non-match? form {:position 7} "([1 32]"
          {:label #{"a form" "')'" "whitespace"}}))
    (is (non-match? document {:position 3} "a/b/c"
          {:message #{"multiple slashes aren't allowed in symbols"}
           :label #{"an indicator" "the end of input"
                    "a symbol character" "whitespace"}}))
    (is (match? form {} ":a/b" = :a/b))
    (is (match? form {:context (ClojureContext "user" {})} "::b" = :user/b))
    (is (non-match? form {:position 3} "::z/abc"
          {:message #{"no namespace with alias 'z'"}
           :label #{"the end of input" "a symbol character" "an indicator"
                    "whitespace"}}))
    (is (match? form {} "clojure.core//" = 'clojure.core//))
    (is (match? form {} "\"a\\n\"" = "a\n"))
    (is (match? document {} "~@a ()" =
          [(list 'clojure.core/unquote-splicing 'a) ()]))
    (is (non-match? document {:position 4} "17rAZ"
          {:label #{"a base-17 digit" "an indicator"
                    "whitespace" "the end of input"}}))
    (is (non-match? document {:position 3} "3/0 3"
          {:label #{"a base-10 digit"}
           :message #{"a fraction's denominator cannot be zero"}}))))

(run-tests)
