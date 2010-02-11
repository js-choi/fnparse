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

(declare form_)

(def comment-indicator_ (p/lit \;))

(def comment-char_ (p/antilit \newline))

(def comment_ (p/cat comment-indicator_ (p/rep* comment-char_)))

(def discarded_ (p/prefix (p/lex (p/mapcat "#_")) #'form_))

(def ws_
  (p/label "whitespace"
    (p/rep+ (p/+ (p/term "a whitespace character" ws-set)
                 comment_ discarded_))))

(def opt-ws_ (p/opt ws_))

(def indicator_ (p/term "an indicator" indicator-set))

(def separator_ (p/+ ws_ indicator_))

(def form-end_ (p/+ (p/followed-by separator_) p/end-of-input))

(def ns-separator_ (p/lit \/))

(def non-alphanumeric-symbol-char_
  (p/set-lit "a non-alphanumeric symbol character" "*+!-_?."))

(def symbol-char_
  (p/label "a symbol character"
    (p/+ p/ascii-alphanumeric non-alphanumeric-symbol-char_)))

(def symbol-char-series_
  (p/hook str* (p/rep+ symbol-char_)))

(def symbol-end_
  (p/annotate-error form-end_
    (fn [error]
      (if (= (:unexpected-token error) \/)
        "multiple slashes aren't allowed in symbols"))))

(def symbol-suffix_
  (p/prefix ns-separator_
    (p/+ symbol-char-series_ (p/chook "/" ns-separator_))))

(def symbol_
  (p/label "symbol"
    (p/for [first-char p/ascii-letter
            rest-pre-slash (p/opt symbol-char-series_)
            post-slash (p/opt symbol-suffix_)
            _ symbol-end_]
      (let [pre-slash (str first-char rest-pre-slash)]
        (if post-slash
          (symbol pre-slash post-slash)
          (or (peculiar-symbols pre-slash) ; In case it's true, false, or nil
              (symbol pre-slash)))))))

(def keyword-indicator_ (p/lit \:))

(def normal-keyword_
  (p/for [_ keyword-indicator_
          pre-slash (p/opt symbol-char-series_)
          post-slash (p/opt symbol-suffix_)
          _ symbol-end_]
    (if post-slash
      (keyword pre-slash post-slash)
      (keyword pre-slash))))

(p/defrm ns-resolved-keyword-end [pre-slash]
  (p/+ (p/for [_ (p/followed-by ns-separator_)
               context p/get-context
               prefix (p/only-when (get-in context [:ns-aliases pre-slash])
                        (format "no namespace with alias '%s'" pre-slash))
               suffix symbol-suffix_]
         [prefix suffix])
       (p/for [context p/get-context]
         [(:ns-name context) pre-slash])))

(def ns-resolved-keyword_
  (p/for [_ (p/lex (p/factor= 2 keyword-indicator_))
          pre-slash symbol-char-series_
          [prefix suffix] (ns-resolved-keyword-end pre-slash)
          _ form-end_]
    (keyword prefix suffix)))

(def keyword_
  (p/label "keyword" (p/+ ns-resolved-keyword_ normal-keyword_)))

(p/defrm radix-natural-number [base]
  (p/cascading-rep+ (p/radix-digit (if (<= base 36) base 36))
    identity #(+ (* base %1) %2)))

(def decimal-natural-number_
  (radix-natural-number 10))

(def number-sign_
  (p/template-alt [label token product]
    (p/label label (p/chook product (p/lit token)))
    "positive sign" \+ 1, "negative sign" \- -1))

(def no-number-tail_
  (p/chook identity p/emptiness))

(def imprecise-fractional-part_
  (p/prefix
    (p/lit \.)
    (p/+ (p/hook #(partial + %)
           (p/cascading-rep+ p/decimal-digit #(/ % 10) #(/ (+ %1 %2) 10)))
         no-number-tail_)))

(def exponential-part_
  (p/prefix
    (p/set-lit "exponent indicator" "eE")
      ; If I wasn't worrying about pure Clojure,
      ; use (p/case-insensitive-lit \e) above instead.
    (p/hook #(partial * (expt-int 10 %)) decimal-natural-number_)))

(def fractional-exponential-part_
  (p/for [frac-fn imprecise-fractional-part_
          exp-fn (p/+ exponential-part_ no-number-tail_)]
    (comp exp-fn frac-fn)))

(def imprecise-number-tail_
  (p/for [tail-fn (p/+ fractional-exponential-part_ exponential-part_)
          big-dec? (p/opt (p/lit \M))]
    (comp (if big-dec? bigdec double) tail-fn)))

(def fraction-denominator-tail_
  (p/prefix (p/lit \/)
    (p/hook (fn [denominator] #(/ % denominator))
      (p/anti-validate decimal-natural-number_ zero?
        "a fraction's denominator cannot be zero"))))

(p/defrm radix-coefficient-tail [base]
  (p/hook constantly
    (p/prefix
      (p/set-lit "radix indicator" "rR")
        ; If I wasn't worrying about pure Clojure,
        ; use (case-insensitive-p/lit \r) above instead.
      (radix-natural-number base))))

(p/defrm number-tail [base]
  (p/+ imprecise-number-tail_ fraction-denominator-tail_
       (radix-coefficient-tail base) no-number-tail_))

(def number_
  (p/for [sign (p/opt number-sign_)
          prefix-number decimal-natural-number_
          tail-fn (number-tail prefix-number)
          _ form-end_]
    (tail-fn (* (or sign 1) prefix-number))))

(def string-delimiter_ (p/lit \"))

(def unicode-escape-sequence_
  (p/prefix (p/lit \u)
    (p/hook (comp char reduce-hexadecimal-digits)
      (p/factor= 4 p/hexadecimal-digit))))

(def character-name_
  (p/+ (p/mapalt #(p/chook (key %) (p/mapcat (val %))) char-name-string)
       unicode-escape-sequence_))

(def character_ (p/prefix (p/lit \\) character-name_))

(def escaped-char_
  (p/prefix (p/lit \\)
    (p/label "a valid escape sequence"
      (p/+ (p/template-alt [token character]
             (p/chook character (p/lit token))
             \t \tab, \n \newline, \\ \\, \" \")
           unicode-escape-sequence_))))

(def string-char_ (p/+ escaped-char_ (p/antilit \")))

(def string_
  (p/hook #(->> % seq/flatten str*)
    (p/circumfix string-delimiter_ (p/rep* string-char_) string-delimiter_)))

(def form-series_ (p/suffix (p/rep* #'form_) opt-ws_))

(template/do-template [rule_ start-token end-token product-fn]
  (def rule_
    (p/for [_ (p/lit start-token)
            contents (p/opt form-series_)
            _ (p/lit end-token)]
      (product-fn contents)))
  list_ \( \) #(apply list %)
  vector_ \[ \] vec
  map_ \{ \} #(apply hash-map %)
  set-inner_ \{ \} set)

(p/defrm padded-lit [token]
  (p/prefix (p/lit token) opt-ws_))

(template/do-template [rule_ prefix product-fn-symbol prefix-is-rule?]
  (def rule_
    (p/hook (prefix-list-fn product-fn-symbol)
      (p/prefix
        (p/cat ((if prefix-is-rule? identity padded-lit) prefix) opt-ws_)
        #'form_)))
  quoted_ \' `quote false
  syntax-quoted_ \` `syntax-quote false
  unquote-spliced_ (p/lex (p/mapcat "~@")) `unquote-splicing true
  unquoted_ \~ `unquote false
  derefed_ \@ `deref false
  var-inner_ \' `var false
  deprecated-meta_ \^ `meta false)

(def deprecated-meta_
  (p/suffix deprecated-meta_
    (p/effects println
      "WARNING: The ^ indicator is deprecated (since Clojure 1.1).")))

(def fn-inner_
  (p/hook (prefix-list-fn `mini-fn)
    (p/circumfix (p/lit \() form-series_ (p/lit \)))))

(def tag_
  (p/hook #(hash-map :tag %)
    (p/+ keyword_ symbol_)))

(def metadata_
  (p/+ map_ tag_))

(def with-meta-inner_
  (p/prefix (padded-lit \^)
    (p/for [metadata metadata_, _ opt-ws_, content #'form_]
      (list `with-meta content metadata))))

; TODO Implement context

(def anonymous-fn-parameter_
  (p/for [_ (p/lit \%), number (p/opt decimal-natural-number_)]
    (or number 1)))

(def anonymous-fn-interior_
  p/nothing)

(def anonymous-fn_
  (p/circumfix
    (p/lit \()
    anonymous-fn-interior_
    (p/lit \))))

(def dispatched-inner_
  (p/+ anonymous-fn_ set-inner_ fn-inner_ var-inner_ with-meta-inner_))

(def dispatched_
  (p/prefix (p/lit \#) dispatched-inner_))

(def form-content_
  (p/+ list_ vector_ map_ dispatched_ string_ syntax-quoted_
       unquote-spliced_ unquoted_ deprecated-meta_ character_ keyword_
       symbol_ number_))

(def form_
  (p/label "a form" (p/prefix opt-ws_ form-content_)))

(def document_
  (p/suffix form-series_ p/end-of-input))

(deftest various-rules
  (is (match? form_ {} "55.2e2" == 5520.))
  (is (match? form_ {} "16rFF" == 255))
  (is (match? form_ {} "16." == 16.))
  (is (match? form_ {} "true" true?))
  (is (= (with-out-str (p/parse form_ "^()" {} list list))
         "WARNING: The ^ indicator is deprecated (since Clojure 1.1).\n"))
  (is (match? form_ {} "[()]" = [()]))
  (is (match? form_ {} "\"\\na\\u3333\"" = "\na\u3333"))
  (is (non-match? form_ {:position 7} "([1 32]"
        {:label #{"a form" "')'" "whitespace"}}))
  (is (non-match? document_ {:position 3} "a/b/c"
        {:message #{"multiple slashes aren't allowed in symbols"}
         :label #{"an indicator" "the end of input"
                  "a symbol character" "whitespace"}}))
  (is (match? form_ {} ":a/b" = :a/b))
  (is (match? form_ {:context (ClojureContext "user" {})} "::b" = :user/b))
  (is (non-match? form_ {:position 3} "::z/abc"
        {:message #{"no namespace with alias 'z'"}
         :label #{"the end of input" "a symbol character" "an indicator"
                  "whitespace"}}))
  (is (match? form_ {} "clojure.core//" = 'clojure.core//))
  (is (match? form_ {} "\"a\\n\"" = "a\n"))
  (is (match? document_ {} "~@a ()" =
        [(list 'clojure.core/unquote-splicing 'a) ()]))
  (is (non-match? document_ {:position 4} "17rAZ"
        {:label #{"a base-17 digit" "an indicator"
                  "whitespace" "the end of input"}}))
  (is (non-match? document_ {:position 3} "3/0 3"
        {:label #{"a base-10 digit"}
         :message #{"a fraction's denominator cannot be zero"}})))

(run-tests)
