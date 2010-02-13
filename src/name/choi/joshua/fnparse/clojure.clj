(ns name.choi.joshua.fnparse.clojure
  (:require [name.choi.joshua.fnparse.hound :as r]
            [clojure.template :as t] [clojure.set :as set]
            [clojure.contrib.seq-utils :as seq]
            name.choi.joshua.fnparse.hound.test)
  (:use [clojure.test :only #{deftest is run-tests}])
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

(declare form_)

(def comment-indicator_ (r/lit \;))

(def comment-char_ (r/antilit \newline))

(def comment_ (r/cat comment-indicator_ (r/rep* comment-char_)))

(def discarded_ (r/prefix (r/lex (r/mapcat "#_")) #'form_))

(def normal-ws-char_
  (r/term "a whitespace character" ws-set))

(def ws_
  (r/label "whitespace"
    (r/rep+ (r/+ normal-ws-char_ comment_ discarded_))))

(def opt-ws_ (r/opt ws_))

(def keyword-indicator_ (r/lit \:))

(def indicator_ (r/term "an indicator" indicator-set))

(def separator_ (r/+ ws_ indicator_))

(def form-end_ (r/+ (r/followed-by separator_) r/end-of-input_))

(def ns-separator_ (r/lit \/))

(def non-alphanumeric-symbol-char_
  (r/set-lit "a non-alphanumeric symbol character" "*+!-_?."))

(def symbol-first-char_
  (r/+ r/ascii-letter_ non-alphanumeric-symbol-char_))

(def symbol-char_
  (r/label "a symbol character"
    (r/+ symbol-first-char_ r/decimal-digit_)))

(def symbol-char-series_
  (r/hook str* (r/rep+ symbol-char_)))

(def symbol-end_
  (r/annotate-error annotate-symbol-end form-end_))

(def slash-symbol-suffix_
  (r/chook "/" ns-separator_))

(def symbol-suffix_
  (r/prefix ns-separator_ (r/+ symbol-char-series_ slash-symbol-suffix_)))

(def symbol_
  (r/for "a symbol"
         [first-char symbol-first-char_
          rest-pre-slash (r/opt symbol-char-series_)
          post-slash (r/opt symbol-suffix_)
          _ symbol-end_]
    (let [pre-slash (str first-char rest-pre-slash)]
      (if post-slash
        (symbol pre-slash post-slash)
        (or (peculiar-symbols pre-slash) ; In case it's true, false, or nil
            (symbol pre-slash))))))

(def normal-keyword_
  (r/for [_ keyword-indicator_
          pre-slash (r/opt symbol-char-series_)
          post-slash (r/opt symbol-suffix_)
          _ symbol-end_]
    (if post-slash
      (keyword pre-slash post-slash)
      (keyword pre-slash))))

(def followed-by-ns-separator_ (r/followed-by ns-separator_))

(r/defn fetch-referred-namespace [context namespace-alias]
  (r/only-when (get-in context [:ns-aliases namespace-alias])
    (format "no namespace with alias '%s'" namespace-alias)))

(r/defn ns-qualified-keyword-end-with-slash [pre-slash]
  (r/for [_ followed-by-ns-separator_
          context r/fetch-context_
          prefix (fetch-referred-namespace context pre-slash)
          suffix symbol-suffix_]
    [prefix suffix]))

(r/defn ns-qualified-keyword-empty-end [pre-slash]
  (r/for [context r/fetch-context_]
    [(:ns-name context) pre-slash]))

(r/defn ns-resolved-keyword-end [pre-slash]
  (r/+ (ns-qualified-keyword-end-with-slash pre-slash)
       (ns-qualified-keyword-empty-end pre-slash)))

(def ns-resolved-keyword_
  (r/for [_ (r/lex (r/factor= 2 keyword-indicator_))
          pre-slash symbol-char-series_
          [prefix suffix] (ns-resolved-keyword-end pre-slash)
          _ form-end_]
    (keyword prefix suffix)))

(def keyword_
  (r/label "a keyword"
    (r/+ ns-resolved-keyword_ normal-keyword_)))

(r/defn radix-natural-number [base]
  (r/cascading-rep+ (r/radix-digit (if (<= base 36) base 36))
    identity #(+ (* base %1) %2)))

(def decimal-natural-number_
  (radix-natural-number 10))

(def number-sign_
  (r/template-alt [label token product]
    (r/label label (r/chook product (r/lit token)))
    "positive sign" \+ 1, "negative sign" \- -1))

(def empty-number-tail_
  (r/chook identity r/emptiness_))

(def imprecise-fractional-part_
  (r/prefix
    (r/lit \.)
    (r/+ (r/hook #(partial + %)
           (r/cascading-rep+ r/decimal-digit_ #(/ % 10) #(/ (+ %1 %2) 10)))
         empty-number-tail_)))

(def exponential-part_
  (r/prefix
    (r/set-lit "exponent indicator" "eE")
      ; If I wasn't worrying about pure Clojure,
      ; use (r/case-insensitive-lit \e) above instead.
    (r/hook #(partial * (expt-int 10 %)) decimal-natural-number_)))

(def fractional-exponential-part_
  (r/for [frac-fn imprecise-fractional-part_
          exp-fn (r/+ exponential-part_ empty-number-tail_)]
    (comp exp-fn frac-fn)))

(def imprecise-number-tail_
  (r/for [tail-fn (r/+ fractional-exponential-part_ exponential-part_)
          big-dec? (r/opt (r/lit \M))]
    (comp (if big-dec? bigdec double) tail-fn)))

(def fraction-denominator-tail_
  (r/prefix (r/lit \/)
    (r/hook (fn [denominator] #(/ % denominator))
      (r/anti-validate decimal-natural-number_ zero?
        "a fraction's denominator cannot be zero"))))

(r/defn radix-coefficient-tail [base]
  (r/hook constantly
    (r/prefix
      (r/set-lit "radix indicator" "rR")
        ; If I wasn't worrying about pure Clojure,
        ; use (case-insensitive-r/lit \r) above instead.
      (radix-natural-number base))))

(r/defn number-tail [base]
  (r/+ imprecise-number-tail_ fraction-denominator-tail_
       (radix-coefficient-tail base) empty-number-tail_))

(def number_
  (r/for "a number"
    [sign (r/opt number-sign_)
     prefix-number decimal-natural-number_
     tail-fn (number-tail prefix-number)
     _ form-end_]
    (tail-fn (* (or sign 1) prefix-number))))

(def string-delimiter_ (r/lit \"))

(def unicode-escape-sequence_
  (r/prefix (r/lit \u)
    (r/hook (comp char reduce-hexadecimal-digits)
      (r/factor= 4 r/hexadecimal-digit_))))

(def character-name_
  (r/+ (r/mapalt #(r/chook (key %) (r/mapcat (val %))) char-name-string)
       unicode-escape-sequence_))

(def character_ (r/prefix (r/lit \\) character-name_))

(def escaped-char_
  (r/prefix (r/lit \\)
    (r/label "a valid escape sequence"
      (r/+ (r/template-alt [token character]
             (r/chook character (r/lit token))
             \t \tab, \n \newline, \\ \\, \" \")
           unicode-escape-sequence_))))

(def string-char_ (r/+ escaped-char_ (r/antilit \")))

(def string_
  (r/hook #(->> % seq/flatten str*)
    (r/circumfix string-delimiter_ (r/rep* string-char_) string-delimiter_)))

(def form-series_ (r/suffix (r/rep* #'form_) opt-ws_))

(t/do-template [rule_ start-token end-token product-fn]
  (def rule_
    (r/for [_ (r/lit start-token)
            contents (r/opt form-series_)
            _ (r/lit end-token)]
      (product-fn contents)))
  list_ \( \) #(apply list %)
  vector_ \[ \] vec
  map_ \{ \} #(apply hash-map %)
  set-inner_ \{ \} set)

(r/defn padded-lit [token]
  (r/prefix (r/lit token) opt-ws_))

(t/do-template [rule_ prefix product-fn-symbol prefix-is-rule?]
  (def rule_
    (r/hook (prefix-list-fn product-fn-symbol)
      (r/prefix
        (r/cat ((if prefix-is-rule? identity padded-lit) prefix) opt-ws_)
        #'form_)))
  quoted_ \' `quote false
  syntax-quoted_ \` `syntax-quote false
  unquote-spliced_ (r/lex (r/mapcat "~@")) `unquote-splicing true
  unquoted_ \~ `unquote false
  derefed_ \@ `deref false
  var-inner_ \' `var false
  deprecated-meta_ \^ `meta false)

(def deprecated-meta_
  (r/suffix deprecated-meta_
    (r/effects println
      "WARNING: The ^ indicator is deprecated (since Clojure 1.1).")))

(def fn-inner_
  (r/hook (prefix-list-fn `mini-fn)
    (r/circumfix (r/lit \() form-series_ (r/lit \)))))

(def tag_
  (r/hook #(hash-map :tag %)
    (r/+ keyword_ symbol_)))

(def metadata_
  (r/+ map_ tag_))

(def with-meta-inner_
  (r/prefix (padded-lit \^)
    (r/for [metadata metadata_, _ opt-ws_, content #'form_]
      (list `with-meta content metadata))))

; TODO Implement context

(def anonymous-fn-parameter-suffix_
  (r/+ decimal-natural-number_ (r/lit \&) (r/chook 1 r/emptiness_)))

(def anonymous-fn-parameter_
  (r/for "a parameter"
    [_ (r/lit \%)
     context r/fetch-context_
     fn-context (r/only-when (:anonymous-fn-context context)
                  "a parameter literals must be inside an anonymous function")
     suffix anonymous-fn-parameter-suffix_
     already-existing-symbol (r/prod (get-already-existing-symbol fn-context
                                                                  suffix))
     parameter-symbol (r/prod (or already-existing-symbol
                                  (gensym "parameter")))
     _ (if (nil? already-existing-symbol)
         (r/alter-context update-fn-context suffix parameter-symbol)
         r/emptiness_)]
    parameter-symbol))

(def anonymous-fn_
  (r/for "an anonymous function"
    [_ (r/lit \()
     pre-context r/fetch-context_
     _ (r/only-when (not (:anonymous-fn-context pre-context))
         "nested anonymous functions are not allowed")
     _ (r/alter-context assoc :anonymous-fn-context (AnonymousFnContext [] nil))
     content form-series_
     post-context r/fetch-context_
     _ (r/alter-context assoc :anonymous-fn-context nil)
     _ (r/lit \))]
    (let [anonymous-fn-context (:anonymous-fn-context post-context)
          parameters (make-parameter-vector anonymous-fn-context)]
      (list `fn 'anonymous-fn parameters content))))

(def dispatched-inner_
  (r/+ anonymous-fn_ set-inner_ fn-inner_ var-inner_ with-meta-inner_))

(def dispatched_
  (r/prefix (r/lit \#) dispatched-inner_))

(def form-content_
  (r/+ list_ vector_ map_ dispatched_ string_ syntax-quoted_
       unquote-spliced_ unquoted_ deprecated-meta_ character_ keyword_
       anonymous-fn-parameter_ symbol_ number_))

(def form_
  (r/label "a form" (r/prefix opt-ws_ form-content_)))

(def document_
  (r/suffix form-series_ r/end-of-input_))

(deftest various-rules
  (is (match? form_ {} "55.2e2" == 5520.))
  (is (match? form_ {} "16rFF" == 255))
  (is (match? form_ {} "16." == 16.))
  (is (match? form_ {} "true" true?))
  (is (= (with-out-str (r/parse form_ "^()" {} list list))
         "WARNING: The ^ indicator is deprecated (since Clojure 1.1).\n"))
  (is (match? form_ {} "[()]" = [()]))
  (is (match? form_ {} "\"\\na\\u3333\"" = "\na\u3333"))
  (is (non-match? form_ {:position 7} "([1 32]"
        {:label #{"a form" "')'" "whitespace"}}))
  (is (non-match? form_ {:position 3} "a/b/c"
        {:message #{"multiple slashes aren't allowed in symbols"}
         :label #{"an indicator" "the end of input"
                  "a symbol character" "whitespace"}}))
  (is (match? form_ {} ":a/b" = :a/b))
  (is (match? form_ {:context (ClojureContext "user" {} nil)}
        "::b" = :user/b))
  (is (non-match? form_ {:position 3} "::z/abc"
        {:message #{"no namespace with alias 'z'"}
         :label #{"the end of input" "a symbol character" "an indicator"
                  "whitespace"}}))
  (is (match? form_ {} "+" = '+))
  (is (match? form_ {} "clojure.core//" = 'clojure.core//))
  (is (match? form_ {} "\"a\\n\"" = "a\n"))
  (is (match? form_ {} "[~@a ()]" =
        [(list 'clojure.core/unquote-splicing 'a) ()]))
  (is (match? form_ {:context (ClojureContext "user" {} nil)}
        "[#(%) #(apply + % %2 %2 %&)]"
        #(= ((eval (second %)) 3 2 2 1) 10)))
  (is (non-match? form_ {:position 4} "17rAZ"
        {:label #{"a base-17 digit" "an indicator"
                  "whitespace" "the end of input"}}))
  (is (non-match? form_ {:position 6, :context (ClojureContext "user" {} nil)}
        "#(% #(%))"
        {:message #{"nested anonymous functions are not allowed"}}))
  (is (non-match? form_ {:position 3} "3/0 3"
        {:label #{"a base-10 digit"}
         :message #{"a fraction's denominator cannot be zero"}})))

(run-tests)
