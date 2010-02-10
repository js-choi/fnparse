(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound clojure.set clojure.template
        clojure.contrib.def clojure.contrib.seq-utils)
  (:import [clojure.lang IPersistentMap]))

; TODO
; How does Clojure's reader figure out namespaces and namespace aliases?
; Unicode character codes.
; Keyword-specific restrictions.
; Anonymous functions.

(defn prefix-list-fn [prefix-r]
  #(list prefix-r %))

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

(declare form)

(def ws-set (set " ,\t\n"))
(def indicator-set (set ";()[]{}\\\"'@^`#"))
(def comment-r (conc (lit \;) (rep* (antilit \newline))))
(def discarded-r (prefix-conc (lex (mapconc "#_")) #'form))
(def ws
  (with-label "whitespace"
    (rep+ (alt (term "a whitespace character" ws-set)
               comment-r discarded-r))))
(def ws? (opt ws))
(def indicator (term "an indicator" indicator-set))
(def separator (alt ws indicator))
(def form-end (alt (followed-by separator) end-of-input))
(def ns-separator (lit \/))
(def non-alphanumeric-symbol-char
  (set-lit "a non-alphanumeric symbol character" "*+!-_?."))
(def symbol-char
  (with-label "a symbol character"
    (alt ascii-alphanumeric non-alphanumeric-symbol-char)))
(def symbol-char-series
  (hook str* (rep+ symbol-char)))

(def symbol-end
  (annotate-error form-end
    (fn [error]
      (if (= (:unexpected-token error) \/)
        "multiple slashes aren't allowed in symbols"))))

(def symbol-suffix
  (prefix-conc ns-separator
    (alt symbol-char-series (constant-semantics ns-separator "/"))))

(def symbol-r
  (with-label "symbol"
    (complex [first-char ascii-letter
              rest-pre-slash (opt symbol-char-series)
              post-slash (opt symbol-suffix)
              _ symbol-end]
      (let [pre-slash (str first-char rest-pre-slash)]
        (if post-slash
          (symbol pre-slash post-slash)
          (or (peculiar-symbols pre-slash) ; In case it's true, false, or nil
              (symbol pre-slash)))))))

(def keyword-indicator (lit \:))

(def normal-keyword
  (complex [_ keyword-indicator
            pre-slash (opt symbol-char-series)
            post-slash (opt symbol-suffix)
            _ symbol-end]
    (if post-slash
      (keyword pre-slash post-slash)
      (keyword pre-slash))))

(defrm ns-resolved-keyword-end [pre-slash]
  (alt (complex [_ (followed-by ns-separator)
                 context get-context
                 prefix (only-when (get-in context [:ns-aliases pre-slash])
                          (format "no namespace with alias '%s'" pre-slash))
                 suffix symbol-suffix]
         [prefix suffix])
       (complex [context get-context]
         [(:ns-name context) pre-slash])))

(def ns-resolved-keyword
  (complex [_ (lex (factor= 2 keyword-indicator))
            pre-slash symbol-char-series
            [prefix suffix] (ns-resolved-keyword-end pre-slash)
            _ form-end]
    (keyword prefix suffix)))

(def keyword-r
  (with-label "keyword" (alt ns-resolved-keyword normal-keyword)))

(defrm radix-natural-number [base]
  (cascading-rep+ (radix-digit (if (<= base 36) base 36))
    identity #(+ (* base %1) %2)))

(def decimal-natural-number
  (radix-natural-number 10))

(def number-sign
  (template-alt [label token product]
    (with-label label (constant-semantics (lit token) product))
    "positive sign" \+ 1, "negative sign" \- -1))

(def no-number-tail
  (constant-semantics emptiness identity))

(def imprecise-fractional-part
  (prefix-conc (lit \.)
    (alt
      (semantics (cascading-rep+ decimal-digit #(/ % 10) #(/ (+ %1 %2) 10))
        #(partial + %))
      no-number-tail)))

(def exponential-part
  (prefix-conc
    (set-lit "exponent indicator" "eE")
      ; If I wasn't worrying about pure Clojure,
      ; use (case-insensitive-lit \e) above instead.
    (semantics decimal-natural-number
      #(partial * (expt-int 10 %)))))

(def fractional-exponential-part
  (complex [frac-fn imprecise-fractional-part
            exp-fn (alt exponential-part no-number-tail)]
    (comp exp-fn frac-fn)))

(def imprecise-number-tail
  (complex [tail-fn (alt fractional-exponential-part exponential-part)
            big-dec? (opt (lit \M))]
    (comp (if big-dec? bigdec double) tail-fn)))

(def fraction-denominator-tail
  (prefix-conc (lit \/)
    (semantics
      (anti-validate decimal-natural-number zero?
        "a fraction's denominator cannot be zero")
      (fn [denominator] #(/ % denominator)))))

(defrm radix-coefficient-tail [base]
  (semantics
    (prefix-conc
      (set-lit "radix indicator" "rR")
        ; If I wasn't worrying about pure Clojure,
        ; use (case-insensitive-lit \r) above instead.
      (radix-natural-number base))
    constantly))

(defrm number-tail [base]
  (alt imprecise-number-tail fraction-denominator-tail
       (radix-coefficient-tail base) no-number-tail))

(def number-r
  (complex [sign (opt number-sign)
            prefix-number decimal-natural-number
            tail-fn (number-tail prefix-number)
            _ form-end]
    (tail-fn (* (or sign 1) prefix-number))))

(def string-delimiter (lit \"))

(def unicode-escape-sequence
  (prefix-conc (lit \u)
    (semantics (factor= 4 hexadecimal-digit)
      (comp char reduce-hexadecimal-digits))))

(def character-name
  (alt (mapalt #(constant-semantics (mapconc (val %)) (key %))
         char-name-string)
       unicode-escape-sequence))

(def character-r (prefix-conc (lit \\) character-name))

(def escaped-char
  (prefix-conc (lit \\)
    (with-label "a valid escape sequence"
      (alt (template-alt [token character]
             (constant-semantics (lit token) character)
             \t \tab, \n \newline, \\ \\, \" \")
           unicode-escape-sequence))))

(def string-char (alt escaped-char (antilit \")))

(def string-r
  (semantics
    (circumfix-conc string-delimiter (rep* string-char) string-delimiter)
    #(->> % flatten (apply str))))

(def form-series (suffix-conc (rep* #'form) ws?))

(do-template [rule-name start-token end-token product-fn]
  (def rule-name
    (complex [_ (lit start-token)
              contents (opt form-series)
              _ (lit end-token)]
      (product-fn contents)))
  list-r \( \) #(apply list %)
  vector-r \[ \] vec
  map-r \{ \} #(apply hash-map %)
  set-inner-r \{ \} set)

(defrm padded-lit [token]
  (prefix-conc (lit token) ws?))

(do-template [rule-name prefix product-fn-symbol prefix-is-rule?]
  (def rule-name
    (semantics
      (prefix-conc (conc ((if prefix-is-rule? identity padded-lit) prefix) ws?)
                   #'form)
      (prefix-list-fn product-fn-symbol)))
  quoted-r \' `quote false
  syntax-quoted-r \` `syntax-quote false
  unquote-spliced-r (lex (mapconc "~@")) `unquote-splicing true
  unquoted-r \~ `unquote false
  derefed-r \@ `deref false
  var-inner-r \' `var false
  deprecated-meta-r \^ `meta false)

(def deprecated-meta-r
  (suffix-conc deprecated-meta-r
    (effects println
      "WARNING: The ^ indicator is deprecated (since Clojure 1.1).")))

(def fn-inner-r
  (semantics (circumfix-conc (lit \() form-series (lit \)))
    (prefix-list-fn `mini-fn)))

(def metadata-r
  (alt map-r (semantics (alt keyword-r symbol-r) #(hash-map :tag %))))

(def with-meta-inner-r
  (prefix-conc (padded-lit \^)
    (complex [metadata metadata-r, _ ws?, content #'form]
      (list `with-meta content metadata))))

; TODO Implement context

(defvar anonymous-fn-parameter
  (complex [_ (lit \%), number (opt decimal-natural-number)]
    (or number 1)))

(defvar anonymous-fn-interior
  nothing)

(def anonymous-fn-r
  (circumfix-conc
    (lit \()
    anonymous-fn-interior
    (lit \))))

(def dispatched-r
  (prefix-conc (lit \#)
    (alt anonymous-fn-r set-inner-r fn-inner-r var-inner-r with-meta-inner-r)))

(def form-content
  (alt list-r vector-r map-r dispatched-r string-r syntax-quoted-r
       unquote-spliced-r unquoted-r deprecated-meta-r character-r keyword-r
       symbol-r number-r))

(def form (with-label "a form" (prefix-conc ws? form-content)))

(def document
  (suffix-conc form-series end-of-input))

(use 'clojure.test 'name.choi.joshua.fnparse.hound.test)

(deftest various-rules
  (let [form form]
    (is (match? form {} "55.2e2" == 5520.))
    (is (match? form {} "16rFF" == 255))
    (is (match? form {} "16." == 16.))
    (is (match? form {} "true" true?))
    (is (= (with-out-str (parse form "^()" {} list list))
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
