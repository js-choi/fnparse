(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound clojure.set clojure.template
        clojure.contrib.def clojure.contrib.seq-utils)
  (:import [clojure.lang IPersistentMap]))

; TODO
; How does Clojure's reader figure out namespaces and namespace aliases?
; Unicode character codes.
; Keyword-specific restrictions.
; Anonymous functions.

(defn- prefix-list-fn [prefix-r]
  #(list prefix-r %))

(defn- str* [chars]
  (apply str chars))

(deftype UnresolvedNSPrefixedForm [f prefix name] IPersistentMap)

(declare form)

(defvar- ws-set (set " ,\t\n"))
(defvar- indicator-set (set ";()[]{}\\\"'@^`#"))
(defvar- comment-r (conc (lit \;) (rep* (antilit \newline))))
(defvar- discarded-r (prefix-conc (lex (mapconc "#_")) #'form))
(defvar- ws
  (with-label "whitespace"
    (rep+ (alt (term "a whitespace character" ws-set)
               comment-r discarded-r))))
(defvar- ws? (opt ws))
(defvar- indicator (term "an indicator" indicator-set))
(defvar- separator (alt ws indicator))
(defvar- form-end (alt (followed-by separator) end-of-input))
(defvar- ns-separator (lit \/))
(defvar- non-alphanumeric-symbol-char
  (set-lit "a non-alphanumeric symbol character" "*+!-_?."))
(defvar- symbol-char
  (with-label "a symbol character"
    (alt ascii-alphanumeric non-alphanumeric-symbol-char)))

(defvar- symbol-end
  (annotate-error form-end
    (fn [error]
      (if (= (:unexpected-token error) \/)
        "multiple slashes aren't allowed in symbols")))
  "When a symbol is read, it must be ensured that the last valid symbol
  character is followed by the actual *end* of the symbol, such as whitespace,
  an indicator like ']', or the end of the entire input. This is done by the
  lookahead rule form-end.
      A common error may be that symbols contain more than one slash, which is
  invalid under Clojure's official reader rules. By default, if the form-end
  rule fails after a symbol's last valid symbol character, the user will get
  an error like: \"parse error: expected a symbol character, whitespace, an
  indicator, or the end of input\". Which is fine, but we can do better.
      If a/b/c is parsed as a symbol, then the symbol rule, which allows one
  slash, will stop at \"/c\". However, then form-end will fail, because the
  slash is not a valid form end (i.e. not whitespace, an indicator, or the
  end of input).
      It would be more informative if the user was given a message like,
  \"Multiple slashes aren't allowed in symbols.\" We can do that with the
  annotate-error rule-maker. It captures any failure that its subrule returns,
  and passes it to a message-creating function. That function can either return
  a string, if it wants to add a message to the error's descriptors, or nil, if
  it does not want to add a message.
      So it tests if the error's unexpected token was a slash. If it is, then
  we know that the user tried to put more than one slash into a symbol, so we
  add the message.
      (In actuality, however, multiple slashes *are* currently allowed by the
  reader as of Clojure 1.1: 'a/b/c is read as (symbol \"a/b\" \"c\"). However,
  the meaning of 'a/b/c is not well-defined, as both (symbol \"a/b\" \"c\") and
  (symbol \"a\" \"b/c\") return 'a/b/c'. It's officially not allowed anyway
  according to http://clojure.org/reader.)")

(defvar- peculiar-symbols {"nil" nil, "true" true, "false" false}
  "This map contains the mappings of the 'peculiar' symbols—nil, true, and
  false—from their strings to their Boolean values. This is used in the
  'normal-symbol rule to determine if a symbol is actually one of these.")

(defvar- symbol-suffix
  (opt (prefix-conc ns-separator
         (alt (rep+ symbol-char) (semantics ns-separator list)))))

(defrm- symbol-chars [first-rule process-chars]
  (complex [first-chars first-rule
            prefix-chars (rep* symbol-char)
            suffix-chars symbol-suffix
            _ symbol-end]
    (process-chars first-chars (str* prefix-chars) (str* suffix-chars))))

(defvar- symbol-r
  (with-label "symbol"
    (symbol-chars ascii-letter
      (fn [first-chars rest-prefix suffix]
        (let [prefix (str first-chars rest-prefix)]
          (if-not (= suffix "")
            (UnresolvedNSPrefixedForm `symbol prefix suffix)
            (or (peculiar-symbols prefix) ; In case it's true, false, or nil
                (symbol prefix))))))))

(defvar- keyword-indicator (lit \:))

(defvar- normal-keyword
  (symbol-chars keyword-indicator
    (fn [_ prefix suffix] (keyword prefix suffix))))

(defvar- ns-resolved-keyword
  (symbol-chars (lex (factor= 2 keyword-indicator))
    (fn [_ prefix suffix]
      (if (= suffix "")
        (UnresolvedNSPrefixedForm `keyword nil prefix)
        (UnresolvedNSPrefixedForm `keyword prefix suffix)))))

(defvar- keyword-r
  (with-label "keyword" (alt ns-resolved-keyword normal-keyword)))

#_(defvar- keyword-r
  (semantics (prefix-conc keyword-indicator symbol-r)
    #(keyword (namespace %) (name %))))

(defrm- radix-natural-number [base]
  (cascading-rep+ (radix-digit base) identity #(+ (* base %1) %2)))

(defvar- decimal-natural-number
  (radix-natural-number 10))

(defvar- number-sign
  (template-alt [label token product]
    (with-label label (constant-semantics (lit token) product))
    "positive sign" \+ 1, "negative sign" \- -1))

(defvar- no-number-tail
  (constant-semantics emptiness identity))

(defvar- imprecise-fractional-part
  (prefix-conc (lit \.)
    (alt
      (semantics (cascading-rep+ decimal-digit #(/ % 10) #(/ (+ %1 %2) 10))
        #(partial + %))
      no-number-tail)))

(defn- expt-int [base pow]
  (loop [n pow, y 1, z base]
    (let [t (bit-and n 1), n (bit-shift-right n 1)]
      (cond
       (zero? t) (recur n y (* z z))
       (zero? n) (* z y)
       :else (recur n (* z y) (* z z))))))

(defvar- exponential-part
  (prefix-conc
    #_(case-insensitive-lit \e)
    (set-lit "exponent indicator" "eE")
    (semantics decimal-natural-number
      #(partial * (expt-int 10 %)))))

(defvar- fractional-exponential-part
  (complex [frac-fn imprecise-fractional-part
            exp-fn (alt exponential-part no-number-tail)]
    (comp exp-fn frac-fn)))

(defvar- imprecise-number-tail
  (complex [tail-fn (alt fractional-exponential-part exponential-part)
            big-dec? (opt (lit \M))]
    (comp (if big-dec? bigdec double) tail-fn)))

(defvar- fraction-denominator-tail
  (prefix-conc (lit \/)
    (semantics
      (anti-validate decimal-natural-number zero?
        "a fraction's denominator cannot be zero")
      (fn [denominator] #(/ % denominator)))))

(defrm- radix-coefficient-tail [base]
  (if (and (integer? base) (<= 0 base 36))
    (semantics
      (prefix-conc
        #_(case-insensitive-lit \r)
        (set-lit "radix indicator" "rR")
        (radix-natural-number base))
      constantly)
    nothing))

(defrm- number-tail [base]
  (alt imprecise-number-tail fraction-denominator-tail
       (radix-coefficient-tail base) no-number-tail))

(defvar- number-r
  (complex [sign (opt number-sign)
            prefix-number decimal-natural-number
            tail-fn (number-tail prefix-number)
            _ form-end]
    (tail-fn (* (or sign 1) prefix-number))))

(defvar- string-delimiter (lit \"))

(defn- reduce-hexadecimal-digits [digits]
  (reduce #(+ (* 16 %1) %2) digits))

(defvar- unicode-escape-sequence
  (prefix-conc (lit \u)
    (semantics (factor= 4 hexadecimal-digit)
      (comp char reduce-hexadecimal-digits))))

(defvar- character-name
  (alt (mapalt #(constant-semantics (mapconc (val %)) (key %))
         char-name-string)
       unicode-escape-sequence))

(defvar- character-r (prefix-conc (lit \\) character-name))

(defvar- escaped-char
  (prefix-conc (lit \\)
    (with-label "a valid escape sequence"
      (alt (template-alt [token character]
             (constant-semantics (lit token) character)
             \t \tab, \n \newline, \\ \\, \" \")
           unicode-escape-sequence))))

(defvar- string-char (alt escaped-char (antilit \")))

(defvar- string-r
  (semantics
    (circumfix-conc string-delimiter (rep* string-char) string-delimiter)
    #(->> % flatten (apply str))))

(defvar- form-series (suffix-conc (rep* #'form) ws?))

(do-template [rule-name start-token end-token product-fn]
  (defvar- rule-name
    (complex [_ (lit start-token)
              contents (opt form-series)
              _ (lit end-token)]
      (product-fn contents)))
  list-r \( \) #(apply list %)
  vector-r \[ \] vec
  map-r \{ \} #(apply hash-map %)
  set-inner-r \{ \} set)

(defn- padded-lit [token]
  (prefix-conc (lit token) ws?))

(do-template [rule-name prefix product-fn-symbol prefix-is-rule?]
  (defvar- rule-name
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

(defvar- fn-inner-r
  (semantics (circumfix-conc (lit \() form-series (lit \)))
    (prefix-list-fn `mini-fn)))

(defvar- metadata-r
  (alt map-r (semantics (alt keyword-r symbol-r) #(hash-map :tag %))))

(defvar- with-meta-inner-r
  (prefix-conc (padded-lit \^)
    (complex [metadata metadata-r, _ ws?, content #'form]
      (list `with-meta content metadata))))

; TODO Implement context

(defvar anonymous-fn-parameter
  (complex [_ (lit \%), number (opt decimal-natural-number)]
    (or number 1)))

(defvar anonymous-fn-interior
  nothing)

(defvar- anonymous-fn-r
  (circumfix-conc
    (lit \()
    anonymous-fn-interior
    (lit \))))

(defvar- dispatched-r
  (prefix-conc (lit \#)
    (alt anonymous-fn-r set-inner-r fn-inner-r var-inner-r with-meta-inner-r)))

(defvar- form-content
  (alt list-r vector-r map-r dispatched-r string-r syntax-quoted-r
       unquote-spliced-r unquoted-r deprecated-meta-r character-r keyword-r
       symbol-r number-r))

(defvar- form (with-label "a form" (prefix-conc ws? form-content)))

(defvar- document
  (suffix-conc form-series end-of-input))

(use 'clojure.test 'name.choi.joshua.fnparse.hound.test)

(deftest various-rules
  (let [form form]
    (is (full-match? form "55.2e2" == 5520.))
    (is (full-match? form "16rFF" == 255))
    (is (full-match? form "16." == 16.))
    (is (full-match? form "true" true?))
    (is (full-match? form "^()" = (list `meta ())))
    (is (full-match? form "[()]" = [()]))
    (is (full-match? form "\"\\na\\u3333\"" = "\na\u3333"))
    (is (non-match? form "([1 32]" 7
          {:label #{"a form" "')'" "whitespace"}}))
    (is (non-match? document "a/b/c" 3
          {:message #{"multiple slashes aren't allowed in symbols"}
           :label #{"an indicator" "the end of input"
                    "a symbol character" "whitespace"}}))
    (is (full-match? form ":a/b" = :a/b))
    (is (full-match? form "::b" = (UnresolvedNSPrefixedForm `keyword nil "b")))
    (is (full-match? form "clojure.core//" =
          (UnresolvedNSPrefixedForm `symbol "clojure.core" "/")))
    (is (full-match? form "clojure.core/map" =
          (UnresolvedNSPrefixedForm `symbol "clojure.core" "map")))
    (is (full-match? form "\"a\\n\"" = "a\n"))
    (is (full-match? document "~@a ()" =
          [(list 'clojure.core/unquote-splicing 'a) ()]))
    (is (non-match? document "17rAZ" 4
          {:label #{"a base-17 digit" "an indicator"
                    "whitespace" "the end of input"}}))
    (is (non-match? document "3/0 3" 3
          {:label #{"a base-10 digit"}
           :message #{"a fraction's denominator cannot be zero"}}))))

(run-tests)
