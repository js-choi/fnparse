(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound clojure.set clojure.template
        clojure.contrib.def clojure.contrib.seq-utils)
  (:import [clojure.lang IPersistentMap]))

; TODO
; How does Clojure's reader figure out namespaces and namespace aliases?
; The qualified division symbol.
; Unicode character codes.
; Keyword-specific restrictions.
; Namespace-qualified keywords.
; Anonymous functions.

(defn- prefix-list-fn [prefix-r]
  #(list prefix-r %))

(defn- apply-str [chars]
  (apply str chars))

(deftype UnresolvedNSPrefixedForm [f prefix name] IPersistentMap)

(declare form)

(defvar- ws-set (set " ,\t\n"))
(defvar- indicator-set (set ";()[]{}\\\"'@^`#"))
(defvar- separator-set (union ws-set indicator-set))
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

(defvar- division-symbol
  (suffix-conc (constant-semantics (lit \/) '/)
    form-end))

(defvar- peculiar-symbols {"nil" nil, "true" true, "false" false})

(defvar- normal-symbol
  (complex [first-letter ascii-letter
            other-prefix-chars (rep* symbol-char)
            suffix-chars (opt (prefix-conc ns-separator (rep+ symbol-char)))
            _ (annotate-error form-end
               #(if (= (:unexpected-token %) \/)
                  "multiple slashes aren't allowed in symbols"))]
    (let [prefix (->> other-prefix-chars (cons first-letter) apply-str)]
      (if (seq suffix-chars)
        (UnresolvedNSPrefixedForm `symbol prefix (apply-str suffix-chars))
        (if-let [peculiar-product (peculiar-symbols prefix)]
          peculiar-product
          (symbol prefix))))))

(defvar- symbol-r
  (with-label "symbol"
    (alt division-symbol normal-symbol)))

(do-template [name string product]
  (defvar- name (constant-semantics (mapconc string) product))
  nil-r "nil" nil, true-r "true" true, false-r "false" false)

(defvar- keyword-indicator (lit \:))

(defvar- keyword-r
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
  (prefix-conc
    (padded-lit \^)
    (complex [metadata metadata-r, _ ws?, content #'form]
      (list `with-meta content metadata))))

(defvar- dispatched-r
  (prefix-conc
    (lit \#)
    (alt set-inner-r fn-inner-r var-inner-r with-meta-inner-r)))

(defvar- form-content
  (alt list-r vector-r map-r dispatched-r string-r syntax-quoted-r
       unquote-spliced-r unquoted-r division-symbol deprecated-meta-r
       character-r keyword-r symbol-r number-r))

(defvar- form (with-label "a form" (prefix-conc ws? form-content)))

(defvar- document
  (suffix-conc form-series end-of-input))

(use 'clojure.test 'name.choi.joshua.fnparse.hound.test)

(deftest various-rules
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
  #_(is (full-match? form ":a/b" = :a/b))
  (is (full-match? form "\"a\\n\"" = "a\n"))
  (is (full-match? document "~@a ()" =
        [(list 'clojure.core/unquote-splicing 'a) ()]))
  (is (non-match? document "17rAZ" 4
        {:label #{"a base-17 digit" "an indicator"
                  "whitespace" "the end of input"}}))
  (is (non-match? document "3/0 3" 3
        {:label #{"a base-10 digit"}
         :message #{"a fraction's denominator cannot be zero"}})))

(run-tests)
