(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound clojure.set clojure.template
        clojure.contrib.def clojure.contrib.seq-utils))

; TODO
; Radix bases and hexadecimal digits in integers.
; Namespace-qualified symbols.
; The qualified division symbol.
; Unicode character codes.
; Keyword-specific restrictions.

(defn- prefix-list-fn [prefix-form]
  #(list prefix-form %))

(declare form)

(defvar- ws-set (set " ,\t\n"))
(defvar- indicator-set (set ";()[]{}\\\"'@^`#"))
(defvar- separator-set (union ws-set indicator-set))
(defvar- comment-r (conc (lit \;) (rep* (antilit \newline))))
(defvar- discarded-form (prefix-conc (lex (mapconc "#_")) #'form))
(defvar- ws
  (with-label "whitespace"
    (rep+ (alt (term "whitespace character" ws-set)
               comment-r discarded-form))))
(defvar- ws? (opt ws))
(defvar- indicator (term "indicator" indicator-set))
(defvar- symbol-char (antiterm "symbol char" separator-set))
(defvar- form-end (alt (followed-by (alt ws indicator)) end-of-input))

(defvar- division-symbol (constant-semantics (lit \/) '/))

(defvar- normal-symbol
  (complex [first-letter ascii-letter, other-chars (rep* symbol-char)]
    (->> other-chars
      (cons first-letter) (apply str) symbol)))

(defvar- symbol-r (alt division-symbol normal-symbol))

(defvar- character-name
  (mapalt #(constant-semantics (mapconc (val %)) (key %))
    char-name-string))

(defvar- character-form (prefix-conc (lit \\) character-name))

(defvar- peculiar-symbol
  (lex (suffix-conc
         (mapalt #(constant-semantics (mapconc (key %)) (val %))
           {"nil" nil, "true" :true, "false" false})
         form-end)))

(defvar- keyword-indicator (lit \:))

(defvar- keyword-r
  (prefix-conc keyword-indicator symbol-r))

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

(defvar- fractional-part
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
  (prefix-conc (alt (lit \e) (lit \E))
    (semantics decimal-natural-number
      #(partial * (expt-int 10 %)))))

(defvar- fractional-exponential-part
  (complex [frac-fn fractional-part
            exp-fn (alt exponential-part no-number-tail)]
    (comp exp-fn frac-fn)))

(defvar- noninteger-number-tail
  (complex [tail-fn (alt fractional-exponential-part exponential-part)
            big-dec? (opt (lit \M))]
    (comp (if big-dec? bigdec double) tail-fn)))

(defrm- radix-coefficient-tail [base]
  (println base)
  (if (and (integer? base) (<= 0 base 36))
    (semantics
      (prefix-conc (case-insensitive-lit \r) (radix-natural-number base))
      constantly)
    nothing))

(defrm- number-tail [base]
  (alt noninteger-number-tail (radix-coefficient-tail base) no-number-tail))

(defvar- simple-integer
  (complex [sign (opt number-sign)
            prefix-number decimal-natural-number
            tail-fn (number-tail prefix-number)]
    (tail-fn (* (or sign 1) prefix-number))))

(defvar- number-form
  simple-integer)

(defvar- string-delimiter (lit \"))
(defvar- escape-sequence-map
  {\t \tab
   \n \newline
   \\ \\
   \" \"})

(defvar- escape-sequence
  (semantics (prefix-conc (lit \\) (set-lit "valid escape sequence"
                                     (keys escape-sequence-map)))
    escape-sequence-map))

(defvar- string-char (alt escape-sequence (antilit \")))

(defvar- string-r
  (semantics
    (circumfix-conc string-delimiter (rep* string-char) string-delimiter)
    #(->> % flatten (apply str))))

(defvar- form-series (suffix-conc (rep* #'form) ws?))

(do-template [rule-name start-token end-token product-fn]
  (defvar- rule-name
    (complex [_ (lit start-token)
              contents (opt form-series)
              _ (with-label (format "a %s or an form" end-token)
                  (lit end-token))]
      (product-fn contents)))
  list-r \( \) list*
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
  quoted-form \' `quote false
  syntax-quoted-form \` `syntax-quote false
  unquote-spliced-form (lex (mapconc "~@")) `unquote-splicing true
  unquoted-form \~ `unquote false
  derefed-form \@ `deref false
  var-inner-r \' `var false)

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

(defvar- dispatched-form
  (prefix-conc
    (lit \#)
    (alt set-inner-r fn-inner-r var-inner-r with-meta-inner-r)))

(defvar- form
  (with-label "a form"
    (prefix-conc
      ws?
      (alt list-r vector-r map-r dispatched-form string-r syntax-quoted-form
           unquote-spliced-form unquoted-form division-symbol character-form
           keyword-r peculiar-symbol symbol-r number-form))))

(use 'clojure.test 'name.choi.joshua.fnparse.hound.test)

(is (full-match? "55.2e2" number-form == 5520.))
(is (full-match? "16rFF" number-form == 255))
(is (full-match? "16" number-form == 16))
(is (full-match? "16." number-form #(isa? (type %) %2) Double))
(is (full-match? "~@a" form = (list `unquote-splicing (`symbol 'a))))
(is (full-match? "16rAZ" (conc number-form ws) == 200))
; (-> "#^{} #{[a b;Comment\nc]}" make-state form prn)
; (-> "#_#_'a'b'c" make-state form prn)
; (-> "#^:monster #{a b c d}" (parse form vector nil) prn)
; (-> "aa\" 2\"]" make-state form println)
; (-> "\"a\\tb\"" make-state form prn)
; (-> "\\t\"" make-state escape-sequence prn)
; (-> "a b;Comment\nc" make-state form-series prn)
; (-> "'a b;Comment\nc" make-state reader-macro prn)
