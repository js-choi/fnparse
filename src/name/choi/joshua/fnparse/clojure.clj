(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound clojure.set clojure.template
        clojure.contrib.def clojure.contrib.seq-utils))

; TODO
; Radix bases and hexadecimal digits in integers.
; Namespace-qualified symbols.
; The qualified division symbol.
; Unicode character codes.
; Keyword-specific restrictions.

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
    (->> other-chars (cons first-letter) (apply str) symbol)))

(defvar- symbol-r (alt division-symbol normal-symbol))

(defvar- decimal-digits (rep+ decimal-digit))
(defvar- optional-sign (opt (set-lit "plus or minus sign" "+-")))
(defn- digits-to-int [digit-chars]
  (->> digit-chars (apply str) Integer/parseInt))

(defvar- character-name
  (mapalt #(constant-semantics (mapconc (val %)) (key %))
    char-name-string))

(defvar- character-form (prefix-conc (lit \\) character-name))

(defvar- special-form
  (suffix-conc
    (mapalt #(constant-semantics (mapconc (key %)) (val %))
      {"nil" nil, "true" :true, "false" false})
    form-end))

(defvar- keyword-r
  (complex [_ (lit \:), content symbol-r]
    content))

(defvar- decimal-number
  (complex [sign optional-sign
            body decimal-digits
            tail (alt (opt (conc (lit \/) decimal-digits))
                      (opt (conc (set-lit "radix sign" "rR") decimal-digits))
                      (conc (opt (conc (lit \.) decimal-digits))
                            (opt (conc (set-lit "exponent sign" "eE")
                                       optional-sign decimal-digits))))]
    (let [signed-body (cons sign body)
          first-tail-token (first tail)]
      (if-not (or tail (= first-tail-token \r))
        (digits-to-int (concat signed-body tail))
        (if (= first-tail-token \/)
          (/ (digits-to-int signed-body) (digits-to-int (next tail)))
          (->> tail (concat signed-body) (apply str)
            Double/parseDouble))))))

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

(defn- prefix-list-fn [prefix-form]
  #(list prefix-form %))

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
  map-r)

(defvar- with-meta-inner-r
  (prefix-conc
    (padded-lit \^)
    (complex [metadata metadata-r, _ ws?, content #'form]
      (list `with-meta content metadata-r))))

(defvar- dispatched-form
  (prefix-conc
    (lit \#)
    (alt set-inner-r fn-inner-r var-inner-r with-meta-inner-r)))

(defvar- form
  (with-label "a form"
    (prefix-conc
      ws?
      (alt list-r vector-r map-r dispatched-form string-r syntax-quoted-form unquote-spliced-form unquoted-form division-symbol character-form keyword-r (lex special-form) symbol-r decimal-number))))
;       (alt string-r dispatched-form quoted-form syntax-quoted-form (lex unquote-spliced-form) unquoted-form derefed-form division-symbol character-form keyword-r (lex special-form) symbol-r decimal-number))))

; (-> "#^{} #{[a b;Comment\nc]}" make-state form prn)
; (-> "#_#_'a'b'c" make-state form prn)
(-> "#{a b c d}" make-state form prn)
; (-> "aa\" 2\"]" make-state form println)
; (-> "\"a\\tb\"" make-state form prn)
; (-> "\\t\"" make-state escape-sequence prn)
; (-> "a b;Comment\nc" make-state form-series prn)
; (-> "'a b;Comment\nc" make-state reader-macro prn)
