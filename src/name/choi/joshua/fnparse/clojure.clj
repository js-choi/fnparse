(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound clojure.set clojure.template
        clojure.contrib.seq-utils))

; TODO
; Radix bases and hexadecimal digits in integers.
; Namespace-qualified symbols.
; The qualified division symbol.
; Unicode character codes.
; Keyword-specific restrictions.

(declare obj)

(def ws-set (set " ,\t\n"))
(def indicator-set (set ";()[]{}\\'@^`#"))
(def separator-set (union ws-set indicator-set))
(def comment-r
  (with-label "comment" (conc (lit \;) (rep* (antilit \newline)))))
(def ws (rep+ (alt (term "whitespace" ws-set) comment-r)))
(def ws? (opt ws))
(def indicator (term "indicator" indicator-set))
(def symbol-char (antiterm "symbol char" separator-set))
(def obj-end (alt (followed-by (alt ws indicator)) end-of-input))

(def symbol-r
  (complex [first-letter ascii-letter, other-chars (rep* symbol-char)]
    (->> other-chars (cons first-letter) (apply str) symbol)))

(def division-symbol
  (constant-semantics (lit \/) '/))

(let [decimal-digits (rep+ decimal-digit)
      optional-sign (opt (set-lit "plus or minus sign" "+-"))
      digits-to-int #(->> % (apply str) Integer/parseInt)]
  (def decimal-number
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
              Double/parseDouble)))))))

(def string-delimiter (lit \"))
(def escape-sequence-map
  {\t \tab
   \n \newline
   \\ \\
   \" \"})
(def escape-sequence
  (complex [_ (lit \\)
            sequence (set-lit "valid escape sequence"
                       (keys escape-sequence-map))]
    (escape-sequence-map sequence)))
(def string-r
  (complex [_ string-delimiter
            content (rep* (alt escape-sequence (antilit \")))
            _ string-delimiter]
    (->> content flatten (apply str))))

(do-template [rule-name prefix-char product-fn-symbol]
  (def rule-name
    (complex [_ (lit prefix-char), content #'obj]
      (list product-fn-symbol content)))
  quoted-obj \' `quote
  syntax-quoted-obj \` `syntax-quote
  unquoted-obj \~ `unquote
  derefed-obj \@ `deref
  var-inner-r \' `var)

(def unquote-spliced-obj
  (complex [_ (mapconc "~@"), content #'obj]
    (list `unquote-splicing content)))

(def character-name
  (mapalt #(constant-semantics (mapconc (val %)) (key %))
    char-name-string))

(def character-r
  (complex [_ (lit \\), content character-name]
    content))

(def special-symbol
  (suffix-conc
    (mapalt #(constant-semantics (mapconc (key %)) (val %))
      {"nil" nil, "true" :true, "false" false})
    obj-end))

(def keyword-r
  (complex [_ (lit \:), content symbol-r]
    content))

(def obj-series
  (circumfix-conc ws? (separated-rep ws #'obj) ws?))

(do-template [rule-name start-token end-token product-fn]
  (def rule-name
    (complex [_ (lit start-token)
              contents (opt obj-series)
              _ (with-label (format "%s or obj" end-token)
                  (lit end-token))]
      (product-fn contents)))
  list-r \( \) list*
  vector-r \[ \] vec
  map-r \{ \} #(apply hash-map %)
  set-inner-r \{ \} set)

(def obj
  (with-label "obj"
    (alt list-r vector-r map-r string-r quoted-obj syntax-quoted-obj (lex unquote-spliced-obj) unquoted-obj derefed-obj division-symbol character-r keyword-r (lex special-symbol) symbol-r decimal-number)))

; (-> "~@[a b;Comment\nc]" make-state ((lex unquote-spliced-obj)) prn)
; (-> "false]" make-state ((alt (lex special-symbol))) prn)
; (-> "" make-state obj-end prn)
(-> "a b;Comment\nc" make-state obj-series prn)
