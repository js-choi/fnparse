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

(def comment-symbol (gensym "comment"))
(def ws-set (set " ,\t\n"))
(def indicator-set (set ";()[]{}\\\"'@^`#"))
(def separator-set (union ws-set indicator-set))
(def ws (rep+ (term "whitespace" ws-set)))
(def ws? (opt ws))
(def indicator (term "indicator" indicator-set))
(def symbol-char (antiterm "symbol char" separator-set))
(def obj-end (alt (followed-by (alt ws indicator)) end-of-input))

(def symbol-r
  (complex [first-letter ascii-letter, other-chars (rep* symbol-char)]
    (->> other-chars (cons first-letter) (apply str) symbol)))

(def division-symbol (constant-semantics (lit \/) '/))

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
  (semantics (prefix-conc (lit \\) (set-lit "valid escape sequence"
                                     (keys escape-sequence-map)))
    escape-sequence-map))
(def string-r
  (semantics (circumfix-conc string-delimiter
                             (rep* (alt escape-sequence (antilit \")))
                             string-delimiter)
    #(->> % flatten (apply str))))

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
  (semantics (prefix-conc (mapconc "~@") #'obj)
    #(list `unquote-splicing %)))

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
  (semantics (suffix-conc (rep* (prefix-conc ws? #'obj)) ws?)
    (partial remove #(= % comment-symbol))))

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

(def comment-r
  (constant-semantics (conc (lit \;) (rep* (antilit \newline)))
    comment-symbol))

(def dispatched-form
  (prefix-conc
    (lit \#)
    (mapalt #(prefix-conc (lit (key %)) (val %))
      {\' (semantics #'obj #(list `var %))})))

(def obj
  (with-label "object or comment"
    (alt list-r vector-r map-r string-r comment-r dispatched-form quoted-obj syntax-quoted-obj (lex unquote-spliced-obj) unquoted-obj derefed-obj division-symbol character-r keyword-r (lex special-symbol) symbol-r decimal-number)))

(-> "#'[a b;Comment\nc]" make-state obj prn)
; (-> "aa\" 2\"]" make-state obj println)
; (-> "\"a\\tb\"" make-state obj prn)
; (-> "\\t\"" make-state escape-sequence prn)
; (-> "a b;Comment\nc" make-state obj-series prn)
