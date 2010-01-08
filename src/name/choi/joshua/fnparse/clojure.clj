(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound clojure.set clojure.template
        clojure.contrib.seq-utils))

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

(defvar- symbol-r
  (complex [first-letter ascii-letter, other-chars (rep* symbol-char)]
    (->> other-chars (cons first-letter) (apply str) symbol)))

(defvar- division-symbol (constant-semantics (lit \/) '/))

(let [decimal-digits (rep+ decimal-digit)
      optional-sign (opt (set-lit "plus or minus sign" "+-"))
      digits-to-int #(->> % (apply str) Integer/parseInt)]
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
              Double/parseDouble)))))))

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
(defvar- string-r
  (semantics (suffix-conc (rep* (alt escape-sequence (antilit \")))
                          string-delimiter)
    #(->> % flatten (apply str))))

(do-template [rule-name prefix-char product-fn-symbol]
  (defvar- rule-name
    (complex [_ (lit prefix-char), content #'form]
      (list product-fn-symbol content)))
  quoted-form \' `quote
  syntax-quoted-form \` `syntax-quote
  unquoted-form \~ `unquote
  derefed-form \@ `deref
  var-inner-r \' `var)

(defvar- unquote-spliced-form
  (semantics (prefix-conc (mapconc "~@") #'form)
    #(list `unquote-splicing %)))

(defvar- character-name
  (mapalt #(constant-semantics (mapconc (val %)) (key %))
    char-name-string))

(defvar- character-r
  (complex [_ (lit \\), content character-name]
    content))

(defvar- special-symbol
  (suffix-conc
    (mapalt #(constant-semantics (mapconc (key %)) (val %))
      {"nil" nil, "true" :true, "false" false})
    form-end))

(defvar- keyword-r
  (complex [_ (lit \:), content symbol-r]
    content))

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

(defvar- dispatched-form
  (prefix-conc
    (lit \#)
    (template-alt [label prefix-token body]
      (with-label label (prefix-conc (lit prefix-token) body))
      "a set form" \{
        (semantics (suffix-conc form-series (lit \})) set)
      "a mini-function" \(
        (semantics (suffix-conc form-series (lit \))) #(list `mini-fn %))
      "a var-quoted form" \'
        (semantics #'form #(list `var %))
      "an form with metadata" \^
        (complex [metadata (alt map-r symbol-r keyword-r)
                  _ ws?
                  base-form #'form]
          (list `with-meta base-form metadata)))))

(defn- add-head [f]
  #(list f %))

(defn- head-prefixed-form [f body]
  (semantics body (add-head f)))

(defn- delimited-form-series [end-token]
  (suffix-conc form-series (with-label (format "a %s or form" end-token)
                             (lit end-token))))

(defvar- reader-macro
  (template-alt [label prefix-token body]
    (with-label label (prefix-conc (lit prefix-token) body))
    "quoted form" \' (head-prefixed-form `quote #'form)
    "derefed form" \@ (head-prefixed-form `deref #'form)
    "syntax-quoted form" \` (head-prefixed-form `syntax-quote #'form)
    "unquoted form" \~ (head-prefixed-form `unquote #'form)
    "list form" \( (semantics (delimited-form-series \)) list*)
    "vector form" \[ (semantics (delimited-form-series \]) vec)
    "map form" \{ (semantics (delimited-form-series \}) #(apply hash-map %))))

(defvar- form
  (with-label "a form"
    (prefix-conc
      ws?
      (alt dispatched-form reader-macro syntax-quoted-form (lex unquote-spliced-form) unquoted-form division-symbol character-r keyword-r (lex special-symbol) symbol-r decimal-number))))
;       (alt string-r dispatched-form quoted-form syntax-quoted-form (lex unquote-spliced-form) unquoted-form derefed-form division-symbol character-r keyword-r (lex special-symbol) symbol-r decimal-number))))

; (-> "#^{} #{[a b;Comment\nc]}" make-state form prn)
; (-> "#_#_'a'b'c" make-state form prn)
(-> "{a b c d}" make-state form prn)
; (-> "aa\" 2\"]" make-state form println)
; (-> "\"a\\tb\"" make-state form prn)
; (-> "\\t\"" make-state escape-sequence prn)
; (-> "a b;Comment\nc" make-state form-series prn)
; (-> "'a b;Comment\nc" make-state reader-macro prn)
