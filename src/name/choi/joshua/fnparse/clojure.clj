(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound clojure.set clojure.template
        clojure.contrib.seq-utils))

; TODO
; Radix bases and hexadecimal digits in integers.
; Namespace-qualified symbols.
; The qualified division symbol.
; Unicode character codes.
; Keyword-specific restrictions.

(declare object)

(def ws-set (set " ,\t\n"))
(def indicator-set (set ";()[]{}\\'@^`#"))
(def separator-set (union ws-set indicator-set))
(def ws (rep* (term "whitespace" ws-set)))
(def symbol-char (antiterm "symbol char" separator-set))
(def object-end (followed-by (term "whitespace or indicator" separator-set)))

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

(def quoted-object
  (apply alt (map #(complex [_ (lit (key %)), content #'object]
                     (list (val %) content))
               {\' `quote, \` `syntax-quote})))

(def character-name
  (mapalt #(constant-semantics (mapconc (val %)) (key %))
    char-name-string))

(def character-r
  (complex [_ (lit \\), content character-name]
    content))

(def special-symbol
  (lex (invisi-conc
         (mapalt #(constant-semantics (mapconc (key %)) (val %))
           {"nil" nil, "true" true, "false" false})
         object-end)))

(def keyword-r
  (complex [_ (lit \:), content symbol-r]
    content))

(def object-series
  (complex [_ ws, contents (rep* (invisi-conc #'object ws))]
    contents))

(do-template [rule-name start-token end-token product-fn]
  (def rule-name
    (complex [_ (lit start-token)
              contents object-series
              _ (with-label (format "%s, object or comment" end-token)
                  (lit end-token))]
      (product-fn contents)))
  list-r \( \) list*
  vector-r \[ \] vec
  map-r \{ \} #(apply hash-map %)
  set-inner-r \{ \} set)

(def object
  (with-label "object or comment"
    (alt list-r vector-r map-r string-r quoted-object division-symbol character-r keyword-r special-symbol symbol-r decimal-number)))

(-> "[a b}" make-state object println)
