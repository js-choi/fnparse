(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound clojure.contrib.seq-utils))

; TODO
; Radix bases and hexadecimal digits in integers.
; Namespace-qualified symbols.
; The qualified division symbol.
; Complete character codes.

(declare object)

(def ws-set (set " \t\n"))
(def ws (rep* (term "whitespace" ws-set)))
(def non-ws-char (antiterm "non-whitespace char" ws-set))

(def symbol-r
  (complex [first-letter ascii-letter, other-chars (rep* non-ws-char)]
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
  (complex [_ (lit \'), content #'object]
    (list `quote content)))

(def character-codes
  {"newline" \newline, "space" \space, "tab" \tab, "backspace" \backspace})
(def character-r
  (complex [_ (lit \\)
            content (apply alt (map mapconc (keys character-codes)))]
    (character-codes (apply str content))))

(def object
  (alt string-r quoted-object division-symbol character-r symbol-r decimal-number))

(-> "'\\space" make-state object println)
