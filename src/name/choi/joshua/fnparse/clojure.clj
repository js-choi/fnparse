(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound clojure.contrib.seq-utils))

(def ws-set (set " \t\n"))
(def ws (rep* (term "whitespace" ws-set)))
(def non-ws-char (antiterm "non-whitespace char" ws-set))

(def symbol-r
  (complex [first-letter ascii-letter, other-chars (rep* non-ws-char)]
    (->> other-chars (cons first-letter) (apply str) symbol)))

(let [decimal-digits (rep+ decimal-digit)
      optional-sign (opt (set-lit "plus or minus sign" "+-"))
      digits-to-int #(->> % (apply str) Integer/parseInt)]
  (def decimal-number
    (complex [sign optional-sign
              body decimal-digits
              tail (alt (conc (lit \/) decimal-digits)
                        (conc (opt (lit \.) decimal-digits)
                              (opt (conc (set-lit "exponent sign" "eE")
                                         optional-sign decimal-digits))))]
      (let [signed-body (cons sign body)]
        (if-not tail
          (digits-to-int signed-body)
          (if (= (first tail) \/)
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

(def object (alt string-r symbol-r decimal-number))

(-> "\"a3\\t5. \"" make-state object println)
