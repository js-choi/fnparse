(ns name.choi.joshua.fnparse.json
  (:refer-clojure)
  (:use name.choi.joshua.fnparse))

(defstruct node :kind :content)

(def string-delimiter (lit \"))
(def escape-indicator (lit \\))
(def false-lit (constant-semantics (lit-conc-seq "false") (struct node :scalar false)))
(def true-lit (constant-semantics (lit-conc-seq "true") (struct node :scalar true)))
(def null-lit (constant-semantics (lit-conc-seq "null") (struct node :scalar nil)))
(def keyword-lit (alt false-lit true-lit null-lit))

(def ws (rep* (apply alt (map lit [\space \tab \newline \return]))))

(def begin-array (constant-semantics (conc ws (lit \[) ws) :begin-array))
(def end-array (constant-semantics (conc ws (lit \]) ws) :end-array))
(def begin-object (constant-semantics (conc ws (lit \{) ws) :begin-object))
(def end-object (constant-semantics (conc ws (lit \}) ws) :end-object))
(def name-separator (constant-semantics (conc ws (lit \:) ws) :name-separator))
(def value-separator (constant-semantics (conc ws (lit \,) ws) :value-separator))

(def minus-sign (lit \-))
(def plus-sign (lit \+))
(def decimal-point (lit \.))
(def exponential-sign (alt (lit \e) (lit \E)))
(def zero-digit (lit \0))
(def nonzero-decimal-digit
  (alt (lit \1) (lit \2) (lit \3) (lit \4) (lit \5) (lit \6) (lit \7)
       (lit \8) (lit \9)))
(def decimal-digit (alt zero-digit nonzero-decimal-digit))
(def fractional-part (conc decimal-point (rep* decimal-digit)))
(def exponential-part
  (conc exponential-sign (opt (alt plus-sign minus-sign)) (rep+ decimal-digit)))

(def number-lit
  (semantics
    (conc (opt minus-sign) (alt zero-digit (rep+ nonzero-decimal-digit))
          (opt fractional-part) (opt exponential-part))
    (fn [product]
        (if (or (product 2) (product 3))
            (hash-map :kind :scalar, :content (Double/parseDouble
                                      (apply str (flatten product))))
            (hash-map :kind :scalar, :content (Integer/parseInt
                                        (apply str (flatten product))))))))

(def hexadecimal-digit
  (alt decimal-digit (lit \A) (lit \B) (lit \C) (lit \D) (lit \E) (lit \F)))

(def unescaped-char (term #(and (not= % \\) (not= % \"))))

(def unicode-char-sequence
  (semantics (conc (lit \u) hexadecimal-digit
                   hexadecimal-digit hexadecimal-digit hexadecimal-digit)
             #(char (Integer/parseInt (apply str (rest %)) 16))))

(defn escape-sequence-rule
  "Creates a rule for escape sequences--that is, the escape indicator followed by
  the given escaped character, together turning into the given new character. The
  new character is the same given escaped character by default."
  ([escaped-character]
   (escape-sequence-rule escaped-character escaped-character))
  ([escaped-character new-character]
   (semantics (lit escaped-character)
              (fn [_] new-character))))

(def escape-sequence
  (semantics
    (conc escape-indicator
          (alt (escape-sequence-rule \")
               (escape-sequence-rule \\)
               (escape-sequence-rule \/)
               (escape-sequence-rule \b \backspace)
               (escape-sequence-rule \f \formfeed)
               (escape-sequence-rule \n \newline)
               (escape-sequence-rule \r \return)
               (escape-sequence-rule \t \tab)
               (escape-sequence-rule \\)
               unicode-char-sequence))
    #(% 1)))

(def string-char
  (alt unescaped-char escape-sequence))

(def string-lit
  (semantics (conc string-delimiter (rep* string-char) string-delimiter)
             #(hash-map :kind :scalar, :content (apply str (% 1)))))

(declare array)
(declare object)

(defn value [tokens]
  (some #(% tokens) [string-lit number-lit keyword-lit array object]))

(def additional-value
  (semantics (conc value-separator value) #(% 1)))

(def array-contents
  (semantics (conc value (rep* additional-value))
             #(into [(% 0)] (% 1))))

(def array
  (semantics (conc begin-array (opt array-contents) end-array)
             #(hash-map :kind :array, :content (vec (% 1)))))

(def entry
  (semantics (conc string-lit name-separator value)
             #(vector (% 0) (% 2))))

(def additional-entry
  (semantics (conc value-separator entry) #(% 1)))

(def object-contents
  (semantics (conc entry (rep* additional-entry))
             #(into [(% 0)] (% 1))))

(def object
  (semantics (conc begin-object (opt object-contents) end-object)
             #(hash-map :kind :object, :content (into {} (% 1)))))

(def text (alt object array))

(def lex seq)

(defn parse [tokens]
  (let [[product remainder] (text tokens)]
    product))

(defmulti represent :kind)

(defmethod represent :object [node]
  (into {} (map #(vector (represent (key %)) (represent (val %))) (:content node))))

(defmethod represent :array [node]
  (vec (map #(represent %) (:content node))))

(defmethod represent :scalar [node]
  (:content node))

(def load-stream (comp represent parse lex))
