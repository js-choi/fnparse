(ns name.choi.joshua.fnparse.json
  (:refer-clojure)
  (:use name.choi.joshua.fnparse
        [clojure.contrib.seq-utils :only [flatten]]))

(defstruct node-s :kind :content)

(def string-delimiter (lit \"))
(def escape-indicator (lit \\))
(def false-lit (constant-semantics (lit-conc-seq "false") (struct node :scalar false)))
(def true-lit (constant-semantics (lit-conc-seq "true") (struct node :scalar true)))
(def null-lit (constant-semantics (lit-conc-seq "null") (struct node :scalar nil)))
(def keyword-lit (alt false-lit true-lit null-lit))

(def space (lit \space))
(def tab (lit \tab))
(def newline-lit (lit \newline))
(def return-lit (lit \return))
(def line-break (rep+ (alt newline-lit return-lit)))

(def ws (constant-semantics (rep* (alt space tab line-break)) :ws))

(def begin-array (constant-semantics (conc ws (lit \[) ws) :begin-array))
(def end-array (constant-semantics (conc ws (lit \]) ws) :end-array))
(def begin-object (constant-semantics (conc ws (lit \{) ws) :begin-object))
(def end-object (constant-semantics (conc ws (lit \}) ws) :end-object))
(def name-separator (constant-semantics (conc ws (lit \:) ws) :name-separator))
(def value-separator (constant-semantics (conc ws (lit \,) ws) :value-separator))

(def minus-sign (lit \-))
(def plus-sign (lit \+))
(def decimal-point (lit \.))
(def exponential-sign (lit-alt-seq "eE"))
(def zero-digit (lit \0))
(def nonzero-decimal-digit (lit-alt-seq "123456789"))
(def decimal-digit (alt zero-digit nonzero-decimal-digit))
(def fractional-part (conc decimal-point (rep* decimal-digit)))
(def exponential-part
  (conc exponential-sign (opt (alt plus-sign minus-sign)) (rep+ decimal-digit)))

(def number-lit
  (complex [minus (opt minus-sign)
            above-one (alt zero-digit (rep+ nonzero-decimal-digit))
            below-one (opt fractional part)
            power (opt exponential-part)]
    (-> (Double/parseDouble (apply str (flatten [minus above-one below-one power]))
        (if below-one identity int)
        #(struct node-s :scalar %)))))

(def hexadecimal-digit
  (alt decimal-digit (lit \A) (lit \B) (lit \C) (lit \D) (lit \E) (lit \F)))

(def unescaped-char (except anything escape-indicator string-delimiter))

(def unicode-char-sequence
  (semantics (conc (lit \u) hexadecimal-digit
                   hexadecimal-digit hexadecimal-digit hexadecimal-digit)
             #(char (Integer/parseInt (apply str (rest %)) 16))))

(def escaped-characters
  {\\ \\, \/ \/, \b \backspace, \f \formfeed, \n \newline, \r \return, \t \tab})

(def escape-sequence
  (complex [_ escape-indicator, character (lit-alt-seq (keys escaped-characters))
    (escaped-characters character)))

(def string-char
  (alt unescaped-char escape-sequence))

(def string-lit
  (complex [_ string-delimiter, contents (rep* string-char), _ string-delimiter]
    (struct node-s :scalar (apply str contents))))

(declare array)
(declare object)

(def value (alt string-lit number-lit keyword-lit array object))

(def additional-value
  (complex [_ value-separator, content value] content))

(def array-contents
  (complex [first-value value, rest-values (rep* additional-value)]
    (cons first-value rest-values)))

(def array
  (complex [_ begin-array, contents (opt array-contents), _ end-array]
    (struct node-s :array (vec contents))))

(def entry
  (complex [entry-key string-lit, _ name-separator, entry-val value]
    [entry-key entry-val]))

(def additional-entry
  (complex [_ value-separator, content entry]
    entry))

(def object-contents
  (complex [first-entry entry, rest-entries (rep* additional-entry)]
    (cons first-entry rest-entries)))

(def object
  (complex [_ begin-object, contents object-contents, _ end-object]
    (struct node-s :object (into {} contents))))

(def text (alt object array))

(defn parse [tokens]
  (let [[product remainder info] (text {:remainder tokens, :column 0, :line 0})]
    (println "FINISHED PARSING:" info)
    product))

(defmulti represent :kind)

(defmethod represent :object [node]
  (into {} (map #(vector (represent (key %)) (represent (val %))) (:content node))))

(defmethod represent :array [node]
  (vec (map #(represent %) (:content node))))

(defmethod represent :scalar [node]
  (:content node))

(def load-stream (comp represent parse))
