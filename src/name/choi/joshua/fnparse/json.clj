(ns name.choi.joshua.fnparse.json
  (:use name.choi.joshua.fnparse clojure.contrib.error-kit
        clojure.contrib.test-is
        [clojure.contrib.seq-utils :only [flatten]])
  (:require [name.choi.joshua.fnparse :as fnparse]))

(defstruct node-s :kind :content) 
  ; A JSON node, which what the parsing will return in the end.

(def make-node
  (partial struct node-s))

(def make-scalar-node
  (partial make-node :scalar))

(def make-array-node
  (partial make-node :array))

(def make-object-node
  (partial make-node :object))

(def apply-str
  (partial apply str))

;; The functions below just convert JSON nodes into Clojure strings,
;; vectors, and maps.

(defmulti represent :kind)

(defmethod represent :object [node]
  (into {}
    (map #(vector (represent (key %)) (represent (val %)))
      (:content node))))

(defmethod represent :array [node]
  (vec (map #(represent %) (:content node))))

(defmethod represent :scalar [node]
  (:content node))

(defn- make-mock-state [tokens warnings column line]
  (state-context standard-template
    (make-state-with-info (seq tokens)
      :warnings warnings, :line line, :column column)))

;; These two functions are given a rule and make it so that it
;; increments the current column (or the current line).

(defn- nb-char [subrule]
  (invisi-conc subrule (update-info :column inc)))

(def nb-char-lit
  (comp nb-char lit))

(defn- b-char [subrule]
  (invisi-conc subrule (update-info :line inc)))

;; A couple of parse errors have been put here and there. It's nowhere
;; near complete, but rather it's to show examples of how to implement
;; errors.

(deferror parse-error [] [state message message-args]
  {:msg (str (format "JSON error at line %s, column %s: "
               (:line state) (:column state))
             (apply format message message-args))
   :unhandled (throw-msg Exception)})

(defn- expectation-error-fn [expectation]
  (fn [remainder state]
    (raise parse-error state "%s expected where \"%s\" is"
      [expectation (or (first remainder) "the end of the file")])))

;; And here are where this parser's rules are defined.

(def string-delimiter
  (nb-char-lit \"))

(def escape-indicator
  (nb-char-lit \\))

(def false-lit
  (constant-semantics (lit-conc-seq "false" nb-char-lit)
    (make-scalar-node false)))

(def true-lit
  (constant-semantics (lit-conc-seq "true" nb-char-lit)
    (make-scalar-node true)))

(def null-lit
  (constant-semantics (lit-conc-seq "null" nb-char-lit)
    (make-scalar-node nil)))

(def keyword-lit (alt false-lit true-lit null-lit))

(def space (nb-char-lit \space))

(def tab (nb-char-lit \tab))

(def newline-lit (lit \newline))

(def return-lit (lit \return))

(def line-break (b-char (rep+ (alt newline-lit return-lit))))

(def json-char (alt line-break (nb-char anything)))

(def ws (constant-semantics (rep* (alt space tab line-break)) :ws))

(def begin-array
  (constant-semantics (conc ws (nb-char-lit \[) ws) :begin-array))
(def end-array
  (constant-semantics (conc ws (nb-char-lit \]) ws) :end-array))

(def begin-object
  (constant-semantics (conc ws (nb-char-lit \{) ws) :begin-object))

(def end-object
  (constant-semantics (conc ws (nb-char-lit \}) ws) :end-object))

(def name-separator
  (constant-semantics (conc ws (nb-char-lit \:) ws) :name-separator))

(def value-separator
  (constant-semantics (conc ws (nb-char-lit \,) ws) :value-separator))

(def minus-sign (nb-char-lit \-))

(def plus-sign (nb-char-lit \+))

(def decimal-point (nb-char-lit \.))

(def exponential-sign (lit-alt-seq "eE" nb-char-lit))

(def zero-digit (nb-char-lit \0))

(def nonzero-decimal-digit (lit-alt-seq "123456789" nb-char-lit))

(def decimal-digit (alt zero-digit nonzero-decimal-digit))

(def fractional-part (conc decimal-point (rep* decimal-digit)))

(def exponential-part
  (conc exponential-sign (opt (alt plus-sign minus-sign))
        (failpoint (rep+ decimal-digit)
          (expectation-error-fn
            (str "in number literal, after an exponent sign, decimal"
                 "digit")))))

(with-test
  (def number-lit
    (complex [minus (opt minus-sign)
              above-one (alt zero-digit (rep+ nonzero-decimal-digit))
              below-one (opt fractional-part)
              power (opt exponential-part)]
      (-> [minus above-one below-one power] flatten apply-str
        Double/parseDouble
        ((if (or below-one power) identity int))
        make-scalar-node)))
  (is (= (number-lit (make-mock-state "123]" [] 3 4))
         [(make-node :scalar 123) (make-mock-state "]" [] 6 4)]))
  (is (= (number-lit (make-mock-state "-123]" [] 3 4))
         [(make-node :scalar -123) (make-mock-state "]" [] 7 4)]))
  (is (= (number-lit (make-mock-state "-123e3]" [] 3 4))
         [(make-node :scalar -123e3) (make-mock-state "]" [] 9 4)]))
  (is (= (number-lit (make-mock-state "-123.9e3]" [] 3 4))
         [(make-node :scalar -123.9e3) (make-mock-state "]" [] 11 4)])))
;  (is (thrown-with-msg? Exception
;        #"JSON error at line 4, column 10: in number literal, after an exponent sign, decimal digit expected where \"e\" is"
;        (number-lit (make-mock-state "-123.9ee3]" [] 3 4)))))

(def hexadecimal-digit
  (alt decimal-digit (lit-alt-seq "ABCDEF" nb-char-lit)))

(def unescaped-char
  (except json-char (alt escape-indicator string-delimiter)))

(with-test
  (def unicode-char-sequence
    (complex [_ (nb-char-lit \u)
                digits (factor= 4
                         (failpoint hexadecimal-digit
                           (expectation-error-fn "hexadecimal digit")))]
      (-> digits apply-str (Integer/parseInt 16) char)))
  (is (= (unicode-char-sequence (make-mock-state "u11A3a\"]" [] 3 4))
         [\u11A3 (make-mock-state (seq "a\"]") [] 8 4)]))
  (is (thrown? Exception
        (unicode-char-sequence (make-mock-state "u11ATa\"]" [] 3 4)))))

(def escaped-characters
  {\\ \\, \/ \/, \b \backspace, \f \formfeed, \n \newline, \r \return,
   \t \tab})

(def normal-escape-sequence
  (semantics (lit-alt-seq (keys escaped-characters) nb-char-lit)
    escaped-characters))

(def escape-sequence
  (complex [_ escape-indicator
            character (alt unicode-char-sequence
                           normal-escape-sequence)]
    character))

(def string-char
  (alt escape-sequence unescaped-char))

(def string-lit
  (complex [_ string-delimiter
            contents (rep* string-char)
            _ string-delimiter]
    (-> contents apply-str make-scalar-node)))

(declare array object)

(def value (alt string-lit number-lit keyword-lit array object))

(def additional-value
  (complex [_ value-separator, content value] content))

(def array-contents
  (complex [first-value value, rest-values (rep* additional-value)]
    (cons first-value rest-values)))

(def array
  (complex [_ begin-array
            contents (opt array-contents)
            _ (failpoint end-array
                (expectation-error-fn "an array is unclosed; \"]\""))]
    (-> contents vec make-array-node)))

(with-test
  (def entry
    (complex [entry-key string-lit, _ name-separator, entry-val value]
      [entry-key entry-val]))
  (is (= (entry (make-mock-state "\"hello\": 55}" [] 3 4))
         [[(make-node :scalar "hello") (make-node :scalar 55)]
          (make-mock-state "}" [] 14 4)])))

(def additional-entry
  (complex [_ value-separator, content entry]
    content))

(def object-contents
  (complex [first-entry entry, rest-entries (rep* additional-entry)]
    (cons first-entry rest-entries)))

(with-test
  (def object
    (complex [_ begin-object
              contents object-contents
              _ (failpoint end-object
                  (expectation-error-fn
                    (str "either \"}\" or another object entry (which "
                         "always starts with a string)")))]
      (struct node-s :object (into {} contents))))
  (is (= (object (make-mock-state "{\"hello\": 55}]" [] 3 4))
         [(make-node :object
          {(make-node :scalar "hello")
             (make-node :scalar 55)})
          (make-mock-state "]" [] 16 4)]))
  (is (= (object (make-mock-state
                   "{\"hello\": 55, \"B\": \"goodbye\"}]"
                   [] 3 4))
         [(make-node :object
          {(make-node :scalar "hello") (make-node :scalar 55)
           (make-node :scalar "B") (make-node :scalar "goodbye")})
          (make-mock-state "]" [] 32 4)])))

(def text (alt object array)) ; The root rule

;; The functions below uses the rules to parse strings.

(defn parse [tokens]
  (state-context standard-template
    (match-rule text
      #(raise parse-error %
         "invalid document \"%s\""
         (apply-str (fetch-remainder %)))
      (fn [product new-state old-state]
        (raise parse-error "leftover data '%s' after a valid node '%s'"
          (apply-str (fetch-remainder new-state))
          product))
      tokens)))

(with-test
  (def load-stream (comp represent parse))
  (is (= (load-stream "[11]") [11]))
  (is (= (load-stream "[1, 2, 3]") [1 2 3])
      "loading a flat array containing integers")
  (is (= (load-stream "[\"a\", \"b\\n\", \"\\u1234\"]")
         ["a" "b\n" "\u1234"])
      "loading a flat array containing strings")
  (is (= (load-stream "{\"a\": 1, \"b\\n\": 2, \"\\u1234\": 3}")
         {"a" 1, "b\n" 2, "\u1234" 3})
      "loading a flat object containing strings and integers"))
