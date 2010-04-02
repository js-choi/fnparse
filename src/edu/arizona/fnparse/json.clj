(ns edu.arizona.fnparse.json
  "Contains a parser for [the JSON language][JSON], or
  JavaScript Object Notation. It is a simple language for
  storing simple data structures: numbers, strings,
  \"arrays\" (i.e. vectors), and \"objects\" (i.e. maps).
  
  The formal grammar can be seen in pictoral format
  at [JSON's homepage][JSON] or in textual format in
  [RFC 4627][RFC].
  
  [JSON]: http://json.org
  [RFC]: http://www.ietf.org/rfc/rfc4627"
  (:require [edu.arizona.fnparse [hound :as p] [core :as c]]
            [clojure.set :as set]
            [clojure.contrib [seq :as seq] [except :as except]])
  (:use [clojure.template :only #{do-template}]
        [clojure.test :only #{set-test is run-tests}])
  (:refer-clojure :exclude #{read-string}))

(defn str* [objects]
  (apply str objects))

(c/defrule <ws?>
  "Optional, ignored JSON whitespace."
  (p/rep* (p/set-term "whitespace" " \t\n\r")))

; Define single-character indicator rules.
; I use `clojure.template/do-template` to reduce repetition.
(do-template [rule-name token]
  (c/defrule rule-name
    "Padded on the front with optional whitespace."
    (p/prefix <ws?> (p/lit token)))
  <escape-char-start> \\
  <str-delimiter>   \"
  <value-separator> \,
  <name-separator>  \:
  <array-start>     \[
  <array-end>       \]
  <object-start>    \{
  <object-end>      \})

; Define special value rules: true, false, and null.
; Again, I use `clojure.template/do-template` to reduce repetition.
(do-template [rule-name tokens product]
  (c/defrule rule-name
    "Padded on the front with optional whitespace."
    (p/prefix <ws?> (p/chook product (p/phrase tokens))))
  <true>  "true"  true
  <false> "false" false
  <null>  "null"  nil)

(c/defrule <control-char>
  "An ASCII control character, which is not allowed in strings."
  (p/chook ::control-char p/<ascii-control>))

(c/defrule <normal-str-char>
  "A normal, non-espaced string character. No control characters allowed."
  {:product "A character."}
  (p/except "a normal string character"
    (fn [subtrahend-prod]
      (when (= subtrahend-prod ::control-char)
        "an illegal, invisible ASCII control character was found in a string"))
    p/<anything>
    (p/+ <str-delimiter> <control-char>)))

(def normal-escape-sequences
  {\" \", \\ \\, \/ \/, \b \backspace, \f \formfeed, \n \newline,
   \r \return, \t \tab})

(defn combine-hexadecimal-digits [digits]
  (reduce #(+ (* 16 %1) %2) digits))

(c/defrule <unicode-sequence>
  "The lowercase u followed by hexadecimal digits."
  {:product "The character with the given digits' Unicode code."}
  (p/prefix
    (p/lit \u)
    (p/hook (comp char combine-hexadecimal-digits)
      (p/factor= 4 p/<hexadecimal-digit>))))

(c/defrule <escaped-str-char>
  "An escaped character in a string: a backslash
  followed by an escape sequence."
  {:product "A character."}
  (p/prefix
    <escape-char-start>
    (p/+ (p/term* "escape sequence" normal-escape-sequences)
         <unicode-sequence>)))

(c/defrule <str-char>
  "A general string character."
  {:product "A character or a sequence of characters."
   :consumes "One character."}
  (p/+ <escaped-str-char> <normal-str-char>))

(c/defrule <str-content>
  "A sequence of string characters."
  {:product "A string.", :consumes "Zero or more characters."}
  (p/hook (comp str* concat) (p/rep* (p/+ <str-char>))))

(c/defrule <str>
  "A JSON string."
  {:product "A string."}
  (p/label "a string"
    (p/circumfix <str-delimiter> <str-content> <str-delimiter>)))

#_(def <nonzero-integer>
  (p/rep ))

(declare <value>)

(c/defrule <array-content>
  "A sequence of JSON values separated by commas, with optional
  whitespace padding on the front."
  {:product "A vector."}
  (p/separated-rep* <value-separator> #'<value>))

(c/defrule <array>
  "A JSON array. Optionally padded on the front with whitespace."
  {:product "A vector."}
  (p/circumfix <array-start> <array-content> <array-end>))

(c/defrule <object-entry>
  "A string-value pair with a colon. They appear in objects.
  Optionally padded on the front with whitespace."
  {:product "A vector pair."}
  (p/for [name <str>, _ <name-separator>, val #'<value>]
    [name val]))

(c/defrule <object-content>
  "A sequence of object entries separated by commas. Optionally
  padded with whitepace on the front."
  (p/hook #(into {} %) (p/separated-rep* <value-separator> <object-entry>)))

(c/defrule <object>
  "A JSON object. Optionally padded on the front with whitespace."
  {:product "A map."}
  (p/circumfix <object-start> <object-content> <object-end>))

(c/defrule <value>
  "A general JSON value, optionally padded with whitespace on the front."
  {:product "A vector, map, number, true, false, or nil."}
  (p/prefix <ws?> (p/+ <object> <array> <str> <true> <false> <null>)))

(c/defrule <document>
  "A general JSON document, optionally padded with whitespace on both sides.
  The root rule of the JSON grammar."
  (p/suffix <value> <ws?>))
