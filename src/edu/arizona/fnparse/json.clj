(ns edu.arizona.fnparse.json
  "Contains a parser for [the JSON language][JSON], or
  JavaScript Object Notation. It is a simple language for
  storing simple data structures: numbers, strings,
  \"arrays\" (i.e. vectors), and \"objects\" (i.e. maps).
  
  The formal grammar can be seen in pictoral format
  at [JSON's homepage][JSON] or in textual format in
  [RFC 4627][RFC].
  
  TODO: Implement numbers!
  
  [JSON]: http://json.org
  [RFC]: http://www.ietf.org/rfc/rfc4627"
  (:require [edu.arizona.fnparse [hound :as h] [core :as c]]
            [clojure.set :as set]
            [clojure.contrib [except :as except]])
  (:use [clojure.template :only #{do-template}]
        [clojure.test :only #{set-test is run-tests}])
  (:refer-clojure :exclude #{read-string}))

(defn str* [objects]
  (apply str objects))

(h/defrule <ws?>
  "Consumes optional, ignored JSON whitespace."
  (h/rep* (h/set-term "whitespace" " \t\n\r")))

; Define single-character indicator rules.
; I use `clojure.template/do-template` to reduce repetition.
(do-template [rule-name token]
  (h/defrule rule-name
    "Padded on the front with optional whitespace."
    (h/lit token))
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
  (h/defrule rule-name
    "Padded on the front with optional whitespace."
    (h/prefix <ws?> (h/chook product (h/phrase tokens))))
  <true>  "true"  true
  <false> "false" false
  <null>  "null"  nil)

(h/defrule <control-char>
  "Consumes an ASCII control character, which is not allowed in strings."
  (h/chook ::control-char h/<ascii-control>))

(h/defrule <normal-str-char>
  "Consumes normal, non-espaced string character.
  No control characters allowed."
  {:product "A character."}
  (h/label "a normal string character"
    (h/except h/<anything> <str-delimiter> <control-char>)))

(def normal-escape-sequences
  {\" \", \\ \\, \/ \/, \b \backspace, \f \formfeed, \n \newline,
   \r \return, \t \tab})

(defn combine-hexadecimal-digits [digits]
  (reduce #(+ (* 16 %1) %2) digits))

(h/defrule <unicode-sequence>
  "Consumes a lowercase 'u' followed by hexadecimal digits."
  {:product "The character with the given digits' Unicode code."}
  (h/prefix
    (h/lit \u)
    (h/hook (comp char combine-hexadecimal-digits)
      (h/factor= 4 h/<hexadecimal-digit>))))

(h/defrule <escaped-str-char>
  "Consumes an escaped character in a string: a backslash
  followed by an escape sequence."
  {:product "A character."}
  (h/prefix
    <escape-char-start>
    (h/+ (h/term* "escape sequence" normal-escape-sequences)
         <unicode-sequence>)))

(h/defrule <str-char>
  "Consumes a general string character."
  {:product "A character or a sequence of characters."
   :consumes "One character."}
  (h/+ <escaped-str-char> <normal-str-char>))

(h/defrule <str-content>
  "Consumes a sequence of string characters."
  {:product "A string.", :consumes "Zero or more characters."}
  (h/hook (comp str* concat) (h/rep* (h/+ <str-char>))))

(h/defrule <str>
  "Consumes a JSON string."
  {:product "A string."}
  (h/label "a string"
    (h/circumfix <str-delimiter> <str-content> <str-delimiter>)))

(declare <value>)

(h/defrule <array-content>
  "Consumes a sequence of JSON values separated by commas, with optional
  whitespace padding on the front."
  {:product "A vector."}
  (h/separated-rep* <value-separator> <value>))

(h/defrule <array>
  "Consumes a JSON array. Optionally padded on the front with whitespace."
  {:product "A vector."}
  (h/circumfix <array-start> <array-content> <array-end>))

(h/defrule <object-entry>
  "Consumes a string-value pair with a colon. They appear in objects.
  Optionally padded on the front with whitespace."
  {:product "A vector pair."}
  (h/for [name <str>, _ <name-separator>, val <value>]
    [name val]))

(h/defrule <object-content>
  "Consumes a sequence of object entries separated by commas. Optionally
  padded with whitepace on the front."
  (h/hook #(into {} %) (h/separated-rep* <value-separator> <object-entry>)))

(h/defrule <object>
  "Consumes a JSON object. Optionally padded on the front with whitespace."
  {:product "A map."}
  (h/circumfix <object-start> <object-content> <object-end>))

(h/defrule <value>
  "Consumes a general JSON value, optionally padded
  with whitespace on the front."
  {:product "A vector, map, number, true, false, or nil."}
  (h/prefix <ws?> (h/+ <object> <array> <str> <true> <false> <null>)))

(h/defrule <document>
  "Consumes a general JSON document, optionally padded
  with whitespace on both sides.
  The root rule of the JSON grammar."
  (h/suffix <value> <ws?>))
