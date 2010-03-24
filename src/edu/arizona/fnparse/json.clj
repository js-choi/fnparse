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
  (:require [edu.arizona.fnparse.hound :as p] [clojure.set :as set]
            [clojure.contrib [seq :as seq] [except :as except]]
            edu.arizona.fnparse.hound.test)
  (:use [clojure.template :only #{do-template}]
        [clojure.test :only #{set-test is run-tests}])
  (:refer-clojure :exclude #{read-string}))

(defn str* [objects]
  (apply str objects))

(p/defrule <ws?>
  "Optional, ignored JSON whitespace."
  (p/rep* (p/set-term "whitespace" " \t\n\r")))

; Define single-character indicator rules.
; I use `clojure.template/do-template` to reduce repetition.
(do-template [rule-name token]
  (p/defrule rule-name
    "Padded on the front with optional whitespace."
    (p/prefix <ws?> (p/lit token)))
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
  (p/defrule rule-name (p/chook product (p/phrase tokens)))
  <true>  "true"  true
  <false> "false" false
  <null>  "null"  nil)

(p/defrule <normal-str-char>
  "Define normal, non-espaced string characters."
  {:product "A character."}
  (p/except "a normal string character" p/<anything> <str-delimiter>))
  ; The `except` rule-maker requires a label argument.

(p/defrule <str-char>
  "A general string character."
  {:product "A character or a sequence of characters."
   :consumes "One character."}
  (p/+ <normal-str-char>))

(p/defrule <str-content>
  "A sequence of string characters."
  {:product "A string.", :consumes "Zero or more characters."}
  (p/hook (comp str* concat) (p/rep* (p/+ <str-char>))))

(p/defrule <str>
  "A JSON string."
  {:product "A string."}
  (p/label "a string"
    (p/circumfix <str-delimiter> <str-content> <str-delimiter>)))

#_(def <nonzero-integer>
  (p/rep ))

(p/defrule <value>
  "A general JSON value, optionally padded with whitespace on the front."
  {:product "A vector, map, number, true, false, or nil."}
  (p/prefix <ws?> (p/+ <str> <true> <false> <null>)))

(p/defrule <array-content>
  "A sequence of JSON values separated by commas, with optional
  whitespace padding on the front."
  {:product "A vector."}
  (p/hook vec (p/opt (p/separated-rep <value-separator> <value>))))

(p/defrule <array>
  "A JSON array. Optionally padded on the front with whitespace."
  {:product "A vector."}
  (p/circumfix <array-start> <array-content> <array-end>))
