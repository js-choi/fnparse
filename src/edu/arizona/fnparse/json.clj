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
        [clojure.contrib.except :as except])
  (:refer-clojure :exclude #{read-string}))

(defn expt-int [core pow]
  (loop [n (int pow), y 1, z core]
    (let [t (bit-and n 1), n (bit-shift-right n 1)]
      (cond
        (zero? t) (recur n y (* z z))
        (zero? n) (* z y)
        :else (recur n (* z y) (* z z))))))

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

; Strings.

(h/defrule <control-char>
  "Consumes an ASCII control character, which is not allowed in strings."
  (h/chook ::control-char h/<ascii-control>))

(h/defrule <normal-str-char>
  "Consumes normal, non-espaced string character.
  No control characters allowed."
  {:product "A character."}
  (h/except "a normal string character"
    h/<anything> <str-delimiter> <control-char>))

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

; Numbers.

(h/defmaker >radix-natural-number<
  "Matches a single natural number whose allowed digits (which are
  alphanumeric) are determined by the `core`, a positive integer.
  Its product is the integer represented."
  [core]
  (h/hooked-rep #(+ (* core %1) %2) 0 (h/radix-digit core)))

(h/defrule <decimal-natural-number>
  "A series of decimal digits; the product is the corresponding integer."
  (>radix-natural-number< 10))

(h/defrule <number-sign>
  "A number sign, positive or negative. Its product can be `+1` or `-1`."
  (h/template-sum [label token product]
    (h/label label (h/chook product (h/lit token)))
    "positive sign" \+ 1, "negative sign" \- -1))

(h/defrule <empty-number-tail>
  "An empty number tail. Returns the `identity` function."
  (h/chook identity h/<emptiness>))

(h/defrule <imprecise-fractional-part>
  "A '.' followed by an optional series of digits:
  a fractional part of a number.
  Its product is a function that takes a number and
  adds the number indicated by the series of digits to it."
  (letfn [(reduce-digit-accumulator [[prev-num multiplier] next-digit]
            [(+ (* next-digit multiplier) prev-num) (/ multiplier 10)])]
    (h/prefix
      (h/lit \.)
      (h/+ (->> h/<decimal-digit>
             (h/hooked-rep reduce-digit-accumulator [0 0.1])
             (h/hook #(partial + (get % 0))))
           (h/hook #(partial + (/ % 10.)) <decimal-natural-number>)
           <empty-number-tail>))))

(h/defrule <exponential-part>
  "An 'e' followed by a series of digits: the exponential part.
  Its product is a function that takes a number
  and raises it to whatever power indicated by the series of digits."
  (h/prefix
    (h/case-insensitive-lit \e)
    (h/hook #(partial * (expt-int 10 %)) <decimal-natural-number>)))

(h/defrule <fractional-exponential-part>
  "A fractional part followed by an optional exponential part.
  Its product is the functional composition of the two parts' products."
  (h/for [frac-fn <imprecise-fractional-part>
          exp-fn (h/+ <exponential-part> <empty-number-tail>)]
    (comp exp-fn frac-fn)))

(h/defrule <imprecise-number-tail>
  "The tail of an imprecise number: that is, a number
  that has a '.', 'e', or 'M'. Its product is a function that
  transforms an integer according to the tail and also
  turns it to a `double` (or a `BigDecimal` if it has an 'M')."
  (h/for [tail-fn (h/+ <fractional-exponential-part> <exponential-part>)
          big-dec? (h/opt (h/lit \M))]
    (comp (if big-dec? bigdec double) tail-fn)))

(h/defrule <fraction-denominator-tail>
  "The tail of a ratio number, i.e. a '/' followed by a denominator.
  The denominator cannot be zero. Its product is a function that
  takes an integer and divides it by the denominator."
  ; Product: a unary function on an integer.
  (h/prefix
    (h/lit \/)
    (h/hook (fn [denominator] #(/ % denominator))
      (h/antivalidate zero? "a fraction's denominator cannot be zero"
        <decimal-natural-number>))))

(h/defrule <number-tail>
  "The tail of a number. Its product is a function that takes
  the integer given by the number's core (the digits before
  any special character like '.' or 'r'), and returns a new
  number: the number represented by the core and tail together."
  (h/+ <imprecise-number-tail> <fraction-denominator-tail>
       <empty-number-tail>))

(h/defrule <number>
  "Any Clojure number. Its product is a `Number`."
  (h/for "a number"
    [sign (h/opt <number-sign>)
     prefix-number <decimal-natural-number>
     tail-fn <number-tail>]
    (tail-fn (* (or sign 1) prefix-number))))

; Recursive data structures.

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
  (h/prefix <ws?> (h/+ <object> <array> <str> <number> <true> <false> <null>)))

(h/defrule <document>
  "Consumes a general JSON document, optionally padded
  with whitespace on both sides.
  The root rule of the JSON grammar."
  (h/suffix <value> <ws?>))

(defn read-string
  "Reads one JSON value from the given sequential
  collection of characters, `input`. The reading
  does not have to reach the end of the character
  sequence to succeed. On success, the function
  returns the value as a nested Clojure vector/
  map/string/number/boolean/nil. On failure, raises
  a Java exception."
  [input]
  (h/match (h/make-state input) <document>
    :success-fn (fn [product position] product)
    :failure-fn (fn [error]
                  (except/throwf "JSON parsing error: %s"
                    (h/format-parse-error error)))))
