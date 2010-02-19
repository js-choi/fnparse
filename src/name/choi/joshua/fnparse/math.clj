(ns name.choi.joshua.fnparse.math
  (:require [name.choi.joshua.fnparse.cat :as r]
            [clojure.template :as template]
            name.choi.joshua.fnparse.cat.test)
  (:use [clojure.test :only #{deftest is run-tests}])
  (:refer-clojure :exclude #{+}))

(set! *warn-on-reflection* true)

(declare expr)

(def digit
  (r/semantics (r/term "a decimal digit" #(Character/isDigit (char %)))
    #(Integer/parseInt (str %))))

(template/do-template [rule-name token]
  (def rule-name (r/lit token))
  plus-sign \+, minus-sign \-, multiplication-sign \*, division-sign \/,
  opening-parenthesis \(, closing-parenthesis \))

(def indicator
  (r/with-label "an indicator"
    (r/+ plus-sign minus-sign multiplication-sign division-sign
         opening-parenthesis closing-parenthesis)))

(def number-expr
  (r/with-label "a number"
    (r/+ (r/complex [first-digits #'number-expr, next-digit digit]
           (r/+ (* 10 first-digits) next-digit))
         digit)))

(def symbol-char (r/except "a symbol character" r/anything indicator))

(def symbol-content
  (r/+ (r/complex [first-char symbol-char, next-chars #'symbol-content]
         (cons first-char next-chars))
       (r/semantics symbol-char list)))

(def symbol-expr
  (r/with-label "a symbol" (r/semantics symbol-content #(apply str %))))

(def terminal-level-expr
  (r/+ number-expr symbol-expr))

(def parenthesized-expr
  (r/circumfix-conc opening-parenthesis #'expr closing-parenthesis))

(def function-expr (r/vconc symbol-expr parenthesized-expr))

(def parenthesized-level-expr
  (r/+ parenthesized-expr terminal-level-expr))

(def function-level-expr
  (r/+ function-expr parenthesized-level-expr))

(def pos-neg-level-expr
  (r/+ (r/vconc (r/+ plus-sign minus-sign) function-level-expr)
       function-level-expr))

(def multiplication-level-expr
  (r/+ (r/vconc
         #'multiplication-level-expr
         (r/+ multiplication-sign division-sign)
         pos-neg-level-expr)
       pos-neg-level-expr))

(def addition-level-expr
  (r/+ (r/vconc
         #'addition-level-expr
         (r/+ plus-sign minus-sign)
         multiplication-level-expr)
       multiplication-level-expr))

(def expr addition-level-expr)

(deftest various-exprs
  (is (match? expr "3+1*cos(-(-5)+sin(2))"
        :product? #(= % [3 \+ [1 \* ["cos" [[\- [\- 5]] \+ ["sin" 2]]]]])))
  (is (non-match? expr "*3+1*cos(-(-5)+sin(2))"
        :labels #{"a number" "a symbol" "'-'" "'+'" "'('"}
        :position 0)))

(run-tests)