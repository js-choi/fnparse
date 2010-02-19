(ns name.choi.joshua.fnparse.math
  (:use clojure.template name.choi.joshua.fnparse.cat clojure.test
        name.choi.joshua.fnparse.cat.test)
  (:refer-clojure :exclude #{+}))

(set! *warn-on-reflection* true)

(declare expr)

(def digit
  (semantics (term "a decimal digit" #(Character/isDigit (char %)))
    #(Integer/parseInt (str %))))

(do-template [rule-name token]
  (def rule-name (lit token))
  plus-sign \+, minus-sign \-, multiplication-sign \*, division-sign \/,
  opening-parenthesis \(, closing-parenthesis \))

(def indicator
  (with-label "an indicator"
    (+ plus-sign minus-sign multiplication-sign division-sign
         opening-parenthesis closing-parenthesis)))

(def number-expr
  (with-label "a number"
    (+ (complex [first-digits #'number-expr, next-digit digit]
           (+ (* 10 first-digits) next-digit))
         digit)))

(def symbol-char (except "a symbol character" anything indicator))

(def symbol-content
  (+ (complex [first-char symbol-char, next-chars #'symbol-content]
         (cons first-char next-chars))
       (semantics symbol-char list)))

(def symbol-expr
  (with-label "a symbol" (semantics symbol-content #(apply str %))))

(def terminal-level-expr
  (+ number-expr symbol-expr))

(def parenthesized-expr
  (circumfix-conc opening-parenthesis #'expr closing-parenthesis))

(def function-expr (vconc symbol-expr parenthesized-expr))

(def parenthesized-level-expr
  (+ parenthesized-expr terminal-level-expr))

(def function-level-expr
  (+ function-expr parenthesized-level-expr))

(def pos-neg-level-expr
  (+ (vconc (+ plus-sign minus-sign) function-level-expr)
       function-level-expr))

(def multiplication-level-expr
  (+ (vconc
         #'multiplication-level-expr
         (+ multiplication-sign division-sign)
         pos-neg-level-expr)
       pos-neg-level-expr))

(def addition-level-expr
  (+ (vconc
         #'addition-level-expr
         (+ plus-sign minus-sign)
         multiplication-level-expr)
       multiplication-level-expr))

(def expr addition-level-expr)

(deftest various-exprs
  (is (match? expr "3+1*cos(-(-5)+sin(2))"
        :product #(= % [3 '+ [1 '* ['cos [['- [-' 5]] '+ ['sin 2]]]]])))
  (is (non-match? expr "*3+1*cos(-(-5)+sin(2))"
        :labels #{"a number" "a symbol" "'-'" "'+'" "'('"}
        :position 0)))

(run-tests)