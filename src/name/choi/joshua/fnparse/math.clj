(ns name.choi.joshua.fnparse.math
  (:use clojure.template name.choi.joshua.fnparse.cat))

(set! *warn-on-reflection* true)

(def digit
  (semantics (term "a decimal digit" #(Character/isDigit (char %)))
    #(Integer/parseInt (str %))))

(do-template [rule-name token]
  (def rule-name (lit token))
  plus-sign \+, minus-sign \-, multiplication-sign \*, division-sign \/,
  opening-parenthesis \(, closing-parenthesis \))

(def indicator
  (with-label "an indicator"
    (alt plus-sign minus-sign multiplication-sign division-sign
         opening-parenthesis closing-parenthesis)))

(def number-expr
  (with-label "a number"
    (alt (complex [first-digits #'number-expr, next-digit digit]
           (+ (* 10 first-digits) next-digit))
         digit)))

(def symbol-char (except anything indicator))

(def symbol-content
  (alt (complex [first-char symbol-char, next-chars #'symbol-content]
         (cons first-char next-chars))
       (semantics symbol-char list)))

(def symbol-expr
  (with-label "a symbol" (semantics symbol-content #(apply str %))))

(def terminal-level-expr
  (alt number-expr symbol-expr))

(declare expr)

(def parenthesized-expr
  (complex [_ opening-parenthesis
            content #'expr
            _ closing-parenthesis]
    content))

(def parenthesized-level-expr
  (alt parenthesized-expr terminal-level-expr))

(def function-level-expr
  (alt (vconc symbol-expr parenthesized-expr) parenthesized-level-expr))

(def pos-neg-level-expr
  (alt (vconc (alt plus-sign minus-sign) function-level-expr)
       function-level-expr))

(def multiplication-level-expr
  (alt (vconc
         #'multiplication-level-expr
         (alt multiplication-sign division-sign)
         pos-neg-level-expr)
       pos-neg-level-expr))

(def addition-level-expr
  (alt (vconc
         #'addition-level-expr
         (alt plus-sign minus-sign)
         multiplication-level-expr)
       multiplication-level-expr))

(def expr addition-level-expr)

;(def a (alt (conc #'a (lit \-) number-level-expr)

;(prn (expr (make-state "3+1*cos(-(-5)+sin(2))")))
(prn (function-level-expr (make-state "abc")))
;(prn ((conc (opt digit) symbol-char) (make-state "+1*cos(-(-5)+sin(2))")))
;(println (expr (make-state "1+3*2+2" {} 0)))
;(println (expr (make-state "2+3-2" {} 0)))
