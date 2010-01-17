(ns name.choi.joshua.fnparse.math
  (:use clojure.template name.choi.joshua.fnparse.cat))

(set! *warn-on-reflection* true)

(def digit (term "a decimal digit" #(Character/isDigit (char %))))

(do-template [rule-name token]
  (def rule-name (lit token))
  plus-sign \+, minus-sign \-, multiplication-sign \*, division-sign \/,
  opening-parenthesis \(, closing-parenthesis \))

(def indicator
  (alt plus-sign minus-sign multiplication-sign division-sign
       opening-parenthesis closing-parenthesis))

(def number-level-expr
  (semantics (rep+ digit)
    #(Integer/parseInt (apply str %))))

(def name-level-expr
  (semantics (rep+ (except anything indicator))
    (partial apply str)))

(def terminal-level-expr
  (alt number-level-expr name-level-expr))

(declare expr)

(def parenthesized-expr
  (complex [_ opening-parenthesis
            content #'expr
            _ closing-parenthesis]
    content))

(def parenthesized-level-expr
  (alt parenthesized-expr terminal-level-expr))

(def function-level-expr
  (alt (vconc name-level-expr parenthesized-expr) parenthesized-level-expr))

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

(prn (expr (make-state "3+1*cos(-(-5)+sin(2))")))
;(println (expr (make-state "1+3*2+2" {} 0)))
;(println (expr (make-state "2+3-2" {} 0)))
