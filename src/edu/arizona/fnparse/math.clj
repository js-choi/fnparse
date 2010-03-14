(ns edu.arizona.fnparse.math
  (:require [edu.arizona.fnparse.cat :as r]
            [clojure.template :as template]
            edu.arizona.fnparse.cat.test)
  (:use [clojure.test :only #{deftest is run-tests}]))

(set! *warn-on-reflection* true)

(declare <expr>)

(def <digit>
  (r/hook #(Integer/parseInt (str %))
    (r/term "a decimal digit" #(Character/isDigit (char %)))))

(def <ws?> (r/opt (r/set-lit "whitespace" " \n\t")))

(template/do-template [rule-name token]
  (def rule-name (r/circumfix <ws?> (r/lit token) <ws?>))
  <plus-sign> \+, <minus-sign> \-, <multiplication-sign> \*, <division-sign> \/,
  <opening-parenthesis> \(, <closing-parenthesis> \))

(def <indicator>
  (r/label "an indicator"
    (r/+ <plus-sign> <minus-sign> <multiplication-sign> <division-sign>
         <opening-parenthesis> <closing-parenthesis>)))

(def <number>
  (r/label "a number"
    (r/+ (r/for [first-digits #'<number>, next-digit <digit>]
           (r/+ (* 10 first-digits) next-digit))
         <digit>)))

(def <symbol-char> (r/except "a symbol character" r/<anything> <indicator>))

(def <symbol-content>
  (r/+ (r/for [first-char <symbol-char>, next-chars #'<symbol-content>]
         (cons first-char next-chars))
       (r/hook list <symbol-char>)))

(def <symbol>
  (r/label "a symbol" (r/hook #(apply str %) <symbol-content>)))

(def <terminal-level>
  (r/+ <number> <symbol>))

(def <parenthesized>
  (r/circumfix <opening-parenthesis> #'<expr> <closing-parenthesis>))

(def <function> (r/vcat <symbol> <parenthesized>))

(def <parenthesized-level>
  (r/+ <parenthesized> <terminal-level>))

(def <function-level>
  (r/+ <function> <parenthesized-level>))

(def <pos-neg-level>
  (r/+ (r/vcat (r/+ <plus-sign> <minus-sign>) <function-level>)
       <function-level>))

(def <multiplication-level>
  (r/+ (r/vcat
         #'<multiplication-level>
         (r/+ <multiplication-sign> <division-sign>)
         <pos-neg-level>)
       <pos-neg-level>))

(def <addition-level>
  (r/+ (r/vcat
         #'<addition-level>
         (r/+ <plus-sign> <minus-sign>)
         <multiplication-level>)
       <multiplication-level>))

(def <expr> <addition-level>)

(require '[edu.arizona.fnparse.common :as c])

(deftest various-tests
  (is (match? <expr> "3 + 1 * cos(-(-5) + sin(2))"
        :product? #(= % [3 \+ [1 \* ["cos" [[\- [\- 5]] \+ ["sin" 2]]]]])))
  (is (non-match? <expr> "*3+1*cos(-(-5)+sin(2))"
        :labels #{"a number" "a symbol" "'-'" "'+'" "'('" "whitespace"}
        :position 0)))

(run-tests)
