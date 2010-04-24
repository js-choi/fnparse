(ns edu.arizona.fnparse.math
  (:require [edu.arizona.fnparse.cat :as k] [clojure.template :as template]))

(set! *warn-on-reflection* true)

(declare <expr>)

(def <digit>
  (k/hook #(Integer/parseInt (str %))
    (k/term "a decimal digit" #(Character/isDigit (char %)))))

(def <ws?> (k/opt (k/set-term "whitespace" " \n\t")))

(template/do-template [rule-name token]
  (def rule-name (k/circumfix <ws?> (k/lit token) <ws?>))
  <plus-sign> \+, <minus-sign> \-, <multiplication-sign> \*, <division-sign> \/,
  <opening-parenthesis> \(, <closing-parenthesis> \))

(def <indicator>
  (k/label "an indicator"
    (k/+ <plus-sign> <minus-sign> <multiplication-sign> <division-sign>
         <opening-parenthesis> <closing-parenthesis>)))

(def <number>
  (k/label "a number"
    (k/+ (k/for [first-digits #'<number>, next-digit <digit>]
           (k/+ (* 10 first-digits) next-digit))
         <digit>)))

(def <symbol-char> (k/except "a symbol character" k/<anything> <indicator>))

(def <symbol-content>
  (k/+ (k/for [first-char <symbol-char>, next-chars #'<symbol-content>]
         (cons first-char next-chars))
       (k/hook list <symbol-char>)))

(def <symbol>
  (k/label "a symbol" (k/hook #(apply str %) <symbol-content>)))

(def <terminal-level>
  (k/+ <number> <symbol>))

(def <parenthesized>
  (k/circumfix <opening-parenthesis> #'<expr> <closing-parenthesis>))

(def <function> (k/vcat <symbol> <parenthesized>))

(def <parenthesized-level>
  (k/+ <parenthesized> <terminal-level>))

(def <function-level>
  (k/+ <function> <parenthesized-level>))

(def <pos-neg-level>
  (k/+ (k/vcat (k/+ <plus-sign> <minus-sign>) <function-level>)
       <function-level>))

(def <multiplication-level>
  (k/+ (k/vcat
         #'<multiplication-level>
         (k/+ <multiplication-sign> <division-sign>)
         <pos-neg-level>)
       <pos-neg-level>))

(def <addition-level>
  (k/+ (k/vcat
         #'<addition-level>
         (k/+ <plus-sign> <minus-sign>)
         <multiplication-level>)
       <multiplication-level>))

(def <expr> <addition-level>)
