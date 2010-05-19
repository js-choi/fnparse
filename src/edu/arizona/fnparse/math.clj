(ns edu.arizona.fnparse.math
  (:require [edu.arizona.fnparse.cat :as k] [clojure.template :as template]))

(set! *warn-on-reflection* true)

(declare <expr> <ws>)

(def <digit>
  (k/hook #(Integer/parseInt (str %))
    (k/term "a decimal digit" #(Character/isDigit (char %)))))

(def <ws-char> (k/set-term "a whitespace character" " \n\t"))
(k/defrule <ws>
  (k/label "whitespace" (k/+ (k/cat <ws> <ws-char>) <ws-char>)))
(def <ws?> (k/opt <ws>))

(comment

(template/do-template [rule-name token]
  (def rule-name (k/suffix (k/lit token) <ws?>))
  <plus-sign> \+, <minus-sign> \-, <multiplication-sign> \*, <division-sign> \/,
  <opening-parenthesis> \(, <closing-parenthesis> \))

(def <indicator>
  (k/label "an indicator"
    (k/+ <plus-sign> <minus-sign> <multiplication-sign> <division-sign>
         <opening-parenthesis> <closing-parenthesis>)))

(def <separator> (k/+ <ws> <indicator>))

(k/defrule <number>
  (k/label "a number"
    (k/+ (k/for [first-digits <number>, next-digit <digit>]
           (+ (* 10 first-digits) next-digit))
         <digit>)))

(def <symbol-char>
  (k/label "a symbol character" (k/except k/<anything> <separator>)))

(k/defrule <symbol-content>
  (k/+ (k/for [first-char <symbol-char>, next-chars <symbol-content>]
         (cons first-char next-chars))
       (k/hook list <symbol-char>)))

(def <symbol>
  (k/label "a symbol" (k/hook #(apply str %) <symbol-content>)))

(def <terminal-level>
  (k/+ <number> <symbol>))

(k/defrule <parenthesized>
  (k/circumfix <opening-parenthesis> <expr> <closing-parenthesis>))

(def <function> (k/vcat <symbol> <parenthesized>))

(def <parenthesized-level>
  (k/+ <parenthesized> <terminal-level>))

(def <function-level>
  (k/+ <function> <parenthesized-level>))

(def <pos-neg-level>
  (k/+ (k/vcat (k/+ <plus-sign> <minus-sign>) <function-level>)
       <function-level>))

(k/defrule <multiplication-level>
  (k/+ (k/vcat
         <multiplication-level>
         (k/+ <multiplication-sign> <division-sign>)
         <pos-neg-level>)
       <pos-neg-level>))

(k/defrule <addition-level>
  (k/+ (k/vcat
         <addition-level>
         (k/+ <plus-sign> <minus-sign>)
         <multiplication-level>)
       <multiplication-level>))

(def <expr> (k/prefix <ws?> <addition-level>))

)