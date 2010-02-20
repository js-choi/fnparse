(ns name.choi.joshua.fnparse.math
  (:require [name.choi.joshua.fnparse.cat :as r]
            [clojure.template :as template]
            name.choi.joshua.fnparse.cat.test)
  (:use [clojure.test :only #{deftest is run-tests}]))

(set! *warn-on-reflection* true)

(declare expr_)

(def digit_
  (r/hook #(Integer/parseInt (str %))
    (r/term "a decimal digit" #(Character/isDigit (char %)))))

(template/do-template [rule-name token]
  (def rule-name (r/lit token))
  plus-sign_ \+, minus-sign_ \-, multiplication-sign_ \*, division-sign_ \/,
  opening-parenthesis_ \(, closing-parenthesis_ \))

(def indicator
  (r/label "an indicator"
    (r/+ plus-sign_ minus-sign_ multiplication-sign_ division-sign_
         opening-parenthesis_ closing-parenthesis_)))

(def number_
  (r/label "a number"
    (r/+ (r/for [first-digits #'number_, next-digit digit_]
           (r/+ (* 10 first-digits) next-digit))
         digit_)))

(def symbol-char_ (r/except "a symbol character" r/anything_ indicator))

(def symbol-content_
  (r/+ (r/for [first-char symbol-char_, next-chars #'symbol-content_]
         (cons first-char next-chars))
       (r/hook list symbol-char_)))

(def symbol_
  (r/label "a symbol" (r/hook #(apply str %) symbol-content_)))

(def terminal-level_
  (r/+ number_ symbol_))

(def parenthesized_
  (r/circumfix opening-parenthesis_ #'expr_ closing-parenthesis_))

(def function_ (r/vcat symbol_ parenthesized_))

(def parenthesized-level_
  (r/+ parenthesized_ terminal-level_))

(def function-level_
  (r/+ function_ parenthesized-level_))

(def pos-neg-level_
  (r/+ (r/vcat (r/+ plus-sign_ minus-sign_) function-level_)
       function-level_))

(def multiplication-level_
  (r/+ (r/vcat
         #'multiplication-level_
         (r/+ multiplication-sign_ division-sign_)
         pos-neg-level_)
       pos-neg-level_))

(def addition-level_
  (r/+ (r/vcat
         #'addition-level_
         (r/+ plus-sign_ minus-sign_)
         multiplication-level_)
       multiplication-level_))

(def expr_ addition-level_)

(deftest various_s
  (is (match? expr_ "3+1*cos(-(-5)+sin(2))"
        :product? #(= % [3 \+ [1 \* ["cos" [[\- [\- 5]] \+ ["sin" 2]]]]])))
  (is (non-match? expr_ "*3+1*cos(-(-5)+sin(2))"
        :labels #{"a number" "a symbol" "'-'" "'+'" "'('"}
        :position 0)))

(run-tests)