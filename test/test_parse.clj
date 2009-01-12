(ns name.choi.joshua.fnparse.test-parse
  (:use clojure.contrib.test-is)
  (:require [name.choi.joshua.fnparse :as p]))

(deftest test-term
  (is (= ((force (p/term #(= % "true"))) ["true" "THEN"])
         ["true" (list "THEN")])
      "created terminal rule works when first token fulfills validator")
  (is (nil? ((force (p/term #(= % "true"))) ["false" "THEN"]))
      "created terminal rule fails when first token fails validator"))

(deftest test-lit
  (is (= ((force (p/lit "true")) ["true" "THEN"])
         ["true" (list "THEN")])
      "created literal rule works when literal token present")
  (is (nil? ((force (p/lit "true")) ["false" "THEN"]))
      "created literal rule fails when literal token not present"))

(deftest test-re-term
  (is (= ((force (p/re-term #"\s*true\s*")) ["  true" "THEN"])
         ["  true" (list "THEN")])
      "created re-term rule works when first token matches regex")
  (is (nil? ((force (p/re-term #"\s*true\s*")) ["false" "THEN"]))
      "created re-term rule fails when first token does not match regex"))

(deftest test-semantics
  (is (= ((force (p/semantics (p/lit "hi") #(str % \!))) ["hi" "THEN"])
         ["hi!" (list "THEN")])
      "created rule applies semantic hook to valid result of given rule")
  (is (nil? ((force (p/semantics (p/lit "hi") #(str % \!))) "RST"))
      "created rule fails when given subrule fails"))

(deftest test-constant-semantics
  (is (= ((force (p/constant-semantics (p/lit "hi") (hash-map :a 1))) ["hi" "THEN"])
         [{:a 1} (list "THEN")])
      "created rule returns constant value when given subrule does not fail"))

(deftest test-conc
  (let [identifier (p/semantics (p/term string?) symbol),
        equals-operator (p/semantics (p/lit "=") keyword),
        answer (p/lit "42"),
        truth (p/conc identifier equals-operator answer)]
    ; Parse the first symbols in the program "answer = 42 THEN"
    (is (= ((force truth) ["answer" "=" "42" "THEN"])
           [['answer := "42"] (list "THEN")])
        "created concatenation rule works when valid symbols are present in order")
    ; Parse the first symbols in the program "answer = 42 THEN"
    (is (= ((force truth) ["answer" "42" "=" "THEN"]) nil)
        "created concatenation rule fails when invalid symbols present")))

(deftest test-alt
  (let [literal-true (p/semantics (p/lit "true") (fn [_] true)),
        literal-false (p/semantics (p/lit "false") (fn [_] false)),
        literal-boolean (p/alt literal-true literal-false)]
    ; Parse the first symbol in the program "false THEN"
    (is (= ((force literal-boolean) ["false" "THEN"])
           [false (list "THEN")])
        "created alternatives rule works with first valid rule product")
    ; Parse the first symbol in the program "aRSTIR"
    (is (nil? ((force literal-boolean) ["aRSTIR"]))
        "created alternatives rule fails when no valid rule product present")))

(deftest test-opt
  (let [opt-true (p/opt (p/semantics (p/lit "true") (fn [_] true)))]
    ; Parse the first symbol in the program "true THEN"
    (is (= ((force opt-true) ["true" "THEN"])
           [true (list "THEN")])
        "created option rule works when symbol present")
    ; Parse the first symbol in the program "THEN"
    (is (= ((force opt-true) (list "THEN"))
           [nil (list "THEN")])
        "created option rule works when symbol absent")))

(deftest test-rep*
  (let [rep*-true (p/rep* (p/semantics (p/lit "true") (fn [_] true)))]
    ; Parse the first symbol in the program "true THEN"
    (is (= ((force rep*-true) ["true" "THEN"])
           [[true] (list "THEN")])
        "created zero-or-more-repetition rule works when symbol present singularly")
    ; Parse the first symbol in the program "true true true THEN"
    (is (= ((force rep*-true) ["true" "true" "true" "THEN"])
           [[true true true] (list "THEN")])
        "created zero-or-more-repetition rule works when symbol present multiply")
    ; Parse the first symbol in the program "THEN"
    (is (= ((force rep*-true) (list "THEN"))
           [[] (list "THEN")])
     "created zero-or-more-repetition rule works when symbol absent"))
  (let [rep*-char (p/rep* (p/term #(not= % \")))]
    ; Parse the first symbol in the program "THEN"
    (is (= ((force rep*-char) (list \a \b \c))
           [[\a \b \c] nil])
        "created zero-or-more-repetition rule with a negative subrule works with no remainder")))

(deftest test-rep+
  (let [rep+-true (p/rep+ (p/semantics (p/lit "true") (fn [_] true)))]
    ; Parse the first symbol in the program "true THEN"
    (is (= ((force rep+-true) ["true" "THEN"])
           [[true] (list "THEN")])
        "created one-or-more-repetition rule works when symbol present singularly")
    ; Parse the first symbol in the program "true true true THEN"
    (is (= ((force rep+-true) ["true" "true" "true" "THEN"])
           [[true true true] (list "THEN")])
        "created one-or-more-repetition rule works when symbol present multiply")
    ; Parse the first symbol in the program "THEN"
    (is (nil? ((force rep+-true) (list "THEN")))
        "created one-or-more-repetition rule fails when symbol absent")))

(deftest test-except
  ; except-rule = ("A" | "B" | "C") - "B" - "C";
  (let [except-rule (p/except (p/alt (p/lit "A") (p/lit "B") (p/lit "C")) (p/lit "B")
                                     (p/lit "C"))]
    (is (= ((force except-rule) (list "A" "B" "C")) ["A" (list "B" "C")])
        "created exception rule works when symbol is not one of the syntatic exceptions")
    (is (= ((force except-rule) (list "B" "A" "C")) nil)
        "created exception rule fails when symbol is one of the syntactic exceptions")
    (is (= ((force except-rule) (list "D" "A" "B")) nil)
        "created exception rule fails when symbol does not fulfill subrule")))
 
(deftest test-factor=
  ; rep=-rule = 3 * "A";
  (let [tested-rule (p/factor= 3 (p/lit "A"))]
    (is (= ((force tested-rule) (list "A" "A" "A" "A" "C")) [["A" "A" "A"] (list "A" "C")])
        "created factor= rule works when symbol fulfills all subrule multiples and leaves strict remainder")
    (is (= ((force tested-rule) (list "A" "A" "A" "C")) [["A" "A" "A"] (list "C")])
        "created factor= rule works when symbol fulfills all subrule multiples only")
    (is (= ((force tested-rule) (list "A" "A" "C")) nil)
        "created factor= rule fails when symbol does not fulfill all subrule multiples")
    (is (= ((force tested-rule) (list "D" "A" "B")) nil)
        "created factor= rule fails when symbol does not fulfill subrule at all")))
 
(deftest test-factor<
  (let [tested-rule (p/factor< 3 (p/lit "A"))]
    (is (= ((force tested-rule) (list "A" "A" "A" "A" "C")) [["A" "A"] (list "A" "A" "C")])
        "created factor< rule works when symbol fulfills all subrule multiples and leaves strict remainder")
    (is (= ((force tested-rule) (list "A" "A" "A" "C")) [["A" "A"] (list "A" "C")])
        "created factor< rule works when symbol fulfills all subrule multiples only")
    (is (= ((force tested-rule) (list "A" "A" "C")) [["A" "A"] (list "C")])
        "created factor< rule works when symbol does not fulfill all subrule multiples")
    (is (= ((force tested-rule) (list "D" "A" "B")) [[] (list "D" "A" "B")])
        "created factor< rule works when symbol does not fulfill subrule at all")))
 
(deftest test-factor<=
  (let [tested-rule (p/factor<= 3 (p/lit "A"))]
    (is (= ((force tested-rule) (list "A" "A" "A" "A" "C")) [["A" "A" "A"] (list "A" "C")])
        "created factor<= rule works when symbol fulfills all subrule multiples and leaves strict remainder")
    (is (= ((force tested-rule) (list "A" "A" "A" "C")) [["A" "A" "A"] (list "C")])
        "created factor<= rule works when symbol fulfills all subrule multiples only")
    (is (= ((force tested-rule) (list "A" "A" "C")) [["A" "A"] (list "C")])
        "created factor<= rule works when symbol does not fulfill all subrule multiples")
    (is (= ((force tested-rule) (list "D" "A" "B")) [[] (list "D" "A" "B")])
        "created factor<= rule works when symbol does not fulfill subrule at all")))
 
(deftest test-rep-predicate
  (let [tested-rule-fn (force (p/rep-predicate (partial > 3) (p/lit "A")))]
    (is (= (tested-rule-fn (list "A" "A" "C")) [["A" "A"] (list "C")])
        "created rep rule works when predicate returns true")
    (is (= (tested-rule-fn (list "A" "A" "A")) nil)
        "created rep rule fails when predicate returns false")
    (is (= (tested-rule-fn (list "D" "A" "B")) [[] (list "D" "A" "B")])
        "created rep rule succeeds when symbol does not fulfill subrule at all")))
 
(deftest test-rep=
  (let [tested-rule-fn (force (p/rep= 3 (p/lit "A")))]
    (is (= (tested-rule-fn (list "A" "A" "A" "C")) [["A" "A" "A"] (list "C")])
        "created rep= rule works when symbol only fulfills all subrule multiples")
    (is (= (tested-rule-fn (list "A" "A" "A" "A")) nil)
        "created rep= rule fails when symbol exceeds subrule multiples")
    (is (= (tested-rule-fn (list "A" "A" "C")) nil)
        "created rep= rule fails when symbol does not fulfill all subrule multiples")
    (is (= (tested-rule-fn (list "D" "A" "B")) nil)
        "created rep= rule fails when symbol does not fulfill subrule at all")))
 
(deftest test-rep<
  (let [tested-rule-fn (force (p/rep< 3 (p/lit "A")))]
    (is (= (tested-rule-fn (list "A" "A" "C")) [["A" "A"] (list "C")])
        "created rep< rule works when number of fulfilled rules is less than limit")
    (is (= (tested-rule-fn (list "A" "A" "A")) nil)
        "created rep< rule fails when number of fulfilled rules is equal to limit")
    (is (= (tested-rule-fn (list "A" "A" "A" "A" "C")) nil)
        "created rep< rule fails when symbol of fulfilled rules is more than limit")
    (is (= (tested-rule-fn (list "D" "A" "B")) [[] (list "D" "A" "B")])
        "created rep< rule succeeds when symbol does not fulfill subrule at all")))
 
(deftest test-rep<=
  (let [tested-rule-fn (force (p/rep<= 3 (p/lit "A")))]
    (is (= (tested-rule-fn (list "A" "A" "C")) [["A" "A"] (list "C")])
        "created rep< rule works when number of fulfilled rules is less than limit")
    (is (= (tested-rule-fn (list "A" "A" "A" "C")) [["A" "A" "A"] (list "C")])
        "created rep< rule works when number of fulfilled rules is equal to limit")
    (is (= (tested-rule-fn (list "A" "A" "A" "A" "C")) nil)
        "created rep< rule fails when symbol of fulfilled rules is more than limit")
    (is (= (tested-rule-fn (list "D" "A" "B")) [[] (list "D" "A" "B")])
        "created rep< rule succeeds when symbol does not fulfill subrule at all")))
 
(deftest test-validate
  (is (= ((force (p/validate (p/lit "hi") #(= "hi" %))) ["hi" "THEN"])
         ["hi" (list "THEN")])
      "created validator rule succeeds when given subrule and validator succeed")
  (is (= ((force (p/validate (p/lit "hi") #(= "RST" %))) "RST") nil)
      "created validator rule fails when given subrule fails")
  (is (= ((force (p/validate (p/lit "hi") #(= "hi" %))) "hi") nil)
      "created validator rule fails when given validator fails"))
 
(deftest test-lit-conc-seq
  ; Parse the first four symbols in the program "THEN"
  (is (= ((force (p/lit-conc-seq "THEN")) (seq "THEN print 42;"))
         [(vec "THEN") (seq " print 42;")])
      "created literal-sequence rule is based on sequence of given token sequencible"))
 
(deftest test-lit-alt-seq
  ; Parse the first four symbols in the program "B 2"
  (is (= ((force (p/lit-alt-seq "ABCD")) (seq "B 2"))
         [\B (seq " 2")])
      "created literal-alternative-sequence rule works when literal symbol present in sequence")
  (is (= ((force (p/lit-alt-seq "ABCD")) (seq "E 2")) nil)
      "created literal-alternative-sequence rule fails when literal symbol not present in sequence"))
 
(deftest test-emptiness
  ; Parse the emptiness before the first symbol
  (is (= (force (p/emptiness (list "A" "B" "C")))
         [nil (list "A" "B" "C")])
      "emptyiness rule matches emptiness"))
 
(deftest test-followed-by
  ; Parse that the next symbol is "A" without consuming it
  (is (= ((force (p/followed-by (p/lit "A"))) (list "A" "B" "C"))
         ["A" (list "A" "B" "C")])
      "created followed-by rule works when first symbol fulfills subrule without consuming any symbols")
  (is (= ((force (p/followed-by (p/lit "A"))) (list "B" "B")) nil)
      "created followed-by rule fails when subrule fails with first symbol"))

(run-tests)
