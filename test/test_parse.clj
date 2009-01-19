(ns name.choi.joshua.fnparse.test-parse
  (:use clojure.contrib.test-is)
  (:require [name.choi.joshua.fnparse :as p]))

(deftest test-term
  (is (= (((p/term #(= % "true"))) ["true" "THEN"])
         ["true" (list "THEN")])
      "created terminal rule works when first token fulfills validator")
  (is (= ^(get (((p/term #(= % "true")
                         (fn [metadata product]
                           (assoc metadata :column (inc (:column metadata))))))
                         #^{:column 13, :line 2} ["true" "THEN"])
               1)
         {:column 14, :line 2})
      "created terminal rule creates new metadata when valid")
  (is (nil? (((p/term #(= % "true"))) ["false" "THEN"]))
      "created terminal rule fails when first token fails validator"))

(deftest test-lit
  (is (= (((p/lit "true")) ["true" "THEN"])
         ["true" (list "THEN")])
      "created literal rule works when literal token present")
  (is (= ^(get (((p/lit "true"
                        (fn [metadata product]
                          (assoc metadata :column (inc (:column metadata))))))
                        #^{:column 13, :line 2} ["true" "THEN"])
               1)
         {:column 14, :line 2})
      "created literal rule creates new metadata when valid")
  (is (nil? (((p/lit "true")) ["false" "THEN"]))
      "created literal rule fails when literal token not present"))

;(deftest test-re-term
;  (is (= (((p/re-term #"\s*true\s*")) ["  true" "THEN"])
;         ["  true" (list "THEN")])
;      "created re-term rule works when first token matches regex")
;  (is (nil? (((p/re-term #"\s*true\s*")) ["false" "THEN"]))
;      "created re-term rule fails when first token does not match regex"))
;
;(deftest test-semantics
;  (is (= (((p/semantics (p/lit "hi") #(str % \!))) ["hi" "THEN"])
;         ["hi!" (list "THEN")])
;      "created rule applies semantic hook to valid result of given rule")
;  (is (nil? (((p/semantics (p/lit "hi") #(str % \!))) "RST"))
;      "created rule fails when given subrule fails"))
;
;(deftest test-constant-semantics
;  (is (= (((p/constant-semantics (p/lit "hi") (hash-map :a 1))) ["hi" "THEN"])
;         [{:a 1} (list "THEN")])
;      "created rule returns constant value when given subrule does not fail"))
;
;(deftest test-conc
;  (let [identifier (p/semantics (p/term string?) symbol),
;        equals-operator (p/semantics (p/lit "=") keyword),
;        answer (p/lit "42"),
;        truth (p/conc identifier equals-operator answer)]
;    ; Parse the first symbols in the program "answer = 42 THEN"
;    (is (= ((truth) ["answer" "=" "42" "THEN"])
;           [['answer := "42"] (list "THEN")])
;        "created concatenation rule works when valid symbols are present in order")
;    ; Parse the first symbols in the program "answer = 42 THEN"
;    (is (= ((truth) ["answer" "42" "=" "THEN"]) nil)
;        "created concatenation rule fails when invalid symbols present")))
;
;(deftest test-alt
;  (let [literal-true (p/semantics (p/lit "true") (fn [_] true)),
;        literal-false (p/semantics (p/lit "false") (fn [_] false)),
;        literal-boolean (p/alt literal-true literal-false)]
;    ; Parse the first symbol in the program "false THEN"
;    (is (= ((literal-boolean) ["false" "THEN"])
;           [false (list "THEN")])
;        "created alternatives rule works with first valid rule product")
;    ; Parse the first symbol in the program "aRSTIR"
;    (is (nil? ((literal-boolean) ["aRSTIR"]))
;        "created alternatives rule fails when no valid rule product present")))
;
;(deftest test-opt
;  (let [opt-true (p/opt (p/semantics (p/lit "true") (fn [_] true)))]
;    ; Parse the first symbol in the program "true THEN"
;    (is (= ((opt-true) ["true" "THEN"])
;           [true (list "THEN")])
;        "created option rule works when symbol present")
;    ; Parse the first symbol in the program "THEN"
;    (is (= ((opt-true) (list "THEN"))
;           [nil (list "THEN")])
;        "created option rule works when symbol absent")))
;
;(deftest test-rep*
;  (let [rep*-true (p/rep* (p/semantics (p/lit "true") (fn [_] true)))]
;    ; Parse the first symbol in the program "true THEN"
;    (is (= ((rep*-true) ["true" "THEN"])
;           [[true] (list "THEN")])
;        "created zero-or-more-repetition rule works when symbol present singularly")
;    ; Parse the first symbol in the program "true true true THEN"
;    (is (= ((rep*-true) ["true" "true" "true" "THEN"])
;           [[true true true] (list "THEN")])
;        "created zero-or-more-repetition rule works when symbol present multiply")
;    ; Parse the first symbol in the program "THEN"
;    (is (= ((rep*-true) (list "THEN"))
;           [[] (list "THEN")])
;     "created zero-or-more-repetition rule works when symbol absent"))
;  (let [rep*-char (p/rep* (p/term #(not= % \")))]
;    ; Parse the first symbol in the program "THEN"
;    (is (= ((rep*-char) (list \a \b \c))
;           [[\a \b \c] nil])
;        "created zero-or-more-repetition rule with a negative subrule works with no remainder")))
;
;(deftest test-rep+
;  (let [rep+-true (p/rep+ (p/semantics (p/lit "true") (fn [_] true)))]
;    ; Parse the first symbol in the program "true THEN"
;    (is (= ((rep+-true) ["true" "THEN"])
;           [[true] (list "THEN")])
;        "created one-or-more-repetition rule works when symbol present singularly")
;    ; Parse the first symbol in the program "true true true THEN"
;    (is (= ((rep+-true) ["true" "true" "true" "THEN"])
;           [[true true true] (list "THEN")])
;        "created one-or-more-repetition rule works when symbol present multiply")
;    ; Parse the first symbol in the program "THEN"
;    (is (nil? ((rep+-true) (list "THEN")))
;        "created one-or-more-repetition rule fails when symbol absent")))
;
;(deftest test-except
;  ; except-rule = ("A" | "B" | "C") - "B" - "C";
;  (let [except-rule (p/except (p/alt (p/lit "A") (p/lit "B") (p/lit "C")) (p/lit "B")
;                                     (p/lit "C"))]
;    (is (= ((except-rule) (list "A" "B" "C")) ["A" (list "B" "C")])
;        "created exception rule works when symbol is not one of the syntatic exceptions")
;    (is (= ((except-rule) (list "B" "A" "C")) nil)
;        "created exception rule fails when symbol is one of the syntactic exceptions")
;    (is (= ((except-rule) (list "D" "A" "B")) nil)
;        "created exception rule fails when symbol does not fulfill subrule")))
; 
;(deftest test-factor=
;  ; rep=-rule = 3 * "A";
;  (let [tested-rule (p/factor= 3 (p/lit "A"))]
;    (is (= ((tested-rule) (list "A" "A" "A" "A" "C")) [["A" "A" "A"] (list "A" "C")])
;        "created factor= rule works when symbol fulfills all subrule multiples and leaves strict remainder")
;    (is (= ((tested-rule) (list "A" "A" "A" "C")) [["A" "A" "A"] (list "C")])
;        "created factor= rule works when symbol fulfills all subrule multiples only")
;    (is (= ((tested-rule) (list "A" "A" "C")) nil)
;        "created factor= rule fails when symbol does not fulfill all subrule multiples")
;    (is (= ((tested-rule) (list "D" "A" "B")) nil)
;        "created factor= rule fails when symbol does not fulfill subrule at all")))
; 
;(deftest test-factor<
;  (let [tested-rule (p/factor< 3 (p/lit "A"))]
;    (is (= ((tested-rule) (list "A" "A" "A" "A" "C")) [["A" "A"] (list "A" "A" "C")])
;        "created factor< rule works when symbol fulfills all subrule multiples and leaves strict remainder")
;    (is (= ((tested-rule) (list "A" "A" "A" "C")) [["A" "A"] (list "A" "C")])
;        "created factor< rule works when symbol fulfills all subrule multiples only")
;    (is (= ((tested-rule) (list "A" "A" "C")) [["A" "A"] (list "C")])
;        "created factor< rule works when symbol does not fulfill all subrule multiples")
;    (is (= ((tested-rule) (list "D" "A" "B")) [[] (list "D" "A" "B")])
;        "created factor< rule works when symbol does not fulfill subrule at all")))
; 
;(deftest test-factor<=
;  (let [tested-rule (p/factor<= 3 (p/lit "A"))]
;    (is (= ((tested-rule) (list "A" "A" "A" "A" "C")) [["A" "A" "A"] (list "A" "C")])
;        "created factor<= rule works when symbol fulfills all subrule multiples and leaves strict remainder")
;    (is (= ((tested-rule) (list "A" "A" "A" "C")) [["A" "A" "A"] (list "C")])
;        "created factor<= rule works when symbol fulfills all subrule multiples only")
;    (is (= ((tested-rule) (list "A" "A" "C")) [["A" "A"] (list "C")])
;        "created factor<= rule works when symbol does not fulfill all subrule multiples")
;    (is (= ((tested-rule) (list "D" "A" "B")) [[] (list "D" "A" "B")])
;        "created factor<= rule works when symbol does not fulfill subrule at all")))
;
;(deftest test-rep-predicate
;  (let [tested-rule-fn ((p/rep-predicate (partial > 3) (p/lit "A")))]
;    (is (= (tested-rule-fn (list "A" "A" "C")) [["A" "A"] (list "C")])
;        "created rep rule works when predicate returns true")
;    (is (= (tested-rule-fn (list "A" "A" "A")) nil)
;        "created rep rule fails when predicate returns false")
;    (is (= (tested-rule-fn (list "D" "A" "B")) [[] (list "D" "A" "B")])
;        "created rep rule succeeds when symbol does not fulfill subrule at all")))
;
;(deftest test-rep=
;  (let [tested-rule-fn ((p/rep= 3 (p/lit "A")))]
;    (is (= (tested-rule-fn (list "A" "A" "A" "C")) [["A" "A" "A"] (list "C")])
;        "created rep= rule works when symbol only fulfills all subrule multiples")
;    (is (= (tested-rule-fn (list "A" "A" "A" "A")) nil)
;        "created rep= rule fails when symbol exceeds subrule multiples")
;    (is (= (tested-rule-fn (list "A" "A" "C")) nil)
;        "created rep= rule fails when symbol does not fulfill all subrule multiples")
;    (is (= (tested-rule-fn (list "D" "A" "B")) nil)
;        "created rep= rule fails when symbol does not fulfill subrule at all")))
;
;(deftest test-rep<
;  (let [tested-rule-fn ((p/rep< 3 (p/lit "A")))]
;    (is (= (tested-rule-fn (list "A" "A" "C")) [["A" "A"] (list "C")])
;        "created rep< rule works when number of fulfilled rules is less than limit")
;    (is (= (tested-rule-fn (list "A" "A" "A")) nil)
;        "created rep< rule fails when number of fulfilled rules is equal to limit")
;    (is (= (tested-rule-fn (list "A" "A" "A" "A" "C")) nil)
;        "created rep< rule fails when symbol of fulfilled rules is more than limit")
;    (is (= (tested-rule-fn (list "D" "A" "B")) [[] (list "D" "A" "B")])
;        "created rep< rule succeeds when symbol does not fulfill subrule at all")))
;
;(deftest test-rep<=
;  (let [tested-rule-fn ((p/rep<= 3 (p/lit "A")))]
;    (is (= (tested-rule-fn (list "A" "A" "C")) [["A" "A"] (list "C")])
;        "created rep< rule works when number of fulfilled rules is less than limit")
;    (is (= (tested-rule-fn (list "A" "A" "A" "C")) [["A" "A" "A"] (list "C")])
;        "created rep< rule works when number of fulfilled rules is equal to limit")
;    (is (= (tested-rule-fn (list "A" "A" "A" "A" "C")) nil)
;        "created rep< rule fails when symbol of fulfilled rules is more than limit")
;    (is (= (tested-rule-fn (list "D" "A" "B")) [[] (list "D" "A" "B")])
;        "created rep< rule succeeds when symbol does not fulfill subrule at all")))
;
;(deftest test-validate
;  (is (= (((p/validate (p/lit "hi") #(= "hi" %))) ["hi" "THEN"])
;         ["hi" (list "THEN")])
;      "created validator rule succeeds when given subrule and validator succeed")
;  (is (= (((p/validate (p/lit "hi") #(= "RST" %))) "RST") nil)
;      "created validator rule fails when given subrule fails")
;  (is (= (((p/validate (p/lit "hi") #(= "hi" %))) "hi") nil)
;      "created validator rule fails when given validator fails"))
; 
;(deftest test-lit-conc-seq
;  ; Parse the first four symbols in the program "THEN"
;  (is (= (((p/lit-conc-seq "THEN")) (seq "THEN print 42;"))
;         [(vec "THEN") (seq " print 42;")])
;      "created literal-sequence rule is based on sequence of given token sequencible"))
; 
;(deftest test-lit-alt-seq
;  ; Parse the first four symbols in the program "B 2"
;  (is (= (((p/lit-alt-seq "ABCD")) (seq "B 2"))
;         [\B (seq " 2")])
;      "created literal-alternative-sequence rule works when literal symbol present in sequence")
;  (is (= (((p/lit-alt-seq "ABCD")) (seq "E 2")) nil)
;      "created literal-alternative-sequence rule fails when literal symbol not present in sequence"))
; 
;(deftest test-emptiness
;  ; Parse the emptiness before the first symbol
;  (is (= ((p/emptiness) (list "A" "B" "C"))
;         [nil (list "A" "B" "C")])
;      "emptyiness rule matches emptiness"))
; 
;(deftest test-followed-by
;  (is (= (((p/followed-by (p/lit "0") (p/lit "A"))) (list "0" "A" "B" "C"))
;         ["0" (list "A" "B" "C")])
;      "created followed-by rule works when base and followed-by subrules fulfilled")
;  (is (= (((p/followed-by (p/lit "0") (p/lit "A"))) (list "0" "B" "B")) nil)
;      "created followed-by rule fails when followed-by subrule fails"))

(time (run-tests))
