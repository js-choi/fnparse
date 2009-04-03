(ns name.choi.joshua.fnparse.test-parse
  (:use clojure.contrib.test-is [clojure.contrib.except :only [throw-arg]])
  (:require [name.choi.joshua.fnparse :as p]))
;(set! *warn-on-reflection* true)

(deftest test-term
  (is (= ((p/term #(= % "true")) ["true" "THEN"] {})
         ["true" (list "THEN") {}])
      "created terminal rule works when first token fulfills validator")
  (is (nil? ((p/term #(= % "true")) ["false" "THEN"] {}))
      "created terminal rule fails when first token fails validator")
  (is (= ((p/term #(= % "true")) ["true"] {})
         ["true" nil {}])
      "created terminal rule works when no remainder"))

(deftest test-lit
  (is (= ((p/lit "true") ["true" "THEN"] {})
         ["true" (list "THEN") {}])
      "created literal rule works when literal token present")
  (is (nil? ((p/lit "true") ["false" "THEN"] {}))
      "created literal rule fails when literal token not present"))

(deftest test-re-term
  (is (= ((p/re-term #"\s*true\s*") ["  true" "THEN"] {})
         ["  true" (list "THEN") {}])
      "created re-term rule works when first token matches regex")
  (is (nil? ((p/re-term #"\s*true\s*") ["false" "THEN"] {}))
      "created re-term rule fails when first token does not match regex"))

(deftest test-semantics
  (is (= ((p/semantics (p/lit "hi") #(str % \!)) ["hi" "THEN"] {})
         ["hi!" (list "THEN") {}])
      "created semantics rule applies semantic hook to valid result of given rule")
  (is (nil? ((p/semantics (p/lit "hi") #(str % \!)) ["RST"] {}))
      "created semantics rule fails when given subrule fails")
  (is (= ((p/semantics (p/with-info (p/lit "hi") #(assoc %1 :a %2)) #(str % \!))
          ["hi" "THEN"] {})
         ["hi!" (list "THEN") {:a "hi"}])
      "created semantics rule passes info to subrule"))

(deftest test-constant-semantics
  (is (= ((p/constant-semantics (p/lit "hi") (hash-map :a 1)) ["hi" "THEN"] {})
         [{:a 1} (list "THEN") {}])
      "created constant sem rule returns constant value when given subrule does not fail"))

(deftest test-validate
  (is (= ((p/validate (p/lit "hi") #(= "hi" %)) ["hi" "THEN"] {})
         ["hi" (list "THEN") {}])
      "created validator rule succeeds when given subrule and validator succeed")
  (is (= ((p/validate (p/lit "hi") #(= "RST" %)) "RST" {}) nil)
      "created validator rule fails when given subrule fails")
  (is (= ((p/validate (p/lit "hi") #(= "hi" %)) "hi" {}) nil)
      "created validator rule fails when given validator fails"))
 
(deftest test-validate-remainder
  (is (= ((p/validate-remainder (p/lit "hi") (fn [r i] (= "THEN" (first r))))
          ["hi" "THEN"] {})
         ["hi" (list "THEN") {}])
      "created remainder-validating rule succeeds when given subrule and validator succeed")
  (is (= ((p/validate-remainder (p/lit "hi") (fn [r i] (= "THEN" (first r))))
          ["bye" "THEN"] {})
         nil)
      "created remainder-validating rule fails when given subrule fails")
  (is (= ((p/validate-remainder (p/lit "hi") (fn [r i] (= "THEN" (first r))))
          ["hi" "WELL"] {})
         nil)
      "created remainder-validating rule fails when given validator fails"))
 
(deftest test-validate-info
  (let [subrule (p/lit "hi")]
    (is (= ((p/validate-info subrule #(contains? % :b)) ["hi" "THEN"] {:b 1})
           ["hi" (list "THEN") {:b 1}])
        "created info-validating rule succeeds when given subrule and validator succeed")
    (is (= ((p/validate-info subrule #(contains? % :b)) ["bye" "THEN"] {:b 1}) nil)
        "created info-validating rule fails when given subrule fails")
    (is (= ((p/validate-info subrule #(contains? % :b)) ["hi" "THEN"] {}) nil)
        "created info-validating rule fails when given validator fails")))
 
(deftest test-conc
  (let [identifier (p/with-info (p/term string?) (fn [m p] (assoc m :b 1)))
        equals-operator (p/semantics (p/lit "=") keyword)
        answer (p/with-info (p/lit "42") (fn [m p] (assoc m :c 3)))
        truth (p/conc identifier equals-operator answer)]
    ; Parse the first symbols in the program "answer = 42 THEN"
    (is (= (truth ["answer" "=" "42" "THEN"] {:a 50})
           [["answer" := "42"] (list "THEN") {:a 50, :b 1, :c 3}])
        "created concatenation rule works when valid symbols are present in order")
    ; Parse the first symbols in the program "answer = 42 THEN"
    (is (= (truth ["answer" "42" "=" "THEN"] {}) nil)
        "created concatenation rule fails when invalid symbols present")))

(deftest test-alt
  (let [literal-true (p/constant-semantics (p/lit "true") true)
        literal-false (p/constant-semantics (p/lit "false") false)
        literal-boolean (p/alt literal-true literal-false)]
    ; Parse the first symbol in the program "false THEN"
    (is (= (literal-boolean ["false" "THEN"] {})
           [false (list "THEN") {}])
        "created alternatives rule works with first valid rule product")
    ; Parse the first symbol in the program "aRSTIR"
    (is (nil? (literal-boolean ["aRSTIR"] {}))
        "created alternatives rule fails when no valid rule product present")))

(deftest test-opt
  (let [opt-true (p/opt (p/semantics (p/lit "true") (fn [_] true)))]
    ; Parse the first symbol in the program "true THEN"
    (is (= (opt-true ["true" "THEN"] {})
           [true (list "THEN") {}])
        "created option rule works when symbol present")
    ; Parse the first symbol in the program "THEN"
    (is (= (opt-true (list "THEN") {})
           [nil (list "THEN") {}])
        "created option rule works when symbol absent")))

(deftest test-rep*
  (let [rep*-true (p/rep* (p/with-info (p/constant-semantics (p/lit "true") true)
                                       (fn [i p] (assoc i :a (inc (i :a))))))]
    ; Parse the first symbol in the program "true THEN"
    (is (= (rep*-true ["true" "THEN"] {:a 3})
           [[true] (list "THEN") {:a 4}])
        "created zero-or-more-repetition rule works when symbol present singularly")
    ; Parse the first symbol in the program "true true true THEN"
    (is (= (rep*-true ["true" "true" "true" "THEN"] {:a 3})
           [[true true true] (list "THEN") {:a 6}])
        "created zero-or-more-repetition rule works when symbol present multiply")
    ; Parse the first symbol in the program "THEN"
    (is (= (rep*-true ["THEN"] {})
           [[] (list "THEN") {}])
     "created zero-or-more-repetition rule works when symbol absent"))
  (let [rep*-char (p/rep* (p/term #(not= % \")))]
    ; Parse the first symbol in the program "THEN"
    (is (= (rep*-char [\a \b \c] {})
           [[\a \b \c] nil {}])
        "created zero-or-more-repetition rule with a negative subrule works with no remainder"))
  (let [letter (p/term int)]
    (is (= ((p/rep* letter) [\a \a \a] {})
           [[\a \a \a] nil {}])
        "created zero-or-more-repetition rule works with a subrule that cannot accept nil and no remainder")))

(deftest test-rep+
  (let [rep+-true (p/rep+ (p/constant-semantics (p/lit "true") true))]
    ; Parse the first symbol in the program "true THEN"
    (is (= (rep+-true ["true" "THEN"] {})
           [[true] (list "THEN") {}])
        "created one-or-more-repetition rule works when symbol present singularly")
    ; Parse the first symbol in the program "true true true THEN"
    (is (= (rep+-true ["true" "true" "true" "THEN"] {})
           [[true true true] (list "THEN") {}])
        "created one-or-more-repetition rule works when symbol present multiply")
    ; Parse the first symbol in the program "THEN"
    (is (nil? (rep+-true (list "THEN") {}))
        "created one-or-more-repetition rule fails when symbol absent")))

(deftest test-except
  ; except-rule = ("A" | "B" | "C") - "B" - "C";
  (let [except-rule (p/except (p/alt (p/lit "A") (p/lit "B") (p/lit "C"))
                              (p/lit "B") (p/with-info (p/lit "C") (fn [i p] {:b "wrong"})))]
    (is (= (except-rule (list "A" "B" "C") {:a 1}) ["A" (list "B" "C") {:a 1}])
        "created exception rule works when symbol is not one of the syntatic exceptions")
    (is (= (except-rule (list "B" "A" "C") {}) nil)
        "created exception rule fails when symbol is one of the syntactic exceptions")
    (is (= (except-rule (list "D" "A" "B") {}) nil)
        "created exception rule fails when symbol does not fulfill subrule")))

(deftest test-factor=
  ; rep=-rule = 3 * "A";
  (let [tested-rule-3 (p/factor= 3 (p/lit "A")), tested-rule-0 (p/factor= 0 (p/lit "A"))]
    (is (= (tested-rule-3 (list "A" "A" "A" "A" "C") {})
           [["A" "A" "A"] (list "A" "C") {}])
        "created factor= rule works when symbol fulfills all subrule multiples and leaves strict remainder")
    (is (= (tested-rule-3 (list "A" "A" "A" "C") {}) [["A" "A" "A"] (list "C") {}])
        "created factor= rule works when symbol fulfills all subrule multiples only")
    (is (= (tested-rule-3 (list "A" "A" "C") {}) nil)
        "created factor= rule fails when symbol does not fulfill all subrule multiples")
    (is (= (tested-rule-3 (list "D" "A" "B") {}) nil)
        "created factor= rule fails when symbol does not fulfill subrule at all")
    (is (= (tested-rule-0 (list "D" "A" "B") {}) [[] (list "D" "A" "B") {}])
        "created factor= rule works when symbol fulfils zero multiples and factor is zero")))

(deftest test-factor<
  (let [tested-rule (p/factor< 3 (p/lit "A"))]
    (is (= (tested-rule (list "A" "A" "A" "A" "C") {}) [["A" "A"] (list "A" "A" "C") {}])
        "created factor< rule works when symbol fulfills all subrule multiples and leaves strict remainder")
    (is (= (tested-rule (list "A" "A" "A" "C") {}) [["A" "A"] (list "A" "C") {}])
        "created factor< rule works when symbol fulfills all subrule multiples only")
    (is (= (tested-rule (list "A" "A" "C") {}) [["A" "A"] (list "C") {}])
        "created factor< rule works when symbol does not fulfill all subrule multiples")
    (is (= (tested-rule (list "D" "A" "B") {}) [[] (list "D" "A" "B") {}])
        "created factor< rule works when symbol does not fulfill subrule at all")))

(deftest test-factor<=
  (let [tested-rule (p/factor<= 3 (p/lit "A"))]
    (is (= (tested-rule (list "A" "A" "A" "A" "C") {}) [["A" "A" "A"] (list "A" "C") {}])
        "created factor<= rule works when symbol fulfills all subrule multiples and leaves strict remainder")
    (is (= (tested-rule (list "A" "A" "A" "C") {}) [["A" "A" "A"] (list "C") {}])
        "created factor<= rule works when symbol fulfills all subrule multiples only")
    (is (= (tested-rule (list "A" "A" "C") {}) [["A" "A"] (list "C") {}])
        "created factor<= rule works when symbol does not fulfill all subrule multiples")
    (is (= (tested-rule (list "D" "A" "B") {}) [[] (list "D" "A" "B") {}])
        "created factor<= rule works when symbol does not fulfill subrule at all")))

(deftest test-rep-predicate
  (let [tested-rule-fn (p/rep-predicate (partial > 3) (p/lit "A"))]
    (is (= (tested-rule-fn (list "A" "A" "C") {}) [["A" "A"] (list "C") {}])
        "created rep rule works when predicate returns true")
    (is (= (tested-rule-fn (list "A" "A" "A") {}) nil)
        "created rep rule fails when predicate returns false")
    (is (= (tested-rule-fn (list "D" "A" "B") {}) [[] (list "D" "A" "B") {}])
        "created rep rule succeeds when symbol does not fulfill subrule at all")))

(deftest test-rep=
  (let [tested-rule-fn (p/rep= 3 (p/lit "A"))]
    (is (= (tested-rule-fn (list "A" "A" "A" "C") {}) [["A" "A" "A"] (list "C") {}])
        "created rep= rule works when symbol only fulfills all subrule multiples")
    (is (= (tested-rule-fn (list "A" "A" "A" "A") {}) nil)
        "created rep= rule fails when symbol exceeds subrule multiples")
    (is (= (tested-rule-fn (list "A" "A" "C") {}) nil)
        "created rep= rule fails when symbol does not fulfill all subrule multiples")
    (is (= (tested-rule-fn (list "D" "A" "B") {}) nil)
        "created rep= rule fails when symbol does not fulfill subrule at all")))

(deftest test-rep<
  (let [tested-rule-fn (p/rep< 3 (p/lit "A"))]
    (is (= (tested-rule-fn (list "A" "A" "C") {}) [["A" "A"] (list "C") {}])
        "created rep< rule works when number of fulfilled rules is less than limit")
    (is (= (tested-rule-fn (list "A" "A" "A") {}) nil)
        "created rep< rule fails when number of fulfilled rules is equal to limit")
    (is (= (tested-rule-fn (list "A" "A" "A" "A" "C") {}) nil)
        "created rep< rule fails when symbol of fulfilled rules is more than limit")
    (is (= (tested-rule-fn (list "D" "A" "B") {}) [[] (list "D" "A" "B") {}])
        "created rep< rule succeeds when symbol does not fulfill subrule at all")))

(deftest test-rep<=
  (let [tested-rule-fn (p/rep<= 3 (p/lit "A"))]
    (is (= (tested-rule-fn (list "A" "A" "C") {}) [["A" "A"] (list "C") {}])
        "created rep< rule works when number of fulfilled rules is less than limit")
    (is (= (tested-rule-fn (list "A" "A" "A" "C") {}) [["A" "A" "A"] (list "C") {}])
        "created rep< rule works when number of fulfilled rules is equal to limit")
    (is (= (tested-rule-fn (list "A" "A" "A" "A" "C") {}) nil)
        "created rep< rule fails when symbol of fulfilled rules is more than limit")
    (is (= (tested-rule-fn (list "D" "A" "B") {}) [[] (list "D" "A" "B") {}])
        "created rep< rule succeeds when symbol does not fulfill subrule at all")))

(deftest test-lit-conc-seq
  ; Parse the first four symbols in the program "THEN"
  (is (= ((p/lit-conc-seq "THEN") (seq "THEN print 42;") {})
         [(vec "THEN") (seq " print 42;") {}])
      "created literal-sequence rule is based on sequence of given token sequencible"))

(deftest test-lit-alt-seq
  ; Parse the first four symbols in the program "B 2"
  (is (= ((p/lit-alt-seq "ABCD") (seq "B 2") {})
         [\B (seq " 2") {}])
      "created literal-alternative-sequence rule works when literal symbol present in sequence")
  (is (= ((p/lit-alt-seq "ABCD") (seq "E 2") {}) nil)
      "created literal-alternative-sequence rule fails when literal symbol not present in sequence"))

(deftest test-emptiness
  ; Parse the emptiness before the first symbol
  (is (= (p/emptiness (list "A" "B" "C") {})
         [nil (list "A" "B" "C") {}])
      "emptiness rule matches emptiness"))

(deftest test-followed-by
  (is (= ((p/followed-by (p/lit "0") (p/lit "A")) (list "0" "A" "B" "C") {})
         ["0" (list "A" "B" "C") {}])
      "created followed-by rule works when base and followed-by subrules fulfilled")
  (is (= ((p/followed-by (p/lit "0")
                          (p/validate-info (p/lit "A") #(contains? % :a)))
          (list "0" "A" "B" "C") {:a 5})
         ["0" (list "A" "B" "C") {:a 5}])
      "created followed-by rule passes info to followed-by subrule")
  (is (= ((p/followed-by (p/lit "0") (p/lit "A")) (list "0" "B" "B") {}) nil)
      "created followed-by rule fails when followed-by subrule fails"))

(deftest test-with-info
  (is (= ((p/with-info (p/lit "true") (fn [i p] (assoc i :column (inc (:column i)))))
          ["true" "THEN"] {:column 13, :line 2})
         ["true" (list "THEN") {:column 14, :line 2}])
      "created info rule applies new info when valid")
  (is (= ((p/with-info (p/lit "true") (constantly {:a 5})) ["false"] {}) nil)
      "created info rule fails when subrule fails"))

(deftest test-failpoint
  (let [failing-rule (p/failpoint (p/lit "A")
                                  (fn [tokens info]
                                    (throw-arg "ERROR at line %s" (:line info))))]
    (is (= (failing-rule ["A"] {:line 3}) ["A" nil {:line 3}])
        "failing rules succeed when their subrules are fulfilled")
    (is (thrown-with-msg? IllegalArgumentException #"ERROR at line 3"
          (failing-rule ["B"] {:line 3})
        "failing rules fail with given exceptions when their subrules fail"))))

(deftest test-do-effects-before
  (let [effect-rule (p/do-effects-before (p/lit "A")
                                         (fn [tokens info]
                                           (println "YES" tokens info)))]
    (is (= (with-out-str
             (is (= (effect-rule ["A" "B"] {:line 3}) ["A" (list "B") {:line 3}])
                 "pre-effect rules succeed when their subrules are fulfilled"))
           "YES [A B] {:line 3}\n")
        "pre-effect rules should call their effect with tokens and info before processing")))

(deftest test-anything
  ; Parse the first symbol
  (is (= (p/anything (list "A" "B" "C") {})
         ["A" (list "B" "C") {}])
      "anything rule matches first token"))

(deftest test-product-context
  (let [receiving-rule-maker (fn rule-maker [n]
                               (p/factor= (Integer/parseInt (str n)) (p/lit \a)))
        digit (p/semantics p/anything #(Integer/parseInt (str %)))
        rule (p/product-context [n digit, m digit]
               (receiving-rule-maker (+ n m)))]
    (is (= (rule (seq "31aaaa23aa") {})
           [[3 1 [\a \a \a \a]] (seq "23aa") {}]))
    (is (= (rule (seq "31aaa23aa") {}) nil)))
  (let [receiving-rule-maker (fn rule-maker [x]
                               (p/rep+ (p/lit x)))
        header (p/semantics (p/conc p/anything p/anything)
                            #(hash-map :token (% 0), :type (% 1)))
        rule (p/product-context [{token :token} header]
               (receiving-rule-maker token))]
    (is (= (rule (seq "a+aasdf") {})
           [[{:type \+, :token \a} [\a \a]] (seq "sdf") {}]))
    (is (= (rule (seq "+asdf") {}) nil))))

(deftest test-product-invisible-context
  (let [digit (p/semantics p/anything #(Integer/parseInt (str %)))
        receiving-rule-maker (fn rule-maker [n]
                               (p/factor= (Integer/parseInt (str n)) p/anything))
        rule (p/product-invisible-context [n digit, m digit]
               (receiving-rule-maker (+ n m)))]
    (is (= (rule (seq "31aaaa") {})
           [[3 1 [\3 \1 \a \a]] (seq "aa") {}]))))

(deftest test-match-remainder
  (is (= ((p/match-remainder (p/lit "hi") (p/lit "THEN")) ["hi" "THEN"] {})
         [["hi" "THEN"] (list "THEN") {}])
      "created remainder-matching rule succeeds when given subrule and matching succeed")
  (is (= ((p/match-remainder (p/lit "hi") (p/lit "THEN")) ["bye" "THEN"] {})
         nil)
      "created remainder-matching rule fails when given subrule fails")
  (is (= ((p/match-remainder (p/lit "hi") (p/lit "THEN")) ["hi" "WELL"] {})
         nil)
      "created remainder-matching rule fails when given matching fails"))
 
(time (run-tests))
