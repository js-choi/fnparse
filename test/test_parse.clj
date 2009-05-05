(ns name.choi.joshua.fnparse.parse
  (:use clojure.contrib.test-is clojure.contrib.monads
        [clojure.contrib.except :only [throw-arg]])
  (:require [name.choi.joshua.fnparse :as p]))
;(set! *warn-on-reflection* true)

(deftest emptiness
  (is (= (p/emptiness {:remainder (list "A" "B" "C")})
         [nil {:remainder (list "A" "B" "C")}])
      "emptiness rule matches emptiness"))

(deftest anything
  (is (= (p/anything {:remainder "ABC"})
         [\A {:remainder (seq "BC")}])
      "anything rule matches first token"))

(deftest term
  (is (= ((p/term (partial = "true")) {:remainder ["true" "THEN"]})
         ["true" {:remainder (list "THEN")}])
      "created terminal rule works when first token fulfills validator")
  (is (nil? ((p/term (partial = "true")) {:remainder ["false" "THEN"]}))
      "created terminal rule fails when first token fails validator")
  (is (= ((p/term (partial = "true")) {:remainder ["true"]})
         ["true" {:remainder nil}])
      "created terminal rule works when no remainder"))

(deftest lit
  (is (= ((p/lit "true") {:remainder ["true" "THEN"]})
         ["true" {:remainder (list "THEN")}])
      "created literal rule works when literal token present")
  (is (nil? ((p/lit "true") {:remainder ["false" "THEN"]}))
      "created literal rule fails when literal token not present"))

(deftest re-term
  (is (= ((p/re-term #"\s*true\s*") {:remainder ["  true" "THEN"]})
         ["  true" {:remainder (list "THEN")}])
      "created re-term rule works when first token matches regex")
  (is (nil? ((p/re-term #"\s*true\s*") {:remainder ["false" "THEN"]}))
      "created re-term rule fails when first token does not match regex"))

(deftest followed-by
  (is (= ((p/followed-by (p/lit \a)) {:remainder "abc"}) [\a {:remainder "abc"}]))
  (is (nil? ((p/followed-by (p/lit \a)) {:remainder "bcd"}))))

(deftest not-followed-by
  (is (= ((p/not-followed-by (p/lit \a)) {:remainder "bcd"}) [true {:remainder "bcd"}]))
  (is (nil? ((p/not-followed-by (p/lit \a)) {:remainder "abc"}))))

(deftest complex
  (is (= ((p/complex [a (p/lit "hi")] (str a "!")) {:remainder ["hi" "THEN"]})
         ["hi!" {:remainder (list "THEN")}])
      "created complex rule applies semantic hook to valid result of given rule")
  (is (nil? ((p/complex [a (p/lit "hi")] (str a \!)) {:remainder ["RST"]}))
      "created complex rule fails when a given subrule fails")
  (is (= ((p/complex [a (p/lit "hi")] (str a \!)) {:remainder ["hi" "THEN"], :a "hi"})
         ["hi!" {:remainder (list "THEN"), :a "hi"}])
      "created complex rule passes rest of state to subrule")
  (is (= ((p/complex [a (p/lit "hi") b (p/lit "THEN")] [(str a "!") b])
          {:remainder ["hi" "THEN" "bye"]})
         [["hi!" "THEN"] {:remainder (list "bye")}])
      "created complex rule succeeds when all subrules fulfilled in order")
  (is (nil? ((p/complex [a (p/lit "hi") b (p/lit "THEN")] [(str a "!") b])
          {:remainder ["hi" "bye" "boom"]}))
      "created complex rule fails when one subrule fails"))

(deftest semantics
  (is (= ((p/semantics (p/lit "hi") #(str % "!")) {:remainder ["hi" "THEN"]})
         ["hi!" {:remainder (list "THEN")}])
      "created simple semantic rule applies semantic hook to valid result of given rule"))

(deftest constant-semantics
  (is (= ((p/constant-semantics (p/lit "hi") {:a 1}) {:remainder ["hi" "THEN"]})
         [{:a 1} {:remainder (list "THEN")}])
      "created constant sem rule returns constant value when given subrule does not fail"))

(deftest validate
  (is (= ((p/validate (p/lit "hi") (partial = "hi")) {:remainder ["hi" "THEN"]})
         ["hi" {:remainder (list "THEN")}])
      "created validator rule succeeds when given subrule and validator succeed")
  (is (nil? ((p/validate (p/lit "hi") (partial = "RST")) {:remainder ["RST"]}))
      "created validator rule fails when given subrule fails")
  (is (nil? ((p/validate (p/lit "hi") (partial = "hi")) {:remainder "hi"}))
      "created validator rule fails when given validator fails"))

(deftest get-remainder
  (is (= ((p/complex [remainder p/get-remainder] remainder) {:remainder ["hi" "THEN"]})
         [["hi" "THEN"] {:remainder ["hi" "THEN"]}])))

;(deftest validate-remainder
;  (is (= ((p/validate-remainder (p/lit "hi") (fn [r] (= "THEN" (first r))))
;          {:remainder ["hi" "THEN"]})
;         ["hi" (list "THEN") {}])
;      "created remainder-validating rule succeeds when given subrule and validator succeed")
;  (is (nil? ((p/validate-remainder (p/lit "hi") (fn [r] (= "THEN" (first r))))
;          {:remainder ["bye" "THEN"]}))
;      "created remainder-validating rule fails when given subrule fails")
;  (is (= ((p/validate-remainder (p/lit "hi") (fn [r] (= "THEN" (first r))))
;          {:remainder ["hi" "WELL"]}))
;      "created remainder-validating rule fails when given validator fails"))
 
;(deftest validate-info
;  (let [subrule (p/lit "hi")]
;    (is (= ((p/validate-info subrule #(contains? % :b)) ["hi" "THEN"] {:b 1})
;           ["hi" (list "THEN") {:b 1}])
;        "created info-validating rule succeeds when given subrule and validator succeed")
;    (is (= ((p/validate-info subrule #(contains? % :b)) ["bye" "THEN"] {:b 1}) nil)
;        "created info-validating rule fails when given subrule fails")
;    (is (= ((p/validate-info subrule #(contains? % :b)) ["hi" "THEN"] {}) nil)
;        "created info-validating rule fails when given validator fails")))
; 

(deftest remainder-peek
  (is (= (p/remainder-peek {:remainder (seq "ABC")})
         [\A {:remainder (seq "ABC")}])))

(deftest conc
  (is (= ((p/conc (p/lit "hi") (p/lit "THEN")) {:remainder ["hi" "THEN" "bye"]})
         [["hi" "THEN"] {:remainder (list "bye")}])
      "created concatenated rule succeeds when all subrules fulfilled in order")
  (is (nil? ((p/conc (p/lit "hi") (p/lit "THEN")) {:remainder ["hi" "bye" "boom"]}))
      "created concatenated rule fails when one subrule fails"))

(deftest alt
  (let [literal-true (p/lit "true")
        literal-false (p/lit "false")
        literal-boolean (p/alt literal-true literal-false)]
    (is (= (literal-boolean {:remainder ["false" "THEN"]})
           ["false" {:remainder (list "THEN")}])
        "created alternatives rule works with first valid rule product")
    (is (nil? (literal-boolean {:remainder ["aRSTIR"]}))
        "created alternatives rule fails when no valid rule product present")))

(deftest lit-conc-seq
  (is (= ((p/lit-conc-seq "THEN") {:remainder "THEN print 42;"})
         [(vec "THEN") {:remainder (seq " print 42;")}])
      "created literal-sequence rule is based on sequence of given token sequencible"))

(deftest lit-alt-seq
  (is (= ((p/lit-alt-seq "ABCD") {:remainder (seq "B 2")})
         [\B {:remainder (seq " 2")}])
      (str "created literal-alternative-sequence rule works when literal symbol present in"
           "sequence"))
  (is (nil? ((p/lit-alt-seq "ABCD") {:remainder (seq "E 2")}))
      (str "created literal-alternative-sequence rule fails when literal symbol not present"
           "in sequence")))

(deftest opt
  (let [opt-true (p/opt (p/lit "true"))]
    ; Parse the first symbol in the program "true THEN"
    (is (= (opt-true {:remainder ["true" "THEN"]})
           ["true" {:remainder (list "THEN")}])
        "created option rule works when symbol present")
    ; Parse the first symbol in the program "THEN"
    (is (= (opt-true {:remainder (list "THEN")})
           [nil {:remainder (list "THEN")}])
        "created option rule works when symbol absent")))

(deftest rep*
  (let [rep*-true (p/rep* (p/lit true))]
    (is (= (rep*-true {:remainder [true "THEN"], :a 3})
           [[true] {:remainder (list "THEN"), :a 3}])
        "created zero-or-more-repetition rule works when symbol present singularly")
    (is (= (rep*-true {:remainder [true true true "THEN"], :a 3})
           [[true true true] {:remainder (list "THEN"), :a 3}])
        "created zero-or-more-repetition rule works when symbol present multiply")
    (is (= (rep*-true {:remainder ["THEN"], :a 3})
           [nil {:remainder (list "THEN"), :a 3}])
     "created zero-or-more-repetition rule works when symbol absent")
    (is (= (rep*-true {:remainder [true true true]})
           [[true true true] {:remainder nil}])
        "created zero-or-more-repetition rule works with no remainder")))

(deftest rep+
  (let [rep+-true (p/rep+ (p/lit true))]
    (is (= (rep+-true {:remainder [true "THEN"]})
           [[true] {:remainder (list "THEN")}])
        "created one-or-more-repetition rule works when symbol present singularly")
    (is (= (rep+-true {:remainder [true true true "THEN"]})
           [[true true true] {:remainder (list "THEN")}])
        "created one-or-more-repetition rule works when symbol present multiply")
    ; Parse the first symbol in the program "THEN"
    (is (nil? (rep+-true {:remainder (list "THEN")}))
        "created one-or-more-repetition rule fails when symbol absent")))

(deftest except
  (let [except-rule (p/except (p/lit-alt-seq "ABC") (p/lit \B) (p/lit \C))]
    (is (= (except-rule {:remainder (seq "ABC"), :a 1}) [\A {:remainder (seq "BC"), :a 1}])
        "created exception rule works when symbol is not one of the syntatic exceptions")
    (is (nil? (except-rule {:remainder (seq "BAC")}))
        "created exception rule fails when symbol is one of the syntactic exceptions")
    (is (nil? (except-rule {:remainder (seq "DAB")}))
        "created exception rule fails when symbol does not fulfill subrule")))

;(deftest factor=
;  ; rep=-rule = 3 * "A";
;  (let [tested-rule-3 (p/factor= 3 (p/lit "A")), tested-rule-0 (p/factor= 0 (p/lit "A"))]
;    (is (= (tested-rule-3 (list "A" "A" "A" "A" "C") {})
;           [["A" "A" "A"] (list "A" "C") {}])
;        "created factor= rule works when symbol fulfills all subrule multiples and leaves strict remainder")
;    (is (= (tested-rule-3 (list "A" "A" "A" "C") {}) [["A" "A" "A"] (list "C") {}])
;        "created factor= rule works when symbol fulfills all subrule multiples only")
;    (is (= (tested-rule-3 (list "A" "A" "C") {}) nil)
;        "created factor= rule fails when symbol does not fulfill all subrule multiples")
;    (is (= (tested-rule-3 (list "D" "A" "B") {}) nil)
;        "created factor= rule fails when symbol does not fulfill subrule at all")
;    (is (= (tested-rule-0 (list "D" "A" "B") {}) [[] (list "D" "A" "B") {}])
;        "created factor= rule works when symbol fulfils zero multiples and factor is zero")))
;
;(deftest factor<
;  (let [tested-rule (p/factor< 3 (p/lit "A"))]
;    (is (= (tested-rule (list "A" "A" "A" "A" "C") {}) [["A" "A"] (list "A" "A" "C") {}])
;        "created factor< rule works when symbol fulfills all subrule multiples and leaves strict remainder")
;    (is (= (tested-rule (list "A" "A" "A" "C") {}) [["A" "A"] (list "A" "C") {}])
;        "created factor< rule works when symbol fulfills all subrule multiples only")
;    (is (= (tested-rule (list "A" "A" "C") {}) [["A" "A"] (list "C") {}])
;        "created factor< rule works when symbol does not fulfill all subrule multiples")
;    (is (= (tested-rule (list "D" "A" "B") {}) [[] (list "D" "A" "B") {}])
;        "created factor< rule works when symbol does not fulfill subrule at all")))
;
;(deftest factor<=
;  (let [tested-rule (p/factor<= 3 (p/lit "A"))]
;    (is (= (tested-rule (list "A" "A" "A" "A" "C") {}) [["A" "A" "A"] (list "A" "C") {}])
;        "created factor<= rule works when symbol fulfills all subrule multiples and leaves strict remainder")
;    (is (= (tested-rule (list "A" "A" "A" "C") {}) [["A" "A" "A"] (list "C") {}])
;        "created factor<= rule works when symbol fulfills all subrule multiples only")
;    (is (= (tested-rule (list "A" "A" "C") {}) [["A" "A"] (list "C") {}])
;        "created factor<= rule works when symbol does not fulfill all subrule multiples")
;    (is (= (tested-rule (list "D" "A" "B") {}) [[] (list "D" "A" "B") {}])
;        "created factor<= rule works when symbol does not fulfill subrule at all")))
;
;(deftest rep-predicate
;  (let [tested-rule-fn (p/rep-predicate (partial > 3) (p/lit "A"))]
;    (is (= (tested-rule-fn (list "A" "A" "C") {}) [["A" "A"] (list "C") {}])
;        "created rep rule works when predicate returns true")
;    (is (= (tested-rule-fn (list "A" "A" "A") {}) nil)
;        "created rep rule fails when predicate returns false")
;    (is (= (tested-rule-fn (list "D" "A" "B") {}) [[] (list "D" "A" "B") {}])
;        "created rep rule succeeds when symbol does not fulfill subrule at all")))
;
;(deftest rep=
;  (let [tested-rule-fn (p/rep= 3 (p/lit "A"))]
;    (is (= (tested-rule-fn (list "A" "A" "A" "C") {}) [["A" "A" "A"] (list "C") {}])
;        "created rep= rule works when symbol only fulfills all subrule multiples")
;    (is (= (tested-rule-fn (list "A" "A" "A" "A") {}) nil)
;        "created rep= rule fails when symbol exceeds subrule multiples")
;    (is (= (tested-rule-fn (list "A" "A" "C") {}) nil)
;        "created rep= rule fails when symbol does not fulfill all subrule multiples")
;    (is (= (tested-rule-fn (list "D" "A" "B") {}) nil)
;        "created rep= rule fails when symbol does not fulfill subrule at all")))
;
;(deftest rep<
;  (let [tested-rule-fn (p/rep< 3 (p/lit "A"))]
;    (is (= (tested-rule-fn (list "A" "A" "C") {}) [["A" "A"] (list "C") {}])
;        "created rep< rule works when number of fulfilled rules is less than limit")
;    (is (= (tested-rule-fn (list "A" "A" "A") {}) nil)
;        "created rep< rule fails when number of fulfilled rules is equal to limit")
;    (is (= (tested-rule-fn (list "A" "A" "A" "A" "C") {}) nil)
;        "created rep< rule fails when symbol of fulfilled rules is more than limit")
;    (is (= (tested-rule-fn (list "D" "A" "B") {}) [[] (list "D" "A" "B") {}])
;        "created rep< rule succeeds when symbol does not fulfill subrule at all")))
;
;(deftest rep<=
;  (let [tested-rule-fn (p/rep<= 3 (p/lit "A"))]
;    (is (= (tested-rule-fn (list "A" "A" "C") {}) [["A" "A"] (list "C") {}])
;        "created rep< rule works when number of fulfilled rules is less than limit")
;    (is (= (tested-rule-fn (list "A" "A" "A" "C") {}) [["A" "A" "A"] (list "C") {}])
;        "created rep< rule works when number of fulfilled rules is equal to limit")
;    (is (= (tested-rule-fn (list "A" "A" "A" "A" "C") {}) nil)
;        "created rep< rule fails when symbol of fulfilled rules is more than limit")
;    (is (= (tested-rule-fn (list "D" "A" "B") {}) [[] (list "D" "A" "B") {}])
;        "created rep< rule succeeds when symbol does not fulfill subrule at all")))
;
;(deftest emptiness
;  ; Parse the emptiness before the first symbol
;  (is (= (p/emptiness (list "A" "B" "C") {})
;         [nil (list "A" "B" "C") {}])
;      "emptiness rule matches emptiness"))
;
;(deftest followed-by
;  (is (= ((p/followed-by (p/lit "0") (p/lit "A")) (list "0" "A" "B" "C") {})
;         ["0" (list "A" "B" "C") {}])
;      "created followed-by rule works when base and followed-by subrules fulfilled")
;  (is (= ((p/followed-by (p/lit "0")
;                          (p/validate-info (p/lit "A") #(contains? % :a)))
;          (list "0" "A" "B" "C") {:a 5})
;         ["0" (list "A" "B" "C") {:a 5}])
;      "created followed-by rule passes info to followed-by subrule")
;  (is (= ((p/followed-by (p/lit "0") (p/lit "A")) (list "0" "B" "B") {}) nil)
;      "created followed-by rule fails when followed-by subrule fails"))
;
;(deftest with-info
;  (is (= ((p/with-info (p/lit "true") (fn [i p] (assoc i :column (inc (:column i)))))
;          ["true" "THEN"] {:column 13, :line 2})
;         ["true" (list "THEN") {:column 14, :line 2}])
;      "created info rule applies new info when valid")
;  (is (= ((p/with-info (p/lit "true") (constantly {:a 5})) ["false"] {}) nil)
;      "created info rule fails when subrule fails"))
;
;(deftest failpoint
;  (let [failing-rule (p/failpoint (p/lit "A")
;                                  (fn [tokens info]
;                                    (throw-arg "ERROR at line %s" (:line info))))]
;    (is (= (failing-rule ["A"] {:line 3}) ["A" nil {:line 3}])
;        "failing rules succeed when their subrules are fulfilled")
;    (is (thrown-with-msg? IllegalArgumentException #"ERROR at line 3"
;          (failing-rule ["B"] {:line 3})
;        "failing rules fail with given exceptions when their subrules fail"))))
;
;(deftest do-effects-before
;  (let [effect-rule (p/do-effects-before (p/lit "A")
;                                         (fn [tokens info]
;                                           (println "YES" tokens info)))]
;    (is (= (with-out-str
;             (is (= (effect-rule ["A" "B"] {:line 3}) ["A" (list "B") {:line 3}])
;                 "pre-effect rules succeed when their subrules are fulfilled"))
;           "YES [A B] {:line 3}\n")
;        "pre-effect rules should call their effect with tokens and info before processing")))
;
;(deftest product-context
;  (let [receiving-rule-maker (fn rule-maker [n]
;                               (p/factor= (Integer/parseInt (str n)) (p/lit \a)))
;        digit (p/semantics p/anything #(Integer/parseInt (str %)))
;        rule (p/product-context [n digit, m digit]
;               (receiving-rule-maker (+ n m)))]
;    (is (= (rule (seq "31aaaa23aa") {})
;           [[3 1 [\a \a \a \a]] (seq "23aa") {}]))
;    (is (= (rule (seq "31aaa23aa") {}) nil)))
;  (let [receiving-rule-maker (fn rule-maker [x]
;                               (p/rep+ (p/lit x)))
;        header (p/semantics (p/conc p/anything p/anything)
;                            #(hash-map :token (% 0), :type (% 1)))
;        rule (p/product-context [{token :token} header]
;               (receiving-rule-maker token))]
;    (is (= (rule (seq "a+aasdf") {})
;           [[{:type \+, :token \a} [\a \a]] (seq "sdf") {}]))
;    (is (= (rule (seq "+asdf") {}) nil))))
;
;(deftest product-invisible-context
;  (let [digit (p/semantics p/anything #(Integer/parseInt (str %)))
;        receiving-rule-maker (fn rule-maker [n]
;                               (p/factor= (Integer/parseInt (str n)) p/anything))
;        rule (p/product-invisible-context [n digit, m digit]
;               (receiving-rule-maker (+ n m)))]
;    (is (= (rule (seq "31aaaa") {})
;           [[3 1 [\3 \1 \a \a]] (seq "aa") {}]))
;    (is (= ((p/conc digit rule) (seq "531aaaa") {})
;           [[5 [3 1 [\3 \1 \a \a]]] (seq "aa") {}]))))
;
;(deftest match-remainder
;  (is (= ((p/match-remainder (p/lit "hi") (p/lit "THEN")) ["hi" "THEN"] {})
;         [["hi" "THEN"] (list "THEN") {}])
;      "created remainder-matching rule succeeds when given subrule and matching succeed")
;  (is (= ((p/match-remainder (p/lit "hi") (p/lit "THEN")) ["bye" "THEN"] {})
;         nil)
;      "created remainder-matching rule fails when given subrule fails")
;  (is (= ((p/match-remainder (p/lit "hi") (p/lit "THEN")) ["hi" "WELL"] {})
;         nil)
;      "created remainder-matching rule fails when given matching fails"))

(time (run-tests))
