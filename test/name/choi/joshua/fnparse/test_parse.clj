(ns name.choi.joshua.fnparse.test-parse
  (:use clojure.test clojure.contrib.monads
        clojure.contrib.error-kit
        [clojure.contrib.except :only [throw-arg]])
  (:require [name.choi.joshua.fnparse :as p]))

(deferror parse-error [] []
  {:msg "WHEEE", :unhandled (throw-msg IllegalArgumentException)})
(deferror weird-error [] []
  {:msg "BOOM", :unhandled (throw-msg Exception)})

(deftest index-fns
  (-> nil p/make-state p/get-index (= 0) is)
  (-> nil p/make-state (p/vary-index inc) p/get-index (= 1) is)
  (-> nil p/make-state (p/set-index 4) p/get-index (= 4) is))

(deftest emptiness
  (is (= (p/emptiness (p/make-state '(A B C)))
         [nil (p/make-state '(A B C))])
      "emptiness rule matches emptiness"))

(deftest anything
  (is (= (p/anything (p/make-state '(A B C)))
         ['A (p/make-state '(B C))])
    "anything rule matches first token")
  (is (= (p/anything (p/make-state '(A B C)))
         ['A (p/make-state '(B C))])
    "anything rule matches first token without index")
  (is (-> '(A B C) p/make-state p/anything second meta ::p/index (= 1)))
  (is (-> '(A B C) p/make-state (vary-meta assoc ::p/index 5)
        p/anything second meta ::p/index (= 6)))
  (is (nil? (p/anything (p/make-state nil)))
    "anything rule fails with no tokens left")
  (is (= ((p/rep* p/anything) (p/make-state '(A B C)))
         ['(A B C) (p/make-state nil)])
    "repeated anything rule does not create infinite loop"))

(deftest term
  (let [rule (p/term (partial = 'A))]
    (is (= (rule (p/make-state '[A B])) ['A (p/make-state '[B])])
      "created terminal rule works when first token fulfills validator")
    (is (nil? (rule (p/make-state '[B B])))
      "created terminal rule fails when first token fails validator")
    (is (= (rule (p/make-state '[A])) ['A (p/make-state nil)])
      "created terminal rule works when no remainder")))

(deftest lit
  (is (= ((p/lit 'A) (p/make-state '[A B]))
         ['A (p/make-state '[B])])
      "created literal rule works when literal token present")
  (is (nil? ((p/lit 'A) (p/make-state '[B])))
      "created literal rule fails when literal token not present"))

(deftest re-term
  (is (= ((p/re-term #"\s*true\s*") (p/make-state ["  true" "THEN"]))
         ["  true" (p/make-state ["THEN"])])
      "created re-term rule works when first token matches regex")
  (is (nil? ((p/re-term #"\s*true\s*") (p/make-state ["false" "THEN"])))
      "created re-term rule fails when first token does not match regex")
  (is (nil? ((p/re-term #"\s*true\s*") (p/make-state nil)))
      "created re-term rule fails when no tokens are left"))

(deftest followed-by
  (is (= ((p/followed-by (p/lit 'A)) (p/make-state '[A B C]))
         ['A (p/make-state '[A B C])]))
  (is (nil? ((p/followed-by (p/lit 'A)) (p/make-state '[B C])))))

(deftest not-followed-by
  (is (= ((p/not-followed-by (p/lit 'A)) (p/make-state '[B C]))
         [true (p/make-state '[B C])]))
  (is (nil? ((p/not-followed-by (p/lit 'A)) (p/make-state '[A B C])))))

(deftest complex
  (let [rule1 (p/complex [a (p/lit 'A)] (str a "!"))
        rule2 (p/complex [a (p/lit 'A), b (p/lit 'B)] (str a "!" b))]
    (is (= (rule1 (p/make-state '[A B])) ["A!" (p/make-state '[B])])
      "created complex rule applies semantic hook to valid subresult")
    (is (nil? (rule1 (p/make-state '[B A])))
      "created complex rule fails when a given subrule fails")
    (is (= (rule2 (p/make-state '[A B C])) ["A!B" (p/make-state '[C])])
      "created complex rule succeeds when all subrules fulfilled in order")
    (is (nil? (rule2 (p/make-state '[A C])))
      "created complex rule fails when one subrule fails")))

(deftest semantics
  (is (= ((p/semantics (p/lit "hi") #(str % "!")) (p/make-state ["hi" "THEN"]))
         ["hi!" (p/make-state (list "THEN"))])
      "created simple semantic rule applies semantic hook to valid result of given rule"))

(deftest constant-semantics
  (is (= ((p/constant-semantics (p/lit "hi") {:a 1}) (p/make-state ["hi" "THEN"]))
         [{:a 1} (p/make-state (list "THEN"))])
      "created constant sem rule returns constant value when given subrule does not fail"))

(deftest validate
  (is (= ((p/validate (p/lit "hi") (partial = "hi")) (p/make-state ["hi" "THEN"]))
         ["hi" (p/make-state (list "THEN"))])
      "created validator rule succeeds when given subrule and validator succeed")
  (is (nil? ((p/validate (p/lit "hi") (partial = "RST")) (p/make-state ["RST"])))
      "created validator rule fails when given subrule fails")
  (is (nil? ((p/validate (p/lit "hi") (partial = "hi")) (p/make-state "hi")))
      "created validator rule fails when given validator fails"))

(deftest get-remainder
  (is (= ((p/complex [remainder p/get-remainder] remainder) (p/make-state ["hi" "THEN"]))
         [["hi" "THEN"] (p/make-state ["hi" "THEN"])])))

(deftest remainder-peek
  (is (= (p/remainder-peek (p/make-state (seq "ABC")))
         [\A (p/make-state (seq "ABC"))])))

(deftest conc
  (is (= ((p/conc (p/lit "hi") (p/lit "THEN")) (p/make-state ["hi" "THEN" "bye"]))
         [["hi" "THEN"] (p/make-state (list "bye"))])
      "created concatenated rule succeeds when all subrules fulfilled in order")
  (is (nil? ((p/conc (p/lit "hi") (p/lit "THEN")) (p/make-state ["hi" "bye" "boom"])))
      "created concatenated rule fails when one subrule fails"))

(deftest alt
  (let [literal-true (p/lit "true")
        literal-false (p/lit "false")
        literal-boolean (p/alt literal-true literal-false)]
    (is (= (literal-boolean (p/make-state ["false" "THEN"]))
           ["false" (p/make-state (list "THEN"))])
        "created alternatives rule works with first valid rule product")
    (is (nil? (literal-boolean (p/make-state ["aRSTIR"])))
        "created alternatives rule fails when no valid rule product present")))

(deftest update-info
  (is (= (-> [\a] p/make-state (assoc :column 3)
           ((p/update-info :column inc)))
         [3 (-> [\a] p/make-state (assoc :column 4))])))

(deftest invisi-conc
  (is (= ((p/invisi-conc (p/lit \a) (p/update-info :column inc))
           (-> "abc" p/make-state (assoc :column 4)))
         [\a (-> "bc" seq p/make-state (assoc :column 5))])))

(deftest lit-conc-seq
  (is (= ((p/lit-conc-seq "THEN") (p/make-state "THEN print 42;"))
         [(vec "THEN") (p/make-state (seq " print 42;"))])
      "created literal-sequence rule is based on sequence of given token sequencible")
  (is (= ((p/lit-conc-seq "THEN"
            (fn [lit-token]
              (p/invisi-conc (p/lit lit-token)
                (p/update-info :column inc))))
          (-> "THEN print 42;" p/make-state (assoc :column 1)))
         [(vec "THEN") (-> (seq " print 42;") p/make-state (assoc :column 5))])
      "created literal-sequence rule uses given rule-maker"))

(deftest lit-alt-seq
  (is (= ((p/lit-alt-seq "ABCD") (p/make-state (seq "B 2")))
         [\B (p/make-state (seq " 2"))])
      (str "created literal-alternative-sequence rule works when literal symbol present in"
           "sequence"))
  (is (nil? ((p/lit-alt-seq "ABCD") (p/make-state (seq "E 2"))))
      (str "created literal-alternative-sequence rule fails when literal symbol not present"
           "in sequence"))
  (is (= ((p/lit-alt-seq "ABCD" (fn [lit-token]
                                    (p/invisi-conc (p/lit lit-token)
                                                   (p/update-info :column inc))))
          (-> "B 2" p/make-state (assoc :column 1)))
         [\B (-> (seq " 2") p/make-state (assoc :column 2))])
      "created literal-alternative-sequence rule uses given rule-maker"))

(deftest opt
  (let [opt-true (p/opt (p/lit "true"))]
    (is (= (opt-true (p/make-state ["true" "THEN"]))
           ["true" (p/make-state (list "THEN"))])
        "created option rule works when symbol present")
    (is (= (opt-true (p/make-state (list "THEN")))
           [nil (p/make-state (list "THEN"))])
        "created option rule works when symbol absent")))

(deftest rep*
  (let [rep*-true (p/rep* (p/lit true))
        rep*-untrue (p/rep* (p/except p/anything (p/lit true)))]
    (is (= (rep*-true (-> [true "THEN"] p/make-state (assoc :a 3)))
           [[true] (-> (list "THEN") p/make-state (assoc :a 3))])
        "created zero-or-more-repetition rule works when symbol present singularly")
    (is (= (rep*-true (-> [true true true "THEN"] p/make-state (assoc :a 3)))
           [[true true true] (-> (list "THEN") p/make-state (assoc :a 3))])
        "created zero-or-more-repetition rule works when symbol present multiply")
    (is (= (rep*-true (-> ["THEN"] p/make-state (assoc :a 3)))
           [nil (-> (list "THEN") p/make-state (assoc :a 3))])
     "created zero-or-more-repetition rule works when symbol absent")
    (is (= (rep*-true (p/make-state [true true true]))
           [[true true true] (p/make-state nil)])
        "created zero-or-more-repetition rule works with no remainder after symbols")
    (is (= (rep*-true (p/make-state nil))
           [nil (p/make-state nil)])
        "created zero-or-more-repetition rule works with no remainder")
    (is (= (rep*-untrue (p/make-state [false false]))
           [[false false] (p/make-state nil)])
        "created zero-or-more-repetition negative rule works consuming up to end")
    (is (= (rep*-untrue (p/make-state [false false true]))
           [[false false] (p/make-state [true])])
        "created zero-or-more-repetition negative rule works consuming until exception")
    (is (= (rep*-untrue (p/make-state nil))
           [nil (p/make-state nil)])
        "created zero-or-more-repetition negative rule works with no remainder")))

(deftest rep+
  (let [rep+-true (p/rep+ (p/lit true))]
    (is (= (rep+-true (p/make-state [true "THEN"]))
           [[true] (p/make-state (list "THEN"))])
        "created one-or-more-repetition rule works when symbol present singularly")
    (is (= (rep+-true (p/make-state [true true true "THEN"]))
           [[true true true] (p/make-state (list "THEN"))])
        "created one-or-more-repetition rule works when symbol present multiply")
    (is (nil? (rep+-true (p/make-state (list "THEN"))))
        "created one-or-more-repetition rule fails when symbol absent")))

(deftest except
  (let [except-rule (p/except (p/lit-alt-seq "ABC") (p/alt (p/lit \B) (p/lit \C)))]
    (is (= (-> "ABC" p/make-state (assoc :a 1) except-rule)
            [\A (-> (seq "BC") p/make-state (assoc :a 1))])
        "created exception rule works when symbol is not one of the syntatic exceptions")
    (is (nil? (except-rule (p/make-state (seq "BAC"))))
        "created exception rule fails when symbol is one of the syntactic exceptions")
    (is (nil? (except-rule (p/make-state (seq "DAB"))))
        "created exception rule fails when symbol does not fulfill subrule")))

(deftest factor=
  (let [tested-rule-3 (p/factor= 3 (p/lit "A"))
        tested-rule-0 (p/factor= 0 (p/lit "A"))]
    (is (= (tested-rule-3 (p/make-state (list "A" "A" "A" "A" "C")))
           [["A" "A" "A"] (p/make-state (list "A" "C"))])
        (str "created factor= rule works when symbol fulfills all subrule multiples and"
             "leaves strict remainder"))
    (is (= (tested-rule-3 (p/make-state (list "A" "A" "A" "C")))
           [["A" "A" "A"] (p/make-state (list "C"))])
        "created factor= rule works when symbol fulfills all subrule multiples only")
    (is (= (tested-rule-3 (p/make-state (list "A" "A" "C"))) nil)
        "created factor= rule fails when symbol does not fulfill all subrule multiples")
    (is (= (tested-rule-3 (p/make-state (list "D" "A" "B"))) nil)
        "created factor= rule fails when symbol does not fulfill subrule at all")
    (is (= (tested-rule-0 (p/make-state (list "D" "A" "B")))
           [[] (p/make-state (list "D" "A" "B"))])
        "created factor= rule works when symbol fulfils no multiples and factor is zero")))

(deftest rep-predicate
  (let [tested-rule-fn (p/rep-predicate (partial > 3) (p/lit "A"))
        infinity-rule (p/rep-predicate (partial > Double/POSITIVE_INFINITY) (p/lit "A"))]
    (is (= (tested-rule-fn (p/make-state (list "A" "A" "C")))
           [["A" "A"] (p/make-state (list "C"))])
        "created rep rule works when predicate returns true")
    (is (nil? (tested-rule-fn (p/make-state (list "A" "A" "A"))))
        "created rep rule fails when predicate returns false")
    (is (= (tested-rule-fn (p/make-state (list "D" "A" "B")))
           [nil (p/make-state (list "D" "A" "B"))])
        "created rep rule succeeds when symbol does not fulfill subrule at all")))

(deftest rep=
  (let [tested-rule-fn (p/rep= 3 (p/lit \A))]
    (is (= (tested-rule-fn (p/make-state (seq "AAAC")))
           [[\A \A \A] (p/make-state (seq "C"))])
        "created rep= rule works when symbol only fulfills all subrule multiples")
    (is (nil? (tested-rule-fn (p/make-state (seq "AAAA"))))
        "created rep= rule fails when symbol exceeds subrule multiples")
    (is (nil? (tested-rule-fn (p/make-state (seq "AAC"))))
        "created rep= rule fails when symbol does not fulfill all subrule multiples")
    (is (nil? (tested-rule-fn (p/make-state (seq "DAB"))))
        "created rep= rule fails when symbol does not fulfill subrule at all")))

(deftest factor<
  (let [tested-rule (p/factor< 3 (p/lit \A))]
    (is (= (tested-rule (p/make-state (seq "AAAAC")))
           [[\A \A] (p/make-state (seq "AAC"))])
        (str "created factor< rule works when symbol fulfills all subrule multiples and"
             "leaves strict remainder"))
    (is (= (tested-rule (p/make-state (seq "AAAC")))
           [[\A \A] (p/make-state (seq "AC"))])
        "created factor< rule works when symbol fulfills all subrule multiples only")
    (is (= (tested-rule (p/make-state (seq "AAC"))) [[\A \A] (p/make-state (seq "C"))])
        "created factor< rule works when symbol does not fulfill all subrule multiples")
    (is (= (tested-rule (p/make-state (seq "DAB")))
           [nil (p/make-state (seq "DAB"))])
        "created factor< rule works when symbol does not fulfill subrule at all")))

(deftest failpoint
  (let [exception-rule (p/failpoint (p/lit "A")
                          (fn [remainder state]
                            (throw-arg "ERROR %s at line %s"
                              (first remainder) (:line state))))]
    (is (= (exception-rule (-> ["A"] p/make-state (assoc :line 3)))
           ["A" (-> nil p/make-state (assoc :line 3))])
        "failing rules succeed when their subrules are fulfilled")
    (is (thrown-with-msg? IllegalArgumentException
          #"ERROR B at line 3"
          (exception-rule (-> ["B"] p/make-state (assoc :line 3)))
        "failing rules fail with given exceptions when their subrules fail"))))

(deftest intercept
  (let [parse-error-rule
          (p/semantics (p/lit \A) (fn [_] (throw (Exception.))))
        intercept-rule
          (p/intercept parse-error-rule
            (fn [rule-call]
              (try (rule-call)
                (catch Exception e :error))))]
    (is (= (intercept-rule (p/make-state "ABC")) :error))))

(deftest effects
  (let [rule
         (p/complex [subproduct (p/lit "A")
                     line-number (p/get-info :line)
                     effects (p/effects (println "!" subproduct)
                                        (println "YES" line-number))]
           subproduct)]
    (is (= (with-out-str
             (is (= (rule (-> ["A" "B"] p/make-state (assoc :line 3)))
                    ["A" (-> (list "B") p/make-state (assoc :line 3))])
                 "pre-effect rules succeed when their subrules are fulfilled"))
           "! A\nYES 3\n")
        "effect rule should call their effect and return the same state")))

(deftest state-context
  (p/state-context {:warnings []}
    (is (= ((p/lit \a) (p/make-state "abc"))
           [\a (-> "bc" seq p/make-state (assoc :warnings []))]))))

; (deftest match-rule
;   (let [rule (p/lit "A")
;         matcher (partial p/match-rule rule identity vector)]
;     (is (= (matcher (p/make-state ["A"])) "A"))
;     (is (= (matcher (p/make-state ["B"])) (p/make-state ["B"])))
;     (is (= (matcher (p/make-state ["A" "B"]))
;            ["A" (p/make-state ["B"]) (p/make-state ["A" "B"])]))))
; 
; (deftest add-states
;   (let [state-a (p/make-state '[a b c d], :index 4)
;         state-b (p/make-state nil, :index 2)]
;     (is (= (p/add-states state-a state-b) (p/make-state '[c d], :index 6)))))
; 
; (deftest find-mem-result
;   (let [remainder-1 '[a b c d]
;         remainder-2 '[d e f]
;         remainder-3 '[a c b d]
;         memory {'[a b] 'dummy-1
;                 '[d e f] 'dummy-2}]
;     (is (= (p/find-mem-result memory remainder-1) 'dummy-1))
;     (is (= (p/find-mem-result memory remainder-2) 'dummy-2))
;     (is (= (p/find-mem-result memory remainder-3) nil))))
; 
; (deftest mem
;   (let [rule (p/mem (p/alt (p/conc (p/lit 'a) (p/lit 'b)) (p/lit 'c)))]
;     (is (= (rule (p/make-state '[a b c])) ['[a b] (p/make-state '[c])]))
;     (is (= (rule (p/make-state '[a b c])) ['[a b] (p/make-state '[c])]))
;     (is (= (rule (p/make-state '[c s a])) ['c (p/make-state '[s a])]))
;     (is (= (rule (p/make-state '[c])) ['c (p/make-state [])]))
;     (is (nil? (rule (p/make-state '[s a]))))
;     (is (nil? (rule (p/make-state '[s a]))))))
; 
; (deftest convert-bundle
;   (let [my-bundle {:remainder-accessor :remainder
;                    :index-accessor :index
;                    :add-info identity}
;         invalid-bundle {:a :arst}]
;     (is (= (p/convert-bundle my-bundle)
;            {#'p/*remainder-accessor* :remainder
;             #'p/*index-accessor* :index
;             #'p/*add-info* identity}))
;     (is (thrown? Exception (p/convert-bundle invalid-bundle)))))
; 
; (deftest with-bundle
;   (let [my-state-s (create-struct :remainder :index)
;         my-bundle {:empty-state (struct my-state-s [])
;                    :remainder-accessor (accessor my-state-s :remainder)
;                    :index-accessor (accessor my-state-s :index)
;                    :add-info identity}
;         my-rule (p/opt p/anything)]
;     (p/with-bundle my-bundle
;       (is (= (my-rule (p/p/make-state '[a b c]))
;              ['a (struct my-state-s '[b c])])))))
; 
; (deftest standard-inc-line-and-column-and-mem
;   (p/with-bundle p/standard-bundle
;   (let [a-rule (p/inc-column (p/lit 'a))
;         b-rule (p/inc-line (p/lit 'n))
;         mem-rule (p/mem (p/alt (p/conc a-rule b-rule a-rule) a-rule))]
;     (is (= (mem-rule (struct p/standard-s '[a n a b] 3 2 5))
;            ['[a n a] (struct p/standard-s '[b] 6 3 1)]))
;     (is (= (mem-rule (struct p/standard-s '[a n a b] 3 2 5))
;            ['[a n a] (struct p/standard-s '[b] 6 3 1)])))))

(time (run-tests))
