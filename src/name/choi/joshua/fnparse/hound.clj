(ns name.choi.joshua.fnparse
  [:use clojure.contrib.seq-utils clojure.contrib.def clojure.test]
  [:require [clojure.contrib.monads :as m]]
  [:import [clojure.lang Sequential IPersistentMap IPersistentVector Var]])

; A RULE is a a function that:
; - Takes a state and returns either nil
;   or a vector pair.
;   - A STATE is a struct map that contains
;     a remainder and maybe info.
;     You create states using the make-cf-state function.
;   - A REMAINDER is a sequence or
;     seqable collection of tokens.
;     It is contained in the
;     :name.choi.joshua.fnparse/remainder key.
;   - A state can also contain INFO, which are
;     any other attributes in the state. Common
;     examples include current line and column numbers
;     and a set of current warnings.
; - If the remainder is VALID under the rule,
;   it CONSUMES any valid tokens and returns a RESULT.
;   - A RESULT is a vector pair containing
;     a product and a new state.
;   - The PRODUCT is the semantic data generated
;     by the rule that corresponds to the
;     information represented by the consumed tokens.
;     It can be any object.
;   - The new state is what the old state now looks like,
;     after its first few tokens are consumed.
; - If the given token sequence is INVALID, then
;   the rule FAILS, meaning that it simply returns NIL.
 
(deftype State [remainder] IPersistentMap)

(deftype Failure [] IPersistentMap)

(defn make-state [remainder]
  (State remainder))

(defn failure? [result]
  (isa? (type result) ::Failure))

(deftype Reply [tokens-consumed? result] IPersistentMap)

(defvar- basic-failure (Failure))

(m/defmonad parser-m
  "The monad that FnParse uses."
  [m-zero
     (fn [state] (Reply false basic-failure))
   m-result
     (fn [product]
       (fn [state] (Reply false [product state])))
   m-bind
     (fn [rule product-fn]
       (letfn [(apply-product-fn [result]
                 (let [[product state] result]
                   ((product-fn product) state)))]
         (fn [state]
           (let [reply (rule state)]
             (if (:tokens-consumed? reply)
               (assoc reply :result
                 (delay
                   (let [result (-> reply :result force)]
                     (if (failure? result)
                       result
                       (-> result apply-product-fn :result force)))))
               (let [result (-> reply :result force)]
                 (if (failure? result)
                   (Reply false result)
                   (apply-product-fn result))))))))
   m-plus
     (letfn [(result-failure? [reply]
               (-> reply :result force failure?))]
       (fn [& rules]
         (fn [state]
           (let [[consuming-replies empty-replies]
                   (->> rules (map #(% state)) (separate :tokens-consumed?))]
             (or (first (drop-while result-failure? consuming-replies))
                 (first (drop-while result-failure? empty-replies))
                 (m-zero state))))))])

(defmacro complex
  "Creates a complex rule in monadic
  form. It's a lot easier than it sounds.
  It's like a very useful combination of
  conc and semantics.
  The first argument is a vector
  containing binding forms à la the let and for
  forms. The keys are new, lexically scoped
  variables. Their corresponding vals
  are subrules. Each of these subrules are
  sequentially called as if they were
  concatinated together with conc. If any of
  them fails, the whole rule immediately fails.
  Meanwhile, each sequential subrule's product
  is bound to its corresponding variable.
  After all subrules match, all of the
  variables can be used in the body.
  The second argument of complex is a body
  that calculates the whole new rule's
  product, with access to any of the variables
  defined in the binding vector.
  It's basically like let, for, or any other
  monad. Very useful!"
  [steps & product-expr]
  `(m/domonad parser-m ~steps ~@product-expr))

(defn anything [state]
  (m/with-monad parser-m
    (if-let [remainder (-> state :remainder seq)]
      (Reply true
        (delay [(first remainder) (assoc state :remainder (next remainder))]))
      (Reply false basic-failure))))

(defvar emptiness
  (m/with-monad parser-m (m/m-result nil)))

(defvar nothing
  (m/with-monad parser-m m/m-zero))

(defn validate [subrule predicate]
  (complex [product subrule, :when (predicate product)]
    product))

(defn term [predicate]
  (validate anything predicate))

(defn lit [token]
  (term (partial = token)))

(defn alt [& subrules]
  (m/with-monad parser-m
    (apply m/m-plus subrules)))

(defn conc [& subrules]
  (m/with-monad parser-m
    (m/m-seq subrules)))

(defn map-conc
  ([tokens] (map-conc lit tokens))
  ([rule-maker tokens] (apply conc (map rule-maker tokens))))

;(def rule (complex [a anything, b anything] [a b]))
;(def rule (validate anything (partial = 'a)))
(def rule (map-conc '[a b]))

(-> '[a b c] make-state rule println)

; (with-test
;   (defrule anything
;     "A rule that matches anything--that is, it matches
;     the first token of the tokens it is given.
;     This rule's product is the first token it receives.
;     It fails if there are no tokens left."
;     (fn [state]
;       (m/with-monad parser-m
;         (let [token (nth (get-tokens state) (get-index state) ::nothing)]
;           (if (not= token ::nothing)
;             [token (inc-index state)]
;             (m/m-zero state))))))
;   (let [input '(A B C)]
;     (is (= ['A (make-cf-state input 1)] (anything (make-cf-state input 0))))
;     (is (failure? (anything (State input 3 nil))))))
; 
; (m/with-monad parser-m
;   (defvar nothing m/m-zero))
; 
; (with-test
;   (defmacro complex
;     "Creates a complex rule in monadic
;     form. It's a lot easier than it sounds.
;     It's like a very useful combination of
;     conc and semantics.
;     The first argument is a vector
;     containing binding forms à la the let and for
;     forms. The keys are new, lexically scoped
;     variables. Their corresponding vals
;     are subrules. Each of these subrules are
;     sequentially called as if they were
;     concatinated together with conc. If any of
;     them fails, the whole rule immediately fails.
;     Meanwhile, each sequential subrule's product
;     is bound to its corresponding variable.
;     After all subrules match, all of the
;     variables can be used in the body.
;     The second argument of complex is a body
;     that calculates the whole new rule's
;     product, with access to any of the variables
;     defined in the binding vector.
;     It's basically like let, for, or any other
;     monad. Very useful!"
;     [steps & product-expr]
;     `(m/domonad parser-m ~steps ~@product-expr)))
; 
; (defvar- fetch-state
;   (m/fetch-state)
;   "A rule that consumes no tokens. Its product
;   is the entire current state.
;   [Equivalent to the result of fetch-state
;   from clojure.contrib.monads.]")
; 
; (defn- set-state [state]
;   (m/set-state state))
; 
; (defn fetch-info
;   "Creates a rule that consumes no tokens.
;   The new rule's product is the value
;   of the given key in the current state.
;   [Equivalent to fetch-val from clojure.contrib.monads.]"
;   [key]
;   (m/fetch-val key))
; 
; ; (with-test
; ;   (defn fetch-remainder
; ;     "Generates a rule whose product is the
; ;     sequence of the remaining tokens of any states
; ;     that it is given. It consumes no tokens.
; ;     [(fetch-remainder) is equivalent to
; ;     (fetch-val get-remainder) from
; ;     clojure.contrib.monads.]"
; ;     []
; ;     (m/fetch-val get-remainder))
; ;   (is (= ((complex [remainder (fetch-remainder)] remainder)
; ;           (make-cf-state ["hi" "THEN"]))
; ;          [["hi" "THEN"] (make-cf-state ["hi" "THEN"])])))
;  
; ; (defn set-info
; ;   "Creates a rule that consumes no tokens.
; ;   The new rule directly changes the
; ;   current state by associating the given
; ;   key with the given value. The product
; ;   is the old value of the changed key.
; ;   [Equivalent to set-val from
; ;   clojure.contrib.monads.]"
; ;   [key value]
; ;   (m/set-val key value))
; ;  
; ; (with-test
; ;   (defn update-info
; ;     "Creates a rule that consumes no tokens.
; ;     The new rule changes the current state
; ;     by associating the given key with the
; ;     evaluated result of applying the given
; ;     updating function to the key's current
; ;     value. The product is the old value of
; ;     the changed key.
; ;     [Equivalent to update-val from clojure.contrib.monads.]"
; ;     [key val-update-fn & args]
; ;     (m/update-val key #(apply val-update-fn % args)))
; ;   (let [mock-state (partial make-state '(A))]
; ;     (is (= [#{} (mock-state 1 {:variables #{'foo}})]
; ;             ((update-info :variables conj 'foo)
; ;              (mock-state 0 {:variables #{}}))))))
;  
; (with-test
;   (m/with-monad parser-m
;     (defvar emptiness
;       (m-result nil)
;       "A rule that matches emptiness--that
;       is, it always matches with every given
;       token sequence, and it always returns
;       [nil given-state].
;       (def a emptiness) would be equivalent
;       to the EBNF a = ; This rule's product
;       is always nil, and it therefore always
;       returns [nil given-state]."))
;   (let [mock-state (partial make-cf-state '(A B C))]
;     (is (= (emptiness (mock-state 0)) [nil (mock-state 0)]))
;     (is (= (emptiness (mock-state 6)) [nil (mock-state 6)]))))
; 
; (with-test
;   (defn validate
;     "Creates a rule from attaching a product-validating function to the given
;     subrule--that is, any products of the subrule must fulfill the validator
;     function.
;     (def a (validate b validator)) says that the rule a succeeds only when b
;     succeeds and also when the evaluated value of (validator b-product) is true.
;     The new rule's product would be b-product."
;     [subrule validator]
;     (complex [subproduct subrule, :when (validator subproduct)]
;       subproduct))
;   (let [valid? (partial = "hi")
;         rule-a (validate anything valid?)
;         rule-b (validate nothing valid?)
;         mock-state (partial make-cf-state ["hi" "THEN"])]
;     (is (= (rule-a (mock-state 0)) ["hi" (mock-state 1)]))
;     (is (failure? (rule-b (mock-state 0))))
;     (is (failure? (rule-a (mock-state 1))))))
;  
;   (defn term
;     "(term validator) is equivalent
;     to (validate anything validator).
;     Creates a rule that is a terminal rule of the given validator--that is, it
;     accepts only tokens for whom (validator token) is true.
;     (def a (term validator)) would be equivalent to the EBNF
;       a = ? (validator %) evaluates to true ?;
;     The new rule's product would be the first token, if it fulfills the
;     validator."
;     [validator]
;     (validate anything validator))
;  
; (with-test
;   (defvar lit
;     (comp term (partial partial =))
;     "Equivalent to (comp term (partial partial =)).
;     Creates a rule that is the terminal
;     rule of the given literal token--that is,
;     it accepts only tokens that are equal to
;     the given literal token.
;     (def a (lit \"...\")) would be equivalent to the EBNF
;       a = \"...\";
;     The new rule's product would be the first
;     token, if it equals the given literal token.")
;   (let [rule (lit 'A)
;         mock-state (partial make-cf-state '[A B])]
;     (is (= (rule (mock-state 0)) ['A (mock-state 1)]))
;     (is (failure? (rule (mock-state 1))))))
; 
; (defvar re-term
;   (comp term (partial partial re-matches))
;   "Equivalent to (comp term (partial partial re-matches)).
;   Creates a rule that is the terminal rule of the given regex--that is, it
;   accepts only tokens that match the given regex.
;   (def a (re-term #\"...\")) would be equivalent to the EBNF
;     a = ? (re-matches #\"...\" %) evaluates to true ?;
;   The new rule's product would be the first token, if it matches the given
;   regex.")
; 
; (set-test complex
;   (let [mock-state (partial make-cf-state '[A B C])
;         rule (complex [a (lit 'A), b (lit 'B)] (str a "!" b))]
;     (is (= (rule (mock-state 0)) ["A!B" (mock-state 2)]))
;     (is (failure? (rule (mock-state 1))))))
; 
; (defn followed-by
;   "Creates a rule that does not consume any tokens, but fails when the given
;   subrule fails.
;   The new rule's product would be the subrule's product."
;   [subrule]
;   (complex [state fetch-state, subproduct subrule, _ (set-state state)]
;     subproduct))
; 
; (m/with-monad parser-m
;   (defn not-followed-by
;     "Creates a rule that does not consume
;     any tokens, but fails when the given
;     subrule succeeds. On success, the new
;     rule's product is always true."
;     [subrule]
;     (fn [state]
;       (if (failure? (subrule state))
;         [true state]
;         (m/m-zero state)))))
; 
; (defn semantics
;   "Creates a rule with a semantic hook,
;   basically a simple version of a complex
;   rule. The semantic hook is a function
;   that takes one argument: the product of
;   the subrule."
;   [subrule semantic-hook]
;   (complex [subproduct subrule]
;     (semantic-hook subproduct)))
; 
; (defn constant-semantics
;   "Creates a rule with a constant semantic
;   hook. Its product is always the given
;   constant."
;   [subrule semantic-value]
;   (complex [subproduct subrule]
;     semantic-value))
;  
; ; (defrule remainder-peek
; ;   "A rule whose product is the very next
; ;   token in the remainder of any given state.
; ;   The new rule does not consume any tokens."
; ;   (complex [remainder (fetch-remainder)]
; ;     (first remainder)))
; 
; (defn conc
;   "Creates a rule that is the concatenation
;   of the given subrules. Basically a simple
;   version of complex, each subrule consumes
;   tokens in order, and if any fail, the entire
;   rule fails.
;   (def a (conc b c d)) would be equivalent to the EBNF:
;     a = b, c, d;
;   This macro is almost equivalent to m-seq for
;   the parser-m monad. The difference is that
;   it defers evaluation of whatever variables
;   it receives, so that it accepts expressions
;   containing unbound variables that are defined later."
;   [& subrules]
;   (m/with-monad parser-m
;     (fn [state]
;       ((m/m-seq subrules) state))))
; 
; (with-test
;   (defn alt
;     "Creates a rule that is the alternation
;     of the given subrules. It succeeds when
;     any of its subrules succeed, and fails
;     when none do. Its result is that of the first
;     subrule that succeeds, so the order of the
;     subrules that this function receives matters.
;     (def a (alt b c d)) would be equivalent to the EBNF:
;      a = b | c | d;
;     This macro is almost equivalent to m-plus for
;     the parser-m monad. The difference is that
;     it defers evaluation of whatever variables it
;     receives, so that it accepts expressions containing
;     unbound variables that are defined later."
;     [& subrules]
;     (m/with-monad parser-m (apply m/m-plus subrules)))
;   (let [rule (alt (lit "hi") (lit "THEN"))
;         mock-state (partial make-cf-state ["THEN" "bye"])]
;     (is (= (rule (mock-state 0)) ["THEN" (mock-state 1)]))
;     (is (failure? (rule (mock-state 1))))))
; 
; (defvar- number-rule (lit '0))
; (declare direct-left-recursive-rule lr-test-term lr-test-fact)
; 
; (with-test
;   (defvar- direct-lr-rule
;     (alt (conc #'direct-left-recursive-rule (lit '-) number-rule)
;          number-rule))
;   (let [mock-state (partial make-cf-state '[0 - 0 - 0])]
;     (is (= ['[[0 - 0] - 0] (mock-state 5)] (direct-lr-rule (mock-state 0))))))
; 
; (defvar- lr-test-term
;   (alt (conc #'lr-test-term (lit '+) #'lr-test-fact)
;        (conc #'lr-test-term (lit '-) #'lr-test-fact)
;        #'lr-test-fact))
; 
; (defvar- lr-test-fact
;   (alt (conc #'lr-test-fact (lit '*) number-rule)
;        (conc #'lr-test-fact (lit '/) number-rule)
;        number-rule))
; 
; (set-test lr-test-term
;   (let [mock-state (partial make-cf-state '[0])]
;     (is (= ['0 (mock-state 1)] (lr-test-term (mock-state 0)))))
;   (let [mock (partial make-cf-state '[0 * 0])]
;     (is (= ['[0 * 0] (mock 3)] (lr-test-term (mock 0)))))
;   (let [mock (partial make-cf-state '[0 + 0 * 0 - 0 / 0])]
;     (is (= ['[[0 + [0 * 0]] - [0 / 0]] (mock 9)] (lr-test-term (mock 0))))))
; 
; ; (with-test
; ;   (defn opt
; ;     "Creates a rule that is the optional form
; ;     of the subrule. It always succeeds. Its result
; ;     is either the subrule's (if the subrule
; ;     succeeds), or else its product is nil, and the
; ;     rule acts as the emptiness rule.
; ;     (def a (opt b)) would be equivalent to the EBNF:
; ;       a = b?;"
; ;     [subrule]
; ;     (m/with-monad parser-m
; ;       (m-plus subrule emptiness)))
; ;   (let [opt-true (opt (lit "true"))]
; ;     (is (= (opt-true (make-cf-state ["true" "THEN"]))
; ;            ["true" (make-cf-state (list "THEN"))])
; ;         "created option rule works when symbol present")
; ;     (is (= (opt-true (make-cf-state (list "THEN")))
; ;            [nil (make-cf-state (list "THEN"))])
; ;         "created option rule works when symbol absent")))
; ;  
; ; (with-test
; ;   (defmacro invisi-conc
; ;     "Like conc, only that the product is the
; ;     first subrule's product only, not a vector of
; ;     all the products of the subrules--effectively
; ;     hiding the products of the other subrules.
; ;     The rest of the subrules consume tokens too;
; ;     their products simply aren't accessible.
; ;     This is useful for applying set-info and
; ;     update-info to a rule, without having to deal
; ;     with set-info or update-info's products."
; ;     [first-subrule & rest-subrules]
; ;     `(semantics (conc ~first-subrule ~@rest-subrules) first)))
; ;  
; ; (set-test invisi-conc
; ;   (is (= ((invisi-conc (lit \a) (update-info :column inc))
; ;            (-> "abc" make-cf-state (assoc :column 4)))
; ;          [\a (-> "bc" seq make-cf-state (assoc :column 5))])))
; ; 
; ; (with-test
; ;   (defn lit-conc-seq
; ;     "A convenience function: it creates a rule
; ;     that is the concatenation of the literals
; ;     formed from the given sequence of literal tokens.
; ;     (def a (lit-conc-seq [\"a\" \"b\" \"c\"]))
; ;     would be equivalent to the EBNF:
; ;       a = \"a\", \"b\", \"c\";
; ;     The function has an optional argument: a
; ;     rule-making function. By default it is the lit
; ;     function. This is the function that is used
; ;     to create the literal rules from each element
; ;     in the given token sequence."
; ;     ([token-seq]
; ;      (lit-conc-seq token-seq lit))
; ;     ([token-seq rule-maker]
; ;      (m/with-monad parser-m
; ;        (m/m-seq (map rule-maker token-seq)))))
; ;   (is (= ((lit-conc-seq "THEN") (make-cf-state "THEN print 42;"))
; ;          [(vec "THEN") (make-cf-state (seq " print 42;"))])
; ;       "created literal-sequence rule is based on sequence of given token sequencible")
; ;   (is (= ((lit-conc-seq "THEN"
; ;             (fn [lit-token]
; ;               (invisi-conc (lit lit-token)
; ;                 (update-info :column inc))))
; ;           (-> "THEN print 42;" make-cf-state (assoc :column 1)))
; ;          [(vec "THEN") (-> (seq " print 42;") make-cf-state (assoc :column 5))])
; ;       "created literal-sequence rule uses given rule-maker"))
; ; 
; ; (with-test
; ;   (defn lit-alt-seq
; ;     "A convenience function: it creates a rule
; ;     that is the alternation of the literals
; ;     formed from the given sequence of literal tokens.
; ;     (def a (lit-alt-seq [\"a\" \"b\" \"c\"]))
; ;     would be equivalent to the EBNF:
; ;       a = \"a\" | \"b\" | \"c\";"
; ;     ([token-seq]
; ;      (lit-alt-seq token-seq lit))
; ;     ([token-seq rule-maker]
; ;      (m/with-monad parser-m
; ;        (apply m-plus (map rule-maker token-seq)))))
; ;   (is (= ((lit-alt-seq "ABCD") (make-cf-state (seq "B 2")))
; ;          [\B (make-cf-state (seq " 2"))])
; ;       (str "created literal-alternative-sequence rule "
; ;            "works when literal symbol present in sequence"))
; ;   (is (failure? ((lit-alt-seq "ABCD") (make-cf-state (seq "E 2"))))
; ;       (str "created literal-alternative-sequence "
; ;            "rule fails when literal symbol not "
; ;            "present in sequence"))
; ;   (is (= ((lit-alt-seq "ABCD"
; ;             (fn [lit-token]
; ;               (invisi-conc (lit lit-token)
; ;                            (update-info :column inc))))
; ;           (-> "B 2" make-cf-state (assoc :column 1)))
; ;          [\B (-> (seq " 2") make-cf-state (assoc :column 2))])
; ;       "created literal-alternative-sequence rule uses given rule-maker"))
; ; 
; ; (with-test
; ;   (defn except
; ;     "Creates a rule that is the exception from
; ;     the first given subrules with the second given
; ;     subrule--that is, it accepts only tokens that
; ;     fulfill the first subrule but fails the
; ;     second of the subrules.
; ;     (def a (except b c)) would be equivalent to the EBNF
; ;       a = b - c;
; ;     The new rule's products would be b-product. If
; ;     b fails or c succeeds, then nil is simply returned."
; ;     [minuend subtrahend]
; ;     (complex [state fetch-state
; ;               minuend-product minuend
; ;               :when (failure? (subtrahend state))]
; ;       minuend-product))
; ;   (let [except-rule (except (lit-alt-seq "ABC") (lit-alt-seq "BC"))]
; ;     (is (= (-> "ABC" make-cf-state (assoc :a 1) except-rule)
; ;             [\A (-> (seq "BC") make-cf-state (assoc :a 1))])
; ;         "created exception rule works when symbol is not one of the syntatic exceptions")
; ;     (is (failure? (except-rule (make-cf-state (seq "BAC"))))
; ;         "created exception rule fails when symbol is one of the syntactic exceptions")
; ;     (is (failure? (except-rule (make-cf-state (seq "DAB"))))
; ;         "created exception rule fails when symbol does not fulfill subrule")))
; ; 
; ; (with-test
; ;   (defn rep*
; ;     "Creates a rule that is the zero-or-more
; ;     greedy repetition of the given subrule. It
; ;     always succeeds. It consumes tokens with
; ;     its subrule until its subrule fails.
; ;     Its result is the sequence of results from
; ;     the subrule's repetitions, (or nil if the
; ;     subrule fails immediately).
; ;     (def a (rep* b)) is equivalent to the EBNF:
; ;       a = {b};
; ;     The new rule's products would be either the
; ;     vector [b-product ...] for how many matches
; ;     of b were found, or nil if there was no
; ;     match. (Note that this means that, in the latter
; ;     case, the result would be [nil given-state].)
; ;     The new rule can never simply return nil."
; ;     [subrule]
; ;     (fn [state]
; ;       (loop [cur-product [], cur-state state]
; ;         (let [subresult (subrule cur-state)]
; ;           (if (success? subresult)
; ;             (let [[subproduct substate] subresult]
; ;               (if (seq (get-remainder substate))
; ;                 (recur (conj cur-product subproduct) substate)
; ;                 [(conj cur-product subproduct) substate]))
; ;             [(if (not= cur-product []) cur-product) cur-state])))))
; ;     ; The following code was used until I found
; ;     ; that the mutually recursive calls to rep+
; ;     ; resulted in an easily inflated function call stack.
; ;   ;  (opt (rep+ subrule)))
; ;   (let [rep*-true (rep* (lit true))
; ;         rep*-untrue (rep* (except anything (lit true)))]
; ;     (is (= (rep*-true (-> [true "THEN"] make-cf-state (assoc :a 3)))
; ;            [[true] (-> (list "THEN") make-cf-state (assoc :a 3))])
; ;         "created zero-or-more-repetition rule works when symbol present singularly")
; ;     (is (= (rep*-true (-> [true true true "THEN"] make-cf-state (assoc :a 3)))
; ;            [[true true true] (-> (list "THEN") make-cf-state (assoc :a 3))])
; ;         "created zero-or-more-repetition rule works when symbol present multiply")
; ;     (is (= (rep*-true (-> ["THEN"] make-cf-state (assoc :a 3)))
; ;            [nil (-> (list "THEN") make-cf-state (assoc :a 3))])
; ;      "created zero-or-more-repetition rule works when symbol absent")
; ;     (is (= (rep*-true (make-cf-state [true true true]))
; ;            [[true true true] (make-cf-state nil)])
; ;         "created zero-or-more-repetition rule works with no remainder after symbols")
; ;     (is (= (rep*-true (make-cf-state nil))
; ;            [nil (make-cf-state nil)])
; ;         "created zero-or-more-repetition rule works with no remainder")
; ;     (is (= (rep*-untrue (make-cf-state [false false]))
; ;            [[false false] (make-cf-state nil)])
; ;         "created zero-or-more-repetition negative rule works consuming up to end")
; ;     (is (= (rep*-untrue (make-cf-state [false false true]))
; ;            [[false false] (make-cf-state [true])])
; ;         "created zero-or-more-repetition negative rule works consuming until exception")
; ;     (is (= (rep*-untrue (make-cf-state nil))
; ;            [nil (make-cf-state nil)])
; ;         "created zero-or-more-repetition negative rule works with no remainder"))
; ;   (is (= ((rep* anything) (make-cf-state '(A B C)))
; ;          ['(A B C) (make-cf-state nil)])
; ;     "repeated anything rule does not create infinite loop"))
; ;  
; ; (with-test
; ;   (defn rep+
; ;     "Creates a rule that is the zero-or-more
; ;     greedy repetition of the given subrule. It
; ;     fails only when its subrule fails immediately.
; ;     It consumes tokens with its subrule until
; ;     its subrule fails. Its result is the sequence
; ;     of results from the subrule's repetitions.
; ;     (def a (rep* b)) is equivalent to the EBNF:
; ;       a = {b}-;
; ;     The new rule's products would be the vector
; ;     [b-product ...] for how many matches
; ;     of b were found. If there was no match, then
; ;     the rule fails."
; ;     [subrule]
; ;     (complex [first-product subrule, rest-products (rep* subrule)]
; ;       (vec (cons first-product rest-products))))
; ;     ; See note at rep*.
; ;   ;  (complex [cur-remainder (fetch-remainder)
; ;   ;            :when (seq cur-remainder)
; ;   ;            first-subproduct subrule
; ;   ;            rest-subproducts (rep* subrule)]
; ;   ;    (cons first-subproduct rest-subproducts)))
; ;   (let [rep+-true (rep+ (lit true))]
; ;     (is (= (rep+-true (make-cf-state [true "THEN"]))
; ;            [[true] (make-cf-state (list "THEN"))])
; ;         "created one-or-more-repetition rule works when symbol present singularly")
; ;     (is (= (rep+-true (make-cf-state [true true true "THEN"]))
; ;            [[true true true] (make-cf-state (list "THEN"))])
; ;         "created one-or-more-repetition rule works when symbol present multiply")
; ;     (is (failure? (rep+-true (make-cf-state (list "THEN"))))
; ;         "created one-or-more-repetition rule fails when symbol absent")))
; ;  
; ; (with-test
; ;   (defn rep-predicate
; ;     "Like the rep* function, only that the number
; ;     of times that the subrule is fulfilled must
; ;     fulfill the given factor-predicate function."
; ;     [factor-predicate subrule]
; ;     (validate (rep* subrule) (comp factor-predicate count)))
; ;   (let [tested-rule-fn (rep-predicate (partial > 3) (lit "A"))
; ;         infinity-rule (rep-predicate (partial > Double/POSITIVE_INFINITY)
; ;                         (lit "A"))]
; ;     (is (= (tested-rule-fn (make-cf-state (list "A" "A" "C")))
; ;            [["A" "A"] (make-cf-state (list "C"))])
; ;         "created rep rule works when predicate returns true")
; ;     (is (failure? (tested-rule-fn (make-cf-state (list "A" "A" "A"))))
; ;         "created rep rule fails when predicate returns false")
; ;     (is (= (tested-rule-fn (make-cf-state (list "D" "A" "B")))
; ;            [nil (make-cf-state (list "D" "A" "B"))])
; ;         "created rep rule succeeds when symbol does not fulfill subrule at all")))
; ;  
; ; (defn rep=
; ;   "Creates a rule that is the greedy repetition
; ;   of the given subrule by the given factor (a
; ;   positive integer)--that is, it eats up all the
; ;   tokens that fulfill the subrule, and it then
; ;   succeeds only if the number of times the subrule
; ;   was fulfilled is equal to the given factor, no
; ;   more and no less.
; ;   (rep= 3 :a) would eat the first three tokens of [:a :a :a :b] and return:
; ;     [[:a :a :a] (list :a :b)].
; ;   (rep= 3 :a) would eat the first four tokens of [:a :a :a :a :b] and fail."
; ;   [factor subrule]
; ;   (rep-predicate (partial = factor) subrule))
; ;  
; ; (defn rep<
; ;   "A similiar function to rep=, only that the
; ;   instead the new rule succeeds if the number
; ;   of times that the subrule is fulfilled is
; ;   less than and not equal to the given factor."
; ;   [factor subrule]
; ;   (rep-predicate (partial > factor) subrule))
; ;  
; ; (defn rep<=
; ;   "A similiar function to rep=, only that the
; ;   instead the new rule succeeds if the number
; ;   of times that the subrule is fulfilled is
; ;   less than or equal to the given factor."
; ;   [factor subrule]
; ;   (rep-predicate (partial >= factor) subrule))
; ;  
; ; (with-test
; ;   (defn factor=
; ;     "Creates a rule that is the syntactic factor
; ;     (that is, a non-greedy repetition) of the
; ;     given subrule by a given integer--that is, it
; ;     is equivalent to the subrule replicated by
; ;     1, 2, etc. times and then concatenated.
; ;     (def a (factor= n b)) would be equivalent to the EBNF
; ;       a = n * b;
; ;     The new rule's products would be b-product.
; ;     If b fails below n times, then nil is simply
; ;     returned.
; ;     (factor= 3 :a) would eat the first three
; ;     tokens [:a :a :a :a :b] and return:
; ;       [[:a :a :a] (list :a :b)].
; ;     (factor= 3 :a) would eat the first three
; ;     tokens [:a :a :b] and fail."
; ;     [factor subrule]
; ;     (m/with-monad parser-m
; ;       (m/m-seq (replicate factor subrule))))
; ;   (let [tested-rule-3 (factor= 3 (lit "A"))
; ;         tested-rule-0 (factor= 0 (lit "A"))]
; ;     (is (= (tested-rule-3 (make-cf-state (list "A" "A" "A" "A" "C")))
; ;            [["A" "A" "A"] (make-cf-state (list "A" "C"))])
; ;         (str "created factor= rule works when symbol fulfills all subrule multiples and"
; ;              "leaves strict remainder"))
; ;     (is (= (tested-rule-3 (make-cf-state (list "A" "A" "A" "C")))
; ;            [["A" "A" "A"] (make-cf-state (list "C"))])
; ;         "created factor= rule works when symbol fulfills all subrule multiples only")
; ;     (is (failure? (tested-rule-3 (make-cf-state (list "A" "A" "C"))))
; ;         "created factor= rule fails when symbol does not fulfill all subrule multiples")
; ;     (is (failure? (tested-rule-3 (make-cf-state (list "D" "A" "B"))))
; ;         "created factor= rule fails when symbol does not fulfill subrule at all")
; ;     (is (= (tested-rule-0 (make-cf-state (list "D" "A" "B")))
; ;            [[] (make-cf-state (list "D" "A" "B"))])
; ;         "created factor= rule works when symbol fulfils no multiples and factor is zero")))
; ;  
; ; (with-test
; ;   (defn factor<
; ;     "Same as the factor= function, except that the
; ;     new rule eats up tokens only until the
; ;     given subrule is fulfilled one less times than
; ;     the factor. The new rule would never fail.
; ;     (factor< 3 :a) would eat the first two tokens [:a :a :a :a :b] and return:
; ;       [[:a :a] (list :a :a :b)].
; ;     (factor< 3 :a) would eat the first three tokens [:b] and return:
; ;       [nil (list :b)]"
; ;     [factor subrule]
; ;     (alt (factor= (dec factor) subrule) (rep< factor subrule)))
; ;   (let [tested-rule (factor< 3 (lit \A))]
; ;     (is (= (tested-rule (make-cf-state (seq "AAAAC")))
; ;            [[\A \A] (make-cf-state (seq "AAC"))])
; ;         (str "created factor< rule works when symbol fulfills all subrule multiples and"
; ;              "leaves strict remainder"))
; ;     (is (= (tested-rule (make-cf-state (seq "AAAC")))
; ;            [[\A \A] (make-cf-state (seq "AC"))])
; ;         "created factor< rule works when symbol fulfills all subrule multiples only")
; ;     (is (= (tested-rule (make-cf-state (seq "AAC"))) [[\A \A] (make-cf-state (seq "C"))])
; ;         "created factor< rule works when symbol does not fulfill all subrule multiples")
; ;     (is (= (tested-rule (make-cf-state (seq "DAB")))
; ;            [nil (make-cf-state (seq "DAB"))])
; ;         "created factor< rule works when symbol does not fulfill subrule at all")))
; ;  
; ; (defn factor<=
; ;   "Same as the factor= function, except that
; ;   the new rule always succeeds, consuming tokens
; ;   until the subrule is fulfilled the same amount
; ;   of times as the given factor. The new rule
; ;   would never fail.
; ;   (factor<= 3 :a) would eat the first two tokens [:a :a :a :a :b] and return:
; ;     [[:a :a :a] (list :a :b)].
; ;   (factor<= 3 :a) would eat the first three tokens [:b] and return:
; ;     [nil (list :b)]"
; ;   [factor subrule]
; ;   (alt (factor= factor subrule) (rep< factor subrule)))
; ;  
; ; (with-test
; ;   (defn failpoint
; ;     "Creates a rule that applies a failpoint to
; ;     a subrule. When the subrule fails—i.e., it
; ;     returns nil—then the failure hook function
; ;     is called with one argument, the state at time
; ;     of failure."
; ;     [subrule failure-hook]
; ;     (fn [state]
; ;       (let [result (subrule state)]
; ;         (if (success? result)
; ;           result
; ;           (failure-hook (get-remainder state) state)))))
; ;   (let [exception-rule (failpoint (lit "A")
; ;                           (fn [remainder state]
; ;                             (throw-arg "ERROR %s at line %s"
; ;                               (first remainder) (:line state))))]
; ;     (is (= (exception-rule (-> ["A"] make-cf-state (assoc :line 3)))
; ;            ["A" (-> nil make-cf-state (assoc :line 3))])
; ;         "failing rules succeed when their subrules are fulfilled")
; ;     (is (thrown-with-msg? IllegalArgumentException
; ;           #"ERROR B at line 3"
; ;           (exception-rule (-> ["B"] make-cf-state (assoc :line 3)))
; ;         "failing rules fail with given exceptions when their subrules fail"))))
; ;  
; ; (with-test
; ;   (defmacro effects
; ;     "Creates a rule that calls the lists given
; ;     in its body for side effects. It does not
; ;     consume any tokens or modify the state in
; ;     any other way."
; ;     [& effect-body]
; ;     `(fn [state#]
; ;        [((fn [] ~@effect-body)) state#])))
; ;  
; ; (set-test effects
; ;   (let [rule
; ;          (complex [subproduct (lit "A")
; ;                    line-number (fetch-info :line)
; ;                    effects (effects (println "!" subproduct)
; ;                                     (println "YES" line-number))]
; ;            subproduct)]
; ;     (is (= (with-out-str
; ;              (is (= (rule (-> ["A" "B"] make-cf-state (assoc :line 3)))
; ;                     ["A" (-> (list "B") make-cf-state (assoc :line 3))])
; ;                  "pre-effect rules succeed when their subrules are fulfilled"))
; ;            "! A\nYES 3\n")
; ;         "effect rule should call their effect and return the same state")))
; ; 
; ; (with-test
; ;   (defn intercept
; ;     "This rule is intended for intercepting
; ;     and continuing exceptions and errors.
; ;     It creates a rule that calls the intercept
; ;     hook. The intercept hook is a function that
; ;     receives only one argument: a function to be
; ;     called with no arguments that calls the
; ;     subrule with the current state. If you don't
; ;     call this argument in the intercept hook, the
; ;     subrule will not be called at all. The result
; ;     of the whole rule will be directly what the
; ;     product of the intercept-hook is. Here's an
; ;     example of intended usage:
; ;       (intercept subrule-that-can-throw-an-exception
; ;         (fn [rule-call]
; ;           (try (rule-call)
; ;             (catch Exception e (throw another-exception)))))"
; ;     [subrule intercept-hook]
; ;     (fn [state] (intercept-hook (partial subrule state))))
; ;   (let [parse-error-rule
; ;           (semantics (lit \A) (fn [_] (throw (Exception.))))
; ;         intercept-rule
; ;           (intercept parse-error-rule
; ;             (fn [rule-call]
; ;               (try (rule-call)
; ;                 (catch Exception e :error))))]
; ;     (is (= (intercept-rule (make-cf-state "ABC")) :error))))
; ;  
; ; (defn validate-state
; ;   "Creates a rule from attaching a
; ;   state-validating function to the given
; ;   subrule--that
; ;   is, any products of the subrule must fulfill
; ;   the validator function.
; ;   (def a (validate-state b validator)) says
; ;   that the rule a succeeds only when b succeeds
; ;   and also when the evaluated value of
; ;   (validator b-state) is true. The new rule's
; ;   product would be b-product."
; ;   [subrule validator]
; ;   (complex [subproduct subrule
; ;             substate fetch-state
; ;             :when (validator substate)]
; ;     subproduct))
; ;  
; ; (defn validate-remainder
; ;   "Creates a rule from attaching a
; ;   remainder-validating function to the given
; ;   subrule--that is, any products of the subrule
; ;   must fulfill the validator function.
; ;   (def a (validate-remainder b validator)) says
; ;   that the rule a succeeds only when b succeeds
; ;   and also when the evaluated value of
; ;   (validator b-remainder) is true. The new rule's
; ;   product would be b-product."
; ;   [subrule validator]
; ;   (complex [subproduct subrule
; ;             subremainder (fetch-remainder)
; ;             :when (validator subremainder)]
; ;     subproduct))
; ; 
; ; ; ; (defvar- constantly-nil
; ; ; ;   (constantly nil))
; ; ; ; 
; ; ; ; (with-test
; ; ; ;   (defnk match-rule
; ; ; ;     "Creates a function that tries to completely
; ; ; ;     match the given rule to the given state,
; ; ; ;     with no remainder left over after the match.
; ; ; ;     - If (rule state-0) fails, then
; ; ; ;       (failure state-0) is called.
; ; ; ;     - If the remainder of the state in the result of
; ; ; ;       (rule state-0) is not empty, then...
; ; ; ;         (incomplete
; ; ; ;           product-from-consumed-tokens
; ; ; ;           new-state-after-rule
; ; ; ;           initial-state)
; ; ; ;       ...is called.
; ; ; ;     - If the new remainder is empty, then the
; ; ; ;       product of the rule is returned.
; ; ; ;     - The failure and incomplete functions are by
; ; ; ;       default (constantly nil)."
; ; ; ;     [state-0 rule :failure constantly-nil, :incomplete constantly-nil]
; ; ; ;     (if-let [[product state-1] (rule state-0)]
; ; ; ;       (if (empty? (get-remainder state-1))
; ; ; ;         product
; ; ; ;         (incomplete product state-1 state-0))
; ; ; ;       (failure state-0)))
; ; ; ;   (let [rule (lit "A")
; ; ; ;         matcher #(match-rule % rule
; ; ; ;                    :failure identity, :incomplete vector)]
; ; ; ;     (is (= (matcher (make-cf-state ["A"])) "A"))
; ; ; ;     (is (= (matcher (make-cf-state ["B"])) (make-cf-state ["B"])))
; ; ; ;     (is (= (matcher (make-cf-state ["A" "B"]))
; ; ; ;            ["A" (make-cf-state ["B"]) (make-cf-state ["A" "B"])]))))
; ; ; ; 
; ; ; ; ; (defmacro memoize-rules
; ; ; ; ;   "Turns the subrules contained in the vars
; ; ; ; ;   referred to by the given symbols
; ; ; ; ;   into memoizing rules that caches
; ; ; ; ;   their results in atoms. In effect, memoize
; ; ; ; ;   is called on all of the rules.
; ; ; ; ;   Whenever the new mem rule is called,
; ; ; ; ;   it checks the cache to see if there is an
; ; ; ; ;   existing match; otherwise, the subrule is called.
; ; ; ; ;  
; ; ; ; ;   Why didn't I just implement this as a
; ; ; ; ;   regular rule-making function? Because this
; ; ; ; ;   is truly only useful for optimization.
; ; ; ; ;   It is better to separate this non-essential
; ; ; ; ;   complexity from the actual definition of
; ; ; ; ;   your rules. It also makes it easier to
; ; ; ; ;   change which rules are optimized.
; ; ; ; ;   Thanks to Chouser for how to do this
; ; ; ; ;   with a variable.
; ; ; ; ;   
; ; ; ; ;   Running (test memoize-rules), which repeats a bunch of
; ; ; ; ;   calls on mem-test-rule two hundred times, takes about
; ; ; ; ;   160 ms on my computer, which uses an 2.2 GHz Intel Core
; ; ; ; ;   Duo and 2 GB of RAM.
; ; ; ; ;   Omitting the memoize-rules form above causes the same test
; ; ; ; ;   to take 430 ms, a very high 92% difference."
; ; ; ; ;   [& subrule-names]
; ; ; ; ;   (let [subrule-vars (vec (for [nm subrule-names] `(var ~nm)))]
; ; ; ; ;     `(doseq [subrule-var# ~subrule-vars]
; ; ; ; ;        (alter-var-root subrule-var# memoize))))
; ; ; ; ;  
; ; ; ; ; (defvar- mem-test-rule
; ; ; ; ;   (alt (conc (lit 'a) (opt (lit 'b))) (lit 'c)))
; ; ; ; ;  
; ; ; ; ; (memoize-rules mem-test-rule)
; ; ; ; ;   ; Running (test memoize-rules), which repeats a bunch of
; ; ; ; ;   ; calls on mem-test-rule two hundred times, takes about
; ; ; ; ;   ; 160 ms on my computer, which uses an 2.2 GHz Intel Core
; ; ; ; ;   ; Duo and 2 GB of RAM.
; ; ; ; ;   ; Omitting the memoize-rules form above causes the same test
; ; ; ; ;   ; to take 430 ms, a very high 92% difference.
; ; ; ; ;  
; ; ; ; ; (set-test memoize-rules
; ; ; ; ;   (dotimes [n 200]
; ; ; ; ;     (is (= (mem-test-rule (make-cf-state '[a c]))
; ; ; ; ;            [['a nil] (make-cf-state '[c])]))
; ; ; ; ;     (is (= (mem-test-rule (make-cf-state '[a b c]))
; ; ; ; ;            ['[a b] (make-cf-state '[c])]))
; ; ; ; ;     (is (= (mem-test-rule (make-cf-state '[a b c]))
; ; ; ; ;            ['[a b] (make-cf-state '[c])]))
; ; ; ; ;     (is (= (mem-test-rule (make-cf-state '[c s a])) ['c (make-cf-state '[s a])]))
; ; ; ; ;     (let [result (mem-test-rule (make-cf-state '(c)))]
; ; ; ; ;       (is (= (first result) 'c))
; ; ; ; ;       (is (empty? (seq (get-remainder (second result))))))
; ; ; ; ;     (is (failure? (mem-test-rule (make-cf-state '[s a]))))
; ; ; ; ;     (is (failure? (mem-test-rule (make-cf-state '[s a]))))))
; ; ; ; ;  
; ; ; ; ; (defn- testing-rule-maker
; ; ; ; ;   [arg1 arg2]
; ; ; ; ;   (conc (opt arg1) (opt arg2)))
; ; ; ; ;  
; ; ; ; ; (state-context std-template
; ; ; ; ;   (defvar- testing-rm-rule
; ; ; ; ;     (testing-rule-maker (lit \a) (lit \b))))
; ; ; ; ;  
; ; ; ; ; (deftest test-rule-makers
; ; ; ; ;   (let [state-0 (state-context std-template (make-cf-state "ab"))
; ; ; ; ;         state-1 (state-context std-template (make-cf-state nil))]
; ; ; ; ;     (is (thrown? RuntimeException
; ; ; ; ;           (testing-rm-rule (make-cf-state "abc"))))
; ; ; ; ;     (is (= (testing-rm-rule state-0) [[\a \b] state-1]))))
; ; ; ; ; 
; ; ; ; ; (defn inc-column
; ; ; ; ;   "Meant to be used only with std-bundle states, or other states with an
; ; ; ; ;   integer :column val.
; ; ; ; ;  
; ; ; ; ;   Creates a new rule that calls the subrule, and then increments the column.
; ; ; ; ;   Meant to be called on literal rules of one non-break character."
; ; ; ; ;   [subrule]
; ; ; ; ;   (invisi-conc subrule (update-info :column inc)))
; ; ; ; ;  
; ; ; ; ; (defn inc-line
; ; ; ; ;   "Meant to be used only with std-bundle states, or other states with an
; ; ; ; ;   integer :column val and an integer :line val.
; ; ; ; ;  
; ; ; ; ;   Creates a new rule that calls the subrule, and then increments the line and
; ; ; ; ;   sets the column to zero."
; ; ; ; ;   [subrule]
; ; ; ; ;   (invisi-conc subrule
; ; ; ; ;     (update-info :line inc) (set-info :column 0)))
