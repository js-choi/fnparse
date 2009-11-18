(ns name.choi.joshua.fnparse
  [:use clojure.contrib.monads clojure.contrib.except
        clojure.contrib.error-kit clojure.contrib.def
        clojure.test]
  [:import [clojure.lang IPersistentMap PersistentArrayMap]])

; A RULE is a a function that:
; - Takes a state and returns either nil
;   or a vector pair.
;   - A STATE is a struct map that contains
;     a remainder and maybe info.
;     You create states using the BasicState function.
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
 
(declare lit rep* rep+ except state-context std-template)

(defprotocol AParseState
  "The protocol representing general FnParse states."
  (get-remainder [state]
    "Gets the state's remainder.")
  (assoc-remainder [state new-remainder]
    "Returns a state that's the old state
    associated with the new remainder."))

(extend IPersistentMap AParseState
  {:get-remainder :remainder
   :assoc-remainder #(assoc %1 :remainder %2)})

(deftype BasicState [remainder] [IPersistentMap])

(defn- general-assoc-remainder [state new-remainder]
  (assoc state :remainder new-remainder))

(extend ::BasicState AParseState
  {:get-remainder :remainder
   :assoc-remainder general-assoc-remainder})

(deftype StdState [remainder line column warnings] [IPersistentMap])

(extend ::StdState AParseState
  {:get-remainder :remainder
   :assoc-remainder general-assoc-remainder})

(deferror fnparse-error [] [message-template & template-args]
  {:msg (str "FnParse error: " (apply format message-template template-args))
   :unhandled (throw-msg Exception)})
 
(defvar parser-m
  (state-t maybe-m)
  "The parser monad of FnParse. What new
  forms can you form from this?")

(with-test
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
    `(domonad parser-m ~steps ~@product-expr)))
 
(defvar- get-state
  (fetch-state)
  "A rule that consumes no tokens. Its product
  is the entire current state.
  [Equivalent to the result of fetch-state
  from clojure.contrib.monads.]")
 
(defn get-info
  "Creates a rule that consumes no tokens.
  The new rule's product is the value
  of the given key in the current state.
  [Equivalent to fetch-val from clojure.contrib.monads.]"
  [key]
  (fetch-val key))
 
(with-test
  (defn fetch-remainder
    "Generates a rule whose product is the
    sequence of the remaining tokens of any states
    that it is given. It consumes no tokens.
    [(fetch-remainder) is equivalent to
    (fetch-val get-remainder) from
    clojure.contrib.monads.]"
    []
    (fetch-val get-remainder))
  (is (= ((complex [remainder (fetch-remainder)] remainder)
          (BasicState ["hi" "THEN"]))
         [["hi" "THEN"] (BasicState ["hi" "THEN"])])))
 
(defn set-info
  "Creates a rule that consumes no tokens.
  The new rule directly changes the
  current state by associating the given
  key with the given value. The product
  is the old value of the changed key.
  [Equivalent to set-val from
  clojure.contrib.monads.]"
  [key value]
  (set-val key value))
 
(with-test
  (defn update-info
    "Creates a rule that consumes no tokens.
    The new rule changes the current state
    by associating the given key with the
    evaluated result of applying the given
    updating function to the key's current
    value. The product is the old value of
    the changed key.
    [Equivalent to update-val from clojure.contrib.monads.]"
    [key val-update-fn & args]
    (update-val key #(apply val-update-fn % args)))
  (is (= (-> [\a] BasicState (assoc :column 3)
           ((update-info :column inc)))
         [3 (-> [\a] BasicState (assoc :column 4))])))
 
(with-test
  (with-monad parser-m
    (defvar emptiness
      (m-result nil)
      "A rule that matches emptiness--that
      is, it always matches with every given
      token sequence, and it always returns
      [nil given-state].
      (def a emptiness) would be equivalent
      to the EBNF a = ; This rule's product
      is always nil, and it therefore always
      returns [nil given-state]."))
  (is (= (emptiness (BasicState '(A B C)))
         [nil (BasicState '(A B C))])
      "emptiness rule matches emptiness"))
 
(with-test
  (defn anything
    "A rule that matches anything--that is, it matches
    the first token of the tokens it is given.
    This rule's product is the first token it receives.
    It fails if there are no tokens left."
    [state]
    (if-let [tokens (get-remainder state)]
      [(first tokens)
       (assoc-remainder state (next tokens))]))
  (is (= (anything {:remainder '(A B C)})
         ['A {:remainder '(B C)}]))
  (is (= (anything (BasicState '(A B C)))
         ['A (BasicState '(B C))])
    "anything rule matches first token")
  (is (nil? (anything (BasicState nil)))
    "anything rule fails with no tokens left")
  (is (= ((rep* anything) (BasicState '(A B C)))
         ['(A B C) (BasicState nil)])
    "repeated anything rule does not create infinite loop"))
 
(with-test
  (defn validate
    "Creates a rule from attaching a product-validating function to the given
    subrule--that is, any products of the subrule must fulfill the validator
    function.
    (def a (validate b validator)) says that the rule a succeeds only when b
    succeeds and also when the evaluated value of (validator b-product) is true.
    The new rule's product would be b-product."
    [subrule validator]
    (complex [subproduct subrule, :when (validator subproduct)]
      subproduct))
  (is (= ((validate (lit "hi") (partial = "hi")) (BasicState ["hi" "THEN"]))
         ["hi" (BasicState (list "THEN"))])
      "created validator rule succeeds when given subrule and validator succeed")
  (is (nil? ((validate (lit "hi") (partial = "RST")) (BasicState ["RST"])))
      "created validator rule fails when given subrule fails")
  (is (nil? ((validate (lit "hi") (partial = "hi")) (BasicState "hi")))
      "created validator rule fails when given validator fails"))
 
(with-test
  (defn term
    "(term validator) is equivalent
    to (validate anything validator).
    Creates a rule that is a terminal rule of the given validator--that is, it
    accepts only tokens for whom (validator token) is true.
    (def a (term validator)) would be equivalent to the EBNF
      a = ? (validator %) evaluates to true ?;
    The new rule's product would be the first token, if it fulfills the
    validator."
    [validator]
    (validate anything validator))
  (let [rule (term (partial = 'A))]
    (is (= (rule (BasicState '[A B])) ['A (BasicState '[B])])
      "created terminal rule works when first token fulfills validator")
    (is (nil? (rule (BasicState '[B B])))
      "created terminal rule fails when first token fails validator")
    (is (= (rule (BasicState '[A])) ['A (BasicState nil)])
      "created terminal rule works when no remainder")))
 
(with-test
  (defvar lit
    (comp term (partial partial =))
    "Equivalent to (comp term (partial partial =)).
    Creates a rule that is the terminal
    rule of the given literal token--that is,
    it accepts only tokens that are equal to
    the given literal token.
    (def a (lit \"...\")) would be equivalent to the EBNF
      a = \"...\";
    The new rule's product would be the first
    token, if it equals the given literal token.")
  (is (= ((lit 'A) (BasicState '[A B]))
         ['A (BasicState '[B])])
      "created literal rule works when literal token present")
  (is (nil? ((lit 'A) (BasicState '[B])))
      "created literal rule fails when literal token not present"))
 
(with-test
  (defvar re-term
    (comp term (partial partial re-matches))
    "Equivalent to (comp term (partial partial re-matches)).
    Creates a rule that is the terminal rule of the given regex--that is, it
    accepts only tokens that match the given regex.
    (def a (re-term #\"...\")) would be equivalent to the EBNF
      a = ? (re-matches #\"...\" %) evaluates to true ?;
    The new rule's product would be the first token, if it matches the given
    regex.")
  (is (= ((re-term #"\s*true\s*") (BasicState ["  true" "THEN"]))
         ["  true" (BasicState ["THEN"])])
      "created re-term rule works when first token matches regex")
  (is (nil? ((re-term #"\s*true\s*") (BasicState ["false" "THEN"])))
      "created re-term rule fails when first token does not match regex")
  (is (nil? ((re-term #"\s*true\s*") (BasicState nil)))
      "created re-term rule fails when no tokens are left"))
 
(deftest complex-test
  (let [rule1 (complex [a (lit 'A)] (str a "!"))
        rule2 (complex [a (lit 'A), b (lit 'B)] (str a "!" b))]
    (is (= (rule1 (BasicState '[A B])) ["A!" (BasicState '[B])])
      "created complex rule applies semantic hook to valid subresult")
    (is (nil? (rule1 (BasicState '[B A])))
      "created complex rule fails when a given subrule fails")
    (is (= (rule2 (BasicState '[A B C])) ["A!B" (BasicState '[C])])
      "created complex rule succeeds when all subrules fulfilled in order")
    (is (nil? (rule2 (BasicState '[A C])))
      "created complex rule fails when one subrule fails")))
 
(with-test
  (defn followed-by
    "Creates a rule that does not consume any tokens, but fails when the given
    subrule fails.
    The new rule's product would be the subrule's product."
    [subrule]
    (complex [state get-state, subproduct subrule, _ (set-state state)]
      subproduct))
  (is (= ((followed-by (lit 'A)) (BasicState '[A B C]))
         ['A (BasicState '[A B C])]))
  (is (nil? ((followed-by (lit 'A)) (BasicState '[B C])))))
 
(with-test
  (defn not-followed-by
    "Creates a rule that does not consume any tokens, but fails when the given
    subrule succeeds. On success, the new rule's product is always true."
    [subrule]
    (fn [state]
      (if (nil? (subrule state))
        [true state])))
  (is (= ((not-followed-by (lit 'A)) (BasicState '[B C]))
         [true (BasicState '[B C])]))
  (is (nil? ((not-followed-by (lit 'A)) (BasicState '[A B C])))))
 
(with-test
  (defn semantics
    "Creates a rule with a semantic hook,
    basically a simple version of a complex
    rule. The semantic hook is a function
    that takes one argument: the product of
    the subrule."
    [subrule semantic-hook]
    (complex [subproduct subrule]
      (semantic-hook subproduct)))
  (is (= ((semantics (lit "hi") #(str % "!")) (BasicState ["hi" "THEN"]))
         ["hi!" (BasicState (list "THEN"))])
      "created simple semantic rule applies semantic hook to valid result of given rule"))
 
(defn constant-semantics
  "Creates a rule with a constant semantic
  hook. Its product is always the given
  constant."
  [subrule semantic-value]
  (complex [subproduct subrule]
    semantic-value))
 
(with-test
  (defn remainder-peek
    "Generates a rule whose product is the very next
    token in the remainder of any given state.
    The new rule does not consume any tokens."
    []
    (complex [remainder (fetch-remainder)]
      (first remainder)))
  (is (= ((remainder-peek) (BasicState (seq "ABC")))
         [\A (BasicState (seq "ABC"))])))
 
(with-test
  (defmacro conc
    "Creates a rule that is the concatenation
    of the given subrules. Basically a simple
    version of complex, each subrule consumes
    tokens in order, and if any fail, the entire
    rule fails.
    (def a (conc b c d)) would be equivalent to the EBNF:
      a = b, c, d;
    This macro is almost equivalent to m-seq for
    the parser-m monad. The difference is that
    it defers evaluation of whatever variables
    it receives, so that it accepts expressions
    containing unbound variables that are defined later."
    [& subrules]
    `(with-monad parser-m
       (fn [state#]
         ((m-seq ~(vec subrules)) state#)))))
 
(set-test conc
  (is (= ((conc (lit "hi") (lit "THEN"))
          (BasicState ["hi" "THEN" "bye"]))
         [["hi" "THEN"] (BasicState (list "bye"))])
      "created concatenated rule succeeds when all subrules fulfilled in order")
  (is (nil? ((conc (lit "hi") (lit "THEN"))
             (BasicState ["hi" "bye" "boom"])))
      "created concatenated rule fails when one subrule fails"))
 
(defmacro alt
  "Creates a rule that is the alternation
  of the given subrules. It succeeds when
  any of its subrules succeed, and fails
  when none do. Its result is that of the first
  subrule that succeeds, so the order of the
  subrules that this function receives matters.
  (def a (alt b c d)) would be equivalent to the EBNF:
   a = b | c | d;
  This macro is almost equivalent to m-plus for
  the parser-m monad. The difference is that
  it defers evaluation of whatever variables it
  receives, so that it accepts expressions containing
  unbound variables that are defined later."
  [& subrules]
  `(with-monad parser-m
     (fn [state#]
       ((~'m-plus ~@subrules) state#))))
 
(set-test alt
  (is (= ((alt (lit "hi") (lit "THEN"))
          (BasicState ["THEN" "bye"]))
         ["THEN" (BasicState (list "bye"))]))
  (is (nil? ((alt (lit "hi") (lit "THEN"))
             (BasicState ["bye" "boom"])))))
 
(with-test
  (defn opt
    "Creates a rule that is the optional form
    of the subrule. It always succeeds. Its result
    is either the subrule's (if the subrule
    succeeds), or else its product is nil, and the
    rule acts as the emptiness rule.
    (def a (opt b)) would be equivalent to the EBNF:
      a = b?;"
    [subrule]
    (with-monad parser-m
      (m-plus subrule emptiness)))
  (let [opt-true (opt (lit "true"))]
    (is (= (opt-true (BasicState ["true" "THEN"]))
           ["true" (BasicState (list "THEN"))])
        "created option rule works when symbol present")
    (is (= (opt-true (BasicState (list "THEN")))
           [nil (BasicState (list "THEN"))])
        "created option rule works when symbol absent")))
 
(with-test
  (defmacro invisi-conc
    "Like conc, only that the product is the
    first subrule's product only, not a vector of
    all the products of the subrules--effectively
    hiding the products of the other subrules.
    The rest of the subrules consume tokens too;
    their products simply aren't accessible.
    This is useful for applying set-info and
    update-info to a rule, without having to deal
    with set-info or update-info's products."
    [first-subrule & rest-subrules]
    `(semantics (conc ~first-subrule ~@rest-subrules) first)))
 
(set-test invisi-conc
  (is (= ((invisi-conc (lit \a) (update-info :column inc))
           (-> "abc" BasicState (assoc :column 4)))
         [\a (-> "bc" seq BasicState (assoc :column 5))])))
 
(with-test
  (defn lit-conc-seq
    "A convenience function: it creates a rule
    that is the concatenation of the literals
    formed from the given sequence of literal tokens.
    (def a (lit-conc-seq [\"a\" \"b\" \"c\"]))
    would be equivalent to the EBNF:
      a = \"a\", \"b\", \"c\";
    The function has an optional argument: a
    rule-making function. By default it is the lit
    function. This is the function that is used
    to create the literal rules from each element
    in the given token sequence."
    ([token-seq]
     (lit-conc-seq token-seq lit))
    ([token-seq rule-maker]
     (with-monad parser-m
       (m-seq (map rule-maker token-seq)))))
  (is (= ((lit-conc-seq "THEN") (BasicState "THEN print 42;"))
         [(vec "THEN") (BasicState (seq " print 42;"))])
      "created literal-sequence rule is based on sequence of given token sequencible")
  (is (= ((lit-conc-seq "THEN"
            (fn [lit-token]
              (invisi-conc (lit lit-token)
                (update-info :column inc))))
          (-> "THEN print 42;" BasicState (assoc :column 1)))
         [(vec "THEN") (-> (seq " print 42;") BasicState (assoc :column 5))])
      "created literal-sequence rule uses given rule-maker"))
 
(with-test
  (defn lit-alt-seq
    "A convenience function: it creates a rule
    that is the alternation of the literals
    formed from the given sequence of literal tokens.
    (def a (lit-alt-seq [\"a\" \"b\" \"c\"]))
    would be equivalent to the EBNF:
      a = \"a\" | \"b\" | \"c\";"
    ([token-seq]
     (lit-alt-seq token-seq lit))
    ([token-seq rule-maker]
     (with-monad parser-m
       (apply m-plus (map rule-maker token-seq)))))
  (is (= ((lit-alt-seq "ABCD") (BasicState (seq "B 2")))
         [\B (BasicState (seq " 2"))])
      (str "created literal-alternative-sequence rule "
           "works when literal symbol present in sequence"))
  (is (nil? ((lit-alt-seq "ABCD") (BasicState (seq "E 2"))))
      (str "created literal-alternative-sequence "
           "rule fails when literal symbol not "
           "present in sequence"))
  (is (= ((lit-alt-seq "ABCD"
            (fn [lit-token]
              (invisi-conc (lit lit-token)
                           (update-info :column inc))))
          (-> "B 2" BasicState (assoc :column 1)))
         [\B (-> (seq " 2") BasicState (assoc :column 2))])
      "created literal-alternative-sequence rule uses given rule-maker"))
 
(with-test
  (defn rep*
    "Creates a rule that is the zero-or-more
    greedy repetition of the given subrule. It
    always succeeds. It consumes tokens with
    its subrule until its subrule fails.
    Its result is the sequence of results from
    the subrule's repetitions, (or nil if the
    subrule fails immediately).
    (def a (rep* b)) is equivalent to the EBNF:
      a = {b};
    The new rule's products would be either the
    vector [b-product ...] for how many matches
    of b were found, or nil if there was no
    match. (Note that this means that, in the latter
    case, the result would be [nil given-state].)
    The new rule can never simply return nil."
    [subrule]
    (fn [state]
      (loop [cur-product [], cur-state state]
        (if-let [[subproduct substate] (subrule cur-state)]
          (if (seq (get-remainder substate))
            (recur (conj cur-product subproduct) substate)
            [(conj cur-product subproduct) substate])
          [(if (not= cur-product []) cur-product) cur-state]))))
    ; The following code was used until I found
    ; that the mutually recursive calls to rep+
    ; resulted in an easily inflated function call stack.
  ;  (opt (rep+ subrule)))
  (let [rep*-true (rep* (lit true))
        rep*-untrue (rep* (except anything (lit true)))]
    (is (= (rep*-true (-> [true "THEN"] BasicState (assoc :a 3)))
           [[true] (-> (list "THEN") BasicState (assoc :a 3))])
        "created zero-or-more-repetition rule works when symbol present singularly")
    (is (= (rep*-true (-> [true true true "THEN"] BasicState (assoc :a 3)))
           [[true true true] (-> (list "THEN") BasicState (assoc :a 3))])
        "created zero-or-more-repetition rule works when symbol present multiply")
    (is (= (rep*-true (-> ["THEN"] BasicState (assoc :a 3)))
           [nil (-> (list "THEN") BasicState (assoc :a 3))])
     "created zero-or-more-repetition rule works when symbol absent")
    (is (= (rep*-true (BasicState [true true true]))
           [[true true true] (BasicState nil)])
        "created zero-or-more-repetition rule works with no remainder after symbols")
    (is (= (rep*-true (BasicState nil))
           [nil (BasicState nil)])
        "created zero-or-more-repetition rule works with no remainder")
    (is (= (rep*-untrue (BasicState [false false]))
           [[false false] (BasicState nil)])
        "created zero-or-more-repetition negative rule works consuming up to end")
    (is (= (rep*-untrue (BasicState [false false true]))
           [[false false] (BasicState [true])])
        "created zero-or-more-repetition negative rule works consuming until exception")
    (is (= (rep*-untrue (BasicState nil))
           [nil (BasicState nil)])
        "created zero-or-more-repetition negative rule works with no remainder")))
 
(with-test
  (defn rep+
    "Creates a rule that is the zero-or-more
    greedy repetition of the given subrule. It
    fails only when its subrule fails immediately.
    It consumes tokens with its subrule until
    its subrule fails. Its result is the sequence
    of results from the subrule's repetitions.
    (def a (rep* b)) is equivalent to the EBNF:
      a = {b}-;
    The new rule's products would be the vector
    [b-product ...] for how many matches
    of b were found. If there was no match, then
    the rule fails."
    [subrule]
    (complex [first-product subrule, rest-products (rep* subrule)]
      (vec (cons first-product rest-products))))
    ; See note at rep*.
  ;  (complex [cur-remainder (fetch-remainder)
  ;            :when (seq cur-remainder)
  ;            first-subproduct subrule
  ;            rest-subproducts (rep* subrule)]
  ;    (cons first-subproduct rest-subproducts)))
  (let [rep+-true (rep+ (lit true))]
    (is (= (rep+-true (BasicState [true "THEN"]))
           [[true] (BasicState (list "THEN"))])
        "created one-or-more-repetition rule works when symbol present singularly")
    (is (= (rep+-true (BasicState [true true true "THEN"]))
           [[true true true] (BasicState (list "THEN"))])
        "created one-or-more-repetition rule works when symbol present multiply")
    (is (nil? (rep+-true (BasicState (list "THEN"))))
        "created one-or-more-repetition rule fails when symbol absent")))
 
(with-test
  (defn except
    "Creates a rule that is the exception from
    the first given subrules with the second given
    subrule--that is, it accepts only tokens that
    fulfill the first subrule but fails the
    second of the subrules.
    (def a (except b c)) would be equivalent to the EBNF
      a = b - c;
    The new rule's products would be b-product. If
    b fails or c succeeds, then nil is simply returned."
    [minuend subtrahend]
    (complex [state (fetch-state)
              minuend-product minuend
              :when (not (subtrahend state))]
      minuend-product))
  (let [except-rule (except (lit-alt-seq "ABC") (alt (lit \B) (lit \C)))]
    (is (= (-> "ABC" BasicState (assoc :a 1) except-rule)
            [\A (-> (seq "BC") BasicState (assoc :a 1))])
        "created exception rule works when symbol is not one of the syntatic exceptions")
    (is (nil? (except-rule (BasicState (seq "BAC"))))
        "created exception rule fails when symbol is one of the syntactic exceptions")
    (is (nil? (except-rule (BasicState (seq "DAB"))))
        "created exception rule fails when symbol does not fulfill subrule")))
 
(with-test
  (defn rep-predicate
    "Like the rep* function, only that the number
    of times that the subrule is fulfilled must
    fulfill the given factor-predicate function."
    [factor-predicate subrule]
    (validate (rep* subrule) (comp factor-predicate count)))
  (let [tested-rule-fn (rep-predicate (partial > 3) (lit "A"))
        infinity-rule (rep-predicate (partial > Double/POSITIVE_INFINITY)
                        (lit "A"))]
    (is (= (tested-rule-fn (BasicState (list "A" "A" "C")))
           [["A" "A"] (BasicState (list "C"))])
        "created rep rule works when predicate returns true")
    (is (nil? (tested-rule-fn (BasicState (list "A" "A" "A"))))
        "created rep rule fails when predicate returns false")
    (is (= (tested-rule-fn (BasicState (list "D" "A" "B")))
           [nil (BasicState (list "D" "A" "B"))])
        "created rep rule succeeds when symbol does not fulfill subrule at all")))
 
(defn rep=
  "Creates a rule that is the greedy repetition
  of the given subrule by the given factor (a
  positive integer)--that is, it eats up all the
  tokens that fulfill the subrule, and it then
  succeeds only if the number of times the subrule
  was fulfilled is equal to the given factor, no
  more and no less.
  (rep= 3 :a) would eat the first three tokens of [:a :a :a :b] and return:
    [[:a :a :a] (list :a :b)].
  (rep= 3 :a) would eat the first four tokens of [:a :a :a :a :b] and fail."
  [factor subrule]
  (rep-predicate (partial = factor) subrule))
 
(defn rep<
  "A similiar function to rep=, only that the
  instead the new rule succeeds if the number
  of times that the subrule is fulfilled is
  less than and not equal to the given factor."
  [factor subrule]
  (rep-predicate (partial > factor) subrule))
 
(defn rep<=
  "A similiar function to rep=, only that the
  instead the new rule succeeds if the number
  of times that the subrule is fulfilled is
  less than or equal to the given factor."
  [factor subrule]
  (rep-predicate (partial >= factor) subrule))
 
(with-test
  (defn factor=
    "Creates a rule that is the syntactic factor
    (that is, a non-greedy repetition) of the
    given subrule by a given integer--that is, it
    is equivalent to the subrule replicated by
    1, 2, etc. times and then concatenated.
    (def a (factor= n b)) would be equivalent to the EBNF
      a = n * b;
    The new rule's products would be b-product.
    If b fails below n times, then nil is simply
    returned.
    (factor= 3 :a) would eat the first three
    tokens [:a :a :a :a :b] and return:
      [[:a :a :a] (list :a :b)].
    (factor= 3 :a) would eat the first three
    tokens [:a :a :b] and fail."
    [factor subrule]
    (with-monad parser-m
      (m-seq (replicate factor subrule))))
  (let [tested-rule-3 (factor= 3 (lit "A"))
        tested-rule-0 (factor= 0 (lit "A"))]
    (is (= (tested-rule-3 (BasicState (list "A" "A" "A" "A" "C")))
           [["A" "A" "A"] (BasicState (list "A" "C"))])
        (str "created factor= rule works when symbol fulfills all subrule multiples and"
             "leaves strict remainder"))
    (is (= (tested-rule-3 (BasicState (list "A" "A" "A" "C")))
           [["A" "A" "A"] (BasicState (list "C"))])
        "created factor= rule works when symbol fulfills all subrule multiples only")
    (is (= (tested-rule-3 (BasicState (list "A" "A" "C"))) nil)
        "created factor= rule fails when symbol does not fulfill all subrule multiples")
    (is (= (tested-rule-3 (BasicState (list "D" "A" "B"))) nil)
        "created factor= rule fails when symbol does not fulfill subrule at all")
    (is (= (tested-rule-0 (BasicState (list "D" "A" "B")))
           [[] (BasicState (list "D" "A" "B"))])
        "created factor= rule works when symbol fulfils no multiples and factor is zero")))
 
(with-test
  (defn factor<
    "Same as the factor= function, except that the
    new rule eats up tokens only until the
    given subrule is fulfilled one less times than
    the factor. The new rule would never fail.
    (factor< 3 :a) would eat the first two tokens [:a :a :a :a :b] and return:
      [[:a :a] (list :a :a :b)].
    (factor< 3 :a) would eat the first three tokens [:b] and return:
      [nil (list :b)]"
    [factor subrule]
    (alt (factor= (dec factor) subrule) (rep< factor subrule)))
  (let [tested-rule (factor< 3 (lit \A))]
    (is (= (tested-rule (BasicState (seq "AAAAC")))
           [[\A \A] (BasicState (seq "AAC"))])
        (str "created factor< rule works when symbol fulfills all subrule multiples and"
             "leaves strict remainder"))
    (is (= (tested-rule (BasicState (seq "AAAC")))
           [[\A \A] (BasicState (seq "AC"))])
        "created factor< rule works when symbol fulfills all subrule multiples only")
    (is (= (tested-rule (BasicState (seq "AAC"))) [[\A \A] (BasicState (seq "C"))])
        "created factor< rule works when symbol does not fulfill all subrule multiples")
    (is (= (tested-rule (BasicState (seq "DAB")))
           [nil (BasicState (seq "DAB"))])
        "created factor< rule works when symbol does not fulfill subrule at all")))
 
(defn factor<=
  "Same as the factor= function, except that
  the new rule always succeeds, consuming tokens
  until the subrule is fulfilled the same amount
  of times as the given factor. The new rule
  would never fail.
  (factor<= 3 :a) would eat the first two tokens [:a :a :a :a :b] and return:
    [[:a :a :a] (list :a :b)].
  (factor<= 3 :a) would eat the first three tokens [:b] and return:
    [nil (list :b)]"
  [factor subrule]
  (alt (factor= factor subrule) (rep< factor subrule)))
 
(with-test
  (defn failpoint
    "Creates a rule that applies a failpoint to
    a subrule. When the subrule fails—i.e., it
    returns nil—then the failure hook function
    is called with one argument, the state at time
    of failure."
    [subrule failure-hook]
    (fn [state]
      (if-let [result (subrule state)]
        result
        (failure-hook (get-remainder state) state))))
  (let [exception-rule (failpoint (lit "A")
                          (fn [remainder state]
                            (throw-arg "ERROR %s at line %s"
                              (first remainder) (:line state))))]
    (is (= (exception-rule (-> ["A"] BasicState (assoc :line 3)))
           ["A" (-> nil BasicState (assoc :line 3))])
        "failing rules succeed when their subrules are fulfilled")
    (is (thrown-with-msg? IllegalArgumentException
          #"ERROR B at line 3"
          (exception-rule (-> ["B"] BasicState (assoc :line 3)))
        "failing rules fail with given exceptions when their subrules fail"))))
 
(with-test
  (defmacro effects
    "Creates a rule that calls the lists given
    in its body for side effects. It does not
    consume any tokens or modify the state in
    any other way."
    [& effect-body]
    `(fn [state#]
       [((fn [] ~@effect-body)) state#])))
 
(deftest effects-test
  (let [rule
         (complex [subproduct (lit "A")
                     line-number (get-info :line)
                     effects (effects (println "!" subproduct)
                                      (println "YES" line-number))]
           subproduct)]
    (is (= (with-out-str
             (is (= (rule (-> ["A" "B"] BasicState (assoc :line 3)))
                    ["A" (-> (list "B") BasicState (assoc :line 3))])
                 "pre-effect rules succeed when their subrules are fulfilled"))
           "! A\nYES 3\n")
        "effect rule should call their effect and return the same state")))
 
(with-test
  (defn intercept
    "This rule is intended for intercepting
    and continuing exceptions and errors.
    It creates a rule that calls the intercept
    hook. The intercept hook is a function that
    receives only one argument: a function to be
    called with no arguments that calls the
    subrule with the current state. If you don't
    call this argument in the intercept hook, the
    subrule will not be called at all. The result
    of the whole rule will be directly what the
    product of the intercept-hook is. Here's an
    example of intended usage:
      (intercept subrule-that-can-throw-an-exception
        (fn [rule-call]
          (try (rule-call)
            (catch Exception e (throw another-exception)))))"
    [subrule intercept-hook]
    (fn [state] (intercept-hook (partial subrule state))))
  (let [parse-error-rule
          (semantics (lit \A) (fn [_] (throw (Exception.))))
        intercept-rule
          (intercept parse-error-rule
            (fn [rule-call]
              (try (rule-call)
                (catch Exception e :error))))]
    (is (= (intercept-rule (BasicState "ABC")) :error))))
 
(defn validate-state
  "Creates a rule from attaching a
  state-validating function to the given
  subrule--that
  is, any products of the subrule must fulfill
  the validator function.
  (def a (validate-state b validator)) says
  that the rule a succeeds only when b succeeds
  and also when the evaluated value of
  (validator b-state) is true. The new rule's
  product would be b-product."
  [subrule validator]
  (complex [subproduct subrule
            substate get-state
            :when (validator substate)]
    subproduct))
 
(defn validate-remainder
  "Creates a rule from attaching a
  remainder-validating function to the given
  subrule--that is, any products of the subrule
  must fulfill the validator function.
  (def a (validate-remainder b validator)) says
  that the rule a succeeds only when b succeeds
  and also when the evaluated value of
  (validator b-remainder) is true. The new rule's
  product would be b-product."
  [subrule validator]
  (complex [subproduct subrule
            subremainder (fetch-remainder)
            :when (validator subremainder)]
    subproduct))

; (defn make-template
;   [default-info]
;   (let [struct-keys
;           (cons ::remainder (keys default-info))
;         state-struct
;           (apply create-struct struct-keys)]
;     {:state-struct state-struct
;      :default-info default-info}))
;  
; (defvar std-template
;   (make-template
;     {:warnings []
;      :line 0
;      :column 0}))
;  
; (defvar minimal-template
;   (make-template {}))

(defvar- constantly-nil
  (constantly nil))

(with-test
  (defnk match-rule
    "Creates a function that tries to completely
    match the given rule to the given state,
    with no remainder left over after the match.
    - If (rule state-0) fails, then
      (failure state-0) is called.
    - If the remainder of the state in the result of
      (rule state-0) is not empty, then...
        (incomplete
          product-from-consumed-tokens
          new-state-after-rule
          initial-state)
      ...is called.
    - If the new remainder is empty, then the
      product of the rule is returned.
    - The failure and incomplete functions are by
      default (constantly nil)."
    [state-0 rule :failure constantly-nil, :incomplete constantly-nil]
    (if-let [[product state-1] (rule state-0)]
      (if (empty? (get-remainder state-1))
        product
        (incomplete product state-1 state-0))
      (failure state-0)))
  (let [rule (lit "A")
        matcher #(match-rule % rule
                   :failure identity, :incomplete vector)]
    (is (= (matcher (BasicState ["A"])) "A"))
    (is (= (matcher (BasicState ["B"])) (BasicState ["B"])))
    (is (= (matcher (BasicState ["A" "B"]))
           ["A" (BasicState ["B"]) (BasicState ["A" "B"])]))))

; (with-test
;   (defmacro state-context
;     "Puts all Clojure forms inside into a state context.
;     This is for customization of states, which affect
;     BasicState and all rules within the context.
;     
;     You customize by providing as a template a map of
;     your states' desired keys and their default values.
;     
;     In addition, you get a speed boost from the automatic
;     generation and use of a struct map and accessors, which
;     are invisibly used by BasicState and all rules.
;     
;     This form uses the binding form, so the context formed
;     is thread-specific.
;     
;     Here is an example to make it clearer how you
;     customize states. Let's say that I want my states to
;     store: (1) any warnings that a rule might want to raise
;     for the user during parsing, (2) the current line number,
;     and (3) the current column number.
;     
;     (use 'name.choi.joshua.fnparse)
;     
;     (def my-template
;       (make-template
;         {:warnings []
;          :line 0
;          :column 0
;          ::p/add-info add-info}))
;     
;     (state-context my-template
;       ; Define your rules and create states inside the context.
;       (def line-break
;         (invisi-conc (lit \\newline)
;           (update-info :line inc)
;           (set-info :column 0)))
;       (defn add-warning [line column]
;         (update-info :warnings
;           #(conj % (format \"Z FOUND AT line %s, col %s!\"
;                      line column))))
;       (def illegal-z
;         (complex [z (lit \\z)
;                   line (get-info :line)
;                   column (get-info :column)
;                   _ (add-warning line column)]
;           \"WRONG\"))
;       (def non-break
;         (invisi-conc (alt illegal-z (except line-break))
;           (update-info :column inc)))
;       (def text
;         (-> (alt line-break non-break) rep+ mem))
;       (def a-state (BasicState \"ABZ\\nC\"))
;         ; Returns
;         ; {::p/remainder \"ABZ\\nC\"
;         ;  :line 1
;         ;  :column 1
;         ;  :warnings []}
;       (text a-state)
;         ; Returns
;         ; [(\\A \\B \"WRONG\" \\newline \\C)
;         ;  {::p/remainder nil
;         ;   :line 2
;         ;   :column 1
;         ;   :warnings [\"Z FOUND AT line 1, column 3\"]}])"
;     [state-template & forms]
;     `(let [state-template#
;              ~state-template
;            add-info-fn#
;              (:add-info state-template#)
;            state-struct#
;              (:state-struct state-template#)
;            default-info#
;              (:default-info state-template#)
;            empty-state#
;              (into (struct state-struct#) default-info#)
;            get-remainder#
;              (accessor state-struct# ::remainder)]
;       (binding [*empty-state* empty-state#
;                 *get-remainder* get-remainder#
;                 *add-info* add-info-fn#]
;         ~@forms))))
;  
; (state-context std-template
;   (with-test
;     (defvar- state-context-test-rule anything)
;     (is (thrown? ClassCastException (state-context-test-rule {})))))
;  
; (set-test state-context
;   (let [state-0 (state-context std-template (BasicState "abc"))]
;     (is (= (state-context-test-rule state-0)))
;     (is (thrown? ClassCastException
;           (state-context-test-rule (BasicState "abc")))))
;   (let [rule-a (state-context std-template anything)
;         rule-b (state-context std-template (lit \a))
;         rule-c (state-context std-template (complex [x anything] x))
;         state-0 (state-context std-template (BasicState "abc"))
;         state-a (state-context std-template
;                   (-> "bc" seq BasicState (assoc :warnings [])))]
;     (is (= (rule-a state-0) [\a state-a]))
;     (is (thrown? ClassCastException
;           (rule-a (BasicState "abc"))))
;     (is (= (rule-b state-0) [\a state-a]))
;     (is (thrown? ClassCastException
;           (rule-b (BasicState "abc"))))
;     (is (= (rule-c state-0) [\a state-a]))
;     (is (thrown? ClassCastException
;           (rule-c (BasicState "abc")))))
;   (state-context (make-template {:warnings []})
;     (is (= (emptiness (BasicState "abc"))))
;     (is (= ((lit \a) (BasicState "abc"))
;            [\a (-> "bc" seq BasicState (assoc :warnings []))]))
;     (is (thrown? ClassCastException
;           ((lit \a) {::remainder []}))))
;   (state-context std-template
;     (is (= {::remainder "ABZ\nC"
;             :line 0
;             :column 0
;             :warnings []}
;            (BasicState "ABZ\nC"))))
;   (is (= (state-context minimal-template 5) 5)))
; 
; (defmacro memoize-rules
;   "Turns the subrules contained in the vars
;   referred to by the given symbols
;   into memoizing rules that caches
;   their results in atoms. In effect, memoize
;   is called on all of the rules.
;   Whenever the new mem rule is called,
;   it checks the cache to see if there is an
;   existing match; otherwise, the subrule is called.
;  
;   Why didn't I just implement this as a
;   regular rule-making function? Because this
;   is truly only useful for optimization.
;   It is better to separate this non-essential
;   complexity from the actual definition of
;   your rules. It also makes it easier to
;   change which rules are optimized.
;   Thanks to Chouser for how to do this
;   with a variable.
;   
;   Running (test memoize-rules), which repeats a bunch of
;   calls on mem-test-rule two hundred times, takes about
;   160 ms on my computer, which uses an 2.2 GHz Intel Core
;   Duo and 2 GB of RAM.
;   Omitting the memoize-rules form above causes the same test
;   to take 430 ms, a very high 92% difference."
;   [& subrule-names]
;   (let [subrule-vars (vec (for [nm subrule-names] `(var ~nm)))]
;     `(doseq [subrule-var# ~subrule-vars]
;        (alter-var-root subrule-var# memoize))))
;  
; (defvar- mem-test-rule
;   (alt (conc (lit 'a) (opt (lit 'b))) (lit 'c)))
;  
; (memoize-rules mem-test-rule)
;   ; Running (test memoize-rules), which repeats a bunch of
;   ; calls on mem-test-rule two hundred times, takes about
;   ; 160 ms on my computer, which uses an 2.2 GHz Intel Core
;   ; Duo and 2 GB of RAM.
;   ; Omitting the memoize-rules form above causes the same test
;   ; to take 430 ms, a very high 92% difference.
;  
; (set-test memoize-rules
;   (dotimes [n 200]
;     (is (= (mem-test-rule (BasicState '[a c]))
;            [['a nil] (BasicState '[c])]))
;     (is (= (mem-test-rule (BasicState '[a b c]))
;            ['[a b] (BasicState '[c])]))
;     (is (= (mem-test-rule (BasicState '[a b c]))
;            ['[a b] (BasicState '[c])]))
;     (is (= (mem-test-rule (BasicState '[c s a])) ['c (BasicState '[s a])]))
;     (let [result (mem-test-rule (BasicState '(c)))]
;       (is (= (first result) 'c))
;       (is (empty? (seq (get-remainder (second result))))))
;     (is (nil? (mem-test-rule (BasicState '[s a]))))
;     (is (nil? (mem-test-rule (BasicState '[s a]))))))
;  
; (defn- testing-rule-maker
;   [arg1 arg2]
;   (conc (opt arg1) (opt arg2)))
;  
; (state-context std-template
;   (defvar- testing-rm-rule
;     (testing-rule-maker (lit \a) (lit \b))))
;  
; (deftest test-rule-makers
;   (let [state-0 (state-context std-template (BasicState "ab"))
;         state-1 (state-context std-template (BasicState nil))]
;     (is (thrown? RuntimeException
;           (testing-rm-rule (BasicState "abc"))))
;     (is (= (testing-rm-rule state-0) [[\a \b] state-1]))))
; 
; (defn inc-column
;   "Meant to be used only with std-bundle states, or other states with an
;   integer :column val.
;  
;   Creates a new rule that calls the subrule, and then increments the column.
;   Meant to be called on literal rules of one non-break character."
;   [subrule]
;   (invisi-conc subrule (update-info :column inc)))
;  
; (defn inc-line
;   "Meant to be used only with std-bundle states, or other states with an
;   integer :column val and an integer :line val.
;  
;   Creates a new rule that calls the subrule, and then increments the line and
;   sets the column to zero."
;   [subrule]
;   (invisi-conc subrule
;     (update-info :line inc) (set-info :column 0)))
