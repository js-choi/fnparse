(ns name.choi.joshua.fnparse
  [:use clojure.contrib.monads clojure.contrib.except
        clojure.contrib.error-kit clojure.contrib.except
        clojure.contrib.def clojure.contrib.test-is])

; A rule is a delay object that contains a function that:
; - Takes a collection of tokens.
; - If the token sequence is valid, it returns a (0) vector containing the (1)
;   consumed symbols' products and (2) a state data object, usually a map. The
;   state contains the (3) sequence of remaining tokens, usually with the key
;   *remainder-accessor*.
; - If the given token sequence is invalid, then the rule Fails, meaning that it
;   simply returns nil.

; - (0) is called the rule's Result.
; - (1) is called the rule's Product.
; - (2) is called the rule's State.
; - (3) is called the rule's Remainder.

(declare lit rep* rep+ except standard-template)

(deferror fnparse-error [] [message-template & template-args]
  {:msg (str "FnParse error: " (apply format message-template template-args))
   :unhandled (throw-msg Exception)})

(defvar parser-m
  (state-t maybe-m)
  "The parser monad of FnParse. What new
  forms can you form from this?")

(defvar- *empty-state*
  {::remainder nil}
  "The overridable var for the context's
  empty state. It does not have an index
  assigned to its metadata; that's
  make-state's job.
  It's private. That's because you're
  supposed to use state-context, which
  does all the work for you.")

(defvar- *remainder-accessor*
  ::remainder
  "The overridable var for the context's
  remainder accessor. If the current
  context uses a struct map, then this
  var contains the speedy accessor for
  ::remainder. But in any case, it refers
  to the ::remainder key; I made that
  standard.
  The var is private. That's because you're
  supposed to use state-context, which
  does all the work for you.")

(defn fetch-remainder
  "Gets the state's remainder."
  [state]
  (*remainder-accessor* state))

(defn- assoc-remainder [state remainder]
  (assoc state ::remainder remainder))

(defn make-state
  "The general function that creates a state
  from the given sequence of tokens.
  You really must use this function to create
  any states that you'll plug into rules."
  [tokens]
  (with-meta (assoc-remainder *empty-state* tokens)
    {::index 0}))

(defn make-state-with-info
  "For mocking a state with already
  provided info. Basically calls make-state
  on the tokens and then applies info-args
  to assoc."
  [tokens & info-args]
  (apply assoc (make-state tokens) info-args))

(with-test
  (defvar- fetch-index
    (comp ::index meta)
    "Gets the given state's index.")
  (-> nil make-state fetch-index (= 0) is))

(defn- set-index
  "Sets the given state's index to the given new-index."
  [state new-index]
  (vary-meta state assoc ::index new-index))

(defn vary-index
  "Sets the given state's index to the result of
  applying the given function to the old index."
  [state f]
  (set-index state (f (fetch-index state))))

(defn new-info
  "Creates a new state with the given info."
  [& info-keys-and-vals]
  (apply assoc *empty-state* info-keys-and-vals))

(defvar- *add-info*
  merge
  "Overridable by using state-context.
  Merges two states' info together. The first
  state is the primary one, and the second state
  adds its warnings, line numbers, and whatever
  info it has to the first state's.")

(with-test
  (defn- add-states
    "This function is not expected to be
    useful for users--only the mem rule maker
    uses it. It adds state-b into state-a. First:
    - The two states' info are added using the
      overridable *add-info* function,
      forming a new state.
    - The remainder of the new state is changed
      to state-a's remainder with the
      first few tokens dropped off. The number
      of tokens dropped is the 
    - The index of the new state is changed to
      the sum of the indexes of state-a and
      state-b."
    [state-a state-b]
    (let [index-b (fetch-index state-b)]
      (-> state-a
        (*add-info* state-b)
        (assoc-remainder (drop index-b (*remainder-accessor* state-a)))
        (set-index (+ (fetch-index state-a) index-b)))))
  (let [state-a (-> '[a b c d] make-state (set-index 4))
        state-b (-> nil make-state (set-index 2))
        summed-state (add-states state-a state-b)]
    (-> '[c d] make-state (= summed-state) is)
    (-> summed-state fetch-index (= 6) is)))

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
  (defvar get-remainder
    (fetch-val *remainder-accessor*)
    "A rule that consumes no tokens. Its
    product is the sequence of the remaining
    tokens.
    [Equivalent to the result of
    (fetch-val *remainder-accessor*) from
    clojure.contrib.monads.]")
  (is (= ((complex [remainder get-remainder] remainder)
          (make-state ["hi" "THEN"]))
         [["hi" "THEN"] (make-state ["hi" "THEN"])])))

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
  (is (= (-> [\a] make-state (assoc :column 3)
           ((update-info :column inc)))
         [3 (-> [\a] make-state (assoc :column 4))])))

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
  (is (= (emptiness (make-state '(A B C)))
         [nil (make-state '(A B C))])
      "emptiness rule matches emptiness"))

(with-test
  (defn anything
    "A rule that matches anything--that is, it matches
    the first token of the tokens it is given.
    This rule's product is the first token it receives.
    It fails if there are no tokens left."
    [state]
    (if-let [tokens (*remainder-accessor* state)]
      [(first tokens)
       (-> state (assoc-remainder (next tokens))
         (vary-index inc))]))
  (is (= (anything (make-state '(A B C)))
         ['A (make-state '(B C))])
    "anything rule matches first token")
  (is (= (anything (make-state '(A B C)))
         ['A (make-state '(B C))])
    "anything rule matches first token without index")
  (is (-> '(A B C) make-state anything second meta ::index (= 1)))
  (is (-> '(A B C) make-state (vary-meta assoc ::index 5)
        anything second meta ::index (= 6)))
  (is (nil? (anything (make-state nil)))
    "anything rule fails with no tokens left")
  (is (= ((rep* anything) (make-state '(A B C)))
         ['(A B C) (make-state nil)])
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
  (is (= ((validate (lit "hi") (partial = "hi")) (make-state ["hi" "THEN"]))
         ["hi" (make-state (list "THEN"))])
      "created validator rule succeeds when given subrule and validator succeed")
  (is (nil? ((validate (lit "hi") (partial = "RST")) (make-state ["RST"])))
      "created validator rule fails when given subrule fails")
  (is (nil? ((validate (lit "hi") (partial = "hi")) (make-state "hi")))
      "created validator rule fails when given validator fails"))

(with-test
  (defvar term
    (partial validate anything)
    "Equivalent to (partial validate anything).
    Creates a rule that is a terminal rule of the given validator--that is, it
    accepts only tokens for whom (validator token) is true.
    (def a (term validator)) would be equivalent to the EBNF
      a = ? (validator %) evaluates to true ?;
    The new rule's product would be the first token, if it fulfills the
    validator.")
  (let [rule (term (partial = 'A))]
    (is (= (rule (make-state '[A B])) ['A (make-state '[B])])
      "created terminal rule works when first token fulfills validator")
    (is (nil? (rule (make-state '[B B])))
      "created terminal rule fails when first token fails validator")
    (is (= (rule (make-state '[A])) ['A (make-state nil)])
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
  (is (= ((lit 'A) (make-state '[A B]))
         ['A (make-state '[B])])
      "created literal rule works when literal token present")
  (is (nil? ((lit 'A) (make-state '[B])))
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
  (is (= ((re-term #"\s*true\s*") (make-state ["  true" "THEN"]))
         ["  true" (make-state ["THEN"])])
      "created re-term rule works when first token matches regex")
  (is (nil? ((re-term #"\s*true\s*") (make-state ["false" "THEN"])))
      "created re-term rule fails when first token does not match regex")
  (is (nil? ((re-term #"\s*true\s*") (make-state nil)))
      "created re-term rule fails when no tokens are left"))

(deftest complex-test
  (let [rule1 (complex [a (lit 'A)] (str a "!"))
        rule2 (complex [a (lit 'A), b (lit 'B)] (str a "!" b))]
    (is (= (rule1 (make-state '[A B])) ["A!" (make-state '[B])])
      "created complex rule applies semantic hook to valid subresult")
    (is (nil? (rule1 (make-state '[B A])))
      "created complex rule fails when a given subrule fails")
    (is (= (rule2 (make-state '[A B C])) ["A!B" (make-state '[C])])
      "created complex rule succeeds when all subrules fulfilled in order")
    (is (nil? (rule2 (make-state '[A C])))
      "created complex rule fails when one subrule fails")))

(with-test
  (defn followed-by
    "Creates a rule that does not consume any tokens, but fails when the given
    subrule fails.
    The new rule's product would be the subrule's product."
    [subrule]
    (complex [state get-state, subproduct subrule, _ (set-state state)]
      subproduct))
  (is (= ((followed-by (lit 'A)) (make-state '[A B C]))
         ['A (make-state '[A B C])]))
  (is (nil? ((followed-by (lit 'A)) (make-state '[B C])))))

(with-test
  (defn not-followed-by
    "Creates a rule that does not consume any tokens, but fails when the given
    subrule succeeds. On success, the new rule's product is always true."
    [subrule]
    (fn [state]
      (if (nil? (subrule state))
        [true state])))
  (is (= ((not-followed-by (lit 'A)) (make-state '[B C]))
         [true (make-state '[B C])]))
  (is (nil? ((not-followed-by (lit 'A)) (make-state '[A B C])))))

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
  (is (= ((semantics (lit "hi") #(str % "!")) (make-state ["hi" "THEN"]))
         ["hi!" (make-state (list "THEN"))])
      "created simple semantic rule applies semantic hook to valid result of given rule"))

(defn constant-semantics
  "Creates a rule with a constant semantic
  hook. Its product is always the given
  constant."
  [subrule semantic-value]
  (complex [subproduct subrule]
    semantic-value))

(with-test
  (defvar remainder-peek
    (complex [remainder get-remainder]
      (first remainder))
    "A rule that does not consume any tokens. Its product is the very next
     token in the remainder.")
  (is (= (remainder-peek (make-state (seq "ABC")))
         [\A (make-state (seq "ABC"))])))

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

(deftest test-conc
  (is (= ((conc (lit "hi") (lit "THEN"))
          (make-state ["hi" "THEN" "bye"]))
         [["hi" "THEN"] (make-state (list "bye"))])
      "created concatenated rule succeeds when all subrules fulfilled in order")
  (is (= (-> ["hi" "THEN" "bye"] make-state
           ((conc (lit "hi") (lit "THEN")))
           second fetch-index)
         2)
      "created concatenated rule correctly deals with indexes")
  (is (nil? ((conc (lit "hi") (lit "THEN"))
             (make-state ["hi" "bye" "boom"])))
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

(deftest test-alt
  (is (= ((alt (lit "hi") (lit "THEN"))
          (make-state ["THEN" "bye"]))
         ["THEN" (make-state (list "bye"))]))
  (is (= (-> ["THEN" "bye"] make-state
           ((alt (lit "hi") (lit "THEN")))
           second fetch-index)
         1))
  (is (nil? ((alt (lit "hi") (lit "THEN"))
             (make-state ["bye" "boom"])))))

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
    (is (= (opt-true (make-state ["true" "THEN"]))
           ["true" (make-state (list "THEN"))])
        "created option rule works when symbol present")
    (is (= (opt-true (make-state (list "THEN")))
           [nil (make-state (list "THEN"))])
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

(deftest test-invisi-conc
  (is (= ((invisi-conc (lit \a) (update-info :column inc))
           (-> "abc" make-state (assoc :column 4)))
         [\a (-> "bc" seq make-state (assoc :column 5))])))

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
  (is (= ((lit-conc-seq "THEN") (make-state "THEN print 42;"))
         [(vec "THEN") (make-state (seq " print 42;"))])
      "created literal-sequence rule is based on sequence of given token sequencible")
  (is (= ((lit-conc-seq "THEN"
            (fn [lit-token]
              (invisi-conc (lit lit-token)
                (update-info :column inc))))
          (-> "THEN print 42;" make-state (assoc :column 1)))
         [(vec "THEN") (-> (seq " print 42;") make-state (assoc :column 5))])
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
  (is (= ((lit-alt-seq "ABCD") (make-state (seq "B 2")))
         [\B (make-state (seq " 2"))])
      (str "created literal-alternative-sequence rule "
           "works when literal symbol present in sequence"))
  (is (nil? ((lit-alt-seq "ABCD") (make-state (seq "E 2"))))
      (str "created literal-alternative-sequence "
           "rule fails when literal symbol not "
           "present in sequence"))
  (is (= ((lit-alt-seq "ABCD"
            (fn [lit-token]
              (invisi-conc (lit lit-token)
                           (update-info :column inc))))
          (-> "B 2" make-state (assoc :column 1)))
         [\B (-> (seq " 2") make-state (assoc :column 2))])
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
          (if (seq (*remainder-accessor* substate))
            (recur (conj cur-product subproduct) substate)
            [(conj cur-product subproduct) substate])
          [(if (not= cur-product []) cur-product) cur-state]))))
    ; The following code was used until I found
    ; that the mutually recursive calls to rep+
    ; resulted in an easily inflated function call stack.
  ;  (opt (rep+ subrule)))
  (let [rep*-true (rep* (lit true))
        rep*-untrue (rep* (except anything (lit true)))]
    (is (= (rep*-true (-> [true "THEN"] make-state (assoc :a 3)))
           [[true] (-> (list "THEN") make-state (assoc :a 3))])
        "created zero-or-more-repetition rule works when symbol present singularly")
    (is (= (rep*-true (-> [true true true "THEN"] make-state (assoc :a 3)))
           [[true true true] (-> (list "THEN") make-state (assoc :a 3))])
        "created zero-or-more-repetition rule works when symbol present multiply")
    (is (= (rep*-true (-> ["THEN"] make-state (assoc :a 3)))
           [nil (-> (list "THEN") make-state (assoc :a 3))])
     "created zero-or-more-repetition rule works when symbol absent")
    (is (= (rep*-true (make-state [true true true]))
           [[true true true] (make-state nil)])
        "created zero-or-more-repetition rule works with no remainder after symbols")
    (is (= (rep*-true (make-state nil))
           [nil (make-state nil)])
        "created zero-or-more-repetition rule works with no remainder")
    (is (= (rep*-untrue (make-state [false false]))
           [[false false] (make-state nil)])
        "created zero-or-more-repetition negative rule works consuming up to end")
    (is (= (rep*-untrue (make-state [false false true]))
           [[false false] (make-state [true])])
        "created zero-or-more-repetition negative rule works consuming until exception")
    (is (= (rep*-untrue (make-state nil))
           [nil (make-state nil)])
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
  ;  (complex [cur-remainder get-remainder
  ;            :when (seq cur-remainder)
  ;            first-subproduct subrule
  ;            rest-subproducts (rep* subrule)]
  ;    (cons first-subproduct rest-subproducts)))
  (let [rep+-true (rep+ (lit true))]
    (is (= (rep+-true (make-state [true "THEN"]))
           [[true] (make-state (list "THEN"))])
        "created one-or-more-repetition rule works when symbol present singularly")
    (is (= (rep+-true (make-state [true true true "THEN"]))
           [[true true true] (make-state (list "THEN"))])
        "created one-or-more-repetition rule works when symbol present multiply")
    (is (nil? (rep+-true (make-state (list "THEN"))))
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
    (is (= (-> "ABC" make-state (assoc :a 1) except-rule)
            [\A (-> (seq "BC") make-state (assoc :a 1))])
        "created exception rule works when symbol is not one of the syntatic exceptions")
    (is (nil? (except-rule (make-state (seq "BAC"))))
        "created exception rule fails when symbol is one of the syntactic exceptions")
    (is (nil? (except-rule (make-state (seq "DAB"))))
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
    (is (= (tested-rule-fn (make-state (list "A" "A" "C")))
           [["A" "A"] (make-state (list "C"))])
        "created rep rule works when predicate returns true")
    (is (nil? (tested-rule-fn (make-state (list "A" "A" "A"))))
        "created rep rule fails when predicate returns false")
    (is (= (tested-rule-fn (make-state (list "D" "A" "B")))
           [nil (make-state (list "D" "A" "B"))])
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
    (is (= (tested-rule-3 (make-state (list "A" "A" "A" "A" "C")))
           [["A" "A" "A"] (make-state (list "A" "C"))])
        (str "created factor= rule works when symbol fulfills all subrule multiples and"
             "leaves strict remainder"))
    (is (= (tested-rule-3 (make-state (list "A" "A" "A" "C")))
           [["A" "A" "A"] (make-state (list "C"))])
        "created factor= rule works when symbol fulfills all subrule multiples only")
    (is (= (tested-rule-3 (make-state (list "A" "A" "C"))) nil)
        "created factor= rule fails when symbol does not fulfill all subrule multiples")
    (is (= (tested-rule-3 (make-state (list "D" "A" "B"))) nil)
        "created factor= rule fails when symbol does not fulfill subrule at all")
    (is (= (tested-rule-0 (make-state (list "D" "A" "B")))
           [[] (make-state (list "D" "A" "B"))])
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
    (is (= (tested-rule (make-state (seq "AAAAC")))
           [[\A \A] (make-state (seq "AAC"))])
        (str "created factor< rule works when symbol fulfills all subrule multiples and"
             "leaves strict remainder"))
    (is (= (tested-rule (make-state (seq "AAAC")))
           [[\A \A] (make-state (seq "AC"))])
        "created factor< rule works when symbol fulfills all subrule multiples only")
    (is (= (tested-rule (make-state (seq "AAC"))) [[\A \A] (make-state (seq "C"))])
        "created factor< rule works when symbol does not fulfill all subrule multiples")
    (is (= (tested-rule (make-state (seq "DAB")))
           [nil (make-state (seq "DAB"))])
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
        (failure-hook (*remainder-accessor* state) state))))
  (let [exception-rule (failpoint (lit "A")
                          (fn [remainder state]
                            (throw-arg "ERROR %s at line %s"
                              (first remainder) (:line state))))]
    (is (= (exception-rule (-> ["A"] make-state (assoc :line 3)))
           ["A" (-> nil make-state (assoc :line 3))])
        "failing rules succeed when their subrules are fulfilled")
    (is (thrown-with-msg? IllegalArgumentException
          #"ERROR B at line 3"
          (exception-rule (-> ["B"] make-state (assoc :line 3)))
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
             (is (= (rule (-> ["A" "B"] make-state (assoc :line 3)))
                    ["A" (-> (list "B") make-state (assoc :line 3))])
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
    (is (= (intercept-rule (make-state "ABC")) :error))))

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
  (complex [subproduct subrule, substate get-state, :when (validator substate)]
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
  (complex [subproduct subrule, subremainder get-remainder, :when (validator subremainder)]
    subproduct))

(with-test
  (defmacro state-context
    "Puts all Clojure forms inside into a state context.
    This is for customization of states, which affect
    make-state and all rules within the context.
    
    You customize by providing as a template a map of
    your states' desired keys and their default values.
    
    In addition, you get a speed boost from the automatic
    generation and use of a struct map and accessors, which
    are invisibly used by make-state and all rules.
    
    This form uses the binding form, so the context formed
    is thread-specific.
    
    You can (and must, if you use things like memoizing
    rules) provide a special info addition recipe in the
    template with the key :name.choi.joshua.fnparse/add-info.
    Corresponding to it would be a two-argument function that
    merges its second argument (a state) into the first
    argument (another state). This is important. It is
    essential if you use the memo rule-maker. Read the example
    below to learn how to implement a proper add-info.
    
    Here is an example to make it clearer how you
    customize states. Let's say that I want my states to
    store: (1) any warnings that a rule might want to raise
    for the user during parsing, (2) the current line number,
    and (3) the current column number. Also, whenever two
    states are merged, I want to do it in a particular way.
    I want the warnings to simply be merged together. Also, I
    want the new state's line and column to similarly be
    the sum of the lines and column of the two states.
    
    But! if the line of the second state's column is above zero,
    then that means that merging the second state into the
    first state should RESET the new column number, since the
    new state is at a new line, a different line from the first
    state! Here's the code...
    
    (use 'name.choi.joshua.fnparse)
    (require '[name.choi.joshua.fnparse :as p])
      ; Did you know that you can shorten double-colon-ed
      ; namespace-qualified keywords using the namespaces'
      ; abbreviations from require? It's true! Thanks to
      ; the above require form, the ::p/remainder keyword
      ; is equivalent to :name.choi.joshua.fnparse/remainder!
    
    (defn add-info [s0 s1]
      (let [new-warnings (into (:warnings s0) (:warnings s1))
            s1-line (s1 :line)
            s1-column (s1 :column)
            new-line (+ (s0 :line) s1-line)
            new-column (if (pos? s1-line)
                         s1-column
                         (+ (s0 :column) s1-column))]
       (new-info
         :warnings new-warnings
         :line new-line
         :column new-column)))
    
    (state-context
      {:warnings []
       :line 0
       :column 0
       ::p/add-info add-info}
      ; Define your rules and create states inside the context.
      (def line-break
        (invisi-conc (lit \\newline)
          (update-info :line inc)
          (set-info :column 0)))
      (defn add-warning [line column]
        (update-info :warnings
          #(conj % (format \"Z FOUND AT line %s, col %s!\"
                     line column))))
      (def illegal-z
        (complex [z (lit \\z)
                  line (get-info :line)
                  column (get-info :column)
                  _ (add-warning line column)]
          \"WRONG\"))
      (def non-break
        (invisi-conc (alt illegal-z (except line-break))
          (update-info :column inc)))
      (def text
        (-> (alt line-break non-break) rep+ mem))
      (def a-state (make-state \"ABZ\\nC\"))
        ; Returns
        ; {::p/remainder \"ABZ\\nC\"
        ;  :line 1
        ;  :column 1
        ;  :warnings []}
      (text a-state)
        ; Returns
        ; [(\\A \\B \"WRONG\" \\newline \\C)
        ;  {::p/remainder nil
        ;   :line 2
        ;   :column 1
        ;   :warnings [\"Z FOUND AT line 1, column 3\"]}])"
    [state-template & forms]
    `(let [default-state#
            (dissoc ~state-template ::add-info)
          struct-keys#
            (cons ::remainder (keys default-state#))
          add-info-fn#
            (::add-info ~state-template)
          state-struct#
            (apply create-struct struct-keys#)
          empty-state#
            (into (struct state-struct#) default-state#)
          remainder-accessor#
            (accessor state-struct# ::remainder)]
      (binding [*empty-state* empty-state#
                *remainder-accessor* remainder-accessor#
                *add-info* add-info-fn#]
        ~@forms))))

(deftest state-context-test
  (state-context {:warnings []}
    (is (= ((lit \a) (make-state "abc"))
           [\a (-> "bc" seq make-state (assoc :warnings []))]))
    (is (thrown? ClassCastException
          ((lit \a) {::remainder []}))))
  (state-context standard-template
    (is (= {::remainder "ABZ\nC"
            :line 0
            :column 0
            :warnings []}
           (make-state "ABZ\nC")))
    (is (= (assoc (make-state (seq "D"))
             :line 1
             :column 1
             :warnings ["I'm a warning!"])
           (add-states
             (assoc (make-state "\nCD")
               :line 0
               :column 3
               :warnings [])
             (assoc (set-index (make-state nil) 2)
               :line 1
               :column 1
               :warnings ["I'm a warning!"]))))))

(with-test
  (defn match-rule
    "Creates a function that tries to completely
    match the given rule to the given tokens,
    with no remainder left over after the match.
    - If (-> tokens make-state rule) fails, then
      (failure-fn given-state) is called.
    - If the remainder of (-> tokens make-state rule)
      is not empty, then...
        (incomplete-fn
          product-from-consumed-tokens
          new-state-after-rule
          initial-state)
      ...is called.
    - If the new remainder is empty, then the
      product of the rule is returned."
    [rule failure-fn incomplete-fn tokens]
    (let [state-0 (make-state tokens)]
      (if-let [[product state-1] (rule state-0)]
        (if (empty? (*remainder-accessor* state-1))
          product
          (incomplete-fn product state-1 state-0))
        (failure-fn state-0))))
  (let [rule (lit "A")
        matcher (partial match-rule rule identity vector)]
    (is (= (matcher ["A"]) "A"))
    (is (= (matcher ["B"]) (make-state ["B"])))
    (is (= (matcher ["A" "B"])
           ["A" (make-state ["B"]) (make-state ["A" "B"])]))))

(defn- starts-with? [subject-seq query-seq]
  (every? identity (map = subject-seq query-seq)))

(with-test
  (defn- find-mem-result [memory-map query-key]
    (if-let [candidates (seq (filter #(starts-with? (key %) query-key)
                               memory-map))]
      (if (> (count candidates) 1)
        ; Just in case more than one entry is found, which isn't supposed to
        ; happen
        (raise fnparse-error
          "found more than one entry that matches the token remainder %s: %s"
          query-key candidates)
        (val (first candidates)))))
  (let [remainder-1 '[a b c d]
        remainder-2 '[d e f]
        remainder-3 '[a c b d]
        memory {'[a b] 'dummy-1
                '[d e f] 'dummy-2}]
    (is (= (find-mem-result memory remainder-1) 'dummy-1))
    (is (= (find-mem-result memory remainder-2) 'dummy-2))
    (is (= (find-mem-result memory remainder-3) nil))))

(with-test
  (defn mem
    "Creates a memoizing rule that caches
    its subrule's results in an atom.
    Whenever the new mem rule is called,
    it checks the cache to see if there is an
    existing match; otherwise, the subrule is called.
  
    If you use a customized state context,
    mem requires that you implement a
    ::fnparse/add-info function in your
    state template. See state-context's docs
    for information on how to do that."
    [subrule]
    (let [memory (atom {})]
      (fn [state-0]
        (let [remainder-0 (*remainder-accessor* state-0)
              index-0 (fetch-index state-0)]
          (if-let [found-result (find-mem-result @memory remainder-0)]
            (let [found-product (found-result 0)
                  found-state (found-result 1)
                  found-state-index (fetch-index found-state)
                  new-remainder (drop found-state-index remainder-0)
                  new-state (-> state-0
                              (add-states found-state)
                              (assoc-remainder new-remainder)
                              (vary-index (+ index-0 found-state-index)))]
              ; (println "> memory found" [found-product found-state])
              [found-product new-state])
            (if-let [subresult (subrule (make-state remainder-0))]
              (let [subproduct (subresult 0)
                    substate (subresult 1)
                    subremainder (*remainder-accessor* substate)
                    subindex (fetch-index substate)
                    consumed-tokens (take subindex remainder-0)
                    mem-state (assoc-remainder substate nil)
                    returned-state (add-states state-0 mem-state)]
                ; (println "> memory registered" consumed-tokens [consumed-tokens mem-state])
                (swap! memory assoc consumed-tokens [subproduct mem-state])
                ; (println "> memory " memory)
                [subproduct returned-state])))))))
  (let [rule (mem (alt (conc (lit 'a) (lit 'b)) (lit 'c)))]
    (is (= (rule (make-state '[a b c]))
           ['[a b] (make-state '[c])]))))
;     (is (= (rule (make-state '[a b c])) ['[a b] (make-state '[c])]))
;     (is (= (rule (make-state '[c s a])) ['c (make-state '[s a])]))
;     (is (= (rule (make-state '[c])) ['c (make-state [])]))
;     (is (nil? (rule (make-state '[s a]))))
;     (is (nil? (rule (make-state '[s a]))))))

(defn- merge-standard-info
  "The standard-template needs special
  behavior for merging its states. Firstly,
  warnings are always just merged into each
  other; it's commutative.
  However, line and column numbers are
  different. If you add a state with a line
  of 0: in other words, "
  [s0 s1]
  (let [new-warnings (into (:warnings s0) (:warnings s1))
        s1-line (s1 :line)
        s1-column (s1 :column)
        new-line (+ (s0 :line) s1-line)
        new-column (if (pos? s1-line)
                     s1-column
                     (+ (s0 :column) s1-column))]
   (new-info
     :warnings new-warnings
     :line new-line
     :column new-column)))

(defvar standard-template
  {:warnings []
   :line 0
   :column 0
   ::add-info merge-standard-info})

(defn inc-column
  "Meant to be used only with standard-bundle states, or other states with an
  integer :column val.

  Creates a new rule that calls the subrule, and then increments the column.
  Meant to be called on literal rules of one non-break character."
  [subrule]
  (invisi-conc subrule (update-info :column inc)))

(defn inc-line
  "Meant to be used only with standard-bundle states, or other states with an
  integer :column val and an integer :line val.

  Creates a new rule that calls the subrule, and then increments the line and
  sets the column to zero."
  [subrule]
  (invisi-conc subrule
    (update-info :line inc) (set-info :column 0)))
