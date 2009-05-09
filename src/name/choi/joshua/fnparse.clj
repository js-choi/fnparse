(ns name.choi.joshua.fnparse
  (:use clojure.contrib.monads clojure.contrib.except))

; A rule is a delay object that contains a function that:
; - Takes a collection of tokens.
; - If the token sequence is valid, it returns a (0) vector containing the (1) consumed
;   symbols' products and (2) a state data object, usually a map. The state contains the (3)
;   sequence of remaining tokens, usually with the key *remainder-accessor*.
; - If the given token sequence is invalid and the rule fails, it simply returns nil.

; - (0) is called the rule's result.
; - (1) is called the rule's product.
; - (2) is called the rule's state.
; - (3) is called the rule's remainder.

(def *remainder-accessor* :remainder)

(def parser-m (state-t maybe-m))

(defmacro complex
  [steps & product-expr]
  `(domonad parser-m ~steps ~@product-expr))

(with-monad parser-m

  (def
    #^{:doc "A rule that consumes no tokens. Its product is the entire current state.
       [Equivalent to the result of fetch-state from clojure.contrib.monads.]"}
    get-state (fetch-state))
  (defn get-info
    "Creates a rule that consumes no tokens. The new rule's product is the value of the given 
    key in the current state.
    [Equivalent to fetch-val from clojure.contrib.monads.]"
    [key]
    (fetch-val key))
  (def
    #^{:doc "A rule that consumes no tokens. Its product is the sequence of the remaining
       tokens.
       (Equivalent to the result of (fetch-val *remainder-accessor*) from clojure.contrib.monads.)"}
    get-remainder (fetch-val *remainder-accessor*))
  (defn set-info
    "Creates a rule that consumes no tokens. The new rule directly changes the current state
    by associating the given key with the given value. The product is nil.
    
    [Equivalent to set-val from clojure.contrib.monads.]"
    [key value]
    (set-val key value))
  (defn update-info
    "Creates a rule that consumes no tokens. The new rule changes the current state by
    associating the given key with the evaluated result of applying the given updating
    function to the key's current value. The product is nil.
    [Equivalent to update-val from clojure.contrib.monads.]"
    [key val-update-fn]
    (update-val key val-update-fn))

  (def
    #^{:doc "A rule that matches emptiness--that is, it always matches with every given token
       sequence, and it always returns [nil tokens].
       (def a emptiness) would be equivalent to the EBNF a = ;
       This rule's product is always nil, and it therefore always returns [nil tokens]."}
    emptiness (m-result nil))

  (defn anything
    "A rule that matches anything--that is, it matches the first token of the tokens it is
    given.
    This rule's product is the first token it receives."
    [{tokens *remainder-accessor*, :as state}]
    [(first tokens) (assoc state *remainder-accessor* (next tokens))])
  
  (defn validate
    "Creates a rule from attaching a product-validating function to the given subrule--that
    is, any products of the subrule must fulfill the validator function.
    (def a (validate b validator)) says that the rule a succeeds only when b succeeds and
    also when the evaluated value of (validator b-product) is true. The new rule's product 
    would be b-product."
    [subrule validator]
    (complex [subproduct subrule, :when (validator subproduct)]
      subproduct))
  
  (defn term
    "Creates a rule that is a terminal rule of the given validator--that is, it accepts only
    tokens for whom (validator token) is true.
    (def a (term validator)) would be equivalent to the EBNF
      a = ? (validator %) evaluates to true ?;
    The new rule's product would be the first token, if it fulfills the validator."
    [validator]
    (validate anything validator))
  
  (defn lit
    "Creates a rule that is the terminal rule of the given literal token--that is, it accepts 
    only tokens that are equal to the given literal token.
    (def a (lit \"...\")) would be equivalent to the EBNF
      a = \"...\";
    The new rule's product would be the first token, if it equals the given literal token."
    [literal-token]
    (term (partial = literal-token)))
  
  (defn re-term
    "Creates a rule that is the terminal rule of the given regex--that is, it accepts only 
    tokens that match the given regex.
    (def a (re-term #\"...\")) would be equivalent to the EBNF
      a = ? (re-matches #\"...\" %) evaluates to true ?;
    The new rule's product would be the first token, if it matches the given regex."
    [token-re]
    (term (partial re-matches token-re)))
  
  (defn followed-by
    "Creates a rule that does not consume any tokens, but fails when the given subrule fails.
    The new rule's product would be the subrule's product."
    [subrule]
    (complex [state get-state, subproduct subrule, _ (set-state state)]
      subproduct))
  
  (defn not-followed-by
    "Creates a rule that does not consume any tokens, but fails when the given subrule
    succeeds. On success, the new rule's product is always true."
    [subrule]
    (fn [state]
      (if (nil? (subrule state))
        [true state])))
  
  (defn semantics
    "Creates a rule with a semantic hook: basically a simple version of a complex rule. The
    semantic hook is a function that takes one argument: the product of the subrule."
    [subrule semantic-hook]
    (complex [subproduct subrule]
      (semantic-hook subproduct)))
  
  (defn constant-semantics
    "Creates a rule with a constant semantic hook. Its product is always the given constant."
    [subrule semantic-value]
    (complex [subproduct subrule]
      semantic-value))

  (def
    #^{:doc "A rule that does not consume any tokens. Its product is the very next token in 
       the remainder."}
    remainder-peek
    (complex [remainder get-remainder]
      (first remainder)))

  (defn conc
    "Creates a rule that is the concatenation of the given subrules. Basically a simple
    version of complex, each subrule consumes tokens in order, and if any fail, the entire
    rule fails.
    (def a (conc b c d)) would be equivalent to the EBNF:
      a = b, c, d;
    This function is equivalent to m-seq for the parser-m monad."
    [& subrules]
    (m-seq subrules))

  (def
    #^{:doc "Creates a rule that is the alternation of the given subrules. It succeeds when
       any of its subrules succeed, and fails when none do. Its result is that of the first
       subrule that succeeds, so the order of the subrules that this function receives
       matters.
       (def a (alt b c d)) would be equivalent to the EBNF:
         a = b | c | d;
       This function is equivalent to m-plus for the parser-m monad."}
    alt m-plus)

  (defn opt
    "Creates a rule that is the optional form of the subrule. It always succeeds. Its result
    is either the subrule's (if the subrule succeeds), or else its product is nil, and the
    rule acts as the emptiness rule.
    (def a (opt b)) would be equivalent to the EBNF:
      a = b?;"
    [subrule]
    (m-plus subrule emptiness))
  
  (defn lit-conc-seq
    "A convenience function: it creates a rule that is the concatenation of the literals
    formed from the given sequence of literal tokens.
    (def a (lit-conc-seq [\"a\" \"b\" \"c\"])) would be equivalent to the EBNF:
      a = \"a\", \"b\", \"c\";"
    [token-seq]
    (m-seq (map lit token-seq)))
  
  (defn lit-alt-seq
    "A convenience function: it creates a rule that is the alternation of the literals
    formed from the given sequence of literal tokens.
    (def a (lit-alt-seq [\"a\" \"b\" \"c\"])) would be equivalent to the EBNF:
      a = \"a\" | \"b\" | \"c\";"
    [token-seq]
    (apply alt (map lit token-seq)))
  
  (declare rep+)
  
  (defn rep*
    "Creates a rule that is the zero-or-more greedy repetition of the given subrule. It
    always succeeds. It consumes tokens with its subrule until its subrule fails.
    Its result is the sequence of results from the subrule's repetitions, (or nil if the
    subrule fails immediately).
    (def a (rep* b)) is equivalent to the EBNF:
      a = {b};
    The new rule's products would be either the vector [b-product ...] for how many matches
    of b were found, or nil if there was no match. (Note that this means that, in the latter
    case, the result would be [nil given-state].) The new rule can never simply return nil."
    [subrule]
    (opt (rep+ subrule)))
  
  (defn rep+
    "Creates a rule that is the zero-or-more greedy repetition of the given subrule. It
    fails only when its subrule fails immediately. It consumes tokens with its subrule until
    its subrule fails. Its result is the sequence of results from the subrule's repetitions.
    (def a (rep* b)) is equivalent to the EBNF:
      a = {b}-;
    The new rule's products would be either the vector [b-product ...] for how many matches
    of b were found. If there was no match, then nil is simply returned."
    [subrule]
    (complex [first-subproduct subrule
              next-token remainder-peek
              rest-subproducts (rep* subrule)]
      (cons first-subproduct rest-subproducts)))

  (defn except
    "Creates a rule that is the exception from the first given subrules with the second given
    subrule--that is, it accepts only tokens that fulfill the first subrule but fails the
    second of the subrules.
    (def a (except b c)) would be equivalent to the EBNF
      a = b - c;
    The new rule's products would be b-product. If b fails or c succeeds, then nil is simply
    returned."
    [minuend subtrahend]
    (complex [state (fetch-state)
              minuend-product minuend
              :when (not (subtrahend state))]
      minuend-product))
  
  (defn rep-predicate
    "Like the rep* function, only that the number of times that the subrule is fulfilled must
    fulfill the given factor-predicate function."
    [factor-predicate subrule]
    (validate (rep* subrule) (comp factor-predicate count)))
  
  (defn rep=
    "Creates a rule that is the greedy repetition of the given subrule by the given factor (a
    positive integer)--that is, it eats up all the tokens that fulfill the subrule, and it
    then succeeds only if the number of times the subrule was fulfilled is equal to the
    given factor, no more and no less.
    (rep= 3 :a) would eat the first three tokens of [:a :a :a :b] and return:
      [[:a :a :a] (list :a :b)].
    (rep= 3 :a) would eat the first four tokens of [:a :a :a :a :b] and fail."
    [factor subrule]
    (rep-predicate (partial = factor) subrule))
  
  (defn rep<
    "A similiar function to rep=, only that the instead the new rule succeeds if the number
    of times that the subrule is fulfilled is less than and not equal to the given factor."
    [factor subrule]
    (rep-predicate (partial > factor) subrule))
  
  (defn rep<=
    "A similiar function to rep=, only that the instead the new rule succeeds if the number
    of times that the subrule is fulfilled is less than or equal to the given factor."
    [factor subrule]
    (rep-predicate (partial >= factor) subrule))
  
  (defn factor=
    "Creates a rule that is the syntactic factor (that is, a non-greedy repetition) of the
    given subrule by a given integer--that is, it is equivalent to the subrule replicated by
    1, 2, etc. times and then concatenated.
    (def a (factor= n b)) would be equivalent to the EBNF
      a = n * b;
    The new rule's products would be b-product. If b fails below n times, then nil is simply
    returned.
    (factor= 3 :a) would eat the first three tokens [:a :a :a :a :b] and return:
      [[:a :a :a] (list :a :b)].
    (factor= 3 :a) would eat the first three tokens [:a :a :b] and fail."
    [factor subrule]
    (apply conc (replicate factor subrule)))
  
  (defn factor<
    "Same as the factor= function, except that the new rule eats up tokens only until the
    given subrule is fulfilled one less times than the factor. The new rule would never fail.
    (factor< 3 :a) would eat the first two tokens [:a :a :a :a :b] and return:
      [[:a :a] (list :a :a :b)].
    (factor< 3 :a) would eat the first three tokens [:b] and return:
      [nil (list :b)]"
    [factor subrule]
    (alt (factor= (dec factor) subrule) (rep< factor subrule)))
  
  (defn factor<=
    "Same as the factor= function, except that the new rule always succeeds, consuming tokens
    until the subrule is fulfilled the same amount of times as the given factor. The new rule
    would never fail.
    (factor<= 3 :a) would eat the first two tokens [:a :a :a :a :b] and return:
      [[:a :a :a] (list :a :b)].
    (factor<= 3 :a) would eat the first three tokens [:b] and return:
      [nil (list :b)]"
    [factor subrule]
    (alt (factor= factor subrule) (rep< factor subrule)))
  
  (defn failpoint
    "Creates a rule that applies a failpoint to a subrule. When the subrule fails—i.e., it
    returns nil—then the failure hook function is called with one argument, the state at time
    of failure."
    [subrule failure-hook]
    (fn [state]
      (if-let [result (subrule state)]
        result
        (failure-hook state))))
  
  (defn effects
    "Creates a rule that calls a function for side effects. It does not consume any tokens
    or modify the state in any other way."
    [effect-hook]
    (fn [state]
      [(effect-hook state) state]))
    
)
