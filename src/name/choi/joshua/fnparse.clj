(ns name.choi.joshua.fnparse
  (:use clojure.contrib.monads clojure.contrib.except))

; A rule is a delay object that contains a function that:
; - Takes a collection of tokens.
; - If the token sequence is valid, it returns a vector containing the (0) consumed symbols'
;   products and (1) a sequence of the remaining symbols or nil. In all documentation here,
;   "a rule's products" is the first element of a valid result from the rule.
; - If the given token sequence is invalid and the rule fails, it simply returns nil.

; A "deepener" is my pet term for the functions that are called to get deeper into a monad:
; (m-bind value deepener)

;(def parser-m (maybe-t state-m))
(def parser-m (state-t maybe-m))

(defmacro complex
  [steps & product-expr]
  `(domonad parser-m ~steps ~@product-expr))

(with-monad parser-m

  (def get-state (fetch-state))
  (def get-remainder (fetch-val :remainder))
  (def get-info fetch-val)

  (def emptiness (m-result nil))

  (defn anything [{tokens :remainder, :as state}]
    [(first tokens) (assoc state :remainder (next tokens))])
  
  (defn validate
    "Creates a rule from attaching a product-validating function to the given subrule--that
    is, any products of the subrule must fulfill the validator function.
    (def a (validate b validator)) says that the rule a succeeds only when b succeeds and
    when (validator b-product) is true. The new rule's product would be b-product. If b fails
    or (validator b-product) is false, then nil is simply returned."
    [subrule validator]
    (complex [subproduct subrule, :when (validator subproduct)]
      subproduct))
  
  (defn term
    "Creates a rule metafunction that is a terminal rule of the given validator--that is, it
    accepts only tokens for whom (validator token) is true.
    (def a (term validator)) would be equivalent to the EBNF
      a = ? (validator %) evaluates to true ?;
    The new rule's product would be the first token, if it fulfills the validator.
    If the token does not fulfill the validator, the new rule simply returns nil."
    [validator]
    (validate anything validator))
  
  (defn lit
    "Creates a rule metafunction that is the terminal rule of the given literal token--that
    is, it accepts only tokens that are equal to the given literal token.
    (def a (lit \"...\")) would be equivalent to the EBNF
      a = \"...\";
    The new rule's product would be the first token, if it equals the given literal token.
    If the token does not equal the given literal token, the new rule simply returns nil."
    [literal-token]
    (term (partial = literal-token)))
  
  (defn re-term
    "Creates a rule metafunction that is the terminal rule of the given regex--that is, it
    accepts only tokens that match the given regex.
    (def a (re-term #\"...\")) would be equivalent to the EBNF
      a = ? (re-matches #\"...\" %) evaluates to true ?;
    The new rule's product would be the first token, if it matches the given regex.
    If the token does not match the given regex, the new rule simply returns nil."
    [token-re]
    (term (partial re-matches token-re)))
  
  (defn followed-by
    [subrule]
    (complex [state get-state, subproduct subrule, _ (set-state state)]
      subproduct))
  
  (defn not-followed-by
    [subrule]
    (fn [state]
      (if (nil? (subrule state))
        [true state])))
  
  (defn semantics
    [subrule semantic-hook]
    (complex [subproduct subrule]
      (semantic-hook subproduct)))
  
  (defn constant-semantics
    [subrule semantic-value]
    (complex [subproduct subrule]
      semantic-value))

  (def remainder-peek
    (complex [remainder get-remainder]
      (first remainder)))

  (defn conc [& subrules]
    (m-seq subrules))

  (def alt m-plus)

  (defn opt
    [subrule]
    (m-plus subrule emptiness))
  
  (defn lit-conc-seq
    [token-seq]
    (m-seq (map lit token-seq)))
  
  (defn lit-alt-seq
    [token-seq]
    (apply alt (map lit token-seq)))
  
  (declare rep+)
  
  (defn rep*
    [subrule]
    (opt (rep+ subrule)))
  
  (defn rep+
    [subrule]
    (complex [first-subproduct subrule
              next-token remainder-peek
              rest-subproducts (rep* subrule)]
      (cons first-subproduct rest-subproducts)))

  (defn except
    "Creates a rule metafunction that is the exception from the first given subrules with the
    rest of the given subrules--that is, it accepts only tokens that fulfill the first
    subrule but fail the rest of the subrules.
    (def a (except b c d)) would be equivalent to the EBNF
      a = b - c - d;
    The new rule's products would be b-product. If b fails or either c or d succeeds, then
    nil is simply returned."
    [minuend subtrahend]
    (complex [state (fetch-state)
              minuend-product minuend
              :when (not (subtrahend state))]
      minuend-product))
  
  (defn rep-predicate
    [factor-predicate subrule]
    (validate (rep* subrule) (comp factor-predicate count)))
  
  (defn rep=
    "Creates a rule metafunction that is the greedy repetition of the given subrule by the
    given positive integer factor--that is, it accepts only a certain number of tokens that
    fulfill the subrule, no more and no less."
    [factor subrule]
    (rep-predicate (partial = factor) subrule))
  
  (defn rep<
    [factor subrule]
    (rep-predicate (partial > factor) subrule))
  
  (defn rep<=
    [factor subrule]
    (rep-predicate (partial >= factor) subrule))
  
  (defn factor=
    "Creates a rule metafunction that is the syntactic factor of the given subrule by a given
    integer--that is, it is equivalent to the subrule replicated by 1, 2, etc. times and
    then concatenated.
    (def a (factor= n b)) would be equivalent to the EBNF
      a = n * b;
    The new rule's products would be b-product. If b fails below n times, then nil is simply
    returned.
    (factor= 3 \"A\") would accept [\"A\" \"A\" \"A\" \"A\" \"B\"] and return
    [[\"A\" \"A\" \"A\"] (\"A\" \"B\")."
    [factor subrule]
    (apply conc (replicate factor subrule)))
  
  (defn factor<
    "Creates a rule metafunction that is the syntactic factor (a nongreedy repetition) of the
    given subrule by less than a given integer--that is, it accepts a certain number of
    tokens that fulfill the subrule that is less than a certain factor, and leaves the rest
    behind."
    [factor subrule]
    (alt (factor= (dec factor) subrule) (rep< factor subrule)))
  
  (defn factor<=
    "Creates a rule metafunction that is the syntactic factor (a nongreedy repetition) of the
    given subrule by a given integer or less--that is, it accepts a certain number of tokens
    that fulfill the subrule that is a certain factor or less, and leaves the rest behind."
    [factor subrule]
    (alt (factor= factor subrule) (rep< factor subrule)))
  
)

;(defn rep*
;  "Creates a rule metafunction that is the zero-or-more repetition of the given subrule-
;  that is, either zero or more of the subrule.
;  (def a (rep* b)) would be equivalent to the EBNF
;    a = {b};
;  The new rule's products would be either the vector [b-product ...] for how many matches
;  of b were found, or the empty vector [] if there was no match. Note that the latter
;  actually means that the new rule would then return the vector [[] tokens]. The new rule
;  can never simply return nil."
;  [subrule]
;  (fn [tokens info]
;    (loop [products [], token-queue (seq tokens), cur-info info]
;      (let [[subproduct subremainder subinfo :as subresult]
;            (subrule token-queue cur-info)]
;        (if (nil? subresult)
;          [products token-queue cur-info]
;          (if (nil? subremainder)
;             [(conj products subproduct) subremainder subinfo]
;            (recur (conj products subproduct) subremainder subinfo)))))))
;

;(defn validate-state
;  [subrule validator]
;  (complex [subproduct subrule, substate get-state, :when (validator state)] subproduct))
;
;(defn validate-remainder
;  [subrule validator]
;  (complex

;(defn- identity-of-first
;  "Returns its first argument."
;  [first-arg & rest-args]
;  first-arg)
;
;(defn term
;  "Creates a rule metafunction that is a terminal rule of the given validator--that is, it
;  accepts only tokens for whom (validator token) is true.
;  (def a (term validator)) would be equivalent to the EBNF
;    a = ? (validator %) evaluates to true ?;
;  The new rule's product would be the first token, if it fulfills the validator.
;  If the token does not fulfill the validator, the new rule simply returns nil."
;  [validator]
;    (fn [tokens info]
;      (let [first-token (first tokens)
;            remainder (next tokens)]
;        (when (validator first-token)
;          [first-token remainder info]))))
;
;(defn validate
;  "Creates a rule metafunction from attaching a product-validating function to the given
;  subrule--that is, any products of the subrule must fulfill the validator function.
;  (def a (validate b validator)) says that the rule a succeeds only when b succeeds and when
;  (validator b-product) is true. The new rule's product would be b-product. If b fails or
;  (validator b-product) is false, then nil is simply returned."
;  [subrule validator]
;  (fn [tokens info]
;    (let [[product :as result] (subrule tokens info)]
;      (when (and (not (nil? result)) (validator product))
;        result))))
;
;(defn validate-remainder
;  "Creates a rule metafunction from attaching a remainder-validating function to the given
;  subrule--that is, any tokens in the remainder of the subrule must fulfill the validator
;  function.
;  (def a (validate-remainder b validator)) says that the rule a succeeds only when b
;  succeeds and when (validator-remainder b-remainder) is true. The new rule's product would
;  be b-product. If b fails or (validator b-remainder b-info) is false, then nil is simply
;  returned."
;  [subrule validator]
;  (fn [tokens info]
;    (let [[_ remainder :as result] (subrule tokens info)]
;      (when (and (not (nil? result)) (validator remainder))
;        result))))
;
;(defn validate-info
;  "Creates a rule metafunction from attaching a info-validating function to the given
;  subrule--that is, any tokens in the remainder of the subrule must fulfill the validator
;  function.
;  (def a (validate-info b validator)) says that the rule a succeeds only when b succeeds and
;  when (validator b-info) is true. The new rule's product would be b-product. If b fails or
;  (validator b-info) is false, then nil is simply returned."
;  [subrule validator]
;  (fn [tokens info]
;    (let [[_ _ info :as result] (subrule tokens info)]
;      (when (and (not (nil? result)) (validator info))
;        result))))
;
;(defn validate-all
;  "Creates a rule metafunction from attaching a product/remainder/info-validating function
;  to the given subrule--that is, any tokens in the remainder of the subrule must fulfill the
;  validator function.
;  (def a (validate-remainder b validator)) says that the rule a succeeds only when b
;  succeeds and when (validator-remainder b-product b-remainder b-info) is true. The new
;  rule's product would be b-product. If b fails or (validator b-remainder b-info) is false,
;  then nil is simply returned."
;  [subrule validator]
;  (fn [tokens info]
;    (let [[product remainder info :as result] (subrule tokens info)]
;      (when (and (not (nil? result)) (validator product remainder info))
;        result))))
;
;(defn semantics
;  "Creates a rule metafunction from attaching a semantic hook function to the given subrule-
;  that is, its products are from applying the semantic hook to the subrule's products. When
;  the subrule fails and returns nil, the new rule will return nil."
;  [subrule semantic-hook]
;  (fn [tokens info]
;    (let [[subproduct remainder subinfo :as subresult] (subrule tokens info)]
;      (when-not (nil? subresult)
;        (let [semantic-product (semantic-hook subproduct)]
;          [semantic-product remainder subinfo])))))
;
;(defn constant-semantics
;  "Creates a rule metafunction from attaching a constant semantic hook function to the given
;  subrule--that is, its product is a constant value. When the subrule fails and returns nil,
;  the new rule will return nil."
;  [subrule semantic-value]
;  (semantics subrule (constantly semantic-value)))
;
;(defn semantics-with-info
;  "Exactly like the semantics function, only both the product and info are passed to the
;  semantics hook."
;  [subrule semantic-hook]
;  (fn [tokens info]
;    (let [[subproduct remainder subinfo :as subresult] (subrule tokens info)]
;      (when-not (nil? subresult)
;        (let [semantic-product (semantic-hook subproduct info)]
;          [semantic-product remainder subinfo])))))
;
;(defn lit
;  "Creates a rule metafunction that is the terminal rule of the given literal token--that
;  is, it accepts only tokens that are equal to the given literal token.
;  (def a (lit \"...\")) would be equivalent to the EBNF
;    a = \"...\";
;  The new rule's product would be the first token, if it equals the given literal token.
;  If the token does not equal the given literal token, the new rule simply returns nil."
;  ([literal-token]
;   (term #(= % literal-token)))
;  ([literal-token process-meta]
;   (term #(= % literal-token) process-meta)))
;
;(defn re-term
;  "Creates a rule metafunction that is the terminal rule of the given regex--that is, it
;  accepts only tokens that match the given regex.
;  (def a (re-term #\"...\")) would be equivalent to the EBNF
;    a = ? (re-matches #\"...\" %) evaluates to true ?;
;  The new rule's product would be the first token, if it matches the given regex.
;  If the token does not match the given regex, the new rule simply returns nil."
;  ([token-regex]
;   (term #(re-matches token-regex %)))
;  ([token-regex process-meta]
;   (term #(re-matches token-regex %) process-meta)))
;
;(defn conc-fn [subrules tokens info]
;  (loop [products [], token-queue tokens, rule-queue (seq subrules), curr-info info]
;    (if (nil? rule-queue),
;        [products token-queue curr-info]
;        (let [[subproduct subremainder subinfo :as subresult]
;              ((first rule-queue) token-queue curr-info)]
;          (when-not (nil? subresult)
;            (recur (conj products subproduct) subremainder
;                   (next rule-queue) subinfo))))))
;
;(defmacro conc
;  "Creates a rule metafunction that is the concatenation of the given subrules--that is,
;  each subrule followed by the next.
;  (def a (conc b c d)) would be equivalent to the EBNF
;    a = b, c, d;
;  The new rule's products would be the vector [b-product c-product d-product]. If any of
;  the subrules don't match in the right place, the new rule simply returns nil."
;  [& subrules]
;  `(fn [tokens# info#]
;     (conc-fn (lazy-seq [~@subrules]) tokens# info#)))
;
;(defn alt-fn [subrules tokens info]
;  (some #(% tokens info) subrules))
;
;(defmacro alt
;  "Creates a rule metafunction that is the alternative of the given subrules--that is, any
;  one of the given subrules. Note that the subrules' order matters: the very first rule that
;  accepts the given tokens will be selected.
;  (def a (alt b c d)) would be equivalent to the EBNF
;    a = b | c | d;
;  The new rule's product would be b-product, c-product, or d-product depending on which
;  of the rules first accepts the given tokens. If none of the subrules matches, the new rule
;  simply returns nil."
;  [& subrules]
;  `(fn [tokens# info#]
;     (alt-fn (lazy-seq [~@subrules]) tokens# info#)))
;
;(defn opt
;  "Creates a rule metafunction that is the optional form of the given subrule--that is,
;  either the presence of the absence of the subrule.
;  (def a (opt b)) would be equivalent to the EBNF
;    a = [b];
;  The new rule's product would be either b-product, if b accepts it, or else nil. Note
;  that the latter actually means that the new rule would then return the vector
;  [nil tokens]. The new rule can never simply return nil."
;  [subrule]
;  (fn [tokens info]
;    (or (subrule tokens info) [nil tokens info])))
;
;(defn rep*
;  "Creates a rule metafunction that is the zero-or-more repetition of the given subrule-
;  that is, either zero or more of the subrule.
;  (def a (rep* b)) would be equivalent to the EBNF
;    a = {b};
;  The new rule's products would be either the vector [b-product ...] for how many matches
;  of b were found, or the empty vector [] if there was no match. Note that the latter
;  actually means that the new rule would then return the vector [[] tokens]. The new rule
;  can never simply return nil."
;  [subrule]
;  (fn [tokens info]
;    (loop [products [], token-queue (seq tokens), cur-info info]
;      (let [[subproduct subremainder subinfo :as subresult]
;            (subrule token-queue cur-info)]
;        (if (nil? subresult)
;          [products token-queue cur-info]
;          (if (nil? subremainder)
;             [(conj products subproduct) subremainder subinfo]
;            (recur (conj products subproduct) subremainder subinfo)))))))
;
;(defn rep+
;  "Creates a rule metafunction that is the one-or-more repetition of the given rule--that
;  is, either one or more of the rule.
;  (def a (rep+ b)) would be equivalent to the EBNF
;    a = {b}-;
;  The new rule's products would be the vector [b-product ...] for how many matches of b
;  were found. If there were zero matches, then nil is simply returned."
;  [subrule]
;  (fn [tokens info]
;    (let [product ((rep* subrule) tokens info)]
;       (when-not (empty? (product 0))
;         product))))
;
;(defn except
;  "Creates a rule metafunction that is the exception from the first given subrules with the
;  rest of the given subrules--that is, it accepts only tokens that fulfill the first
;  subrule but fail the second subrule.
;  (def a (except b c d)) would be equivalent to the EBNF
;    a = b - c - d;
;  The new rule's products would be b-product. If b fails or either c or d succeeds, then
;  nil is simply returned."
;  [minuend & subtrahends]
;  (fn [tokens info]
;    (let [product (minuend tokens info)]
;      (when (and (not (nil? product)) (every? #(nil? (% tokens info)) subtrahends))
;        product))))
;
;(defn factor=
;  "Creates a rule metafunction that is the syntactic factor of the given subrule by a given
;  integer--that is, it is equivalent to the subrule replicated by 1, 2, etc. times and
;  then concatenated.
;  (def a (factor= n b)) would be equivalent to the EBNF
;    a = n * b;
;  The new rule's products would be b-product. If b fails below n times, then nil is simply
;  returned.
;  (factor= 3 \"A\") would accept [\"A\" \"A\" \"A\" \"A\" \"B\"] and return
;  [[\"A\" \"A\" \"A\"] (\"A\" \"B\")."
;  [factor subrule]
;  (fn [tokens info]
;    (conc-fn (replicate factor subrule) tokens info)))
; 
;(defn rep-predicate
;  "Creates a rule metafunction that is the greedy repetition of the given subrule whose valid
;  size is determined by a predicate."
;  [factor-predicate subrule]
;  (validate (rep* subrule) (comp factor-predicate count)))
; 
;(defn rep=
;  "Creates a rule metafunction that is the greedy repetition of the given subrule by the
;  given positive integer factor--that is, it accepts only a certain number of tokens that
;  fulfill the subrule, no more and no less."
;  [factor subrule]
;  (validate (rep* subrule) #(= (count %) factor)))
;
;(defn rep<
;  "Creates a rule metafunction that is the greedy repetition of the given subrule by less
;  than the given positive integer factor--that is, it accepts a certain range number of
;  tokens that fulfill the subrule, less than but not equal to the limiting factor.
;  The new rule's products would be b-product. If b fails below n times, then nil is simply
;  returned."
;  [limit subrule]
;  (validate (rep* subrule) #(< (count %) limit)))
;
;(defn rep<=
;  "Creates a rule metafunction that is the greedy repetition of the given subrule by the
;  given positive integer factor or less--that is, it accepts a certain range number of
;  tokens that fulfill the subrule, less than but not equal to the limiting factor.
;  The new rule's products would be b-product. If b fails below n times, then nil is simply
;  returned."
;  [limit subrule]
;  (validate (rep* subrule) #(<= (count %) limit)))
;
;(defn factor<
;  "Creates a rule metafunction that is the syntactic factor (a nongreedy repetition) of the
;  given subrule by less than a given integer--that is, it accepts a certain number of tokens
;  that fulfill the subrule that is less than a certain factor, and leaves the rest behind."
;  [factor subrule]
;  (alt (factor= (dec factor) subrule) (rep< factor subrule)))
;
;(defn factor<=
;  "Creates a rule metafunction that is the syntactic factor (a nongreedy repetition) of the
;  given subrule by a given integer or less--that is, it accepts a certain number of tokens
;  that fulfill the subrule that is a certain factor or less, and leaves the rest behind."
;  [factor subrule]
;  (alt (factor= factor subrule) (rep< factor subrule)))
;
;(defn lit-conc-seq
;  "Creates a rule metafunction that is the concatenation of the literals of the sequence of
;  the given sequenceable object--that is, it accepts only a series of tokens that matches
;  the sequence of the token sequence.
;  (def a (lit-seq \"ABCD\")) would be equivalent to the EBNF
;    a = \"A\", \"B\", \"C\", \"D\";
;  The new rule's products would be the result of the concatenation rule."
;  [token-seq]
;  (fn [tokens info]
;    (conc-fn (map lit token-seq) tokens info)))
;
;(defn lit-alt-seq
;  "Creates a rule metafunction that is the alternative of the literals of the sequence of
;  the given sequenceable object--that is, it accepts only a series of tokens that matches
;  any of the token sequence.
;  (def a (lit-seq \"ABCD\")) would be equivalent to the EBNF
;    a = \"A\" | \"B\" | \"C\" | \"D\";
;  The new rule's products would be the result of the concatenation rule."
;  [token-seq]
;  (fn [tokens info]
;    (alt-fn (map lit token-seq) tokens info)))
;
;(defn emptiness
;  "A rule metafunction that matches emptiness--that is, it always matches with every given
;  token sequence, and it always returns [nil tokens].
;  (def a emptiness) would be equivalent to the EBNF
;    a = ;
;  This rule's product is always nil, and it therefore always returns [nil tokens]."
;  [tokens info]
;  [nil tokens info])
;
;(defn followed-by
;  "Creates a rule metafunction that figures out if the following tokens after the base
;  subrule match the given following subrule, without consuming any of those following
;  tokens.
;  Make sure that the following subrule doesn't depend on info at all."
;  [base-subrule following-subrule]
;  (validate-all base-subrule
;    (fn [_ remainder info] (following-subrule remainder info))))
;
;(defn with-info
;  "Creates a rule metafunction that applies a processing function to a subrule's results'
;  info. The processing function should accept two arguments: the info of the subrule's
;  results and the product of the subrule's results."
;  [subrule process-info]
;  (fn [tokens info]
;    (let [subrule-result (subrule tokens info)]
;      (when-not (nil? subrule-result)
;        (assoc subrule-result 2 (process-info info (subrule-result 0)))))))
;
;(defn failpoint
;  "Creates a rule metafunction that applies a failpoint to a subrule. When the subrule
;  fails—i.e., it returns nil—then the failure function is called. Its two arguments are the
;  tokens and info that caused it to fail."
;  [subrule failure]
;  (fn [tokens info]
;    (let [subrule-result (subrule tokens info)]
;      (if (nil? subrule-result)
;          (failure tokens info)
;          subrule-result))))
;
;(defn do-effects-before
;  "Creates a rule metafunction that applies a side-effect function to a subrule before its
;  subrule tests its tokens.
;  This is useful for temporarily making a rule print a message whenever it's called. The
;  effects function is passed the tokens and info given to this rule."
;  [subrule effects]
;  (fn [tokens info]
;    (effects tokens info)
;    (subrule tokens info)))
;
;(defn anything
;  "A rule metafunction that matches anything--that is, it matches the first token of the
;  tokens it is given.
;  This rule's product is the first token it receives."
;  [tokens info]
;  [(first tokens) (next tokens) info])
;
;(defmacro product-context
;  "Creates a concatenation rule metafunction with bindings. First, the tokens are fed into a
;  series of binding subrules in a vector head: each of those rule's products is bound to a
;  lexical variable(s). Then, each of the subrules in the body is evaluated with those
;  variables available. In other words, it's like the let macro, except that all arguments
;  are rules concatenated together."
;  [bindvec & other-subrules]
;  (if (odd? (count bindvec))
;    (throw-arg "Odd number of elements in product-context bindings")
;    `(fn [tokens# info#]
;       (when-let [[[~@(take-nth 2 bindvec) :as subproducts#] subremainder# subinfo#]
;                  (conc-fn (lazy-seq [~@(take-nth 2 (next bindvec))]) tokens# info#)]
;         (when-let [second-result#
;                    (conc-fn (lazy-seq [~@other-subrules]) subremainder# subinfo#)]
;           (assoc second-result# 0 (into subproducts# (second-result# 0))))))))
;
;(defmacro product-invisible-context
;  "Like product-context, only the bindings don't consume any tokens."
;  [bindvec & other-subrules]
;  (if (odd? (count bindvec))
;    (throw-arg "Odd number of elements in product-context bindings")
;    `(fn [tokens# info#]
;       (when-let [[[~@(take-nth 2 bindvec) :as subproducts#] subremainder# subinfo#]
;                  (conc-fn (lazy-seq [~@(take-nth 2 (next bindvec))]) tokens# info#)]
;         (when-let [second-result#
;                    (conc-fn (lazy-seq [~@other-subrules]) tokens# info#)]
;           (assoc second-result# 0 (into subproducts# (second-result# 0))))))))
;
;(defn match-remainder
;  "Creates a rule made of two subrules. The first matches the first of its tokens as usual.
;  The second matches the remainder, but does not actually consume the remainder. The product
;  of (match-remainder a b) is [a b], and the remainder is a-remainder and the info is
;  a-info.
;  If either subrule fails, the whole rule fails."
;  [first-subrule remainder-subrule]
;  (fn [tokens info]
;    (when-let [[first-product first-remainder first-info] (first-subrule tokens info)]
;      (when-let [[remainder-product] (remainder-subrule first-remainder first-info)]
;        [[first-product remainder-product] first-remainder first-info]))))
