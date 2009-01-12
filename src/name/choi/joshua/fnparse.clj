(ns name.choi.joshua.fnparse)

; A rule is a function that:
; - Takes a sequential collection of tokens.
; - If the token sequence is valid, it returns a vector containing the (0) consumed tokens'
;   products and (1) a sequence of the remaining tokens or nil. In all documentation here,
;   "a rule's products" is the first element of a valid result from the rule.
; - If the given token sequence is invalid and the rule fails, it simply returns nil.

(defn term
  "Creates a rule function that is a terminal rule of the given validator--that is, it accepts
  only tokens for whom (validator token) is true.
  (def a (term validator)) would be equivalent to the EBNF
    a = ? (validator %) evaluates to true ?;
  The new rule's product would be the first token, if it fulfills the validator.
  If the token does not fulfill the validator, the new rule simply returns nil."
  [validator]
  (fn [tokens]
    (let [first-token (first tokens)]
      (if (validator first-token),
          [first-token (rest tokens)]))))

(defn validate
  "Creates a rule function from attaching a validator function to the given subrule--that is,
  any products of the subrule must fulfill the validator function.
  (def a (validate b validator)) says that the rule a succeeds only when b succeeds and when
  (validator b-product) is true. The new rule's product would be b-product. If b fails or
  (validator b-product) is false, then nil is simply returned."
  [subrule validator]
  (fn [tokens]
    (let [[product remainder :as result] (subrule tokens)]
      (if (and (not (nil? result)) (validator product))
          result))))

(defn semantics
  "Creates a rule function from attaching a semantic hook function to the given subrule--that
  is, its products are from applying the semantic hook to the subrule's products. When the
  subrule fails and returns nil, the new rule will return nil."
  [subrule semantic-hook]
  (fn [tokens]
    (let [[product remainder :as result] (subrule tokens)]
      (if (not (nil? result))
          [(semantic-hook product) remainder]))))

(defn constant-semantics
  "Creates a rule function from attaching a constant semantic hook function to the given
  subrule--that is, its product is a constant value. When the subrule fails and returns nil,
  the new rule will return nil."
  [subrule semantic-value]
  (semantics subrule (fn [_] semantic-value)))

(defn lit
  "Creates a rule function that is the terminal rule of the given literal token--that is, it
  accepts only tokens that are equal to the given literal token.
  (def a (lit \"...\")) would be equivalent to the EBNF
    a = \"...\";
  The new rule's product would be the first token, if it equals the given literal token.
  If the token does not equal the given literal token, the new rule simply returns nil."
  [literal-token]
  (term #(= % literal-token)))

(defn re-term
  "Creates a rule function that is the terminal rule of the given regex--that is, it accepts
  only tokens that match the given regex.
  (def a (re-term #\"...\")) would be equivalent to the EBNF
    a = ? (re-matches #\"...\" %) evaluates to true ?;
  The new rule's product would be the first token, if it matches the given regex.
  If the token does not match the given regex, the new rule simply returns nil."
  [token-regex]
  (term #(re-matches token-regex %)))

(defn conc
  "Creates a rule function that is the concatenation of the given subrules--that is, each
  subrule followed by the next.
  (def a (conc b c d)) would be equivalent to the EBNF
    a = b, c, d;
  The new rule's products would be the vector [b-product c-product d-product]. If any of
  the subrules don't match in the right place, the new rule simply returns nil."
  [& subrules]
  (fn [tokens]
    (loop [products [], token-queue tokens, rule-queue subrules]
      (if (nil? rule-queue),
          [products token-queue],
          (let [curr-result ((first rule-queue) token-queue)]
            (if (not (nil? curr-result))
                (recur (conj products (curr-result 0))
                       (curr-result 1)
                       (rest rule-queue))))))))

(defn alt
  "Creates a rule function that is the alternative of the given subrules--that is, any one
  of the given subrules. Note that the subrules' order matters: the very first rule that
  accepts the given tokens will be selected.
  (def a (alt b c d)) would be equivalent to the EBNF
    a = b | c | d;
  The new rule's product would be b-product, c-product, or d-product depending on which
  of the rules first accepts the given tokens. If none of the subrules matches, the new rule
  simply returns nil."
  [& subrules]
  (fn [tokens]
    (some #(% tokens) subrules)))

(defn opt
  "Creates a rule function that is the optional form of the given subrule--that is, either
  the presence of the absence of the subrule.
  (def a (opt b)) would be equivalent to the EBNF
    a = [b];
  The new rule's product would be either b-product, if b accepts it, or else nil. Note
  that the latter actually means that the new rule would then return the vector
  [nil tokens]. The new rule can never simply return nil."
  [subrule]
  (fn [tokens]
    (or (subrule tokens) [nil tokens])))

(defn rep*
  "Creates a rule function that is the zero-or-more repetition of the given subrule--that
  is, either zero or more of the subrule.
  (def a (rep* b)) would be equivalent to the EBNF
    a = {b};
  The new rule's products would be either the vector [b-product ...] for how many matches
  of b were found, or the empty vector [] if there was no match. Note that the latter
  actually means that the new rule would then return the vector [[] tokens]. The new rule
  can never simply return nil."
  [subrule]
  (fn [tokens]
    (loop [products [], token-queue tokens]
      (let [cur-result (subrule token-queue)]
        (if (or (nil? cur-result) (= cur-result [nil nil]))
            [products token-queue],
            (recur (conj products (cur-result 0))
                   (cur-result 1)))))))

(defn rep+
  "Creates a rule function that is the one-or-more repetition of the given subrule--that
  is, either one or more of the subrule.
  (def a (rep+ b)) would be equivalent to the EBNF
    a = {b}-;
  The new rule's products would be the vector [b-product ...] for how many matches of b
  were found. If there were zero matches, then nil is simply returned."
  [subrule]
  (fn [tokens]
    (let [product ((rep* subrule) tokens)]
       (if (not (empty? (product 0))), product))))

(defn except
  "Creates a rule function that is the exception from the first given subrules with the
  rest of the given subrules--that is, it accepts only tokens that fulfill the first
  subrule but fail the second subrule.
  (def a (except b c d)) would be equivalent to the EBNF
    a = b - c - d;
  The new rule's products would be b-product. If b fails or either c or d succeeds, then
  nil is simply returned."
  [minuend & subtrahends]
  (fn [tokens]
    (let [product (minuend tokens)]
      (if (and (not (nil? product)) (every? #(nil? (% tokens)) subtrahends))
          product))))

(defn factor=
  "Creates a rule function that is the syntactic factor of the given subrule by a given
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

(defn rep-rule
  "Creates a rule function that is the repetition of the given subrule whose valid size is
  determined by a predicate."
  [factor-predicate subrule]
  (validate (rep* subrule) (comp factor-predicate count)))

(defn rep=
  "Creates a rule function that is the repetition of the given subrule by the given positive
  integer factor--that is, it accepts only a certain number of tokens that fulfill the
  subrule, no more and no less."
  [factor subrule]
  (validate (rep* subrule) #(= (count %) factor)))

(defn rep<
  "Creates a rule function that is the repetition of the given subrule by less than the
  given positive integer factor--that is, it accepts a certain range number of tokens that
  fulfill the subrule, less than but not equal to the limiting factor.
  The new rule's products would be b-product. If b fails below n times, then nil is simply
  returned."
  [limit subrule]
  (validate (rep* subrule) #(< (count %) limit)))

(defn rep<=
  "Creates a rule function that is the repetition of the given subrule by the given positive
  integer factor or less--that is, it accepts a certain range number of tokens that fulfill
  the subrule, less than but not equal to the limiting factor.
  The new rule's products would be b-product. If b fails below n times, then nil is simply
  returned."
  [limit subrule]
  (validate (rep* subrule) #(<= (count %) limit)))

(defn factor<
  "Creates a rule function that is the syntactic factor of the given subrule by less than
  a given integer--that is, it accepts a certain number of tokens that fulfill the subrule
  that is less than a certain factor, and leaves the rest behind."
  [factor subrule]
  (alt (factor= (dec factor) subrule) (rep< factor subrule)))

(defn factor<=
  "Creates a rule function that is the syntactic factor of the given subrule by a given
  integer or less--that is, it accepts a certain number of tokens that fulfill the subrule
  that is a certain factor or less, and leaves the rest behind."
  [factor subrule]
  (alt (factor= factor subrule) (rep< factor subrule)))

(defn lit-conc-seq
  "Creates a rule function that is the concatenation of the literals of the sequence of the
  given sequenceable object--that is, it accepts only a series of tokens that matches the
  sequence of the token sequence.
  (def a (lit-seq \"ABCD\")) would be equivalent to the EBNF
    a = \"A\", \"B\", \"C\", \"D\";
  The new rule's products would be the result of the concatenation rule."
  [token-seq]
  (apply conc (map lit token-seq)))

(defn lit-alt-seq
  "Creates a rule function that is the alternative of the literals of the sequence of the
  given sequenceable object--that is, it accepts only a series of tokens that matches any
  of the token sequence.
  (def a (lit-seq \"ABCD\")) would be equivalent to the EBNF
    a = \"A\" | \"B\" | \"C\" | \"D\";
  The new rule's products would be the result of the concatenation rule."
  [token-seq]
  (apply alt (map lit token-seq)))

(defn emptiness
  "A rule function that matches emptiness--that is, it always matches with every given token
  sequence, and it always returns [nil tokens].
  (def a emptiness) would be equivalent to the EBNF
    a = ;
  This rule's product is always nil, and it therefore always returns [nil tokens]."
  [tokens]
  [nil tokens])

(defn followed-by
  "Creates a rule function that figures out if the first token fulfills the subrule without
  consuming the token."
  [subrule]
  (fn [tokens]
    (let [[product _ :as result] (subrule tokens)]
      (if (not (nil? result))
          [product tokens]))))

(defn flatten
  "Takes any nested combination of sequential things (lists, vectors,
  etc.) and returns their contents as a single, flat sequence."
  [x]
  (let [s? #(instance? clojure.lang.Sequential %)]
    (filter (complement s?) (tree-seq s? seq x))))
