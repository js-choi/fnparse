(ns name.choi.joshua.fnparse.cat
  (:use clojure.template clojure.contrib.def clojure.contrib.seq-utils)
  (:require [clojure.contrib.monads :as m])
  (:import [clojure.lang Sequential IPersistentMap IPersistentVector Var]))

(declare remember lit rep* rep+)

(defprotocol ABankable
  (get-bank [o])
  (set-bank [o new-bank]))

(defn- vary-bank [bankable f & args]
  (set-bank bankable (apply f (get-bank bankable) args)))

(deftype State [tokens position] IPersistentMap)

(deftype Success [product state] IPersistentMap)

(deftype Failure [] IPersistentMap)

(deftype Bank [memory lr-stack position-heads] IPersistentMap)
  ; memory: a nested map with function keys and map vals
    ; The keys are rules
    ; The vals are maps with integer keys and result vals
      ; The nested keys correspond to token positions
      ; The vals can be successes, failures, or the
      ; keyword :lr-stack-peek.
  ; lr-stack: a vector of LRNodes
  ; position-heads: a map with position keys and index vals
    ; The keys correspond to token positions
    ; The vals correspond to LRNodes' indexes in the lr-stack

(deftype LRNode [seed rule head] IPersistentMap)

(deftype Head [involved-rules rules-to-be-evaluated] IPersistentMap)

(extend ::State ABankable
  {:get-bank meta
   :set-bank with-meta})

(extend ::Success ABankable
  {:get-bank (comp get-bank :state)
   :set-bank #(update-in %1 [:state] set-bank %2)})

(extend ::Failure ABankable
  {:get-bank meta
   :set-bank with-meta})

(extend ::LRNode ABankable
  {:get-bank meta
   :set-bank with-meta})

(do-template [fn-name type-name doc-string]
  (defn fn-name doc-string [result]
    (-> result type (isa? type-name)))
  failure? ::Failure "Is the given result a Failure?"
  success? ::Success "Is the given result is a Success?")

(defn failure? [result]
  (-> result type (isa? ::Failure)))

(defn success? [result]
  (-> result type (isa? ::Success)))

(defn make-state [input]
  (State input 0 (Bank {} [] {}) nil))

(defn inc-position [state]
  (update-in state [:position] inc))

; (defn parse
;   [input rule success-fn failure-fn]
;   (let [result (-> input make-state rule)]
;     (if (failure? result)
;       (failure-fn nil)
;       (success-fn (:product result) (-> result :state :remainder)))))

(defn get-var-name [#^Var variable]
  (symbol (str (.ns variable)) (name (.sym variable))))

; (defmacro defrulemaker
;   ([var-name args body]
;    (defrulemaker var-name nil body))
;   ([var-name doc-string args body]
;    `(defn ~var-name ~doc-string ~args
;       ~body)))

(defvar- basic-failure (Failure))

(defn mock-state
  ([tokens] (mock-state tokens nil))
  ([tokens context] (partial make-state tokens context)))

(m/defmonad parser-m
  "The monad that FnParse uses."
  [m-zero
     (fn [state] (set-bank basic-failure (get-bank state)))
   m-result
     (fn m-result-parser [product]
       (fn [state] (Success product state)))
   m-bind
     (fn m-bind-parser [rule product-fn]
       (fn [state]
         (let [result (rule state)]
           (if (failure? result)
             result
             ((product-fn (:product result)) (:state result))))))
   m-plus
    (fn m-plus-parser [& rules]
      (remember
        (fn summed-rule [state]
          (let [results (rest (reductions #(%2 (set-bank state (get-bank %1)))
                                state rules))]
            (or (find-first success? results)
                (set-bank basic-failure (get-bank (last results))))))))])

(defn with-product [product]
  (m/with-monad parser-m (m-result product)))

(defn anything
  "A rule that matches anything--that is, it matches
  the first token of the tokens it is given.
  This rule's product is the first token it receives.
  It fails if there are no tokens left."
  [state]
  {:pre #{(isa? (type state) ::State)}}
  (m/with-monad parser-m
    (let [token (nth (:tokens state) (:position state) ::nothing)]
      (if (not= token ::nothing)
        (Success token (inc-position state))
        (m/m-zero state)))))

(defn- get-memory [bank subrule state-position]
  (-> bank :memory (get-in [subrule state-position])))

(defn- store-memory [bank subrule state-position result]
  (assoc-in bank [:memory subrule state-position] result))

(defn- clear-bank [bankable]
  (set-bank bankable nil))

(defn- get-lr-node [bank index]
  (-> bank :lr-stack (get index)))

(defn- grow-lr [subrule state node-index]
  (let [state-0 state
        position-0 (:position state-0)
        bank-0 (assoc-in (get-bank state-0)
                 [:position-heads position-0]
                 node-index)]
    (loop [cur-bank bank-0]
      (let [cur-bank (update-in cur-bank [:lr-stack node-index]
                       #(assoc % :rules-to-be-evaluated
                          (:involved-rules %)))
            cur-result (subrule (set-bank state-0 cur-bank))
            cur-result-state (:state cur-result)
            cur-result-bank (get-bank cur-result)
            cur-memory-val (get-memory cur-result-bank subrule position-0)]
        (if (or (failure? cur-result)
                (<= (-> cur-result :state :position)
                    (-> cur-memory-val :state :position)))
          (let [cur-result-bank (update-in cur-result-bank
                                  [:position-heads]
                                  dissoc node-index)]
            (set-bank cur-memory-val cur-result-bank))
          (let [new-bank (store-memory cur-result-bank subrule
                           position-0 (clear-bank cur-result))]
            (recur new-bank)))))))

(defn- add-head-if-not-already-there [head involved-rules]
  (update-in (or head (Head #{} #{})) [:involved-rules]
    into involved-rules))

(defn- setup-lr [lr-stack stack-index]
  (let [indexes (range (inc stack-index) (count lr-stack))
        involved-rules (map :rule (subvec lr-stack (inc stack-index)))
        lr-stack (update-in lr-stack [stack-index :head]
                   add-head-if-not-already-there involved-rules)
        lr-stack (reduce #(assoc-in %1 [%2 :head] stack-index)
                   lr-stack indexes)]
    lr-stack))

(defn- lr-answer [subrule state node-index seed-result]
  (let [bank (get-bank state)
        bank (assoc-in bank [:lr-stack node-index :seed] seed-result)
        lr-node (get-lr-node bank node-index)
        node-seed (:seed lr-node)]
    (if (-> lr-node :rule (not= subrule))
      node-seed
      (let [bank (store-memory bank subrule (:position state)
                   node-seed)]
        (if (failure? node-seed)
          (set-bank node-seed bank)
          (grow-lr subrule (set-bank state bank) node-index))))))

(defn- recall [bank subrule state]
  (let [position (:position state)
        memory (get-memory bank subrule position)
        node-index (-> bank :position-heads (get position))
        lr-node (get-lr-node bank node-index)]
    (if (nil? lr-node)
      memory
      (let [head (:head lr-node)]
        (if-not (or memory
                    (-> lr-node :rule (= subrule))
                    (-> head :involved-rules (contains? subrule)))
          (set-bank basic-failure bank)
          (if (-> head :rules-to-be-evaluated (contains? subrule))
            (let [bank (update-in [:lr-stack node-index          
                                   :rules-to-be-evalated]
                         disj subrule)
                  result (-> state (set-bank bank) subrule)]
              (vary-bank result store-memory subrule position result))
            memory))))))

(defn- remember [subrule]
  (fn remembering-rule [state]
    (let [bank (get-bank state)
          state-position (:position state)
          found-memory-val (recall bank subrule state)]
      (if found-memory-val
        (do
          (if (integer? found-memory-val)
            (let [bank (update-in bank [:lr-stack]
                         setup-lr found-memory-val)
                  new-failure (set-bank basic-failure bank)]
              new-failure)
            (set-bank found-memory-val bank)))
        (do
          (let [bank (store-memory bank subrule state-position
                       (-> bank :lr-stack count))
                bank (update-in bank [:lr-stack] conj
                       (LRNode nil subrule nil))
                state-0b (set-bank state bank)
                subresult (subrule state-0b)
                bank (get-bank subresult)
                submemory (get-memory bank subrule state-position)
                current-lr-node (-> bank :lr-stack peek)
                ; bank (update-in bank [:lr-stack] pop)
                bank (store-memory bank subrule state-position
                       (clear-bank subresult))
                new-state (set-bank state bank)
                result
                  (if (and (integer? submemory) (:head current-lr-node))
                    (lr-answer subrule new-state submemory subresult)
                    (set-bank subresult bank))
                result (vary-bank result update-in [:lr-stack] pop)]
            result))))))

(m/with-monad parser-m
  (defvar nothing m/m-zero))

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

; (defvar- fetch-state
;   (m/fetch-state)
;   "A rule that consumes no tokens. Its product
;   is the entire current state.
;   [Equivalent to the result of fetch-state
;   from clojure.contrib.monads.]")
; 
; (defn- set-state [state]
;   (m/set-state state))

; (defn fetch-info
;   "Creates a rule that consumes no tokens.
;   The new rule's product is the value
;   of the given key in the current state.
;   [Equivalent to fetch-val from clojure.contrib.monads.]"
;   [key]
;   (m/fetch-val key))

; (with-test
;   (defn fetch-remainder
;     "Generates a rule whose product is the
;     sequence of the remaining tokens of any states
;     that it is given. It consumes no tokens.
;     [(fetch-remainder) is equivalent to
;     (fetch-val get-remainder) from
;     clojure.contrib.monads.]"
;     []
;     (m/fetch-val get-remainder))
;   (is (= ((complex [remainder (fetch-remainder)] remainder)
;           (make-cf-state ["hi" "THEN"]))
;          [["hi" "THEN"] (make-cf-state ["hi" "THEN"])])))
 
; (defn set-info
;   "Creates a rule that consumes no tokens.
;   The new rule directly changes the
;   current state by associating the given
;   key with the given value. The product
;   is the old value of the changed key.
;   [Equivalent to set-val from
;   clojure.contrib.monads.]"
;   [key value]
;   (m/set-val key value))
;  
; (with-test
;   (defn update-info
;     "Creates a rule that consumes no tokens.
;     The new rule changes the current state
;     by associating the given key with the
;     evaluated result of applying the given
;     updating function to the key's current
;     value. The product is the old value of
;     the changed key.
;     [Equivalent to update-val from clojure.contrib.monads.]"
;     [key val-update-fn & args]
;     (m/update-val key #(apply val-update-fn % args)))
;   (let [mock (partial make-state '(A))]
;     (is (= [#{} (mock 1 {:variables #{'foo}})]
;             ((update-info :variables conj 'foo)
;              (mock 0 {:variables #{}}))))))
 
(m/with-monad parser-m
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

(defvar re-term
  (comp term (partial partial re-matches))
  "Equivalent to (comp term (partial partial re-matches)).
  Creates a rule that is the terminal rule of the given regex--that is, it
  accepts only tokens that match the given regex.
  (def a (re-term #\"...\")) would be equivalent to the EBNF
    a = ? (re-matches #\"...\" %) evaluates to true ?;
  The new rule's product would be the first token, if it matches the given
  regex.")

(defmacro deflits
  "Intended for defining many literal rules at once."
  [map-name name-token-map]
  (letfn [(make-rule-def-form [name-token-entry]
            (let [[rule-name token] name-token-entry]
              `(def ~rule-name (lit ~token))))
          (make-keyword-rule-entry [name]
            [(keyword name) (first `(~name))])]
    (let [rule-def-forms (map make-rule-def-form name-token-map)
          keyword-rule-pairs (->> name-token-map keys
                               (mapcat make-keyword-rule-entry))
          rule-map-form `(def ~map-name (array-map ~@keyword-rule-pairs))]
      `(do ~@rule-def-forms ~rule-map-form))))

(defn followed-by [rule]
  (fn [state]
    (let [result (rule state)]
      (if (failure? result)
        result
        ((with-product (:product result)) state)))))

(defn not-followed-by
  "Creates a rule that does not consume
  any tokens, but fails when the given
  subrule succeeds. On success, the new
  rule's product is always true."
  [subrule]
  (m/with-monad parser-m
    (fn [state]
      (if (failure? (subrule state))
        (Success true state)
        (m/m-zero state)))))

(defn semantics
  "Creates a rule with a semantic hook,
  basically a simple version of a complex
  rule. The semantic hook is a function
  that takes one argument: the product of
  the subrule."
  [subrule semantic-hook]
  (complex [subproduct subrule]
    (semantic-hook subproduct)))

(defn constant-semantics
  "Creates a rule with a constant semantic
  hook. Its product is always the given
  constant."
  [subrule semantic-value]
  (complex [subproduct subrule]
    semantic-value))
 
; (def remainder-peek
;   "A rule whose product is the very next
;   token in the remainder of any given state.
;   The new rule does not consume any tokens."
;   (complex [remainder (fetch-remainder)]
;     (first remainder)))

(defn conc
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
  (m/with-monad parser-m
    (fn [state]
      ((m/m-seq subrules) state))))

(defn vconc [& subrules]
  (semantics (apply conc subrules) vec))

(defn alt
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
  (m/with-monad parser-m (apply m/m-plus subrules)))

(defn opt
  "Creates a rule that is the optional form
  of the subrule. It always succeeds. Its result
  is either the subrule's (if the subrule
  succeeds), or else its product is nil, and the
  rule acts as the emptiness rule.
  (def a (opt b)) would be equivalent to the EBNF:
    a = b?;"
  [subrule]
  (m/with-monad parser-m
    (m-plus subrule emptiness)))

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
  `(semantics (conc ~first-subrule ~@rest-subrules) first))
 
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
   (alt conc (map rule-maker token-seq))))

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
   (apply alt (map rule-maker token-seq))))

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
  (complex [_ (not-followed-by subtrahend), product minuend]
    product))

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
    (loop [cur-product (transient []), cur-state state]
      (let [subresult (subrule cur-state)]
        (if (success? subresult)
          (recur (conj! cur-product (:product subresult)) (:state subresult))
          (Success (persistent! cur-product) cur-state))))))

(defn rep-predicate
  "Like the rep* function, only that the number
  of times that the subrule is fulfilled must
  fulfill the given factor-predicate function."
  [factor-predicate subrule]
  (validate (rep* subrule) (comp factor-predicate count)))

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
  (rep-predicate pos? subrule))

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
  (apply conc (replicate factor subrule)))

; (with-test
;   (defn factor<
;     "Same as the factor= function, except that the
;     new rule eats up tokens only until the
;     given subrule is fulfilled one less times than
;     the factor. The new rule would never fail.
;     (factor< 3 :a) would eat the first two tokens [:a :a :a :a :b] and return:
;       [[:a :a] (list :a :a :b)].
;     (factor< 3 :a) would eat the first three tokens [:b] and return:
;       [nil (list :b)]"
;     [factor subrule]
;     (alt (factor= (dec factor) subrule) (rep< factor subrule)))
;   (let [tested-rule (factor< 3 (lit \A))]
;     (is (= (tested-rule (make-cf-state (seq "AAAAC")))
;            [[\A \A] (make-cf-state (seq "AAC"))])
;         (str "created factor< rule works when symbol fulfills all subrule multiples and"
;              "leaves strict remainder"))
;     (is (= (tested-rule (make-cf-state (seq "AAAC")))
;            [[\A \A] (make-cf-state (seq "AC"))])
;         "created factor< rule works when symbol fulfills all subrule multiples only")
;     (is (= (tested-rule (make-cf-state (seq "AAC"))) [[\A \A] (make-cf-state (seq "C"))])
;         "created factor< rule works when symbol does not fulfill all subrule multiples")
;     (is (= (tested-rule (make-cf-state (seq "DAB")))
;            [nil (make-cf-state (seq "DAB"))])
;         "created factor< rule works when symbol does not fulfill subrule at all")))
;  
; (defn factor<=
;   "Same as the factor= function, except that
;   the new rule always succeeds, consuming tokens
;   until the subrule is fulfilled the same amount
;   of times as the given factor. The new rule
;   would never fail.
;   (factor<= 3 :a) would eat the first two tokens [:a :a :a :a :b] and return:
;     [[:a :a :a] (list :a :b)].
;   (factor<= 3 :a) would eat the first three tokens [:b] and return:
;     [nil (list :b)]"
;   [factor subrule]
;   (alt (factor= factor subrule) (rep< factor subrule)))
;  
; (with-test
;   (defn failpoint
;     "Creates a rule that applies a failpoint to
;     a subrule. When the subrule fails—i.e., it
;     returns nil—then the failure hook function
;     is called with one argument, the state at time
;     of failure."
;     [subrule failure-hook]
;     (fn [state]
;       (let [result (subrule state)]
;         (if (success? result)
;           result
;           (failure-hook (get-remainder state) state)))))
;   (let [exception-rule (failpoint (lit "A")
;                           (fn [remainder state]
;                             (throw-arg "ERROR %s at line %s"
;                               (first remainder) (:line state))))]
;     (is (= (exception-rule (-> ["A"] make-cf-state (assoc :line 3)))
;            ["A" (-> nil make-cf-state (assoc :line 3))])
;         "failing rules succeed when their subrules are fulfilled")
;     (is (thrown-with-msg? IllegalArgumentException
;           #"ERROR B at line 3"
;           (exception-rule (-> ["B"] make-cf-state (assoc :line 3)))
;         "failing rules fail with given exceptions when their subrules fail"))))
;  
; (with-test
;   (defmacro effects
;     "Creates a rule that calls the lists given
;     in its body for side effects. It does not
;     consume any tokens or modify the state in
;     any other way."
;     [& effect-body]
;     `(fn [state#]
;        [((fn [] ~@effect-body)) state#])))
;  
; (set-test effects
;   (let [rule
;          (complex [subproduct (lit "A")
;                    line-number (fetch-info :line)
;                    effects (effects (println "!" subproduct)
;                                     (println "YES" line-number))]
;            subproduct)]
;     (is (= (with-out-str
;              (is (= (rule (-> ["A" "B"] make-cf-state (assoc :line 3)))
;                     ["A" (-> (list "B") make-cf-state (assoc :line 3))])
;                  "pre-effect rules succeed when their subrules are fulfilled"))
;            "! A\nYES 3\n")
;         "effect rule should call their effect and return the same state")))
; 
; (with-test
;   (defn intercept
;     "This rule is intended for intercepting
;     and continuing exceptions and errors.
;     It creates a rule that calls the intercept
;     hook. The intercept hook is a function that
;     receives only one argument: a function to be
;     called with no arguments that calls the
;     subrule with the current state. If you don't
;     call this argument in the intercept hook, the
;     subrule will not be called at all. The result
;     of the whole rule will be directly what the
;     product of the intercept-hook is. Here's an
;     example of intended usage:
;       (intercept subrule-that-can-throw-an-exception
;         (fn [rule-call]
;           (try (rule-call)
;             (catch Exception e (throw another-exception)))))"
;     [subrule intercept-hook]
;     (fn [state] (intercept-hook (partial subrule state))))
;   (let [parse-error-rule
;           (semantics (lit \A) (fn [_] (throw (Exception.))))
;         intercept-rule
;           (intercept parse-error-rule
;             (fn [rule-call]
;               (try (rule-call)
;                 (catch Exception e :error))))]
;     (is (= (intercept-rule (make-cf-state "ABC")) :error))))
;  
; (defn validate-state
;   "Creates a rule from attaching a
;   state-validating function to the given
;   subrule--that
;   is, any products of the subrule must fulfill
;   the validator function.
;   (def a (validate-state b validator)) says
;   that the rule a succeeds only when b succeeds
;   and also when the evaluated value of
;   (validator b-state) is true. The new rule's
;   product would be b-product."
;   [subrule validator]
;   (complex [subproduct subrule
;             substate fetch-state
;             :when (validator substate)]
;     subproduct))
;  
; (defn validate-remainder
;   "Creates a rule from attaching a
;   remainder-validating function to the given
;   subrule--that is, any products of the subrule
;   must fulfill the validator function.
;   (def a (validate-remainder b validator)) says
;   that the rule a succeeds only when b succeeds
;   and also when the evaluated value of
;   (validator b-remainder) is true. The new rule's
;   product would be b-product."
;   [subrule validator]
;   (complex [subproduct subrule
;             subremainder (fetch-remainder)
;             :when (validator subremainder)]
;     subproduct))
; 
; ; ; (defvar- constantly-nil
; ; ;   (constantly nil))
; ; ; 
; ; ; (with-test
; ; ;   (defnk match-rule
; ; ;     "Creates a function that tries to completely
; ; ;     match the given rule to the given state,
; ; ;     with no remainder left over after the match.
; ; ;     - If (rule state-0) fails, then
; ; ;       (failure state-0) is called.
; ; ;     - If the remainder of the state in the result of
; ; ;       (rule state-0) is not empty, then...
; ; ;         (incomplete
; ; ;           product-from-consumed-tokens
; ; ;           new-state-after-rule
; ; ;           initial-state)
; ; ;       ...is called.
; ; ;     - If the new remainder is empty, then the
; ; ;       product of the rule is returned.
; ; ;     - The failure and incomplete functions are by
; ; ;       default (constantly nil)."
; ; ;     [state-0 rule :failure constantly-nil, :incomplete constantly-nil]
; ; ;     (if-let [[product state-1] (rule state-0)]
; ; ;       (if (empty? (get-remainder state-1))
; ; ;         product
; ; ;         (incomplete product state-1 state-0))
; ; ;       (failure state-0)))
; ; ;   (let [rule (lit "A")
; ; ;         matcher #(match-rule % rule
; ; ;                    :failure identity, :incomplete vector)]
; ; ;     (is (= (matcher (make-cf-state ["A"])) "A"))
; ; ;     (is (= (matcher (make-cf-state ["B"])) (make-cf-state ["B"])))
; ; ;     (is (= (matcher (make-cf-state ["A" "B"]))
; ; ;            ["A" (make-cf-state ["B"]) (make-cf-state ["A" "B"])]))))
; ; ; 
; ; ; ; (defmacro memoize-rules
; ; ; ;   "Turns the subrules contained in the vars
; ; ; ;   referred to by the given symbols
; ; ; ;   into memoizing rules that caches
; ; ; ;   their results in atoms. In effect, memoize
; ; ; ;   is called on all of the rules.
; ; ; ;   Whenever the new mem rule is called,
; ; ; ;   it checks the cache to see if there is an
; ; ; ;   existing match; otherwise, the subrule is called.
; ; ; ;  
; ; ; ;   Why didn't I just implement this as a
; ; ; ;   regular rule-making function? Because this
; ; ; ;   is truly only useful for optimization.
; ; ; ;   It is better to separate this non-essential
; ; ; ;   complexity from the actual definition of
; ; ; ;   your rules. It also makes it easier to
; ; ; ;   change which rules are optimized.
; ; ; ;   Thanks to Chouser for how to do this
; ; ; ;   with a variable.
; ; ; ;   
; ; ; ;   Running (test memoize-rules), which repeats a bunch of
; ; ; ;   calls on mem-test-rule two hundred times, takes about
; ; ; ;   160 ms on my computer, which uses an 2.2 GHz Intel Core
; ; ; ;   Duo and 2 GB of RAM.
; ; ; ;   Omitting the memoize-rules form above causes the same test
; ; ; ;   to take 430 ms, a very high 92% difference."
; ; ; ;   [& subrule-names]
; ; ; ;   (let [subrule-vars (vec (for [nm subrule-names] `(var ~nm)))]
; ; ; ;     `(doseq [subrule-var# ~subrule-vars]
; ; ; ;        (alter-var-root subrule-var# memoize))))
; ; ; ;  
; ; ; ; (defvar- mem-test-rule
; ; ; ;   (alt (conc (lit 'a) (opt (lit 'b))) (lit 'c)))
; ; ; ;  
; ; ; ; (memoize-rules mem-test-rule)
; ; ; ;   ; Running (test memoize-rules), which repeats a bunch of
; ; ; ;   ; calls on mem-test-rule two hundred times, takes about
; ; ; ;   ; 160 ms on my computer, which uses an 2.2 GHz Intel Core
; ; ; ;   ; Duo and 2 GB of RAM.
; ; ; ;   ; Omitting the memoize-rules form above causes the same test
; ; ; ;   ; to take 430 ms, a very high 92% difference.
; ; ; ;  
; ; ; ; (set-test memoize-rules
; ; ; ;   (dotimes [n 200]
; ; ; ;     (is (= (mem-test-rule (make-cf-state '[a c]))
; ; ; ;            [['a nil] (make-cf-state '[c])]))
; ; ; ;     (is (= (mem-test-rule (make-cf-state '[a b c]))
; ; ; ;            ['[a b] (make-cf-state '[c])]))
; ; ; ;     (is (= (mem-test-rule (make-cf-state '[a b c]))
; ; ; ;            ['[a b] (make-cf-state '[c])]))
; ; ; ;     (is (= (mem-test-rule (make-cf-state '[c s a])) ['c (make-cf-state '[s a])]))
; ; ; ;     (let [result (mem-test-rule (make-cf-state '(c)))]
; ; ; ;       (is (= (first result) 'c))
; ; ; ;       (is (empty? (seq (get-remainder (second result))))))
; ; ; ;     (is (failure? (mem-test-rule (make-cf-state '[s a]))))
; ; ; ;     (is (failure? (mem-test-rule (make-cf-state '[s a]))))))
; ; ; ;  
; ; ; ; (defn- testing-rule-maker
; ; ; ;   [arg1 arg2]
; ; ; ;   (conc (opt arg1) (opt arg2)))
; ; ; ;  
; ; ; ; (state-context std-template
; ; ; ;   (defvar- testing-rm-rule
; ; ; ;     (testing-rule-maker (lit \a) (lit \b))))
; ; ; ;  
; ; ; ; (deftest test-rule-makers
; ; ; ;   (let [state-0 (state-context std-template (make-cf-state "ab"))
; ; ; ;         state-1 (state-context std-template (make-cf-state nil))]
; ; ; ;     (is (thrown? RuntimeException
; ; ; ;           (testing-rm-rule (make-cf-state "abc"))))
; ; ; ;     (is (= (testing-rm-rule state-0) [[\a \b] state-1]))))
; ; ; ; 
; ; ; ; (defn inc-column
; ; ; ;   "Meant to be used only with std-bundle states, or other states with an
; ; ; ;   integer :column val.
; ; ; ;  
; ; ; ;   Creates a new rule that calls the subrule, and then increments the column.
; ; ; ;   Meant to be called on literal rules of one non-break character."
; ; ; ;   [subrule]
; ; ; ;   (invisi-conc subrule (update-info :column inc)))
; ; ; ;  
; ; ; ; (defn inc-line
; ; ; ;   "Meant to be used only with std-bundle states, or other states with an
; ; ; ;   integer :column val and an integer :line val.
; ; ; ;  
; ; ; ;   Creates a new rule that calls the subrule, and then increments the line and
; ; ; ;   sets the column to zero."
; ; ; ;   [subrule]
; ; ; ;   (invisi-conc subrule
; ; ; ;     (update-info :line inc) (set-info :column 0)))
