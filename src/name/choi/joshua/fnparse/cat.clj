(ns name.choi.joshua.fnparse.cat
  (:require [clojure.contrib.monads :as m] [clojure.template :as template]
            [name.choi.joshua.fnparse.common :as c] [clojure.contrib.def :as d]
            [clojure.contrib.seq :as seq])
  (:refer-clojure
    :rename {defn define-fn, defn- define-fn-}
    :exclude #{+ for})
  (:import [clojure.lang IPersistentMap]))

(defprotocol ABankable
  (get-bank [o])
  (set-bank [o new-bank]))

(define-fn- vary-bank [bankable f & args]
  (set-bank bankable (apply f (get-bank bankable) args)))

(deftype State [tokens position context] :as this
  c/AState
    (position [] position)
  ABankable
    (get-bank [] (meta this))
    (set-bank [new-bank] (with-meta this new-bank))
  IPersistentMap)

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

(deftype LRNode [seed rule head] :as this
  ABankable
    (get-bank [] (meta this))
    (set-bank [new-bank] (with-meta this new-bank))
  IPersistentMap)

(deftype Head [involved-rules rules-to-be-evaluated] IPersistentMap)

(extend ::c/Success ABankable
  {:get-bank (comp get-bank :state)
   :set-bank #(update-in %1 [:state] set-bank %2)})

(extend ::c/Failure ABankable
  {:get-bank meta
   :set-bank with-meta})

(define-fn- make-state [input context]
  (State input 0 context (Bank {} [] {}) nil))

(define-fn parse [rule input context success-fn failure-fn]
  (c/parse make-state rule input context success-fn failure-fn))

(define-fn prod [product]
  (fn product-rule [state]
    (c/Success product state
      (c/ParseError (:position state) nil nil))))

(defmacro defrm [& forms]
  `(d/defn-memo ~@forms))

(defmacro defrm- [& forms]
  `(defrm ~@forms))

(d/defvar emptiness_
  (prod nil)
  "A rule that matches emptiness--that
  is, it always matches with every given
  token sequence, and it always returns
  [nil given-state].
  (def a emptiness) would be equivalent
  to the EBNF a = ; This rule's product
  is always nil, and it therefore always
  returns [nil given-state].")

(define-fn- make-failure [state unexpected-token descriptors]
  (set-bank
    (c/Failure
      (c/ParseError (:position state) unexpected-token descriptors))
    (get-bank state)))

(define-fn nothing_ [state]
  (make-failure state nil #{}))

(define-fn with-error [message]
  (fn with-error-rule [state]
    (make-failure state nil #{(c/ErrorDescriptor :message message)})))

(define-fn only-when [valid? message]
  (if-not valid? (with-error message) (prod valid?)))

(define-fn combine [rule product-fn]
  (fn [state]
    (let [{first-error :error, :as first-result} (c/apply-rule state rule)]
      (if (c/success? first-result)
        (let [next-rule
                (-> first-result :product product-fn)
              {next-error :error, :as next-result}
                (-> first-result :state (c/apply-rule next-rule))]
          (assoc next-result
            :error (c/merge-parse-errors first-error next-error)))
        first-result))))

(define-fn- get-memory [bank subrule state-position]
  (-> bank :memory (get-in [subrule state-position])))

(define-fn- store-memory [bank subrule state-position result]
  (assoc-in bank [:memory subrule state-position] result))

(define-fn- clear-bank [bankable]
  (set-bank bankable nil))

(define-fn- get-lr-node [bank index]
  (-> bank :lr-stack (get index)))

(define-fn- grow-lr [subrule state node-index]
  (let [state-0 state
        position-0 (:position state-0)
        bank-0 (assoc-in (get-bank state-0) [:position-heads position-0]
                 node-index)]
    (loop [cur-bank bank-0]
      (let [cur-bank (update-in cur-bank [:lr-stack node-index]
                       #(assoc % :rules-to-be-evaluated
                          (:involved-rules %)))
            cur-result (c/apply-rule (set-bank state-0 cur-bank) subrule)
            cur-result-bank (get-bank cur-result)
            cur-memory-val (get-memory cur-result-bank subrule position-0)]
        (if (or (c/failure? cur-result)
                (<= (-> cur-result :state :position)
                    (-> cur-memory-val :state :position)))
          (let [cur-result-bank (update-in cur-result-bank [:position-heads]
                                  dissoc node-index)]
            (set-bank cur-memory-val cur-result-bank))
          (let [new-bank (store-memory cur-result-bank subrule
                           position-0 (clear-bank cur-result))]
            (recur new-bank)))))))

(define-fn- add-head-if-not-already-there [head involved-rules]
  (update-in (or head (Head #{} #{})) [:involved-rules]
    into involved-rules))

(define-fn- setup-lr [lr-stack stack-index]
  (let [indexes (range (inc stack-index) (count lr-stack))
        involved-rules (map :rule (subvec lr-stack (inc stack-index)))
        lr-stack (update-in lr-stack [stack-index :head]
                   add-head-if-not-already-there involved-rules)
        lr-stack (reduce #(assoc-in %1 [%2 :head] stack-index)
                   lr-stack indexes)]
    lr-stack))

(define-fn- lr-answer [subrule state node-index seed-result]
  (let [bank (get-bank state)
        bank (assoc-in bank [:lr-stack node-index :seed] seed-result)
        lr-node (get-lr-node bank node-index)
        node-seed (:seed lr-node)]
    (if (-> lr-node :rule (not= subrule))
      node-seed
      (let [bank (store-memory bank subrule (:position state) node-seed)]
        (if (c/failure? node-seed)
          (set-bank node-seed bank)
          (grow-lr subrule (set-bank state bank) node-index))))))

(define-fn- recall [bank subrule state]
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
          (set-bank (nothing_ state) bank)
          (if (-> head :rules-to-be-evaluated (contains? subrule))
            (let [bank (update-in [:lr-stack node-index :rules-to-be-evalated]
                         disj subrule)
                  result (-> state (set-bank bank) (c/apply-rule subrule))]
              (vary-bank result store-memory subrule position result))
            memory))))))

(define-fn- remember [subrule]
  (fn remembering-rule [state]
    (let [bank (get-bank state)
          state-position (:position state)
          found-memory-val (recall bank subrule state)]
      (if found-memory-val
        (if (integer? found-memory-val)
          (let [bank (update-in bank [:lr-stack]
                       setup-lr found-memory-val)
                new-failure (set-bank (nothing_ state) bank)]
            new-failure)
          (set-bank found-memory-val bank))
        (let [bank (store-memory bank subrule state-position
                     (-> bank :lr-stack count))
              bank (update-in bank [:lr-stack] conj
                     (LRNode nil subrule nil))
              state-0b (set-bank state bank)
              subresult (c/apply-rule  state-0b subrule)
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
          result)))))

(define-fn + [& rules]
  (remember
    (fn summed-rule [state]
      (let [apply-next-rule
             (fn apply-next-rule [prev-result next-rule]
               (-> state
                 (set-bank (get-bank prev-result))
                 (c/apply-rule next-rule)
                 (update-in [:error]
                   #(c/merge-parse-errors (:error prev-result) %))))
            initial-result (emptiness_ state)
            results (rest (seq/reductions apply-next-rule
                            initial-result rules))]
        #_ (str results) #_ (prn "results" results)
        (or (seq/find-first c/success? results) (last results))))))

(m/defmonad parser-m
  "The monad that FnParse uses."
  [m-zero nothing_
   m-result prod
   m-bind combine
   m-plus +])

(define-fn label [label-str rule]
  {:pre #{(string? label-str)}}
  (fn labelled-rule [state]
    (let [result (c/apply-rule state rule), initial-position (:position state)]
      (if-not (-> result :error :position (> initial-position))
        (assoc-in result [:error :descriptors]
          #{(c/ErrorDescriptor :label label-str)})
        result))))

(defmacro for
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
  ([label-str steps product-expr]
   `(->> (for ~steps ~product-expr) (label ~label-str)))
  ([steps product-expr]
  `(m/domonad parser-m ~steps ~product-expr)))

(define-fn term
  "(term validator) is equivalent
  to (validate anything validator).
  Creates a rule that is a terminal rule of the given validator--that is, it
  accepts only tokens for whom (validator token) is true.
  (def a (term validator)) would be equivalent to the EBNF
    a = ? (validator %) evaluates to true ?;
  The new rule's product would be the first token, if it fulfills the
  validator."
  [label-str validator]
  (label label-str
    (fn terminal-rule [{:keys #{tokens position} :as state}]
      (let [token (nth tokens position ::nothing)]
        (if (not= token ::nothing)
          (if (validator token)
            (c/Success token (assoc state :position (inc position))
              (c/ParseError position token nil))
            (make-failure state token nil))
          (make-failure state ::end-of-input nil))))))

(define-fn antiterm [label-str pred]
  (term label-str (complement pred)))

(d/defvar anything
  (term "anything" (constantly true))
  "A rule that matches anything--that is, it matches
  the first token of the tokens it is given.
  This rule's product is the first token it receives.
  It fails if there are no tokens left.")

(define-fn lit
  "Equivalent to (comp term (partial partial =)).
  Creates a rule that is the terminal
  rule of the given literal token--that is,
  it accepts only tokens that are equal to
  the given literal token.
  (def a (lit \"...\")) would be equivalent to the EBNF
    a = \"...\";
  The new rule's product would be the first
  token, if it equals the given literal token."
  [token]
  (term (format "'%s'" token) (partial = token)))

(define-fn re-term
  "Equivalent to (comp term (partial partial re-matches)).
  Creates a rule that is the terminal rule of the given regex--that is, it
  accepts only tokens that match the given regex.
  (def a (re-term #\"...\")) would be equivalent to the EBNF
    a = ? (re-matches #\"...\" %) evaluates to true ?;
  The new rule's product would be the first token, if it matches the given
  regex."
  [pattern]
  (term (str "a token matching pattern " pattern)
    (partial re-matches pattern)))

(define-fn followed-by [rule]
  (fn [state]
    (let [result (c/apply-rule state rule)]
      (if (c/success? result)
        ((prod (:product result)) state)
        result))))

(define-fn not-followed-by
  "Creates a rule that does not consume
  any tokens, but fails when the given
  subrule succeeds. On success, the new
  rule's product is always true."
  [rule]
  (label "<not followed by something>"
    (fn not-followed-by-rule [state]
      (let [result (c/apply-rule state rule)]
        (if (c/failure? result)
          (c/Success true state (:error result))
          (-> state nothing_ (assoc :error (:error result))))))))

(define-fn semantics
  "Creates a rule with a semantic hook,
  basically a simple version of a complex
  rule. The semantic hook is a function
  that takes one argument: the product of
  the subrule."
  [subrule semantic-hook]
  (for [subproduct subrule]
    (semantic-hook subproduct)))

(define-fn constant-semantics
  "Creates a rule with a constant semantic
  hook. Its product is always the given
  constant."
  [subrule semantic-value]
  (for [subproduct subrule]
    semantic-value))

(define-fn conc
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
    (fn concatenation-rule [state]
      ((m/m-seq subrules) state))))

(define-fn vconc [& subrules]
  (semantics (apply conc subrules) vec))

(define-fn opt
  "Creates a rule that is the optional form
  of the subrule. It always succeeds. Its result
  is either the subrule's (if the subrule
  succeeds), or else its product is nil, and the
  rule acts as the emptiness rule.
  (def a (opt b)) would be equivalent to the EBNF:
    a = b?;"
  [subrule]
  (+ subrule emptiness_))

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

(define-fn lit-conc-seq
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
   (+ conc (map rule-maker token-seq))))

(define-fn lit-alt-seq
  "A convenience function: it creates a rule
  that is the alternation of the literals
  formed from the given sequence of literal tokens.
  (def a (lit-alt-seq [\"a\" \"b\" \"c\"]))
  would be equivalent to the EBNF:
    a = \"a\" | \"b\" | \"c\";"
  ([token-seq]
   (lit-alt-seq token-seq lit))
  ([token-seq rule-maker]
   (apply + (map rule-maker token-seq))))

(define-fn except
  "Creates a rule that is the exception from
  the first given subrules with the second given
  subrule--that is, it accepts only tokens that
  fulfill the first subrule but fails the
  second of the subrules.
  (def a (except b c)) would be equivalent to the EBNF
    a = b - c;
  The new rule's products would be b-product. If
  b fails or c succeeds, then nil is simply returned."
  ([label-str minuend subtrahend]
   (label label-str
     (for [_ (not-followed-by subtrahend), product minuend]
       product)))
  ([label-str minuend first-subtrahend & rest-subtrahends]
   (except label-str minuend
     (apply + (cons first-subtrahend rest-subtrahends)))))

(define-fn antiterm [label-str pred]
  (term label-str (complement pred)))

(define-fn antilit [token]
  (term (str "anything except " token) #(not= token %)))

(define-fn set-lit [label-str tokens]
  (term label-str (set tokens)))

(define-fn anti-set-lit [label-str tokens]
  (antiterm label-str (tokens set)))

(define-fn mapconc [tokens]
  (apply conc (map lit tokens)))

(define-fn mapalt [f coll]
  (apply + (map f coll)))

(define-fn prefix-conc [prefix body]
  (for [_ prefix, content body] content))

(define-fn suffix-conc [body suffix]
  (for [content body, _ suffix] content))

(define-fn circumfix-conc [prefix body suffix]
  (prefix-conc prefix (suffix-conc body suffix)))

(defmacro template-+ [argv expr & values]
  (let [c (count argv)]
    `(+ ~@(map (fn [a] (template/apply-template argv expr a)) 
              (partition c values)))))

(define-fn case-insensitive-lit [#^Character token]
  (+ (lit (Character/toLowerCase token))
       (lit (Character/toUpperCase token))))

(d/defvar ascii-digits "0123456789")
(d/defvar lowercase-ascii-alphabet "abcdefghijklmnopqrstuvwxyz")
(d/defvar base-36-digits (str ascii-digits lowercase-ascii-alphabet))

(defrm radix-digit
  ([base] (radix-digit (format "a base-%s digit" base) base))
  ([label-str base]
   {:pre #{(integer? base) (<= 0 base 36)}}
   (->> base-36-digits (take base) seq/indexed
     (mapalt (fn [[index token]]
               (constant-semantics (case-insensitive-lit token) index)))
     (label label-str))))

(d/defvar decimal-digit
  (radix-digit "a decimal digit" 10))

(d/defvar hexadecimal-digit
  (radix-digit "a hexadecimal digit" 16))

(d/defvar uppercase-ascii-letter
  (set-lit "an uppercase ASCII letter" "ABCDEFGHIJKLMNOPQRSTUVWXYZ"))

(d/defvar lowercase-ascii-letter
  (set-lit "a lowercase ASCII letter" "abcdefghijklmnopqrstuvwxyz"))

(d/defvar ascii-letter
  (label "an ASCII letter"
    (+ uppercase-ascii-letter lowercase-ascii-letter)))
