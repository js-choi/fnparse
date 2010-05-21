(ns edu.arizona.fnparse.cat
  (:require [edu.arizona.fnparse [core :as c] [common :as k]]
            [clojure.contrib [monads :as m] [def :as d] [except :as except]
                             [seq :as seq] [core :as cljcore]]
            [clojure.template :as template])
  (:import [edu.arizona.fnparse.core Success Failure])
  (:refer-clojure :rename {peek vec-peek, when if-when}
                  :exclude #{for + mapcat find}))

(d/defalias match c/match)
(d/defalias find c/find)
(d/defalias substitute c/substitute)
(d/defalias substitute-1 c/substitute-1)

(defn rule?
  "Tests if the given object is a Hound Rule, or a var containing a Hound Rule."
  [obj]
  (-> obj type (= ::Rule)))

(defmacro defrule
  "Defines a rule var. You really should use this instead of `def`
  whenever you define rules, because:
  1. It gives you cool shortcuts to write rule-related documentation.
  2. It allows you to use not-yet defined rules in mutually
     recursive rules.
  
  Metadata documentation options
  ==============================
  The `meta-opts` parameter expects a map argument,
  and makes it the new var's metadata. Giving certain
  options in the metadata also does appends certain
  things to the rule's `doc-string`.
  
  *  `:succeeds` expects a short description on when
     the rule succeeds.
  *  `:product` expects a short description on what
     products the rule gives when it succeeds.
  *  `:consumes` expects a short description on how
     many and what kinds of tokens the rule consumes
     when it succeeds.
  *  `:error` expects a short description on the
     error that the rule gives when it fails."
  ([rule-name form] `(defrule ~rule-name nil ~form))
  ([rule-name doc-string form] `(defrule ~rule-name ~doc-string nil ~form))
  ([rule-name doc-string meta-opts form]
  `(k/general-defrule ~rule-name "FnParse Hound rule" ~doc-string ~meta-opts
     ::Rule ~form)))

(defmacro defrule-
  "Like `defrule`, but also makes the var private."
  [fn-name & forms]
  (list* `defrule (vary-meta fn-name assoc :private true) forms))

(defmacro defmaker
  "Creates a rule-making function. Use this instead of
  `clojure.core/defn` whenever you make a rule-making
  function. (It does other stuff like memoization and
  and stuff.) Also see `defmaker-` and `defmaker-macro`.
  
  Arguments
  =========
  `defmaker` requires exactly the same arguments as
  `clojure.core/defn`. Particularly important is being
  able to give metadata easily.
  
  Metadata options
  ================
  `defmaker` accepts all special metadata options that
  `defrule` does; see `defrule` for more information.
  There is also a `:no-memoize?` option
  that does something special, detailed below.
  
  Memoization
  ===========
  `defmaker` rule-makers *memoize by default*. This means
  that they save the arguments they receive and their
  corresponding results in a cache, and search the cache
  every time they are called for equal arguments. See
  `clojure.k/memoize` for more information.
  
  95% of the time, you won't have to worry about the warning below.
  
  A warning: memoization uses *Clojure equality*. This
  means that giving vector arguments must always return the
  same rule as giving list arguments, because vectors can
  be equal to lists. If your function must return a different
  rule when given `[1 2 3]` versus `'(1 2 3)`, then you should
  give `{:no-memoize? true}` in your metadata."
  [fn-name & forms]
  (list* `k/general-defmaker `defn "FnParse Hound rule-maker" fn-name forms))

(defmacro defmaker-
  "Like `defmaker`, but also makes the var private."
  [fn-name & forms]
  (list* `defmaker (vary-meta fn-name assoc :private true) forms))

(defmacro defmaker-macro
  "Like `defmaker`, but makes a macro rule-maker
  instead of a function rule-maker."
  [fn-name & forms]
  (list* `k/general-defmaker `defmacro "FnParse Hound macro rule-maker"
    fn-name forms))

(defprotocol ABankable
  (get-bank [o])
  (set-bank [o new-bank]))

(defn- vary-bank [bankable f & args]
  (set-bank bankable (apply f (get-bank bankable) args)))

(defrecord State [tokens position location warnings context alter-location]
  c/AState
    (get-position [this] position)
    (get-remainder [this] (drop position tokens))
    (next-state [this]
      (when-let [token (get tokens position)]
        (assoc this
          :position (inc position))
          :location ((alter-location (nth position tokens)) location)))
    (state-location [this] location)
    (state-warnings [this] warnings)
  ABankable
    (get-bank [this] (meta this))
    (set-bank [this new-bank] (with-meta this new-bank)))

(defrecord Bank [memory lr-stack position-heads])
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

(defrecord LRNode [seed rule head] ABankable
  (get-bank [this] (meta this))
  (set-bank [this new-bank] (with-meta this new-bank)))

(defrecord Head [involved-rules rules-to-be-evaluated])

(extend-protocol ABankable
  Success
    (get-bank [success] (get-bank (:state success)))
    (set-bank [success bank] (update-in success [:state] set-bank bank))
  Failure
    (get-bank [failure] (meta failure))
    (set-bank [failure bank] (with-meta failure bank)))

(defn make-state
  [input & {:keys #{location context alter-location}
            :or {location (c/make-standard-location 0 0)
                 alter-location c/standard-alter-location}}]
  {:pre #{(or (nil? location) (c/location? location)) (ifn? alter-location)}}
  (State. input 0 location #{} context alter-location (Bank. {} [] {}) nil))

(defn state?
  "Tests if the given object is a Hound State."
  [obj]
  (isa? (type obj) ::State))

(defmacro make-rule [rule-symbol [state-symbol :as args] & body]
  {:pre #{(symbol? rule-symbol) (symbol? state-symbol) (empty? (rest args))}}
 `(k/make-rule ::Rule ~rule-symbol ~state-symbol ~@body))

(defn- make-failure [state descriptors]
  (set-bank
    (c/make-failure
      (c/make-parse-error (:position state) (:location state) descriptors))
    (get-bank state)))

(defmaker prod
  "Creates a rule that always returns the given `product`.
  
  Use the `:let` modifier in preference to this function
  when you use this inside rule comprehensions from the
  `for` macro.
  
  Is the result monadic function of the `parser-m` monad."
  {:succeeds "Always."
   :product "The given `product`."
   :consumes "No tokens."
   :no-memoize? true}
  [product]
  (make-rule product-rule [state]
    (c/make-success product state
      (c/make-parse-error (:position state) (:location state) #{}))))

(defmacro defrm [& forms]
  `(d/defn-memo ~@forms))

(defmacro defrm- [& forms]
  `(defrm ~@forms))

(defrule <emptiness>
  "The general emptiness rule. (Actually just `(prod nil)`)."
  {:succeeds "Always."
   :product "`nil`."
   :consumes "No tokens."}
  (prod nil))

(defrule <nothing>
  "The general failing rule.
  
  Use `with-error` or `when` in preference to `<nothing>`,
  because the first two rule-makers can attach meaningful
  error messages.
  
  Is the zero monadic value of the `parser-m` monad."
  {:succeeds "Never."
   :error "`\"Expected: absolutely nothing\"`."}
  (make-rule nothing-rule [state]
    (make-failure state #{})))

(defmaker with-error
  "Creates an always-failing rule with the given
  message. Use this in preference to `<nothing>`."
  {:succeeds "Never."
   :error "An error with the given `message`."}
  [message]
  (make-rule with-error-rule [state]
    (make-failure state #{(c/make-message-descriptor message)})))

(defmaker when
  "Creates a maybe-failing rule—
  an either succeeding or a failing rule—
  depending on if `valid?` is logical true. If
  `valid?`, then the rule always succeeds and acts
  like `(prod valid?)`. If not `valid?`, then the
  rule always fails and acts like `(with-error message)`.
  
  Examples
  ========
  This function is very useful for when you want
  to validate a certain rule.
  
    (for [value <number>
            _ (when (< odd 10)
                \"number must be less than ten\")]
        value)
  
  The rule given above succeeds only when `<number>`
  matches and `<number>`'s product is less than 10."
  {:succeeds "If `valid?` is a true value."
   :product "The value of `valid?`."
   :consumes "No tokens."
   :error-messages "The given `message`."
   :no-memoize? true}
  [valid? message]
  (if-not valid? (with-error message) (prod valid?)))

(defmaker combine
  "Creates a rule combining the given `rule` into the
  `product-fn`.
  
  *Use `cat` or `for`* instead of this function.
  You *shouldn't have to use this function*
  at all, unless you're doing something special.

  The product-fn must return a rule when given the
  product of the first rule. `combine` is the bind
  monadic function of the parser monad.
  
  Below, the rule returned by `(product-fn
  state-after-first-rule)` will be referred to as
  `second-rule`."
  {:success "If both `rule` and `(product-fn state-after-first-rule)` succeed."
   :product "The product of `(product-fn state-after-first-rule)`."
   :consumes "All tokens that `rule` and then `(product-fn
             state-after-first-rule)` consume."
   :fail "If either `rule` and `(product-fn state-after-first-rule)` fail."
   :labels "Any labels that the failing rule gives."
   :messages "Any messages that the failing rule gives."}
  [rule product-fn]
  (make-rule combined-rule [state]
    (let [{first-error :error, :as first-result} (c/apply rule state)]
      (if (c/success? first-result)
        (let [next-rule (-> first-result :product product-fn)
              next-result (c/apply next-rule (:state first-result))
              next-error (:error next-result)]
          (assoc next-result :error
            (k/merge-parse-errors first-error next-error)))
        first-result))))

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
        bank-0 (assoc-in (get-bank state-0) [:position-heads position-0]
                 node-index)]
    (loop [cur-bank bank-0]
      (let [cur-bank (update-in cur-bank [:lr-stack node-index]
                       #(assoc % :rules-to-be-evaluated
                          (:involved-rules %)))
            cur-result (c/apply subrule (set-bank state-0 cur-bank))
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

(defn- add-head-if-not-already-there [head involved-rules]
  (update-in (or head (Head. #{} #{})) [:involved-rules]
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
      (let [bank (store-memory bank subrule (:position state) node-seed)]
        (if (c/failure? node-seed)
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
          (set-bank (c/apply <nothing> state) bank)
          (if (-> head :rules-to-be-evaluated (contains? subrule))
            (let [bank (update-in [:lr-stack node-index :rules-to-be-evalated]
                         disj subrule)
                  result (c/apply subrule (set-bank state bank))]
              (vary-bank result store-memory subrule position result))
            memory))))))

(defn- remember [subrule]
  (make-rule remembering-rule [state]
    (let [bank (get-bank state)
          state-position (:position state)
          found-memory-val (recall bank subrule state)]
      (if found-memory-val
        (if (integer? found-memory-val)
          (let [bank (update-in bank [:lr-stack]
                       setup-lr found-memory-val)
                new-failure (set-bank (c/apply <nothing> state) bank)]
            new-failure)
          (set-bank found-memory-val bank))
        (let [bank (store-memory bank subrule state-position
                     (-> bank :lr-stack count))
              bank (update-in bank [:lr-stack] conj
                     (LRNode. nil subrule nil))
              state-0b (set-bank state bank)
              subresult (c/apply subrule state-0b)
              bank (get-bank subresult)
              submemory (get-memory bank subrule state-position)
              current-lr-node (-> bank :lr-stack vec-peek)
              bank (store-memory bank subrule state-position
                     (clear-bank subresult))
              new-state (set-bank state bank)
              result
                (if (and (integer? submemory) (:head current-lr-node))
                  (lr-answer subrule new-state submemory subresult)
                  (set-bank subresult bank))
              result (vary-bank result update-in [:lr-stack] pop)]
          result)))))

(defmaker +
  "Creates a summed rule.
  
  Adds the given sub-rules together, forming a new rule.
  The order of the sub-rules matters.
  
  This is the FnParse *Cat* version of +. Unlike
  FnParse Hound's `+` rule-maker, Cat's *does* backtrack.
  
  This means that it searches for the *first successful*
  match from its sub-rules, regardless of whether they
  consume tokens or not.
  
  Otherwise, if every sub-rule failed, then a failure
  is returned with the proper error descriptors.
  
  This is the plus monadic operator of the `parser-m` monad."
  {:success "If any sub-rule succeeds."
   :failure "If not a single sub-rule succeeds."
   :product "The product of the succeeding sub-rule."
   :consumes "Whatever the succeeding sub-rule consumes."
   :error "An intelligent combination of the errors
                from all the failed sub-rules."
   :no-memoize? true}
  [& rules]
  (letfn [(merge-result-errors [prev-result next-error]
            (k/merge-parse-errors (:error prev-result) next-error))
          (apply-next-rule [state prev-result next-rule]
            (-> next-rule
              (c/apply (set-bank state (get-bank prev-result)))
              (update-in [:error] (partial merge-result-errors prev-result))))]
    (c/self-label-rule-meta rules
      (remember
        (make-rule summed-rule [state]
          (let [apply-next-rule (partial apply-next-rule state)
                initial-result (c/apply <emptiness> state)
                results (rest (reductions apply-next-rule
                                initial-result rules))]
            (or (seq/find-first c/success? results) (last results))))))))

(m/defmonad parser-m
  "The monad that FnParse Cat uses."
  [m-zero <nothing>
   m-result prod
   m-bind combine
   m-plus +])

(defmaker label
  "Creates a labelled rule.
  
  Labels the given rule with the given string, returning
  a new rule. The given label will appear in the descriptors
  of any parse errors that expected the given rule to
  succeed.
  
  Personally, I label rules with articles like \"a\" or \"an\".
  For instance, I'd label a rule representing Clojure
  vectors \"a vector\".
  
  You don't have to understand the details, but...
  If `rule` consumed *no* tokens, then all error labels
  from `rule`'s result are overrided with the
  given `l`. Otherwise, the old labels are
  untouched, as they contain information from
  further down the input."
  {:success "If `rule` succeeds."
   :product "`rule`'s product."
   :consumes "Whatever `rule` consumes."
   :error "Smartly determines the appropriate error message."}
  [l rule]
  {:pre #{(c/descriptor-content? l)}}
  (let [rule (or (c/rule-unlabelled-base rule) rule)]
    (c/label-rule-meta #{l} rule
      (make-rule labelled-rule [state]
        (let [result (c/apply rule state), initial-position (:position state)]
          (if (-> result :error :position (<= initial-position))
            (update-in result [:error :descriptors]
              k/assoc-label-in-descriptors l)
            result))))))

(defmaker annotate-error
  "Creates an error-annotating rule. Whenever
  the given `rule` fails, the error is passed
  into the `message-fn` function. This can be
  useful to add a message with more info to an
  error when certain conditions are met.
  
  `message-fn` must return a string when given
  the original `ParseError`, which will be added
  to the `ParseError`, or `nil` for no message.
  (`ParseError`s are maps of type
  `:edu.arizona.fnparse.c/ParseError`.
  See its documentation for more information.)"
  [message-fn rule]
  {:pre #{(ifn? message-fn) (rule? rule)}}
  (letfn [(annotate [error]
            (let [new-message (message-fn error)]
              (if new-message
                (update-in error [:descriptors]
                  conj (c/make-message-descriptor new-message))
                error)))]
    (make-rule error-annotation-rule [state]
      (let [reply (c/apply rule state)]
        (update-in reply [:error] annotate)))))

(defmaker-macro for
  "Creates a rule comprehension, very much like
  `clojure.core/for`. If it succeeds or fails and
  also how many tokens it consumes is similar to `cat`.
  How the final product is calculated is similar to `hook`.
  
  If you want to know, this macro is equivalent to the
  `clojure.contrib.monads/domonad` form of the `parser-m` monad.
  
  Arguments
  =========
  *   `l`: An optional label string. See the
      `label` function for more info.
  *   `steps`: A binding vector containing *binding-form/
      rule pairs* optionally followed by *modifiers*.
      The given rules in each pair are concatenated
      together one after another to create
      the new rule. Each binding-form is bound
      to the product of its corresponding rule.
      The rule expressions can refer to any
      symbol bound to in a previous pair.
      The only current recommended modifier
      is `:let`, which works like how it does it
      `clojure.core/for`.
  *   `product-expr`: The final product of the new rule.
      Only is reached after every sub-rule
      succeeds. The expression can refer
      to any symbol bound to in the `steps`."
  {:success "All sub-rules in the given `steps` succeed, in order."
   :product "Whatever is calculated by `product-expr`."
   :consumes "All tokens that each step consecutively consumes."
   :error "Whatever error the failed rule returns."
   :no-memoize? true}
  ([l steps product-expr]
   `(->> (for ~steps ~product-expr) (label ~l)))
  ([steps product-expr]
  `(m/domonad parser-m ~steps ~product-expr)))

(defmaker validate
  "Creates a validating rule.
  
  A convenience function. Returns a new rule that
  acts like the given `rule`, but also validates
  `rule`'s products with the given predicate.
  Basically just a shortcut for `for` and `when`."
  {:success "When `rule` succeeds and its product fulfills `(pred product)`."
   :product "`rule`'s product."
   :consumes "What `rule` consumes."
   :no-memoize? true}
  [pred message rule]
  {:pre #{(ifn? pred) (string? message) (rule? rule)}}
  (for [product rule, _ (when (pred product) message)]
    product))

(defmaker antivalidate
  "Exactly like the `validate` function, except that
  it uses the complement of `pred` instead."
  {:no-memoize? true}
  [pred message rule]
  {:pre #{(ifn? pred)}}
  (validate (complement pred) message rule))

(defn term-
  "All terminal Cat rules, including `term` and
  `term*`, are based on this function."
  [pred-product? l f]
  (label l
    (make-rule terminal-rule [state]
      (let [{:keys #{tokens position}} state
            token (nth tokens position ::nothing)]
        (if (not= token ::nothing)
          (if-let [f-result (f token)]
            (c/make-success (if pred-product? f-result token)
              (assoc state :position (inc position)
                           :location (((:alter-location state) token)
                                      (:location state)))
              (c/make-parse-error position (:location state) #{}))
            (make-failure state #{}))
          (make-failure state #{}))))))

(defmaker term
  "Creates a terminal rule.
  
  The new rule either consumes one token or fails.
  It must have a `l` that describes it
  and a `predicate` to test if the token it consumes is
  valid.
  
  Do you really need to use `term`?
  =================================
  * If you just want to make sure that the consumed
    token equals something, use `lit` instead.
  * If you just want to make sure that the consumed
    token equals one of a bunch of things, use `term`
    on a set of tokens, or `set-term` on a sequence of
    tokens.
  * If you want to use the complement of the predicate,
    use `antiterm`.
  * If you don't care about what token is consumed,
    just as long as a token is consumed, use `-anything-`.
  * If you want a terminal rule, but you want the result
    of the predicate to be the rule's product instead of
    the token itself, use `term*`. This is useful if
    you have a map of tokens and their products (e.g.
    string escape sequences)."
  {:success "When there's a next token, and it fulfills `(pred token)`."
   :product "The consumed token itself."
   :consumes "One token, any type that fulfills `pred`."
   :error "When `(term \"number\" num?)` fails,
           its error is \"Expected number.\""
   :no-memoize? true}
  [l predicate]
  (term- false l predicate))

(defmaker term*
  "Exactly like `term`, only its product is the result of
  `(f token)` rather than `token`."
  {:no-memoize? true}
  [l f]
  (term- true l f))

(defn antiterm [l pred]
  (term l (complement pred)))

(defmaker antiterm
  "Exactly like term, only uses the complement of the
  given predicate instead."
  {:no-memoize? true}
  [l pred]
  {:pre #{(ifn? pred)}}
  (term l (complement pred)))

(defrule <anything>
  "The generic terminal rule that matches any one token."
  {:succeeds "If there are any tokens left, i.e.
   not at the end of input."
   :product "The token it consumes."
   :consumes "One token, any type."
   :error "\"Expected anything.\""}
  (term "anything" (constantly true)))

(defmaker hook
  "Creates a rule with a semantic hook.
  A shortcut for the `for` macro."
  {:no-memoize? true
   :success "If `rule` succeeds."
   :product "`(semantic-hook product-from-rule)`."
   :consumes "Whatever `rule` consumes."}
  [semantic-hook rule]
  {:pre #{(ifn? semantic-hook) (rule? rule)}}
  (c/self-label-rule-meta [rule]
    (for [product rule] (semantic-hook product))))

(defn chook
  "Creates a rule with a constant semantic hook.
  A shortcut for the `for` macro. The name
  stands for 'constant-hook'. It's exactly like
  `hook`, only the product is a constant; its
  product is always the given `product` object."
  {:no-memoize? true
   :success "If `rule` succeeds."
   :product "Always the given `product`."
   :consumes "Whatever `rule` consumes."}
  [product rule]
  {:pre #{(rule? rule)}}
  (c/self-label-rule-meta [rule]
    (for [_ rule] product)))

(defmaker lit
  "Creates a rule of a literal. A shortcut for
  `(term (partial = token))`. It automatically adds an
  appropriate label."
  {:success "If there is a next token and it is equal to the given `token`."
   :product "Always the consumed `token`."
   :consumes "One token, equal to the given `token`."
   :error "When `(lit \\a) fails, its error says, \"Expected 'a'.\""}
  [token]
  (term (format "'%s'" token) (partial = token)))

(defmaker antilit
  "Creates a rule of an antiliteral.
  A shortcut for `term`.
  It automatically adds an appropriate label."
  {:success "If there is a next token and it is *unequal* to the given `token`."
   :product "The consumed token."
   :consumes "One token, any type (so long as it doesn't equal `token`)."
   :error "When `(antilit \\a) fails, its error
           says, \"Expected anything except 'a'.\""}
  [token]
  (term (format "anything except '%s'" token) #(not= token %)))

(defmaker set-term
  "Creates a terminal rule with a set.
  A shortcut for `(term l (set tokens))`."
  [l tokens]
  {:pre #{(cljcore/seqable? tokens)}}
  (term l (set tokens)))

(defmaker antiset-term
  "Creates a terminal rule with an antiset.
  A shortcut for `(antiterm l (set tokens))`."
  [l tokens]
  (antiterm l (set tokens)))

(defmaker cat
  "Creates a concatenated rule out of many given `rules`."
  {:success "All given `rules` succeed, one after another."
   :product "The sequence (not lazy) of all the `rules`'s respective products."
   :consumes "All tokens that the `rules` sequentially consume."
   :error "The error of whatever sub-rule failed."}
  [& rules]
  {:pre #{(every? rule? rules)}}
  (m/with-monad parser-m
    (m/m-seq rules)))

(defmaker vcat
  "Exactly like cat, only applies `vec` to its product."
  [& subrules]
  (hook vec (apply cat subrules)))

(defmaker opt
  "Creates an optional rule. It is equivalent to `(+ rule emptiness)`."
  {:success "Always."
   :product "Either `rule`'s product (if it succeeds) or `nil` if it fails."
   :consumes "Either whatever `rule` consumes (if it succeeds) or no tokens."}
  [rule]
  {:pre #{(rule? rule)}}
  (+ rule <emptiness>))

(defmaker peek
  "Creates a lookahead rule. Checks if the given
  `rule` succeeds, but doesn't actually consume
  any tokens."
  {:success "If `rule` succeeds."
   :consumes "No tokens."}
  [rule]
  (make-rule peeking-rule [state]
    (let [result (c/apply rule state)]
      (if (c/success? result)
        ((prod (:product result)) state)
        result))))

(defmaker mapcat
  "Creates a rule that is the result of
  applying `cat` to the result of applying map
  to `f` and `token-colls`.
  Use the `phrase` function instead of this
  function when `f` is just `lit`."
  [f & token-colls]
  {:pre #{(ifn? f) (every? cljcore/seqable? token-colls)}}
  (->> token-colls (apply map f) (apply cat)))

(defmaker mapsum
  "Creates a rule that is the result of applying `+` to the
  result of applying map to `f` and `token-colls`.
  Use the `set-term` function instead of this
  function when `f` is just `lit`."
  [f & token-colls]
  {:pre #{(ifn? f) (every? cljcore/seqable? token-colls)}}
  (->> token-colls (apply map f) (apply +)))

(defmaker phrase
  "Creates a phrase rule, which succeeds
  only when the next few tokens all
  consecutively match the given tokens.
  (Actually, it's just `(mapcat lit tokens)`.)"
  [tokens]
  (mapcat lit tokens))

(defmaker prefix
  "Creates a prefixed rule. Use when you want to
  concatenate two rules, but you don't care about
  the first rule's product.
  Its product is always the body-rule's product.
  A shortcut for `(for [_ prefix-rule, content body-rule] content)`."
  [prefix-rule body-rule]
  {:pre #{(rule? prefix-rule) (rule? body-rule)}}
  (for [_ prefix-rule, content body-rule] content))

(defmaker suffix
  "Creates a suffixed rule. Use when you want to
  concatenate two rules, but you don't care about
  the second rule's product.
  Its product is always the body-rule's product.
  A shortcut for `(for [content body-rule, _ suffix-rule] content)`."
  [body-rule suffix-rule]
  {:pre #{(rule? suffix-rule) (rule? body-rule)}}
  (for [content body-rule, _ suffix-rule] content))

(defmaker circumfix
  "Creates a circumfixed rule. Use when you want to
  concatenate three rules, but you don't care about
  the first and third rules' products.
  Its product is always the body-rule's product.
  A shortcut for `(prefix prefix-rule (suffix body-rule suffix-rule))`."
  [prefix-rule body-rule suffix-rule]
  {:pre #{(rule? prefix-rule) (rule? body-rule) (rule? suffix-rule)}}
  (prefix prefix-rule (suffix body-rule suffix-rule)))

(defn- not-followed- [<following>]
  {:pre [(rule? <following>)], :post [(rule? %)]}
  (make-rule following-rule [s]
    (let [following-lbls (c/require-rule-labels <following>)
          descriptors #{(c/make-following-descriptor following-lbls)}]
      (let [following-result (c/apply <following> s)]
        (if (c/failure? following-result)
          (c/apply <emptiness> s)
          (make-failure s descriptors))))))

(defmaker not-followed
  "See also `except`."
  [<base> & following-rules]
  {:pre [(rule? <base>) (every? rule? following-rules)]}
  (suffix <base> (mapcat not-followed- following-rules)))

(defmaker-macro template-sum
  "Creates a summed rule using a template.
  Acts very similarly to `clojure.template/do-template`,
  but instead sums each rule together."
  [argv expr & values]
  {:pre #{(zero? (mod (count values) (count argv)))}}
  (let [c (count argv)]
   `(+ ~@(map (fn [a] (template/apply-template argv expr a))
           (partition c values)))))

(defmaker case-insensitive-lit
  "Creates a case-insensitive rule using Java's
  `Character/toLowerCase` and `Character/toUpperCase`
  methods. Only works with `Character`-type tokens."
  {:succeeds "If there is a next token and it's equal to either
              the upper or lowercase of the given `token`."
   :consumes "One character."}
  [#^Character token]
  {:pre #{(char? token)}}
  (+ (lit (Character/toLowerCase token))
     (lit (Character/toUpperCase token))))

(defmaker effects
  "Creates a side-effect rule. Applies the given
  arguments to the given function. You may prefer `prod`."
  {:succeeds "Always."
   :no-memoize? true
   :product "The result of `(apply f args)`."
   :consumes "No tokens."}
  [f & args]
  {:pre #{(ifn? f)}}
  (make-rule effects-rule [state]
    (c/apply <emptiness> state)))

(defn- except- [<subtrahend>]
  (make-rule exception-rule [s]
    (let [subtrahend-lbls (c/rule-labels <subtrahend>)
          descriptors #{(c/make-exception-descriptor nil subtrahend-lbls)}]
      (let [subtrahend-result (c/apply <subtrahend> s)]
        (if (c/success? subtrahend-result)
          (make-failure s descriptors)
          (c/apply <emptiness> s))))))

(defmaker except
  "Creates a subtracted rule. Matches using
  the given minuend rule, but only when the
  subtrahend rule does not also match. You
  must provide a custom `l`.

  `message-fn`, if given, creates a detailed error
  message when the `subtrahend` succeeds. `message-fn`
  should be a function that takes one argument: `subtrahend`'s
  product, and returns a string."
  {:success "If `minuend` succeeds and `subtrahend` fails."
   :product "`minuend`'s product."
   :consumes "Whatever `minuend` consumes."
   :error "Uses the `l` you provide."}
  [<minuend> & subtrahends]
  {:pre #{(rule? <minuend>) (every? rule? subtrahends)}}
  (prefix (mapcat except- subtrahends) <minuend>))

(defrule <end-of-input>
  "The standard end-of-input rule."
  {:succeeds "If there are no tokens left."
   :product "`true`."
   :consumes "No tokens."}
  (label "the end of input" (except <emptiness> <anything>)))

(defrule <fetch-location>
  "A rule that fetches the current state's location."
  {:success "Always.", :product "The current location.",
   :consumes "Zero tokens."}
  (make-rule fetch-location-rule [state]
    (c/apply (prod (:location state)) state)))

(defmaker alter-location
  "A rule that alters the current location."
  {:success "Always.", :product "The new location.",
   :consumes "Zero tokens."}
  [f & args]
  {:pre #{(ifn? f)}}
  (make-rule location-altering-rule [state]
    (let [altered-state (apply update-in state [:location] f args)]
      (c/apply <fetch-location> altered-state))))

(defrule <fetch-warnings>
  "A rule that fetches the current state's warnings."
  {:success "Always.", :product "The current warnings.",
   :consumes "Zero tokens."}
  (make-rule fetch-warnings-rule [state]
    (c/apply (prod (:warnings state)) state)))

(defmaker add-warning
  "A rule that adds a new warning with the given message."
  {:success "Always.", :product "`nil`.",
   :consumes "Zero tokens."}
  [message]
  (make-rule warnings-altering-rule [state]
    (c/apply <emptiness>
      (update-in state [:warnings] conj (c/make-warning state message)))))

(def ascii-digits "0123456789")
(def lowercase-ascii-alphabet "abcdefghijklmnopqrstuvwxyz")
(def uppercase-ascii-alphabet "ABCDEFGHIJKLMNOPQRSTUVWXYZ")

(defn radix-label
  "The function used by radix-digit to smartly
  create digit labels for the given `core`."
  [core]
  (case core
    10 "a decimal digit"
    16 "a hexadecimal digit"
    8 "an octal digit"
    2 "a binary digit"
    (format "a core-%s digit" core)))

(defmaker radix-digit
  "Returns a rule that accepts one digit character
  token in the number system with the given `core`.
  For instance, `(radix-digit 12)` is a rule
  of a single duodecimal digit.
  
  Digits past 9 are case-insensitive letters:
  11, for instance, is \\b or \\B. cores above
  36 are accepted, but there's no way to use
  digits beyond \\Z (which corresponds to 36).
  
  The rules `<decimal-digit>` and
  `<hexadecimal-digit>` are already provided."
  {:succeeds "If the next token is a digit
    character in the given `core`'s number
    system."
   :product "The digit's corresponding integer."
   :consumes "One character."}
  [core]
  {:pre #{(integer? core) (pos? core)}}
  (term* (radix-label core)
   #(let [product (Character/digit (char %) (int core))]
      (if-when (not= product -1)
        product))))

(defrule <decimal-digit>
  "A rule matching a single core-10 digit
  character token (i.e. \\0 through \\9)."
  {:product "The matching digit's corresponding Integer object, 0 through 9."
   :consumes "One character."}
  (radix-digit 10))

(defrule <hexadecimal-digit>
  "A rule matching a single core-16 digit
  character token (i.e. \\0 through \\F)."
  {:product "The matching digit's corresponding Integer object, 0 through 15."
   :consumes "One character."}
  (radix-digit 16))

(defrule <uppercase-ascii-letter>
  "A rule matching a single uppercase ASCII letter."
  {:product "The matching character itself."
   :consumes "One character."}
  (set-term "an uppercase ASCII letter" uppercase-ascii-alphabet))

(defrule <lowercase-ascii-letter>
  "A rule matching a single lowercase ASCII letter."
  {:product "The matching character itself."
   :consumes "One character."}
  (set-term "a lowercase ASCII letter" lowercase-ascii-alphabet))

(defrule <ascii-letter>
  "A rule matching a single uppercase or lowercase ASCII letter."
  {:product "The matching character itself."
   :consumes "One character."}
  (label "an ASCII letter"
    (+ <uppercase-ascii-letter> <lowercase-ascii-letter>)))

(defrule <ascii-digit>
  "A rule matching a single ASCII numeric digit. You may
  want to use instead `decimal-digit`, which automatically
  converts digits to Integer objects."
  {:product "The matching character itself."
   :consumes "One character."}
  (set-term "an ASCII digit" ascii-digits))

(defrule <ascii-alphanumeric>
  "A rule matching a single alphanumeric ASCII letter."
  {:product "The matching character itself."
   :consumes "One character."}
  (label "an alphanumeric ASCII character"
    (+ <ascii-letter> <ascii-digit>)))

(defrule <ascii-control>
  "A rule matching a single ASCII control character,
  i.e. a character within Unicode points 0000 and 001F."
  {:product "The matching character itself."
   :consumes "One character."}
  (term "an ASCII control character" #(Character/isISOControl (char %))))
