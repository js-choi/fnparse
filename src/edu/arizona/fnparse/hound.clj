(ns edu.arizona.fnparse.hound
  "This is *FnParse Hound*, which can create unambiguous,
  LL(1) or LL(n) parsers."
  (:require [edu.arizona.fnparse :as c]
            [clojure.contrib.seq :as seq]
            [clojure.contrib.monads :as m]
            [clojure.template :as t]
            [clojure.contrib.def :as d]
            [clojure.contrib.except :as except])
  (:refer-clojure :rename {mapcat seq-mapcat}
                  :exclude #{for + peek})
  (:import [clojure.lang IPersistentMap]))

(deftype State [remainder position context] :as this
  IPersistentMap
  c/AState
    (position [] (:position this)))

(deftype Reply [tokens-consumed? result] :as this
  IPersistentMap
  c/AParseAnswer (answer-result [] (-> this :result force)))

(defn make-state
  "Creates a state with the given remainder and context."
  [remainder context]
  (State remainder 0 context))

(defn parse
  "The general parsing function of FnParse Hound.
  
  *   `rule`: The rule. It must accept whatever state that
      make-state returns.
  *   `input`: The sequence of tokens to parse.
  *   `context`: The initial context for the rule.
  *   `success-fn`: A function called when the rule matches
      the input. `(success-fn final-product final-position)`
      is called.
  *   `failure-fn`: A function called when the rule does not
      match the input. `(failure-fn final-error)` is called,
      where `final-error` is an object of type
      `:edu.arizona.fnparse/ParseError`.
  
  If `success-fn` and `failure-fn` aren't included, then
  parse will print out a report of the parsing result."
  ([rule input context success-fn failure-fn]
   (c/parse make-state rule input context success-fn failure-fn))
  ([rule input context]
   (parse rule input context nil nil)))

(defn format-parse-error [error]
  (c/format-parse-error error))

(defn merge-replies [mergee merger]
  (assoc merger :result
    (update-in (-> merger :result force) [:error]
      c/merge-parse-errors (-> mergee :result force :error))))

(def library-name "FnParse Hound")

(defmacro defrule
  "Defines a rule var. You should use this instead of `def`,
  if only because it gives you cool shortcuts to write documentation.
  
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
  `(c/general-defrule ~library-name ~rule-name ~doc-string ~meta-opts ~form)))

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
  `defmaker` accepts all metadata options that `defrule`
  does too. There is also a special `:no-memoize?` option
  that does something special, detailed below.
  
  Memoization
  ===========
  `defmaker` rule-makers *memoize by default*. This means
  that they save the arguments they receive and their
  corresponding results in a cache, and search the cache
  every time they are called for equal arguments. See
  `clojure.core/memoize` for more information.
  
  95% of the time, you won't have to worry about the warning below.
  
  A warning: memoization uses Clojure equality. This
  means that *giving vector arguments must always return the
  same rule as giving list arguments*, because vectors can
  be equal to lists. If your function must return a different
  rule when given `[1 2 3]` versus `'(1 2 3)`, then you should
  give `{:no-memoize? true}` in your metadata."
  [fn-name & forms]
  (list* `c/general-defmaker library-name "rule maker" `defn fn-name forms))

(defmacro defmaker-
  "Like `defmaker`, but also makes the var private."
  [fn-name & forms]
  (list* `defmaker (vary-meta fn-name assoc :private true) forms))

(defmacro defmaker-macro
  "Like `defmaker`, but makes a macro rule-maker
  instead of a function rule-maker."
  [fn-name & forms]
  (list* `c/general-defmaker library-name "rule maker (macro)" `defmacro fn-name
    forms))

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
  (fn prod-rule [state]
    (Reply false
      (c/Success product state
        (c/ParseError (:position state) nil nil)))))

(defrule <emptiness>
  "The general emptiness rule. (Actually just `(prod nil)`)."
  {:succeeds "Always."
   :product "`nil`."
   :consumes "No tokens."}
  (prod nil))

(defn- make-failed-reply
  "Used to create replies containing failures."
  ([state descriptors]
   (make-failed-reply state (first (:remainder state)) descriptors))
  ([state unexpected-token descriptors]
   (Reply false
     (c/Failure
       (c/ParseError (:position state) unexpected-token descriptors)))))

(d/defvar nothing-descriptors
  #{(c/ErrorDescriptor :label "absolutely nothing")}
  "The error descriptors that `<nothing>` uses.")

(defrule <nothing>
  "The general failing rule.
  
  Use `with-error` in preference to `<nothing>`,
  because `with-error` rules can attach meaningful
  error messages.
  
  Is the zero monadic value of the `parser-m` monad."
  {:succeeds "Never."
   :error "`\"Expected: absolutely nothing\"`."}
  (fn nothing-rule [state]
    (make-failed-reply state nothing-descriptors)))

(defmaker with-error
  "Creates an always-failing rule with the given
  message. Use this in preference to `<nothing>`."
  {:succeeds "Never."
   :error "An error with the given `message`."}
  [message]
  (fn with-error-rule [state]
    (make-failed-reply state #{(c/ErrorDescriptor :message message)})))

(defmaker only-when
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
            _ (only-when (< odd 10)
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
  (letfn [(apply-product-fn [result]
            (c/apply (:state result) (product-fn (:product result))))]
    (fn [state]
      (let [first-reply (c/apply state rule)]
        (if (:tokens-consumed? first-reply)
          (assoc first-reply :result
            (delay
              (let [{first-error :error, :as first-result}
                      (-> first-reply :result force)]
                (if (c/success? first-result)
                  (let [{next-error :error, :as next-result}
                         (-> first-result apply-product-fn :result force)]
                    (assoc next-result :error
                      (c/merge-parse-errors first-error next-error)))
                  first-result))))
          (let [first-result (-> first-reply :result force)]
            (if (c/success? first-result)
              (let [first-error (:error first-result)
                    next-reply (apply-product-fn first-result)]
                (assoc next-reply :result
                  (delay
                    (let [next-result (-> next-reply :result force)
                          next-error (:error next-result)]
                      (assoc next-result :error
                        (c/merge-parse-errors first-error next-error))))))
              (Reply false first-result))))))))

(defmaker +
  "Creates a summed rule.
  
  Adds the given sub-rules together, forming a new rule.
  The order of the sub-rules matters.
  
  This is the FnParse *Hound* version of +. It does *not*
  backtrack.
  
  This means that it *first* searches for a successful parse from its
  subrules that *consumed any tokens*. The first such success is
  *immediately returned*.
  
  If all sub-rules that consumed tokens failed, then
  the first successful parse that *didn't* consume any
  tokens is returned.
  
  Otherwise, if every sub-rule failed, then a failure
  is returned with the proper error descriptors.
  
  This is the plus monadic operator of the `parser-m` monad."
  {:success "If *either* of the following is true:
             1. Any sub-rule both consumes tokens and succeeds.
             2. Any sub-rule succeeds without consuming any
                tokens, *and* no sub-rule that consumes tokens
                also succeeds."
   :failure "If *either* of the following is true:
             1. Any sub-rule both consumes tokens and fails.
             2. Not a single sub-rule succeeds."
   :product "The product of the succeeding sub-rule."
   :consumes "Whatever the succeeding sub-rule consumes."
   :error "An intelligent combination of the errors
                from all the failed sub-rules."}
  [& rules]
  (fn summed-rule [state]
    (let [[consuming-replies empty-replies]
            (->> rules
              (map #(c/apply state %))
              (seq/separate :tokens-consumed?))]
      (if (empty? consuming-replies)
        (if (empty? empty-replies)
          (c/apply <nothing> state)
          (let [empty-replies (seq/reductions merge-replies empty-replies)]
            (or (first (drop-while #(-> % :result force c/failure?)
                         empty-replies))
                (last empty-replies))))
        (first consuming-replies)))))

(m/defmonad parser-m
  "The monad that FnParse uses."
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
  given `label-str`. Otherwise, the old labels are
  untouched, as they contain information from
  further down the input."
  {:success "If `rule` succeeds."
   :product "`rule`'s product."
   :consumes "Whatever `rule` consumes."
   :error "Smartly determines the appropriate error message."}
  [label-str rule]
  (letfn [(assoc-label [result]
            (-> result force
              (assoc-in [:error :descriptors]
                #{(c/ErrorDescriptor :label label-str)})
              delay))]
    (fn labelled-rule [state]
      (let [reply (c/apply state rule)]
        (if-not (:tokens-consumed? reply)
          (update-in reply [:result] assoc-label)
          reply)))))

(defmaker-macro for
  "Creates a rule comprehension, very much like
  `clojure.core/for`. If it succeeds or fails and
  also how many tokens it consumes is similar to `cat`.
  How the final product is calculated is similar to `hook`.
  
  If you want to know, this macro is equivalent to the
  `clojure.contrib.monads/domonad` form of the `parser-m` monad.
  
  Arguments
  =========
  *   `label-str`: An optional label string. See the
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
  ([label-str steps product-expr]
   `(->> (for ~steps ~product-expr) (label ~label-str)))
  ([steps product-expr]
  `(m/domonad parser-m ~steps ~product-expr)))

(defmaker validate
  "Creates a validating rule.
  
  A convenience function. Returns a new rule that
  acts like the given `rule`, but also validates
  `rule`'s products with the given predicate.
  Basically just a shortcut for `for` and `only-when`."
  {:success "When `rule` succeeds and its product fulfills `(pred product)`."
   :product "`rule`'s product."
   :consumes "What `rule` consumes."
   :no-memoize? true}
  [pred message rule]
  (for [product rule, _ (only-when (pred product) message)]
    product))

(defmaker antivalidate
  "Exactly like the `validate` function, except that
  it uses the complement of `pred` instead."
  {:no-memoize? true}
  [pred message rule]
  (validate (complement pred) message rule))

(defn- term-
  "All terminal rules, including `term` and
  `term*`, are based on this function."
  [pred-product? label-str f]
  (label label-str
    (fn terminal-rule [state]
      (let [position (:position state)]
        (if-let [remainder (-> state :remainder seq)]
          (let [first-token (first remainder), f-result (f first-token)]
            (if f-result
              (Reply true
                (delay
                  (c/Success (if pred-product? f-result first-token)
                    (assoc state :remainder (next remainder)
                                 :position (inc position))
                    (c/ParseError position nil nil))))
              (make-failed-reply state first-token nil)))
          (make-failed-reply state ::c/end-of-input nil))))))

(defmaker term
  "Creates a terminal rule.
  
  The new rule either consumes one token or fails.
  It must have a `label-str` that describes it
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
    the token itself, use `term*`."
  {:success "When there's a next token, and it fulfills `(pred token)`."
   :product "The consumed token itself."
   :consumes "One token, any type that fulfills `pred`."
   :error "When `(term \"number\" num?)` fails,
           its error is \"Expected number.\""
   :no-memoize? true}
  [label-str predicate]
  (term- false label-str predicate))

(defmaker term*
  "Exactly like `term`, only its product is the result of
  `(f token)` rather than `token`."
  {:no-memoize? true}
  [label-str f]
  (term- true label-str f))

(defmaker antiterm
  "Exactly like term, only uses the complement of the
  given predicate instead."
  {:no-memoize? true}
  [label-str pred]
  (term label-str (complement pred)))

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
  (for [product rule] (semantic-hook product)))

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
  [product subrule]
  (for [_ subrule] product))

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
  A shortcut for `(term label-str (set tokens))`."
  [label-str tokens]
  (term label-str (set tokens)))

(defmaker antiset-lit
  "Creates a terminal rule with an antiset.
  A shortcut for `(antiterm label-str (set tokens))`."
  [label-str tokens]
  (antiterm label-str (set tokens)))

(defmaker cat
  "Creates a concatenated rule out of many given `rules`."
  {:success "All given `rules` succeed, one after another."
   :product "The sequence (not lazy) of all the `rules`'s respective products."
   :consumes "All tokens that the `rules` sequentially consume."
   :error "The error of whatever sub-rule failed."}
  [& rules]
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
  (+ rule <emptiness>))

(defmaker lex
  "Creates a lexical rule.
  You use this whenever you want the lexer to
  *backtrack* when it fails, *even* if it consumes
  tokens. (Don't forget, usually *if a rule consumes
  tokens, it cannot backtrack at all*.)
  
  How it works
  ============
  Rules surrounded by lex count as 'empty' rules—
  rules that don't consume any tokens—regardless
  if they really consume tokens or not. This changes
  the behavior of any summed rules that contain it.
  
  Why you would need to use it
  ============================
    (require '[edu.arizona.fnparse.hound :as r])
    (def <ws> (r/lit \\space))
    (def <claim> (r/phrase \"x = 1\"))
    (def <let-expr> (r/cat (r/phrase \"let\") <ws> <let-expr>))
    (def <identifier> (r/rep r/<ascii-letter>))
    (def <expr> (r/+ <let-expr> <identifier>))
    (parse <let-expr> \"number\" nil) ; Line one
    (parse <let-expr> \"letter\" nil) ; Line two
  
  In the code above, line one will give a successful
  parse, because the input \"number\" matches
  <indentifier>.
  
  But line two will give a failure. This is because
  (r/phrase \"let\") will match, but the <ws> after it
  will not match. Thus, <let-expr> fails. Also, because
  <let-expr> consumed the first three tokens of \"letter\",
  the summed rule <expr> will immediately fail without
  even trying <identifier-.
  
  And so how you use it
  =====================
  Change <let-expr> to use the following:
    (r/cat (r/lex (r/phrase \"let\")) <ws> <let-expr>)
  Now both line one and two will be successful."
  [subrule]
  (fn [state]
    (-> state subrule
      (assoc :tokens-consumed? false))))

(defmaker peek
  "Creates a lookahead rule. Checks if the given
  `rule` succeeds, but doesn't actually consume
  any tokens."
  {:success "If `rule` succeeds."
   :consumes "No tokens."}
  [rule]
  (fn [state]
    (let [result (-> state (c/apply rule) :result force)]
      (if (c/failure? result)
        (Reply false result)
        ((prod (:product result)) state)))))

(defmaker antipeek
  "Creates a negative lookahead rule. Checks if
  the given `rule` fails, but doesn't actually
  consume any tokens. You must provide a `label-str`
  describing this rule."
  {:success "If `rule` succeeds."
   :product "Always `true`."}
  [label-str rule]
  (label label-str
    (fn antipeek-rule [state]
      (let [result (-> state (c/apply rule) :result force)]
        (if (c/failure? result)
          (Reply false (c/Success true state (:error result)))
          (-> state (c/apply <nothing>)))))))

(defn- apply-reply-and-rule [f prev-reply next-rule]
  (c/apply nil
    (combine (constantly prev-reply)
      (fn [prev-product]
        (combine next-rule
          (fn [next-product]
            (prod (f prev-product next-product))))))))

(defn- hooked-rep- [reduced-fn initial-product-fn rule]
  (let [apply-reduced-fn (partial apply-reply-and-rule reduced-fn)]
    (fn hooked-repeating-rule [state]
      (let [initial-product (initial-product-fn)
            first-fn (partial reduced-fn initial-product)
            first-reply (c/apply state (hook first-fn rule))]
        (if (:tokens-consumed? first-reply)
          (Reply true
            (delay
              (let [[last-success first-failure]
                    (->> rule repeat
                      (seq/reductions apply-reduced-fn first-reply)
                      (partition 2 1)
                      (take-while #(-> % first :result force c/success?))
                      last)]
                (-> last-success :result force
                  (assoc :error (-> first-failure :result force :error))))))
          (if (-> first-reply :result force c/success?)
            (except/throwf "empty rules cannot be greedily repeated")
            first-reply))))))

(defmaker hooked-rep
  "A `reduce`-like version of `rep`. See `rep` for more info.
  
  `f` should be a function of two arguments. The
  product is the result of applying `f` first to
  `initial-product` and the product of `rule`'s
  first match, then applying `f` to that result and
  the product of `rule`'s second match, and so on.
  
  Why would you use this instead of `(->> rule rep
  (hook #(reduce f initial-product %)))`? Because
  this saves memory. Using `rep` and `hook` instead
  forces the entire repetition's product to be in
  memory at the start, which may be prohibitive for
  potentially large repititions.
  
  *Warning!* Do not use this with any rules that
  possibly may succeed without consuming any tokens.
  An error will be thrown, because it doesn't make sense."
  {:no-memoize? true
   :success "If rule succeeds at least once."
   :consumes "As many tokens as rule can consecutively consume."
   :product "`(reduce f initial-product seq-of-consecutive-rule-products)`."}
  [f initial-product rule]
  (hooked-rep- f (constantly initial-product) rule))

(defmaker rep
  "Creates a one-or-more greedy repetition rule. Tries to
  repeat consecutively the given `rule` as many
  times as possible.
  
  *Warning!* Do not use this with any rules that
  possibly may succeed without consuming any tokens.
  An error will be thrown, because it doesn't make sense."
  {:success "If rule succeeds at least once."
   :consumes "As many tokens as rule can consecutively consume."
   :product "A *vector* of all of `rule`'s consecutive products."}
  [rule]
  (->> rule (hooked-rep- conj! #(transient [])) (hook persistent!)))

(defmaker rep*
  "Creates a zero-or-more greedy repetition rule.
  
  *Warning!* Do not use this with any rules that
  possibly may succeed without consuming any tokens.
  An error will be thrown, because it doesn't make sense."
  {:success "If rule succeeds at least once."
   :consumes "As many tokens as rule can consecutively consume."
   :product "A *vector* of all of `rule`'s consecutive products.
             If `rule` fails immediately, then this is `[]`."}
  [rule]
  (+ (rep rule) (prod [])))

(defmaker mapcat
  "Creates a rule that is the result of
  applying `cat` to the result of applying map
  to `f` and `colls`.
  Use the `phrase` function instead of this
  function when `f` is just `lit`."
  [f & token-colls]
  (->> token-colls (apply map f) (apply cat)))

(defmaker mapsum
  "Creates a rule that is the result of applying `+` to the
  result of applying map to `f` and `colls`.
  Use the `set-term` function instead of this
  function when `f` is just `lit`."
  [f & token-colls]
  (->> token-colls (apply map f) (apply +)))

(defmaker phrase
  "Creates a phrase rule, which succeeds
  only when the next few tokens all
  consecutively match the given tokens.
  (Actually, it's just `(mapcat lit tokens)`.)"
  [tokens]
  (mapcat lit tokens))

(defrule <end-of-input>
  "The standard end-of-input rule."
  {:succeeds "If there are no tokens left."
   :product "`true`."
   :consumes "No tokens."}
  (antipeek "the end of input" <anything>))

(defmaker prefix
  "Creates a prefixed rule. Use when you want to
  concatenate two rules, but you don't care about
  the first rule's product.
  Its product is always the body-rule's product.
  A shortcut for `(for [_ prefix-rule, content body-rule] content)`."
  [prefix-rule body-rule]
  (for [_ prefix-rule, content body-rule] content))

(defmaker suffix [body-rule suffix-rule]
  "Creates a suffixed rule. Use when you want to
  concatenate two rules, but you don't care about
  the second rule's product.
  Its product is always the body-rule's product.
  A shortcut for `(for [content body-rule, _ suffix-rule] content)`."
  (for [content body-rule, _ suffix-rule] content))

(defmaker circumfix
  "Creates a circumfixed rule. Use when you want to
  concatenate three rules, but you don't care about
  the first and third rules' products.
  Its product is always the body-rule's product.
  A shortcut for `(prefix prefix-rule (suffix body-rule suffix-rule))`."
  [prefix-rule body-rule suffix-rule]
  (prefix prefix-rule (suffix body-rule suffix-rule)))

(defmaker separated-rep
  "Creates a greedy repetition rule with a separator.
  The `separator` is a rule that must succeed between
  each `element` success."
  {:success "If `element` succeeds at least once."
   :product "The vector of `element`'s successes."}
  [separator element]
  (for [first-element element
        rest-elements (rep* (prefix separator element))]
    (into [first-element] rest-elements)))

(defmaker-macro template-sum
  "Creates a summed rule using a template.
  Acts very similarly to `clojure.template/do-template`,
  but instead sums each rule together."
  [argv expr & values]
  (let [c (count argv)]
   `(+ ~@(map (fn [a] (t/apply-template argv expr a))
           (partition c values)))))

(defmaker case-insensitive-lit
  "Creates a case-insensitive rule using Java's
  `Character/toLowerCase` and `Character/toUpperCase`
  methods. Only works with `Character`-type tokens."
  {:succeeds "If there is a next token and it's equal to either
              the upper or lowercase of the given `token`."
   :consumes "One character."}
  [#^Character token]
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
  (fn effects-rule [state]
    (c/apply state (prod (apply f args)))))

(defmaker except
  "Creates a subtracted rule. Matches using
  the given minuend rule, but only when the
  subtrahend rule does not also match. You
  must provide a custom `label-str`."
  {:success "If `minuend` succeeds and `subtrahend` fails."
   :product "`minuend`'s product."
   :consumes "Whatever `minuend` consumes."
   :error "Uses the `label-str` you provide."}
  ([label-str minuend subtrahend]
   (for [_ (antipeek label-str subtrahend)
         product (label label-str minuend)]
     product))
  ([label-str minuend first-subtrahend & rest-subtrahends]
   (except label-str minuend
     (apply + (cons first-subtrahend rest-subtrahends)))))

(defmaker annotate-error
  "Creates an error-annotating rule. Whenever
  the given `rule` fails, the error is passed
  into the `message-fn` function. This can be
  useful to add a message with more info to an
  error when certain conditions are met.
  
  `message-fn` must return a string when given
  the original `ParseError`, which will be added
  to the `ParseError`.
  `ParseError`s are maps of type
  `:edu.arizona.fnparse/ParseError`.
  See its documentation for more information."
  [message-fn rule]
  (letfn [(annotate [result]
            (delay (let [{error :error, :as forced-result} (force result)
                         new-message (message-fn error)]
                     (if new-message
                       (update-in forced-result [:error :descriptors]
                         conj (c/ErrorDescriptor :message new-message))
                       forced-result))))]
    (fn error-annotation-rule [state]
      (let [reply (c/apply state rule)]
        (update-in reply [:result] annotate)))))

(defmaker factor=
  "Creates a non-greedy repetition rule.
  Concatenates the given `rule` to itself `n` times."
  [n rule]
  (->> rule (replicate n) (apply cat)))

(defrule <fetch-context>
  "A rule that fetches the current context."
  {:success "Always."
   :product "The current context."
   :consumes "Zero tokens."}
  (fn fetch-context-rule [state]
    (c/apply state (prod (:context state)))))

(defn alter-context
  "A rule that alters the curent context."
  {:success "Always."
   :product "The current context."
   :consumes "Zero tokens."
   :no-memoize? true}
  [f & args]
  (fn context-altering-rule [state]
    (let [altered-state (apply update-in state [:context] f args)]
      (c/apply altered-state <fetch-context>))))

(def ascii-digits "0123456789")
(def lowercase-ascii-alphabet "abcdefghijklmnopqrstuvwxyz")
(def uppercase-ascii-alphabet
  (map #(Character/toUpperCase (char %)) lowercase-ascii-alphabet))
(def base-36-digits (concat ascii-digits lowercase-ascii-alphabet))
(def base-36-digit-map
  (letfn [(digit-entries [[index digit-char]]
            (let [digit-char (char digit-char)]
              [[(Character/toUpperCase digit-char) index]
               [(Character/toLowerCase digit-char) index]]))]
    (->> base-36-digits seq/indexed (seq-mapcat digit-entries) (into {}))))

(defn radix-label
  "The function used by radix-digit to smartly
  create digit labels for the given `base`."
  [base]
  (case base
    10 "a decimal digit"
    16 "a hexadecimal digit"
    8 "an octal digit"
    2 "a binary digit"
    (format "a base-%s digit" base)))

(defmaker radix-digit
  "Returns a rule that accepts one digit character
  token in the number system with the given `base`.
  For instance, `(radix-digit 12)` is a rule
  of a single duodecimal digit.
  
  Digits past 9 are case-insensitive letters:
  11, for instance, is \\b or \\B. Bases above
  36 are accepted, but there's no way to use
  digits beyond \\Z (which corresponds to 36).
  
  The rules `<decimal-digit>` and
  `<hexadecimal-digit>` are already provided."
  {:succeeds "If the next token is a digit
    character in the given `base`'s number
    system."
   :product "The digit's corresponding integer."
   :consumes "One character."}
  [base]
  {:pre #{(integer? base) (> base 0)}}
  (->> base-36-digit-map (filter #(< (val %) base)) (into {})
    (term* (radix-label base))))

(defrule <decimal-digit>
  "A rule matching a single base-10 digit
  character token (i.e. \\0 through \\9)."
  {:product "The matching digit's corresponding Integer object, 0 through 9."
   :consumes "One character."}
  (radix-digit 10))

(defrule <hexadecimal-digit>
  "A rule matching a single base-16 digit
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
