(ns name.choi.joshua.fnparse.hound
  (:require [name.choi.joshua.fnparse.common :as c]
            [clojure.contrib.seq :as seq]
            [clojure.contrib.monads :as m]
            [clojure.template :as t]
            [clojure.contrib.def :as d])
  (:refer-clojure :rename {defn define-fn, defn- define-fn-, mapcat seq-mapcat}
                  :exclude #{for + peek})
  (:import [clojure.lang IPersistentMap]))

(deftype State [remainder position context] :as this
  IPersistentMap
  c/AState
    (position [] (:position this)))

(deftype Reply [tokens-consumed? result] :as this
  IPersistentMap
  c/AParseAnswer (answer-result [] (-> this :result force)))

(define-fn make-state
  "Creates a state with the given remainder and context."
  [remainder context]
  (State remainder 0 context))

(define-fn parse
  "The general parsing function of FnParse Hound.
  
  *   `rule`: The rule. It must accept whatever state that
      make-state returns.
  *   `input`: The sequence of tokens to parse.
  *   `context`: The initial context for the rule.
  *   `success-fn`: A function called when the rule matches
      the input. `(success-fn final-product final-position)`
      is called.
  *   `failure-fn`: A function called when the rule does not
      match the input. `(failure-fn final-error)` is called."
  [rule input context success-fn failure-fn]
  (c/parse make-state rule input context success-fn failure-fn))

(define-fn format-parse-error [error]
  (c/format-parse-error error))

(define-fn merge-replies [mergee merger]
  (assoc merger :result
    (update-in (-> merger :result force) [:error]
      c/merge-parse-errors (-> mergee :result force :error))))

(define-fn prod
  "Creates a product rule.
  *   Succeeds? Always.
      *   Product: The given `product`.
      *   Consumes: Zero tokens.
  *   Fails? Never.
  
  Use the :let modifier in preference to this function
  when you use this inside rule comprehensions with the
  for macro.
  
  Is the result monadic function of the parser monad."
  [product]
  (fn prod-rule [state]
    (Reply false
      (c/Success product state
        (c/ParseError (:position state) nil nil)))))

(d/defvar <emptiness> (prod nil)
  "The general emptiness rule.
  
  *   Succeeds? Always.
      *   Product: `nil`.
      *   Consumes: Zero tokens.
  *   Fails? Never.
  
  Happens to be equivalent to `(prod nil)`.")

(define-fn- make-failed-reply
  "Used to create replies containing failures."
  ([state descriptors]
   (make-failed-reply state (first (:remainder state)) descriptors))
  ([state unexpected-token descriptors]
   (Reply false
     (c/Failure
       (c/ParseError (:position state) unexpected-token descriptors)))))

(d/defvar nothing-descriptors
  #{(c/ErrorDescriptor :label "absolutely nothing")}
  "The error descriptors that `-nothing-` uses.")

(define-fn <nothing>
  "The general failing rule.
  
  *   Succeeds? Never.
  *   Fails? Always.
      *   Labels: \"absolutely nothing\"
      *   Message: None.
  
  Use `with-error` in preference to this rule,
  because 
  
  Is the zero monadic value of the parser monad."
  [state]
  (make-failed-reply state nothing-descriptors))

(define-fn with-error
  "Creates an always-failing rule with the given
  message. Use this in preference to <nothing-.
  
  *   Succeeds? Never.
  *   Fails? Always.
      *   Labels: None.
      *   Message: The given `message`."
  [message]
  (fn with-error-rule [state]
    (make-failed-reply state #{(c/ErrorDescriptor :message message)})))

(letfn [(delayify [f] (fn [& args] (delay (force (apply f args)))))]
  (defmacro defn
    "Creates a rule-making function. Use this instead of
    `clojure.core/defn` whenever you make a rule-making
    function. (It does other stuff like memoization and
    delaying and stuff.)"
    [fn-name & forms]
   `(do (d/defn-memo ~fn-name ~@forms)
        (alter-var-root (var ~fn-name) ~delayify)
        (var ~fn-name))))

(defmacro defn-
  "Like `defn`, but also makes the var private."
  [fn-name & forms]
  (list* `defn (vary-meta fn-name assoc :private true) forms))

(defn only-when
  "Creates a maybe-failing rule.
  
  *   Succeeds? Only if the given `valid?` is
      logical true.
      *   Product: `valid?`.
      *   Consumes: Zero tokens.
  *   Fails? Only if not `valid?`.
      *   Labels: None.
      *   Messages: The given `message`.
  It creates an either succeeding or a failing rule,
  depending on if `valid?` is logical true. If
  `valid?`, then the rule always succeeds and acts
  like `(prod valid?)`. If not `valid?`, then the
  rule always fails and acts like `(with-error message)`.
  
  This function is very useful for when you want
  to validate a certain rule. For instance:
      (for [value <number>
            _ (only-when (< odd 10)
                \"number must be less than ten\")]
        value)
  The example above succeeds only when `-number-`
  matches and its product is less than 10."
  [valid? message]
  (if-not valid? (with-error message) (prod valid?)))

(define-fn combine
  "Creates a rule combining the given `rule` into the
  `product-fn`.
  
  *Use `cat` or `for` instead* of this function.
  You *shouldn't have to use this function*
  at all, unless you're doing something special.

  The product-fn must return a rule when given the
  product of the first rule. `combine` is the bind
  monadic function of the parser monad.
  
  Below, the rule returned by `(product-fn
  state-after-first-rule)` will be referred to as
  `second-rule`.
  
  *   Succeeds? If both `rule` and `second-rule` succeed.
      *   Product: The product of `second-rule`.
      *   Consumes: All the tokens that `rule` and then
          `second-rule` consume.
  *   Fails? If either `rule` or `second-rule` fail.
      *   Labels and messages: Whatever the failed rule
          gives."
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

(defn +
  "Creates a summed rule.
  
  Adds the given sub-rules together, forming a new rule.
  The order of the sub-rules matters.
  
  *This is the FnParse Hound version of +.* It does *not*
  backtrack.
  
  This means that it *first* searches for a successful parse from its
  subrules that *consumed any tokens*. The first such success is
  *immediately returned*.
  
  If all sub-rules that consumed tokens failed, then
  the first successful parse that *didn't* consume any
  tokens is returned.
  
  Otherwise, if every sub-rule failed, then a failure
  is returned with the proper error descriptors.
  
  This is the plus monadic operator of the parser monad.
  
  *   Success?
      *   If *either* of the following is true:
          1. Any sub-rule both consumes tokens and succeeds.
          2. Any sub-rule succeeds without consuming any
             tokens, *and* no sub-rule that consumes tokens
             also succeeds.
      *   The first sub-rule that fulfills #1, or else #2,
          above is used.
      *   Product: The product of that first sub-rule.
      *   Consumes: Whatever tokens that first sub-rule
          consumes too.
  *   Failure?
      *   If *either* of the following is true:
          1. Any sub-rule both consumes tokens and fails.
          2. Not a single sub-rule succeeds.
      *   Descriptors: The descriptors of all failed rules
          are combined in an intelligent way."
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

(define-fn label
  "Creates a labelled rule.
  
  Labels the given rule with the given string, returning
  a new rule. The given label will appear in the descriptors
  of any parse errors that expected the given rule to
  succeed.
  
  *   Success? If `rule` succeeds.
      *   Product: `rule`'s product.
      *   Consumes: Whatever `rule` consumes.
  *   Failure? If `rule` fails.
      *   Labels: All of `rule`'s labels are overrided
          with `label-str`, but only if `rule` consumed
          no tokens. (If `rule` did consume tokens, then
          its labels contain more specific information
          than `label-str`.)
      *   Messages: Whatever `rule` returns."
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

(defmacro for
  "Creates a rule comprehension, very much like
  `clojure.core/for`.
  
  Arguments
  =========
  *   label-str: An optional label string. See the
      label function for more info.
  *   steps: A binding vector containing binding-form/
      rule pairs followed by optional modifiers.
      The given rules in each pair are conca>
      tenated together in sequence to create
      the new rule. Each binding-form is bound
      to the product of its corresponding rule.
      The rule expressions can refer to any
      symbol bound to in a previous pair.
      The only current recommended modifier
      is `:let`, which works like how it does it
      `clojure.core/for`.
  *   product-expr: The final product of the new rule.
      Only is reached after every sub-rule
      succeeds. The expression can refer
      to any symbol bound to in the `steps`.
  
  Rule behaviour
  ==============
  If it succeeds or fails and also how many tokens
  it consumes is similar to `cat`. How the final
  product is calculated is similar to `hook`.
  *   Success: All sub-rules in the `steps`
      succeed, in order.
      *   Product: Whatever is calculated by
          `product-expr`.
      *   Consumes: All tokens that each step
          consumes.
  *   Failure: Any sub-rule in the `steps` fails.
      *   Labels and messages: Whatever is
          returned by the failed rule.
  
  Miscellaneous info
  ==================
  For examples of for rules, check the example
  libraries like `fnparse.clojure`.
  
  This macro is equivalent to the domonad form of
  the parser monad."
  ([label-str steps product-expr]
   `(->> (for ~steps ~product-expr) (label ~label-str)))
  ([steps product-expr]
  `(m/domonad parser-m ~steps ~product-expr)))

(define-fn validate
  "Creates a validating rule.
  
  A convenience function. Returns a new rule that
  acts like the given `rule`, but also validates
  `rule`'s products with the given predicate.
  Basically just a shortcut for `for` and `only-when`.
  
  *   Success: When `rule` succeeds and its product
      fulfills `(pred product)`.
      *   Product: `rule`'s product.
      *   Consumes: What `rule` consumes.
  *   Failure: When `rule` fails or `(pred product)`
      is false."
  [pred message rule]
  (for [product rule, _ (only-when (pred product) message)]
    product))

(define-fn antivalidate
  "Exactly like the validate function, except that
  it uses the complement of pred instead."
  [pred message rule]
  (validate (complement pred) message rule))

(define-fn- term>
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

(define-fn term
  "Creates a terminal rule.
  
  The new rule either consumes one token or fails.
  It must have a `label-str` that describes it
  and a `pred`icate to test if the token it consumes is
  valid.
  
  *   Success: When there are still tokens left in
      the input, and the next such token fulfills
      `(pred token)`.
      *   Product: The consumed token.
      *   Consumes: One and only one token.
  *   Failure: When there are no tokens left, or
      `(pred next-token)` is false.
      *   Labels: The given `label-str`.
      *   Messages: None.
  
  Notes
  =====
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
  [label-str predicate]
  (term> false label-str predicate))

(define-fn term*
  "Exactly like term, only its product is the result of
  `(f token)` rather than `token`."
  [label-str f]
  (term> true label-str f))

(define-fn antiterm
  "Exactly like term, only uses the complement of the
  given predicate instead."
  [label-str pred]
  (term label-str (complement pred)))

(d/defvar <anything> (term "anything" (constantly true))
  "The generic terminal rule. It consumes one token.
  
  *   Success: If there are any tokens left.
      *   Product: The token it consumes.
      *   Consumes: One token.
  *   Failure: If it's at the end of input.")

(define-fn hook
  "Creates a rule with a semantic hook.
  A shortcut for the `for` macro.
  
  *   Success: If `rule` succeeds.
      *   Product: `(semantic-hook rule-product)`.
      *   Consumes: Whatever `rule` consumes.
  *   Failure: If `rule` fails."
  [semantic-hook rule]
  (for [product rule] (semantic-hook product)))

(define-fn chook
  "Creates a rule with a constant semantic hook.
  A shortcut for the for macro. The name
  stands for 'constant-hook'. It's exactly like
  hook, only the product is a constant; its
  product is always the given object.
  
  *   Success: If `rule` succeeds.
      *   Product: Always is `product`.
      *   Consumes: Whatever `rule` consumes.
  *   Failure: If `rule` fails."
  [product subrule]
  (for [_ subrule] product))

(define-fn lit
  "Creates a rule of a literal. A shortcut for
  the term function. It automatically adds an
  appropriate label.
  
  *   Success? If there are tokens left, and
      the first remaining token is equal to
      the given `token`.
      *   Product: The consumed token.
      *   Consumes: One token.
  *   Failure? If it's at the end of input, or
      the next token is not equal to the given
      `token`.
      *   Labels: The given `token` in single>
          quotes. For instance, (lit \\$) has
          the label `\"'$'\"`."
  [token]
  (term (format "'%s'" token) #(= token %)))

(define-fn antilit
  "Creates a rule of an antiliteral.
  A shortcut for the term function. It consumes
  one token, and succeeds only if it *does not
  Its product is the consumed token.
  equal* the given token. It fails otherwise.
  It automatically adds an appropriate label
  (e.g. `(antilit \\$)` is labelled
  `\"anything except '$'\")."
  [token]
  (term (format "anything except '%s'" token) #(not= token %)))

(define-fn set-term
  "Creates a terminal rule with a set.
  A shortcut for `(term label-str (set tokens))`."
  [label-str tokens]
  (term label-str (set tokens)))

(define-fn antiset-lit
  "Creates a terminal rule with an antiset.
  A shortcut for `(antiterm label-str (set tokens))`."
  [label-str tokens]
  (antiterm label-str (tokens set)))

(define-fn cat
  "Creates a concatenated rule out of many given `rules`.
  
  *   Success: All given `rules` succeed, one after another.
      *   Product: The sequence of all the `rules`'
          respective products.
      *   Consumes: All tokens that each rule in `rules`
          consecutively consumes.
  *   Failure: Any rule in the `rule` fails at its
      respective position.
      *   Labels and messages: Whatever is
          returned by the failed rule."
  [& rules]
  (m/with-monad parser-m
    (m/m-seq rules)))

(define-fn vcat
  "Exactly like cat, only applies vec to its product."
  [& subrules]
  (hook vec (apply cat subrules)))

(define-fn opt
  "Creates an optional rule. The new rule
  always succeeds. It is equivalent to the
  sum of the given rule and `-emptiness-`.
  
  *   Success: Always.
      *   Product: If `rule` succeeds, whatever
          product `rule` gives. Otherwise, `nil`.
      *   Consumes: If `rule` succeeds, whatever
          `rule` consumed. Otherwise, nothing is
          consumed.
  *   Failure: Never."
  [rule]
  (+ rule <emptiness>))

(define-fn lex
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
    (require '[name.choi.joshua.fnparse.hound :as r])
    (def <ws> (r/lit \\space))
    (def <claim> (r/phrase \"x = 1\"))
    (def <let-expr> (r/cat (r/phrase \"let\") <ws> <let-expr>))
    (def <identifier> (r/rep+ r/<ascii-letter>))
    (def <expr> (r/+ <let-expr> <identifier>))
    (parse <let-expr> \"number\" nil) ; Line one
    (parse <let-expr> \"letter\" nil) ; Line two
  In the code above, line one will give a successful
  parse, because the input \"number\" matches
  <indentifier-.
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

(define-fn peek
  "Creates a lookahead rule. Checks if the given
  `rule` succeeds, but doesn't actually consume
  any tokens.
  
  *   Success? If `rule` succeeds.
      *   Product: `rule`'s product.
      *   Consumes: Zero tokens.
  *   Failure? If `rule` fails."
  [rule]
  (fn [state]
    (let [result (-> state (c/apply rule) :result force)]
      (if (c/failure? result)
        (Reply false result)
        ((prod (:product result)) state)))))

(define-fn antipeek
  "Creates a negative lookahead rule. Checks if
  the given `rule` fails, but doesn't actually
  consume any tokens. You must provide a `label-str`
  describing this rule.
  
  *   Success? If `rule` fails.
      *   Product: `true`.
      *   Consumes: Zero tokens.
  *   Failure? If `rule` succeeds.
      *   Labels: Uses the given `label-str`."
  [label-str rule]
  (label label-str
    (fn antipeek-rule [state]
      (let [result (-> state (c/apply rule) :result force)]
        (if (c/failure? result)
          (Reply false (c/Success true state (:error result)))
          (-> state (c/apply <nothing>)))))))

(define-fn cascading-rep+ [rule unary-hook binary-hook]
  ; TODO: Rewrite to not blow up stack with many valid tokens
  (for [first-token rule
        rest-tokens (opt (cascading-rep+ rule unary-hook binary-hook))]
    (if (nil? rest-tokens)
      (unary-hook first-token)
      (binary-hook first-token rest-tokens))))

(define-fn rep+ [rule]
  ; TODO: Rewrite to not blow up stack with many valid tokens
  (cascading-rep+ rule list cons))

; (define-fn rep* [rule]
;   (with-monad parser-m
;     (m-seq-while (complement failure?) (repeat 10 rule))))

(define-fn rep* [rule]
  (opt (rep+ rule)))

(define-fn mapcat
  "Returns the result of applying `cat` to the
  result of applying map to `f` and `colls`.
  Use the `phrase` function instead of this
  function when `f` is just `lit`."
  [f & token-colls]
  (->> token-colls (apply map f) (apply cat)))

(define-fn mapsum
  "Returns the result of applying `+` to the
  result of applying map to `f` and `colls`.
  Use the `set-term` function instead of this
  function when `f` is just `lit`."
  [f & token-colls]
  (->> token-colls (apply map f) (apply +)))

(define-fn phrase
  "Returns a phrase rule, which succeeds
  only when the next few tokens all
  consecutively match the given tokens.
  Actually, it's just `(mapcat lit tokens)`."
  [tokens]
  (mapcat lit tokens))

(d/defvar <end-of-input>
  (antipeek "the end of input" <anything>)
  "The standard end-of-input rule.
  
  *   Success? If there are no tokens left.
      *   Product: `true`.
      *   Consumes: Zero tokens.
  *   Failure? If there are any tokens left.")

(define-fn prefix
  "Creates a prefixed rule. Use when you want to
  concatenate two rules, but you don't care about
  the first rule's product.
  Its product is always the body-rule's product.
  A shortcut for:
    (for [_ prefix-rule, content body-rule] content)."
  [prefix-rule body-rule]
  (for [_ prefix-rule, content body-rule] content))

(define-fn suffix [body-rule suffix-rule]
  "Creates a suffixed rule. Use when you want to
  concatenate two rules, but you don't care about
  the second rule's product.
  Its product is always the body-rule's product.
  A shortcut for:
    (for [content body-rule, _ suffix-rule] content)."
  (for [content body-rule, _ suffix-rule] content))

(define-fn circumfix
  "Creates a circumfixed rule. Use when you want to
  concatenate three rules, but you don't care about
  the first and third rules' products.
  Its product is always the body-rule's product.
  A shortcut for:
    (prefix prefix-rule (suffix body-rule suffix-rule))."
  [prefix-rule body-rule suffix-rule]
  (prefix prefix-rule (suffix body-rule suffix-rule)))

(define-fn separated-rep [separator element]
  (for [first-element element
        rest-elements (rep* (prefix separator element))]
    (cons first-element rest-elements)))

(defmacro template-sum
  "Creates a summed rule using a template.
  Acts very similarly to `clojure.template/do-template`,
  but instead sums each rule together."
  [argv expr & values]
  (let [c (count argv)]
   `(+ ~@(map (fn [a] (t/apply-template argv expr a))
           (partition c values)))))

(define-fn case-insensitive-lit
  "Creates a case-insensitive rule using Java's
  `Character/toLowerCase` and `Character/toUpperCase`
  methods. Only works with `Character`-type tokens.
  
  *   Succeeds? If there is a next token and it's
      equal to either the lower> or upper-case of
      the given `token`.
      *   Product: The consumed token.
      *   Consumes: One token.
  *   Failure? If there are no more tokens or if
      the next token doesn't equal the upper> or
      lower-case of the given `token`."
  [#^Character token]
  (+ (lit (Character/toLowerCase token))
     (lit (Character/toUpperCase token))))

(define-fn effects
  "Creates a side-effect rule. Applies the given
  arguments to the given function.
  
  *   Succeeds? Always.
      *   Product: The result of `(apply f args)`.
      *   Consumes: No tokens.
  *   Failure? Never."
  [f & args]
  (fn effects-rule [state]
    (c/apply state (prod (apply f args)))))

(define-fn except
  "Creates a subtracted rule. Matches using
  the given minuend rule, but only when the
  subtrahend rule does not also match.
  
  *   Succeeds? `minuend` succeeds and
      `subtrahend` fails.
      *   Product: `minuend`'s product.
      *   Consumes: Whatever `minuend` consumes.
  *   Fails? `minuend` fails or `subtrahend`
      succeeds."
  ([label-str minuend subtrahend]
   (for [_ (antipeek label-str subtrahend)
         product (label label-str minuend)]
     product))
  ([label-str minuend first-subtrahend & rest-subtrahends]
   (except label-str minuend
     (apply + (cons first-subtrahend rest-subtrahends)))))

(define-fn annotate-error
  "Creates an error-annotating rule. Whenever
  the given `rule` fails, the error is passed
  into the `message-fn` function. This can be
  useful to add a message with more info to an
  error when certain conditions are met.
  
  The result that `message-fn` receives is of the
  type `::name.choi.joshua.fnparse.common/ParseError`.
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

(define-fn factor=
  "Creates a non-greedy repetition rule.
  Concatenates the given `rule` to itself `n` times."
  [n rule]
  (->> rule (replicate n) (apply cat)))

(define-fn <fetch-context>
  "A rule that fetches the current context.
  
  *   Success? Always.
      *   Product: The current context.
      *   Consumes: Zero tokens.
  *   Failure? Never."
  [state]
  (c/apply state (prod (:context state))))

(define-fn alter-context
  "A rule that alters the curent context.
  
  *   Success? Always.
      *   Product: The new context.
      *   Consumes: Zero tokens.
  *   Failure? Never."
  [f & args]
  (fn context-altering-rule [state]
    (let [altered-state (apply update-in state [:context] f args)]
      (c/apply altered-state <fetch-context>))))

(def ascii-digits "0123456789")
(def lowercase-ascii-alphabet "abcdefghijklmnopqrstuvwxyz")
(def uppercase-ascii-alphabet
  (map #(Character/toUpperCase %) lowercase-ascii-alphabet))
(def base-36-digits (concat ascii-digits lowercase-ascii-alphabet))
(set! *warn-on-reflection* true)
(def base-36-digit-map
  (letfn [(digit-entries [[index digit-char]]
            (let [digit-char (char digit-char)]
              [[(Character/toUpperCase digit-char) index]
               [(Character/toLowerCase digit-char) index]]))]
    (->> base-36-digits seq/indexed (seq-mapcat digit-entries) (into {}))))

(define-fn radix-label
  "The function used by radix-digit to smartly
  create digit labels for the given `base`."
  [base]
  (case base
    10 "a decimal digit"
    16 "a hexadecimal digit"
    8 "an octal digit"
    2 "a binary digit"
    (format "a base-%s digit" base)))

(defn radix-digit
  "Returns a rule that accepts one digit character
  token in the number system with the given `base`.
  For instance, `(radix-digit 12)` is a rule
  of a single duodecimal digit.
  
  Digits past 9 are case-insensitive letters:
  11, for instance, is \\b or \\B. Bases above
  36 are accepted, but there's no way to use
  digits beyond \\Z (which corresponds to 36).
  
  The rules `-decimal-digit-` and
  `-hexadecimal-digit-` are already provided.
  
  *   Success? If the next token is a digit
      character in the given `base`'s number
      system.
      *   Product: The digit's corresponding
          integer.
      *   Consumes: One token."
  [base]
  {:pre #{(integer? base) (> base 0)}}
  (->> base-36-digit-map (filter #(< (val %) base)) (into {})
    (term* (radix-label base))))

(d/defvar <decimal-digit>
  (radix-digit 10)
  "A rule matching a single base-10 digit
  character token (i.e. \\0–\\9). Its product
  is the digit's corresponding integer.")

(d/defvar <hexadecimal-digit>
  (radix-digit 16)
  "A rule matching a single base-16 digit
  character token (i.e. \\0–\\F). Its product
  is the digit's corresponding integer.")

(d/defvar <uppercase-ascii-letter>
  (set-term "an uppercase ASCII letter" uppercase-ascii-alphabet)
  "A rule matching a single uppercase ASCII letter.")

(d/defvar <lowercase-ascii-letter>
  (set-term "a lowercase ASCII letter" lowercase-ascii-alphabet)
  "A rule matching a single lowercase ASCII letter.")

(d/defvar <ascii-letter>
  (label "an ASCII letter"
    (+ <uppercase-ascii-letter> <lowercase-ascii-letter>))
  "A rule matching a single upper> or lower-case ASCII letter.")

(d/defvar <ascii-alphanumeric>
  (label "an alphanumeric ASCII character"
    (+ <ascii-letter> <decimal-digit>))
  "A rule matching an ASCII alphanumeric character.")
