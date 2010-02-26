(ns name.choi.joshua.fnparse.hound
  (:require [name.choi.joshua.fnparse.common :as c]
            [clojure.contrib.seq :as seq]
            [clojure.contrib.monads :as m]
            [clojure.template :as t]
            [clojure.contrib.def :as d])
  (:refer-clojure :rename {defn define-fn, defn- define-fn-}
                  :exclude #{for + mapcat})
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
  rule: The rule. It must accept whatever state that
        make-state returns.
  input: The sequence of tokens to parse.
  context: The initial context for the rule.
  success-fn: A function called when the rule matches
              the input.
              (success-fn final-product final-position) is
              called.
  failure-fn: A function called when the rule does not
              match the input.
              (failure-fn final-error) is called."
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
  Creates an rule that is empty (i.e. does not
  consume any tokens) and whose product is always
  the given product.
  In for moands, use the :let modifier in preference
  to this function.
  Is the result monadic function of the parser monad."
  [product]
  (fn prod-rule [state]
    (Reply false
      (c/Success product state
        (c/ParseError (:position state) nil nil)))))

(d/defvar -emptiness- (prod nil)
  "The general emptiness rule. Always succeeds.
  Does not consume any tokens. Its product is
  always nil.")

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
  "The error descriptors that -nothing- uses.")

(define-fn -nothing-
  "The general failing rule. It always fails. Use
  with-error in preference to this rule. (Its error
  descriptor is 'expected: absolutely nothing'.)
  Is the zero monadic value of the parser monad."
  [state]
  (make-failed-reply state nothing-descriptors))

(define-fn with-error
  "Creates an always- failing rule with the given
  message. Rules created with this function always fail.
  Use this in preference to -nothing-."
  [message]
  (fn with-error-rule [state]
    (make-failed-reply state #{(c/ErrorDescriptor :message message)})))

(letfn [(delayify [f] (fn [& args] (delay (force (apply f args)))))]
  (defmacro defn
    "Creates a rule-making function. Use this instead of
    clojure.core/defn whenever you make a rule-making
    function. (It does other stuff like memoization and
    delaying and stuff.)"
    [fn-name & forms]
   `(do (d/defn-memo ~fn-name ~@forms)
        (alter-var-root (var ~fn-name) ~delayify)
        (var ~fn-name))))

(defmacro defn-
  "Like defn, only makes the var private."
  [fn-name & forms]
  (list* `defn (vary-meta fn-name assoc :private true) forms))

(defn only-when
  "Creates a maybe-failing rule.
  Creates an either succeeding or a failing rule,
  depending on if valid? is logical true. If valid?
  is true, then the rule always succeeds and acts
  like (prod valid?). If valid? is false, then the
  rule always fails and acts like (with-error message).
      This function is very useful for when you want
  to validate a certain rule. For instance:
    (for [value -number-
          _ (only-when (< odd 10)
              \"number must be less than ten\")]
      value)
  The example above succeeds only when -number-
  matches and its product is less than 10."
  [valid? message]
  (if-not valid? (with-error message) (prod valid?)))

(define-fn combine
  "Creates a rule combining the given rule into the
  product-fn. *Use cat in preference to this function.*
      The product-fn must return a rule when
  given the product of the first rule. Is the bind
  monadic function of the parser monad."
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
      *This is the FnParse Hound version of +.* It first
  searches for a successful parse from its subrules that
  consumed any tokens. The first such success is
  immediately returned.
  If all sub-rules that consumed tokens failed, then
  the first successful parse that didn't consume any
  tokens is returned.
  Otherwise, if every sub-rule failed, then a failure
  is returned with the proper error descriptors.
      This is the plus monadic operator of the parser monad."
  [& rules]
  (fn summed-rule [state]
    (let [[consuming-replies empty-replies]
            (->> rules
              (map #(c/apply state %))
              (seq/separate :tokens-consumed?))]
      (if (empty? consuming-replies)
        (if (empty? empty-replies)
          (c/apply -nothing- state)
          (let [empty-replies (seq/reductions merge-replies empty-replies)]
            (or (first (drop-while #(-> % :result force c/failure?)
                         empty-replies))
                (last empty-replies))))
        (first consuming-replies)))))

(m/defmonad parser-m
  "The monad that FnParse uses."
  [m-zero -nothing-
   m-result prod
   m-bind combine
   m-plus +])

(define-fn label
  "Creates a labelled rule.
  Labels the given rule with the given string, returning
  a new rule. The given label will appear in the descriptors
  of any parse errors that expected the given rule to
  succeed."
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
  clojure.core/for.
  label-str: An optional label string. See the
             label function for more info.
  steps: A binding vector containing binding-form/
         rule pairs followed by optional modifiers.
         The given rules in each pair are conca-
         tenated together in sequence to create
         the new rule. Each binding-form is bound
         to the product of its corresponding rule.
         The rule expressions can refer to any
         symbol bound to in a previous pair.
         The only current recommended modifier
         is :let, which works like how it does it
         clojure.core/for.
  product-expr: The final product of the new rule.
                Only is reached after every sub-rule
                succeeds. The expression can refer
                to any symbol bound to in the steps.
  For examples of for rules, check the example
  libraries like fnparse.clojure.
  This macro is equivalent to the domonad form of
  the parser monad."
  ([label-str steps product-expr]
   `(->> (for ~steps ~product-expr) (label ~label-str)))
  ([steps product-expr]
  `(m/domonad parser-m ~steps ~product-expr)))

(define-fn validate
  "Creates a validating rule.
  A convenience function. Returns a new rule that
  acts like the given sub-rule, but also validates
  the sub-rule's products with the given predicate.
  If (pred product) is false, then the rule fails
  with the given message as an error.
      Basically just a shortcut for the for macro
  and only-when function."
  [pred message rule]
  (for [product rule, _ (only-when (pred product) message)]
    product))

(define-fn antivalidate
  "Exactly like the validate function, except that
  it uses the complement of pred instead."
  [pred message rule]
  (validate (complement pred) message rule))

(define-fn term
  "Creates a terminal rule.
  The new rule either consumes one token or fails.
  It must have a label-str that describes it
  and a predicate to test if the token it consumes is
  valid. Its product is the token it consumes.
  * If you just want to make sure that the consumed
    token equals something, use lit instead.
  * If you just want to make sure that the consumed
    token equals one of a bunch of things, use set-lit.
  * If you want to use the complement of the predicate,
    use antiterm.
  * If you don't care about what token is consumed,
    just as long as a token is consumed, use -anything-."
  [label-str predicate]
  (label label-str
    (fn terminal-rule [state]
      (let [position (:position state)]
        (if-let [remainder (-> state :remainder seq)]
          (let [first-token (first remainder)]
            (if (predicate first-token)
              (Reply true
                (delay
                  (c/Success first-token
                    (assoc state :remainder (next remainder)
                                 :position (inc position))
                    (c/ParseError position nil nil))))
              (make-failed-reply state first-token nil)))
          (make-failed-reply state ::c/end-of-input nil))))))

(define-fn antiterm
  "Exactly like term, only uses the complement of the
  given predicate instead."
  [label-str pred]
  (term label-str (complement pred)))

(d/defvar -anything- (term "anything" (constantly true))
  "The generic terminal rule. It consumes one token.
  It fails only when it's at the end of the input and
  there are no more tokens. Its product is the very token
  it consumed.")

(define-fn hook
  "Creates a rule with a semantic hook.
  A shortcut for the for macro. Creates a
  new rule. If the given sub-rule succeeds,
  then it succeeds, but its product is
  (semantic-hook sub-rule-product) instead."
  [semantic-hook rule]
  (for [product rule] (semantic-hook product)))

(define-fn chook
  "Creates a rule with a constant semantic hook.
  A shortcut for the for macro. The name
  stands for 'constant-hook'. It's exactly like
  hook, only the product is a constant; its
  product is always the given object."
  [product subrule]
  (for [_ subrule] product))

(define-fn lit
  "Creates a rule of a literal.
  A shortcut for the term function. It consumes
  one token, and succeeds only if it equals the
  given token. Otherwise, it fails.
  Its product is the token.
  It automatically adds an appropriate label."
  [token]
  (term (format "'%s'" token) #(= token %)))

(define-fn antilit
  "Creates a rule of an anti-literal.
  A shortcut for the term function. It consumes
  one token, and succeeds only if it *does not
  Its product is the consumed token.
  equal* the given token. It fails otherwise.
  It automatically adds an appropriate label."
  [token]
  (term (str "anything except " token) #(not= token %)))

(define-fn set-lit
  "Creates a rule of a literal of a set.
  A shortcut for the term function. It creates
  a set from the given sequence of tokens. The
  new rule consumes one token and succeeds only
  if the token is one of the given tokens.
  Its product is the consumed token.
  You must provide an appropriate label."
  [label-str tokens]
  (term label-str (set tokens)))

(define-fn anti-set-lit
  "Creates a rule of a anti-literal of a set.
  A shortcut for the term function. It creates
  a set from the given sequence of tokens. The
  new rule consumes one token and succeeds only
  if the token *is not* one of the given tokens.
  Its product is the consumed token.
  You must provide an appropriate label."
  [label-str tokens]
  (antiterm label-str (tokens set)))

(define-fn cat
  "Creates a concatenated rule.
  Concatenates many rules together. If one of
  the sub-rules fail, the whole rule fails.
  Its product is a sequence of the respective
  products of each sub-rule."
  [& subrules]
  (m/with-monad parser-m
    (m/m-seq subrules)))

(define-fn vcat
  "Exactly like cat, only applies vec to its product."
  [& subrules]
  (hook vec (apply cat subrules)))

(define-fn opt
  "Creates an optional rule. The new rule
  always succeeds. It is equivalent to the
  sum of the given rule and the emptiness rule."
  [rule]
  (+ rule -emptiness-))

(define-fn lex
  "Creates a lexical rule.
  You use this whenever you want the lexer to
  *backtrack* when it fails, *even* if it consumes
  tokens. (Don't forget, usually *if a rule consumes
  tokens, it cannot backtrack at all*.)
  HOW IT WORKS:
  Rules surrounded by lex count as 'empty' rules—
  rules that don't consume any tokens—regardless
  if they really consume tokens or not. This changes
  the behavior of any summed rules that contain it.
  WHY YOU WOULD NEED TO USE IT:
    (require '[name.choi.joshua.fnparse.hound :as r])
    (def -ws- (r/lit \\space))
    (def -claim- (r/phrase \"x = 1\"))
    (def -let-expr- (r/cat (r/phrase \"let\") -ws- -let-expr-))
    (def -identifier- (r/rep+ r/-ascii-letter-))
    (def -expr- (r/+ -let-expr- -identifier-))
    (parse -let-expr- \"number\" nil) ; Line one
    (parse -let-expr- \"letter\" nil) ; Line two
  In the code above, line one will give a successful
  parse, because the input \"number\" matches
  -indentifier-.
      But line two will give a failure. This is because
  (r/phrase \"let\") will match, but the -ws- after it
  will not match. Thus, -let-expr- fails. Also, because
  -let-expr- consumed the first three tokens of \"letter\",
  the summed rule -expr- will immediately fail without
  even trying -identifier-.
  AND SO HOW YOU USE IT:
  Change -let-expr- to use the following:
    (r/cat (r/lex (r/phrase \"let\")) -ws- -let-expr-)
  Now both line one and two will be successful."
  [subrule]
  (fn [state]
    (-> state subrule
      (assoc :tokens-consumed? false))))

(define-fn followed-by
  "Creates a lookahead rule. The new rule does
  not consume any tokens. It succeeds only when
  the given sub-rule succeeds, and fails when
  the sub-rule fails.
  On success, its product is its sub-rule's
  product."
  [rule]
  (fn [state]
    (let [result (-> state (c/apply rule) :result force)]
      (if (c/failure? result)
        (Reply false result)
        ((prod (:product result)) state)))))

(define-fn not-followed-by
  "Creates a negative lookahead rule. The new
  rule does not consume any tokens. It succeeds
  only when the given sub-rule fails, and
  otherwise succeeds.
  On success, its product is the boolean true.
  You must provide a label."
  [label-str rule]
  (label label-str
    (fn not-followed-by-rule [state]
      (let [result (-> state (c/apply rule) :result force)]
        (if (c/failure? result)
          (Reply false (c/Success true state (:error result)))
          (-> state (c/apply -nothing-) (assoc :error (:error result))))))))

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

(define-fn mapcat [f tokens]
  (->> tokens (map f) (apply cat)))

(define-fn mapsum [f tokens]
  (->> tokens (map f) (apply +)))

(define-fn phrase [tokens]
  (mapcat lit tokens))

(d/defvar -end-of-input-
  (not-followed-by "the end of input" -anything-)
  "WARNING: Because this is an always succeeding,
  always empty rule, putting this directly into a
  rep*/rep+/etc.-type rule will result in an
  infinite loop.")

(define-fn prefix [prefix-rule body-rule]
  (for [_ prefix-rule, content body-rule] content))

(define-fn suffix [body-rule suffix-rule]
  (for [content body-rule, _ suffix-rule] content))

(define-fn circumfix [prefix-rule body-rule suffix-rule]
  (prefix prefix-rule (suffix body-rule suffix-rule)))

(define-fn separated-rep [separator element]
  (for [first-element element
            rest-elements (rep* (prefix separator element))]
    (cons first-element rest-elements)))

(defmacro template-sum [argv expr & values]
  (let [c (count argv)]
   `(+ ~@(map (fn [a] (t/apply-template argv expr a))
           (partition c values)))))

(define-fn case-insensitive-lit [#^Character token]
  (+ (lit (Character/toLowerCase token))
     (lit (Character/toUpperCase token))))

(define-fn effects [f & args]
  (fn effects-rule [state]
    (apply f args)
    (c/apply state -emptiness-)))

(define-fn except
  "Creates a rule that is the exception from
  the first given subrules with the second given
  subrule--that is, it accepts only tokens that
  fulfill the first subrule but fails the
  second of the subrules.
  (define a (except b c)) would be equivalent to the EBNF
    a = b - c;
  The new rule's products would be b-product. If
  b fails or c succeeds, then nil is simply returned."
  ([label-str minuend subtrahend]
   (for [_ (not-followed-by label-str subtrahend)
         product (label label-str minuend)]
     product))
  ([label-str minuend first-subtrahend & rest-subtrahends]
   (except label-str minuend
     (apply + (cons first-subtrahend rest-subtrahends)))))

(define-fn annotate-error [message-fn rule]
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

(define-fn factor= [n rule]
  (->> rule (replicate n) (apply cat)))

(define-fn -fetch-context- [state]
  (c/apply state (prod (:context state))))

(define-fn alter-context [f & args]
  (fn context-altering-rule [state]
    (let [altered-state (apply update-in state [:context] f args)]
      ; (prn (c/apply altered-state -fetch-context-))
      (c/apply altered-state -fetch-context-))))

(def ascii-digits "0123456789")
(def lowercase-ascii-alphabet "abcdefghijklmnopqrstuvwxyz")
(def uppercase-ascii-alphabet "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
(def base-36-digits (str ascii-digits lowercase-ascii-alphabet))

(defn radix-digit
  ([base] (radix-digit (format "a base-%s digit" base) base))
  ([label-str base]
   {:pre #{(integer? base) (> base 0)}}
   (->> base-36-digits (take base) seq/indexed
     (mapsum (fn [[index token]] (chook index (case-insensitive-lit token))))
     (label label-str))))

(def -decimal-digit-
  (radix-digit "a decimal digit" 10))

(def -hexadecimal-digit-
  (radix-digit "a hexadecimal digit" 16))

(def -uppercase-ascii-letter-
  (set-lit "an uppercase ASCII letter" uppercase-ascii-alphabet))

(def -lowercase-ascii-letter-
  (set-lit "a lowercase ASCII letter" lowercase-ascii-alphabet))

(def -ascii-letter-
  (label "an ASCII letter"
    (+ -uppercase-ascii-letter- -lowercase-ascii-letter-)))

(def -ascii-alphanumeric-
  (label "an alphanumeric ASCII character"
    (+ -ascii-letter- -decimal-digit-)))
