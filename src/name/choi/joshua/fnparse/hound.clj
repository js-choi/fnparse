(ns name.choi.joshua.fnparse.hound
  [:use clojure.contrib.seq-utils clojure.contrib.def clojure.test
        clojure.set clojure.contrib.monads]
  [:import [clojure.lang Sequential IPersistentMap IPersistentVector Var]])

(set! *warn-on-reflection* true)

; A RULE is a a function that:
; - Takes a state and returns either nil
;   or a vector pair.
;   - A STATE is a struct map that contains
;     a remainder and maybe info.
;     You create states using the make-cf-state function.
;   - A REMAINDER is a sequence or
;     seqable collection of tokens.
;     It is contained in the
;     :name.choi.joshua.fnparse/remainder key.
;   - A state can also contain INFO, which are
;     any other attributes in the state. Common
;     examples include current line and column numbers
;     and a set of current warnings.
; - If the remainder is VALID under the rule,
;   it CONSUMES any valid tokens and returns a RESULT.
;   - A RESULT is a vector pair containing
;     a product and a new state.
;   - The PRODUCT is the semantic data generated
;     by the rule that corresponds to the
;     information represented by the consumed tokens.
;     It can be any object.
;   - The new state is what the old state now looks like,
;     after its first few tokens are consumed.
; - If the given token sequence is INVALID, then
;   the rule FAILS, meaning that it simply returns NIL.

(deftype State [remainder position] IPersistentMap)

(deftype Reply [tokens-consumed? result] IPersistentMap)

(deftype Expectation [position unexpected-token expected-rules] IPersistentMap)

(deftype Failure [expectation] IPersistentMap)

(deftype Success [product state expectation]
  ; The expectation is that of the error that would have
  ; occurred if this successful alternative wasn't taken.
  IPersistentMap)

(defn make-state [remainder]
  (State remainder 0))

(defn failure? [result]
  (isa? (type result) ::Failure))

(letfn [(reply-expected-rules [reply]
          (-> reply :result :expectation :expected-rules))]
  (defn merge-replies [mergee merger]
    (let [merger-set (reply-expected-rules merger)
          mergee-set (reply-expected-rules mergee)]
      (assoc-in merger [:result :expectation :expected-rules]
        (union merger-set mergee-set)))))

(defmonad parser-m
  "The monad that FnParse uses."
  [m-zero
     (fn [state]
       (Reply false (Failure (Expectation (:position state)
                                          (first (:remainder state))
                                          nil))))
   m-result
     (fn [product]
       (fn [state]
         (Reply false
           (Success product state
             (Expectation (:position state) nil nil)))))
   m-bind
     (fn [rule product-fn]
       (letfn [(apply-product-fn [result]
                 ((product-fn (:product result)) (:state result)))]
         (fn [state]
           (let [reply (rule state)]
             (if (:tokens-consumed? reply)
               (assoc reply :result
                 (delay
                   (let [result (-> reply :result force)]
                     (if (failure? result)
                       result
                       (-> result apply-product-fn :result force)))))
               (let [result (-> reply :result)]
                 (if (failure? result)
                   (Reply false result)
                   (apply-product-fn result))))))))
   m-plus
     (letfn [(result-failure? [reply]
               (-> reply :result force failure?))]
       (fn [& rules]
         (fn [state]
           (let [[consuming-replies empty-replies]
                   (->> rules (map #(% state)) (separate :tokens-consumed?))]
             (if (empty? consuming-replies)
               (if (empty? empty-replies)
                 (m-zero state)
                 (let [empty-replies (reductions merge-replies empty-replies)]
                   (or (first (drop-while #(-> % :result failure?)
                                empty-replies))
                       (last empty-replies))))
               (first consuming-replies))))))])

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
  `(domonad parser-m ~steps ~@product-expr))

(defn term [predicate]
  (with-monad parser-m
    (fn [state]
      (let [position (:position state)]
        (if-let [remainder (-> state :remainder seq)]
          (let [first-token (first remainder)]
            (if (predicate first-token)
              (Reply true (delay (Success first-token
                                          (assoc state
                                            :remainder (next remainder)
                                            :position (inc position))
                                          (Expectation position nil nil))))
              (Reply false (Failure (Expectation position first-token nil)))))
          (Reply false (Failure (Expectation position :nothing nil))))))))

(defvar anything
  (term (constantly true)))

(defn with-result [product]
  (with-monad parser-m (m-result product)))

(defvar emptiness
  (with-result nil))

(defvar nothing
  (with-monad parser-m m-zero))

(defn with-label [label rule]
  (fn [state]
    (let [reply (rule state)]
      (if (:tokens-consumed? reply)
        reply
        (assoc-in reply [:result :expectation :expected-rules]
          #{label})))))

(defn lit* [token]
  (term (partial = token)))

(defn lit [token]
  (with-label token (lit* token)))

(defn string-set [string]
  (into #{} string))

(defn multilit [label tokens]
  (with-label label (term (into #{} tokens))))

(defn anti-multilit [label tokens]
  (with-label label (term (complement (into #{} tokens)))))

(defn alt [& subrules]
  (with-monad parser-m
    (apply m-plus subrules)))

(defn conc [& subrules]
  (with-monad parser-m
    (m-seq subrules)))

(defn opt [rule]
  (alt rule emptiness))

(defn mapconc
  ([tokens] (mapconc lit tokens))
  ([rule-maker tokens] (apply conc (map rule-maker tokens))))

(defn mapalt
  ([tokens] (mapalt lit tokens))
  ([rule-maker tokens] (apply alt (map rule-maker tokens))))

(defn lex [subrule]
  (fn [state]
    (-> state subrule (assoc :tokens-consumed? false))))

(defn rep+ [rule]
  ; TODO: Rewrite to not blow up stack with many valid tokens
  (complex [first-token rule
            rest-tokens (opt (rep+ rule))]
    (cons first-token rest-tokens)))

; (defn rep* [rule]
;   (with-monad parser-m
;     (m-seq-while (complement failure?) (repeat 10 rule))))

(defn rep* [rule]
  (opt (rep+ rule)))

(defvar decimal-digit
  (with-label "decimal digit" (mapalt lit* "1234567890")))

(let [decimal-digits (rep+ decimal-digit)]
  (def decimal-number
    (complex [sign (opt (mapalt "+-"))
              integer-part decimal-digits
              fractional-part (opt (conc (lit \.) (opt decimal-digits)))
              exponent-part (opt (conc (mapalt "eE") decimal-digits))]
      (let [digits (->> [sign integer-part fractional-part exponent-part]
                     flatten (apply str))]
        (if (or fractional-part exponent-part)
          (Double/parseDouble digits)
          (Integer/parseInt digits))))))

(defvar hexadecimal-digit
  (with-label "hexadecimal digit"
    (mapalt lit* "1234567890ABCDEFabcdef")))

(defvar uppercase-ascii-letter
  (with-label "uppercase ASCII letter"
    (mapalt lit* "ABCDEFGHIJKLMNOPQRSTUVWXYZ")))

(defvar lowercase-ascii-letter
  (with-label "lowercase ASCII letter"
    (mapalt lit* "abcdefghijklmnopqrstuvwxyz")))

(defvar ascii-letter
  (with-label "ASCII letter"
    (alt uppercase-ascii-letter lowercase-ascii-letter)))

