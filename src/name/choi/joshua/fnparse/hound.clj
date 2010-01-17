(ns name.choi.joshua.fnparse.hound
  (:use clojure.contrib.seq-utils clojure.contrib.def clojure.test
        clojure.set clojure.contrib.monads clojure.template)
  (:import [clojure.lang Sequential IPersistentMap IPersistentVector Var]))

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

(deftype ErrorDescriptor [kind message] IPersistentMap)

(deftype ParseError [position unexpected-token descriptors] IPersistentMap)

(deftype Failure [error] IPersistentMap)

(deftype Success [product state error]
  ; :error is the error that would have
  ; occurred if this successful alternative wasn't taken.
  IPersistentMap)

(defn make-state [remainder]
  (State remainder 0))

(do-template [fn-name type-name doc-string]
  (defn fn-name doc-string [result]
    (-> result type (isa? type-name)))
  failure? ::Failure "Is the given result a Failure?"
  success? ::Success "Is the given result is a Success?")

(defn parse
  [input rule success-fn failure-fn]
  (let [result (-> input make-state rule :result force)]
    (if (failure? result)
      (failure-fn (:error result))
      (success-fn (:product result) (-> result :state :remainder)))))

(letfn [(reply-expected-rules [reply]
          (-> reply :result :error :descriptors))]
  (defn merge-replies [mergee merger]
    (let [merger-rules (reply-expected-rules merger)
          mergee-rules (reply-expected-rules mergee)]
      (assoc-in merger [:result :error :descriptors]
        (concat mergee-rules merger-rules)))))

(defmonad parser-m
  "The monad that FnParse uses."
  [m-zero
     (fn [state]
       (Reply false (Failure (ParseError (:position state)
                                         (first (:remainder state))
                                         nil))))
   m-result
     (fn [product]
       (fn [state]
         (Reply false
           (Success product state
             (ParseError (:position state) nil nil)))))
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
               (let [result (-> reply :result force)]
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
                   (or (first (drop-while #(-> % :result force failure?)
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

(defn with-label [label rule]
  (fn [state]
    (let [reply (rule state)]
      (if (:tokens-consumed? reply)
        reply
        (assoc-in reply [:result :error :descriptors]
          (list (ErrorDescriptor :expectation label)))))))

(defn term [label predicate]
  (with-monad parser-m
    (with-label label
      (fn [state]
        (let [position (:position state)]
          (if-let [remainder (-> state :remainder seq)]
            (let [first-token (first remainder)]
              (if (predicate first-token)
                (Reply true
                  (delay (Success first-token
                           (assoc state
                             :remainder (next remainder)
                             :position (inc position))
                           (ParseError position nil nil))))
                (Reply false (Failure (ParseError position first-token nil)))))
            (Reply false (Failure (ParseError position :nothing nil)))))))))

(defn antiterm [label pred]
  (term label (complement pred)))

(defvar anything
  (term "anything" (constantly true)))

(defn semantics [subrule semantic-hook]
  (complex [product subrule] (semantic-hook product)))

(defn constant-semantics [subrule product]
  (complex [_ subrule] product))

(defn with-product [product]
  (with-monad parser-m (m-result product)))

(defvar emptiness (with-product nil))

(defvar nothing
  (with-monad parser-m m-zero))

(defvar end-of-input
  (with-label "end of input"
    (fn [state]
      (if (-> state anything :result failure?)
        (emptiness state)
        (nothing state))))
  "WARNING: Because this is an always succeeding,
  always empty rule, putting this directly into a
  rep*/rep+/etc.-type rule will result in an
  infinite loop.")

(defn lit [token]
  (term token #(= token %)))

(defn antilit [token]
  (term (str "anything except " token) #(not= token %)))

(defn set-lit [label tokens]
  (term label (set tokens)))

(defn anti-set-lit [label tokens]
  (antiterm label (tokens set)))

(defn alt [& subrules]
  (with-monad parser-m
    (apply m-plus subrules)))

(defn conc [& subrules]
  (with-monad parser-m
    (m-seq subrules)))

(defn opt [rule]
  (alt rule emptiness))

(defn lex [subrule]
  (fn [state]
    (-> state subrule
      (assoc :tokens-consumed? false)
      (update-in [:result] force))))

(defn cascading-rep+ [rule unary-hook binary-hook]
  ; TODO: Rewrite to not blow up stack with many valid tokens
  (complex [first-token rule
            rest-tokens (opt (cascading-rep+ rule unary-hook binary-hook))]
    (if (nil? rest-tokens)
      (unary-hook first-token)
      (binary-hook first-token rest-tokens))))

(defn rep+ [rule]
  ; TODO: Rewrite to not blow up stack with many valid tokens
  (cascading-rep+ rule cons cons))

; (defn rep* [rule]
;   (with-monad parser-m
;     (m-seq-while (complement failure?) (repeat 10 rule))))

(defn rep* [rule]
  (opt (rep+ rule)))

(defn mapconc [tokens]
  (apply conc (map lit tokens)))

(defn mapalt [f coll]
  (apply alt (map f coll)))

(defn followed-by [rule]
  (fn [state]
    (let [result (-> state rule :result force)]
      (if (failure? result)
        (Reply false result)
        ((with-product (:product result)) state)))))

(defn prefix-conc [prefix body]
  (complex [_ prefix, content body] content))

(defn suffix-conc [body suffix]
  (complex [content body, _ suffix] content))

(defn circumfix-conc [prefix body suffix]
  (prefix-conc prefix (suffix-conc body suffix)))

(defn separated-rep [separator element]
  (complex [first-element element
            rest-elements (rep* (prefix-conc separator element))]
    (cons first-element rest-elements)))

(defmacro template-alt [argv expr & values]
  (let [c (count argv)]
    `(alt ~@(map (fn [a] (apply-template argv expr a)) 
              (partition c values)))))

(defn case-insensitive-lit [#^Character token]
  (alt (lit (Character/toLowerCase token))
       (lit (Character/toUpperCase token))))

(defmacro defrm [& forms]
  `(defn-memo ~@forms))

(defmacro defrm- [& forms]
  `(defrm ~@forms))

(defvar ascii-digits "0123456789")
(defvar lowercase-ascii-alphabet "abcdefghijklmnopqrstuvwxyz")
(defvar base-36-digits (str ascii-digits lowercase-ascii-alphabet))

(defrm radix-digit
  ([base] (radix-digit (format "a base-%s digit" base) base))
  ([label base]
   {:pre #{(<= 0 base 36)}}
   (->> base-36-digits (take base) indexed
     (mapalt (fn [[index token]]
               (constant-semantics (case-insensitive-lit token) index)))
     (with-label label))))

(defvar decimal-digit
  (radix-digit "a decimal digit" 10))

(defvar hexadecimal-digit
  (radix-digit "a hexadecimal digit" 16))

(defvar uppercase-ascii-letter
  (set-lit "an uppercase ASCII letter" "ABCDEFGHIJKLMNOPQRSTUVWXYZ"))

(defvar lowercase-ascii-letter
  (set-lit "a lowercase ASCII letter" "abcdefghijklmnopqrstuvwxyz"))

(defvar ascii-letter
  (with-label "an ASCII letter"
    (alt uppercase-ascii-letter lowercase-ascii-letter)))

; (def rule (complex [a anything, b anything] [a b]))
; (def rule (validate anything (partial = 'a)))
; (def rule (mapconc '[a b]))
; (def rule (lit \3))
; (def rule (lex (mapconc "let 3")))
; (def rule (alt (lex (mapconc "let 3")) (mapconc "la")))
; (def rule (lex (with-label "let expr" (mapconc "let 3"))))
; (def rule (alt (lex (with-label "let expr" (mapconc "let 3")))
;                (lit \3)))
; (def rule emptiness)
; (def rule (rep* (antilit \3)))
; (def rule (rep* decimal-digit))
; (def rule (followed-by (mapconc "li")))

; (-> "lit 3" make-state rule println)
