(ns name.choi.joshua.fnparse.hound
  (:use clojure.contrib.seq-utils clojure.contrib.def clojure.test
        clojure.set clojure.contrib.monads clojure.template)
  (:require [name.choi.joshua.fnparse.common :as c])
  (:import [clojure.lang Sequential IPersistentMap IPersistentVector Var]))

(deftype State [remainder position] :as this
  IPersistentMap
  c/AState
    (position [] (:position this)))

(deftype Reply [tokens-consumed? result] :as this
  IPersistentMap
  c/AParseAnswer (answer-result [] (-> this :result force)))

(defn make-state [remainder]
  (State remainder 0))

(defn parse [rule input success-fn failure-fn]
  (c/parse make-state rule input success-fn failure-fn))

(defn merge-replies [mergee merger]
  (assoc merger :result
    (update-in (-> merger :result force) [:error]
      c/merge-parse-errors (-> mergee :result force :error))))

(defn with-product [product]
  (fn with-product-rule [state]
    (Reply false
      (c/Success product state
        (c/ParseError (:position state) nil nil)))))

(defvar emptiness (with-product nil))

(defn- base-nothing [state unexpected-token descriptors]
  (Reply false
    (c/Failure
      (c/ParseError (:position state)
                    (first (:remainder state))
                    descriptors))))

(defn nothing [state]
  (base-nothing state nil nil))

(defn with-error [message]
  (fn with-error-rule [state]
    (base-nothing state nil #{(c/ErrorDescriptor :message message)})))

(defn only-when [valid? message]
  (if-not valid? (with-error message) emptiness))

(defn combine [rule product-fn]
  (letfn [(apply-product-fn [result]
            ((product-fn (:product result)) (:state result)))]
    (fn [state]
      (let [first-reply (rule state)]
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

(defn alt [& rules]
  (fn summed-rule [state]
    (let [[consuming-replies empty-replies]
            (->> rules (map #(% state)) (separate :tokens-consumed?))]
      (if (empty? consuming-replies)
        (if (empty? empty-replies)
          (m-zero state)
          (let [empty-replies (reductions merge-replies empty-replies)]
            (or (first (drop-while #(-> % :result force c/failure?)
                         empty-replies))
                (last empty-replies))))
        (first consuming-replies)))))

(defmonad parser-m
  "The monad that FnParse uses."
  [m-zero nothing
   m-result with-product
   m-bind combine
   m-plus alt])

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
  (letfn [(assoc-label [result]
            (-> result force
              (assoc-in [:error :descriptors]
                #{(c/ErrorDescriptor :label label)})
              delay))]
    (fn labelled-rule [state]
      (let [reply (rule state)]
        (if-not (:tokens-consumed? reply)
          (update-in reply [:result] assoc-label)
          reply)))))

(defn validate [rule pred message]
  (complex [product rule, _ (only-when (pred product) message)]
    product))

(defn anti-validate [rule pred message]
  (validate rule (complement pred) message))

(defn term [label predicate]
  (with-label label
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
              (base-nothing state first-token nil)))
          (base-nothing state ::end-of-input nil))))))

(defn antiterm [label pred]
  (term label (complement pred)))

(defvar anything
  (term "anything" (constantly true)))

(defn semantics [subrule semantic-hook]
  (complex [product subrule] (semantic-hook product)))

(defn constant-semantics [subrule product]
  (complex [_ subrule] product))

(defn lit [token]
  (term (format "'%s'" token) #(= token %)))

(defn antilit [token]
  (term (str "anything except " token) #(not= token %)))

(defn set-lit [label tokens]
  (term label (set tokens)))

(defn anti-set-lit [label tokens]
  (antiterm label (tokens set)))

(defn conc [& subrules]
  (with-monad parser-m
    (m-seq subrules)))

(defn opt [rule]
  (alt rule emptiness))

(defn lex [subrule]
  (fn [state]
    (-> state subrule
      (assoc :tokens-consumed? false))))

(defn cascading-rep+ [rule unary-hook binary-hook]
  ; TODO: Rewrite to not blow up stack with many valid tokens
  (complex [first-token rule
            rest-tokens (opt (cascading-rep+ rule unary-hook binary-hook))]
    (if (nil? rest-tokens)
      (unary-hook first-token)
      (binary-hook first-token rest-tokens))))

(defn rep+ [rule]
  ; TODO: Rewrite to not blow up stack with many valid tokens
  (cascading-rep+ rule list cons))

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
      (if (c/failure? result)
        (Reply false result)
        ((with-product (:product result)) state)))))

(defn not-followed-by
  [label rule]
  (with-label label
    (fn not-followed-by-rule [state]
      (let [result (-> state rule :result force)]
        (if (c/failure? result)
          (Reply false (c/Success true state (:error result)))
          (-> state nothing (assoc :error (:error result))))))))

(defvar end-of-input
  (not-followed-by "the end of input" anything)
  "WARNING: Because this is an always succeeding,
  always empty rule, putting this directly into a
  rep*/rep+/etc.-type rule will result in an
  infinite loop.")

(defn prefix-conc
  ([rule-0 rule-1 rule-2 & rest-rules]
   (let [rest-rules (cons rule-2 rest-rules)
         body (last rest-rules)
         prefixes (concat [rule-0 rule-1] (drop-last rest-rules))]
     (prefix-conc (apply conc prefixes) body)))
  ([prefix body]
   (complex [_ prefix, content body] content)))

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

(defn effects [f & args]
  (fn effects-rule [state]
    (apply f args)
    (emptiness state)))

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
  ([label minuend subtrahend]
   (with-label label
     (complex [_ (not-followed-by nil subtrahend), product minuend]
       product)))
  ([label minuend first-subtrahend & rest-subtrahends]
   (except label minuend
     (apply alt (cons first-subtrahend rest-subtrahends)))))

(defn annotate-error [rule message-fn]
  (letfn [(annotate [result]
            (delay (let [{error :error, :as forced-result} (force result)
                         new-message (message-fn error)]
                     (if new-message
                       (update-in forced-result [:error :descriptors]
                         conj (c/ErrorDescriptor :message new-message))
                       forced-result))))]
    (fn error-annotation-rule [state]
      (let [reply (rule state)]
        (update-in reply [:result] annotate)))))

(defvar ascii-digits "0123456789")
(defvar lowercase-ascii-alphabet "abcdefghijklmnopqrstuvwxyz")
(defvar uppercase-ascii-alphabet "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
(defvar base-36-digits (str ascii-digits lowercase-ascii-alphabet))

(defrm radix-digit
  ([base] (radix-digit (format "a base-%s digit" base) base))
  ([label base]
   {:pre #{(integer? base) (<= 0 base 36)}}
   (->> base-36-digits (take base) indexed
     (mapalt (fn [[index token]]
               (constant-semantics (case-insensitive-lit token) index)))
     (with-label label))))

(defvar decimal-digit
  (radix-digit "a decimal digit" 10))

(defvar hexadecimal-digit
  (radix-digit "a hexadecimal digit" 16))

(defvar uppercase-ascii-letter
  (set-lit "an uppercase ASCII letter" uppercase-ascii-alphabet))

(defvar lowercase-ascii-letter
  (set-lit "a lowercase ASCII letter" lowercase-ascii-alphabet))

(defvar ascii-letter
  (with-label "an ASCII letter"
    (alt uppercase-ascii-letter lowercase-ascii-letter)))

(defvar ascii-alphanumeric
  (with-label "an alphanumeric ASCII character"
    (alt ascii-letter decimal-digit)))

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
