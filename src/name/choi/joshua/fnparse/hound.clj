(ns name.choi.joshua.fnparse.hound
  (:use clojure.contrib.seq-utils clojure.contrib.def clojure.test
        clojure.set clojure.contrib.monads clojure.template)
  (:require [name.choi.joshua.fnparse.common :as c])
  (:refer-clojure :exclude #{for + mapcat})
  (:import [clojure.lang Sequential IPersistentMap IPersistentVector Var]))

(deftype State [remainder position context] :as this
  IPersistentMap
  c/AState
    (position [] (:position this)))

(deftype Reply [tokens-consumed? result] :as this
  IPersistentMap
  c/AParseAnswer (answer-result [] (-> this :result force)))

(defn make-state [remainder context]
  (State remainder 0 context))

(defn parse [rule input context success-fn failure-fn]
  (c/parse make-state rule input context success-fn failure-fn))

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

(defmacro defrm [fn-name & forms]
  (letfn [(delayify [f] (fn [& args] (delay (force (apply f args)))))]
   `(do
      (defn-memo ~fn-name ~@forms)
      (alter-var-root (var ~fn-name) ~delayify)
      (var ~fn-name))))

(defmacro defrm- [& forms]
  `(defrm ~@forms))

(defn only-when [valid? message]
  (if-not valid? (with-error message) (with-product valid?)))

(defn combine [rule product-fn]
  (letfn [(apply-product-fn [result]
            (c/apply-rule (:state result) (product-fn (:product result))))]
    (fn [state]
      (let [first-reply (c/apply-rule state rule)]
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

(defn + [& rules]
  (fn summed-rule [state]
    (let [[consuming-replies empty-replies]
            (->> rules
              (map #(c/apply-rule state %))
              (separate :tokens-consumed?))]
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
   m-plus +])

(defn label [label-string rule]
  (letfn [(assoc-label [result]
            (-> result force
              (assoc-in [:error :descriptors]
                #{(c/ErrorDescriptor :label label-string)})
              delay))]
    (fn labelled-rule [state]
      (let [reply (c/apply-rule state rule)]
        (if-not (:tokens-consumed? reply)
          (update-in reply [:result] assoc-label)
          reply)))))

(defmacro for
  "Creates a for rule in monadic
  form. It's a lot easier than it sounds.
  It's like a very useful combination of
  cat and semantics.
  The first argument is a vector
  containing binding forms à la the let and for
  forms. The keys are new, lexically scoped
  variables. Their corresponding vals
  are subrules. Each of these subrules are
  sequentially called as if they were
  concatinated together with cat. If any of
  them fails, the whole rule immediately fails.
  Meanwhile, each sequential subrule's product
  is bound to its corresponding variable.
  After all subrules match, all of the
  variables can be used in the body.
  The second argument of for is a body
  that calculates the whole new rule's
  product, with access to any of the variables
  defined in the binding vector.
  It's basically like let, for, or any other
  monad. Very useful!"
  ([label-string steps product-expr]
   `(->> (for ~steps ~product-expr) (label ~label-string)))
  ([steps product-expr]
  `(domonad parser-m ~steps ~product-expr)))

(defn validate [rule pred message]
  (for [product rule, _ (only-when (pred product) message)]
    product))

(defn anti-validate [rule pred message]
  (validate rule (complement pred) message))

(defn term [label-string predicate]
  (label label-string
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

(defn antiterm [label-string pred]
  (term label-string (complement pred)))

(defvar anything
  (term "anything" (constantly true)))

(defn hook [semantic-hook subrule]
  (for [product subrule] (semantic-hook product)))

(defn chook [product subrule]
  (for [_ subrule] product))

(defn lit [token]
  (term (format "'%s'" token) #(= token %)))

(defn antilit [token]
  (term (str "anything except " token) #(not= token %)))

(defn set-lit [label-string tokens]
  (term label-string (set tokens)))

(defn anti-set-lit [label-string tokens]
  (antiterm label-string (tokens set)))

(defn cat [& subrules]
  (with-monad parser-m
    (m-seq subrules)))

(defn opt [rule]
  (+ rule emptiness))

(defn lex [subrule]
  (fn [state]
    (-> state subrule
      (assoc :tokens-consumed? false))))

(defn cascading-rep+ [rule unary-hook binary-hook]
  ; TODO: Rewrite to not blow up stack with many valid tokens
  (for [first-token rule
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

(defn mapcat [tokens]
  (apply cat (map lit tokens)))

(defn mapalt [f coll]
  (apply + (map f coll)))

(defn optcat [& rules]
  (opt (apply cat rules)))

(defn followed-by [rule]
  (fn [state]
    (let [result (-> state (c/apply-rule rule) :result force)]
      (if (c/failure? result)
        (Reply false result)
        ((with-product (:product result)) state)))))

(defn not-followed-by
  [label-string rule]
  (label label-string
    (fn not-followed-by-rule [state]
      (let [result (-> state (c/apply-rule rule) :result force)]
        (if (c/failure? result)
          (Reply false (c/Success true state (:error result)))
          (-> state nothing (assoc :error (:error result))))))))

(defvar end-of-input
  (not-followed-by "the end of input" anything)
  "WARNING: Because this is an always succeeding,
  always empty rule, putting this directly into a
  rep*/rep+/etc.-type rule will result in an
  infinite loop.")

(defn prefix [prefix-rule body]
  (for [_ prefix-rule, content body] content))

(defn suffix [body suffix-rule]
  (for [content body, _ suffix-rule] content))

(defn circumfix [prefix-rule body suffix-rule]
  (prefix prefix-rule (suffix body suffix-rule)))

(defn separated-rep [separator element]
  (for [first-element element
            rest-elements (rep* (prefix separator element))]
    (cons first-element rest-elements)))

(defmacro template-alt [argv expr & values]
  (let [c (count argv)]
   `(+ ~@(map (fn [a] (apply-template argv expr a))
           (partition c values)))))

(defn case-insensitive-lit [#^Character token]
  (+ (lit (Character/toLowerCase token))
     (lit (Character/toUpperCase token))))

(defn effects [f & args]
  (fn effects-rule [state]
    (apply f args)
    (c/apply-rule state emptiness)))

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
  ([label-string minuend subtrahend]
   (label label-string
     (for [_ (not-followed-by nil subtrahend), product minuend]
       product)))
  ([label-string minuend first-subtrahend & rest-subtrahends]
   (except label-string minuend
     (apply + (cons first-subtrahend rest-subtrahends)))))

(defn annotate-error [message-fn rule]
  (letfn [(annotate [result]
            (delay (let [{error :error, :as forced-result} (force result)
                         new-message (message-fn error)]
                     (if new-message
                       (update-in forced-result [:error :descriptors]
                         conj (c/ErrorDescriptor :message new-message))
                       forced-result))))]
    (fn error-annotation-rule [state]
      (let [reply (c/apply-rule state rule)]
        (update-in reply [:result] annotate)))))

(defn factor= [n rule]
  (->> rule (replicate n) (apply cat)))

(defn get-context [state]
  (c/apply-rule state (with-product (:context state))))

(defvar ascii-digits "0123456789")
(defvar lowercase-ascii-alphabet "abcdefghijklmnopqrstuvwxyz")
(defvar uppercase-ascii-alphabet "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
(defvar base-36-digits (str ascii-digits lowercase-ascii-alphabet))

(defrm radix-digit
  ([base] (radix-digit (format "a base-%s digit" base) base))
  ([label-string base]
   {:pre #{(integer? base) (> base 0)}}
   (->> base-36-digits (take base) indexed
     (mapalt (fn [[index token]]
               (chook index (case-insensitive-lit token))))
     (label label-string))))

(defvar decimal-digit
  (radix-digit "a decimal digit" 10))

(defvar hexadecimal-digit
  (radix-digit "a hexadecimal digit" 16))

(defvar uppercase-ascii-letter
  (set-lit "an uppercase ASCII letter" uppercase-ascii-alphabet))

(defvar lowercase-ascii-letter
  (set-lit "a lowercase ASCII letter" lowercase-ascii-alphabet))

(defvar ascii-letter
  (label "an ASCII letter"
    (+ uppercase-ascii-letter lowercase-ascii-letter)))

(defvar ascii-alphanumeric
  (label "an alphanumeric ASCII character"
    (+ ascii-letter decimal-digit)))

; (def rule (for [a anything, b anything] [a b]))
; (def rule (validate anything (partial = 'a)))
; (def rule (mapcat '[a b]))
; (def rule (lit \3))
; (def rule (lex (mapcat "let 3")))
; (def rule (+ (lex (mapcat "let 3")) (mapcat "la")))
; (def rule (lex (label "let expr" (mapcat "let 3"))))
; (def rule (+ (lex (label "let expr" (mapcat "let 3")))
;                (lit \3)))
; (def rule emptiness)
; (def rule (rep* (antilit \3)))
; (def rule (rep* decimal-digit))
; (def rule (followed-by (mapcat "li")))

; (-> "lit 3" make-state rule println)
