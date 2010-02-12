(ns name.choi.joshua.fnparse.hound
  (:require [name.choi.joshua.fnparse.common :as c]
            [clojure.contrib.seq-utils :as seq]
            [clojure.contrib.monads :as m]
            [clojure.template :as t]
            [clojure.contrib.def :as d])
  (:refer-clojure :exclude #{for + mapcat}
                  :rename {defn define-fn, defn- define-fn-})
  (:import [clojure.lang IPersistentMap]))

(deftype State [remainder position context] :as this
  IPersistentMap
  c/AState
    (position [] (:position this)))

(deftype Reply [tokens-consumed? result] :as this
  IPersistentMap
  c/AParseAnswer (answer-result [] (-> this :result force)))

(define-fn make-state [remainder context]
  (State remainder 0 context))

(define-fn parse [rule input context success-fn failure-fn]
  (c/parse make-state rule input context success-fn failure-fn))

(define-fn merge-replies [mergee merger]
  (assoc merger :result
    (update-in (-> merger :result force) [:error]
      c/merge-parse-errors (-> mergee :result force :error))))

(define-fn with-product [product]
  (fn with-product-rule [state]
    (Reply false
      (c/Success product state
        (c/ParseError (:position state) nil nil)))))

(def emptiness_ (with-product nil))

(define-fn- make-failed-reply
  ([state descriptors]
   (make-failed-reply state (first (:remainder state)) descriptors))
  ([state unexpected-token descriptors]
   (Reply false
     (c/Failure
       (c/ParseError (:position state) unexpected-token descriptors)))))

(def nothing-descriptors
  #{(c/ErrorDescriptor :label "absolutely nothing")})

(define-fn nothing_ [state]
  (make-failed-reply state nothing-descriptors))

(define-fn with-error [message]
  (fn with-error-rule [state]
    (make-failed-reply state #{(c/ErrorDescriptor :message message)})))

(letfn [(delayify [f] (fn [& args] (delay (force (apply f args)))))]
  (defmacro defn [fn-name & forms]
   `(do (d/defn-memo ~fn-name ~@forms)
        (alter-var-root (var ~fn-name) ~delayify)
        (var ~fn-name))))

(defmacro defn- [fn-name & forms]
  (list* `defn (vary-meta fn-name assoc :private true) forms))

(defn only-when [valid? message]
  (if-not valid? (with-error message) (with-product valid?)))

(define-fn combine [rule product-fn]
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
              (seq/separate :tokens-consumed?))]
      (if (empty? consuming-replies)
        (if (empty? empty-replies)
          (c/apply-rule nothing_ state)
          (let [empty-replies (seq/reductions merge-replies empty-replies)]
            (or (first (drop-while #(-> % :result force c/failure?)
                         empty-replies))
                (last empty-replies))))
        (first consuming-replies)))))

(m/defmonad parser-m
  "The monad that FnParse uses."
  [m-zero nothing_
   m-result with-product
   m-bind combine
   m-plus +])

(define-fn label [label-string rule]
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
  `(m/domonad parser-m ~steps ~product-expr)))

(define-fn validate [rule pred message]
  (for [product rule, _ (only-when (pred product) message)]
    product))

(define-fn anti-validate [rule pred message]
  (validate rule (complement pred) message))

(define-fn term [label-string predicate]
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
              (make-failed-reply state first-token nil)))
          (make-failed-reply state ::end-of-input nil))))))

(define-fn antiterm [label-string pred]
  (term label-string (complement pred)))

(def anything_
  (term "anything" (constantly true)))

(define-fn hook [semantic-hook subrule]
  (for [product subrule] (semantic-hook product)))

(define-fn chook [product subrule]
  (for [_ subrule] product))

(define-fn lit [token]
  (term (format "'%s'" token) #(= token %)))

(define-fn antilit [token]
  (term (str "anything except " token) #(not= token %)))

(define-fn set-lit [label-string tokens]
  (term label-string (set tokens)))

(define-fn anti-set-lit [label-string tokens]
  (antiterm label-string (tokens set)))

(define-fn cat [& subrules]
  (m/with-monad parser-m
    (m/m-seq subrules)))

(define-fn opt [rule]
  (+ rule emptiness_))

(define-fn lex [subrule]
  (fn [state]
    (-> state subrule
      (assoc :tokens-consumed? false))))

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

(define-fn mapcat [tokens]
  (apply cat (map lit tokens)))

(define-fn mapalt [f coll]
  (apply + (map f coll)))

(define-fn optcat [& rules]
  (opt (apply cat rules)))

(define-fn followed-by [rule]
  (fn [state]
    (let [result (-> state (c/apply-rule rule) :result force)]
      (if (c/failure? result)
        (Reply false result)
        ((with-product (:product result)) state)))))

(define-fn not-followed-by
  [label-string rule]
  (label label-string
    (fn not-followed-by-rule [state]
      (let [result (-> state (c/apply-rule rule) :result force)]
        (if (c/failure? result)
          (Reply false (c/Success true state (:error result)))
          (-> state (c/apply-rule nothing_) (assoc :error (:error result))))))))

(d/defvar end-of-input_
  (not-followed-by "the end of input" anything_)
  "WARNING: Because this is an always succeeding,
  always empty rule, putting this directly into a
  rep*/rep+/etc.-type rule will result in an
  infinite loop.")

(define-fn prefix [prefix-rule body]
  (for [_ prefix-rule, content body] content))

(define-fn suffix [body suffix-rule]
  (for [content body, _ suffix-rule] content))

(define-fn circumfix [prefix-rule body suffix-rule]
  (prefix prefix-rule (suffix body suffix-rule)))

(define-fn separated-rep [separator element]
  (for [first-element element
            rest-elements (rep* (prefix separator element))]
    (cons first-element rest-elements)))

(defmacro template-alt [argv expr & values]
  (let [c (count argv)]
   `(+ ~@(map (fn [a] (t/apply-template argv expr a))
           (partition c values)))))

(define-fn case-insensitive-lit [#^Character token]
  (+ (lit (Character/toLowerCase token))
     (lit (Character/toUpperCase token))))

(define-fn effects [f & args]
  (fn effects-rule [state]
    (apply f args)
    (c/apply-rule state emptiness_)))

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
  ([label-string minuend subtrahend]
   (label label-string
     (for [_ (not-followed-by nil subtrahend), product minuend]
       product)))
  ([label-string minuend first-subtrahend & rest-subtrahends]
   (except label-string minuend
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
      (let [reply (c/apply-rule state rule)]
        (update-in reply [:result] annotate)))))

(define-fn factor= [n rule]
  (->> rule (replicate n) (apply cat)))

(define-fn fetch-context_ [state]
  (c/apply-rule state (with-product (:context state))))

(def ascii-digits "0123456789")
(def lowercase-ascii-alphabet "abcdefghijklmnopqrstuvwxyz")
(def uppercase-ascii-alphabet "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
(def base-36-digits (str ascii-digits lowercase-ascii-alphabet))

(defn radix-digit
  ([base] (radix-digit (format "a base-%s digit" base) base))
  ([label-string base]
   {:pre #{(integer? base) (> base 0)}}
   (->> base-36-digits (take base) seq/indexed
     (mapalt (fn [[index token]]
               (chook index (case-insensitive-lit token))))
     (label label-string))))

(def decimal-digit_
  (radix-digit "a decimal digit" 10))

(def hexadecimal-digit_
  (radix-digit "a hexadecimal digit" 16))

(def uppercase-ascii-letter_
  (set-lit "an uppercase ASCII letter" uppercase-ascii-alphabet))

(def lowercase-ascii-letter_
  (set-lit "a lowercase ASCII letter" lowercase-ascii-alphabet))

(def ascii-letter_
  (label "an ASCII letter"
    (+ uppercase-ascii-letter_ lowercase-ascii-letter_)))

(def ascii-alphanumeric_
  (label "an alphanumeric ASCII character"
    (+ ascii-letter_ decimal-digit_)))

; (define rule (for [a anything_, b anything_] [a b]))
; (define rule (validate anything_ (partial = 'a)))
; (define rule (mapcat '[a b]))
; (define rule (lit \3))
; (define rule (lex (mapcat "let 3")))
; (define rule (+ (lex (mapcat "let 3")) (mapcat "la")))
; (define rule (lex (label "let expr" (mapcat "let 3"))))
; (define rule (+ (lex (label "let expr" (mapcat "let 3")))
;                (lit \3)))
; (define rule emptiness_)
; (define rule (rep* (antilit \3)))
; (define rule (rep* decimal-digit))
; (define rule (followed-by (mapcat "li")))

; (-> "lit 3" make-state rule println)
