(ns edu.arizona.fnparse.common
  {:author "Joshua Choi"}
  (:require [edu.arizona.fnparse.base :as base] [clojure.contrib.def :as d]
            [clojure.set :as set])
  (:refer-clojure :exclude #{find})
  (:import [clojure.lang IPersistentMap]))

(defn rule-doc-summary-header [obj-type-str]
  (format "\n
  Summary
  ======="
    obj-type-str))

(defn- rule-doc-first-header [library-name obj-type-str]
  (format "%s %s.\n\n  " library-name obj-type-str))

(def rule-doc-info
  {:succeeds "Success"
   :product "Product"
   :consumes "Consumes"
   :error "Error"})

(defn rule-doc-str [doc-str library-name obj-type-str meta-opts]
  (let [doc-str (or doc-str "No description available.")
        doc-str (str (rule-doc-first-header library-name obj-type-str) doc-str)
        doc-opts (select-keys meta-opts (keys rule-doc-info))
        opt-seq (seq doc-opts)]
    (if opt-seq
      (->> doc-opts sort
        (map #(format "  * %s: %s" (rule-doc-info (key %)) (val %)))
        (interpose "\n")
        (apply str doc-str (rule-doc-summary-header obj-type-str) "\n"))
      doc-str)))

(defmacro general-defrule [library-name rule-name doc-string meta-opts form]
 `(let [rule-var# (d/defvar ~rule-name ~form ~doc-string)]
    (alter-meta! rule-var# update-in [:doc] rule-doc-str
      ~library-name "rule" ~meta-opts)
    rule-var#))

(defmacro general-defmaker [library-name obj-type-str def-form fn-name & forms]
 `(let [maker-var# (~def-form ~fn-name ~@forms)]
    (alter-var-root maker-var# identity)
    ; Add extended documentation.
    (alter-meta! maker-var# update-in [:doc] rule-doc-str
      ~library-name ~obj-type-str (meta maker-var#))
    ; Memoize unless the :no-memoize meta flag is true.
    (if-not (:no-memoize? (meta maker-var#))
      (alter-var-root maker-var# memoize))
    maker-var#))

(defn- print-complete [product]
  (printf
    "COMPLETE MATCH
==============
* Final product: %s
* Final product type: %s
"
    (pr-str product) (type product))
  true)

(defn- print-incomplete [string-input? product final-remainder]
  (printf
    "INCOMPLETE MATCH
================
* Final product: %s
* Final product type: %s
* Unmatched remainder: %s
"
    (pr-str product) (type product)
    (base/format-remainder string-input? final-remainder))
  false)

(defn print-success [string-input? product final-remainder]
  (if (empty? final-remainder)
    (print-complete product)
    (print-incomplete string-input? product final-remainder)))

(defn print-failure [error]
  (printf
    "FAILED MATCH
=============
%s
"
    (base/format-parse-error error))
  false)

(defn match
  "The general matching function of FnParse Hound. Attempt to
  match the given rule to at least the beginning of the given input.
  
  *   `rule`: The rule to match with.
  *   `state`: The initial state.
  *   `success-fn`: A function called when the rule
      matches the input.
      `(complete-fn final-product final-remainder)` is called.
  *   `failure-fn`: A function called when the rule does not
      match the input. `(failure-fn final-error)` is called,
      where `final-error` is an object of type
      `:edu.arizona.fnparse/ParseError`.
    
  If `success-fn` and `failure-fn` aren't included, then
  `match` will print out a report of the parsing result."
  ([rule state success-fn failure-fn]
   (let [result (-> state (base/apply rule) base/answer-result)]
     (if (base/failure? result)
       (failure-fn (:error result))
       (success-fn (:product result) (-> result :state base/get-remainder)))))
  ([rule state]
   (let [string-input? (string? (base/get-remainder state))]
     (match rule state
       (partial print-success string-input?)
       print-failure))))

(defn- find*
  [rule input context state-0]
  (when-let [input (seq input)]
    (lazy-seq
      (match rule (base/make-another-state state-0 input context)
        (fn find-success [product remainder]
          (cons product (find* rule remainder context state-0)))
        (fn find-failure [_]
          (find* rule (rest input) context state-0))))))

(defn find
  "Finds all occurrences of a rule in a sequence of tokens.
  Returns a lazy sequence of the rule's products at each
  occurence. The occurences do not overlap."
  [rule state]
  (find* rule (base/get-remainder state) (:context state) state))

#_(defn substitute
  "Substitutes all occurences of a rule in a sequence of tokens
  with their respective products. Returns a lazy sequence of
  tokens and products.
  
  `flatten?` is a boolean. If it is true, then the substituting
  products will be flattened into the input sequence; in that
  case the products must always be Seqables."
  [rule flatten? state]
  (let [combining-fn (if flatten? concat cons)]
    (when-let [input (seq input)]
      (lazy-seq
        (match rule context
          (fn substitute-success [product remainder]
            (combining-fn product
              (substitute match-fn rule context flatten? remainder)))
          (fn substitute-failure [_]
            (cons (first input)
              (substitute match-fn rule context flatten? (rest input))))
          input)))))

#_(defn substitute-1
  "Substitutes the first occurence of a rule in a sequence of
  tokens with its respective product. Returns a lazy sequence
  of tokens and products.
  
  See `substitute`'s docs for information on `flatten?`."
  [rule context flatten? input]
  (let [combining-fn (if flatten? concat cons)]
    (when-let [input (seq input)]
      (lazy-seq
        (match-fn rule context
          (fn substitute-1-success [product remainder]
            (combining-fn product remainder))
          (fn substitute-1-failure [_]
            (cons (first input)
              (substitute-1 match-fn rule context flatten? (rest input))))
          input)))))

(defn merge-parse-errors
  "Merges two ParseErrors together. If the two errors are at the same
  position, their descriptors are combined. If one of the errors
  is at a further position than the other, than that first error
  is returned instead."
  [error-a error-b]
  (let [{position-a :position, descriptors-a :descriptors} error-a
        {position-b :position, descriptors-b :descriptors} error-b]
    (cond
      (or (> position-b position-a) (empty? descriptors-a)) error-b
      (or (< position-b position-a) (empty? descriptors-b)) error-a
      true (assoc error-a :descriptors
             (set/union descriptors-a descriptors-b)))))
