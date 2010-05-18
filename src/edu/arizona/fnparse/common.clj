(ns edu.arizona.fnparse.common
  "This is a namespace *not* to be used by users of FnParse.
  It is a library that contains \"private\" functions that
  are still common to both FnParse Hound and Cat."
  {:author "Joshua Choi", :skip-wiki true}
  (:require [clojure.contrib [def :as d] [string :as str] [seq :as seq]]
            [clojure.set :as set] [edu.arizona.fnparse.core :as c])
  (:refer-clojure :exclude #{find}))

(d/defvar- rule-doc-summary-header
  "\n
  Rule Summary
  ============")

(d/defvar- rule-doc-info
  {:succeeds "Success"
   :product "Product"
   :consumes "Consumes"
   :error "Error"})

(defn rule-doc-str [doc-str meta-opts]
  (let [doc-str (or doc-str "No description available.")
        doc-opts (select-keys meta-opts (keys rule-doc-info))
        opt-seq (seq doc-opts)]
    (if opt-seq
      (->> doc-opts sort
        (map #(format "  * %s: %s" (rule-doc-info (key %)) (val %)))
        (interpose "\n")
        (apply str doc-str rule-doc-summary-header "\n"))
      doc-str)))

(defmacro general-defrule [rule-name doc-string meta-opts form]
 `(let [rule-var# (d/defvar ~rule-name ~form ~doc-string)]
    (alter-meta! rule-var# update-in [:doc] rule-doc-str ~meta-opts)
    rule-var#))

(defmacro general-defmaker [def-form fn-name & forms]
 `(let [maker-var# (~def-form ~fn-name ~@forms)]
    (alter-var-root maker-var# identity)
    ; Add extended documentation.
    (alter-meta! maker-var# update-in [:doc] rule-doc-str (meta maker-var#))
    ; Memoize unless the :no-memoize meta flag is true.
    (when-not (:no-memoize? (meta maker-var#))
      (alter-var-root maker-var# memoize))
    maker-var#))

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

(defn label-exception-descriptor [descriptor lbl]
  (if (c/exception-descriptor? descriptor)
    (assoc descriptor :main-lbl lbl)
    descriptor))

(defn assoc-label-in-descriptors
  "Removes all labels from the given `descriptors` set, then adds the
  given `label-str`."
  [descriptors lbl]
  {:pre #{(set? descriptors)}, #_:post #_ [(set? %)]}
  (let [descriptors (set/select (complement c/label-descriptor?) descriptors)
        descriptors (set (map #(label-exception-descriptor % lbl) descriptors))
        new-label-descriptor (c/make-label-descriptor lbl)
        descriptors (conj descriptors new-label-descriptor)]
    descriptors))
