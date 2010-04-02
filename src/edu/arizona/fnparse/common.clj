(ns edu.arizona.fnparse.common
  {:author "Joshua Choi", :skip-wiki true}
  (:require [clojure.contrib.def :as d] [clojure.set :as set])
  (:refer-clojure :exclude #{find})
  (:import [clojure.lang IPersistentMap]))

(defn- rule-doc-summary-header [obj-type-str]
  (format "\n
  Summary
  ======="
    obj-type-str))

(defn- rule-doc-first-header [library-name obj-type-str]
  (format "%s %s.\n\n  " library-name obj-type-str))

(d/defvar- rule-doc-info
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
