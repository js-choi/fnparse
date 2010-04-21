(ns edu.arizona.fnparse.core-private
  "This is a namespace *not* to be used by users of FnParse.
  It is a library that contains \"private\" functions that
  the FnParse core needs to use."
  {:author "Joshua Choi", :skip-wiki true}
  (:require [clojure.contrib [def :as d] [string :as str]]
            [clojure.set :as set])
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
