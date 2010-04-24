(ns edu.arizona.fnparse.common
  "This is a namespace *not* to be used by users of FnParse.
  It is a library that contains \"private\" functions that
  are still common to both FnParse Hound and Cat."
  {:author "Joshua Choi", :skip-wiki true}
  (:require [clojure.contrib [def :as d] [string :as str]]
            [clojure.set :as set] [edu.arizona.fnparse.core :as c])
  (:refer-clojure :exclude #{find}))

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

(defn assoc-label-in-descriptors
  "Removes all labels from the given `descriptors` set, then adds the
  given `label-str`."
  [descriptors label-str]
  {:pre #{(set? descriptors) (string? label-str)}}
  (let [descriptors (set/select #(not= (:kind %) :label) descriptors)
        new-descriptor (c/make-error-descriptor :label label-str)
        descriptors (conj descriptors new-descriptor)]
    descriptors))
