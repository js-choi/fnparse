(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound clojure.contrib.seq-utils))

(def ws-set (string-set " \t\n"))
(def ws (rep* (multilit "whitespace" ws-set)))
(def non-ws-char (anti-multilit "non-whitespace char" ws-set))
(def symbol-r
  (complex [first-letter ascii-letter, other-chars (rep* non-ws-char)]
    (->> other-chars (cons first-letter) (apply str) symbol)))
(def object (alt symbol-r decimal-number))

(-> "a35. " make-state object println)
