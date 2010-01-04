(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound clojure.contrib.seq-utils))

(def ws-set (set " \t\n"))
(def ws (rep* (term "whitespace" ws-set)))
(def non-ws-char (antiterm "non-whitespace char" ws-set))

(def symbol-r
  (complex [first-letter ascii-letter, other-chars (rep* non-ws-char)]
    (->> other-chars (cons first-letter) (apply str) symbol)))

(def string-delimiter (lit \"))
(def string-r
  (complex [_ string-delimiter
            content (rep* (antilit \"))
            _ string-delimiter]
    (->> content flatten (apply str))))

(def object (alt string-r symbol-r decimal-number))

(-> "\"a35. " make-state object println)
