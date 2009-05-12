(ns name.choi.joshua.fnparse.test-parse-json
  (:use clojure.contrib.test-is)
  (:require [name.choi.joshua.fnparse.json :as j]))

(defstruct node-s :kind :content)
(def make-node (partial struct node-s))

(deftest number-lit
  (is (= (j/number-lit {:remainder "123]"}) [(make-node :scalar 123) {:remainder (seq "]")}])))

;(deftest load-stream
;  (is (= (j/load-stream "[1, 2, 3]") [1 2 3])
;      "loading a flat vector containing integers")
;  (is (= (j/load-stream "[\"a\", \"b\\n\", \"\\u1234\"]")
;         ["a" "b\n" "\u1234"])
;      "loading a flat vector containing strings")
;  (is (= (j/load-stream "{\"a\": 1, \"b\\n\": 2, \"\\u1234\": 3}")
;         {"a" 1, "b\n" 2, "\u1234" 3})
;      "loading a flat object containing strings and integers"))

(time (run-tests))
