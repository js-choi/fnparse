(ns name.choi.joshua.fnparse.test-parse-json
  (:use clojure.contrib.test-is)
  (:require [name.choi.joshua.fnparse.json :as j]))

(defstruct node-s :kind :content)
(defstruct state-s :remainder :column :row)
(def make-node (partial struct node-s))
(def make-state (partial struct state-s))

(deftest number-lit
  (is (= (j/number-lit (make-state "123]" 3 4))
         [(make-node :scalar 123) (make-state (seq "]") 6 4)]))
  (is (= (j/number-lit (make-state "-123]" 3 4))
         [(make-node :scalar -123) (make-state (seq "]") 7 4)]))
  (is (= (j/number-lit (make-state "-123e3]" 3 4))
         [(make-node :scalar -123e3) (make-state (seq "]") 9 4)]))
  (is (= (j/number-lit (make-state "-123.9e3]" 3 4))
         [(make-node :scalar -123.9e3) (make-state (seq "]") 11 4)])))

(deftest unicode-char-sequence
  (is (= (j/unicode-char-sequence (make-state "u11A3a\"]" 3 4))
         [\u11A3 (make-state (seq "a\"]") 8 4)])))

(deftest escape-sequence
  (is (= (j/escape-sequence (make-state "\\\\a\"]" 3 4))
         [\\ (make-state (seq "a\"]") 5 4)]))
  (is (= (j/escape-sequence (make-state "\\u1111a\"]" 3 4))
         [\u1111 (make-state (seq "a\"]") 9 4)])))

(deftest string-lit
  (is (= (j/string-lit (make-state "\"hello\"]" 3 4))
         [(make-node :scalar "hello") (make-state (seq "]") 10 4)]))
  (is (= (j/string-lit (make-state "\"hello\\u1111\"]" 3 4))
         [(make-node :scalar "hello\u1111") (make-state (seq "]") 16 4)])))

(deftest entry
  (is (= (j/entry (make-state "\"hello\": 55}" 3 4))
         [[(make-node :scalar "hello") (make-node :scalar 55)]
          (make-state (seq "}") 14 4)])))

(deftest additional-entry
  (is (= (j/additional-entry (make-state ", \"hello\": 55}" 3 4))
         [[(make-node :scalar "hello") (make-node :scalar 55)]
          (make-state (seq "}") 16 4)])))

(deftest object
  (is (= (j/object (make-state "{\"hello\": 55}]" 3 4))
         [(make-node :object {(make-node :scalar "hello") (make-node :scalar 55)})
          (make-state (seq "]") 16 4)]))
  (is (= (j/object (make-state "{\"hello\": 55, \"B\": \"goodbye\"}]" 3 4))
         [(make-node :object {(make-node :scalar "hello") (make-node :scalar 55)
                              (make-node :scalar "B") (make-node :scalar "goodbye")})
          (make-state (seq "]") 32 4)])))

(deftest load-stream
  (is (= (j/load-stream "[1, 2, 3]") [1 2 3])
      "loading a flat vector containing integers")
  (is (= (j/load-stream "[\"a\", \"b\\n\", \"\\u1234\"]")
         ["a" "b\n" "\u1234"])
      "loading a flat vector containing strings")
  (is (= (j/load-stream "{\"a\": 1, \"b\\n\": 2, \"\\u1234\": 3}")
         {"a" 1, "b\n" 2, "\u1234" 3})
      "loading a flat object containing strings and integers"))

(time (run-tests))
