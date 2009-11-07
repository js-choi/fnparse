  (ns name.choi.joshua.fnparse.test-parse-json
    (:use clojure.contrib.test-is)
    (:require [name.choi.joshua.fnparse.json :as j]
              [name.choi.joshua.fnparse :as p]))
  
  (defn- make-mock-state [tokens warnings column line]
      (make-mock-state-with-info (seq tokens)
        :warnings warnings, :line line, :column column))

  (deftest string-lit
    (is (= (string-lit (make-mock-state "\"hello\"]" [] 3 4))
           [(make-node :scalar "hello") (make-mock-state "]" [] 10 4)]))
    (is (= (string-lit (make-mock-state "\"hello\\u1111\"]" [] 3 4))
           [(make-node :scalar "hello\u1111") (make-mock-state "]" [] 16 4)])))
  
  (time (run-tests))
