(ns edu.arizona.fnparse.cat.test
  (:require [edu.arizona.fnparse :as c]
            [edu.arizona.fnparse.cat :as p]
            [clojure.test :as test]))

(defmethod test/assert-expr 'match?
  [msg [_ rule input & opts]]
  (c/match-assert-expr p/parse msg rule input opts))

(defmethod test/assert-expr 'non-match?
  [msg [_ rule input & opts]]
  (c/non-match-assert-expr p/parse msg rule input opts))
