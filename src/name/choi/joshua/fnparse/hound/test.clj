(ns name.choi.joshua.fnparse.hound.test
  (:require [name.choi.joshua.fnparse.common :as c]
            [name.choi.joshua.fnparse.hound :as p]
            [clojure.test :as test]))

(defmethod test/assert-expr 'match?
  [msg [_ rule input & opts]]
  (c/match-assert-expr p/parse msg rule input opts))

(defmethod test/assert-expr 'non-match?
  [msg [_ rule input & opts]]
  (c/non-match-assert-expr p/parse msg rule input opts))
