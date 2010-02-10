(ns name.choi.joshua.fnparse.hound.test
  (:require [name.choi.joshua.fnparse.common :as c]
            [name.choi.joshua.fnparse.hound :as p]
            [clojure.test :as test]))

(defmethod test/assert-expr 'match?
  [msg [_ rule opts input product-pred & product-pred-args]]
  (c/match-assert-expr p/parse msg rule opts input product-pred
                       product-pred-args))

(defmethod test/assert-expr 'non-match?
  [msg [_ rule opts input descriptor-map]]
  (c/non-match-assert-expr p/parse msg rule opts input descriptor-map))
