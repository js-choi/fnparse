(ns name.choi.joshua.fnparse.cat.test
  (:use name.choi.joshua.fnparse.cat clojure.test)
  (:require [name.choi.joshua.fnparse.common :as c]))

(defmethod assert-expr 'match?
  [msg [_ rule opts input product-pred & product-pred-args]]
  (c/match-assert-expr parse msg rule {} input product-pred
                       product-pred-args))

(defmethod assert-expr 'non-match?
  [msg [_ rule opts input descriptor-map]]
  (c/non-match-assert-expr parse msg rule opts input descriptor-map))
