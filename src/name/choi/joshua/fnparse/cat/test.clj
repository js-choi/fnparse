(ns name.choi.joshua.fnparse.cat.test
  (:use name.choi.joshua.fnparse.cat clojure.test)
  (:require [name.choi.joshua.fnparse.common :as c]))

(defmethod assert-expr 'partial-match?
  [msg [_ rule input consumed-tokens-num product-pred & product-pred-args]]
  (c/match-assert-expr parse msg rule input consumed-tokens-num product-pred
                       product-pred-args))

(defmethod assert-expr 'full-match?
  [msg [_ rule input product-pred & product-pred-args]]
  (c/match-assert-expr parse msg rule input nil product-pred
                       product-pred-args))
