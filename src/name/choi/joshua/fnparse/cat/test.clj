(ns name.choi.joshua.fnparse.cat.test
  (:use name.choi.joshua.fnparse.cat clojure.test)
  (:require [name.choi.joshua.fnparse.common :as c]))

(defmethod assert-expr 'partial-match? [msg args]
  (c/partial-match-assert-expr parse msg args))

(defmethod assert-expr 'full-match? [msg args]
  (c/full-match-assert-expr parse msg args))
