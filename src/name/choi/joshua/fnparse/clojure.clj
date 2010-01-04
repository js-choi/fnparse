(ns name.choi.joshua.fnparse.clojure
  (:use name.choi.joshua.fnparse.hound))

(def digit (mapalt "1234567890"))
(def number-sign (mapalt "+-"))
(def decimal-point (lit \.))

(-> "55" digit println)
