(ns name.choi.joshua.fnparse.test-parse
  (:use clojure.test clojure.contrib.monads
        clojure.contrib.error-kit
        [clojure.contrib.except :only [throw-arg]])
  (:require [name.choi.joshua.fnparse :as p]))

(time (run-tests 'name.choi.joshua.fnparse))
