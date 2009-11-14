(ns name.choi.joshua.fnparse.test-parse
  (:use clojure.test clojure.contrib.monads
        clojure.contrib.error-kit
        [clojure.contrib.except :only [throw-arg]])
  (:require name.choi.joshua.fnparse
            name.choi.joshua.fnparse.json))

(time (run-tests 'name.choi.joshua.fnparse))
(time (run-tests 'name.choi.joshua.fnparse.json))
