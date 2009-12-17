(ns name.choi.joshua.fnparse.test-parse
  (:use clojure.test clojure.contrib.monads
        clojure.contrib.error-kit
        [clojure.contrib.except :only [throw-arg]])
  (:require name.choi.joshua.fnparse))
            ; name.choi.joshua.fnparse.json))

;(time (run-tests 'name.choi.joshua.fnparse))
;(time (test #'name.choi.joshua.fnparse/anything))
;(time (test #'name.choi.joshua.fnparse/direct-left-recursive-rule))
(time (test #'name.choi.joshua.fnparse/lr-test-term))
;(time (run-tests 'name.choi.joshua.fnparse.json))
