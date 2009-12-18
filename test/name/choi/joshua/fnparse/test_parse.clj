(ns name.choi.joshua.fnparse.cat.test-parse
  (:use clojure.test clojure.contrib.monads
        clojure.contrib.error-kit
        [clojure.contrib.except :only [throw-arg]])
  (:require name.choi.joshua.fnparse.cat))
            ; name.choi.joshua.fnparse.cat.json))

(time (run-tests 'name.choi.joshua.fnparse.cat))
;(time (test #'name.choi.joshua.fnparse.cat/anything))
;(time (test #'name.choi.joshua.fnparse.cat/direct-left-recursive-rule))
;(time (test #'name.choi.joshua.fnparse.cat/lr-test-term))
;(time (run-tests 'name.choi.joshua.fnparse.cat.json))
