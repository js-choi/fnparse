(ns name.choi.joshua.fnparse.hound.test
  (:use name.choi.joshua.fnparse.hound clojure.test)
  (:require [clojure.contrib.str-utils2 :as str]
            [name.choi.joshua.fnparse.common :as c]))

(defmethod assert-expr 'partial-match?
  [msg [_ input rule consumed-tokens-num product-pred & product-pred-args]]
  (let [input-count (count input)]
   `(letfn [(report-this#
              ([kind# expected-arg# actual-arg#]
               (report {:type kind#, :message ~msg,
                        :expected expected-arg#,
                        :actual actual-arg#}))
              ([kind#] (report {:type kind#, :message ~msg})))]
      (parse ~input ~rule
        (fn [actual-product# actual-remainder#]
          (let [actual-consumed-tokens-num#
                 (- ~input-count (count actual-remainder#))]
            (if (not= actual-consumed-tokens-num# ~consumed-tokens-num)
              (report-this# :fail
                (format "%s tokens consumed by the rule" ~consumed-tokens-num)
                (format "%s tokens actually consumed"
                        actual-consumed-tokens-num#)
              (if (not (~product-pred actual-product# ~@product-pred-args))
                (report-this# :fail
                  (list* '~product-pred '~'rule-product '~product-pred-args)
                  (list '~'not (list* '~product-pred actual-product#
                                      '~product-pred-args)))
                (report-this# :pass))))))
        (fn [error#]
          (report-this# :fail
            (format "a valid input for the given rule '%s'" '~rule)
            (c/format-parse-error error#)))))))

(defmethod assert-expr 'full-match?
  [msg [_ input rule product-pred & product-pred-args]]
  (assert-expr msg
    (list* 'partial-match? input rule (count input) product-pred
           product-pred-args)))
