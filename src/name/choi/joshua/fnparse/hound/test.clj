(ns name.choi.joshua.fnparse.hound.test
  (:use name.choi.joshua.fnparse.hound clojure.test)
  (:require [clojure.contrib.str-utils2 :as str]
            [name.choi.joshua.fnparse.common :as c]))

(defmethod assert-expr 'partial-match?
  [msg [_ input rule consumed-tokens-num product-pred & product-pred-args]]
  (let [input-count (count input)]
   `(letfn [(report-this#
              ([kind# format-template# expected-arg# actual-arg# & other-args#]
               (report {:type kind#, :message ~msg,
                        :expected (apply format format-template#
                                    expected-arg# other-args#),
                        :actual (apply format format-template#
                                  actual-arg# other-args#)}))
              ([kind#] (report {:type kind#, :message ~msg})))]
      (parse ~input ~rule
        (fn [actual-product# actual-remainder#]
          (let [actual-consumed-tokens-num#
                 (- ~input-count (count actual-remainder#))]
            (if (not= actual-consumed-tokens-num# ~consumed-tokens-num)
              (report-this# :fail "%s tokens consumed"
                ~consumed-tokens-num actual-consumed-tokens-num#)
              (if (not (~product-pred actual-product# ~@product-pred-args))
                (report-this# :fail "%s"
                  (format "a product P so that %s is true"
                    (list* '~product-pred '~'P '~product-pred-args))
                  (format "the unmatching product %s"
                    actual-product#))
                (report-this# :pass)))))
        (fn [expectation#]
          (let [unexpected-token# (:unexpected-token expectation#)]
            (report-this# :fail "%s at position %s"
              (->> expectation# :descriptors
                (map c/communique
                    #_(fn [{kind# :kind, message# :message}]
                       (format "%s (%s)" message# kind#)))
                (str/join " or "))
              (if (= unexpected-token# :nothing)
                "the end of the input (no more tokens)"
                (str "a token " unexpected-token# " (of the type "
                     (pr-str (type unexpected-token#)) ")"))
              (:position expectation#))))))))

(defmethod assert-expr 'full-match?
  [msg [_ input rule product-pred & product-pred-args]]
  (assert-expr msg
    (list* 'partial-match? input rule (count input) product-pred
           product-pred-args)))
