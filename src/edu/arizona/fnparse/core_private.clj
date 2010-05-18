(ns edu.arizona.fnparse.core-private
  "This is a namespace *not* to be used by users of FnParse.
  It is a library that contains \"private\" functions that
  the FnParse core needs to use."
  {:author "Joshua Choi", :skip-wiki true}
  (:require [clojure.contrib [def :as d] [string :as str]]
            [clojure.set :as set])
  (:refer-clojure :exclude #{find}))
