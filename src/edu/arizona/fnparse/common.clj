(ns edu.arizona.fnparse.common
  "This is a namespace *not* to be used by users of FnParse.
  It is a library that contains \"private\" functions that
  are still common to both FnParse Hound and Cat."
  {:author "Joshua Choi", :skip-wiki true}
  (:require [clojure.contrib [def :as d] [string :as str] [seq :as seq]]
            [clojure.set :as set] [edu.arizona.fnparse.core :as c])
  (:refer-clojure :exclude #{find}))
