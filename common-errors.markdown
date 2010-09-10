Common Errors in FnParse 3
==========================

I'm starting to compile a list of errors that may commonly be encountered when FnParse 3 is used.

***

`java.lang.ClassCastException: edu.arizona.fnparse.core.NamedRule cannot be cast to clojure.lang.IFn`

This means that a `Rule` is being called as a function somewhere. The fact that it's specifically a `NamedRule`, which only `defrule`, `defmaker`, and `defmaker-macro` create, makes it probable that the programmer mistakenly defined a rule-maker with `defrule` instead of `defmaker`.

***

`java.lang.IllegalArgumentException: No implementation of method: :apply of protocol: #'edu.arizona.fnparse.core/Rule found for class: nil`

This means that there's a `nil` where a `Rule` should be. What probably happened is that there's a rule-maker somewhere that's somehow returning `nil`.
