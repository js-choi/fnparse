# Farewell to FnParse

This library is **deprecated**. You’re free to fork it as per the [CPL](https://en.wikipedia.org/wiki/Common_Public_License), but don’t use it for production. For general-purpose parsing in Clojure, use an alternative, living library such as:

* [clojure.spec by Rich Hickey et al.](http://clojure.org/about/spec)
* [Instaparse by Mark Engelberg](https://github.com/Engelberg/instaparse)
* [pex by Ghadi Shayban](https://github.com/ghadishayban/pex)
* [sequex by Jonathan Claggett](https://github.com/jclaggett/seqex)
* [squarepeg by Eric Normand](https://github.com/ericnormand/squarepeg)

Long ago, while Clojure was still young, I wrote FnParse as an exercise in monadic parsing. I was merely a college pre-medical student, but programming was a fun, rewarding activity that helped me in my research. But in the years since, my life has really changed, and my time for programming has been sadly very scarce. It is with a heavy heart, then, that I explicitly deprecate FnParse today.

Of course, any users left of this library have long known this; the most-recent previous commit was in 2010. In the interim, I’ve thought often about FnParse with much guilt. It’s freely licensed open source, of course, and people can copy, fork, and adapt it freely for their use. And life has been very, very busy. But it was still embarrassing. I wanted to come out with a better version before I would publicly publish any more code. But that time won’t be for a while, and this, for now, is for the best.

I still want to make a better rewrite, under a new name—but in the meantime, I’ll keep this repository up for historical purposes. My apologies to everyone ever inconvenienced, especially those who contributed any pull requests or issues.

J S C
2016-06-07

***

FnParse is a library for creating functional parsers in the Clojure programming
language. It presents an easy, functional way to create parsers from EBNF rules and
was inspired by the paper Using Functional Parsing to Achieve Quality in Software
Maintenance (http://citeseer.ist.psu.edu/148293.html).

FnParse's distribution has src and test folders. To use FnParse, download this
distribution and include its src folder in your program's classpath—for instance,
  java -cp $CLOJURE_PATH:path-to-FnParse-folder/src/ ...

FnParse's namespace is name.choi.joshua.fnparse.

FnParse's unit tests are stored in the tests folder and use the test-is library
from clojure-contrib, the Clojure standard library.

For documentation, go to: http://github.com/joshua-choi/fnparse/wikis

 *   FnParse
 *   Copyright (c) 2009 Joshua Choi. All rights reserved.
 *   The use and distribution terms for this software are covered by the
 *   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
 *   which can be found in the file epl-v10.html at the root of this distribution.
 *   By using this software in any fashion, you are agreeing to be bound by
 * 	 the terms of this license.
 *   You must not remove this notice, or any other, from this software.
