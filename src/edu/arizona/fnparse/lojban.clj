(ns edu.arizona.fnparse.lojban
  "A nascent parser for Lojban, post xorlo reform."
  {:author "Joshua Choi", :skip-wiki true}
  (:require [edu.arizona.fnparse [core :as r] [cat :as c]]
            [clojure.template :as t]
            [clojure.contrib [string :as str] [def :as d]]))

(d/defalias match c/match)
(d/defalias matches-seq c/matches-seq)
(d/defalias make-state c/make-state)

; Parses one word only.

(declare <nucleus> <voiced> <unvoiced> <silibant> <affricate>
  <h> <l> <m> <n> <r> <b> <d> <g> <v> <j> <z> <s> <c> <x> <k> <f> <p> <t>
  consonant-types <syllable-series> <rafsi-string> <initial-rafsi-series> <final-rafsi> <cmavo> <gismu> <cmevla-part-series> <nucleus-and-h-series> <cmevla> <Y> <Y-series>)

(def lerfu-strings
  {\a ["a"], \e ["e"], \i ["i"], \o ["o"], \u ["u"], \y ["y"]
   \' ["'" "h"], \l ["l"], \m ["m"], \n ["n"], \r ["r"]
   \b ["b"], \d ["d"], \g ["g"], \v ["v"], \j ["j"], \z ["z"]
   \s ["s"], \c ["c"], \x ["x"], \k ["k"], \f ["f"], \p ["p"], \t ["t"]})

(def selmaho-kws
  {"ca'a" :bai, "pu'i" :bai, "nu'o" :bai, "ka'e" :bai, "cu'e" :bai, "nau" :bai, "ru'i" :bai, "ta'e" :bai, "di'i" :bai, "na'o" :bai, "ve'u" :bai, "ve'a" :bai, "ve'i" :bai, "ve'e" :bai, "vi'i" :bai, "vi'a" :bai, "vi'u" :bai, "vi'e" :bai, "vi" :bai, "va" :bai, "vu" :bai, "du'a" :bai, "be'a" :bai, "ne'u" :bai, "vu'a" :bai, "ga'u" :bai, "ti'a" :bai, "ni'a" :bai, "ca'u" :bai, "zu'a" :bai, "ri'u" :bai, "ru'u" :bai, "re'o" :bai, "te'e" :bai, "bu'u" :bai, "ne'a" :bai, "pa'o" :bai, "ne'i" :bai, "to'o" :bai, "zo'i" :bai, "ze'o" :bai, "zo'a" :bai, "fa'a" :bai, "ze'u" :bai, "ze'a" :bai, "ze'i" :bai, "ze'e" :bai, "co'i" :bai, "pu'o" :bai, "co'u" :bai, "mo'u" :bai, "ca'o" :bai, "co'a" :bai, "de'a" :bai, "ba'o" :bai, "di'a" :bai, "za'o" :bai, "zu" :bai, "za" :bai, "zi" :bai, "ba" :bai, "pu" :bai, "ca" :bai, "ki" :bai, "du'o" :bai, "si'u" :bai, "zau" :bai, "ki'i" :bai, "du'i" :bai, "cu'u" :bai, "tu'i" :bai, "ti'u" :bai, "di'o" :bai, "ji'u" :bai, "ri'a" :bai, "ni'i" :bai, "mu'i" :bai, "ki'u" :bai, "va'u" :bai, "koi" :bai, "ca'i" :bai, "ta'i" :bai, "pu'e" :bai, "ja'i" :bai, "kai" :bai, "bai" :bai, "fi'e" :bai, "de'i" :bai, "ci'o" :bai, "mau" :bai, "mu'u" :bai, "ri'i" :bai, "ra'i" :bai, "ka'a" :bai, "pa'u" :bai, "pa'a" :bai, "le'a" :bai, "ku'u" :bai, "tai" :bai, "bau" :bai, "ma'i" :bai, "ci'e" :bai, "fau" :bai, "po'i" :bai, "cau" :bai, "ma'e" :bai, "ci'u" :bai, "ra'a" :bai, "pu'a" :bai, "li'e" :bai, "la'u" :bai, "ba'i" :bai, "ka'i" :bai, "sau" :bai, "fa'e" :bai, "be'i" :bai, "ti'i" :bai, "ja'e" :bai, "ga'a" :bai, "va'o" :bai, "ji'o" :bai, "me'a" :bai, "do'e" :bai, "ji'e" :bai, "pi'o" :bai, "gau" :bai, "zu'e" :bai, "me'e" :bai, "rai" :bai, "ba'e" :bahe, "za'e" :zahe, "be" :be, "bei" :bei, "be'o" :beho, "bo" :bo, "boi" :boi, "bu" :bu, "tei" :by, "foi" :by, "ce'a" :by, "lau" :by, "zai" :by, "tau" :by, "jo'o" :by, "ru'o" :by, "ge'o" :by, "je'o" :by, "lo'a" :by, "na'a" :by, "se'e" :by, "to'a" :by, "ga'e" :by, "y'y" :by, "by" :by, "cy" :by, "dy" :by, "fy" :by, "gy" :by, "jy" :by, "ky" :by, "ly" :by, "my" :by, "ny" :by, "py" :by, "ry" :by, "sy" :by, "ty" :by, "vy" :by, "xy" :by, "zy" :by, "cei" :cei, "co" :co, "doi" :doi, "ju'i" :doi, "coi" :doi, "fi'i" :doi, "ta'a" :doi, "mu'o" :doi, "fe'o" :doi, "co'o" :doi, "pe'u" :doi, "ke'o" :doi, "nu'e" :doi, "re'i" :doi, "be'e" :doi, "je'e" :doi, "mi'e" :doi, "ki'e" :doi, "vi'o" :doi, "cu" :cu, "do'u" :dohu, "fai" :fa, "fa" :fa, "fe" :fa, "fi" :fa, "fo" :fa, "fu" :fa, "fi'a" :fa, "fa'o" :faho, "fe'u" :fehu, "fi'o" :fiho, "ga" :ga, "ge'i" :ga, "ge" :ga, "go" :ga, "gu" :ga, "ge'u" :gehu, "gi" :gi, "gi'e" :giha, "gi'i" :giha, "gi'o" :giha, "gi'a" :giha, "gi'u" :giha, "no'u" :goi, "ne" :goi, "goi" :goi, "po'u" :goi, "pe" :goi, "po'e" :goi, "po" :goi, "mo" :goha, "nei" :goha, "go'u" :goha, "go'o" :goha, "go'i" :goha, "no'a" :goha, "go'e" :goha, "go'a" :goha, "du" :goha, "bu'a" :goha, "bu'e" :goha, "bu'i" :goha, "co'e" :cohe, "i" :i, "jai" :jai, "fa'u" :joi, "pi'u" :joi, "joi" :joi, "ce'o" :joi, "ce" :joi, "jo'u" :joi, "ku'a" :joi, "jo'e" :joi, "ju'e" :joi, "jo'i" :joi, "je'i" :joi, "je" :joi, "jo" :joi, "ja" :joi, "ju" :joi, "a" :joi, "e" :joi, "ji" :joi, "o" :joi, "u" :joi, "mi'i" :joi, "bi'o" :joi, "bi'i" :joi, "ge'a" :joi, "fu'u" :joi, "pi'i" :joi, "fe'i" :joi, "vu'u" :joi, "su'i" :joi, "ju'u" :joi, "gei" :joi, "pa'i" :joi, "fa'i" :joi, "te'a" :joi, "cu'a" :joi, "va'a" :joi, "ne'o" :joi, "de'o" :joi, "fe'a" :joi, "sa'o" :joi, "re'a" :joi, "ri'o" :joi, "sa'i" :joi, "pi'a" :joi, "si'i" :joi, "ke" :ke, "ke'e" :kehe, "kei" :kei, "da'u" :koha, "da'e" :koha, "di'u" :koha, "di'e" :koha, "de'u" :koha, "de'e" :koha, "dei" :koha, "do'i" :koha, "mi'o" :koha, "ma'a" :koha, "mi'a" :koha, "do'o" :koha, "ko'a" :koha, "fo'u" :koha, "ko'e" :koha, "ko'i" :koha, "ko'o" :koha, "ko'u" :koha, "fo'a" :koha, "fo'e" :koha, "fo'i" :koha, "fo'o" :koha, "vo'a" :koha, "vo'e" :koha, "vo'i" :koha, "vo'o" :koha, "vo'u" :koha, "ru" :koha, "ri" :koha, "ra" :koha, "ta" :koha, "tu" :koha, "ti" :koha, "zi'o" :koha, "ke'a" :koha, "ma" :koha, "zu'i" :koha, "zo'e" :koha, "ce'u" :koha, "da" :koha, "de" :koha, "di" :koha, "ko" :koha, "mi" :koha, "do" :koha, "ku" :ku, "ku'o" :kuho, "tu'a" :lahe, "lu'a" :lahe, "lu'o" :lahe, "la'e" :lahe, "vu'i" :lahe, "lu'i" :lahe, "lu'e" :lahe, "lai" :le, "la'i" :le, "la" :le, "lei" :le, "loi" :le, "le'i" :le, "lo'i" :le, "le'e" :le, "lo'e" :le, "lo" :le, "le" :le, "le'u" :lehu, "li" :li, "li'u" :lihu, "lo'o" :loho, "lo'u" :lohu, "lu" :lu, "lu'u" :luhu, "mai" :mai, "mo'o" :moho, "me" :me, "nu'a" :me, "ni'e" :nihe, "ni'o" :niho, "noi" :noi, "dau" :pa, "fei" :pa, "gai" :pa, "jau" :pa, "rei" :pa, "vai" :pa, "pi'e" :pa, "pi" :pa, "fi'u" :pa, "za'u" :pa, "me'i" :pa, "ni'u" :pa, "ki'o" :pa, "ce'i" :pa, "ma'u" :pa, "ra'e" :pa, "da'a" :pa, "so'a" :pa, "ji'i" :pa, "su'o" :pa, "su'e" :pa, "ro" :pa, "rau" :pa, "so'u" :pa, "so'i" :pa, "so'e" :pa, "so'o" :pa, "mo'a" :pa, "du'e" :pa, "te'o" :pa, "ka'o" :pa, "ci'i" :pa, "tu'o" :pa, "xo" :pa, "pai" :pa, "no'o" :pa, "no" :pa, "pa" :pa, "re" :pa, "ci" :pa, "vo" :pa, "mu" :pa, "xa" :pa, "ze" :pa, "bi" :pa, "so" :pa, "ni" :nu, "du'u" :nu, "si'o" :nu, "nu" :nu, "li'i" :nu, "ka" :nu, "jei" :nu, "su'u" :nu, "zu'o" :nu, "mu'e" :nu, "pu'u" :nu, "za'i" :nu, "roi" :roi, "re'u" :roi, "se" :se, "te" :se, "ve" :se, "xe" :se, "sei" :sei, "ti'o" :sei, "se'u" :sehu, "si" :si, "su" :su, "te'u" :tehu, "to" :to, "to'i" :to, "toi" :toi, "tu'e" :tuhe, "tu'u" :tuhu, "ra'o" :ui, "ke'i" :ui, "ga'o" :ui, "nai" :ui, "pei" :ui, "cai" :ui, "cu'i" :ui, "sai" :ui, "ru'e" :ui, "da'o" :ui, "fu'e" :ui, "fu'o" :ui, "i'a" :ui, "ie" :ui, "a'e" :ui, "u'i" :ui, "i'o" :ui, "i'e" :ui, "a'a" :ui, "ia" :ui, "o'i" :ui, "o'e" :ui, "e'e" :ui, "oi" :ui, "uo" :ui, "e'i" :ui, "u'o" :ui, "au" :ui, "ua" :ui, "a'i" :ui, "i'u" :ui, "ii" :ui, "u'a" :ui, "ui" :ui, "a'o" :ui, "ai" :ui, "a'u" :ui, "iu" :ui, "ei" :ui, "o'o" :ui, "e'a" :ui, "uu" :ui, "o'a" :ui, "o'u" :ui, "u'u" :ui, "e'o" :ui, "io" :ui, "e'u" :ui, "ue" :ui, "i'i" :ui, "u'e" :ui, "ba'a" :ui, "ja'o" :ui, "ca'e" :ui, "su'a" :ui, "ti'e" :ui, "ka'u" :ui, "se'o" :ui, "za'a" :ui, "pe'i" :ui, "ru'a" :ui, "ju'a" :ui, "ta'o" :ui, "ra'u" :ui, "li'a" :ui, "ba'u" :ui, "mu'a" :ui, "do'a" :ui, "to'u" :ui, "va'i" :ui, "pa'e" :ui, "zu'u" :ui, "sa'e" :ui, "la'a" :ui, "ke'u" :ui, "sa'u" :ui, "da'i" :ui, "je'u" :ui, "sa'a" :ui, "kau" :ui, "ta'u" :ui, "na'i" :ui, "jo'a" :ui, "bi'u" :ui, "li'o" :ui, "pau" :ui, "mi'u" :ui, "ku'i" :ui, "ji'a" :ui, "si'a" :ui, "po'o" :ui, "pe'a" :ui, "ro'i" :ui, "ro'e" :ui, "ro'o" :ui, "ro'u" :ui, "ro'a" :ui, "re'e" :ui, "le'o" :ui, "ju'o" :ui, "fu'i" :ui, "dai" :ui, "ga'i" :ui, "zo'o" :ui, "be'u" :ui, "ri'e" :ui, "se'i" :ui, "se'a" :ui, "vu'e" :ui, "ki'a" :ui, "xu" :ui, "ge'e" :ui, "bu'o" :ui, "vau" :vau, "vei" :vei, "ve'o" :veho, "vu'o" :vuho, "xi" :xi, "zei" :zei, "zi'e" :zihe, "zo" :zo, "zoi" :zoi, "zo'u" :zohu})

(defrecord Lerfu [canonical-char text-char-seq])

(d/defn-memo make-lerfu-record [canonical-char text-char-seq]
  {:pre [(every? char? text-char-seq) (char? canonical-char)]}
  (Lerfu. canonical-char text-char-seq))

(defn lerfu-record? [obj]
  (instance? Lerfu obj))

(defrecord Valsi [maintype subtype canonical-str text-str])

(defn make-valsi-record* [maintype subtype text-lerfu-seq]
  {:pre [(keyword? maintype) (keyword? subtype)
         #_(every? lerfu-record? text-lerfu-seq)]}
  (Valsi. maintype subtype
    (->> text-lerfu-seq (map :canonical-char) (apply str))
    (->> text-lerfu-seq (mapcat :text-char-seq) (apply str))))

(defn make-valsi-record [maintype subtype text-lerfu-tree]
  (make-valsi-record* maintype subtype
    (->> text-lerfu-tree flatten (filter identity))))

(defn make-cmavo-record [text-lerfu-tree]
  (let [record (make-valsi-record :cmavo :unknown text-lerfu-tree)
        standard-selmaho (selmaho-kws (:canonical-str record))]
    (if standard-selmaho
      (assoc record :subtype standard-selmaho)
      record)))

(defn hesitate-valsi-record [valsi-rec hesitation-text]
  {:pre [(instance? Valsi valsi-rec) (string? hesitation-text)]}
  (update-in valsi-rec [:text] #(str hesitation-text %)))

(defn case-insensitive-set [s]
  {:pre [(string? s)]}
  (into (set s) (str/swap-case s)))

(t/do-template [sym canonical-char]
  (c/defrule sym
    (let [phrases (lerfu-strings canonical-char)]
      (c/label (format "the vowel %s" (first phrases))
        (c/hook (partial make-lerfu-record canonical-char)
          (c/mapsum c/phrase phrases)))))
  <a> \a, <e> \e, <i> \i, <o> \o, <u> \u)

(d/defalias <space> c/<end-of-input>)

(c/defrule <y>
  (c/not-followed "the letter y"
    (c/hook (partial make-lerfu-record \y)
      (c/mapsum c/phrase (lerfu-strings \y)))
    <nucleus>))

(c/defrule <I>
  (c/label "an i or u" (c/suffix-peek (c/+ <i> <u>) <nucleus>)))

(c/defrule <V>
  (c/not-followed "a vowel" (c/+ <a> <e> <i> <o> <u>) <nucleus>))

(c/defrule <VV>
  (c/not-followed "a vowel pair"
    (c/+ (c/cat <a> (c/+ <i> <u>)) (c/cat <e> <i>) (c/cat <o> <i>))
    <nucleus>))

(c/defrule <nucleus> (c/label "a syllable nucleus" (c/+ <VV> <V> <y>)))

(c/defrule <h>
  (let [phrases (lerfu-strings \')]
    (c/label (format "the consonant \"%s\"" (first phrases))
      (c/hook (partial make-lerfu-record \')
        (c/suffix-peek (c/mapsum c/phrase phrases) <nucleus>)))))

(c/defmaker opposite-voice-rule [<r>]
  (condp #((%1 consonant-types) %2) <r>
    :voiced <unvoiced>
    :unvoiced <voiced>
    nil))

(t/do-template [sym canonical-char special-illegal-rules]
  (c/defrule sym
    (let [phrases (lerfu-strings canonical-char)]
      (apply c/not-followed (format "the consonant '%s'" (first phrases))
        (c/hook (partial make-lerfu-record canonical-char)
          (c/mapsum c/phrase phrases))
        <h> sym
        (if-let [<opposite-voice> (opposite-voice-rule sym)]
          (conj special-illegal-rules <opposite-voice>)
          special-illegal-rules))))
  <l> \l [], <m> \m [<z>], <n> \n [<affricate>], <r> \r []
  <b> \b [], <d> \d [], <g> \g [], <v> \v [], <j> \j [<z>], <z> \z [<j>]
  <s> \s [<c>], <c> \c [<s> <x>], <x> \x [<c> <k>], <k> \k [<x>]
  <f> \f [], <p> \p [], <t> \t [])

(def consonant-types
  {:voiced #{<b> <d> <g> <v> <j> <z>}, :unvoiced #{<s> <c> <x> <k> <f> <p> <t>},
   :silibant #{<l> <m> <n>}})

(t/do-template [rule-sym type-kw]
  (c/defrule rule-sym
    (c/label (format "a %s consonant" (name type-kw))
      (apply c/+ (consonant-types type-kw))))
  <voiced> :voiced, <unvoiced> :unvoiced, <silibant> :silibant)

(c/defrule <affricate>
  (c/+ (c/label "'tc'" (c/cat <t> <c>)) (c/label "'ts'" (c/cat <t> <s>))
       (c/label "'dj'" (c/cat <d> <j>)) (c/label "'dz'" (c/cat <d> <z>))))

(c/defrule <C> (c/label "a consonant" (c/+ <voiced> <unvoiced> <silibant>)))

(c/defrule <R> (c/+ (c/suffix-peek <r> <C>) (c/suffix-peek <n> <r>)))

(c/defrule <CR>
  (c/+ (c/cat <C> <R>)
       (c/suffix-peek (c/cat <r> <n>) <C>)
       (c/suffix-peek (c/cat <r> <l>) (c/+ <n> <affricate>))
       (c/suffix-peek (c/cat <n> <l>) <r>)))

(c/defrule <CC> (c/label "a consonant cluster" (c/cat <C> <C>)))

(c/defrule <liquid> (c/+ <l> <r>))

(c/defrule <middle>
  (c/+ <p> <b> <f> <v> <m>
       (c/not-followed "a middle 't'" <t> <l>)
       (c/not-followed "a middle 't'" <d> <l>)
       (c/not-followed "a middle 't'" <n> <l> <r>)
       <k> <g> <x>))

(c/defrule <sibilant>
  (c/+ <c>
       (c/not-followed "a sibilant 's'" <s> <x>)
       (c/not-followed "a sibilant 'j'" <j> <n> <l> <r>)
       (c/not-followed "a sibilant 'z'" <z> <n> <l> <r>)))

(c/defrule <onset>
  (c/label "a syllable onset"
    (c/suffix-peek
      (c/+ <h>
           (c/cat (c/opt <C>) <I>)
           <affricate>
           (c/cat (c/opt <sibilant>) (c/opt <middle>) (c/opt <liquid>)))
      <nucleus>)))

(c/defrule <coda> (c/except "a syllable coda" <C> <onset>))

(c/defrule <syllable>
  (c/cat (c/not-followed "a regular syllable onset" <onset> <y>)
         <nucleus>
         (c/opt <coda>)))

(c/defrule <syllable-series>
  (c/+ (c/cat <syllable-series> <syllable>) <syllable>))

(c/defrule <short-rafsi>
  (c/label "a short rafsi"
    (c/+ (c/cat <C> <V> <C>) (c/cat <CC> <V>) (c/cat <C> <VV> (c/opt <R>))
         (c/cat <C> <V> <h> <V> (c/opt <R>)))))

(c/defrule <y-rafsi>
  (c/label "a y-rafsi"
    (c/+ (c/cat <C> <V> <C> <C> <y>) (c/cat <CC> <V> <C> <y>)
         (c/cat <C> <V> <C> <y>))))

(c/defrule <full-rafsi>
  (c/label "a full rafsi"
    (c/+ (c/cat <C> <V> <C> <C> <V>) (c/cat <CC> <V> <C> <V>))))

(c/defrule <classifier>
  (c/label "a classifier rafsi"
    (c/+ (c/cat <C> <V> <C> <CR>) (c/cat <CC> <V> <CR>) (c/cat <C> <V> <CR>)
         (c/cat <y-rafsi> <R>))))

(c/defrule <y-less-rafsi>
  (c/label "a y-less rafsi"
    (c/suffix-peek <short-rafsi> <rafsi-string>)))

(c/defrule <rafsi-string>
  (c/label "a string of rafsi"
    (c/+ (c/cat <y-less-rafsi> <rafsi-string>)
         <gismu> <final-rafsi> <y-rafsi> (c/cat <CC> <y>)
         (c/cat <h> <y>) (c/cat <full-rafsi> <h> <y>))))

(c/defrule <slinkuhi-invalid-rafsi>
  (c/label "a slinku'i-like rafsi" (c/cat <C> <rafsi-string>)))

(c/defrule <fuhivla-rafsi>
  (c/except "a fu'ivla rafsi" (c/cat <syllable-series> <onset> <y>)
    <cmavo> <rafsi-string> <slinkuhi-invalid-rafsi>))

(c/defrule <type-3-rafsi>
  (c/label "a type-3 rafsi"
    (c/cat <classifier> (c/opt <syllable-series>) <onset> <y>)))

(c/defrule <brivla-rafsi>
  (c/except "a brivla rafsi" (c/cat <syllable> <syllable-series> <h> <y>)
    <cmavo> <slinkuhi-invalid-rafsi>))

(c/defrule <initial-rafsi>
  (c/label "an initial rafsi"
    (c/+ <y-less-rafsi> <y-rafsi> <fuhivla-rafsi> <type-3-rafsi> <brivla-rafsi>)))

(c/defrule <initial-rafsi-series>
  (c/+ (c/cat <initial-rafsi-series> <initial-rafsi>) <initial-rafsi>))

(c/defrule <final-rafsi>
  (c/except "a final rafsi" (c/cat <short-rafsi> <space>)
    <cmevla>))

(c/defrule <gismu>
  (c/label "a gismu" (c/cat <full-rafsi> <space>)))

(c/defrule <fuhivla-root>
  (c/except "a fu'ivla root"
    (c/cat <syllable> <syllable-series> <space>)
    <cmevla> <cmavo>))

(c/defrule <type-3-fuhivla>
  (c/except "a type-3 fu'ivla" (c/cat <classifier> <syllable-series> <space>)
    <cmevla>))

(c/defrule <lujvo>
  (c/except "a lujvo"
    (c/cat <initial-rafsi-series>
           (c/+ <final-rafsi> <gismu> <fuhivla-root> <type-3-fuhivla>))
    <cmavo> <h>))

(c/defrule <type-4-fuhivla>
  (c/except "a type-4 fu'ivla" <fuhivla-root> <h>))

(c/defrule <cmevla-part>
  (c/+ <V> <VV> <y> <I> <h>
       (c/not-followed "a consonant inside a cmevla" <C> <space>)))

(c/defrule <cmevla-part-series>
  (c/+ (c/cat <cmevla-part-series> <cmevla-part>) <cmevla-part>))

(c/defrule <cmevla>
  (c/except "cmevla" (c/cat <cmevla-part-series> <C> <space>) <h>))

(def make-brivla-record (partial make-valsi-record :brivla))

(c/defrule <brivla>
  (c/label "a brivla"
    (c/+ (c/hook (partial make-brivla-record :gismu) <gismu>)
         (c/hook (partial make-brivla-record :type-4-fuhivla) <type-4-fuhivla>)
         (c/hook (partial make-brivla-record :type-3-fuhivla) <type-3-fuhivla>)
         (c/hook (partial make-brivla-record :lujvo) <lujvo>)
         (c/hook (partial make-brivla-record :cmevla) <cmevla>))))

(c/defrule <post-cmavo> (c/+ <space> <cmavo> <brivla>))

(c/defrule <CVCy-lujvo>
  (c/label "a CVCy lujvo"
    (c/cat <C> <V> <C> <y> <initial-rafsi-series>
           (c/+ <final-rafsi> <gismu> <fuhivla-root> <type-3-fuhivla>))))

(c/defrule <nucleus-and-h-series>
  (c/+ (c/cat <nucleus-and-h-series> <h> <nucleus>) <nucleus>))

(c/defrule <cmavo>
  (c/except "a cmavo"
    (c/hook make-cmavo-record
      (c/suffix-peek (c/cat (c/opt <C>) (c/opt <I>) <nucleus-and-h-series>)
        <post-cmavo>))
    <cmevla> <CVCy-lujvo>))

(c/defrule <Y>
  (c/not-followed "hesitation"
    (c/for [lerfu-record <y>]
      (make-valsi-record :cmavo :Y [lerfu-record]))
    <nucleus>))

(c/defrule <valsi>
  (c/+ <Y> <brivla> <cmavo>))

(defn chunk-words [chunk]
  (c/matches-seq chunk <valsi>))

(defn text-words [text]
  {:pre [(string? text)]}
  (->> text (str/split #"( \.)+") (mapcat #(chunk-words (make-state %)))))


