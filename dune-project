(lang dune 2.7)

(name "dates_calc")
(authors
        "Aymeric Fromherz"
        "Denis Merigoux"
        "Raphaël Monat")
(maintainers
        "Raphaël Monat <raphael.monat@lip6.fr>")
(source (github CatalaLang/dates-calc))
(license "Apache-2.0")

(generate_opam_files false)

(package
 (name dates_calc)
 (synopsis "A date calculation library")
 (description
 "A date calculation library, with exact operators to add a given
 number of days to a date, and approximate operators to add months or
 years."
)
 (depends
        (ocaml (>= 4.11.0))
        (alcotest (>= 1.0.0))
        (qcheck (>= 0.10))
 )
)
