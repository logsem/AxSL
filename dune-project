(lang dune 3.9)
(name coq-iris-axiomatic-arm)
(using coq 0.8)

(generate_opam_files true)

(package
  (name coq-iris-axiomatic-arm)
  (allow_empty)
  (depends
    (coq (= 8.19.2))
    (coq-equations (= "1.3+8.19"))
    (coq-record-update (= 0.3.4))
    (coq-hammer-tactics (= "1.3.2+8.19"))
    (coq-stdpp (= "1.11.0"))
    (coq-stdpp-bitvector (= "1.11.0"))
    (coq-iris (= "4.3.0"))
  )
)
