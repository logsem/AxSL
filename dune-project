(lang dune 3.9)
(name coq-iris-axiomatic-arm)
(using coq 0.8)

(generate_opam_files true)

(package
  (name coq-iris-axiomatic-arm)
  (allow_empty)
  (depends
    (coq (= 8.18.0))
    (coq-record-update (= 0.3.3))
    (coq-hammer-tactics (= "1.3.2+8.18"))
    (coq-stdpp (= "1.10.0"))
    (coq-stdpp-bitvector (= "1.10.0"))
    (coq-iris (= "4.2.0"))
  )
)
