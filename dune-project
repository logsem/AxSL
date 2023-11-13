(lang dune 3.9)
(name coq-iris-axiomatic-arm)
(using coq 0.8)

(generate_opam_files true)

(authors
 "Zongyuan Liu <zy.liu@cs.au.dk>"
 "Angus Hammond <Angus.Hammond@cl.cam.ac.uk>"
 "Jean Pichon-Pharabod <jean.pichon@cs.au.dk>"
 "Thibaut Pérami <Thibaut.Perami@cl.cam.ac.uk>")

(maintainers
 "Zongyuan Liu <zy.liu@cs.au.dk>")

(source
 (github logsem/AxSL))

(package
  (name coq-iris-axiomatic-arm)
  (allow_empty)
  (depends
    (coq (= 8.16.1))
    (coq-record-update (= 0.3.2))
    (coq-hammer-tactics (= "1.3.2+8.16"))
    (coq-stdpp (= "dev.2023-08-03.3.4be5fd62"))
    (coq-stdpp-unstable (= "dev.2023-08-03.3.4be5fd62"))
    (coq-iris (= "dev.2023-08-11.1.81f394da"))
  )
)
