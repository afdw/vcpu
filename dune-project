(lang dune 3.8)

(name vcpu-plugin)

(generate_opam_files true)

(source
 (github afdw/vcpu))

(authors "Anton Danilkin")

(maintainers "Anton Danilkin")

(using coq 0.8)

(package
 (name vcpu-plugin)
 (synopsis "Verified CPU Coq plugin")
 (description "Verified CPU Coq plugin")
 (depends ocaml dune coq-core))
