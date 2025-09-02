(lang dune 3.8)

(name vcpu)

(generate_opam_files true)

(source
 (github afdw/vcpu))

(using coq 0.8)

(package
 (name vcpu)
 (synopsis "Verified CPU")
 (description "Verified CPU")
 (depends ocaml dune rocq-core rocq-stdlib))
