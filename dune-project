(lang dune 2.4)
(using coq 0.1)

(name CoqR)

(generate_opam_files true)
(license GPL-2.0-or-later)
(source (github Mbodin/CoqR))

(package
	(name CoqR)
	(synopsis "A Coq formalisation of the R programming language"))

(package
	(name runR)
	(synopsis "R interpreter extracted from the Coq formalisation"))

