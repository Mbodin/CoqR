(lang dune 2.4)
(using coq 0.1)

(name CoqR)

(generate_opam_files true)
(license GPL-2.0-or-later)
(source (github Mbodin/CoqR))

(package
	(name CoqR)
	(depends Lib)
	(synopsis "A Coq formalisation of the R programming language"))

(package
	(name runR)
	(depends CoqR)
	(synopsis "R interpreter extracted from the Coq formalisation"))

(package
	(name Lib)
	(synopsis "Internal library for CoqR"))

