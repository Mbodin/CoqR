(lang dune 2.5)
(using coq 0.2)

(name CoqR)
(license GPL-2.0-or-later)
(source (github Mbodin/CoqR))

(generate_opam_files true)

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

