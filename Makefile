
OCAMLFILES= \
	src/runR.ml \
	src/print.ml \
	src/hooks.ml \
	src/lexer.mll \
	src/parser.mly \
	src/parserUtils.ml \
	src/debug.ml \
	src/debugType.ml \
	src/funlist.mli

AT=

%: Makefile.coq phony
	${AT}+make -f Makefile.coq $@

all: all_coq all_interp all_html random

all_coq: Makefile.coq
	${AT}+make -f Makefile.coq all

all_html: Makefile.coq
	${AT}+make -f Makefile.coq html

doc: all_html

clean: Makefile.coq clean_interp clean_random
	${AT}+make -f Makefile.coq clean
	${AT}rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	${AT}coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

_CoqProject: ;

Makefile: ;

.PHONY: all clean clean_all doc all_interp clean_interp tlc clean_tlc run random clean_random

clean_all: clean clean_tlc
	${AT}rm src/initial.state || true
	${AT}rm Rlib/bootstrapping.state || true

tlc:
	${AT}cd lib/tlc ; make ; cd ../..

clean_tlc:
	${AT}cd lib/tlc ; make clean ; cd ../..

all_interp: src/runR.native src/runR.d.byte src/initial.state Rlib/bootstrapping.state

# Runs the program.
run: src/runR.native src/initial.state
	${AT}src/runR.native -initial-state src/initial.state

# Precomputes the initial state.
src/initial.state: src/runR.native
	${AT}# Note: the following command may take some time to execute.
	${AT}src/runR.native -non-interactive -final-state $@ > /dev/null

Rlib/bootstrapping.state: src/initial.state Rlib/bootstrapping.R
	${AT}cat Rlib/bootstrapping.R | src/runR.native -initial-state $< -final-state $@ > /dev/null

clean_interp:
	${AT}rm src/runR.native || true
	${AT}rm src/runR.d.byte || true
	${AT}rm -Rf src/_build || true
	${AT}rm -f extract.ml{,i} || true
	${AT}rm -f src/extract.ml{,i} || true
	${AT}rm -f src/funlist.ml || true
	${AT}# If there if a file src/funlist.v, it would also be a good idea to remove it, but this may removes a human-generated file.

src/funlist.ml: src/extract.mli src/gen-funlist.pl
	${AT}src/gen-funlist.pl

src/Extraction.vo: Makefile.coq
	${AT}+make -f Makefile.coq $@

src/extract.ml: src/Extraction.vo
	${AT}mv extract.ml $@ 2> /dev/null || true

src/extract.mli: src/Extraction.vo
	${AT}mv extract.mli $@ 2> /dev/null || true

src/runR.native: src/extract.ml src/extract.mli ${OCAMLFILES} src/funlist.ml
	${AT}cd src ; ocamlbuild -pkg extlib -use-menhir -menhir "menhir --explain" -tag 'optimize(3)' runR.native ; cd ..

# Debug mode
src/runR.d.byte: src/extract.ml src/extract.mli ${OCAMLFILES} src/funlist.ml
	${AT}cd src ; ocamlbuild -pkg extlib -use-menhir -menhir "menhir --explain" runR.d.byte ; cd ..

random: gen/gen.native
	${AT}mkdir gen/tests || true
	${AT}for i in `seq -w 99`; do gen/gen.native -smart -max-step 300 gen/gram > gen/tests/$$i.R; done

gen/gen.native: gen/gen.ml gen/lexer.mll gen/parser.mly
	${AT}cd gen ; ocamlbuild -pkg extlib -use-menhir -menhir "menhir --explain" gen.native ; cd ..

clean_random:
	${AT}rm gen/gen.native || true
	${AT}rm -Rf gen/_build || true
	${AT}rm -Rf gen/tests/*.R || true

