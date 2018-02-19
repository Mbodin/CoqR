
OCAMLFILES= \
	low/runR.ml \
	low/print.ml \
	low/hooks.ml \
	low/lexer.mll \
	low/parser.mly \
	low/parserUtils.ml \
	low/debug.ml \
	low/debugType.ml \
	low/funlist.mli

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

tlc:
	${AT}cd lib/tlc ; make ; cd ../..

clean_tlc:
	${AT}cd lib/tlc ; make clean ; cd ../..

all_interp: low/runR.native low/runR.d.byte low/initial.state

run: low/runR.native low/initial.state
	${AT}low/runR.native -initial-state low/initial.state

# To launch the program faster through the “make run” command.
low/initial.state: low/runR.native
	${AT}# Note: the following command may take some time to execute.
	${AT}low/runR.native -non-interactive -final-state low/initial.state > /dev/null

clean_interp:
	${AT}rm low/runR.native || true
	${AT}rm low/runR.d.byte || true
	${AT}rm -Rf low/_build || true
	${AT}rm -f low.ml{,i} || true
	${AT}rm -f low/low.ml{,i} || true
	${AT}rm -f low/funlist.ml || true
	${AT}# If there if a file low/funlist.v, it would also be a good idea to remove it, but this may removes a human-generated file.

low/funlist.ml: low/low.mli low/gen-funlist.pl
	${AT}low/gen-funlist.pl

low/Extraction.vo: Makefile.coq
	${AT}+make -f Makefile.coq $@

low/low.ml: low/Extraction.vo
	${AT}mv low.ml low/low.ml || true

low/low.mli: low/Extraction.vo
	${AT}mv low.mli low/low.mli || true

low/runR.native: low/low.ml low/low.mli ${OCAMLFILES} low/funlist.ml
	${AT}cd low ; ocamlbuild -pkg extlib -use-menhir -menhir "menhir --explain" -tag 'optimize(3)' runR.native ; cd ..

# Debug mode
low/runR.d.byte: low/low.ml low/low.mli ${OCAMLFILES} low/funlist.ml
	${AT}cd low ; ocamlbuild -pkg extlib -use-menhir -menhir "menhir --explain" runR.d.byte ; cd ..

random: gen/gen.native
	${AT}mkdir gen/tests || true
	${AT}for i in `seq -w 99`; do gen/gen.native -smart -max-step 300 gen/gram > gen/tests/$$i.R; done

gen/gen.native: gen/gen.ml gen/lexer.mll gen/parser.mly
	${AT}cd gen ; ocamlbuild -pkg extlib -use-menhir -menhir "menhir --explain" gen.native ; cd ..

clean_random:
	${AT}rm gen/gen.native || true
	${AT}rm -Rf gen/_build || true
	${AT}rm -Rf gen/tests/*.R || true

