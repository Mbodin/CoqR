
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

all: all_coq all_interp all_html

all_coq: Makefile.coq
	${AT}+make -f Makefile.coq all

all_html: Makefile.coq
	${AT}+make -f Makefile.coq html

clean: Makefile.coq clean_interp
	${AT}+make -f Makefile.coq clean
	${AT}rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	${AT}coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean clean_all phony all_interp clean_interp tlc clean_tlc run

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

low/low.ml: low/Extraction.vo
	${AT}mv low.ml low/low.ml || true

low/low.mli: low/Extraction.vo
	${AT}mv low.mli low/low.mli || true

low/runR.native: low/low.ml low/low.mli ${OCAMLFILES} low/funlist.ml
	${AT}cd low ; ocamlbuild -pkg extlib -use-menhir -menhir "menhir --explain" runR.native ; cd ..

# Debug mode
low/runR.d.byte: low/low.ml low/low.mli ${OCAMLFILES} low/funlist.ml
	${AT}cd low ; ocamlbuild -pkg extlib -use-menhir -menhir "menhir --explain" runR.d.byte ; cd ..

