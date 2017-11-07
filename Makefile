
OCAMLFILES= \
	low/runR.ml \
	low/print.ml \
	low/lexer.mll \
	low/parser.mly \
	low/parserUtils.ml \
	low/debug.ml \
	low/debugType.ml \
	low/funlist.mli

%: Makefile.coq phony
	+make -f Makefile.coq $@

all: all_coq all_interp all_html

all_coq: Makefile.coq
	+make -f Makefile.coq all

all_html: Makefile.coq
	+make -f Makefile.coq html

clean: Makefile.coq clean_interp
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony all_interp clean_interp

all_interp: low/runR.native

clean_interp:
	rm low/runR.native || true
	rm -R low/_build || true
	rm -f low/funlist.ml || true

low/funlist.ml: low/Extraction.vo low/gen-funlist.pl
	low/gen-funlist.pl

low/runR.native: low/Extraction.vo ${OCAMLFILES} low/funlist.ml
	mv low.ml low/low.ml || true
	mv low.mli low/low.mli || true
	cd low ; ocamlbuild -pkg extlib -use-menhir -menhir "menhir --explain" runR.native ; cd ..

