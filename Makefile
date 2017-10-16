
OCAMLFILES= \
	low/runR.ml \
	low/print.ml \
	low/lexer.mll \
	low/parser.mly

%: Makefile.coq phony
	+make -f Makefile.coq $@

all: all_coq all_interp

all_coq: Makefile.coq
	+make -f Makefile.coq all

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
	rm low/runR.native
	rm -R low/_build

low/runR.native: low/Extraction.vo ${OCAMLFILES}
	mv low.ml low/low.ml || true
	mv low.mli low/low.mli || true
	cd low ; ocamlbuild -use-menhir runR.native ; cd ..

