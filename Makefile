
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

.PHONY: all clean clean_all phony all_interp clean_interp tlc clean_tlc

clean_all: clean clean_tlc

tlc:
	cd lib/tlc ; make ; cd ../..

clean_tlc:
	cd lib/tlc ; make clean ; cd ../..

all_interp: low/runR.native low/runR.d.byte

clean_interp:
	rm low/runR.native || true
	rm -Rf low/_build || true
	rm -f low.ml{,i} || true
	rm -f low/low.ml{,i} || true
	rm -f low/funlist.ml || true

low/funlist.ml: low/low.mli low/gen-funlist.pl
	low/gen-funlist.pl

low/low.ml: low/Extraction.vo
	mv low.ml low/low.ml || true

low/low.mli: low/Extraction.vo
	mv low.mli low/low.mli || true

low/runR.native: low/low.ml low/low.mli ${OCAMLFILES} low/funlist.ml
	cd low ; ocamlbuild -pkg extlib -use-menhir -menhir "menhir --explain" runR.native ; cd ..

# Debug mode
low/runR.d.byte: low/low.ml low/low.mli ${OCAMLFILES} low/funlist.ml
	cd low ; ocamlbuild -pkg extlib -use-menhir -menhir "menhir --explain" runR.d.byte ; cd ..

