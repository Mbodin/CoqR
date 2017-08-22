MODULES := Low Structured High
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	        $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	        coq_makefile -R . Main -R low Low -R structured Structured -R high High -R lib Lib -R lib/tlc/src TLC $(VS) -o Makefile.coq

clean:: Makefile.coq
	        $(MAKE) -f Makefile.coq clean
			        rm -f Makefile.coq

