MLSRC = cyclic.ml fact.ml test.ml test2.ml
TOP = ../../..
COQGEN = $(TOP)/boot/ocamlrun $(TOP)/ocamlc -I $(TOP)/stdlib -c -coq

all: $(MLSRC:.ml=.v) Makefile.coq
	$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	rm -f $(MLSRC:.ml=.v)
	$(MAKE) -f Makefile.coq cleanall

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject Makefile: ;

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@

%.v: %.ml
	$(COQGEN) $< 

.PHONY: all clean
