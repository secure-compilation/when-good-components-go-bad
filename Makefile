%: Makefile.coq phony
	+make -f Makefile.coq $@

all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

beancount:
	coqwc `find . -name "*.v" -not -path "./CompCert/*" -not -path ./Intermediate/Decomposition.v -not -path ./Intermediate/Composition.v -not -path ./Intermediate/PS.v -not -path ./Intermediate/Extra.v -not -path "./_opam/*"`

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony  
