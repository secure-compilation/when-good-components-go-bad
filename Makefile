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
	coqwc `find . -name "*.v" -not -path "./CompCert/*" -not -path ./Intermediate/Decomposition.v -not -path ./Intermediate/Composition.v -not -path ./Intermediate/PS.v -not -path ./Intermediate/Extra.v`

# Build the recomposition cone up to (and including) the does_prefix-transfer assembly.
# Builds only PaddingTransfer.vo's dependency cone (Definitions .. PaddingWf, PaddingTransfer),
# not the whole project. Use `make -j4 recomp`.
recomp: Makefile.coq
	+make -f Makefile.coq MicroPolicies/Recomposition/PaddingTransfer.vo

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony recomp
