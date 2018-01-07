%: Makefile.coq phony
	+make -f Makefile.coq $@

all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -rf *.cmi *.cmx
	rm -f run_test*
	rm -rf _build
	rm -rf ._d

ocaml:  
	+make clean
	+make all
	rm -f run_test.mli
	cat ocaml/main.ml >> run_test.ml
	ocamlopt -o run_test run_test.ml

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony ocaml
