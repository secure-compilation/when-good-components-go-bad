%: Makefile.coq phony
	+make -f Makefile.coq $@

all: all_coq test 

all_coq: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -rf *.cmi *.cmx
	rm -f run_test.*
	rm -f bin/run_test
	rm -rf _build
	rm -rf ._d

run_test.ml: all_coq

test: run_test.ml ocaml/main.ml 
	rm -f run_test.mli
	ocamlopt -o bin/run_test run_test.ml ocaml/main.ml

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony test1 test2 run_test.ml 
