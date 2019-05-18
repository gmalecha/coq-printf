all: Makefile.coq
	$(MAKE) -f Makefile.coq

test: all
	$(MAKE) -C test-suite

install: all
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
