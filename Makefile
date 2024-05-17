all: coq # plugin

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

install: coq # plugin
	$(MAKE) -f Makefile.coq install
	# $(MAKE) -f Makefile.plugin install

doc : Makefile.coq
	$(MAKE) -f Makefile.coq html

uninstall: coq # plugin
	$(MAKE) -f Makefile.coq uninstall
	# $(MAKE) -f Makefile.plugin uninstall

.PHONY: plugin

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
