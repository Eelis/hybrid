SHELL := /bin/sh

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean all config dist doc install-dist install-doc tags

CoRN := /home/koper/CoRN
CoLoR := /home/koper/color/color/
COQMAKE := $(MAKE) -f Makefile.coq
EXAMPLES := thermostat
EXAMPLES_BIN := $(addsuffix .bin,$(EXAMPLES))
EXAMPLES_GENERATED := $(addsuffix .ml,$(EXAMPLES)) $(addsuffix .mli,$(EXAMPLES))

all: Makefile.coq
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs"

Makefile.coq:
	$(MAKE) config

examples: $(EXAMPLES_BIN)

%.bin: %_extract.vo
	sed "s/failwith/fun _ -> failwith/" $*.ml > $*_patched.ml
	ocamlopt $*.mli $*_patched.ml $*_test.ml -o $@
	
config:
	$(COQBIN)/coq_makefile -R . HS -R $(CoRN) CoRN -R $(CoLoR) CoLoR `find ./*.v` > Makefile.coq
	$(COQMAKE) depend

clean:
	rm -f *~ doc/HybSys.*.html doc/index.html $(EXAMPLES_GENERATED)
	$(COQMAKE) clean

tags:
	$(COQBIN)/coqtags `find . -name \*.v`

doc:
	$(COQBIN)/coqdoc --html -g -d doc -R $(CoRN) CoRN -R $(CoLoR) CoLoR `find ./*.v`
	./createIndex

install-doc:
	rm -rf $(WEB)/doc
	mkdir $(WEB)/doc
	cp doc/*.html doc/coqdoc.css $(WEB)/doc

dist:
	./createDist

install-dist:
	mv -f HybSys_`date +%y%m%d`.tar.gz $(WEB)/HybSys.tar.gz

%.vo: %.v
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs" $@

%:
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs" $@
