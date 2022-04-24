build: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

clean: clean-make clean-compiled clean-coqdoc
	@echo "Clean complete"

clean-make:
	@echo "Cleaning Coq makefiles"
	rm *Makefile.coq*

clean-compiled:
	@echo "Removing compiled files..."
	find . * | grep "\(\.vo\|\.aux\|\.glob\)" | xargs rm -f
	@echo "...Files removed"

clean-coqdoc:
	rm -r CoqDoc

coqdoc: coqdoc-lite coqdoc-verbose

coqdoc-lite:
	mkdir -p CoqDoc/light
	coqdoc --html -g -d "CoqDoc/light" src/*.v --no-index --toc

coqdoc-verbose:
	mkdir -p CoqDoc/verbose
	coqdoc --html -d "CoqDoc/verbose" src/*.v --no-index --toc
