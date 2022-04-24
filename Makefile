build: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

clean: clean-make clean-compiled
	@echo "Cleaned complete"

clean-make:
	@echo "Cleaning Coq makefiles"
	rm *Makefile.coq*

clean-compiled:
	@echo "Removing compiled files..."
	find . * | grep "\(\.vo\|\.aux\|\.glob\)" | xargs rm -f
	@echo "...Files removed"
