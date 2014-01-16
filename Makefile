MODULES := Rules Cache Channel Compatible DataTypes Hier L1 LatestValue MsiState StoreAtomicity Tree Useful Top L1Axioms CompatBehavior LatestValueAxioms ChannelAxiom
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
