%:
	mkdir -p bdir
	bsc -u -sim -bdir bdir -info-dir bdir -simdir bdir -aggressive-conditions $*.bsv
	bsc -u -sim -simdir bdir -e mk$*Inst *.c bdir/*.ba

clean:
	rm -rf bdir a.out a.out.so

.PHONY: clean

.DEFAULT_GOAL :=
