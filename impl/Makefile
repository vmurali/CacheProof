%:
	mkdir -p bdir
	bsc -u -sim -bdir bdir -info-dir bdir -simdir bdir $*.bsv
	bsc -u -sim -simdir bdir -e mk$*Inst *.c bdir/*.ba
	mkdir -p build
	mv a.out* *.o build

clean:
	rm -rf bdir a.out a.out.so *.o

.PHONY: clean

.DEFAULT_GOAL :=
