.PHONY: all clean

all:
	mkdir -p build
	pdflatex -output-directory build Main.tex
	bibtex build/Main
	pdflatex -output-directory build Main.tex
	pdflatex -output-directory build Main.tex

clean:
	rm -rf build
