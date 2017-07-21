all:
	latexmk -pdf main
	cp main.pdf paper.pdf

clean:
	-latexmk -c
	-rm -f main.pdf main.dvi *~ *.bbl *.aux

