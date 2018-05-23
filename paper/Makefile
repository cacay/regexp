LATEXMK = latexmk -pdf

all: report.pdf

report.pdf: report.tex bibliography.bib bibliography-extra.bib *.sty macro/*.sty
	$(LATEXMK) report

bibliography.bib: bibliography.bibdb
	bibdb bibliography.bibdb

clean:
	$(LATEXMK) -C report
	rm bibliography.bib

.PHONY: all clean
