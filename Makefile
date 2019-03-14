.PHONY: all clean

all: a.pdf b.pdf supp.pdf

supp.pdf: common.tex supp.tex
	latexmk -pdf -use-make supp.tex

a.pdf: common.tex cstar.tex a.tex vn.tex proc.tex main.bib
	latexmk -pdf -use-make a.tex

b.pdf: common.tex b.tex dils.tex eff.tex bintr.tex main.bib
	latexmk -pdf -use-make b.tex

apropos.pdf: common.tex apropos.tex
	latexmk -pdf -use-make apropos.tex

cstar.pdf: common.tex cstar.tex
	latexmk -pdf -use-make cstar.tex

vn.pdf: common.tex vn.tex
	latexmk -pdf -use-make vn.tex

proc.pdf: common.tex proc.tex
	latexmk -pdf -use-make proc.tex

misc.pdf: common.tex misc.tex
	latexmk -pdf -use-make misc.tex

common.tex: main.bib

clean:
	latexmk -CA
	-rm *.{bbl,parsectoc,log}
