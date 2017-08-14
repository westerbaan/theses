.PHONY: all clean

all: a.pdf b.pdf

a.pdf: com.tex common.tex cstar.tex a.tex vn.tex proc.tex
	latexmk -pdf -use-make a.tex

b.pdf: common.tex b.tex dils.tex eff.tex
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
