.PHONY: all clean

all: a.pdf b.pdf

a.pdf: com.tex common.tex cstar.tex a.tex vn.tex
	latexmk -pdf -use-make a.tex

b.pdf: common.tex b.tex dils.tex
	latexmk -pdf -use-make b.tex

cstar.pdf: common.tex cstar.tex
	latexmk -pdf -use-make cstar.tex

vn.pdf: common.tex vn.tex
	latexmk -pdf -use-make vn.tex

common.tex: main.bib

clean:
	latexmk -CA
