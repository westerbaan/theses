.PHONY: all clean

all: A.pdf B.pdf

A.pdf: com.tex common.tex cstar.tex A.tex vn.tex
	latexmk -pdf -use-make A.tex

B.pdf: common.tex B.tex dils.tex
	latexmk -pdf -use-make B.tex

cstar.pdf: common.tex cstar.tex
	latexmk -pdf -use-make cstar.tex

vn.pdf: common.tex vn.tex
	latexmk -pdf -use-make vn.tex

common.tex: main.bib

clean:
	latexmk -CA
