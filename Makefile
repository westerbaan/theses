.PHONY: all clean

A.pdf: com.tex common.tex cstar.tex A.tex vn.tex
	latexmk -pdf -use-make A.tex

cstar.pdf: common.tex cstar.tex
	latexmk -pdf -use-make cstar.tex

vn.pdf: common.tex vn.tex
	latexmk -pdf -use-make vn.tex

clean:
	latexmk -CA
