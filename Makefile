.PHONY: all clean

main.pdf: com.tex common.tex cstar.tex main.tex vn.tex
	latexmk -pdf -use-make main.tex

cstar.pdf: common.tex cstar.tex
	latexmk -pdf -use-make cstar.tex

vn.pdf: common.tex vn.tex
	latexmk -pdf -use-make vn.tex

clean:
	latexmk -CA
