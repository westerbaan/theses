Theses of Abraham and Bas Westerbaan
====================================

<a href="https://arxiv.org/abs/1804.02203"><img src="bram-cover-preview.jpg" width="300px"/></a> <a href="https://arxiv.org/abs/1803.01911"><img src="bas-cover-preview.jpg" width="300px"/></a>

Generating PDFs
---------------
The theses can be typeset by running `make`.  On some platforms the generated PDFs will lack an index due to `xindy` not being available.  Such issues can be avoided by running `make` inside the `texlive` container using: `docker run --rm -v .:/workdir -it texlive/texlive make`.


See also
--------

* [Path tracer for the Cover](https://github.com/westerbaan/ndpt)
* [Homepage of the defences](https://westerbaan.name/promotie)
