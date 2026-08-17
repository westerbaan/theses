#!/bin/sh
# Run xindy in a container, passing all arguments on to it.
#
# .latexmkrc calls this where xindy is missing from the PATH, which it is on
# platforms for which TeX Live ships none (it needs clisp).  makeindex is not
# an alternative --- the index locators are parsec numbers such as 10.50 and
# the hyperlinks are an xindy crossref class, see parsec.xdy.
#
# Needs a docker command and the image built by `make xindy-image`.
exec docker run --rm -v "$(pwd)":/work -w /work theses-xindy xindy "$@"
