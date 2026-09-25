# Formalisations of the follow-up papers

Selected by the author on 2026-09-26: the post-thesis papers of Bram and Bas
Westerbaan with John van de Wetering, and the reconstruction paper.

A separate effort from the theses tree (`Theses/`), in the same Lake project so
that it can import the theses' foundations (effect algebras and monoids,
order unit spaces, Euclidean Jordan algebras, von Neumann algebras).

| tag | paper | source | directory |
|---|---|---|---|
| `EJA` | A. Westerbaan, B. Westerbaan, J. van de Wetering, *Pure Maps between Euclidean Jordan Algebras*, QPL 2018, arXiv:1805.11496 | `../papers/1805.11496/main.tex` | `Papers/EJA/` |
| `OAP` | —, *A characterisation of ordered abstract probabilities*, LICS 2020, arXiv:1912.10040 | `../papers/1912.10040/first.tex` | `Papers/OAP/` |
| `SEA` | —, *The three types of normal sequential effect algebras*, Quantum 2020, arXiv:2004.12749 | `../papers/2004.12749/second.tex` | `Papers/SEA/` |
| `REC` | B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of quantum theory*, arXiv:2109.10707 (2021) | `../papers/2109.10707/short.tex` | `Papers/REC/` |

## Citing a point

Each paper numbers all theorem-like environments with one global counter, so
"Theorem 12" is the 12th numbered environment.  `../papers/index.py` computes
the numbering; `../papers/<TAG>-points.csv` lists every point with its kind,
label and `file:line`.  A declaration's doc comment opens with the tag and
number in bold, then the label and line, then the kind:

    /-- **OAP 23** (`prop:foo`, first.tex:1234, Proposition): … -/

Grepping for `**OAP 23**` finds the formalisation of that point.

## Rules

The rules of the theses tree apply unchanged (`../README.md`, `../CONVENTIONS.md`):
compile only through `scripts/lean1.sh`; never add a `sorry` without a row in
`docs/papers-why-open.csv` saying why; statements follow the print, and any
deviation is recorded in the point's audit row (`docs/audit/papers-<tag>.csv`,
same schema as the theses' audit) and, where the print is wrong, in
`../papers/ERRATA.md`; proofs follow the paper's own argument where it prints
one.  Reuse the theses' definitions (`Theses.B.Eff.EffectAlgebra`,
`EffectMonoid`, `OrderUnitSpace`, `JordanAlgebras`) rather than redefining;
where a paper's definition differs from the theses', record it.
