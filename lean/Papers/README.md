# Formalisations of the follow-up papers

Selected by the author on 2026-09-26: the post-thesis papers of Bram and Bas
Westerbaan with John van de Wetering, and the reconstruction paper; SIG added because REC depends on it.

A separate effort from the theses tree (`Theses/`), in the same Lake project so
that it can import the theses' foundations (effect algebras and monoids,
order unit spaces, Euclidean Jordan algebras, von Neumann algebras).

| tag | paper | source | directory |
|---|---|---|---|
| `EJA` | A. Westerbaan, B. Westerbaan, J. van de Wetering, *Pure Maps between Euclidean Jordan Algebras*, QPL 2018, arXiv:1805.11496 | `../papers/1805.11496/main.tex` | `Papers/EJA/` |
| `OAP` | —, *A characterisation of ordered abstract probabilities*, LICS 2020, arXiv:1912.10040 | `../papers/1912.10040/first.tex` | `Papers/OAP/` |
| `SEA` | —, *The three types of normal sequential effect algebras*, Quantum 2020, arXiv:2004.12749 | `../papers/2004.12749/second.tex` | `Papers/SEA/` |
| `SIG` | K. Cho, B. Westerbaan, J. van de Wetering, *Dichotomy between deterministic and probabilistic models in countably additive effectus theory*, QPL 2020, arXiv:2003.10245 | `../papers/2003.10245/main.tex` | `Papers/SIG/` |
| `FDS` | T. Fritz, B. Westerbaan, *The universal property of infinite direct sums in C\*- and W\*-categories*, Appl. Categ. Structures 2019, arXiv:1907.04714 | `../papers/1907.04714/direct_sums.tex` | `Papers/FDS/` |
| `REC` | B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of quantum theory*, arXiv:2109.10707 (2021) | `../papers/2109.10707/short.tex` | `Papers/REC/` |

## Status (2026-09-26, end of the first day)

| tag | points | Lean lines | state |
|---|---|---|---|
| `OAP` | 73 / 73 | 7,600 | complete; Yosida's representation theorem (OAP 64) proved rather than cited |
| `SEA` | 73 / 73 | 9,200 | complete; main theorem SEA 64 (every normal SEA is B ⊕ E_c ⊕ E_ac) |
| `EJA` | 54 / 54 | 9,100 | complete up to one named external input (EJA 54: the Hanche-Olsen–Størmer classification); headline EJA 40 unconditional; the fundamental formula and the Albert algebra proved |
| `FDS` | 19 / 19 | 4,500 | complete; the predual definition of W*-categories implies the used one under a common-embedding hypothesis |
| `SIG` | 73 / 73 | 17,700 | complete; SIG 46's B(H) clause uses Kochen–Specker as a named hypothesis |
| `REC` | 136 / 136 | 14,400 | complete; Theorems 102, 103 and 136 under named hypotheses (Alfsen–Shultz, Hanche-Olsen–Størmer, Shultz; the A–S 9.43/9.48 one is REC's own transplant, truth open); REC 104 refuted (sequential effectuses have irreducible scalars); REC 128 only for two-level elements |

No `sorry` anywhere; every headline theorem checked axiom-clean.  Defects found in
the papers are in `../papers/ERRATA.md` (false-as-printed statements are refuted
in Lean with the corrected statement proved beside them); each paper's
`PLAN.md` carries the per-point record and hand-over notes.

## Citing a point

EJA, OAP, SEA, SIG and REC number all theorem-like environments with one global
counter, so "Theorem 12" is the 12th numbered environment; FDS numbers within
sections ("Theorem 5.2", cited as `**FDS 5.2**`).  `../papers/index.py` computes
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

Audit vocabulary: as the theses' (`docs/STATEMENT-AUDIT.md`), with one addition for
the proof column: `tree` — the point is discharged by an existing theorem of the
theses tree, which the row names; whether that proof follows the paper is judged
on the tree's own row.  A proof of ours for a point the paper only cites is `none`.
