# Conventions for the Lean formalization of the theses

This directory contains a Lean 4 + Mathlib formalization of the *statements* of
the two theses in this repository:

* **Thesis A** — Abraham Westerbaan, *The Category of Von Neumann Algebras*
  (arXiv:1804.02203): chapters `cstar.tex`, `vn.tex`, `proc.tex`.
* **Thesis B** — Bas Westerbaan, *Dagger and Dilation in the Category of Von
  Neumann Algebras* (arXiv:1803.01911): chapters `bintr.tex`, `dils.tex`,
  `eff.tex`.

At this stage every lemma/proposition/theorem/corollary/exercise is stated
with a `sorry` proof; proofs are to be filled in later.

## Source referencing

The theses number their material by *parsec* and *point*: a point
`\begin{point}{50}` in `\begin{parsec}{340}` is displayed as **34V**
(parsec 34 = 340/10, point V = roman(50/10)).  Every Lean declaration carries a
doc comment of the form:

```lean
/-- **34V** (`operator-norm-complete`, cstar.tex:359, Lemma):
original statement, lightly paraphrased. -/
```

i.e. display number, LaTeX label (if any), source file:line, and the point's
tag.  Declarations are named after the LaTeX label when there is one
(`operator-norm-complete` → `operatorNorm_complete` / thematic Lean name),
otherwise a descriptive name is invented.

### Finding an exercise's published solution

The two solution files are keyed **differently**, and a wrong guess fails
*silently* — it returns no matches, which is indistinguishable from "this
exercise has no solution".  That mistake suppressed the author's proofs for a
whole batch of A/CStar statements in session 2.

* **`../bsols.tex`** (thesis B, 79 solutions) — keyed by the **LaTeX label** the
  doc comment carries: `grep -n 'solution}{exc-subbase}' ../bsols.tex`.
* **`../asols.tex`** (thesis A, 64 solutions) — keyed by **parsec and point**:
  `solution}{parsec-<parsec×10>.<point×10>}`.  So DISP `4IV` is
  `parsec-40.40`, `9X` is `parsec-90.100`, `11XV` is `parsec-110.150`.

The inverse rule — key `parsec-<P>.<Q>` → DISP `(P/10)·roman(Q/10)` — was
checked mechanically against all 792 DISP + `file:line` doc comments in the Lean
tree, with **zero genuine violations**.  Two extensions cover the exceptions:

* point not a multiple of 10 → letter suffix on the *numeral*:
  `90.41` → **9IVa**, `160.61` → **16VIa**;
* parsec not a multiple of 10 → letter suffix on the *parsec*:
  `201` → **20a**, `341` → **34a**, `842` → **84b**.

Two further facts worth knowing.  First, `asols.tex` **covers parsecs 40–340
only** — the last solution is `parsec-340.60`.  Every one is for a `cstar.tex`
exercise; there are none for `vn.tex` or `proc.tex`, and none for the
`cstar.tex` parsecs **350–390** either.  So for 35VI, 36III, 37IX, 38III, 38VI,
39VI and their neighbours there is genuinely no published solution, and a Lean
proof there is original work rather than a transcription — worth saying so in
the log.

**This is confirmed by the author, not merely inferred from a failed search:**
the solutions to the von Neumann exercises were never written.  `vn.tex` does
have **75 inline `{Proof}` points** covering its Lemmas, Propositions, Theorems
and Corollaries — those are author arguments and should be transcribed as usual
— but its **62 Exercises have no author argument at all**.

That has a consequence worth stating plainly.  Every `cstar.tex` exercise came
with a written solution, so someone had already checked the statement was
provable.  The `vn.tex` exercises have never had that check, and a Lean proof of
one is the first proof of it that has ever existed.  **Statement bugs are
therefore much likelier there**, and finding that such an exercise is false as
stated is a *more* valuable result than proving it.  Test against the failure
modes this project has already hit: falsity in the trivial algebra `{0}`
(Mathlib's `CStarAlgebra` does not extend `Nontrivial` — see 16V, 16VI, 22III.5);
degeneracy at `N = 0` or an empty index (Lean's `2/(0:ℝ) = 0` made 34aVII false);
and hypotheses the author uses but never states (26II.1, 37IX).  Second, **there is no `aerr.tex`**: thesis A's 27 errata and addenda
live at the *top of* `asols.tex`, keyed the same way, and should be consulted
before filing a new erratum.  (Thesis B does have `../berr.tex`.)

## File layout

```
Theses/
  A/CStar/…      -- cstar.tex, one file per (sub)section
  A/VN/…         -- vn.tex
  A/Proc/…       -- proc.tex
  B/Dils/…       -- dils.tex
  B/Eff/…        -- eff.tex
```

Namespaces follow the directory structure: `Theses.A.CStar`, etc.  Where a
definition from an earlier chapter is needed later it is imported (thesis B
freely imports from thesis A's files, matching the cross-references in the
text).

## Mapping to Mathlib

* Prefer Mathlib's existing notions over redefining them.  In particular:
  * C*-algebra (thesis: unital) → `CStarAlgebra A` (which is unital);
    commutative → `CommCStarAlgebra A`.
  * Hilbert space → `[NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]`; bounded operators → `H →L[ℂ] H`; adjoints →
    `ContinuousLinearMap.adjoint`.
  * Spectrum → `spectrum ℂ a`; positivity → the `PartialOrder` /
    `StarOrderedRing` order on a C*-algebra (`0 ≤ a`); square root and
    functional calculus → CFC (`cfc`, `CFC.sqrtₙ`/`CFC.sqrt`).
  * States, characters → `WeakDual.CharacterSpace`, positive linear
    functionals; Gelfand representation → `gelfandStarTransform`.
* When a thesis definition *does not* exist in Mathlib (e.g. Kadison-style
  abstract von Neumann algebras, np-maps, ultraweak/ultrastrong topology on an
  abstract von Neumann algebra, corners, filters, Paschke dilations, effect
  algebras, effectuses, &-effectuses, ⋄-effectuses, †-effectuses), formalize
  the thesis's definition faithfully as a new `class`/`structure`/`def`.
* A *definition* point is formalized by an actual definition (no `sorry`), or
  by a note that it coincides with an existing Mathlib notion.  A point that
  both defines something and claims its well-definedness gets a definition
  plus `sorry`-ed lemmas for the claims.
* Points tagged **Exercise**/**Exercise\*** are statements too — convert them
  exactly like lemmas.
* Multi-part statements (enumerate) become one declaration per part, suffixed
  `_1`, `_2`, … or with descriptive suffixes.
* Points that are proof-steps of a preceding theorem (tags like “1 ⇒ 2”,
  “Induction step”, “Ad 3”) are *not* converted separately; they belong to the
  proof, which is out of scope for now.

## Key global choices

* Everything lives in the root namespace `Theses` (with subnamespaces per
  chapter), so short names never clash with Mathlib.
* Following Mathlib's own style for C*-algebra order theory, statements about
  positivity in a C*-algebra `A` assume
  `[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]`, referring to the
  canonical (spectral/Loewner) order.  (Mathlib does not register a global
  order instance on an abstract C*-algebra; concrete types like `ℂ` and
  `H →L[ℂ] H` have it.)
* Thesis A defines a **von Neumann algebra** abstractly (Kadison, vn.tex 42I):
  a C*-algebra with (1) suprema of bounded directed sets of self-adjoint
  elements and (2) faithful normal positive functionals.  This is formalized
  as a class `Theses.VonNeumannAlgebra` (a `Prop`-valued mixin over
  `[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]`).  Note Mathlib's
  `WStarAlgebra` (Sakai: exists predual) and concrete `VonNeumannAlgebra H`
  (double commutant) are *different* definitions; the thesis's results relating
  these definitions are stated against the thesis's own.
* The morphisms: `miu` = unital ∗-homomorphism (`StarAlgHom` restricted
  appropriately), `nmiu` = normal unital ∗-homomorphism, `cp`/`ncp` =
  (normal) completely positive, `pu`/`npu`, `cpsu`/`ncpsu` = (normal) cp
  subunital, following the thesis's naming.  The categories `CStar_miu`,
  `W*_nmiu`, `W*_ncpsu`, … are defined with Mathlib's category theory library
  when a chapter needs them.
* Scalars are `ℂ` throughout, as in the theses.
