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
