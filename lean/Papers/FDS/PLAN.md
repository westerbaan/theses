# FDS — plan

T. Fritz, B. Westerbaan, *The universal property of infinite direct sums in
C\*-categories and W\*-categories*, ACS 2019 (arXiv:1907.04714),
`../papers/1907.04714/direct_sums.tex`; 19 points (`../papers/FDS-points.csv`),
numbered within sections, cited `**FDS n.m**`.  Everything goes in
`Papers/FDS/DirectSums.lean` (one file: a second new file could not import the
first this session).

## Global design

* **Categories.**  Mathlib `Category C` + `Preadditive C` + `Linear ℂ C` is
  exactly "enriched over complex vector spaces with bilinear composition"
  (Def 2.1(1)).  On top, three classes, mixin style:
  `StarCategory C` (data: the involution `f†`; Def 2.1(2),(3)),
  `NormedStarCategory C` (data: a norm on each hom-set; Def 2.2(1)), and the
  Prop-mixins `CStarCategory C` (completeness + C\*-identity, Def 2.2(2)) and
  `WStarCategory C` (Def 2.2(3)).  Normed-group / normed-space instances on
  `X ⟶ Y` are *derived* from the norm field (`NormedAddCommGroup.ofCore`), so
  the additive group is Mathlib's `Preadditive` one definitionally.
* **Endomorphism C\*-algebras.**  `End A` gets a `CStarAlgebra` instance
  (ring = Mathlib's `End.ring`, algebra = `Linear`'s), with the spectral order
  (`CStarAlgebra.spectralOrder`) as its order.  `f ≫ g` is the paper's `g f`.
* **Hilbert modules, mirrored.**  The paper uses `C(B,A)` as a *right*
  `C(B,B)`-module with `⟨g,f⟩ = g*f`; the theses tree (and Mathlib's
  `CStarModule`) use *left* modules with `⟪x,y⟫ = y x*`.  We use: `A ⟶ B` is a
  left `End B`-module (`b • f = f ≫ b`, Mathlib's `End.mulActionRight`) with
  `⟪f,g⟫ = f† ≫ g` (= `g f*`).  The paper's constructions are transported
  by `*` (e.g. the paper builds `f* = ∑ κⱼ fⱼ*` in `C(B,A)`, we build
  `f = ∑ fⱼ κⱼ*` in `C(A,B)`); recorded per row.
* **W\*-category** (Def 2.2(3)).  The print's definition is "every hom-set has
  a Banach predual"; its "Equivalently [GLR, Prop. 2.15]" clause (every
  `C(A,A)` is a W\*-algebra and every `C(A,B)` is a self-dual Hilbert
  `C(A,A)`-module) is the one the proofs use, and it is what `WStarCategory`
  asserts (W\*-algebra = the theses' Kadison `VonNeumannAlgebra`; self-dual =
  `Theses.B.Dils.SelfDual`, mirrored as above: `C(A,B)` self-dual over
  `End B`, for all `A, B` — equivalent to the print's by `*`).  The predual
  form is defined (`HomsHavePreduals`) for reference; the GLR equivalence is
  cited by the print, not proved there, and not proved here.
* **Sums `∑ fᵢ fᵢ* < ∞`** in a C\*-category: the print's reading "a fixed
  element upper bounds all finite partial sums" (`SqSummable`); the norm is
  `(sup_S ‖∑_{i∈S} fᵢfᵢ*‖)^{1/2}`.  The print's alternative reading
  (ultraweak convergence in the bidual `C(B,B)**`) is not formalised (no
  enveloping W\*-algebra available).  In a W\*-category `∑ κⱼκⱼ* = 1` (5.1(c))
  is read as `IsLUB` of the partial sums (the print's footnote: for positive
  families ultraweak sum = supremum).
* **Ban-valued functors** (3.4): `BanFunctor C`: object map to complex Banach
  spaces, morphism map to bounded operators, functorial, linear and
  contractive in the morphism (enrichment in `Ban`).  Representability: an
  object `A` with isometric linear equivalences `C(A,X) ≃ₗᵢ F X` natural in
  `X`.

## Points

| pt | kind | content | Lean | deps | cost |
|---|---|---|---|---|---|
| 1.1 | Thm (cited, Borceux) | additive cat.: coproduct-representing ⇔ product-representing ⇔ biproduct equations | `directsum_equiv_trad` as `TFAE` of three `∃`s, (a),(b) as natural additive bijections `C(A,-) ≃+ C(A₁,-)×C(A₂,-)` | Preadditive | S |
| 2.1 | Defn | complex \*-category | `StarCategory` | — | S |
| 2.2 | Defn | normed \*-cat, C\*-cat, W\*-cat; projections, isometries, unitaries | `NormedStarCategory`, `CStarCategory`, `WStarCategory`, `HomsHavePreduals`, `IsIsometry`, `IsUnitary`; `CStarAlgebra (End A)` | 2.1 | M (instances) |
| 2.3 | Ex | `Hilb` is a W\*-category | `Hilb` category; C\* by Mathlib; W\* via the linking-algebra lemma below | 2.2, theses `VonNeumannAlgebra (H →L H)`, `cornerLeft_selfDual` | L |
| 2.4 | Ex | `Rep A` (non-degenerate reps, intertwiners) is a W\*-category; `Rep ℂ ≅ Hilb` | `Rep A` (unital reps of a unital C\*-algebra = non-degenerate); W\* via commutants + linking lemma | 2.3 infra | L |
| 2.5 | Ex | `NRep N` W\*-category; `NRep(A**) ≅ Rep A` | `NRep N`; the `A**` clause not converted (no enveloping W\*-algebra) | 2.4 | M |
| 3.1 | Lem | `a*ta ≤ 1-s ⇔ asa* ≤ 1-t ⇔ tas = 0 ⇔ sa*t = 0` (‖a‖ ≤ 1, projections) | `contrapositionlemma` TFAE | 2.2 | M |
| 3.2 | Lem | `‖a‖,‖b‖ ≤ 1`, `ab = 1` ⇒ `b` isometry, `a = b*` | `isometrylemma` | 3.1 | S |
| 3.3 | Cor | invertible contraction with contractive inverse is unitary | `unitaries` | 3.2 | S |
| 3.4 | Defn | representable Ban-functor | `BanFunctor`, `BanFunctor.IsRepresentedBy` | 2.2 | S |
| 3.5 | Cor | representing object unique up to unique unitary | `unique_up_to_unitary` | 3.3, Yoneda by hand | S |
| 4.1 | Lem | `⊕ᵢ C(Aᵢ,B)` complete | `DSum`, its normed space, `lem_complete` (paper's Cauchy-sequence proof) | 2.2 | M |
| 4.2 | Defn | `I`-indexed direct sum = representing object of `⊕ᵢ C(Aᵢ,-)` | `dsumFunctor`, `IsDirectSum` | 3.4, 4.1 | S |
| 4.3 | Rem | dagger limits (finite `I`); infinite direct sums are not limits | informal comparison with [daglims]; not converted (reason in audit) | — | — |
| 4.4 | Rem | "we believe" no weight gives `⊕ C(Aᵢ,-)` | opinion; not converted | — | — |
| 4.5 | Rem | direct sums with a PSD kernel `K`; completeness "works in the same way" | `KSum`, `kernel_complete` for a constant family and `K` PSD with `Kⱼⱼ ≠ 0`; **flag** (ERRATA): `fᵢfⱼ*` is ill-typed unless `Aᵢ = Aⱼ`, and for PSD `K` with a zero diagonal entry (e.g. `K = 0`) the "norm" is only a seminorm | 4.1 | M |
| 5.1 | Thm | W\*-cat: (a) direct sum ⇔ (b) universal family with norm ⇔ (c) GLR: `κᵢ*κⱼ = δᵢⱼ`, `∑κⱼκⱼ* = 1` | `directsum_equiv` (TFAE) + the three implications separately, (a)⇔(b) in any C\*-category | 3.2, 4.2, theses ultranorm (`bddUnComplete_of_selfDual`, `innerprod_ultraweak`, `blinear_bounded_is_ultranorm`, `vna_supremum_uslimit`) | L |
| 5.2 | Cor | normal \*-functors preserve direct sums | `NormalStarFunctor`-hypotheses on `F : C ⥤ D`; via 5.1(c) | 5.1 | S |
| 5.3 | Prop | in `NRep N` the ℓ²-sum is a direct sum, and every direct sum is one (up to unitary) | `lp`-sum of reps; via 5.1(c)⇒(a) and 3.5 | 2.5, 5.1 | L |

## Supporting lemma for the examples (not a point)

*Linking lemma*: in a C\*-category, if `A` and `B` embed isometrically into
an object `S` with `End S` a von Neumann algebra, then `End A` is a von
Neumann algebra (corner `pLp`, theses `cornerSet_vonNeumannAlgebra`) and
`C(A,B)` is self-dual over `End B` (corner `qL`, theses
`cornerLeft_selfDual`, cut down by `p`).  Hilb, Rep, NRep: `S = A ⊕ B`,
`End S` = a commutant, a von Neumann subalgebra of `B(H)`.

## Flags

* **4.5** ill-typed for non-constant families (`fᵢ fⱼ*` needs `Aᵢ = Aⱼ`) and
  false as printed for PSD kernels with a zero diagonal entry (only a
  seminorm); formalised for `Aᵢ = A` under `Kⱼⱼ ≠ 0` (ERRATA FDS 4.5).  Also
  under-specified: which finite partial sums (we take squares `S × S`).
* **2.2(3)** under-specified reading of "self dual as a Hilbert
  `C(A,A)`-module": `C(A,B)` with `⟨a,b⟩ = a*b` is a *right* `C(A,A)`-module;
  fine.
* **Parenthetical after (4.1)**: the `B`-valued inner product `∑ fᵢgᵢ*` need
  not converge in a C\*-category (only in the bidual); not formalised.
* **2.5** `NRep(A**) ≅ Rep(A)` not converted.

## Outcome (2026-09-26)

All in `Papers/FDS/DirectSums.lean`, no `sorry`.  17 of 19 points formalised
(4.3 and 4.4 are informal remarks, not converted).  Partial: 2.4 covers
unital C\*-algebras only; 2.5 omits `NRep(A**) ≅ Rep A`; 4.5 as corrected.
The W\*-structure of the examples goes through the linking lemma
(`WStarCategory.of_linking`), not in the print.
