# Lean formalization of the theses

This Lean 4 project contains formalized *statements* of (essentially) every
lemma, proposition, theorem, corollary and exercise of the two theses in this
repository:

* **Thesis A** — Abraham Westerbaan, *The Category of Von Neumann Algebras*
  ([arXiv:1804.02203](https://arxiv.org/abs/1804.02203))
* **Thesis B** — Bas Westerbaan, *Dagger and Dilation in the Category of Von
  Neumann Algebras* ([arXiv:1803.01911](https://arxiv.org/abs/1803.01911))

All proofs are currently `sorry`; the intent is to fill them in one by one.
Definitions, by contrast, are real (no `sorry`), so that later proof work has
solid statements to prove.

## Layout

```
Theses/
  Common.lean            -- shared: Kadison-style von Neumann algebra class,
                         --   np-functionals, nmiu/ncp/ncpsu maps, effects
  A/CStar/               -- thesis A ch. 1 (cstar.tex): C*-algebras
    Basic.lean           --   definition, Hilbert spaces, B(H), basics
    Positive.lean        --   holomorphic fns, spectral radius, sqrt
    Representation.lean  --   Gelfand, states, GNS, Gelfand–Naimark
    Matrices.lean        --   M_N(𝒜), complete positivity, Russo–Dye
    TowardsVN.lean       --   directed suprema, normal functionals
  A/VN/                  -- thesis A ch. 2 (vn.tex): von Neumann algebras
    Basic.lean           --   definition, ultraweak/ultrastrong, examples
    Projections.lean     --   ceiling/floor, support, carrier, centre
    Completeness.lean    --   Kaplansky density, completeness
    Division.lean        --   pseudoinverses, polar decomposition
    NormalFunctionals.lean --  ultraweak boundedness & permanence
  A/Proc/                -- thesis A ch. 3 (proc.tex): structure in W*_cpsu
    Measurement.lean     --   corners, filters, purity, ⋄-positivity
    Tensor.lean          --   tensor product of von Neumann algebras
    QuantumLambda.lean   --   model of the quantum lambda calculus
    Duplicators.lean     --   duplicable vNa's are ℓ∞(X); monoids
  B/Dils/                -- thesis B ch. 2 (dils.tex): dilations
    Stinespring.lean     --   GNS', Stinespring, Kraus
    HilbertModules.lean  --   Hilbert C*-modules, ultranorm uniformity
    SelfDualCompletion.lean -- self-dual completion
    Paschke.lean         --   Paschke dilations, KSGNS
    Kaplansky.lean       --   Kaplansky density for Hilbert C*-modules
    SelfDual.lean        --   more on self-dual modules, exterior ⊗
    Pure.lean            --   pure maps
  B/Eff/                 -- thesis B ch. 3 (eff.tex): effectus theory
    EffectAlgebras.lean  --   PCMs, effect algebras/monoids/modules
    Effectus.lean        --   effectuses, partial/total, Cho's theorem
    WStarCat.lean        --   the category of vNa's with ncpsu-maps
    StatesPredicates.lean --  predicates, states, scalars, M-convex sets
    Quotients.lean       --   quotients, comprehension, images, sharpness
    DiamondAmp.lean      --   ⋄-effectuses, &-effectuses
    Dagger.lean          --   †-effectuses, dilations
    Comparisons.lean     --   †-kernel cats, sequential product, homology
```

(`bintr.tex` contains no mathematical statements; `misc.tex` is not part of
either thesis.)

## Conventions

See [CONVENTIONS.md](CONVENTIONS.md).  In short: every declaration's doc
comment starts with the thesis's point number in bold (e.g. **34V** — parsec
34, point V, the same numbers printed in the margins of the printed theses)
followed by the LaTeX label, source `file:line`, and the point's tag.  So
grepping for `**34V**` finds the formalization of point 34V, and vice versa
the doc comment leads back to the LaTeX source.

Where Mathlib already has a notion (C*-algebras, spectrum, GNS, …) the
thesis's definition points are mapped onto Mathlib's vocabulary in comment
blocks; where it doesn't (normality via directed suprema, the Kadison
definition of von Neumann algebra, corners and filters, Paschke dilations,
effect algebras, effectuses, …) the thesis's definitions are formalized here.

## Building

```
lake exe cache get   # fetch the Mathlib build cache (once)
lake build           # expect a wall of `sorry` warnings — that's the point
```
