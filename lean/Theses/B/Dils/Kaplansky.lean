/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 4082–4279.

  parsec 1580:  the Kaplansky density theorem for Hilbert C*-modules

Statements only; every proof is `sorry`.  Following the conventions of
`HilbertModules.lean`, ultrastrong/ultranorm approximation is expressed
through the seminorms `unSeminorm ω B` (with `B = mulInner ℬ` for the
ultrastrong uniformity on `ℬ` itself); "there is a net `x_α → x` ultranorm
with `‖x_α‖ ≤ ‖x‖`" is rendered as bounded approximability within every
entourage (finitely many seminorms, `ε > 0`), which yields the canonical
approximating net.
-/
import Theses.B.Dils.HilbertModules

open scoped ComplexOrder CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u v w

namespace Theses.B.Dils

/-! **158I** (dils.tex:4084) and **158Ib** (dils.tex:4129): introduction and
discussion — nothing to formalize. -/

section Kaplansky

variable {ℬ : Type u}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **158Ia** (dils.tex:4121, Kaplansky density theorem), the variant of
thesis A's `kaplansky` (vn.tex 74IV) used here: for an ultrastrongly dense
C*-subalgebra `𝒜` of a von Neumann algebra `ℬ` and every `b ∈ ℬ`, there is
a net in `𝒜`, norm-bounded by `‖b‖`, converging ultrastrongly to `b`. -/
theorem kaplansky_bounded_approx [VonNeumannAlgebra ℬ]
    (A : StarSubalgebra ℂ ℬ) (hA : IsClosed (A : Set ℬ))
    (hdense : UnDense (mulInner ℬ) (A : Set ℬ)) (b : ℬ) :
    ∀ (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (ε : ℝ), 0 < ε →
      ∃ a ∈ A, ‖a‖ ≤ ‖b‖ ∧
        ∀ i, unSeminorm (ωs i) (mulInner ℬ) (a - b) ≤ ε :=
  sorry

variable {X : Type v}
  [NormedAddCommGroup X] [Module ℂ X] [SMul ℬ X] [CStarModule ℬ X]

/-- **158II** (`kaplansky-hilbmod`, dils.tex:4135, Kaplansky density
theorem for Hilbert C*-modules): let `X` be a Hilbert ℬ-module for a von
Neumann algebra `ℬ` with an ultranorm-dense 𝒜-submodule `D ⊆ X`, where
`𝒜 ⊆ ℬ` is a C*-subalgebra with `⟨y,y⟩ ∈ 𝒜` for all `y ∈ D`.  Then every
`x ∈ X` is the ultranorm limit of a net in `D` norm-bounded by `‖x‖`.

**158III** and **158IV** are the elementary part of the proof (with
`h y = y · 2/(1+⟨y,y⟩)` and `g x = x · 1/(1+√(1-⟨x,x⟩))`: `‖h y‖ ≤ 1` and
`h (g x) = x`) — not converted.  **158V**, the ultranorm continuity of `h`,
is the real work; its four convergence estimates are stated separately
below as `kaplansky_hilbmod_A₁`, `kaplansky_hilbmod_A₁'`,
`kaplansky_hilbmod_A₂` and `kaplansky_hilbmod_A₂'`. -/
theorem kaplansky_hilbmod [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (A : StarSubalgebra ℂ ℬ) (hA : IsClosed (A : Set ℬ))
    (D : Set X)
    (hD0 : (0 : X) ∈ D)
    (hDadd : ∀ d ∈ D, ∀ d' ∈ D, d + d' ∈ D)
    (hDsmul : ∀ a ∈ A, ∀ d ∈ D, a • d ∈ D)
    (hDinner : ∀ d ∈ D, inner ℬ d d ∈ A)
    (hdense : UnDense (inner ℬ) D) (x : X) :
    ∀ (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (ε : ℝ), 0 < ε →
      ∃ d ∈ D, ‖d‖ ≤ ‖x‖ ∧
        ∀ i, unSeminorm (ωs i) (inner ℬ) (x - d) ≤ ε :=
  sorry

/-! ### 158V (dils.tex:4189): ultranorm continuity of `h`

For `h y = y · 2/(1+⟨y,y⟩)` and a net `y_α → y` ultranorm, the splitting
`kaplansky-splitting` (dils.tex:4205) reads

  `⟨h y - h y_α, h y - h y_α⟩ = A₁ + A₁' + A₂ + A₂'`,

and each of the four terms is shown to converge ultraweakly to `0`; that
gives `h y_α → h y` ultranorm.  The four estimates are the four theorems
below.  (`A₁`, `A₁'` are dual to each other under swapping `y` and `y_α`,
as are `A₂`, `A₂'`, but the thesis states — and uses — all four.) -/

/-- `inv1p b = (1 + b)⁻¹`, the resolvent occurring throughout **158V**; for
`b ≥ 0` in a C*-algebra `1 + b` is invertible, so `Ring.inverse` is the
genuine inverse there, and `0 ≤ inv1p b ≤ 1` as well as `0 ≤ b * inv1p b ≤ 1`
(dils.tex:4213). -/
private noncomputable def inv1p (b : ℬ) : ℬ := Ring.inverse (1 + b)

variable {ι : Type w} {l : Filter ι}

/-- **158V**.1 (dils.tex:4193, the term `A₁` of `kaplansky-splitting`): if
`y_α → y` ultranorm, then

  `A₁ = ⟨y,y⟩ (1+⟨y,y⟩)⁻² - (1+⟨y_α,y_α⟩)⁻¹ ⟨y,y⟩ (1+⟨y,y⟩)⁻¹ → 0`

ultraweakly.  Proof (dils.tex:4211): rewrite `A₁` as
`(1+⟨y,y⟩)⁻¹ (⟨y_α-y,y_α⟩ + ⟨y,y_α-y⟩) (1+⟨y_α,y_α⟩)⁻¹ ⟨y,y⟩ (1+⟨y,y⟩)⁻¹`
using the resolvent identity, then use ultraweak continuity of
multiplication by constants (`mult-uws-cont`) together with
`⟨y_α-y, y_α (1+⟨y_α,y_α⟩)⁻¹⟩ → 0` and `⟨y, y_α-y⟩ (1+⟨y_α,y_α⟩)⁻¹ → 0`,
both by Cauchy–Schwarz for the `f`-seminorms. -/
private theorem kaplansky_hilbmod_A₁ [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (y : ι → X) (y₀ : X) (hy : UnTendsto (inner ℬ) y l y₀) :
    UWTendsto (fun i =>
        inner ℬ y₀ y₀ * inv1p (inner ℬ y₀ y₀) * inv1p (inner ℬ y₀ y₀)
          - inv1p (inner ℬ (y i) (y i))
              * (inner ℬ y₀ y₀ * inv1p (inner ℬ y₀ y₀))) l 0 :=
  sorry

/-- **158V**.2 (dils.tex:4196, the term `A₁'` of `kaplansky-splitting`): if
`y_α → y` ultranorm, then

  `A₁' = ⟨y_α,y_α⟩ (1+⟨y_α,y_α⟩)⁻² - (1+⟨y,y⟩)⁻¹ ⟨y_α,y_α⟩ (1+⟨y_α,y_α⟩)⁻¹ → 0`

ultraweakly.  This is `A₁` with the roles of `y` and `y_α` interchanged;
"in a similar way one sees `A₁' → 0` ultraweakly" (dils.tex:4272). -/
private theorem kaplansky_hilbmod_A₁' [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (y : ι → X) (y₀ : X) (hy : UnTendsto (inner ℬ) y l y₀) :
    UWTendsto (fun i =>
        inner ℬ (y i) (y i) * inv1p (inner ℬ (y i) (y i))
              * inv1p (inner ℬ (y i) (y i))
          - inv1p (inner ℬ y₀ y₀)
              * (inner ℬ (y i) (y i) * inv1p (inner ℬ (y i) (y i)))) l 0 :=
  sorry

/-- **158V**.3 (dils.tex:4200, the term `A₂` of `kaplansky-splitting`): if
`y_α → y` ultranorm, then

  `A₂ = (1+⟨y,y⟩)⁻¹ ⟨y_α - y, y_α⟩ (1+⟨y_α,y_α⟩)⁻¹ → 0`

ultraweakly; "the proofs for `A₂, A₂' → 0` are very similar"
(dils.tex:4273) — the middle factor is exactly the quantity bounded by
Cauchy–Schwarz in the proof of `A₁`, and the outer resolvents are bounded
by `1`. -/
private theorem kaplansky_hilbmod_A₂ [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (y : ι → X) (y₀ : X) (hy : UnTendsto (inner ℬ) y l y₀) :
    UWTendsto (fun i =>
        inv1p (inner ℬ y₀ y₀) * inner ℬ (y i - y₀) (y i)
          * inv1p (inner ℬ (y i) (y i))) l 0 :=
  sorry

/-- **158V**.4 (dils.tex:4202, the term `A₂'` of `kaplansky-splitting`): if
`y_α → y` ultranorm, then

  `A₂' = (1+⟨y_α,y_α⟩)⁻¹ ⟨y - y_α, y⟩ (1+⟨y,y⟩)⁻¹ → 0`

ultraweakly; as for `A₂` (dils.tex:4273). -/
private theorem kaplansky_hilbmod_A₂' [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (y : ι → X) (y₀ : X) (hy : UnTendsto (inner ℬ) y l y₀) :
    UWTendsto (fun i =>
        inv1p (inner ℬ (y i) (y i)) * inner ℬ (y₀ - y i) y₀
          * inv1p (inner ℬ y₀ y₀)) l 0 :=
  sorry

end Kaplansky

end Theses.B.Dils
