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

universe u v

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

**158III**–**158V** are the proof — not converted. -/
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

end Kaplansky

end Theses.B.Dils
