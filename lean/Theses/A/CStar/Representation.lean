/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 1: C*-algebras — cstar.tex, lines 3887–4958.

  §Representation
    … by Continuous Functions   (parsec 270: Riesz ideals, multiplicative
                                 states, Stone–Weierstraß, Gelfand's
                                 representation theorem; parsec 280: the
                                 continuous functional calculus, monotonicity
                                 of the square root; parsec 290: the duality
                                 with compact Hausdorff spaces)
    … by Bounded Operators      (parsec 300: states, the GNS construction,
                                 the Gelfand–Naimark theorem)

Statements only; every proof is `sorry`.  See CONVENTIONS.md for the
numbering (**27XV** = parsec 270, point 150) and naming conventions.
-/
import Theses.A.CStar.Positive

open scoped ComplexOrder ComplexInnerProductSpace ComplexStarModule
open Filter Topology WeakDual

universe u v

namespace Theses.A.CStar

/-! ## Parsec 270: Gelfand's representation theorem

**27I** (cstar.tex:3890): introduction — nothing to formalize.
**27II** (cstar.tex:3899, Setting): `𝒜` is a commutative C*-algebra.

**27III** (`gelfand-representation`, cstar.tex:3902, Definition): the
*spectrum* `spec(𝒜)` of `𝒜` is the set of miu-maps `f : 𝒜 → ℂ` with the
topology of pointwise convergence — in Mathlib `WeakDual.characterSpace ℂ 𝒜`
(its elements are the non-zero continuous algebra homomorphisms, which for a
C*-algebra are exactly the miu-maps, automatically continuous by
`norm_mi_map_contractive`); the *Gelfand representation*
`γ : 𝒜 → C(spec 𝒜)`, `γ(a)(f) = f(a)`, is Mathlib's
`gelfandTransform ℂ 𝒜` (star-preserving version: `gelfandStarTransform`).

**27V** (cstar.tex:3922, Remark): the relation between `spec(𝒜)` and
`spec(a)` appears at **27XVII**; nothing to formalize.
**27VI** (cstar.tex:3932): program — nothing to formalize. -/

section GelfandRepresentation

variable {𝒜 : Type*} [CommCStarAlgebra 𝒜]

/-- **27IV** (`gelfand-representation-basic`, cstar.tex:3916, Exercise),
part 1: the evaluation map `f ↦ f(a)` on `spec(𝒜)` is continuous for every
`a ∈ 𝒜`. -/
theorem gelfand_representation_basic_1 (a : 𝒜) :
    Continuous fun φ : characterSpace ℂ 𝒜 => φ a :=
  sorry

/-- **27IV** (`gelfand-representation-basic`, cstar.tex:3916, Exercise),
part 2: the Gelfand representation is an miu-map; multiplicativity and
unitality are part of the bundled `gelfandTransform`, so involution
preservation remains. -/
theorem gelfand_representation_basic_2 (a : 𝒜) :
    gelfandTransform ℂ 𝒜 (star a) = star (gelfandTransform ℂ 𝒜 a) :=
  sorry

section Order

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **27VII** (cstar.tex:3949, Definition): a *Riesz ideal* of `𝒜` is an
order ideal `I` with `|a| ∈ I` for every self-adjoint `a ∈ I`. -/
def IsRieszIdeal (I : Submodule ℂ 𝒜) : Prop :=
  IsOrderIdeal I ∧ ∀ a ∈ I, IsSelfAdjoint a → CFC.abs a ∈ I

/-- **27VII** (cstar.tex:3949, Definition): a *maximal Riesz ideal* is a
proper Riesz ideal maximal among the proper Riesz ideals. -/
def IsMaximalRieszIdeal (I : Submodule ℂ 𝒜) : Prop :=
  (IsRieszIdeal I ∧ (1 : 𝒜) ∉ I) ∧
    ∀ J : Submodule ℂ 𝒜, IsRieszIdeal J → (1 : 𝒜) ∉ J → I ≤ J → J = I

/-- **27VIII** (`riesz-ideal-ring-ideal`, cstar.tex:3960, Lemma): a Riesz
ideal `I` of `𝒜` is a ring ideal: `a x ∈ I` for `a ∈ 𝒜`, `x ∈ I`. -/
theorem riesz_ideal_ring_ideal (I : Submodule ℂ 𝒜) (hI : IsRieszIdeal I)
    (a : 𝒜) (x : 𝒜) (hx : x ∈ I) : a * x ∈ I :=
  sorry

/-- **27X** (`riesz-ideal-basic`, cstar.tex:3980, Exercise), part 1: the
least Riesz ideal containing a self-adjoint `a` is
`(a)ₘ = { b : |Re b|, |Im b| ≤ n|a| for some n ∈ ℕ }`. -/
theorem riesz_ideal_basic_1 (a : 𝒜) (ha : IsSelfAdjoint a) :
    ∃ I : Submodule ℂ 𝒜, IsRieszIdeal I ∧ a ∈ I ∧
      (∀ J : Submodule ℂ 𝒜, IsRieszIdeal J → a ∈ J → I ≤ J) ∧
      ∀ b : 𝒜, b ∈ I ↔ ∃ n : ℕ,
        CFC.abs ((ℜ b : 𝒜)) ≤ (n : ℝ) • CFC.abs a ∧
        CFC.abs ((ℑ b : 𝒜)) ≤ (n : ℝ) • CFC.abs a :=
  sorry

/-- **27X** (`riesz-ideal-basic`, cstar.tex:3980, Exercise), part 1b: the
least Riesz ideal containing a self-adjoint `a` is all of `𝒜` iff `a` is
invertible. -/
theorem riesz_ideal_basic_1b (a : 𝒜) (ha : IsSelfAdjoint a)
    (I : Submodule ℂ 𝒜) (hI : IsRieszIdeal I) (haI : a ∈ I)
    (hleast : ∀ J : Submodule ℂ 𝒜, IsRieszIdeal J → a ∈ J → I ≤ J) :
    I = ⊤ ↔ IsUnit a :=
  sorry

/-- **27X** (`riesz-ideal-basic`, cstar.tex:3980, Exercise), part 1c: for
positive `a` the least Riesz ideal `(a)ₘ` coincides with the least order
ideal `(a)` (of **22III**).  (For non-positive `a` they may differ; that
claim is not converted.) -/
theorem riesz_ideal_basic_1c (a : 𝒜) (ha : 0 ≤ a) (I J : Submodule ℂ 𝒜)
    (hI : IsRieszIdeal I) (haI : a ∈ I)
    (hIleast : ∀ K : Submodule ℂ 𝒜, IsRieszIdeal K → a ∈ K → I ≤ K)
    (hJ : IsOrderIdeal J) (haJ : a ∈ J)
    (hJleast : ∀ K : Submodule ℂ 𝒜, IsOrderIdeal K → a ∈ K → J ≤ K) :
    I = J :=
  sorry

/-- **27X** (`riesz-ideal-basic`, cstar.tex:3980, Exercise), part 2: the sum
`I + J` of two Riesz ideals is a Riesz ideal.  (That `I + J` might not be an
order ideal for order ideals `I`, `J` is not converted.) -/
theorem riesz_ideal_basic_2 (I J : Submodule ℂ 𝒜) (hI : IsRieszIdeal I)
    (hJ : IsRieszIdeal J) : IsRieszIdeal (I ⊔ J) :=
  sorry

/-- **27X** (`riesz-ideal-basic`, cstar.tex:3980, Exercise), part 3: each
proper Riesz ideal is contained in a maximal Riesz ideal. -/
theorem riesz_ideal_basic_3 (I : Submodule ℂ 𝒜) (hI : IsRieszIdeal I)
    (h1 : (1 : 𝒜) ∉ I) :
    ∃ J : Submodule ℂ 𝒜, IsMaximalRieszIdeal J ∧ I ≤ J :=
  sorry

/-- **27XI** (`maximal-riesz-ideal-maximal-order-ideal`, cstar.tex:4007,
Lemma): a maximal Riesz ideal of `𝒜` is a maximal order ideal. -/
theorem maximal_riesz_ideal_maximal_order_ideal (I : Submodule ℂ 𝒜)
    (hI : IsMaximalRieszIdeal I) : IsMaximalOrderIdeal I :=
  sorry

/-- **27XIII** (`riesz-ideal-miu-map`, cstar.tex:4034, Lemma): for every
maximal Riesz ideal `I` of `𝒜` there is an miu-map `f : 𝒜 → ℂ` with
`ker(f) = I`. -/
theorem riesz_ideal_miu_map (I : Submodule ℂ 𝒜) (hI : IsMaximalRieszIdeal I) :
    ∃ f : 𝒜 →⋆ₐ[ℂ] ℂ, ∀ a : 𝒜, f a = 0 ↔ a ∈ I :=
  sorry

/-- **27XV** (`inv-mult-state`, cstar.tex:4055, Proposition): a self-adjoint
element `a` of the commutative C*-algebra `𝒜` is not invertible iff
`f(a) = 0` for some `f ∈ spec(𝒜)`. -/
theorem inv_mult_state (a : 𝒜) (ha : IsSelfAdjoint a) :
    ¬IsUnit a ↔ ∃ φ : characterSpace ℂ 𝒜, φ a = 0 :=
  sorry

end Order

/-- **27XVII** (`spectrum-miu`, cstar.tex:4078, Exercise):
`spec(a) = { f(a) : f ∈ spec(𝒜) }` for self-adjoint `a ∈ 𝒜`.  (Mathlib
proves this for arbitrary `a`: `WeakDual.CharacterSpace.mem_spectrum_iff_exists`.) -/
theorem spectrum_miu (a : 𝒜) (ha : IsSelfAdjoint a) :
    spectrum ℂ a = Set.range fun φ : characterSpace ℂ 𝒜 => φ a :=
  sorry

/-- **27XVIII** (`gelfand-representation-isometry`, cstar.tex:4082,
Exercise), part 1: the Gelfand representation is an isometry,
`‖γ(a)‖ = ‖a‖`. -/
theorem gelfand_representation_isometry (a : 𝒜) :
    ‖gelfandTransform ℂ 𝒜 a‖ = ‖a‖ :=
  sorry

/-- **27XVIII** (`gelfand-representation-isometry`, cstar.tex:4082,
Exercise), part 2: consequently `γ` is injective (and its range is a
C*-subalgebra of `C(spec 𝒜)`, cf. **29IX**). -/
theorem gelfand_representation_injective :
    Function.Injective (gelfandTransform ℂ 𝒜) :=
  sorry

/-- **27XX** (`stone-weierstrass`, cstar.tex:4103, Theorem
(Stone–Weierstraß)): a C*-subalgebra `𝒮` of `C(X)`, `X` compact Hausdorff,
which separates the points of `X` is all of `C(X)`.  (Mathlib:
`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`.) -/
theorem stone_weierstrass {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (S : StarSubalgebra ℂ C(X, ℂ)) (hS : IsClosed (S : Set C(X, ℂ)))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ S, f x ≠ f y) :
    S = ⊤ :=
  sorry

/-- **27XXV** (`spectrum-calg-compact-hausdorff`, cstar.tex:4186, Lemma): the
spectrum `spec(𝒜)` of a commutative C*-algebra is a compact Hausdorff space.
(Mathlib instances on `characterSpace ℂ 𝒜`.) -/
theorem spectrum_calg_compact_hausdorff :
    CompactSpace (characterSpace ℂ 𝒜) ∧ T2Space (characterSpace ℂ 𝒜) :=
  sorry

/-- **27XXVII** (`gelfand`, cstar.tex:4221, Gelfand's Representation
Theorem): for a commutative C*-algebra `𝒜` the Gelfand representation
`γ : 𝒜 → C(spec 𝒜)` is an miu-isomorphism — it is bijective (Mathlib:
`gelfandTransform_bijective`; and star-preserving by
`gelfand_representation_basic_2`, so a ⋆-isomorphism:
`gelfandStarTransform`). -/
theorem gelfand : Function.Bijective (gelfandTransform ℂ 𝒜) :=
  sorry

end GelfandRepresentation

/-! ## Parsec 280: the continuous functional calculus -/

section FunctionalCalculus

variable {𝒜 : Type*} [CStarAlgebra 𝒜]

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 1: there
is a least C*-subalgebra `C*(a)` of `𝒜` containing `a` — Mathlib's
`StarAlgebra.elemental ℂ a`. -/
theorem functional_calculus_1 (a : 𝒜) :
    IsLeast {S : StarSubalgebra ℂ 𝒜 | a ∈ S ∧ IsClosed (S : Set 𝒜)}
      (StarAlgebra.elemental ℂ a) :=
  sorry

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 1b:
every `b ∈ C*(a)` commutes with every `c` that commutes with `a` (and with
`a*`). -/
theorem functional_calculus_1b (a b : 𝒜) (hb : b ∈ StarAlgebra.elemental ℂ a)
    (c : 𝒜) (hc : a * c = c * a) (hc' : star a * c = c * star a) :
    b * c = c * b :=
  sorry

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 2: `a`
is *normal* (`C*(a)` commutative, Mathlib: `IsStarNormal a`) iff
`a a* = a* a` iff `Re(a) Im(a) = Im(a) Re(a)`. -/
theorem functional_calculus_2 (a : 𝒜) :
    ((∀ x y : StarAlgebra.elemental ℂ a, x * y = y * x) ↔
      a * star a = star a * a) ∧
    (a * star a = star a * a ↔
      (ℜ a : 𝒜) * (ℑ a : 𝒜) = (ℑ a : 𝒜) * (ℜ a : 𝒜)) :=
  sorry

/-! **28II**, part 3: for normal `a` the functional calculus
`Φ : C(spec a) → 𝒜`, `f ↦ f(a)`, obtained by composing Gelfand's
representation theorem for `C*(a)` with the restriction along
`j : spec(C*(a)) → spec(a)`, `ρ ↦ ρ(a)` — in Mathlib the continuous
functional calculus `cfc f a` (for `f : ℂ → ℂ` continuous on `spec a`),
and `CFC.rpow a α` for the powers `a^α`, `a ≥ 0`, `α ∈ (0,∞)`. -/

section Ordered
variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 3
(sample property): `a^α a^β = a^{α+β}` for `a ≥ 0` and `α, β ∈ (0,∞)`. -/
theorem functional_calculus_3 (a : 𝒜) (ha : 0 ≤ a) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) :
    CFC.rpow a α * CFC.rpow a β = CFC.rpow a (α + β) :=
  sorry

end Ordered

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 4:
`f(a)` is the unique element `b` of `C*(a)` with `φ(b) = f(φ(a))` for all
`φ ∈ spec(C*(a))`. -/
theorem functional_calculus_4 (a : 𝒜) [IsStarNormal a] (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) :
    ∃! b : StarAlgebra.elemental ℂ a,
      ∀ φ : characterSpace ℂ (StarAlgebra.elemental ℂ a),
        φ b = f (φ (⟨a, StarAlgebra.elemental.self_mem ℂ a⟩ :
          StarAlgebra.elemental ℂ a)) :=
  sorry

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 5
(Spectral mapping theorem): `spec(f(a)) = f(spec(a))` for normal `a` and
`f ∈ C(spec a)`.  (Mathlib: `cfc_map_spectrum`.) -/
theorem functional_calculus_5 (a : 𝒜) [IsStarNormal a] (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) :
    spectrum ℂ (cfc f a) = f '' spectrum ℂ a :=
  sorry

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 6:
`spec(ρ(a)) ⊆ spec(a)` and `ρ(f(a)) = f(ρ(a))` for every miu-map
`ρ : 𝒜 → ℬ`. -/
theorem functional_calculus_6 {ℬ : Type*} [CStarAlgebra ℬ]
    (ρ : 𝒜 →⋆ₐ[ℂ] ℬ) (a : 𝒜) [IsStarNormal a] (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) :
    spectrum ℂ (ρ a) ⊆ spectrum ℂ a ∧ ρ (cfc f a) = cfc f (ρ a) :=
  sorry

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 7:
`g(f(a)) = (g ∘ f)(a)` for normal `a`.  (Mathlib: `cfc_comp`.) -/
theorem functional_calculus_7 (a : 𝒜) [IsStarNormal a] (f g : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a))
    (hg : ContinuousOn g (f '' spectrum ℂ a)) :
    cfc g (cfc f a) = cfc (g ∘ f) a :=
  sorry

section Ordered2
variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 7b:
`(a^α)^β = a^{αβ}` for `a ≥ 0` and `α, β ∈ (0,∞)`. -/
theorem functional_calculus_7b (a : 𝒜) (ha : 0 ≤ a) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) :
    CFC.rpow (CFC.rpow a α) β = CFC.rpow a (α * β) :=
  sorry

/-- **28III** (`sqrt-monotone`, cstar.tex:4353, Theorem): `0 ≤ a ≤ b`
implies `a^α ≤ b^α` for `α ∈ (0, 1]`; in particular the square root is
monotone on the positive elements. -/
theorem sqrt_monotone (a b : 𝒜) (ha : 0 ≤ a) (hab : a ≤ b) (α : ℝ)
    (h0 : 0 < α) (h1 : α ≤ 1) :
    CFC.rpow a α ≤ CFC.rpow b α :=
  sorry

end Ordered2

end FunctionalCalculus

/-! ## Parsec 290 (`gelfand-equivalence`): duality with compact Hausdorff spaces

**29I** (cstar.tex:4475): the functors `C : CH → (cCStar_miu)^op` and
`spec : (cCStar_miu)^op → CH`, and the statement that the Gelfand
representations form a natural isomorphism giving an equivalence
`(cCStar_miu)^op ≃ CH`.  The construction of the categories is out of scope
here; the key mathematical content is **29II** and **29VII** below. -/

section Duality

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **29II** (cstar.tex:4503, Lemma): every miu-map `τ : C(X) → ℂ`, `X`
compact Hausdorff, is given by evaluation at some point `x ∈ X`. -/
theorem multiplicative_state_on_cx (τ : C(X, ℂ) →⋆ₐ[ℂ] ℂ) :
    ∃ x : X, ∀ f : C(X, ℂ), τ f = f x :=
  sorry

/-- **29VII** (cstar.tex:4563, Exercise): the map `x ↦ δₓ` (with
`δₓ(f) = f(x)`, an miu-map) is a homeomorphism from `X` onto
`spec(C(X))`.  (Mathlib: `WeakDual.CharacterSpace.homeoEval`.) -/
theorem eval_homeomorphism :
    ∃ e : X ≃ₜ characterSpace ℂ C(X, ℂ),
      ∀ (x : X) (f : C(X, ℂ)), (e x : WeakDual ℂ C(X, ℂ)) f = f x :=
  sorry

variable {𝒜 ℬ : Type*} [CStarAlgebra 𝒜] [CStarAlgebra ℬ]

/-- **29VIII** (`injective-miu-isometry`, cstar.tex:4573, Exercise): every
injective miu-map between C*-algebras is an isometry.  (The intermediate
categorical steps — mono = injective and epi = surjective in `CH` — are part
of the proof and not converted separately.) -/
theorem injective_miu_isometry (ρ : 𝒜 →⋆ₐ[ℂ] ℬ)
    (hρ : Function.Injective ρ) (a : 𝒜) : ‖ρ a‖ = ‖a‖ :=
  sorry

/-- **29IX** (`injective-miu-iso-on-image`, cstar.tex:4600, Exercise): the
range of an injective miu-map `ρ : 𝒜 → ℬ` is closed, hence a C*-subalgebra
of `ℬ` isomorphic to `𝒜`. -/
theorem injective_miu_iso_on_image (ρ : 𝒜 →⋆ₐ[ℂ] ℬ)
    (hρ : Function.Injective ρ) : IsClosed (Set.range ρ) :=
  sorry

end Duality

/-! ## Parsec 300: representation by bounded operators

**30I** (`completion-inner-product-space`, cstar.tex:4613): the plan for the
Gelfand–Naimark theorem via the GNS construction — nothing to formalize. -/

section GNS

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **30II** (`state-inner-product`, cstar.tex:4662, Lemma): for every p-map
`ω : 𝒜 → ℂ` on a C*-algebra, `[a, b]_ω = ω(a* b)` defines an inner product
on `𝒜` (positive semi-definite, conjugate symmetric; linearity in the second
argument is automatic). -/
theorem state_inner_product (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω)
    (a b : 𝒜) :
    0 ≤ ω (star a * a) ∧ star (ω (star a * b)) = ω (star b * a) :=
  sorry

/-- The seminorm `‖a‖_ω = ω(a* a)^{1/2}` induced by a positive functional
`ω` (**30IV**, `omega-norm-basic`, cstar.tex:4680). -/
noncomputable def omegaSeminorm (ω : 𝒜 →ₗ[ℂ] ℂ) (a : 𝒜) : ℝ :=
  Real.sqrt (ω (star a * a)).re

/-- **30IV** (`omega-norm-basic`, cstar.tex:4680, Exercise), part 1
(Kadison's inequality): `|ω(a* b)|² ≤ ω(a* a) ω(b* b)` for a p-map `ω`. -/
theorem omega_norm_basic_1 (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω)
    (a b : 𝒜) :
    ((‖ω (star a * b)‖ : ℂ)) ^ 2 ≤ ω (star a * a) * ω (star b * b) :=
  sorry

/-- **30IV** (`omega-norm-basic`, cstar.tex:4680, Exercise), part 2:
`‖ab‖_ω ≤ ‖a‖ ‖b‖_ω` (using `a* a ≤ ‖a‖²`; the thesis writes an additional
harmless factor `‖ω‖`).  The counterexamples to the variants
`‖ab‖_ω ≤ ‖ω‖ ‖a‖_ω ‖b‖`, `‖ab‖_ω ≤ ‖a‖_ω ‖b‖_ω`, `‖a* a‖_ω = ‖a‖_ω²` and
`‖a*‖_ω = ‖a‖_ω` are not converted. -/
theorem omega_norm_basic_2 (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω)
    (a b : 𝒜) :
    omegaSeminorm ω (a * b) ≤ ‖a‖ * omegaSeminorm ω b :=
  sorry

/-- **30V** (`inner-product-completion`, cstar.tex:4733, Exercise): every
complex inner product space `V` can be completed to a Hilbert space `H` in
which it embeds densely (Mathlib: `UniformSpace.Completion` with its
`InnerProductSpace` instance; the intermediate steps — the metric, extension
of uniformly continuous maps and of bounded linear maps — are Mathlib's
completion API). -/
theorem inner_product_completion (V : Type v) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] :
    ∃ (H : Type v) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (e : V →ₗᵢ[ℂ] H), DenseRange e :=
  sorry

/-! **30VI** (`gns`, cstar.tex:4779, Definition (Gelfand–Naimark–Segal
construction)): for a p-map `ω : 𝒜 → ℂ`, the Hilbert space `ℋ_ω` is the
completion of `𝒜` under `[·,·]_ω`, with embedding `η_ω : 𝒜 → ℋ_ω`, and
`ϱ_ω(a) : ℋ_ω → ℋ_ω` is the continuous extension of `b ↦ ab`.  In Mathlib
(`Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`), for
`ω : 𝒜 →ₚ[ℂ] ℂ`: `ω.PreGNS` (= `𝒜` with the `[·,·]_ω` inner product),
`ω.GNS` (its completion), and `ω.gnsStarAlgHom : 𝒜 →⋆ₐ[ℂ] B(ω.GNS)`. -/

/-- **30VII** (cstar.tex:4812, Proposition): `ϱ_ω : 𝒜 → B(ℋ_ω)` is an
miu-map — Mathlib's `ω.gnsStarAlgHom` is bundled as one; the defining
property `ϱ_ω(a) η_ω(b) = η_ω(ab)` is recorded here. -/
theorem gns_starAlgHom_apply (ω : 𝒜 →ₚ[ℂ] ℂ) (a b : 𝒜) :
    ω.gnsStarAlgHom a ((ω.toPreGNS b : ω.PreGNS) : ω.GNS) =
      ((ω.toPreGNS (a * b) : ω.PreGNS) : ω.GNS) :=
  sorry

/-! **30IX** (`gelfand-naimark-representation`, cstar.tex:4859, Definition):
given a collection `Ω` of p-maps on `𝒜`, the representation
`ϱ_Ω : 𝒜 → B(⊕_{ω∈Ω} ℋ_ω)`, `ϱ_Ω(a) x = (ϱ_ω(a) x(ω))_ω`.  Rather than
constructing the direct sum representation here, its relevant properties are
stated existentially in **30X** and **30XIV** below. -/

variable (𝒜) in
/-- The map `a ↦ b* a b` as a linear map (used to express condition 3 of
**30X**). -/
noncomputable def conjMap (b : 𝒜) : 𝒜 →ₗ[ℂ] 𝒜 :=
  (LinearMap.mulLeft ℂ (star b)).comp (LinearMap.mulRight ℂ b)

/-- **30X** (`proto-gelfand-naimark`, cstar.tex:4870, Proposition),
equivalence (2) ↔ (3): a collection `Ω` of p-maps on `𝒜` is centre
separating iff `Ω' = { ω(b* (·) b) : ω ∈ Ω, b ∈ 𝒜 }` is order separating. -/
theorem proto_gelfand_naimark_1 {ι : Type v} (ω : ι → (𝒜 →ₗ[ℂ] ℂ))
    (hpos : ∀ i, IsPositiveMap (ω i)) :
    CentreSeparating (fun i => ω i) ↔
      OrderSeparating (fun p : ι × 𝒜 => (ω p.1).comp (conjMap 𝒜 p.2)) :=
  sorry

/-- **30X** (`proto-gelfand-naimark`, cstar.tex:4870, Proposition),
(2) ⇒ (1) and final claim: if `Ω` is centre separating then `ϱ_Ω` is
injective, so `𝒜` is miu-isomorphic to a C*-algebra of bounded operators on
the Hilbert space `ℋ_Ω` (by **29IX**).  Stated existentially. -/
theorem proto_gelfand_naimark_2 {ι : Type v} (ω : ι → (𝒜 →ₗ[ℂ] ℂ))
    (hpos : ∀ i, IsPositiveMap (ω i))
    (hc : CentreSeparating (fun i => ω i)) :
    ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H)
      (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ρ : 𝒜 →⋆ₐ[ℂ] (H →L[ℂ] H)), Function.Injective ρ :=
  sorry

end GNS

/-- **30XIV** (`gelfand-naimark`, cstar.tex:4941, Theorem
(Gelfand–Naimark)): every C*-algebra `𝒜` is miu-isomorphic to a C*-algebra
of bounded operators on a Hilbert space. -/
theorem gelfand_naimark (𝒜 : Type u) [CStarAlgebra 𝒜] :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (ρ : 𝒜 →⋆ₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective ρ :=
  sorry

end Theses.A.CStar
