/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 4280–5965.

  parsec 1590:  |x⟩⟨y| operators, ultraweak density of their span
  parsec 1600:  orthocomplements and the projection theorem
  parsec 1610:  ℓ²((pᵢ)ᵢ) and orthonormal bases
  parsec 1620:  comparison of projections; the normal form of self-dual
                modules over factors
  parsec 1630:  the completion is determined by its universal property
  parsec 1640:  the self-dual exterior tensor product
  parsec 1650:  𝒷ᵃ(X) ⊗ 𝒷ᵃ(Y) ≅ 𝒷ᵃ(X ⊗ Y)
  parsec 1660:  ultranorm continuity of the exterior tensor product
  parsec 1670:  the tensor product of Paschke dilations

Statements only; every proof is `sorry`.  Conventions as in
`HilbertModules.lean` (mirrored left-action convention).

NOTE(proc-dep): the tensor product of von Neumann algebras is developed in
thesis A (proc.tex, parsec 1080, label `tensor`), which is not yet
formalized; the interface needed here (an miu-bilinear map whose product
np-functionals are separating and whose image generates) is axiomatized
below as `IsVNTensor`.
-/
import Theses.B.Dils.Paschke
import Theses.B.Dils.Kaplansky

open scoped ComplexOrder CStarAlgebra WithCStarModule Uniformity
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u v

namespace Theses.B.Dils

/-! ## Parsec 1590: the operators |x⟩⟨y|

**159I** (dils.tex:4282): introduction — nothing to formalize. -/

section Ketbra

variable {ℬ : Type u} {X : Type v}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]

/-! ### Elementary properties of the module action

`CStarModule ℬ X` assumes only `SMul ℬ X`; the module laws for that action
are consequences of the axioms, by definiteness of the inner product (the
same derivation as `Theses.A.CStar.moduleAdjointable_linear`).  Together
with `norm_op_smul_le` these are exactly what is needed to *define* the
operator `|x⟩⟨y| : z ↦ ⟨y,z⟩ • x` of **159II** as a
`LinearMap.mkContinuous`. -/

theorem op_add_smul (a b : ℬ) (x : X) : (a + b) • x = a • x + b • x :=
  eq_of_inner_right_eq (𝒜 := ℬ) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_add_right,
      CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_right, add_mul]

theorem op_mul_smul (a b : ℬ) (x : X) : (a * b) • x = a • (b • x) :=
  eq_of_inner_right_eq (𝒜 := ℬ) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_right,
      CStarModule.inner_op_smul_right, mul_assoc]

theorem op_smul_complex_smul (c : ℂ) (a : ℬ) (x : X) :
    (c • a) • x = c • (a • x) :=
  eq_of_inner_right_eq (𝒜 := ℬ) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_smul_right_complex,
      CStarModule.inner_op_smul_right, smul_mul_assoc]

theorem op_smul_add (a : ℬ) (x y : X) : a • (x + y) = a • x + a • y :=
  eq_of_inner_right_eq (𝒜 := ℬ) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_add_right,
      CStarModule.inner_add_right, CStarModule.inner_op_smul_right,
      CStarModule.inner_op_smul_right, mul_add]

theorem op_zero_smul (x : X) : (0 : ℬ) • x = 0 :=
  eq_of_inner_right_eq (𝒜 := ℬ) fun z => by
    rw [CStarModule.inner_op_smul_right, zero_mul, CStarModule.inner_zero_right]

theorem op_smul_zero (a : ℬ) : a • (0 : X) = 0 :=
  eq_of_inner_right_eq (𝒜 := ℬ) fun z => by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_zero_right, mul_zero]

theorem norm_op_smul_le (a : ℬ) (x : X) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ := by
  have hinner : (inner ℬ (a • x) (a • x) : ℬ) = a * inner ℬ x x * star a := by
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_left,
      mul_assoc]
  have hsq : ‖a • x‖ ^ 2 ≤ (‖a‖ * ‖x‖) ^ 2 := by
    rw [CStarModule.norm_sq_eq (A := ℬ), hinner]
    calc ‖a * inner ℬ x x * star a‖ ≤ ‖a‖ * ‖(inner ℬ x x : ℬ)‖ * ‖star a‖ :=
          (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = (‖a‖ * ‖x‖) ^ 2 := by
          rw [norm_star, ← CStarModule.norm_sq_eq (A := ℬ)]; ring
  have h1 : (0 : ℝ) ≤ ‖a • x‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖a‖ * ‖x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

variable (ℬ) in
/-- **159II** (dils.tex:4292, Definition): for `x, y` in a Hilbert
ℬ-module `X`, the bounded operator `|x⟩⟨y| : z ↦ x⟨y,z⟩` (mirrored:
`⟨y,z⟩ • x`; in the literature `θ_{x,y}`, **159IIa**).

The algebra `ℬ` is an explicit argument: `CStarModule ℬ X` is what supplies
the ℬ-valued inner product `⟨y,z⟩`, and it cannot be inferred from `x, y :
X` alone. -/
noncomputable def mketbra (x y : X) : X →L[ℂ] X :=
  LinearMap.mkContinuous
    { toFun := fun z => inner ℬ y z • x
      map_add' := fun z z' => by
        rw [CStarModule.inner_add_right, op_add_smul]
      map_smul' := fun c z => by
        rw [CStarModule.inner_smul_right_complex, op_smul_complex_smul,
          RingHom.id_apply] }
    (‖y‖ * ‖x‖) fun z => by
      calc ‖(inner ℬ y z : ℬ) • x‖ ≤ ‖(inner ℬ y z : ℬ)‖ * ‖x‖ :=
            norm_op_smul_le _ _
        _ ≤ ‖y‖ * ‖z‖ * ‖x‖ :=
            mul_le_mul_of_nonneg_right (CStarModule.norm_inner_le X)
              (norm_nonneg _)
        _ = ‖y‖ * ‖x‖ * ‖z‖ := by ring

variable (ℬ) in
/-- **159II** (dils.tex:4292, Definition), characterizing property:
`|x⟩⟨y| z = ⟨y,z⟩ • x`. -/
theorem mketbra_apply (x y z : X) :
    mketbra ℬ x y z = inner ℬ y z • x :=
  rfl

variable (ℬ) in
/-- **159III** (`hilbmodketbrarules`, dils.tex:4302): `|x⟩⟨y|` is
adjointable, with adjoint `|y⟩⟨x|`. -/
theorem mketbra_adjointable (x y : X) :
    ModuleAdjointTo ℬ (⇑(mketbra ℬ x y) : X → X) ⇑(mketbra ℬ y x) := by
  intro z w
  rw [mketbra_apply, mketbra_apply, CStarModule.inner_op_smul_left,
    CStarModule.inner_op_smul_right, CStarModule.star_inner]

variable (ℬ) in
/-- **159III** (`hilbmodketbrarules`, dils.tex:4302): the calculus of the
`|x⟩⟨y|`: `|xb⟩⟨y| = |x⟩⟨yb*|` (mirrored) and
`|x⟩⟨y| |v⟩⟨w| = |x⟨y,v⟩⟩⟨w|`; if `⟨e,e⟩` is a projection then `|e⟩⟨e|`
is a projection; and `T|x⟩⟨y| = |Tx⟩⟨y|`, `|x⟩⟨y| T* = |x⟩⟨Ty|` for
adjointable `T`. -/
theorem mketbra_rules (x y v w e : X) (b : ℬ)
    (T T' : X →L[ℂ] X) (hT : ModuleAdjointTo ℬ ⇑T ⇑T')
    (he : IsStarProjection (inner ℬ e e)) :
    mketbra ℬ (b • x) y = mketbra ℬ x (star b • y) ∧
    (mketbra ℬ x y).comp (mketbra ℬ v w) = mketbra ℬ (inner ℬ y v • x) w ∧
    ((mketbra ℬ e e).comp (mketbra ℬ e e) = mketbra ℬ e e ∧
      ModuleAdjointTo ℬ (⇑(mketbra ℬ e e) : X → X) ⇑(mketbra ℬ e e)) ∧
    T.comp (mketbra ℬ x y) = mketbra ℬ (T x) y ∧
    (mketbra ℬ x y).comp T' = mketbra ℬ x (T y) := by
  obtain ⟨-, hTc, hTm⟩ := moduleAdjointable_linear (𝒜 := ℬ) ⇑T ⟨_, hT⟩
  refine ⟨?_, ?_, ⟨?_, mketbra_adjointable ℬ e e⟩, ?_, ?_⟩
  · ext z
    change (inner ℬ y z : ℬ) • (b • x) = (inner ℬ (star b • y) z : ℬ) • x
    rw [CStarModule.inner_op_smul_left, star_star, op_mul_smul]
  · ext z
    change (inner ℬ y ((inner ℬ w z : ℬ) • v) : ℬ) • x
      = (inner ℬ w z : ℬ) • ((inner ℬ y v : ℬ) • x)
    rw [CStarModule.inner_op_smul_right, op_mul_smul]
  · ext z
    change (inner ℬ e ((inner ℬ e z : ℬ) • e) : ℬ) • e = (inner ℬ e z : ℬ) • e
    rw [CStarModule.inner_op_smul_right, op_mul_smul, mod_projelabs e he]
  · ext z
    change T ((inner ℬ y z : ℬ) • x) = (inner ℬ y z : ℬ) • T x
    rw [hTm]
  · ext z
    change (inner ℬ y (T' z) : ℬ) • x = (inner ℬ (T y) z : ℬ) • x
    rw [hT y z]

variable [CompleteSpace X]

/-- **159IV** (`ketbra-ultraweakly-dense`, dils.tex:4319, Proposition): for
a self-dual Hilbert ℬ-module `X` with orthonormal basis `(eᵢ)`, the linear
span of the operators `|eᵢb⟩⟨eⱼ|` is ultraweakly dense in `ℬᵃ(X)`: every
`T` is the ultraweak limit of a net (canonically `p_S T p_S`, indexed by
finite subsets of the basis) from the span.

**159V**–**159VIII** are the proof — not converted. -/
theorem ketbra_ultraweakly_dense [VonNeumannAlgebra ℬ]
    (hX : SelfDual ℬ X) {ι : Type v} (e : ι → X) (he : IsONBasis ℬ e)
    (T : Ba ℬ X) :
    ∃ approx : Finset ι → Ba ℬ X,
      (∀ s, approx s ∈ Submodule.span ℂ
        {S : Ba ℬ X | ∃ (i j : ι) (b : ℬ), S.1 = mketbra ℬ (b • e i) (e j)}) ∧
      UWTendsto approx atTop T :=
  sorry

/-- **159IX** (`ketbra-ultranorm-continuous`, dils.tex:4378, Proposition):
for a self-dual Hilbert ℬ-module `X`: if a norm-bounded net `x_α → x`
ultranorm, then `|x_α⟩⟨y| → |x⟩⟨y|` ultraweakly.

**159X**–**159XI** are the proof — not converted. -/
theorem ketbra_ultranorm_continuous [VonNeumannAlgebra ℬ]
    (hX : SelfDual ℬ X) {ι : Type v} {l : Filter ι} (x : ι → X) (x₀ : X)
    (hbdd : ∃ M : ℝ, ∀ i, ‖x i‖ ≤ M)
    (hx : UnTendsto (inner ℬ) x l x₀) (y : X)
    (K : ι → Ba ℬ X) (hK : ∀ i, (K i).1 = mketbra ℬ (x i) y)
    (K₀ : Ba ℬ X) (hK₀ : K₀.1 = mketbra ℬ x₀ y) :
    UWTendsto K l K₀ :=
  sorry

end Ketbra

/-! ## Parsec 1600: orthocomplements

**160I** (dils.tex:4456): introduction — nothing to formalize. -/

section Ortho

variable {ℬ : Type u} {X Y Z : Type v}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z] [SMul ℬ Z] [CStarModule ℬ Z]

omit [StarOrderedRing ℬ] in
/-- An inner-product-preserving map between pre-Hilbert ℬ-modules is
automatically additive: `⟨κ(x+x') − κx − κx', κ(x+x') − κx − κx'⟩` expands to
`⟨(x+x') − x − x', (x+x') − x − x'⟩ = 0`. -/
theorem innerPreserving_add (κ : X → Z)
    (h : ∀ x x' : X, inner ℬ (κ x) (κ x') = inner ℬ x x') (x x' : X) :
    κ (x + x') = κ x + κ x' := by
  have hz : (inner ℬ (κ (x + x') - (κ x + κ x')) (κ (x + x') - (κ x + κ x')) : ℬ)
      = 0 := by
    simp only [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
      CStarModule.inner_add_left, CStarModule.inner_add_right, h]
    abel
  have h0 := CStarModule.inner_self (A := ℬ) (x := κ (x + x') - (κ x + κ x')) |>.mp hz
  rwa [sub_eq_zero] at h0

omit [StarOrderedRing ℬ] in
/-- The additive-monoid-hom packaging of an inner-product-preserving map
(`innerPreserving_add`). -/
noncomputable def innerPreservingHom (κ : X → Z)
    (h : ∀ x x' : X, inner ℬ (κ x) (κ x') = inner ℬ x x') : X →+ Z :=
  AddMonoidHom.mk' κ (innerPreserving_add κ h)

/-- Taking the left part of a finite subset of `ι ⊕ κ` is cofinal: the net
indexed by `Finset (ι ⊕ κ)` refines the one indexed by `Finset ι`. -/
private theorem tendsto_finset_toLeft_atTop {ι κ : Type v} :
    Tendsto (Finset.toLeft : Finset (ι ⊕ κ) → Finset ι) atTop atTop :=
  Filter.tendsto_atTop_atTop.mpr fun t =>
    ⟨t.map Function.Embedding.inl, fun _ hs _ hi =>
      Finset.mem_toLeft.mpr (hs (Finset.mem_map_of_mem _ hi))⟩

private theorem tendsto_finset_toRight_atTop {ι κ : Type v} :
    Tendsto (Finset.toRight : Finset (ι ⊕ κ) → Finset κ) atTop atTop :=
  Filter.tendsto_atTop_atTop.mpr fun t =>
    ⟨t.map Function.Embedding.inr, fun _ hs _ hi =>
      Finset.mem_toRight.mpr (hs (Finset.mem_map_of_mem _ hi))⟩

/-- **160II** (`direct-prod-self-dual-basis`, dils.tex:4465, Exercise): the
direct sum of self-dual Hilbert ℬ-modules `X ⊕ Y` (represented abstractly:
a Hilbert ℬ-module `Z` with module embeddings `κ₁, κ₂` which are mutually
orthogonal, inner-product-preserving and jointly surjective) has
`κ₁(E) ∪ κ₂(F)` as an orthonormal basis for bases `E` of `X`, `F` of `Y`;
in particular it is self dual. -/
theorem direct_prod_self_dual_basis [VonNeumannAlgebra ℬ]
    [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
    (κ₁ : X → Z) (κ₂ : Y → Z)
    (h₁ : ∀ x x' : X, inner ℬ (κ₁ x) (κ₁ x') = inner ℬ x x')
    (h₂ : ∀ y y' : Y, inner ℬ (κ₂ y) (κ₂ y') = inner ℬ y y')
    (h₁₂ : ∀ (x : X) (y : Y), inner ℬ (κ₁ x) (κ₂ y) = 0)
    (hadd : ∀ z : Z, ∃ (x : X) (y : Y), z = κ₁ x + κ₂ y)
    (hκ₁ : ∀ (b : ℬ) (x : X), κ₁ (b • x) = b • κ₁ x)
    (hκ₂ : ∀ (b : ℬ) (y : Y), κ₂ (b • y) = b • κ₂ y)
    {ι κ : Type v} (e : ι → X) (d : κ → Y)
    (he : IsONBasis ℬ e) (hd : IsONBasis ℬ d) :
    IsONBasis ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d)) ∧ SelfDual ℬ Z := by
  set K₁ : X →+ Z := innerPreservingHom κ₁ h₁ with hK₁def
  set K₂ : Y →+ Z := innerPreservingHom κ₂ h₂ with hK₂def
  have h₂₁ : ∀ (y : Y) (x : X), (inner ℬ (κ₂ y) (κ₁ x) : ℬ) = 0 := by
    intro y x
    have h := congrArg star (h₁₂ x y)
    rwa [CStarModule.star_inner, star_zero] at h
  -- splitting a finite sum over `ι ⊕ κ`
  have hsplit : ∀ (c : ι ⊕ κ → ℬ) (s : Finset (ι ⊕ κ)),
      ∑ g ∈ s, c g • Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) g
        = κ₁ (∑ i ∈ s.toLeft, c (Sum.inl i) • e i)
          + κ₂ (∑ j ∈ s.toRight, c (Sum.inr j) • d j) := by
    intro c s
    rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
    congr 1
    · rw [show κ₁ (∑ i ∈ s.toLeft, c (Sum.inl i) • e i)
        = K₁ (∑ i ∈ s.toLeft, c (Sum.inl i) • e i) from rfl, map_sum]
      exact Finset.sum_congr rfl fun i _ => (hκ₁ _ _).symm
    · rw [show κ₂ (∑ j ∈ s.toRight, c (Sum.inr j) • d j)
        = K₂ (∑ j ∈ s.toRight, c (Sum.inr j) • d j) from rfl, map_sum]
      exact Finset.sum_congr rfl fun j _ => (hκ₂ _ _).symm
  -- the embeddings are ultranorm isometries
  have htr₁ : ∀ (ω : NPFunctional ℬ) (u u' : X),
      unSeminorm ω (inner ℬ : Z → Z → ℬ) (κ₁ u - κ₁ u')
        = unSeminorm ω (inner ℬ : X → X → ℬ) (u - u') := by
    intro ω u u'
    rw [show κ₁ u - κ₁ u' = κ₁ (u - u') from (map_sub K₁ u u').symm,
      unSeminorm, unSeminorm, h₁]
  have htr₂ : ∀ (ω : NPFunctional ℬ) (u u' : Y),
      unSeminorm ω (inner ℬ : Z → Z → ℬ) (κ₂ u - κ₂ u')
        = unSeminorm ω (inner ℬ : Y → Y → ℬ) (u - u') := by
    intro ω u u'
    rw [show κ₂ u - κ₂ u' = κ₂ (u - u') from (map_sub K₂ u u').symm,
      unSeminorm, unSeminorm, h₂]
  -- the joint convergence statement used for both clauses of `IsONBasis`
  have hconv : ∀ (c : ι ⊕ κ → ℬ) (x : X) (y : Y),
      UnTendsto (inner ℬ) (fun t : Finset ι => ∑ i ∈ t, c (Sum.inl i) • e i) atTop x →
      UnTendsto (inner ℬ) (fun u : Finset κ => ∑ j ∈ u, c (Sum.inr j) • d j) atTop y →
      UnTendsto (inner ℬ)
        (fun s : Finset (ι ⊕ κ) => ∑ g ∈ s, c g • Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) g)
        atTop (κ₁ x + κ₂ y) := by
    intro c x y hx hy ω
    simp only [hsplit c]
    refine squeeze_zero (fun s => unSeminorm_nonneg _ _ _)
      (g := fun s : Finset (ι ⊕ κ) =>
        unSeminorm ω (inner ℬ : X → X → ℬ)
            ((∑ i ∈ s.toLeft, c (Sum.inl i) • e i) - x)
          + unSeminorm ω (inner ℬ : Y → Y → ℬ)
            ((∑ j ∈ s.toRight, c (Sum.inr j) • d j) - y)) (fun s => ?_) ?_
    · have hrw : κ₁ (∑ i ∈ s.toLeft, c (Sum.inl i) • e i)
            + κ₂ (∑ j ∈ s.toRight, c (Sum.inr j) • d j) - (κ₁ x + κ₂ y)
          = (κ₁ (∑ i ∈ s.toLeft, c (Sum.inl i) • e i) - κ₁ x)
            + (κ₂ (∑ j ∈ s.toRight, c (Sum.inr j) • d j) - κ₂ y) := by abel
      rw [hrw, ← htr₁ ω _ x, ← htr₂ ω _ y]
      exact unSeminorm_add_le ω (cstarBInner ℬ Z) _ _
    · have hL := (hx ω).comp (tendsto_finset_toLeft_atTop (ι := ι) (κ := κ))
      have hR := (hy ω).comp (tendsto_finset_toRight_atTop (ι := ι) (κ := κ))
      simpa using hL.add hR
  -- orthonormality
  have hbasis : IsONBasis ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d)) := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rintro (i | j) (i' | j') hne
      · exact (h₁ _ _).trans (he.1.1 i i' (fun h => hne (by rw [h])))
      · exact h₁₂ _ _
      · exact h₂₁ _ _
      · exact (h₂ _ _).trans (hd.1.1 j j' (fun h => hne (by rw [h])))
    · rintro (i | j)
      · rw [show (inner ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) (Sum.inl i))
          (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) (Sum.inl i)) : ℬ) = inner ℬ (e i) (e i) from h₁ _ _]
        exact he.1.2 i
      · rw [show (inner ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) (Sum.inr j))
          (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) (Sum.inr j)) : ℬ) = inner ℬ (d j) (d j) from h₂ _ _]
        exact hd.1.2 j
    · intro z
      obtain ⟨x, y, rfl⟩ := hadd z
      have hcoefL : ∀ i : ι,
          (inner ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) (Sum.inl i)) (κ₁ x + κ₂ y) : ℬ)
            = inner ℬ (e i) x := by
        intro i
        change (inner ℬ (κ₁ (e i)) (κ₁ x + κ₂ y) : ℬ) = _
        rw [CStarModule.inner_add_right, h₁, h₁₂, add_zero]
      have hcoefR : ∀ j : κ,
          (inner ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) (Sum.inr j)) (κ₁ x + κ₂ y) : ℬ)
            = inner ℬ (d j) y := by
        intro j
        change (inner ℬ (κ₂ (d j)) (κ₁ x + κ₂ y) : ℬ) = _
        rw [CStarModule.inner_add_right, h₂, h₂₁, zero_add]
      refine hconv (fun g => inner ℬ (Sum.elim (κ₁ ∘ e) (κ₂ ∘ d) g) (κ₁ x + κ₂ y)) x y
        ?_ ?_
      · simpa only [hcoefL] using he.2.1 x
      · simpa only [hcoefR] using hd.2.1 y
    · rintro c ⟨M, hM⟩
      have hL : L2Summable ℬ (fun i => c (Sum.inl i)) := by
        refine ⟨M, fun t => ?_⟩
        have h := hM (t.map Function.Embedding.inl)
        rwa [Finset.sum_map] at h
      have hR : L2Summable ℬ (fun j => c (Sum.inr j)) := by
        refine ⟨M, fun t => ?_⟩
        have h := hM (t.map Function.Embedding.inr)
        rwa [Finset.sum_map] at h
      obtain ⟨x₀, hx₀⟩ := he.2.2 _ hL
      obtain ⟨y₀, hy₀⟩ := hd.2.2 _ hR
      exact ⟨κ₁ x₀ + κ₂ y₀, hconv c x₀ y₀ hx₀ hy₀⟩
  exact ⟨hbasis, selfDual_of_isONBasis hbasis⟩

variable (ℬ) in
/-- **160III** (dils.tex:4476, Definition): the **orthocomplement**
`V^⊥ = {x : ⟨x,v⟩ = 0 for all v ∈ V}` of a subset `V` of a Hilbert
C*-module. -/
def orthoCompl (V : Set X) : Set X :=
  {x : X | ∀ v ∈ V, inner ℬ x v = 0}

variable (ℬ) in
/-- The set of points ultranorm-approximable from `S` (the ultranorm
closure; auxiliary for **160IV**). -/
def unClosure (B : X → X → ℬ) (S : Set X) : Set X :=
  {x : X | ∀ (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (ε : ℝ), 0 < ε →
    ∃ d ∈ S, ∀ i, unSeminorm (ωs i) B (x - d) ≤ ε}

variable (ℬ) in
/-- The ℬ-linear span of a subset of a Hilbert ℬ-module (auxiliary for
**160IV**). -/
def bSpan (V : Set X) : Set X :=
  {x : X | ∃ (n : ℕ) (c : Fin n → ℂ) (b : Fin n → ℬ) (v : Fin n → X),
    (∀ i, v i ∈ V) ∧ x = ∑ i, c i • b i • v i}

/-- **160IV** (`hilbmod-projthm`, dils.tex:4488, Proposition), part 1: for
a subset `V` of a self-dual Hilbert ℬ-module `X`, the orthocomplement
`V^⊥` is an ultranorm-closed ℬ-submodule of `X` (and hence so is
`V^⊥⊥`). -/
theorem hilbmod_projthm_1 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (V : Set X) :
    (0 : X) ∈ orthoCompl ℬ V ∧
    (∀ x ∈ orthoCompl ℬ V, ∀ y ∈ orthoCompl ℬ V, x + y ∈ orthoCompl ℬ V) ∧
    (∀ (b : ℬ), ∀ x ∈ orthoCompl ℬ V, b • x ∈ orthoCompl ℬ V) ∧
    (∀ (c : ℂ), ∀ x ∈ orthoCompl ℬ V, c • x ∈ orthoCompl ℬ V) ∧
    unClosure ℬ (inner ℬ) (orthoCompl ℬ V) = orthoCompl ℬ V := by
  -- "It is easy to see `V^⊥` is a submodule of `X`" (dils.tex:4506)
  refine ⟨fun v _ => CStarModule.inner_zero_left, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy v hv
    rw [CStarModule.inner_add_left, hx v hv, hy v hv, add_zero]
  · intro b x hx v hv
    rw [CStarModule.inner_op_smul_left, hx v hv, zero_mul]
  · intro c x hx v hv
    rw [CStarModule.inner_smul_left_complex, hx v hv, smul_zero]
  -- "To show `V^⊥` is ultranorm closed … `⟨v, unlim xα⟩ = uslim ⟨v, xα⟩ = 0`"
  refine Set.eq_of_subset_of_subset (fun x hx v hv => ?_) (fun x hx n ωs ε hε => ?_)
  · -- every np-functional kills `⟨x,v⟩`, so it is `0` (**44XI**)
    refine np_separating _ fun ω => ?_
    set C : ℝ := unSeminorm ω (cstarBInner ℬ X).inner v with hCdef
    have hC : 0 ≤ C := unSeminorm_nonneg ω _ v
    -- `|ω⟨x,v⟩| = |ω⟨x−d,v⟩| ≤ ‖x−d‖_ω ‖v‖_ω ≤ ε C` for every `ε > 0`
    have key : ∀ ε : ℝ, 0 < ε → ‖ω (inner ℬ x v : ℬ)‖ ≤ ε * C := by
      intro ε hε
      obtain ⟨d, hd, hdist⟩ := hx 1 (fun _ => ω) ε hε
      have hsplit : (inner ℬ x v : ℬ) = inner ℬ (x - d) v := by
        rw [CStarModule.inner_sub_left, hd v hv, sub_zero]
      calc ‖ω (inner ℬ x v : ℬ)‖
          = ‖ω ((cstarBInner ℬ X).inner (x - d) v)‖ := by rw [hsplit]; rfl
        _ ≤ unSeminorm ω (cstarBInner ℬ X).inner (x - d) * C :=
            unSeminorm_inner_le ω (cstarBInner ℬ X) _ _
        _ ≤ ε * C := mul_le_mul_of_nonneg_right (hdist 0) hC
    have hzero : ‖ω (inner ℬ x v : ℬ)‖ ≤ 0 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have h1 : δ / (C + 1) * C ≤ δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith [key (δ / (C + 1)) (by positivity)]
    simpa using le_antisymm hzero (norm_nonneg _)
  · exact ⟨x, hx, fun i => by simpa [unSeminorm] using hε.le⟩

/-- **160IV** (`hilbmod-projthm`, dils.tex:4488, Proposition), part 2:
`V^⊥⊥` is the ultranorm closure of the ℬ-linear span of `V`. -/
theorem hilbmod_projthm_2 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (V : Set X) :
    orthoCompl ℬ (orthoCompl ℬ V) = unClosure ℬ (inner ℬ) (bSpan ℬ V) :=
  sorry

/-- **160IV** (`hilbmod-projthm`, dils.tex:4488, Proposition), part 3:
`V^⊥⊥ ⊕ V^⊥ ≅ X` via `(x,y) ↦ x + y`: every element of `X` decomposes
uniquely as a sum of an element of `V^⊥⊥` and one of `V^⊥`.

**160V**–**160VIII** are the proof — not converted. -/
theorem hilbmod_projthm_3 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) (V : Set X) (x : X) :
    ∃! p : X × X, p.1 ∈ orthoCompl ℬ (orthoCompl ℬ V) ∧
      p.2 ∈ orthoCompl ℬ V ∧ x = p.1 + p.2 :=
  sorry

/-- **160IX** (`selfdual-orthn-basis`, dils.tex:4565, Exercise): for an
orthonormal family `(eᵢ)` in a self-dual Hilbert ℬ-module: (1) `(eᵢ)` is a
basis of `E^⊥⊥` (every `x ∈ E^⊥⊥` is the ultranorm limit of its basis
expansion); (2) `x ∈ E^⊥⊥` iff `⟨x,x⟩ = ∑ᵢ ⟨x,eᵢ⟩⟨eᵢ,x⟩` (mirrored). -/
theorem selfdual_orthn_basis [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) {ι : Type v} (e : ι → X)
    (he : OrthonormalFam ℬ e) (x : X) :
    (x ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) →
      UnTendsto (inner ℬ)
        (fun s : Finset ι => ∑ i ∈ s, inner ℬ (e i) x • e i) atTop x) ∧
    (x ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range e)) ↔
      UWTendsto
        (fun s : Finset ι => ∑ i ∈ s, inner ℬ (e i) x * inner ℬ x (e i))
        atTop (inner ℬ x x)) :=
  sorry

/-- **160X** (`selfdual-gramschmidt`, dils.tex:4581, Exercise): for
`x₁, …, xₙ` in a self-dual Hilbert ℬ-module there is a finite orthonormal
basis of `{x₁,…,xₙ}^⊥⊥` of at most `n` elements (each `xᵢ` is its finite
basis expansion). -/
theorem selfdual_gramschmidt [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) {n : ℕ} (x : Fin n → X) :
    ∃ (m : ℕ), m ≤ n ∧ ∃ f : Fin m → X,
      OrthonormalFam ℬ f ∧
      (∀ k, f k ∈ orthoCompl ℬ (orthoCompl ℬ (Set.range x))) ∧
      ∀ i, x i = ∑ k, inner ℬ (f k) (x i) • f k :=
  sorry

end Ortho

/-! ## Parsec 1610: ℓ²((pᵢ)) and orthonormal bases

**161I** (`thel2matter`, dils.tex:4594) and **161III** (`hilbel-matter`,
dils.tex:4625, counterexamples): discussion — nothing to formalize. -/

section L2

variable {ℬ : Type u}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

variable (ℬ) in
/-- The set `ℓ²((pᵢ)ᵢ)` of ℓ²-summable tuples `(bᵢ)` with
`⌈bᵢbᵢ*⌉ ≤ pᵢ` (**161II**; mirrored), as a subset of `ι → ℬ`. -/
def L2Set [VonNeumannAlgebra ℬ] {ι : Type v} (p : ι → ℬ) : Set (ι → ℬ) :=
  {b | L2Summable ℬ b ∧ ∀ i, ceil (b i * star (b i)) ≤ p i}

/-- **161II** (`hilbmod-el2`, dils.tex:4602, Exercise), part 1: for
ℓ²-summable tuples `(bᵢ)`, `(cᵢ)` over a von Neumann algebra the inner
product `∑ᵢ bᵢ* cᵢ` (mirrored: `∑ᵢ cᵢ bᵢ*`) converges ultraweakly; with
the coordinatewise operations this turns `ℓ²((pᵢ)ᵢ)` into a (pre-)Hilbert
ℬ-module. -/
theorem hilbmod_el2_inner [VonNeumannAlgebra ℬ] {ι : Type v} (b c : ι → ℬ)
    (hb : L2Summable ℬ b) (hc : L2Summable ℬ c) :
    ∃ s : ℬ, UWTendsto (fun t : Finset ι => ∑ i ∈ t, c i * star (b i))
      atTop s :=
  sorry

variable {X : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]

/-- **161II** (`hilbmod-el2`, dils.tex:4602, Exercise), part 2:
`ℓ²((pᵢ)ᵢ)` is self dual, and every self-dual Hilbert ℬ-module `X` with
orthonormal basis `(eᵢ)ᵢ` is isomorphic to `ℓ²((⟨eᵢ,eᵢ⟩)ᵢ)` via the
coordinate map `x ↦ (⟨eᵢ,x⟩)ᵢ`: the coordinate map is injective, additive,
lands bijectively on `ℓ²((⟨eᵢ,eᵢ⟩)ᵢ)` and identifies the inner
products. -/
theorem hilbmod_el2 [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hX : SelfDual ℬ X) {ι : Type v} (e : ι → X) (he : IsONBasis ℬ e) :
    Set.BijOn (fun (x : X) (i : ι) => inner ℬ (e i) x) Set.univ
        (L2Set ℬ fun i => inner ℬ (e i) (e i)) ∧
      ∀ x y : X,
        UWTendsto
          (fun t : Finset ι =>
            ∑ i ∈ t, inner ℬ (e i) y * star (inner ℬ (e i) x))
          atTop (inner ℬ x y) :=
  sorry

/-- **161IV** (`onb1`, dils.tex:4673, Exercise), part 1: if `(eᵢ)` is an
orthonormal basis of a Hilbert ℬ-module `X` and `(uᵢ)` are partial
isometries with `uᵢuᵢ* = ⟨eᵢ,eᵢ⟩`, then `(eᵢuᵢ)ᵢ` (mirrored:
`star uᵢ • eᵢ`) is an orthonormal basis of `X`. -/
theorem onb1 [VonNeumannAlgebra ℬ] [CompleteSpace X] {ι : Type v}
    (e : ι → X) (he : IsONBasis ℬ e) (u : ι → ℬ)
    (hpi : ∀ i, IsStarProjection (star (u i) * u i))
    (hu : ∀ i, u i * star (u i) = inner ℬ (e i) (e i)) :
    IsONBasis ℬ fun i => star (u i) • e i := by
  -- `bsols.tex`, solution `onb1`, first part, transcribed.
  obtain ⟨⟨heorth, heproj⟩, hebasis, hel2⟩ := he
  -- `⟨eᵢuᵢ, eⱼuⱼ⟩ = uⱼ* ⟨eᵢ,eⱼ⟩ uᵢ` (mirrored)
  have hinner : ∀ i j : ι, (inner ℬ (star (u i) • e i) (star (u j) • e j) : ℬ)
      = star (u j) * inner ℬ (e i) (e j) * u i := by
    intro i j
    rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_left,
      star_star, mul_assoc]
  -- `⟨eᵢuᵢ, eᵢuᵢ⟩ = uᵢ*uᵢ`, a projection
  have hdiag : ∀ i : ι, (inner ℬ (star (u i) • e i) (star (u i) • e i) : ℬ)
      = star (u i) * u i := by
    intro i
    rw [hinner i i, ← hu i]
    have h := (hpi i).isIdempotentElem
    calc star (u i) * (u i * star (u i)) * u i
        = (star (u i) * u i) * (star (u i) * u i) := by noncomm_ring
      _ = star (u i) * u i := h
  -- `⟨eᵢ,x⟩⟨eᵢ,eᵢ⟩ = ⟨eᵢ,x⟩` (mirrored), from **149III**
  have hself : ∀ (i : ι) (x : X), (inner ℬ (e i) x : ℬ) * inner ℬ (e i) (e i)
      = inner ℬ (e i) x := by
    intro i x
    have hps : star (inner ℬ (e i) (e i) : ℬ) = inner ℬ (e i) (e i) :=
      (heproj i).1.isSelfAdjoint
    have h2 : (inner ℬ ((inner ℬ (e i) (e i) : ℬ) • e i) x : ℬ)
        = inner ℬ (e i) x := by rw [mod_projelabs (e i) (heproj i).1]
    rwa [CStarModule.inner_op_smul_left, hps] at h2
  -- the two families have the same partial sums
  have hterm : ∀ (x : X) (i : ι),
      (inner ℬ (star (u i) • e i) x : ℬ) • (star (u i) • e i)
        = (inner ℬ (e i) x : ℬ) • e i := by
    intro x i
    rw [CStarModule.inner_op_smul_left, star_star, ← op_mul_smul, mul_assoc,
      hu i, hself i x]
  refine ⟨⟨fun i j hij => by rw [hinner i j, heorth i j hij, mul_zero, zero_mul],
    fun i => ⟨?_, ?_⟩⟩, fun x => ?_, fun b hb => ?_⟩
  · rw [hdiag i]; exact hpi i
  · -- `uᵢ*uᵢ ≠ 0`, for otherwise `uᵢ = 0` and `⟨eᵢ,eᵢ⟩ = uᵢuᵢ* = 0`
    rw [hdiag i]
    intro h0
    have hun : ‖u i‖ * ‖u i‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, h0, norm_zero]
    have hu0 : u i = 0 := norm_eq_zero.mp (mul_self_eq_zero.mp hun)
    exact (heproj i).2 (by rw [← hu i, hu0]; simp)
  · -- basis expansion: term by term the same as for `(eᵢ)`
    have hfun : (fun s : Finset ι =>
        ∑ i ∈ s, (inner ℬ (star (u i) • e i) x : ℬ) • (star (u i) • e i))
        = fun s : Finset ι => ∑ i ∈ s, (inner ℬ (e i) x : ℬ) • e i := by
      funext s
      exact Finset.sum_congr rfl fun i _ => hterm x i
    rw [hfun]
    exact hebasis x
  · -- `∑ᵢ bᵢ(eᵢuᵢ) = ∑ᵢ (bᵢuᵢ*)eᵢ`, and `(bᵢuᵢ*)` is again ℓ²-summable
    obtain ⟨M, hM⟩ := hb
    have hple : ∀ i : ι, star (u i) * u i ≤ 1 := by
      intro i
      refine sub_nonneg.mp ?_
      have hidem : (star (u i) * u i) * (star (u i) * u i) = star (u i) * u i :=
        (hpi i).isIdempotentElem
      have hsa : star (star (u i) * u i) = star (u i) * u i :=
        (hpi i).isSelfAdjoint
      have hsq : (1 - star (u i) * u i) * (1 - star (u i) * u i)
          = 1 - star (u i) * u i := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, hidem]
        abel
      have : (1 : ℬ) - star (u i) * u i
          = star ((1 : ℬ) - star (u i) * u i) * (1 - star (u i) * u i) := by
        rw [star_sub, star_one, hsa, hsq]
      rw [this]
      exact star_mul_self_nonneg _
    have hl2 : L2Summable ℬ fun i => b i * star (u i) := by
      refine ⟨M, fun s => ?_⟩
      have hcalc : ∀ i : ι, (b i * star (u i)) * star (b i * star (u i))
          = b i * (star (u i) * u i) * star (b i) := by
        intro i; rw [star_mul, star_star]; noncomm_ring
      have hle : ∑ i ∈ s, (b i * star (u i)) * star (b i * star (u i))
          ≤ ∑ i ∈ s, b i * star (b i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hcalc i]
        have := star_right_conjugate_le_conjugate (hple i) (b i)
        rwa [mul_one] at this
      have hnn : (0 : ℬ) ≤ ∑ i ∈ s, (b i * star (u i)) * star (b i * star (u i)) :=
        Finset.sum_nonneg fun i _ => mul_star_self_nonneg _
      exact le_trans (CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hle) (hM s)
    obtain ⟨x, hx⟩ := hel2 _ hl2
    refine ⟨x, ?_⟩
    have hfun : (fun s : Finset ι => ∑ i ∈ s, b i • (star (u i) • e i))
        = fun s : Finset ι => ∑ i ∈ s, (b i * star (u i)) • e i := by
      funext s
      exact Finset.sum_congr rfl fun i _ => (op_mul_smul _ _ _).symm
    rw [hfun]
    exact hx

/-- Murray–von Neumann equivalence `p ∼ q` of projections: `u* u = p` and
`u u* = q` for some partial isometry `u` (**161IV**; cf. vn.tex 83II
`vmleq`). -/
def MvNEquiv (p q : ℬ) : Prop :=
  ∃ u : ℬ, star u * u = p ∧ u * star u = q

/-- **161IV** (`onb1`, dils.tex:4673, Exercise), part 2:
`ℓ²((pᵢ)ᵢ) ≅ ℓ²((qᵢ)ᵢ)` for pointwise Murray–von Neumann equivalent
families of projections: there is a bijection between the tuple sets that
identifies the (ultraweakly converging) inner products. -/
theorem onb1_el2 [VonNeumannAlgebra ℬ] {ι : Type v} (p q : ι → ℬ)
    (hp : ∀ i, IsStarProjection (p i)) (hq : ∀ i, IsStarProjection (q i))
    (hpq : ∀ i, MvNEquiv (p i) (q i)) :
    ∃ Φ : (ι → ℬ) → (ι → ℬ),
      Set.BijOn Φ (L2Set ℬ p) (L2Set ℬ q) ∧
      ∀ b ∈ L2Set ℬ p, ∀ c ∈ L2Set ℬ p, ∀ s : ℬ,
        UWTendsto (fun t : Finset ι => ∑ i ∈ t, c i * star (b i)) atTop s ↔
        UWTendsto (fun t : Finset ι => ∑ i ∈ t, Φ c i * star (Φ b i))
          atTop s :=
  sorry

/-- **161V** (`onb2`, dils.tex:4696, Exercise): if `(eᵢ)` is an orthonormal
basis of `X` with distinguished indices `i₁ ≠ i₂` and
`⟨e_{i₁},e_{i₁}⟩ + ⟨e_{i₂},e_{i₂}⟩ ≤ 1`, then removing `e_{i₁}, e_{i₂}`
and inserting `e_{i₁} + e_{i₂}` again yields an orthonormal basis.  (The
consequence `pℬ ⊕ qℬ ≅ (p+q)ℬ` for `p + q ≤ 1` is not converted
separately.) -/
theorem onb2 [VonNeumannAlgebra ℬ] [CompleteSpace X] {ι : Type v}
    [DecidableEq ι]
    (e : ι → X) (he : IsONBasis ℬ e) (i₁ i₂ : ι) (hne : i₁ ≠ i₂)
    (hle : inner ℬ (e i₁) (e i₁) + inner ℬ (e i₂) (e i₂) ≤ 1) :
    IsONBasis ℬ fun i : {i : ι // i ≠ i₂} =>
      if (i : ι) = i₁ then e i₁ + e i₂ else e i := by
  -- `bsols.tex`, solution `onb2`, transcribed.
  classical
  obtain ⟨⟨horth, hproj⟩, hexp, hl2⟩ := he
  set f : {i : ι // i ≠ i₂} → X :=
    fun i => if (i : ι) = i₁ then e i₁ + e i₂ else e i with hfdef
  set i₁' : {i : ι // i ≠ i₂} := ⟨i₁, hne⟩ with hi₁'
  have hpr : ∀ i, IsStarProjection (inner ℬ (e i) (e i) : ℬ) := fun i => (hproj i).1
  have hfpair : f i₁' = e i₁ + e i₂ := by simp [hfdef, hi₁']
  have hfelse : ∀ i : {i : ι // i ≠ i₂}, (i : ι) ≠ i₁ → f i = e (i : ι) := by
    intro i hi; simp [hfdef, hi]
  -- "$p_1$ and $p_2$ are projections with $p_1 + p_2 \leq 1$ and so by
  -- `orthogonal-tuple-of-projections` they are orthogonal" (**55XIII**)
  have htfae := orthogonal_tuple_of_projections_1
    (inner ℬ (e i₁) (e i₁) : ℬ) (inner ℬ (e i₂) (e i₂) : ℬ) (hpr i₁) (hpr i₂)
  have h12 : (inner ℬ (e i₁) (e i₁) : ℬ) * inner ℬ (e i₂) (e i₂) = 0 :=
    (htfae.out 3 0).mp hle
  have h21 : (inner ℬ (e i₂) (e i₂) : ℬ) * inner ℬ (e i₁) (e i₁) = 0 :=
    (htfae.out 3 1).mp hle
  have hsumproj :
      IsStarProjection ((inner ℬ (e i₁) (e i₁) : ℬ) + inner ℬ (e i₂) (e i₂)) :=
    (htfae.out 3 5).mp hle
  -- **149III** `mod-projelabs` in coefficient form: `⟨eᵢ,x⟩⟨eᵢ,eᵢ⟩ = ⟨eᵢ,x⟩`
  have hcoef : ∀ (i : ι) (x : X),
      (inner ℬ (e i) x : ℬ) * inner ℬ (e i) (e i) = inner ℬ (e i) x := by
    intro i x
    calc (inner ℬ (e i) x : ℬ) * inner ℬ (e i) (e i)
        = inner ℬ ((inner ℬ (e i) (e i) : ℬ) • e i) x := by
          rw [CStarModule.inner_op_smul_left, (hpr i).isSelfAdjoint.star_eq]
      _ = inner ℬ (e i) x := by rw [mod_projelabs (e i) (hpr i)]
  -- "$e_2 \langle e_1, x\rangle = e_2 p_2 \langle e_1, x\rangle = 0$"
  have hkill : ∀ i j : ι, (inner ℬ (e i) (e i) : ℬ) * inner ℬ (e j) (e j) = 0 →
      ∀ x : X, (inner ℬ (e i) x : ℬ) • e j = 0 := by
    intro i j hij x
    have h1 : (inner ℬ (e i) x : ℬ) * inner ℬ (e j) (e j) = 0 := by
      conv_lhs => rw [← hcoef i x]
      rw [mul_assoc, hij, mul_zero]
    calc (inner ℬ (e i) x : ℬ) • e j
        = (inner ℬ (e i) x : ℬ) • ((inner ℬ (e j) (e j) : ℬ) • e j) := by
          rw [mod_projelabs (e j) (hpr j)]
      _ = ((inner ℬ (e i) x : ℬ) * inner ℬ (e j) (e j)) • e j :=
          (op_mul_smul _ _ _).symm
      _ = 0 := by rw [h1, op_zero_smul]
  -- "$(e_1+e_2)\langle e_1+e_2,x\rangle = e_1\langle e_1,x\rangle
  --    + e_2 \langle e_2,x\rangle$"
  have hpairsum : ∀ x : X, (inner ℬ (e i₁ + e i₂) x : ℬ) • (e i₁ + e i₂)
      = (inner ℬ (e i₁) x : ℬ) • e i₁ + (inner ℬ (e i₂) x : ℬ) • e i₂ := by
    intro x
    rw [CStarModule.inner_add_left, op_add_smul, op_smul_add, op_smul_add,
      hkill i₁ i₂ h12 x, hkill i₂ i₁ h21 x, add_zero, zero_add]
  have hdiag : (inner ℬ (e i₁ + e i₂) (e i₁ + e i₂) : ℬ)
      = inner ℬ (e i₁) (e i₁) + inner ℬ (e i₂) (e i₂) := by
    rw [CStarModule.inner_add_left, CStarModule.inner_add_right,
      CStarModule.inner_add_right, horth i₁ i₂ hne, horth i₂ i₁ hne.symm]
    abel
  have hoff : ∀ j : ι, j ≠ i₁ → j ≠ i₂ →
      (inner ℬ (e i₁ + e i₂) (e j) : ℬ) = 0 ∧
      (inner ℬ (e j) (e i₁ + e i₂) : ℬ) = 0 := by
    intro j hj1 hj2
    refine ⟨?_, ?_⟩
    · rw [CStarModule.inner_add_left, horth i₁ j (Ne.symm hj1),
        horth i₂ j (Ne.symm hj2), add_zero]
    · rw [CStarModule.inner_add_right, horth j i₁ hj1, horth j i₂ hj2, add_zero]
  -- the reindexing `Finset {i // i ≠ i₂} → Finset ι`
  set g : Finset {i : ι // i ≠ i₂} → Finset ι :=
    fun s => if i₁' ∈ s then insert i₂ (s.image Subtype.val) else s.image Subtype.val
    with hgdef
  have hvalinj : Function.Injective (Subtype.val : {i : ι // i ≠ i₂} → ι) :=
    Subtype.val_injective
  have hi₂notmem : ∀ s : Finset {i : ι // i ≠ i₂}, i₂ ∉ s.image Subtype.val := by
    intro s hmem
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
    exact a.2 ha
  have hsplit : ∀ (v : {i : ι // i ≠ i₂} → X) (v' : ι → X),
      (∀ i : {i : ι // i ≠ i₂}, (i : ι) ≠ i₁ → v i = v' (i : ι)) →
      v i₁' = v' i₁ + v' i₂ →
      ∀ s : Finset {i : ι // i ≠ i₂}, ∑ i ∈ s, v i = ∑ j ∈ g s, v' j := by
    intro v v' hveq hvpair s
    by_cases hs : i₁' ∈ s
    · have hcong : ∀ i ∈ s.erase i₁', v i = v' (i : ι) := fun i hi =>
        hveq i fun hc => Finset.ne_of_mem_erase hi (Subtype.ext hc)
      rw [hgdef]
      simp only [if_pos hs]
      rw [Finset.sum_insert (hi₂notmem s),
        Finset.sum_image (fun a _ c _ h => hvalinj h),
        ← Finset.add_sum_erase s v hs,
        ← Finset.add_sum_erase s (fun i => v' (i : ι)) hs, hvpair,
        Finset.sum_congr rfl hcong]
      abel
    · have hcong : ∀ i ∈ s, v i = v' (i : ι) := by
        intro i hi
        refine hveq i fun hc => hs ?_
        have : i = i₁' := Subtype.ext hc
        rwa [← this]
      rw [hgdef]
      simp only [if_neg hs]
      rw [Finset.sum_image (fun a _ c _ h => hvalinj h)]
      exact Finset.sum_congr rfl hcong
  have hgtop : Tendsto g atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro t
    refine ⟨insert i₁' (t.subtype (fun j => j ≠ i₂)), fun s hs => ?_⟩
    have hmem : i₁' ∈ s := hs (Finset.mem_insert_self _ _)
    intro j hj
    rw [hgdef]
    simp only [if_pos hmem]
    by_cases hj2 : j = i₂
    · subst hj2; exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨j, hj2⟩, ?_, rfl⟩)
      exact hs (Finset.mem_insert_of_mem (Finset.mem_subtype.mpr hj))
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  -- "$E'$ is an orthogonal set"
  · intro i j hij
    by_cases hi : (i : ι) = i₁ <;> by_cases hj : (j : ι) = i₁
    · exact absurd (Subtype.ext (hi.trans hj.symm)) hij
    · rw [show f i = e i₁ + e i₂ by rw [hfdef]; simp [hi], hfelse j hj]
      exact (hoff (j : ι) hj j.2).1
    · rw [hfelse i hi, show f j = e i₁ + e i₂ by rw [hfdef]; simp [hj]]
      exact (hoff (i : ι) hi i.2).2
    · rw [hfelse i hi, hfelse j hj]
      exact horth _ _ fun hc => hij (Subtype.ext hc)
  -- "$\langle e_1+e_2, e_1+e_2\rangle = p_1 + p_2$ is a (non-zero) projection"
  · intro i
    by_cases hi : (i : ι) = i₁
    · rw [show f i = e i₁ + e i₂ by rw [hfdef]; simp [hi], hdiag]
      refine ⟨hsumproj, fun hzero => (hproj i₁).2 ?_⟩
      calc (inner ℬ (e i₁) (e i₁) : ℬ)
          = inner ℬ (e i₁) (e i₁) *
              (inner ℬ (e i₁) (e i₁) + inner ℬ (e i₂) (e i₂)) := by
            rw [mul_add, h12, add_zero, (hpr i₁).isIdempotentElem.eq]
        _ = 0 := by rw [hzero, mul_zero]
    · rw [hfelse i hi]; exact hproj _
  -- "$x = (e_1+e_2)\langle e_1+e_2,x\rangle + \sum_{e\in E} e\langle e,x\rangle$"
  · intro x ω
    have hkey : ∀ s : Finset {i : ι // i ≠ i₂},
        ∑ i ∈ s, (inner ℬ (f i) x : ℬ) • f i
          = ∑ j ∈ g s, (inner ℬ (e j) x : ℬ) • e j := by
      refine hsplit _ _ (fun i hi => by rw [hfelse i hi]) ?_
      rw [hfpair]; exact hpairsum x
    refine ((hexp x ω).comp hgtop).congr fun s => ?_
    simp only [Function.comp_apply, hkey s]
  -- "the second condition holds automatically as $E'$ is an orthonormal set"
  · intro b hb
    obtain ⟨M, hM⟩ := hb
    set b' : ι → ℬ := fun j => if h : j = i₂ then b i₁' else b ⟨j, h⟩ with hb'def
    have hb'val : ∀ i : {i : ι // i ≠ i₂}, b' (i : ι) = b i := by
      intro i; simp [hb'def, i.2]
    have hb'one : b' i₁ = b i₁' := by simp [hb'def, hne, hi₁']
    have hb'two : b' i₂ = b i₁' := by simp [hb'def]
    have himg : (t : Finset ι) → (t.subtype (fun j => j ≠ i₂)).image Subtype.val
        = t.erase i₂ := by
      intro t; ext j; simp [Finset.mem_erase, and_comm]
    have hsub : ∀ t : Finset ι, ∑ j ∈ t.erase i₂, b' j * star (b' j)
        = ∑ i ∈ t.subtype (fun j => j ≠ i₂), b i * star (b i) := by
      intro t
      rw [← himg t, Finset.sum_image (fun a _ c _ h => hvalinj h)]
      exact Finset.sum_congr rfl fun i _ => by rw [hb'val i]
    have hb'l2 : L2Summable ℬ b' := by
      refine ⟨M + ‖b i₁' * star (b i₁')‖, fun t => ?_⟩
      by_cases hi₂ : i₂ ∈ t
      · rw [← Finset.add_sum_erase t (fun j => b' j * star (b' j)) hi₂, hsub t,
          hb'two]
        calc ‖b i₁' * star (b i₁')
              + ∑ i ∈ t.subtype (fun j => j ≠ i₂), b i * star (b i)‖
            ≤ ‖b i₁' * star (b i₁')‖
              + ‖∑ i ∈ t.subtype (fun j => j ≠ i₂), b i * star (b i)‖ :=
              norm_add_le _ _
          _ ≤ ‖b i₁' * star (b i₁')‖ + M := by gcongr; exact hM _
          _ = M + ‖b i₁' * star (b i₁')‖ := add_comm _ _
      · rw [← Finset.erase_eq_of_notMem hi₂, hsub t]
        exact le_trans (hM _) (le_add_of_nonneg_right (norm_nonneg _))
    obtain ⟨x, hx⟩ := hl2 b' hb'l2
    refine ⟨x, fun ω => ?_⟩
    have hkey : ∀ s : Finset {i : ι // i ≠ i₂},
        ∑ i ∈ s, b i • f i = ∑ j ∈ g s, b' j • e j := by
      refine hsplit _ _ (fun i hi => by rw [hfelse i hi, hb'val i]) ?_
      rw [hfpair, hb'one, hb'two]
      exact op_smul_add _ _ _
    refine ((hx ω).comp hgtop).congr fun s => ?_
    simp only [Function.comp_apply, hkey s]

end L2

/-! ## Parsec 1620: comparison of projections and the normal form

**162I** (dils.tex:4708): introduction — nothing to formalize. -/

section NormalForm

variable {ℬ : Type u}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

variable (ℬ) in
/-- A von Neumann algebra is a **factor** when its centre is `ℂ1`
(**162II**). -/
def IsFactor : Prop :=
  ∀ z : ℬ, IsCentral ℬ z → ∃ c : ℂ, z = algebraMap ℂ ℬ c

/-- The Murray–von Neumann preorder `p ≲ q` on projections: `u* u = p` and
`u u* ≤ q` for some `u` (dils.tex:4708, recalled from vn.tex 83II). -/
def MvNLe (p q : ℬ) : Prop :=
  ∃ u : ℬ, star u * u = p ∧ u * star u ≤ q

/-- **162II** (`total-mv-order`, dils.tex:4717, Proposition): in a factor,
any two projections are comparable: `p ≲ q` or `q ≲ p`.

**162III** is the proof — not converted. -/
theorem total_mv_order [VonNeumannAlgebra ℬ] (hF : IsFactor ℬ) (p q : ℬ)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MvNLe p q ∨ MvNLe q p :=
  sorry

variable {X : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul ℬ X] [CStarModule ℬ X]

/-- **162IV** (`selfdual-normalish-form`, dils.tex:4747, Theorem): every
self-dual Hilbert ℬ-module over a factor `ℬ` is isomorphic to
`ℓ²((1)_{α∈κ})` for an infinite cardinal `κ`, or to `ℓ²((1,…,1,p))` for
some `n ∈ ℕ` and projection `p`.  Stated through bases (cf. **161II**):
`X` has an orthonormal basis `(eᵢ)` such that either `⟨eᵢ,eᵢ⟩ = 1` for all
`i`, or the basis is finite and `⟨eᵢ,eᵢ⟩ = 1` for all but (at most) one
index.

**162V**–**162VII** are the proof; **162VIII** (dils.tex:4908, discussion
of non-uniqueness of κ) — not converted. -/
theorem selfdual_normalish_form [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hF : IsFactor ℬ) (hX : SelfDual ℬ X) :
    ∃ (ι : Type v) (e : ι → X), IsONBasis ℬ e ∧
      ((∀ i, inner ℬ (e i) (e i) = 1) ∨
        (Finite ι ∧ ∃ i₀ : ι, ∀ i, i ≠ i₀ → inner ℬ (e i) (e i) = 1)) :=
  sorry

end NormalForm

/-! ## Parsec 1630: the completion is determined by its universal property

**163I** (dils.tex:4927): introduction; **163III** is the proof — not
converted. -/

section CompletionDefining

variable {ℬ : Type u} {V : Type v}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [AddCommGroup V] [Module ℂ V] [SMul ℬ V]

/-- **163II** (`selfdual-compl-defining`, dils.tex:4935, Proposition),
uniqueness half: two self-dual completions of the same 𝒷-module with
𝒷-valued inner product (each has the universal property by **151Ia**) are
isomorphic by a unique inner-product-preserving module isomorphism
commuting with the embeddings. -/
theorem selfdual_compl_defining_unique [VonNeumannAlgebra ℬ]
    (B : BInner ℬ V) (E₁ E₂ : SelfDualCompletion.{u, v, v} B) :
    ∃! U : E₁.X → E₂.X,
      (∃ C : ℝ, IsBoundedModuleMap (cstarBInner ℬ E₁.X)
        (cstarBInner ℬ E₂.X) C U) ∧
      Function.Bijective U ∧
      (∀ x y : E₁.X, inner ℬ (U x) (U y) = inner ℬ x y) ∧
      ∀ v : V, U (E₁.η v) = E₂.η v :=
  sorry

/-- **163II** (`selfdual-compl-defining`, dils.tex:4935, Proposition),
moreover-clause: if an inner-product-preserving module map `η : V → X`
into a self-dual Hilbert ℬ-module has the universal property (every
bounded module map `V → Y` into a self-dual `Y` factors uniquely through
`η`), then the image of `η` is ultranorm dense. -/
theorem selfdual_compl_defining_dense [VonNeumannAlgebra ℬ]
    (B : BInner ℬ V) {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [SMul ℬ X] [CStarModule ℬ X] [CompleteSpace X] (hX : SelfDual ℬ X)
    (η : V → X) (hadd : ∀ v w, η (v + w) = η v + η w)
    (hsmulc : ∀ (c : ℂ) v, η (c • v) = c • η v)
    (hsmul : ∀ (b : ℬ) v, η (b • v) = b • η v)
    (hinner : ∀ v w, inner ℬ (η v) (η w) = B.inner v w)
    (huniv : ∀ (Y : Type v) (_ : NormedAddCommGroup Y) (_ : NormedSpace ℂ Y)
      (_ : SMul ℬ Y) (_ : CStarModule ℬ Y) (_ : CompleteSpace Y),
      SelfDual ℬ Y → ∀ (C : ℝ) (T : V → Y),
        IsBoundedModuleMap B (cstarBInner ℬ Y) C T →
        ∃! T' : X → Y,
          (∃ C' : ℝ, IsBoundedModuleMap (cstarBInner ℬ X)
            (cstarBInner ℬ Y) C' T') ∧ ∀ v, T' (η v) = T v) :
    UnDense (inner ℬ) (Set.range η) :=
  sorry

end CompletionDefining

/-! ## The von Neumann algebra tensor product interface

NOTE(proc-dep): axiomatization of thesis A's tensor product of von Neumann
algebras (proc.tex 108II, label `tensor`), used by parsecs 1640–1670. -/

section VNTensor

variable {𝒜 ℬ 𝒞 : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]

variable (𝒜 ℬ) in
/-- An np-functional on `𝒞` is a *product functional* for a bilinear map
`t : 𝒜 × ℬ → 𝒞` when it is of the form `ω ⊗ ξ` on the image of `t`. -/
def IsProductFunctional (t : 𝒜 → ℬ → 𝒞) (Ω : NPFunctional 𝒞) : Prop :=
  ∃ (ω : NPFunctional 𝒜) (ξ : NPFunctional ℬ),
    ∀ (a : 𝒜) (b : ℬ), Ω (t a b) = ω a * ξ b

/-- The interface of the tensor product `𝒞 = 𝒜 ⊗ ℬ` of von Neumann
algebras (proc.tex 108II, `tensor`): an miu-bilinear map
`t : 𝒜 × ℬ → 𝒞` whose image generates `𝒞` as a von Neumann algebra and
whose product np-functionals are separating. -/
structure IsVNTensor (t : 𝒜 → ℬ → 𝒞) : Prop where
  add_left : ∀ (a a' : 𝒜) (b : ℬ), t (a + a') b = t a b + t a' b
  add_right : ∀ (a : 𝒜) (b b' : ℬ), t a (b + b') = t a b + t a b'
  smul_complex : ∀ (c : ℂ) (a : 𝒜) (b : ℬ), t (c • a) b = c • t a b
  mul : ∀ (a a' : 𝒜) (b b' : ℬ), t a b * t a' b' = t (a * a') (b * b')
  one : t 1 1 = 1
  star : ∀ (a : 𝒜) (b : ℬ), star (t a b) = t (star a) (star b)
  generates : wstar 𝒞 (Set.range fun p : 𝒜 × ℬ => t p.1 p.2) = ⊤
  separating : ∀ z : 𝒞, 0 ≤ z →
    (∀ Ω : NPFunctional 𝒞, IsProductFunctional 𝒜 ℬ t Ω → Ω z = 0) → z = 0

end VNTensor

/-! ## Parsec 1640: the self-dual exterior tensor product

**164I** (dils.tex:4987): introduction — nothing to formalize. -/

section ExtTensor

variable {𝒜 ℬ 𝒞 : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]
  {X Y : Type u}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul ℬ Y] [CStarModule ℬ Y]

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), the data:
a **self-dual exterior tensor product** of a self-dual Hilbert 𝒜-module
`X` and a self-dual Hilbert ℬ-module `Y` over the von Neumann tensor
product `𝒞 = 𝒜 ⊗ ℬ` (given by `t`): a self-dual Hilbert 𝒞-module `Z`
with a bilinear `η : X × Y → Z` satisfying
`η(xa, yb) = (a ⊗ b)·η(x,y)` and
`⟨η(x,y), η(x',y')⟩ = ⟨x,x'⟩ ⊗ ⟨y,y'⟩`, whose image spans an
ultranorm-dense submodule, and which is universal among bounded
`𝒜 ⊙ ℬ`-bilinear maps into self-dual Hilbert 𝒞-modules. -/
structure ExtTensor (t : 𝒜 → ℬ → 𝒞) (ht : IsVNTensor t)
    (X Y : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X]
    [CStarModule 𝒜 X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul ℬ Y]
    [CStarModule ℬ Y] : Type (u + 1) where
  /-- The carrier `X ⊗ Y`. -/
  Z : Type u
  [nacg : NormedAddCommGroup Z]
  [nsp : NormedSpace ℂ Z]
  [smul : SMul 𝒞 Z]
  [cstarMod : CStarModule 𝒞 Z]
  [complete : CompleteSpace Z]
  /-- `X ⊗ Y` is self dual. -/
  selfDual : SelfDual 𝒞 Z
  /-- The bilinear map `η(x, y) = x ⊗ y`. -/
  η : X → Y → Z
  η_add_left : ∀ (x x' : X) (y : Y), η (x + x') y = η x y + η x' y
  η_add_right : ∀ (x : X) (y y' : Y), η x (y + y') = η x y + η x y'
  η_smul_complex : ∀ (c : ℂ) (x : X) (y : Y), η (c • x) y = c • η x y
  /-- `η(xa, yb) = (a ⊗ b) η(x,y)` (mirrored). -/
  η_smul : ∀ (a : 𝒜) (b : ℬ) (x : X) (y : Y),
    η (a • x) (b • y) = t a b • η x y
  /-- `⟨x ⊗ y, x' ⊗ y'⟩ = ⟨x,x'⟩ ⊗ ⟨y,y'⟩`. -/
  η_inner : ∀ (x x' : X) (y y' : Y),
    inner 𝒞 (η x y) (η x' y') = t (inner 𝒜 x x') (inner ℬ y y')
  /-- Universal property: bounded `𝒜 ⊙ ℬ`-bilinear maps into self-dual
  Hilbert 𝒞-modules factor uniquely through `η`. -/
  univ : ∀ (W : Type u) (_ : NormedAddCommGroup W) (_ : NormedSpace ℂ W)
    (_ : SMul 𝒞 W) (_ : CStarModule 𝒞 W) (_ : CompleteSpace W),
    SelfDual 𝒞 W →
    ∀ T : X → Y → W,
      (∀ (x x' : X) (y : Y), T (x + x') y = T x y + T x' y) →
      (∀ (x : X) (y y' : Y), T x (y + y') = T x y + T x y') →
      (∀ (a : 𝒜) (b : ℬ) (x : X) (y : Y),
        T (a • x) (b • y) = t a b • T x y) →
      (∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
        ‖∑ i, T (x i) (y i)‖ ^ 2 ≤
          C * ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖) →
      ∃! T' : Z → W,
        (∃ C' : ℝ, IsBoundedModuleMap (cstarBInner 𝒞 Z) (cstarBInner 𝒞 W)
          C' T') ∧ ∀ (x : X) (y : Y), T' (η x y) = T x y

attribute [instance] ExtTensor.nacg ExtTensor.nsp ExtTensor.smul
  ExtTensor.cstarMod ExtTensor.complete

variable {t : 𝒜 → ℬ → 𝒞} {ht : IsVNTensor t}

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), existence:
for self-dual `X`, `Y` over von Neumann algebras the self-dual exterior
tensor product exists.

**164III**–**164VIII** (construction via `ℓ²((pᵢⱼ))` and its proof,
including `ext-tensor-dfn-eta`, `ext-tensor-preserves-inner-prod`,
injectivity of `η`, `ultranorm-dense-tensor-base`) are proof steps — not
converted separately. -/
theorem univprop_ext_tensor [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) :
    Nonempty (ExtTensor t ht X Y) :=
  sorry

section ExtTensorAux

variable [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ] [VonNeumannAlgebra 𝒞]
  [CompleteSpace X] [CompleteSpace Y]

/-- The Gram identity `‖∑ᵢ xᵢ ⊗ yᵢ‖² = ‖∑ᵢⱼ ⟨xᵢ,xⱼ⟩ ⊗ ⟨yᵢ,yⱼ⟩‖`, from
`ExtTensor.η_inner`.  (Auxiliary for parsecs 1640–1670.) -/
private theorem extTensor_gram (E : ExtTensor t ht X Y) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) :
    ‖∑ i, E.η (x i) (y i)‖ ^ 2
      = ‖∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j))‖ := by
  have hg : (inner 𝒞 (∑ i, E.η (x i) (y i)) (∑ i, E.η (x i) (y i)) : 𝒞)
      = ∑ i, ∑ j, t (inner 𝒜 (x i) (x j)) (inner ℬ (y i) (y j)) := by
    rw [CStarModule.inner_sum_left]
    exact Finset.sum_congr rfl fun i _ => by
      rw [CStarModule.inner_sum_right]
      exact Finset.sum_congr rfl fun j _ => E.η_inner _ _ _ _
  rw [← hg, CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞),
    Real.sq_sqrt (norm_nonneg _)]

/-- Auxiliary for parsecs 1640–1670: two bounded module maps out of a
self-dual exterior tensor product which agree on the elementary tensors
are equal.  This is the uniqueness half of the universal property
**164II**, and is the substitute — offered by the author himself in
`bsols.tex`, solution `hilbmod-tensor-ketbra` — for the ultranorm density
of the elementary tensors. -/
private theorem extTensor_map_ext (E : ExtTensor t ht X Y) {W : Type u}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [SMul 𝒞 W] [CStarModule 𝒞 W]
    [CompleteSpace W] (hW : SelfDual 𝒞 W) (C₁ C₂ : ℝ) (F G : E.Z → W)
    (hF : IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 W) C₁ F)
    (hG : IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 W) C₂ G)
    (hFG : ∀ (x : X) (y : Y), F (E.η x y) = G (E.η x y)) :
    F = G := by
  have hnormF : ∀ z : E.Z, ‖F z‖ ≤ C₁ * ‖z‖ := fun z => by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (F z),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) z]
    exact hF.bound z
  have huniv := E.univ W inferInstance inferInstance inferInstance
    inferInstance inferInstance hW (fun x y => F (E.η x y))
    (fun x x' y => by rw [E.η_add_left, hF.add])
    (fun x y y' => by rw [E.η_add_right, hF.add])
    (fun a b x y => by rw [E.η_smul, hF.smul])
    ⟨C₁ ^ 2, fun n x y => ?_⟩
  · exact huniv.unique ⟨⟨C₁, hF⟩, fun _ _ => rfl⟩
      ⟨⟨C₂, hG⟩, fun x y => (hFG x y).symm⟩
  · have hsum : ∑ i, F (E.η (x i) (y i)) = F (∑ i, E.η (x i) (y i)) :=
      (map_sum (AddMonoidHom.mk' F hF.add) _ _).symm
    rw [hsum, ← extTensor_gram E n x y]
    nlinarith [hnormF (∑ i, E.η (x i) (y i)),
      norm_nonneg (∑ i, E.η (x i) (y i)),
      norm_nonneg (F (∑ i, E.η (x i) (y i)))]

/-- Auxiliary for parsecs 1640–1670: a vector of `X ⊗ Y` orthogonal to
every elementary tensor is `0`.  (Via `extTensor_map_ext` applied to
`|w⟩⟨w|`.) -/
private theorem extTensor_sep (E : ExtTensor t ht X Y) (w : E.Z)
    (hw : ∀ (x : X) (y : Y), (inner 𝒞 (E.η x y) w : 𝒞) = 0) : w = 0 := by
  have hK : IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 E.Z)
      ‖mketbra 𝒞 w w‖ ⇑(mketbra 𝒞 w w) :=
    ⟨fun z z' => map_add _ z z', fun c z => map_smul _ c z,
      fun b z => by
        show (inner 𝒞 w (b • z) : 𝒞) • w = b • ((inner 𝒞 w z : 𝒞) • w)
        rw [CStarModule.inner_op_smul_right, op_mul_smul],
      fun z => by
        have h : ‖(mketbra 𝒞 w w) z‖ ≤ ‖mketbra 𝒞 w w‖ * ‖z‖ :=
          (mketbra 𝒞 w w).le_opNorm z
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞)
            ((mketbra 𝒞 w w) z),
          CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) z] at h
        exact h⟩
  have hZ : IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 E.Z) 0
      (fun _ : E.Z => (0 : E.Z)) :=
    ⟨fun _ _ => (add_zero _).symm, fun c _ => (smul_zero c).symm,
      fun b _ => (op_smul_zero b).symm,
      fun z => by
        show Real.sqrt ‖(inner 𝒞 (0 : E.Z) (0 : E.Z) : 𝒞)‖
          ≤ 0 * Real.sqrt ‖(inner 𝒞 z z : 𝒞)‖
        simp [CStarModule.inner_zero_left]⟩
  have hmap := extTensor_map_ext E E.selfDual _ _ _ _ hK hZ fun x y => by
    show (inner 𝒞 w (E.η x y) : 𝒞) • w = 0
    rw [← CStarModule.star_inner (E.η x y) w, hw x y, star_zero, op_zero_smul]
  have happ : (inner 𝒞 w w : 𝒞) • w = 0 := congrFun hmap w
  have hsa : star (inner 𝒞 w w : 𝒞) = inner 𝒞 w w := CStarModule.star_inner w w
  have h3 : (inner 𝒞 w w : 𝒞) * inner 𝒞 w w * inner 𝒞 w w = 0 := by
    have := congrArg (fun z : E.Z => (inner 𝒞 z z : 𝒞)) happ
    simpa [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
      hsa, mul_assoc] using this
  have h4 : (inner 𝒞 w w : 𝒞) * inner 𝒞 w w = 0 := by
    refine (CStarRing.star_mul_self_eq_zero_iff _).mp ?_
    calc star ((inner 𝒞 w w : 𝒞) * inner 𝒞 w w) * ((inner 𝒞 w w : 𝒞) * inner 𝒞 w w)
        = (inner 𝒞 w w : 𝒞) * (inner 𝒞 w w * inner 𝒞 w w * inner 𝒞 w w) := by
          rw [star_mul, hsa]; noncomm_ring
      _ = 0 := by rw [h3, mul_zero]
  refine (CStarModule.inner_self (A := 𝒞) (x := w)).mp ?_
  refine (CStarRing.star_mul_self_eq_zero_iff _).mp ?_
  rw [hsa]; exact h4

/-- The identity is a bounded module map (auxiliary). -/
private theorem isBoundedModuleMap_id {V : Type u} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [SMul 𝒞 V] [CStarModule 𝒞 V] :
    IsBoundedModuleMap (cstarBInner 𝒞 V) (cstarBInner 𝒞 V) 1
      (id : V → V) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun z => by
    show (cstarBInner 𝒞 V).norm z ≤ 1 * (cstarBInner 𝒞 V).norm z
    rw [one_mul]⟩

/-- Bounded module maps compose (auxiliary). -/
private theorem isBoundedModuleMap_comp {V₁ V₂ V₃ : Type u}
    [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [SMul 𝒞 V₁] [CStarModule 𝒞 V₁]
    [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [SMul 𝒞 V₂] [CStarModule 𝒞 V₂]
    [NormedAddCommGroup V₃] [NormedSpace ℂ V₃] [SMul 𝒞 V₃] [CStarModule 𝒞 V₃]
    {C₁ C₂ : ℝ} {F : V₁ → V₂} {G : V₂ → V₃}
    (hF : IsBoundedModuleMap (cstarBInner 𝒞 V₁) (cstarBInner 𝒞 V₂) C₁ F)
    (hG : IsBoundedModuleMap (cstarBInner 𝒞 V₂) (cstarBInner 𝒞 V₃) C₂ G) :
    IsBoundedModuleMap (cstarBInner 𝒞 V₁) (cstarBInner 𝒞 V₃) (|C₂| * |C₁|)
      (fun z => G (F z)) := by
  refine ⟨fun z z' => by rw [hF.add, hG.add],
    fun c z => by rw [hF.smul_complex, hG.smul_complex],
    fun b z => by rw [hF.smul, hG.smul], fun z => ?_⟩
  have h1 : ‖F z‖ ≤ C₁ * ‖z‖ := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (F z),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) z]
    exact hF.bound z
  have h2 : ‖G (F z)‖ ≤ C₂ * ‖F z‖ := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (G (F z)),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (F z)]
    exact hG.bound (F z)
  have hgoal : ‖G (F z)‖ ≤ |C₂| * |C₁| * ‖z‖ := by
    have hA : ‖F z‖ ≤ |C₁| * ‖z‖ :=
      h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    have hB : ‖G (F z)‖ ≤ |C₂| * ‖F z‖ :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    calc ‖G (F z)‖ ≤ |C₂| * ‖F z‖ := hB
      _ ≤ |C₂| * (|C₁| * ‖z‖) := mul_le_mul_of_nonneg_left hA (abs_nonneg _)
      _ = |C₂| * |C₁| * ‖z‖ := by ring
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (G (F z)),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) z] at hgoal
  exact hgoal

/-- Auxiliary for parsecs 1640–1670: a bounded 𝒞-linear functional on
`X ⊗ Y` vanishing on the elementary tensors is `0` (self-duality of
`X ⊗ Y` plus `extTensor_sep`). -/
private theorem extTensor_functional_ext (E : ExtTensor t ht X Y)
    (ψ : E.Z →ₗ[ℂ] 𝒞) (hmod : ∀ (b : 𝒞) (z : E.Z), ψ (b • z) = b * ψ z)
    (hbdd : ∃ C : ℝ, ∀ z : E.Z, ‖ψ z‖ ≤ C * ‖z‖)
    (hzero : ∀ (x : X) (y : Y), ψ (E.η x y) = 0) : ∀ z : E.Z, ψ z = 0 := by
  obtain ⟨p, hp⟩ := E.selfDual ψ hmod hbdd
  have hp0 : p = 0 := by
    refine extTensor_sep E p fun x y => ?_
    rw [← CStarModule.star_inner p (E.η x y), ← hp (E.η x y), hzero x y,
      star_zero]
  intro z
  rw [hp z, hp0, CStarModule.inner_zero_left]

/-- Auxiliary for **164IX**: two vector functionals `⟨a, U ·⟩` and `⟨b, ·⟩`
on `X ⊗ Y` (with `U` a bounded module map) which agree on the elementary
tensors agree everywhere. -/
private theorem extTensor_inner_diff_ext (E : ExtTensor t ht X Y)
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℂ W] [SMul 𝒞 W]
    [CStarModule 𝒞 W] (U : E.Z → W) (C : ℝ)
    (hU : IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 W) C U)
    (a : W) (b : E.Z)
    (hzero : ∀ (x : X) (y : Y),
      (inner 𝒞 a (U (E.η x y)) : 𝒞) = inner 𝒞 b (E.η x y)) :
    ∀ z : E.Z, (inner 𝒞 a (U z) : 𝒞) = inner 𝒞 b z := by
  have hUnorm : ∀ z : E.Z, ‖U z‖ ≤ |C| * ‖z‖ := fun z => by
    have h : ‖U z‖ ≤ C * ‖z‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) (U z),
        CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞) z]
      exact hU.bound z
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hψ := extTensor_functional_ext E
    { toFun := fun z => (inner 𝒞 a (U z) : 𝒞) - inner 𝒞 b z
      map_add' := fun z z' => by
        simp only [hU.add, CStarModule.inner_add_right]; abel
      map_smul' := fun c z => by
        simp only [hU.smul_complex, CStarModule.inner_smul_right_complex,
          RingHom.id_apply, smul_sub] }
    (fun b₀ z => by
      show (inner 𝒞 a (U (b₀ • z)) : 𝒞) - inner 𝒞 b (b₀ • z)
        = b₀ * ((inner 𝒞 a (U z) : 𝒞) - inner 𝒞 b z)
      rw [hU.smul, CStarModule.inner_op_smul_right,
        CStarModule.inner_op_smul_right, mul_sub])
    ⟨‖a‖ * |C| + ‖b‖, fun z => ?_⟩
    (fun x y => by
      show (inner 𝒞 a (U (E.η x y)) : 𝒞) - inner 𝒞 b (E.η x y) = 0
      rw [hzero x y, sub_self])
  · intro z
    have h : (inner 𝒞 a (U z) : 𝒞) - inner 𝒞 b z = 0 := hψ z
    exact sub_eq_zero.mp h
  · show ‖(inner 𝒞 a (U z) : 𝒞) - inner 𝒞 b z‖ ≤ (‖a‖ * |C| + ‖b‖) * ‖z‖
    calc ‖(inner 𝒞 a (U z) : 𝒞) - inner 𝒞 b z‖
        ≤ ‖(inner 𝒞 a (U z) : 𝒞)‖ + ‖(inner 𝒞 b z : 𝒞)‖ := norm_sub_le _ _
      _ ≤ ‖a‖ * ‖U z‖ + ‖b‖ * ‖z‖ := by
          gcongr <;> exact CStarModule.norm_inner_le _
      _ ≤ ‖a‖ * (|C| * ‖z‖) + ‖b‖ * ‖z‖ := by
          gcongr
          exact hUnorm z
      _ = (‖a‖ * |C| + ‖b‖) * ‖z‖ := by ring

end ExtTensorAux

/-- **164IX** (`ext-tensor-uniqueness`, dils.tex:5286, Uniqueness — stated
in **164II** as "up-to-isomorphism unique"): two self-dual exterior tensor
products are isomorphic by a unique inner-product-preserving module
isomorphism commuting with the embeddings. -/
theorem ext_tensor_uniqueness [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y)
    (E₁ E₂ : ExtTensor t ht X Y) :
    ∃! U : E₁.Z → E₂.Z,
      (∃ C : ℝ, IsBoundedModuleMap (cstarBInner 𝒞 E₁.Z)
        (cstarBInner 𝒞 E₂.Z) C U) ∧
      Function.Bijective U ∧
      (∀ z z' : E₁.Z, inner 𝒞 (U z) (U z') = inner 𝒞 z z') ∧
      ∀ (x : X) (y : Y), U (E₁.η x y) = E₂.η x y := by
  -- `η₂ : X × Y → E₂.Z` is itself an admissible datum for `E₁`'s universal
  -- property (the required bound is the Gram identity with `C = 1`), and
  -- symmetrically; the two induced maps are mutually inverse.
  obtain ⟨U, ⟨hUb, hUη⟩, -⟩ := E₁.univ E₂.Z inferInstance inferInstance
    inferInstance inferInstance inferInstance E₂.selfDual E₂.η
    E₂.η_add_left E₂.η_add_right E₂.η_smul
    ⟨1, fun n x y => by rw [extTensor_gram E₂ n x y, one_mul]⟩
  obtain ⟨V, ⟨hVb, hVη⟩, -⟩ := E₂.univ E₁.Z inferInstance inferInstance
    inferInstance inferInstance inferInstance E₁.selfDual E₁.η
    E₁.η_add_left E₁.η_add_right E₁.η_smul
    ⟨1, fun n x y => by rw [extTensor_gram E₁ n x y, one_mul]⟩
  obtain ⟨CU, hCU⟩ := hUb
  obtain ⟨CV, hCV⟩ := hVb
  have hVU : (fun z => V (U z)) = (id : E₁.Z → E₁.Z) :=
    extTensor_map_ext E₁ E₁.selfDual _ 1 _ _
      (isBoundedModuleMap_comp hCU hCV) isBoundedModuleMap_id
      fun x y => by rw [hUη, hVη]; rfl
  have hUV : (fun z => U (V z)) = (id : E₂.Z → E₂.Z) :=
    extTensor_map_ext E₂ E₂.selfDual _ 1 _ _
      (isBoundedModuleMap_comp hCV hCU) isBoundedModuleMap_id
      fun x y => by rw [hVη, hUη]; rfl
  -- inner products: first against elementary tensors, then in general
  have hstep1 : ∀ (x₀ : X) (y₀ : Y) (z : E₁.Z),
      (inner 𝒞 (E₂.η x₀ y₀) (U z) : 𝒞) = inner 𝒞 (E₁.η x₀ y₀) z := by
    intro x₀ y₀
    refine extTensor_inner_diff_ext E₁ U CU hCU _ _ fun x y => ?_
    rw [hUη, E₂.η_inner, E₁.η_inner]
  have hstep2 : ∀ z' z : E₁.Z,
      (inner 𝒞 (U z') (U z) : 𝒞) = inner 𝒞 z' z := by
    intro z'
    refine extTensor_inner_diff_ext E₁ U CU hCU _ _ fun x y => ?_
    rw [hUη, ← CStarModule.star_inner (E₂.η x y) (U z'), hstep1 x y z',
      CStarModule.star_inner]
  refine ⟨U, ⟨⟨CU, hCU⟩, ?_, fun z z' => hstep2 z z', hUη⟩, ?_⟩
  · exact Function.bijective_iff_has_inverse.mpr
      ⟨V, fun z => congrFun hVU z, fun z => congrFun hUV z⟩
  · rintro U' ⟨⟨CU', hCU'⟩, -, -, hU'η⟩
    exact extTensor_map_ext E₁ E₂.selfDual _ _ _ _ hCU' hCU
      fun x y => by rw [hU'η, hUη]

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), property 1:
the (span of the) image of `η` is ultranorm dense in `X ⊗ Y`. -/
theorem ext_tensor_dense [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y) :
    UnDense (inner 𝒞)
      {z : E.Z | ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
        z = ∑ i, E.η (x i) (y i)} :=
  sorry

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), property 2a:
for orthonormal bases `(eᵢ)` of `X` and `(dⱼ)` of `Y`, the family
`(eᵢ ⊗ dⱼ)` is an orthonormal basis of `X ⊗ Y`. -/
theorem ext_tensor_basis [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    {ι κ : Type u} (e : ι → X) (d : κ → Y)
    (he : IsONBasis 𝒜 e) (hd : IsONBasis ℬ d) :
    IsONBasis 𝒞 fun p : ι × κ => E.η (e p.1) (d p.2) :=
  sorry

/-- **164II** (`univprop-ext-tensor`, dils.tex:5024, Theorem), property 2b:
the linear span of the `|(eᵢa) ⊗ (dⱼb)⟩⟨e_k ⊗ d_l|` is ultraweakly dense
in `𝒞ᵃ(X ⊗ Y)`.

**164X**–**164XI** are the proof; **164XII** (Examples) — not
converted. -/
theorem ext_tensor_ketbra_dense [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    {ι κ : Type u} (e : ι → X) (d : κ → Y)
    (he : IsONBasis 𝒜 e) (hd : IsONBasis ℬ d) (T : Ba 𝒞 E.Z) :
    ∃ approx : Finset (ι × κ) → Ba 𝒞 E.Z,
      (∀ s, approx s ∈ Submodule.span ℂ
        {S : Ba 𝒞 E.Z | ∃ (i k : ι) (j l : κ) (a : 𝒜) (b : ℬ),
          S.1 = mketbra 𝒞 (E.η (a • e i) (b • d j)) (E.η (e k) (d l))}) ∧
      UWTendsto approx atTop T :=
  sorry

/-! ## Parsec 1650: 𝒷ᵃ(X) ⊗ 𝒷ᵃ(Y) ≅ 𝒷ᵃ(X ⊗ Y)

**165I** (dils.tex:5407): introduction; **165II** (Setting) — nothing to
formalize. -/

/-- **165III** (`dfn-tensor-of-hilbmod-maps`, dils.tex:5426, Proposition):
for `S ∈ 𝒜ᵃ(X)` and `T ∈ ℬᵃ(Y)` there is a unique operator
`S ⊗ T ∈ 𝒞ᵃ(X ⊗ Y)` with `(S ⊗ T)(x ⊗ y) = (Sx) ⊗ (Ty)`.

**165IV** is the proof — not converted. -/
theorem dfn_tensor_of_hilbmod_maps [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] [VonNeumannAlgebra 𝒞] [CompleteSpace X]
    [CompleteSpace Y] (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y)
    (E : ExtTensor t ht X Y) (S : Ba 𝒜 X) (T : Ba ℬ Y) :
    ∃! R : Ba 𝒞 E.Z,
      ∀ (x : X) (y : Y), R.1 (E.η x y) = E.η (S.1 x) (T.1 y) :=
  sorry

/-- **165V** (`hilbmod-tensor-ketbra`, dils.tex:5506, Exercise): the rules
for `⊗` of module operators: (1) `|x₁⟩⟨x₂| ⊗ |y₁⟩⟨y₂| = |x₁⊗y₁⟩⟨x₂⊗y₂|`;
(2) `1 ⊗ 1 = 1`; (3) `(S ⊗ T)(S' ⊗ T') = SS' ⊗ TT'`;
(4) `(S ⊗ T)* = S* ⊗ T*`.  (Stated for operators characterized by their
values on elementary tensors, as in **165III**.) -/
theorem hilbmod_tensor_ketbra [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    (S S' : Ba 𝒜 X) (T T' : Ba ℬ Y) (R R' R'' : Ba 𝒞 E.Z)
    (hR : ∀ x y, R.1 (E.η x y) = E.η (S.1 x) (T.1 y))
    (hR' : ∀ x y, R'.1 (E.η x y) = E.η (S'.1 x) (T'.1 y))
    (hR'' : ∀ x y, R''.1 (E.η x y) = E.η ((S * S').1 x) ((T * T').1 y)) :
    (∀ (x₁ x₂ : X) (y₁ y₂ : Y),
      (∀ x y, R.1 (E.η x y) =
          E.η ((mketbra 𝒜 x₁ x₂ : X →L[ℂ] X) x) ((mketbra ℬ y₁ y₂) y)) →
        R.1 = mketbra 𝒞 (E.η x₁ y₁) (E.η x₂ y₂)) ∧
    ((∀ x y, R.1 (E.η x y) = E.η x y) → R = 1) ∧
    R * R' = R'' ∧
    (∀ x y, (star R).1 (E.η x y) = E.η ((star S).1 x) ((star T).1 y)) := by
  -- `bsols.tex`, solution `hilbmod-tensor-ketbra`.  Of the two routes the
  -- author offers ("either by appealing to the defining universal property
  -- of `X ⊗ Y` or by … ultranorm density") we take the first, since the
  -- density statement **164II**.1 (`ext_tensor_dense`) is still `sorry`.
  -- Every `R ∈ 𝒞ᵃ(X ⊗ Y)` is a bounded module map.
  have hbdd : ∀ R₀ : Ba 𝒞 E.Z, ∃ C : ℝ,
      IsBoundedModuleMap (cstarBInner 𝒞 E.Z) (cstarBInner 𝒞 E.Z) C ⇑R₀.1 := by
    intro R₀
    obtain ⟨-, -, hRm⟩ := moduleAdjointable_linear (𝒜 := 𝒞) ⇑R₀.1 R₀.2
    refine ⟨‖R₀.1‖, ⟨fun x y => map_add _ x y, fun c x => map_smul _ c x,
      hRm, fun x => ?_⟩⟩
    change Real.sqrt ‖(inner 𝒞 (R₀.1 x) (R₀.1 x) : 𝒞)‖
      ≤ ‖R₀.1‖ * Real.sqrt ‖(inner 𝒞 x x : 𝒞)‖
    rw [← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞),
      ← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒞)]
    exact R₀.1.le_opNorm x
  -- "This is sufficient to show …": operators agreeing on the elementary
  -- tensors agree, by the uniqueness half of the universal property.
  have hunique : ∀ R₁ R₂ : Ba 𝒞 E.Z,
      (∀ (x : X) (y : Y), R₁.1 (E.η x y) = R₂.1 (E.η x y)) → R₁ = R₂ := by
    intro R₁ R₂ hagree
    obtain ⟨C₁, hC₁⟩ := hbdd R₁
    obtain ⟨C₂, hC₂⟩ := hbdd R₂
    exact Subtype.ext (DFunLike.coe_injective
      (extTensor_map_ext E E.selfDual C₁ C₂ _ _ hC₁ hC₂ hagree))
  -- vector separation: a vector orthogonal to every elementary tensor is `0`
  have hsep : ∀ w : E.Z, (∀ (x : X) (y : Y), (inner 𝒞 (E.η x y) w : 𝒞) = 0) →
      w = 0 := extTensor_sep E
  refine ⟨?_, ?_, ?_, ?_⟩
  -- (1) `|x₁⟩⟨x₂| ⊗ |y₁⟩⟨y₂| = |x₁⊗y₁⟩⟨x₂⊗y₂|`
  · intro x₁ x₂ y₁ y₂ hRk
    have hK : ModuleAdjointable 𝒞 ⇑(mketbra 𝒞 (E.η x₁ y₁) (E.η x₂ y₂)) :=
      ⟨_, mketbra_adjointable 𝒞 _ _⟩
    have := hunique R ⟨mketbra 𝒞 (E.η x₁ y₁) (E.η x₂ y₂), hK⟩ fun x y => by
      rw [hRk x y]
      show E.η ((inner 𝒜 x₂ x : 𝒜) • x₁) ((inner ℬ y₂ y : ℬ) • y₁)
        = (inner 𝒞 (E.η x₂ y₂) (E.η x y) : 𝒞) • E.η x₁ y₁
      rw [E.η_smul, E.η_inner]
    rw [this]
  -- (2) `1 ⊗ 1 = 1`
  · intro h1
    exact hunique R 1 fun x y => h1 x y
  -- (3) `(S ⊗ T)(S' ⊗ T') = SS' ⊗ TT'`
  · refine hunique _ _ fun x y => ?_
    show R.1 (R'.1 (E.η x y)) = _
    rw [hR' x y, hR (S'.1 x) (T'.1 y), hR'' x y]
    rfl
  -- (4) `(S ⊗ T)* = S* ⊗ T*`
  · intro x y
    have hRadj : ModuleAdjointTo 𝒞 (⇑R.1 : E.Z → E.Z)
      ⇑((star R : Ba 𝒞 E.Z)).1 := baSubalgebra_star_spec R
    have hSadj : ModuleAdjointTo 𝒜 (⇑S.1 : X → X)
      ⇑((star S : Ba 𝒜 X)).1 := baSubalgebra_star_spec S
    have hTadj : ModuleAdjointTo ℬ (⇑T.1 : Y → Y)
      ⇑((star T : Ba ℬ Y)).1 := baSubalgebra_star_spec T
    refine sub_eq_zero.mp (hsep _ fun x' y' => ?_)
    rw [CStarModule.inner_sub_right, ← hRadj (E.η x' y') (E.η x y), hR x' y',
      E.η_inner, E.η_inner, hSadj x' x, hTadj y' y, sub_self]

/-- **165VI** (`ba-ext-tensor-pres`, dils.tex:5531, Theorem): there is an
nmiu-isomorphism `𝒜ᵃ(X) ⊗ ℬᵃ(Y) ≅ 𝒞ᵃ(X ⊗ Y)` sending `S ⊗ T` to
`S ⊗ T`; stated as: the bilinear map `Θ(S,T) = S ⊗ T` exhibits
`𝒞ᵃ(X ⊗ Y)` as the von Neumann tensor product of `𝒜ᵃ(X)` and `ℬᵃ(Y)`.

**165VII**–**165X** are the proof — not converted. -/
theorem ba_ext_tensor_pres [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    (Θ : Ba 𝒜 X → Ba ℬ Y → Ba 𝒞 E.Z)
    (hΘ : ∀ (S : Ba 𝒜 X) (T : Ba ℬ Y) (x : X) (y : Y),
      (Θ S T).1 (E.η x y) = E.η (S.1 x) (T.1 y)) :
    IsVNTensor Θ :=
  sorry

/-! ## Parsec 1660: ultranorm continuity of the exterior tensor product

**166I** (dils.tex:5625): introduction; **166III**, **166V**, **166VII**
are proofs — not converted. -/

/-- **166II** (`ultranorm-continuity-ext-tensor`, dils.tex:5630, Lemma): if
`x_α → x` and `y_α → y` ultranorm for norm-bounded nets, then
`x_α ⊗ y_α → x ⊗ y` ultranorm. -/
theorem ultranorm_continuity_ext_tensor [VonNeumannAlgebra 𝒜]
    [VonNeumannAlgebra ℬ] [VonNeumannAlgebra 𝒞] [CompleteSpace X]
    [CompleteSpace Y] (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y)
    (E : ExtTensor t ht X Y) {ι : Type u} {l : Filter ι}
    (x : ι → X) (x₀ : X) (y : ι → Y) (y₀ : Y)
    (hxb : ∃ M : ℝ, ∀ i, ‖x i‖ ≤ M) (hyb : ∃ M : ℝ, ∀ i, ‖y i‖ ≤ M)
    (hx : UnTendsto (inner 𝒜) x l x₀) (hy : UnTendsto (inner ℬ) y l y₀) :
    UnTendsto (inner 𝒞) (fun i => E.η (x i) (y i)) l (E.η x₀ y₀) :=
  sorry

/-- **166IV** (`exttensor-dense-subsets`, dils.tex:5669, Lemma): for
ultranorm-dense submodules `U ⊆ X` and `V ⊆ Y`, the linear span of
`U ⊗ V = {u ⊗ v}` is ultranorm dense in `X ⊗ Y`. -/
theorem exttensor_dense_subsets [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    [VonNeumannAlgebra 𝒞] [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒜 X) (hY : SelfDual ℬ Y) (E : ExtTensor t ht X Y)
    (U : Set X) (V : Set Y)
    (hU : UnDense (inner 𝒜) U) (hV : UnDense (inner ℬ) V)
    (hUsub : ∀ u ∈ U, ∀ u' ∈ U, u + u' ∈ U)
    (hUsmul : ∀ (a : 𝒜), ∀ u ∈ U, a • u ∈ U)
    (hVsub : ∀ v ∈ V, ∀ v' ∈ V, v + v' ∈ V)
    (hVsmul : ∀ (b : ℬ), ∀ v ∈ V, b • v ∈ V) :
    UnDense (inner 𝒞)
      {z : E.Z | ∃ (n : ℕ) (u : Fin n → X) (v : Fin n → Y),
        (∀ i, u i ∈ U) ∧ (∀ i, v i ∈ V) ∧ z = ∑ i, E.η (u i) (v i)} :=
  sorry

end ExtTensor

/-- **166VI** (`dilationspace-dense-subset`, dils.tex:5695, Lemma): for an
ncp-map `φ : 𝒜 → ℬ` between von Neumann algebras with ultrastrongly dense
∗-subalgebras `𝒜' ⊆ 𝒜`, `ℬ' ⊆ ℬ`, the linear span of
`{a ⊗ b : a ∈ 𝒜', b ∈ ℬ'}` is ultranorm dense in `𝒜 ⊗_φ ℬ`. -/
theorem dilationspace_dense_subset {𝒜 ℬ : Type u}
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
    (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ)
    (A' : StarSubalgebra ℂ 𝒜) (B' : StarSubalgebra ℂ ℬ)
    (hA : UnDense (mulInner 𝒜) (A' : Set 𝒜))
    (hB : UnDense (mulInner ℬ) (B' : Set ℬ)) :
    UnDense (inner ℬ)
      {z : M.X | ∃ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ),
        (∀ i, a i ∈ A') ∧ (∀ i, b i ∈ B') ∧
        z = ∑ i, M.tprod (a i) (b i)} :=
  sorry

/-! ## Parsec 1670: the tensor product of Paschke dilations -/

section PaschkeTensor

variable {𝒜₁ 𝒜₂ 𝒜₁₂ ℬ₁ ℬ₂ ℬ₁₂ P₁₂ : Type u}
  [CStarAlgebra 𝒜₁] [PartialOrder 𝒜₁] [StarOrderedRing 𝒜₁]
  [CStarAlgebra 𝒜₂] [PartialOrder 𝒜₂] [StarOrderedRing 𝒜₂]
  [CStarAlgebra 𝒜₁₂] [PartialOrder 𝒜₁₂] [StarOrderedRing 𝒜₁₂]
  [CStarAlgebra ℬ₁] [PartialOrder ℬ₁] [StarOrderedRing ℬ₁]
  [CStarAlgebra ℬ₂] [PartialOrder ℬ₂] [StarOrderedRing ℬ₂]
  [CStarAlgebra ℬ₁₂] [PartialOrder ℬ₁₂] [StarOrderedRing ℬ₁₂]
  [CStarAlgebra P₁₂] [PartialOrder P₁₂] [StarOrderedRing P₁₂]

/-- **167I** (`paschke-tensor`, dils.tex:5746, Theorem), main claim: if
`(𝒫ᵢ, ϱᵢ, hᵢ)` is a Paschke dilation of the ncp-map `φᵢ : 𝒜ᵢ → ℬᵢ`
(i = 1,2), then `(𝒫₁ ⊗ 𝒫₂, ϱ₁ ⊗ ϱ₂, h₁ ⊗ h₂)` is a Paschke dilation of
`φ₁ ⊗ φ₂`.  (The tensor products of algebras are given through the
`IsVNTensor` interface, and the tensor products of maps through their
characterizing values on elementary tensors.)

**167II**–**167VI** are the proof — not converted. -/
theorem paschke_tensor
    (tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂) (htA : IsVNTensor tA)
    (tB : ℬ₁ → ℬ₂ → ℬ₁₂) (htB : IsVNTensor tB)
    (φ₁ : NCPMap 𝒜₁ ℬ₁) (φ₂ : NCPMap 𝒜₂ ℬ₂)
    (D₁ : PaschkeTriple 𝒜₁ ℬ₁) (D₂ : PaschkeTriple 𝒜₂ ℬ₂)
    (h₁ : IsPaschkeDilationOf D₁ ⇑φ₁) (h₂ : IsPaschkeDilationOf D₂ ⇑φ₂)
    (tP : D₁.P → D₂.P → P₁₂) (htP : IsVNTensor tP)
    (vnP : VonNeumannAlgebra P₁₂)
    (Φ : NCPMap 𝒜₁₂ ℬ₁₂)
    (hΦ : ∀ (a₁ : 𝒜₁) (a₂ : 𝒜₂), Φ (tA a₁ a₂) = tB (φ₁ a₁) (φ₂ a₂))
    (R : NMIUMap 𝒜₁₂ P₁₂)
    (hR : ∀ (a₁ : 𝒜₁) (a₂ : 𝒜₂), R (tA a₁ a₂) = tP (D₁.ρ a₁) (D₂.ρ a₂))
    (H : NCPMap P₁₂ ℬ₁₂)
    (hH : ∀ (c₁ : D₁.P) (c₂ : D₂.P),
      H (tP c₁ c₂) = tB (D₁.h c₁) (D₂.h c₂)) :
    IsPaschkeDilationOf ⟨P₁₂, vnP, R, H⟩ ⇑Φ :=
  sorry

/-- **167I** (`paschke-tensor`, dils.tex:5746, Theorem), furthermore-claim
(dils.tex:5754): the dilation spaces satisfy
`(𝒜₁ ⊗_{φ₁} ℬ₁) ⊗ (𝒜₂ ⊗_{φ₂} ℬ₂) ≅ (𝒜₁ ⊗ 𝒜₂) ⊗_{φ₁⊗φ₂} (ℬ₁ ⊗ ℬ₂)`,
via the map determined on elementary tensors. -/
theorem paschke_tensor_module
    [VonNeumannAlgebra 𝒜₁] [VonNeumannAlgebra 𝒜₂] [VonNeumannAlgebra 𝒜₁₂]
    [VonNeumannAlgebra ℬ₁] [VonNeumannAlgebra ℬ₂] [VonNeumannAlgebra ℬ₁₂]
    (tA : 𝒜₁ → 𝒜₂ → 𝒜₁₂) (htA : IsVNTensor tA)
    (tB : ℬ₁ → ℬ₂ → ℬ₁₂) (htB : IsVNTensor tB)
    (φ₁ : NCPMap 𝒜₁ ℬ₁) (φ₂ : NCPMap 𝒜₂ ℬ₂)
    (M₁ : PaschkeModule φ₁) (M₂ : PaschkeModule φ₂)
    (Φ : NCPMap 𝒜₁₂ ℬ₁₂)
    (hΦ : ∀ (a₁ : 𝒜₁) (a₂ : 𝒜₂), Φ (tA a₁ a₂) = tB (φ₁ a₁) (φ₂ a₂))
    (M₁₂ : PaschkeModule Φ)
    (E : ExtTensor tB htB M₁.X M₂.X) :
    ∃ U : E.Z → M₁₂.X,
      (∃ C : ℝ, IsBoundedModuleMap (cstarBInner ℬ₁₂ E.Z)
        (cstarBInner ℬ₁₂ M₁₂.X) C U) ∧
      Function.Bijective U ∧
      (∀ z z' : E.Z, inner ℬ₁₂ (U z) (U z') = inner ℬ₁₂ z z') ∧
      ∀ (a₁ : 𝒜₁) (b₁ : ℬ₁) (a₂ : 𝒜₂) (b₂ : ℬ₂),
        U (E.η (M₁.tprod a₁ b₁) (M₂.tprod a₂ b₂)) =
          M₁₂.tprod (tA a₁ a₂) (tB b₁ b₂) :=
  sorry

end PaschkeTensor

end Theses.B.Dils
