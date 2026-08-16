/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 2–1266.

  parsec 1350:  GNS' and Stinespring's theorem (statements)
  parsec 1360:  completion of an inner product space into a Hilbert space
  parsec 1370:  proof of Stinespring's theorem (135IV and its corollaries are
                proved here, where the thesis proves them, since the argument
                needs 136II from parsec 1360)
  parsec 1380:  nmiu-maps between type I factors, Kraus decomposition,
                essential uniqueness of purification
  parsec 1390:  normal Stinespring dilations, their universal property
  parsec 1400:  Paschke dilations: definition, Stinespring is Paschke,
                uniqueness, basic properties

Statements only; every proof is `sorry`.  See CONVENTIONS.md for the
numbering (**135II** = parsec 1350, point 20) and naming conventions.

Conventions specific to this file: all von Neumann algebras and Hilbert
spaces live in a single universe `u`; the ncp-maps `φ : 𝒜 → B(H)` of the
thesis are represented either by a bare linear map plus
`IsCompletelyPositiveMap`/`PreservesDirSups` (following
`Theses.A.CStar.Matrices`) or by the bundled `Theses.NCPMap`;
`ad_V = conjOperator V` is from `Theses.A.CStar.Matrices`.
-/
import Theses.Common
import Theses.A.CStar.Matrices
import Theses.A.VN.Projections

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u v

namespace Theses.B.Dils

/-! ## Parsec 1350: GNS' and Stinespring

**135I** (dils.tex:5): introduction — nothing to formalize. -/

section GNSStinespring

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **135II** (`dils-gns`, dils.tex:15, Theorem (GNS')): for each pu-map
`ω : 𝒜 → ℂ` from a C*-algebra `𝒜` there is a Hilbert space `ℋ`, an miu-map
`ϱ : 𝒜 → B(ℋ)` and a vector `x ∈ ℋ` such that `ω = h ∘ ϱ` where
`h(T) = ⟪x, Tx⟫`. -/
theorem dils_gns (ω : 𝒜 →ₗ[ℂ] ℂ) (hp : IsPositiveMap ω) (hu : ω 1 = 1) :
    ∃ (ℋ : Type u) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (ϱ : MIUMap 𝒜 (ℋ →L[ℂ] ℋ)) (x : ℋ),
      ∀ a : 𝒜, ω a = ⟪x, ϱ a x⟫ := by
  -- The thesis defers the proof of GNS' to the proof of Stinespring's theorem
  -- (dils.tex:35, dils.tex:586); the construction for `ℋ = ℂ` is Mathlib's
  -- `PositiveLinearMap.gnsStarAlgHom`, i.e. the completion of `𝒜` under
  -- `[a,b] = ω(a* b)`, with cyclic vector the image of `1`.
  set f : 𝒜 →ₚ[ℂ] ℂ :=
    { toLinearMap := ω
      monotone' := fun x y hxy => by
        have h := hp (y - x) (sub_nonneg.mpr hxy)
        rw [map_sub] at h
        exact sub_nonneg.mp h } with hf
  refine ⟨f.GNS, inferInstance, inferInstance, inferInstance, f.gnsStarAlgHom,
    ((f.toPreGNS 1 : f.PreGNS) : f.GNS), fun a => ?_⟩
  show (ω a : ℂ) = ⟪((f.toPreGNS 1 : f.PreGNS) : f.GNS),
    f.gnsStarAlgHom a ((f.toPreGNS 1 : f.PreGNS) : f.GNS)⟫
  simp [PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.gnsNonUnitalStarAlgHom_apply,
    UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]
  rfl

/-! **135IV** (`stinespring-theorem`, dils.tex:37) — Stinespring's theorem
itself — is stated *and proved* in parsec 1370 below, where the thesis proves
it: Lean wants a theorem's proof at the point of its statement, and the proof
needs **136II** of parsec 1360. -/

end GNSStinespring

/-! ## Parsec 1360: completion into a Hilbert space

**136I** (dils.tex:218): introduction — nothing to formalize.
**136III**–**136VII** are the proof of **136II** — not converted. -/

/-- **136II** (`prop-complete-into-hilbert-space`, dils.tex:238,
Proposition): let `V` be a complex vector space with a (not necessarily
definite) inner product, here a positive conjugate-symmetric sesquilinear
form `B`.  There is a Hilbert space `ℋ` and a bounded (automatic here)
linear map `η : V → ℋ` with `B v w = ⟪η v, η w⟫` and dense image.
(Cf. `inner_product_completion`, cstar.tex 30V, which assumes definiteness.) -/
theorem prop_complete_into_hilbert_space (V : Type v) [AddCommGroup V]
    [Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hsymm : ∀ v w : V, B w v = starRingEnd ℂ (B v w))
    (hpos : ∀ v : V, 0 ≤ (B v v).re) :
    ∃ (ℋ : Type v) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (η : V →ₗ[ℂ] ℋ),
      (∀ v w : V, (⟪η v, η w⟫ : ℂ) = B v w) ∧ DenseRange η := by
  -- The author's proof (dils.tex:250) builds `ℋ` by hand from fast Cauchy
  -- sequences, i.e. re-develops the metric completion; we instead use
  -- Mathlib's: `B` makes `V` a *semi*-inner-product space, its separation
  -- quotient is an inner product space, and its completion is a Hilbert
  -- space.  (Divergence (2): the same construction, taken off the shelf.)
  let core : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => (hsymm y x).symm
      re_inner_nonneg := hpos
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  let _ : SeminormedAddCommGroup V :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ) (F := V) (c := core)
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore core
  refine ⟨UniformSpace.Completion (SeparationQuotient V), inferInstance, inferInstance,
    inferInstance,
    ((UniformSpace.Completion.toComplL : SeparationQuotient V →L[ℂ]
        UniformSpace.Completion (SeparationQuotient V)).comp
      (SeparationQuotient.mkCLM ℂ V)).toLinearMap, fun v w => ?_, ?_⟩
  · change (⟪((SeparationQuotient.mk v : SeparationQuotient V) :
        UniformSpace.Completion (SeparationQuotient V)),
      ((SeparationQuotient.mk w : SeparationQuotient V) :
        UniformSpace.Completion (SeparationQuotient V))⟫ : ℂ) = B v w
    rw [UniformSpace.Completion.inner_coe, SeparationQuotient.inner_mk_mk]
    rfl
  · exact UniformSpace.Completion.denseRange_coe.comp
      SeparationQuotient.surjective_mk.denseRange
      (UniformSpace.Completion.continuous_coe _)

/-! ## Parsec 1370: proof of Stinespring's theorem

**137I**–**137VII** (dils.tex:397–585) are the proof of **135IV**
(`dils-proof-stinespring` and its sub-points, including the extension lemma
`stinespring-extend-operator`); that proof is transcribed in this section, with
`stinespring-extend-operator` supplied by `LinearMap.extendOfNorm`.
**137VIII** (dils.tex:586, Remark) — not converted; note the Lean development
does *not* follow it, deriving 135II downstream from Mathlib's GNS rather than
using GNS inside the proof of 135IV. -/

section StinespringProof

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The sesquilinear form `[a ⊗ x, b ⊗ y] = ⟪x, φ(a*b) y⟫` on `𝒜 ⊙ ℋ`. -/
private noncomputable def stForm (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) :
    TensorProduct ℂ 𝒜 H →ₗ⋆[ℂ] TensorProduct ℂ 𝒜 H →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun x => TensorProduct.lift
            (LinearMap.mk₂ ℂ (fun (b : 𝒜) (y : H) => (⟪x, φ (star a * b) y⟫ : ℂ))
              (by intro b₁ b₂ y; simp [mul_add])
              (by intro c b y; simp)
              (by intro b y₁ y₂; simp)
              (by intro c b y; simp))
          map_add' := by
            intro x₁ x₂
            refine TensorProduct.ext' fun b y => ?_
            simp
          map_smul' := by
            intro c x
            refine TensorProduct.ext' fun b y => ?_
            simp [mul_comm] }
      map_add' := by
        intro a₁ a₂
        refine LinearMap.ext fun x => ?_
        refine TensorProduct.ext' fun b y => ?_
        simp [add_mul]
      map_smul' := by
        intro c a
        refine LinearMap.ext fun x => ?_
        refine TensorProduct.ext' fun b y => ?_
        simp }

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
private theorem stForm_tmul (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) (a b : 𝒜) (x y : H) :
    stForm φ (a ⊗ₜ[ℂ] x) (b ⊗ₜ[ℂ] y) = ⟪x, φ (star a * b) y⟫ := rfl

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
/-- Every element of `𝒜 ⊙ ℋ` is a finite sum `∑ᵢ aᵢ ⊗ xᵢ`. -/
private theorem exists_fin_rep (t : TensorProduct ℂ 𝒜 H) :
    ∃ (n : ℕ) (a : Fin n → 𝒜) (x : Fin n → H), t = ∑ i, a i ⊗ₜ[ℂ] x i := by
  induction t with
  | zero => exact ⟨0, ![], ![], by simp⟩
  | tmul a x => exact ⟨1, ![a], ![x], by simp⟩
  | add s t hs ht =>
    obtain ⟨m, a, x, rfl⟩ := hs
    obtain ⟨k, b, y, rfl⟩ := ht
    refine ⟨m + k, Fin.append a b, Fin.append x y, ?_⟩
    rw [Fin.sum_univ_add]
    simp

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
private theorem stForm_sum (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) {m n : ℕ}
    (a : Fin m → 𝒜) (x : Fin m → H) (b : Fin n → 𝒜) (y : Fin n → H) :
    stForm φ (∑ i, a i ⊗ₜ[ℂ] x i) (∑ j, b j ⊗ₜ[ℂ] y j)
      = ∑ i, ∑ j, (⟪x i, φ (star (a i) * b j) (y j)⟫ : ℂ) := by
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_sum, stForm_tmul]
  exact Finset.sum_comm

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- The key positivity computation of dils.tex:415: for a completely positive
`φ`, `0 ≤ ∑ᵢⱼ ⟪xᵢ, φ(aᵢ* aⱼ) xⱼ⟫`.  (The thesis phrases this via `M_n φ`
acting on `ℋ^{⊕n}`; complete positivity is *defined* in this formalization,
cstar.tex 10II.6, as `0 ≤ ∑ᵢⱼ bᵢ* φ(aᵢ*aⱼ) bⱼ`, so it suffices to take for
`bᵢ` the rank-one operators `|xᵢ⟩⟨u|` at a unit vector `u`.) -/
private theorem cp_inner_nonneg (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositiveMap φ) {n : ℕ} (a : Fin n → 𝒜) (x : Fin n → H) :
    0 ≤ ∑ i, ∑ j, (⟪x i, φ (star (a i) * a j) (x j)⟫ : ℂ) := by
  by_cases hH : ∀ w : H, w = 0
  · have hx : ∀ i, x i = 0 := fun i => hH (x i)
    simp [hx]
  obtain ⟨w, hw⟩ := not_forall.mp hH
  set u : H := (‖w‖⁻¹ : ℝ) • w with hu
  have hun : ‖u‖ = 1 := by rw [hu]; exact norm_smul_inv_norm hw
  have huu : (⟪u, u⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hun]
    norm_num
  set b : Fin n → (H →L[ℂ] H) := fun i => (innerSL ℂ u).smulRight (x i) with hb
  have hbu : ∀ i, b i u = x i := by
    intro i
    simp [hb, hun]
  have hkey := hφ n a b
  have h2 : 0 ≤ (⟪u, (∑ i, ∑ j, star (b i) * φ (star (a i) * a j) * b j) u⟫ : ℂ) := by
    have h3 := astara_pos_basic_2_cp (vectorFunctional u) (ad_cp_3 u) _ hkey
    rwa [vectorFunctional_apply] at h3
  have hcomp : (⟪u, (∑ i, ∑ j, star (b i) * φ (star (a i) * a j) * b j) u⟫ : ℂ)
      = ∑ i, ∑ j, (⟪x i, φ (star (a i) * a j) (x j)⟫ : ℂ) := by
    simp only [sum_apply, inner_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_apply_eq_comp, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, hbu, hbu]
  rwa [hcomp] at h2

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- Positivity of `[·,·]` (dils.tex:415). -/
private theorem stForm_nonneg (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositiveMap φ) (t : TensorProduct ℂ 𝒜 H) :
    0 ≤ stForm φ t t := by
  obtain ⟨n, a, x, rfl⟩ := exists_fin_rep t
  rw [stForm_sum]
  exact cp_inner_nonneg φ hφ a x

/-- Conjugate symmetry of `[·,·]` (dils.tex:410), from the fact that a
positive map preserves the involution (**10IV**). -/
private theorem stForm_symm (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) (hp : IsPositiveMap φ)
    (s t : TensorProduct ℂ 𝒜 H) :
    stForm φ t s = starRingEnd ℂ (stForm φ s t) := by
  have hi : ∀ c : 𝒜, φ (star c) = star (φ c) := cstar_p_implies_i φ hp
  induction s with
  | zero => simp
  | add s₁ s₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂, map_add]
  | tmul a x =>
    induction t with
    | zero => simp
    | add t₁ t₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂, map_add]
    | tmul b y =>
      rw [stForm_tmul, stForm_tmul, inner_conj_symm]
      rw [show star b * a = star (star a * b) by rw [star_mul, star_star],
        hi, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]

/-- `ϱ₀(b)` on `𝒜 ⊙ ℋ` (dils.tex:466): `a ⊗ x ↦ (b a) ⊗ x`. -/
private noncomputable def rho0 (b : 𝒜) :
    TensorProduct ℂ 𝒜 H →ₗ[ℂ] TensorProduct ℂ 𝒜 H :=
  TensorProduct.map (LinearMap.mulLeft ℂ b) LinearMap.id

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
private theorem rho0_tmul (b a : 𝒜) (x : H) :
    rho0 (H := H) b (a ⊗ₜ[ℂ] x) = (b * a) ⊗ₜ[ℂ] x := rfl

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
private theorem rho0_sum (b : 𝒜) {n : ℕ} (a : Fin n → 𝒜) (x : Fin n → H) :
    rho0 b (∑ i, a i ⊗ₜ[ℂ] x i) = ∑ i, (b * a i) ⊗ₜ[ℂ] x i := by
  rw [map_sum]
  simp only [rho0_tmul]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
private theorem rho0_one : rho0 (H := H) (1 : 𝒜) = LinearMap.id := by
  refine TensorProduct.ext' fun a x => ?_
  rw [rho0_tmul, one_mul]
  rfl

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
private theorem rho0_mul (b b' : 𝒜) :
    rho0 (H := H) (b * b') = (rho0 b).comp (rho0 b') := by
  refine TensorProduct.ext' fun a x => ?_
  rw [rho0_tmul]
  rw [LinearMap.comp_apply, rho0_tmul, rho0_tmul, mul_assoc]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
/-- The adjointness computation of dils.tex:495:
`[ϱ₀(b*) s, t] = [s, ϱ₀(b) t]`. -/
private theorem stForm_rho0_adj (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) (b : 𝒜)
    (s t : TensorProduct ℂ 𝒜 H) :
    stForm φ (rho0 (star b) s) t = stForm φ s (rho0 b t) := by
  induction s with
  | zero => simp
  | add s₁ s₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a x =>
    induction t with
    | zero => simp
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul d y =>
      rw [rho0_tmul, rho0_tmul, stForm_tmul, stForm_tmul, star_mul, star_star,
        mul_assoc]

/-- The bound of dils.tex:466–485: `[ϱ₀(b)t, ϱ₀(b)t] ≤ ‖b‖² [t,t]`, from the
matrix inequality `(aᵢ* b* b aⱼ)ᵢⱼ ≤ ‖b‖² (aᵢ* aⱼ)ᵢⱼ`. -/
private theorem stForm_rho0_le (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositiveMap φ) (b : 𝒜) (t : TensorProduct ℂ 𝒜 H) :
    stForm φ (rho0 b t) (rho0 b t) ≤ ((‖b‖ ^ 2 : ℝ) : ℂ) * stForm φ t t := by
  obtain ⟨n, a, x, rfl⟩ := exists_fin_rep t
  -- `b* b ≤ ‖b‖²`, so `‖b‖² − b* b = c* c` for some `c ∈ 𝒜`
  have h1 : star b * b ≤ algebraMap ℝ 𝒜 ‖star b * b‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg b))
  have h2 : algebraMap ℝ 𝒜 ‖star b * b‖ = ((‖b‖ ^ 2 : ℝ) : ℂ) • (1 : 𝒜) := by
    rw [CStarRing.norm_star_mul_self, Algebra.algebraMap_eq_smul_one,
      ← IsScalarTower.algebraMap_smul ℂ (‖b‖ * ‖b‖ : ℝ) (1 : 𝒜)]
    norm_num [sq]
  rw [h2] at h1
  obtain ⟨c, hc⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr h1)
  have hentry : ∀ i j : Fin n,
      star (c * a i) * (c * a j)
        = ((‖b‖ ^ 2 : ℝ) : ℂ) • (star (a i) * a j)
          - star (b * a i) * (b * a j) := by
    intro i j
    rw [star_mul, star_mul]
    have : star (a i) * (star c * c) * a j
        = star (a i) * (((‖b‖ ^ 2 : ℝ) : ℂ) • (1 : 𝒜) - star b * b) * a j := by
      rw [← hc]
    calc star (a i) * star c * (c * a j)
        = star (a i) * (star c * c) * a j := by noncomm_ring
      _ = star (a i) * (((‖b‖ ^ 2 : ℝ) : ℂ) • (1 : 𝒜) - star b * b) * a j := this
      _ = ((‖b‖ ^ 2 : ℝ) : ℂ) • (star (a i) * a j)
            - star (a i) * star b * (b * a j) := by
          rw [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc]
          congr 1
          noncomm_ring
  rw [rho0_sum, stForm_sum, stForm_sum, ← sub_nonneg]
  have hkey := cp_inner_nonneg φ hφ (fun i => c * a i) x
  convert hkey using 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hentry]
  simp

/-- The construction underlying **135IV** and its part 1: the Stinespring
dilation of a cp-map `φ`, together with the fact that `V` is an isometry
when `φ` is unital.  (dils.tex:400–570.) -/
private theorem stinespring_aux (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositiveMap φ) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ϱ : MIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (V : H →L[ℂ] 𝒦),
      (∀ a : 𝒜, φ a = conjOperator V (ϱ a)) ∧ (φ 1 = 1 → Isometry V) ∧
      Dense (Submodule.span ℂ
        {k : 𝒦 | ∃ (a : 𝒜) (x : H), k = ϱ a (V x)} : Set 𝒦) ∧
      (∀ R : 𝒦 →L[ℂ] 𝒦, (∀ (a : 𝒜) (x : H), R (ϱ a (V x)) = 0) → R = 0) ∧
      (∀ (a : 𝒜) (x : H) (b : 𝒜),
        (⟪ϱ a (V x), ϱ b (ϱ a (V x))⟫ : ℂ) = ⟪x, φ (star a * b * a) x⟫) := by
  have hp : IsPositiveMap φ := astara_pos_basic_2_cp φ hφ
  obtain ⟨𝒦, _, _, _, η, hη, hdense⟩ :=
    prop_complete_into_hilbert_space (TensorProduct ℂ 𝒜 H) (stForm φ)
      (fun v w => stForm_symm φ hp v w)
      (fun v => by simpa using (Complex.le_def.mp (stForm_nonneg φ hφ v)).1)
  -- `‖η t‖² = [t,t]`
  have hnorm : ∀ t : TensorProduct ℂ 𝒜 H, ‖η t‖ ^ 2 = (stForm φ t t).re := by
    intro t
    rw [← hη t t]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (η t)).symm
  -- `‖η (ϱ₀(b) t)‖ ≤ ‖b‖ ‖η t‖`
  have hbnd : ∀ (b : 𝒜) (t : TensorProduct ℂ 𝒜 H),
      ‖η (rho0 b t)‖ ≤ ‖b‖ * ‖η t‖ := by
    intro b t
    have h1 := stForm_rho0_le φ hφ b t
    have h2 : (stForm φ (rho0 b t) (rho0 b t)).re
        ≤ ‖b‖ ^ 2 * (stForm φ t t).re := by
      have h := (Complex.le_def.mp h1).1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero] at h
      exact h
    rw [← hnorm, ← hnorm] at h2
    have h3 : ‖η (rho0 b t)‖ ^ 2 ≤ (‖b‖ * ‖η t‖) ^ 2 := by rw [mul_pow]; exact h2
    have h4 := Real.sqrt_le_sqrt h3
    rwa [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at h4
  -- the extension `ϱ(b) = \hat{ϱ₀(b)}` (dils.tex:455, `stinespring-extend-operator`)
  set ϱ : 𝒜 → (𝒦 →L[ℂ] 𝒦) :=
    fun b => LinearMap.extendOfNorm (η.comp (rho0 b)) η with hϱdef
  have hϱ : ∀ (b : 𝒜) (t : TensorProduct ℂ 𝒜 H), ϱ b (η t) = η (rho0 b t) :=
    fun b t => LinearMap.extendOfNorm_eq hdense ⟨‖b‖, fun s => hbnd b s⟩ t
  have hext : ∀ S T : 𝒦 →L[ℂ] 𝒦, (∀ t, S (η t) = T (η t)) → S = T := by
    intro S T h
    refine ContinuousLinearMap.ext fun k => ?_
    exact hdense.induction_on k (isClosed_eq (by fun_prop) (by fun_prop)) h
  -- `ϱ` is a ∗-homomorphism
  have hone : ϱ 1 = 1 := hext _ _ fun t => by rw [hϱ, rho0_one]; rfl
  have hmul : ∀ b b' : 𝒜, ϱ (b * b') = ϱ b * ϱ b' := fun b b' =>
    hext _ _ fun t => by
      rw [hϱ, rho0_mul, LinearMap.comp_apply, mul_apply_eq_comp, hϱ, hϱ]
  have hzero : ϱ 0 = 0 := hext _ _ fun t => by
    rw [hϱ, show rho0 (H := H) (0 : 𝒜) = 0 from by
      refine TensorProduct.ext' fun a x => ?_
      rw [rho0_tmul, zero_mul, TensorProduct.zero_tmul]
      rfl]
    simp
  have hadd : ∀ b b' : 𝒜, ϱ (b + b') = ϱ b + ϱ b' := fun b b' =>
    hext _ _ fun t => by
      rw [hϱ, show rho0 (H := H) (b + b') = rho0 b + rho0 b' from by
        refine TensorProduct.ext' fun a x => ?_
        rw [rho0_tmul, add_mul, TensorProduct.add_tmul]
        rw [LinearMap.add_apply, rho0_tmul, rho0_tmul]]
      simp [hϱ]
  have hsmul : ∀ (r : ℂ) (b : 𝒜), ϱ (r • b) = r • ϱ b := fun r b =>
    hext _ _ fun t => by
      rw [hϱ, show rho0 (H := H) (r • b) = r • rho0 b from by
        refine TensorProduct.ext' fun a x => ?_
        rw [rho0_tmul, smul_mul_assoc, LinearMap.smul_apply, rho0_tmul,
          TensorProduct.smul_tmul']]
      simp [hϱ]
  -- involution: `[ϱ₀(b*)s, t] = [s, ϱ₀(b)t]` gives `ϱ(b*) = ϱ(b)*`
  have hinner : ∀ (b : 𝒜) (k l : 𝒦), (⟪ϱ (star b) k, l⟫ : ℂ) = ⟪k, ϱ b l⟫ := by
    intro b k l
    have h1 : ∀ s t : TensorProduct ℂ 𝒜 H,
        (⟪ϱ (star b) (η s), η t⟫ : ℂ) = ⟪η s, ϱ b (η t)⟫ := by
      intro s t
      rw [hϱ, hϱ, hη, hη]
      exact stForm_rho0_adj φ b s t
    have h2 : ∀ (k : 𝒦) (t : TensorProduct ℂ 𝒜 H),
        (⟪ϱ (star b) k, η t⟫ : ℂ) = ⟪k, ϱ b (η t)⟫ := fun k t =>
      hdense.induction_on k (isClosed_eq (by fun_prop) (by fun_prop))
        (fun s => h1 s t)
    exact hdense.induction_on l (isClosed_eq (by fun_prop) (by fun_prop))
      (fun t => h2 k t)
  have hstar : ∀ b : 𝒜, ϱ (star b) = star (ϱ b) := by
    intro b
    rw [ContinuousLinearMap.star_eq_adjoint]
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun k l => hinner b k l
  -- `V`
  have hV0 : ∀ x : H,
      ‖η ((1 : 𝒜) ⊗ₜ[ℂ] x)‖ ≤ Real.sqrt ‖φ 1‖ * ‖x‖ := by
    intro x
    have h1 : ‖η ((1 : 𝒜) ⊗ₜ[ℂ] x)‖ ^ 2 ≤ ‖φ 1‖ * ‖x‖ ^ 2 := by
      rw [hnorm]
      have h2 : (stForm φ ((1 : 𝒜) ⊗ₜ[ℂ] x) ((1 : 𝒜) ⊗ₜ[ℂ] x)).re
          = (⟪x, φ 1 x⟫ : ℂ).re := by
        rw [stForm_tmul, star_one, one_mul]
      rw [h2]
      calc (⟪x, φ 1 x⟫ : ℂ).re ≤ ‖(⟪x, φ 1 x⟫ : ℂ)‖ := Complex.re_le_norm _
        _ ≤ ‖x‖ * ‖φ 1 x‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖φ 1‖ * ‖x‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _)
              (norm_nonneg _)
        _ = ‖φ 1‖ * ‖x‖ ^ 2 := by ring
    have h3 : ‖η ((1 : 𝒜) ⊗ₜ[ℂ] x)‖ ≤ Real.sqrt (‖φ 1‖ * ‖x‖ ^ 2) := by
      rw [show ‖η ((1 : 𝒜) ⊗ₜ[ℂ] x)‖
          = Real.sqrt (‖η ((1 : 𝒜) ⊗ₜ[ℂ] x)‖ ^ 2) from
        (Real.sqrt_sq (norm_nonneg _)).symm]
      exact Real.sqrt_le_sqrt h1
    calc ‖η ((1 : 𝒜) ⊗ₜ[ℂ] x)‖ ≤ Real.sqrt (‖φ 1‖ * ‖x‖ ^ 2) := h3
      _ = Real.sqrt ‖φ 1‖ * ‖x‖ := by
          rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  set V : H →L[ℂ] 𝒦 :=
    LinearMap.mkContinuous (η.comp (TensorProduct.mk ℂ 𝒜 H 1))
      (Real.sqrt ‖φ 1‖) hV0 with hVdef
  have hVapp : ∀ x : H, V x = η ((1 : 𝒜) ⊗ₜ[ℂ] x) := fun _ => rfl
  have hVinner : ∀ x y : H, (⟪V y, V x⟫ : ℂ) = ⟪y, φ 1 x⟫ := by
    intro x y
    rw [hVapp, hVapp, hη, stForm_tmul, star_one, one_mul]
  have hϱV : ∀ (a : 𝒜) (x : H), ϱ a (V x) = η (a ⊗ₜ[ℂ] x) := by
    intro a x
    rw [hVapp, hϱ, rho0_tmul, mul_one]
  -- minimality: the span of `ϱ(𝒜)Vℋ` contains the range of `η`
  have hmin : Dense (Submodule.span ℂ
      {k : 𝒦 | ∃ (a : 𝒜) (x : H), k = ϱ a (V x)} : Set 𝒦) := by
    refine Dense.mono ?_ hdense
    rintro k ⟨t, rfl⟩
    obtain ⟨n, a, x, rfl⟩ := exists_fin_rep t
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_
    exact ⟨a i, x i, (hϱV (a i) (x i)).symm⟩
  -- the vectors `ϱ(a)Vx` separate the operators on `𝒦`
  have hsep : ∀ R : 𝒦 →L[ℂ] 𝒦,
      (∀ (a : 𝒜) (x : H), R (ϱ a (V x)) = 0) → R = 0 := by
    intro R hR
    refine hext R 0 fun t => ?_
    obtain ⟨n, a, x, rfl⟩ := exists_fin_rep t
    have hz : ∀ i, R (η (a i ⊗ₜ[ℂ] x i)) = 0 := fun i => by
      rw [← hϱV (a i) (x i)]; exact hR _ _
    simp [map_sum, hz]
  -- the vector states `⟪ϱ(a)Vx, ϱ(b)ϱ(a)Vx⟫ = ⟪x, φ(a* b a)x⟫`
  have hvec : ∀ (a : 𝒜) (x : H) (b : 𝒜),
      (⟪ϱ a (V x), ϱ b (ϱ a (V x))⟫ : ℂ) = ⟪x, φ (star a * b * a) x⟫ := by
    intro a x b
    rw [hϱV, hϱ, rho0_tmul, hη, stForm_tmul, mul_assoc]
  refine ⟨𝒦, inferInstance, inferInstance, inferInstance,
    { toFun := ϱ
      map_one' := hone
      map_mul' := hmul
      map_zero' := hzero
      map_add' := hadd
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, hsmul, hone,
          Algebra.algebraMap_eq_smul_one]
      map_star' := hstar }, V, fun a => ?_, fun hu => ?_, hmin, hsep, hvec⟩
  · refine ContinuousLinearMap.ext fun x => ?_
    refine ext_inner_left ℂ fun y => ?_
    change (⟪y, φ a x⟫ : ℂ)
      = ⟪y, ContinuousLinearMap.adjoint V ((ϱ a).comp V x)⟫
    rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply,
      hVapp, hVapp, hϱ, rho0_tmul, mul_one, hη, stForm_tmul, star_one, one_mul]
  · refine AddMonoidHomClass.isometry_of_norm V fun x => ?_
    have h1 : ‖V x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (V x), hVinner, hu]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) x
    nlinarith [norm_nonneg (V x), norm_nonneg x]

/-- `φ` as a positive linear map, for the normality argument. -/
private noncomputable def toPos (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) (hp : IsPositiveMap φ) :
    𝒜 →ₚ[ℂ] (H →L[ℂ] H) where
  toLinearMap := φ
  monotone' := fun x y hxy => by
    have h := hp (y - x) (sub_nonneg.mpr hxy)
    rw [map_sub] at h
    exact sub_nonneg.mp h

/-- `b ↦ a* b a` as a positive linear map (**44VIII**). -/
private noncomputable def adPos (a : 𝒜) : 𝒜 →ₚ[ℂ] 𝒜 where
  toLinearMap :=
    { toFun := fun b => star a * b * a
      map_add' := fun x y => by noncomm_ring
      map_smul' := fun c x => by simp }
  monotone' := fun _ _ hxy => star_left_conjugate_le_conjugate hxy a

private theorem adPos_apply (a b : 𝒜) : adPos a b = star a * b * a := rfl

private theorem adPos_normal [VonNeumannAlgebra 𝒜] (a : 𝒜) :
    PreservesDirSups ⇑(adPos a) := by
  intro D s hne hdir hlub
  have hb : BddAbove D := ⟨s, hlub.1⟩
  have hs : dirSup D ⟨hne, hdir, hb⟩ = s :=
    (isLUB_dirSup D ⟨hne, hdir, hb⟩).unique hlub
  have h := ad_normal a D ⟨hne, hdir, hb⟩
  rw [hs] at h
  exact h

/-- **135IV**, part 2 (dils.tex:555): the Stinespring representation of a
*normal* cp-map on a von Neumann algebra is normal, together with the
minimality of the dilation (used for **139I**). -/
private theorem stinespring_normal_aux [VonNeumannAlgebra 𝒜]
    (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) (hφ : IsCompletelyPositiveMap φ)
    (hn : PreservesDirSups ⇑φ) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ϱ : NMIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (V : H →L[ℂ] 𝒦),
      (∀ a : 𝒜, φ a = conjOperator V (ϱ a)) ∧ (φ 1 = 1 → Isometry V) ∧
      Dense (Submodule.span ℂ
        {k : 𝒦 | ∃ (a : 𝒜) (x : H), k = ϱ a (V x)} : Set 𝒦) := by
  obtain ⟨𝒦, hn1, hn2, hn3, ϱ, V, heq, hiso, hmin, hsep, hvec⟩ :=
    stinespring_aux φ hφ
  have hp : IsPositiveMap φ := astara_pos_basic_2_cp φ hφ
  have hnormal : PreservesDirSups ⇑ϱ := by
    refine starAlgHom_preservesDirSups_of_vectors ϱ
      {k : 𝒦 | ∃ (a : 𝒜) (x : H), k = ϱ a (V x)} ?_ ?_
    · rintro R hR
      exact hsep R fun a x => hR _ ⟨a, x, rfl⟩
    · rintro y ⟨a, x, rfl⟩
      exact ⟨compNP (adPos a) (adPos_normal a)
        (compNP (toPos φ hp) hn (vectorNP x)), fun b => hvec a x b⟩
  refine ⟨𝒦, hn1, hn2, hn3, ⟨ϱ, hnormal⟩, V, ?_, ?_, ?_⟩
  · exact heq
  · exact hiso
  · exact hmin

/-- **135IV** (`stinespring-theorem`, dils.tex:37, Theorem (Stinespring)):
for every cp-map `φ : 𝒜 → B(ℋ)` from a C*-algebra `𝒜` to the bounded
operators on a Hilbert space `ℋ` there are a Hilbert space `𝒦`, an miu-map
`ϱ : 𝒜 → B(𝒦)` and a bounded operator `V : ℋ → 𝒦` with
`φ = ad_V ∘ ϱ`, i.e. `φ(a) = V* ϱ(a) V`. -/
theorem stinespring (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) (hφ : IsCompletelyPositiveMap φ) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ϱ : MIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (V : H →L[ℂ] 𝒦),
      ∀ a : 𝒜, φ a = conjOperator V (ϱ a) := by
  obtain ⟨𝒦, h1, h2, h3, ϱ, V, heq, -, -, -, -⟩ := stinespring_aux φ hφ
  exact ⟨𝒦, h1, h2, h3, ϱ, V, heq⟩

/-- **135IV** (`stinespring-theorem`, dils.tex:37, Theorem (Stinespring)),
part 1: if moreover `φ` is unital, the dilation can be chosen with `V` an
isometry. -/
theorem stinespring_unital (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositiveMap φ) (hu : φ 1 = 1) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ϱ : MIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (V : H →L[ℂ] 𝒦),
      Isometry V ∧ ∀ a : 𝒜, φ a = conjOperator V (ϱ a) := by
  obtain ⟨𝒦, h1, h2, h3, ϱ, V, heq, hiso, -, -, -⟩ := stinespring_aux φ hφ
  exact ⟨𝒦, h1, h2, h3, ϱ, V, hiso hu, heq⟩

/-- **135IV** (`stinespring-theorem`, dils.tex:37, Theorem (Stinespring)),
part 2: if `𝒜` is a von Neumann algebra and `φ` is normal, then the
representation `ϱ` can be chosen normal as well (an nmiu-map).

**135V**, **135VI** (`overview-dils`): discussion and overview — nothing to
formalize. -/
theorem stinespring_normal [VonNeumannAlgebra 𝒜] (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositiveMap φ) (hn : PreservesDirSups ⇑φ) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ϱ : NMIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (V : H →L[ℂ] 𝒦),
      ∀ a : 𝒜, φ a = conjOperator V (ϱ a) := by
  obtain ⟨𝒦, h1, h2, h3, ϱ, V, heq, -, -⟩ := stinespring_normal_aux φ hφ hn
  exact ⟨𝒦, h1, h2, h3, ϱ, V, heq⟩

end StinespringProof


/-! ## The Hilbert space tensor product

Infrastructure for parsec 1380: the completed tensor product `H ⊗ K` of
Hilbert spaces (Mathlib: the inner product space `H ⊗[ℂ] K` and its
`UniformSpace.Completion`), and the operator `a ⊗ b` on it.  (The Hilbert
space tensor product is developed in thesis A, proc.tex parsecs 1090–1100,
which is not yet formalized; we use Mathlib's ingredients directly.) -/

section HilbTensor

variable (H K : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- The Hilbert space tensor product `H ⊗ K`: the completion of the
algebraic tensor product `H ⊗[ℂ] K` with the inner product
`⟪x ⊗ y, x' ⊗ y'⟫ = ⟪x, x'⟫ ⟪y, y'⟫`. -/
noncomputable abbrev hilbTensor : Type u :=
  UniformSpace.Completion (TensorProduct ℂ H K)

variable {H K}

/-- The canonical image of an elementary tensor `x ⊗ y` in `hilbTensor H K`. -/
noncomputable def hilbTensorMk (x : H) (y : K) : hilbTensor H K :=
  ((x ⊗ₜ[ℂ] y : TensorProduct ℂ H K) : hilbTensor H K)

/-- The operator `a ⊗ b` on `hilbTensor H K`, for bounded operators
`a : H → H` and `b : K → K` — the continuous extension of
`TensorProduct.map`, obtained as `TensorProduct.mapL` followed by
`LinearMap.extendOfNorm` along the dense range into the completion.  Its
characterizing property is `tensorCLM_mk` below. -/
noncomputable def tensorCLM (a : H →L[ℂ] H) (b : K →L[ℂ] K) :
    hilbTensor H K →L[ℂ] hilbTensor H K :=
  LinearMap.extendOfNorm
    (((UniformSpace.Completion.toComplL :
          TensorProduct ℂ H K →L[ℂ] hilbTensor H K).comp
        (TensorProduct.mapL a b)).toLinearMap)
    ((UniformSpace.Completion.toComplL :
        TensorProduct ℂ H K →L[ℂ] hilbTensor H K).toLinearMap)

set_option linter.unusedSectionVars false in
/-- Characterizing property of `tensorCLM`:
`(a ⊗ b) (x ⊗ y) = (a x) ⊗ (b y)`. -/
theorem tensorCLM_mk (a : H →L[ℂ] H) (b : K →L[ℂ] K) (x : H) (y : K) :
    tensorCLM a b (hilbTensorMk x y) = hilbTensorMk (a x) (b y) := by
  have hdense : DenseRange
      ⇑((UniformSpace.Completion.toComplL :
          TensorProduct ℂ H K →L[ℂ] hilbTensor H K).toLinearMap) := by
    simpa [UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.denseRange_coe (α := TensorProduct ℂ H K))
  have hnorm : ∃ C : ℝ, ∀ z : TensorProduct ℂ H K,
      ‖(((UniformSpace.Completion.toComplL :
            TensorProduct ℂ H K →L[ℂ] hilbTensor H K).comp
          (TensorProduct.mapL a b)).toLinearMap) z‖ ≤
        C * ‖((UniformSpace.Completion.toComplL :
            TensorProduct ℂ H K →L[ℂ] hilbTensor H K).toLinearMap) z‖ := by
    refine ⟨‖a‖ * ‖b‖, fun z => ?_⟩
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
      Function.comp_apply,
      UniformSpace.Completion.coe_toComplL, UniformSpace.Completion.norm_coe]
    calc ‖TensorProduct.mapL a b z‖ ≤ ‖TensorProduct.mapL a b‖ * ‖z‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖a‖ * ‖b‖ * ‖z‖ :=
          mul_le_mul_of_nonneg_right (TensorProduct.norm_mapL_le a b) (norm_nonneg _)
  change LinearMap.extendOfNorm _ _
    ((UniformSpace.Completion.toComplL :
      TensorProduct ℂ H K →L[ℂ] hilbTensor H K).toLinearMap (x ⊗ₜ[ℂ] y)) = _
  rw [LinearMap.extendOfNorm_eq hdense hnorm]
  rfl

end HilbTensor

/-! ### Auxiliary development for 138II

The thesis proves **138II** (dils.tex 138III–138V) by building an orthonormal
basis `rᵢⱼ = ϱ(uᵢ*) dⱼ` of `𝒦` out of an orthonormal basis `(eᵢ)` of `ℋ`, an
orthonormal basis `(dⱼ)` of `𝒦' = ϱ(p_{i₀})𝒦` and the partial isometries
`uᵢ = |e_{i₀}⟩⟨eᵢ|`, and reading the unitary `U` off it.  What follows is the
same construction in coordinate-free form: the map `W(x ⊗ d) = ϱ(|x⟩⟨e₀|) d`,
for one unit vector `e₀` (the thesis's `e_{i₀}`), satisfies `W(eᵢ ⊗ dⱼ) = rᵢⱼ`.
That `W` is isometric *is* the thesis's orthonormality computation, and the
intertwining relation `W ∘ (a ⊗ 1) = ϱ(a) ∘ W`, immediate from
`a·|x⟩⟨e₀| = |a x⟩⟨e₀|`, replaces the ultrastrongly convergent expansion of
`|a eᵢ⟩⟨e_{i₀}|` in 138V.  A basis of `ℋ` is still needed, but only for the
surjectivity of `W`, which is where the thesis's `∑ᵢⱼ |rᵢⱼ⟩⟨rᵢⱼ| = 1` and the
normality of `ϱ` are used.  See PROVING-LOG.md. -/

section KetbraAux


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `|x⟩⟨y| z = ⟪y, z⟫ x` (**4XIX**.1). -/
theorem ketbra_apply' (x y z : H) : ketbra x y z = ⟪y, z⟫ • x := rfl

/-- `(|x⟩⟨y|)* = |y⟩⟨x|` (**4XIX**.2, in `star` form). -/
theorem ketbra_star (x y : H) : star (ketbra x y) = ketbra y x := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr ?_).symm
  intro u v
  simp only [ketbra_apply', inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

/-- `|a⟩⟨b| · |c⟩⟨d| = ⟪b,c⟫ |a⟩⟨d|`. -/
theorem ketbra_mul (a b c d : H) : ketbra a b * ketbra c d = ⟪b, c⟫ • ketbra a d := by
  ext z
  show ketbra a b (ketbra c d z) = _
  simp only [ketbra_apply', ContinuousLinearMap.smul_apply, smul_smul, inner_smul_right]
  ring_nf

/-- `|x⟩⟨y| · a = |x⟩⟨a* y|`. -/
theorem ketbra_mul_op (a : H →L[ℂ] H) (x y : H) :
    ketbra x y * a = ketbra x (ContinuousLinearMap.adjoint a y) := by
  ext z
  show ⟪y, a z⟫ • x = ⟪ContinuousLinearMap.adjoint a y, z⟫ • x
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- `a · |x⟩⟨y| = |a x⟩⟨y|`. -/
theorem mul_ketbra (a : H →L[ℂ] H) (x y : H) : a * ketbra x y = ketbra (a x) y := by
  ext z
  show a (⟪y, z⟫ • x) = ⟪y, z⟫ • a x
  rw [map_smul]

/-- `|x⟩⟨x|` is a projection when `x` is a unit vector. -/
theorem isStarProjection_ketbra {x : H} (hx : ‖x‖ = 1) : IsStarProjection (ketbra x x) := by
  refine ⟨?_, ?_⟩
  · show ketbra x x * ketbra x x = ketbra x x
    rw [ketbra_mul, inner_self_eq_norm_sq_to_K, hx]
    simp
  · exact ketbra_star x x

/-- The rank-one projections of an orthonormal family are pairwise orthogonal. -/
theorem ketbra_orth {ι : Type*} {v : ι → H} (hv : Orthonormal ℂ v) {i j : ι} (hij : i ≠ j) :
    ketbra (v i) (v i) * ketbra (v j) (v j) = 0 := by
  rw [ketbra_mul, hv.2 hij]
  simp

/-- For a Hilbert basis `b`, the partial sums `∑_{i∈F} |bᵢ⟩⟨bᵢ|` have supremum `1`
in the self-adjoint part of `B(H)` — the statement of normality needs. -/
theorem isLUB_hilbertBasis_partialSums {ι : Type u} (b : HilbertBasis ι ℂ H) :
    ∀ (hsa : ∀ F : Finset ι, IsSelfAdjoint (∑ i ∈ F, ketbra (b i) (b i))),
    IsLUB (Set.range fun F : Finset ι =>
      (⟨∑ i ∈ F, ketbra (b i) (b i), hsa F⟩ : selfAdjoint (H →L[ℂ] H))) 1 := by
  intro hsa
  have hproj : ∀ F : Finset ι, IsStarProjection (∑ i ∈ F, ketbra (b i) (b i)) := fun F =>
    isStarProjection_sum F _ (fun i => isStarProjection_ketbra (b.orthonormal.1 i))
      (fun i _ j _ hij => ketbra_orth b.orthonormal hij)
  constructor
  · rintro _ ⟨F, rfl⟩
    exact (hproj F).le_one
  · rintro t ht
    show (1 : H →L[ℂ] H) ≤ (t : H →L[ℂ] H)
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff']
    refine ⟨(t.2.sub (IsSelfAdjoint.one _)), fun ξ => ?_⟩
    have hle : ∀ F : Finset ι, (0:ℂ) ≤ ⟪((t : H →L[ℂ] H) - ∑ i ∈ F, ketbra (b i) (b i)) ξ, ξ⟫ := by
      intro F
      have := ht ⟨F, rfl⟩
      have h2 : (∑ i ∈ F, ketbra (b i) (b i)) ≤ (t : H →L[ℂ] H) := this
      rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff'] at h2
      exact h2.2 ξ
    have hsum := b.hasSum_inner_mul_inner ξ ξ
    have hpartial : ∀ F : Finset ι,
        ∑ i ∈ F, ⟪ξ, b i⟫ * ⟪b i, ξ⟫ ≤ ⟪(t : H →L[ℂ] H) ξ, ξ⟫ := by
      intro F
      have h := hle F
      rw [ContinuousLinearMap.sub_apply, inner_sub_left] at h
      have hcomp : ⟪(∑ i ∈ F, ketbra (b i) (b i)) ξ, ξ⟫
          = ∑ i ∈ F, ⟪ξ, b i⟫ * ⟪b i, ξ⟫ := by
        rw [ContinuousLinearMap.sum_apply, sum_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ketbra_apply', inner_smul_left, inner_conj_symm]
      rw [hcomp] at h
      exact sub_nonneg.mp h
    have hfin := le_of_tendsto hsum (Filter.Eventually.of_forall hpartial)
    rw [ContinuousLinearMap.sub_apply, inner_sub_left, ContinuousLinearMap.one_apply]
    exact sub_nonneg.mpr hfin

end KetbraAux

section HilbTensorAPI


variable {H K Z : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]

/-- The algebraic tensor product is dense in `H ⊗ K`. -/
theorem hilbTensor_denseRange_coe :
    DenseRange (fun z : TensorProduct ℂ H K => ((z : hilbTensor H K))) :=
  UniformSpace.Completion.denseRange_coe

/-- `⟪x ⊗ y, x' ⊗ y'⟫ = ⟪x,x'⟫ ⟪y,y'⟫` in `H ⊗ K`. -/
theorem hilbTensor_inner_mk (x x' : H) (y y' : K) :
    ⟪hilbTensorMk x y, hilbTensorMk x' y'⟫ = ⟪x, x'⟫ * ⟪y, y'⟫ := by
  unfold hilbTensorMk
  rw [UniformSpace.Completion.inner_coe]
  simp

/-- Two continuous linear maps out of `H ⊗ K` agreeing on elementary tensors are equal. -/
theorem hilbTensor_ext {f g : hilbTensor H K →L[ℂ] Z}
    (h : ∀ x y, f (hilbTensorMk x y) = g (hilbTensorMk x y)) : f = g := by
  have hEq : Set.EqOn ⇑f ⇑g (Set.range (fun z : TensorProduct ℂ H K => ((z : hilbTensor H K)))) := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp only []; rw [show ((0 : TensorProduct ℂ H K) : hilbTensor H K) = 0 from UniformSpace.Completion.coe_zero]; simp
    | tmul x y => exact h x y
    | add z z' hz hz' =>
        simp only [UniformSpace.Completion.coe_add, map_add, hz, hz']
  exact DFunLike.coe_injective
    (Continuous.ext_on hilbTensor_denseRange_coe f.continuous g.continuous hEq)

/-- The continuous extension to `H ⊗ K` of an inner-product-preserving linear map on
the algebraic tensor product. -/
theorem exists_hilbTensor_isometry (w : TensorProduct ℂ H K →ₗ[ℂ] Z)
    (hw : ∀ z z', ⟪w z, w z'⟫ = ⟪z, z'⟫) :
    ∃ W : hilbTensor H K →L[ℂ] Z,
      (∀ z : TensorProduct ℂ H K, W (z : hilbTensor H K) = w z) ∧ ∀ v, ‖W v‖ = ‖v‖ := by
  have hnormw : ∀ z : TensorProduct ℂ H K, ‖w z‖ = ‖z‖ := by
    intro z
    have h2 : ‖w z‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hw]
    have := congrArg Real.sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
  have hdense : DenseRange
      ⇑((UniformSpace.Completion.toComplL :
          TensorProduct ℂ H K →L[ℂ] hilbTensor H K).toLinearMap) := by
    simpa [UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.denseRange_coe (α := TensorProduct ℂ H K))
  have hbound : ∃ C : ℝ, ∀ z : TensorProduct ℂ H K, ‖w z‖ ≤ C *
      ‖((UniformSpace.Completion.toComplL :
        TensorProduct ℂ H K →L[ℂ] hilbTensor H K).toLinearMap) z‖ := by
    refine ⟨1, fun z => ?_⟩
    simp [UniformSpace.Completion.coe_toComplL, hnormw]
  set W := w.extendOfNorm
    ((UniformSpace.Completion.toComplL :
      TensorProduct ℂ H K →L[ℂ] hilbTensor H K).toLinearMap) with hW
  have key : ∀ z : TensorProduct ℂ H K, W (z : hilbTensor H K) = w z := by
    intro z
    have h1 := LinearMap.extendOfNorm_eq (f := w)
      (e := ((UniformSpace.Completion.toComplL :
        TensorProduct ℂ H K →L[ℂ] hilbTensor H K).toLinearMap)) hdense hbound z
    simpa [UniformSpace.Completion.coe_toComplL, hW] using h1
  refine ⟨W, key, ?_⟩
  intro v
  have hclosed : IsClosed {v : hilbTensor H K | ‖W v‖ = ‖v‖} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  refine hilbTensor_denseRange_coe.induction_on (p := fun v => ‖W v‖ = ‖v‖) v hclosed ?_
  intro z
  rw [key z, UniformSpace.Completion.norm_coe, hnormw]

end HilbTensorAPI

section TypeIAux

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `|·⟩⟨y|` is additive in its first argument. -/
theorem ketbra_add_left (x x' y : H) : ketbra (x + x') y = ketbra x y + ketbra x' y := by
  ext z; simp [ketbra_apply', smul_add]

/-- `|·⟩⟨y|` is homogeneous in its first argument. -/
theorem ketbra_smul_left (c : ℂ) (x y : H) : ketbra (c • x) y = c • ketbra x y := by
  ext z
  show ⟪y, z⟫ • (c • x) = c • (⟪y, z⟫ • x)
  rw [smul_comm]

/-- A star projection whose range lies in a closed subspace `M` is below the
orthogonal projection onto `M`. -/
theorem isStarProjection_le_starProjection {M : Submodule ℂ K} [M.HasOrthogonalProjection]
    {e : K →L[ℂ] K} (he : IsStarProjection e) (hr : ∀ v, e v ∈ M) :
    e ≤ M.starProjection := by
  have hPe : M.starProjection * e = e := by
    ext v
    exact Submodule.starProjection_eq_self_iff.mpr (hr v)
  have hPsa : star (M.starProjection : K →L[ℂ] K) = M.starProjection :=
    (isSelfAdjoint_starProjection M).star_eq
  have heP : e * M.starProjection = e := by
    have := congrArg star hPe
    rwa [star_mul, hPsa, he.isSelfAdjoint.star_eq] at this
  have hidem : IsIdempotentElem (M.starProjection - e) := by
    show (M.starProjection - e) * (M.starProjection - e) = M.starProjection - e
    rw [sub_mul, mul_sub, mul_sub, hPe, heP, he.isIdempotentElem.eq,
      M.isIdempotentElem_starProjection.eq]
    abel
  have hsa : IsSelfAdjoint (M.starProjection - e) := by
    show star _ = _
    rw [star_sub, hPsa, he.isSelfAdjoint.star_eq]
  have hnn : (0 : K →L[ℂ] K) ≤ M.starProjection - e :=
    (IsStarProjection.mk hidem hsa).nonneg
  rw [ContinuousLinearMap.le_def]
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp hnn

/-- The heart of the thesis's proof of **138II** (dils.tex 138IV): if a closed
subspace `M ⊆ 𝒦` absorbs every `ϱ(|x⟩⟨e₀|)η` with `η` fixed by `ϱ(|e₀⟩⟨e₀|)`,
then `M = 𝒦`.  This is the thesis's computation `1 = ϱ(1) = ∑ᵢ ϱ(pᵢ)
= ∑ᵢⱼ |rᵢⱼ⟩⟨rᵢⱼ|`, read as: the projection onto `M` dominates every partial
sum `ϱ(∑_{i∈F} pᵢ)` — because `pᵢ = |eᵢ⟩⟨e₀| · |e₀⟩⟨e₀| · |e₀⟩⟨eᵢ|` — while
`1` is the *least* upper bound of those partial sums, by normality of `ϱ`. -/
theorem nmiu_forall_mem (ϱ : NMIUMap (H →L[ℂ] H) (K →L[ℂ] K)) (e₀ : H) (he₀ : ‖e₀‖ = 1)
    (M : Submodule ℂ K) [M.HasOrthogonalProjection]
    (hM : ∀ (x : H) (η : K), ϱ (ketbra e₀ e₀) η = η → ϱ (ketbra x e₀) η ∈ M) :
    ∀ y : K, y ∈ M := by
  classical
  have hcoe : ⇑ϱ = ⇑ϱ.toStarAlgHom := rfl
  have he₀e₀ : ⟪e₀, e₀⟫ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, he₀]; norm_num
  have hmapmul : ∀ b b' : H →L[ℂ] H, ϱ (b * b') = ϱ b * ϱ b' := fun b b' => by
    simpa [hcoe] using map_mul ϱ.toStarAlgHom b b'
  have hmulapp : ∀ (b b' : H →L[ℂ] H) (y : K), ϱ b (ϱ b' y) = ϱ (b * b') y := by
    intro b b' y; rw [hmapmul]; rfl
  have hp₀idem : ketbra e₀ e₀ * ketbra e₀ e₀ = ketbra e₀ e₀ := by
    rw [ketbra_mul, he₀e₀, one_smul]
  -- every `ϱ(|x⟩⟨x|)` has its range inside `M`
  have hrangeM : ∀ (x : H) (ξ : K), ϱ (ketbra x x) ξ ∈ M := by
    intro x ξ
    have hfact : ketbra x x = ketbra x e₀ * (ketbra e₀ e₀ * ketbra e₀ x) := by
      rw [ketbra_mul, he₀e₀, one_smul, ketbra_mul, he₀e₀, one_smul]
    have hη : ϱ (ketbra e₀ e₀) (ϱ (ketbra e₀ e₀) (ϱ (ketbra e₀ x) ξ))
        = ϱ (ketbra e₀ e₀) (ϱ (ketbra e₀ x) ξ) := by
      rw [hmulapp, hp₀idem]
    have hval : ϱ (ketbra x x) ξ
        = ϱ (ketbra x e₀) (ϱ (ketbra e₀ e₀) (ϱ (ketbra e₀ x) ξ)) := by
      rw [hfact, ← hmulapp, ← hmulapp]
    rw [hval]
    exact hM x _ hη
  obtain ⟨sB, bb, hbb⟩ := exists_hilbertBasis ℂ H
  have hprojF : ∀ F : Finset ↥sB, IsStarProjection (∑ i ∈ F, ketbra (bb i) (bb i)) := fun F =>
    isStarProjection_sum F _ (fun i => isStarProjection_ketbra (bb.orthonormal.1 i))
      (fun i _ j _ hij => ketbra_orth bb.orthonormal hij)
  have hsa : ∀ F : Finset ↥sB, IsSelfAdjoint (∑ i ∈ F, ketbra (bb i) (bb i)) := fun F =>
    (hprojF F).isSelfAdjoint
  have hleP : ∀ F : Finset ↥sB,
      ϱ (∑ i ∈ F, ketbra (bb i) (bb i)) ≤ M.starProjection := by
    intro F
    refine isStarProjection_le_starProjection (IsStarProjection.map (hprojF F) ϱ.toStarAlgHom) ?_
    intro ξ
    have hsum : ϱ (∑ i ∈ F, ketbra (bb i) (bb i)) ξ = ∑ i ∈ F, ϱ (ketbra (bb i) (bb i)) ξ := by
      rw [show ϱ (∑ i ∈ F, ketbra (bb i) (bb i)) = ∑ i ∈ F, ϱ (ketbra (bb i) (bb i)) from
        map_sum ϱ.toStarAlgHom _ F, ContinuousLinearMap.sum_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => hrangeM (bb i) ξ
  -- `1` is the supremum of the partial sums; normality transports it to `ϱ`
  set D : Set (selfAdjoint (H →L[ℂ] H)) :=
    Set.range (fun F : Finset ↥sB =>
      (⟨∑ i ∈ F, ketbra (bb i) (bb i), hsa F⟩ : selfAdjoint (H →L[ℂ] H))) with hDdef
  have hmono : ∀ F G : Finset ↥sB, F ⊆ G →
      (∑ i ∈ F, ketbra (bb i) (bb i)) ≤ ∑ i ∈ G, ketbra (bb i) (bb i) := by
    intro F G hFG
    have hsplit := Finset.sum_sdiff (f := fun i => ketbra (bb i) (bb i)) hFG
    have hdiff : (∑ i ∈ G, ketbra (bb i) (bb i)) - ∑ i ∈ F, ketbra (bb i) (bb i)
        = ∑ i ∈ G \ F, ketbra (bb i) (bb i) := by
      rw [← hsplit]; abel
    rw [ContinuousLinearMap.le_def, hdiff]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp (hprojF _).nonneg
  have hDne : D.Nonempty := ⟨_, ⟨∅, rfl⟩⟩
  have hDdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    exact ⟨_, ⟨F ∪ G, rfl⟩, hmono F (F ∪ G) Finset.subset_union_left,
      hmono G (F ∪ G) Finset.subset_union_right⟩
  have hlubD : IsLUB D 1 := isLUB_hilbertBasis_partialSums bb hsa
  have hnormal := ϱ.preservesDirSups' D 1 hDne hDdir hlubD
  have hub : M.starProjection ∈
      upperBounds ((fun d : selfAdjoint (H →L[ℂ] H) => ϱ (d : H →L[ℂ] H)) '' D) := by
    rintro _ ⟨_, ⟨F, rfl⟩, rfl⟩
    exact hleP F
  have h1le : (1 : K →L[ℂ] K) ≤ M.starProjection := by
    have h := hnormal.2 hub
    rwa [show ((1 : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H) = 1 from rfl,
      map_one ϱ.toStarAlgHom] at h
  have hPone : M.starProjection = (1 : K →L[ℂ] K) :=
    le_antisymm (isStarProjection_starProjection).le_one h1le
  intro y
  refine Submodule.starProjection_eq_self_iff.mp ?_
  rw [hPone]; rfl

section TypeIAuxMain

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem nmiu_between_type_I_aux (ϱ : NMIUMap (H →L[ℂ] H) (K →L[ℂ] K))
    (e₀ : H) (he₀ : ‖e₀‖ = 1) :
    ∃ (K' : Type u) (_ : NormedAddCommGroup K') (_ : InnerProductSpace ℂ K')
      (_ : CompleteSpace K') (U : K →L[ℂ] hilbTensor H K'),
      (ContinuousLinearMap.adjoint U).comp U = 1 ∧
      U.comp (ContinuousLinearMap.adjoint U) = 1 ∧
      ∀ a : H →L[ℂ] H, ϱ a = conjOperator U (tensorCLM a 1) := by
  classical
  have hcoe : ⇑ϱ = ⇑ϱ.toStarAlgHom := rfl
  have he₀e₀ : ⟪e₀, e₀⟫ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, he₀]; norm_num
  set p₀ : H →L[ℂ] H := ketbra e₀ e₀ with hp₀
  have hp₀idem : p₀ * p₀ = p₀ := by
    rw [hp₀, ketbra_mul, he₀e₀, one_smul]
  -- the subspace `K' = ϱ(p₀) K`, as the fixed points of `ϱ(p₀)`
  set S : Submodule ℂ K := LinearMap.ker (((1 : K →L[ℂ] K) - ϱ p₀) : K →ₗ[ℂ] K) with hSdef
  have hSmem : ∀ d : K, d ∈ S ↔ ϱ p₀ d = d := by
    intro d
    rw [hSdef, LinearMap.mem_ker]
    show ((1 : K →L[ℂ] K) - ϱ p₀) d = 0 ↔ _
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero]
    exact eq_comm
  have hSclosed : IsClosed (S : Set K) :=
    ContinuousLinearMap.isClosed_ker ((1 : K →L[ℂ] K) - ϱ p₀)
  haveI : CompleteSpace ↥S := hSclosed.completeSpace_coe
  -- the bilinear map `(x, d) ↦ ϱ(|x⟩⟨e₀|) d`
  have hmapadd : ∀ b b' : H →L[ℂ] H, ϱ (b + b') = ϱ b + ϱ b' := fun b b' => by
    simpa [hcoe] using map_add ϱ.toStarAlgHom b b'
  have hmapsmul : ∀ (c : ℂ) (b : H →L[ℂ] H), ϱ (c • b) = c • ϱ b := fun c b => by
    simpa [hcoe] using map_smul ϱ.toStarAlgHom c b
  have hmapmul : ∀ b b' : H →L[ℂ] H, ϱ (b * b') = ϱ b * ϱ b' := fun b b' => by
    simpa [hcoe] using map_mul ϱ.toStarAlgHom b b'
  have hmapstar : ∀ b : H →L[ℂ] H, ϱ (star b) = star (ϱ b) := fun b => by
    simpa [hcoe] using map_star ϱ.toStarAlgHom b
  have hmapone : ϱ (1 : H →L[ℂ] H) = 1 := by simpa [hcoe] using map_one ϱ.toStarAlgHom
  set B : H →ₗ[ℂ] ↥S →ₗ[ℂ] K :=
    LinearMap.mk₂ ℂ (fun (x : H) (d : ↥S) => ϱ (ketbra x e₀) (d : K))
      (fun x x' d => by rw [ketbra_add_left, hmapadd]; rfl)
      (fun c x d => by rw [ketbra_smul_left, hmapsmul]; rfl)
      (fun x d d' => by rw [Submodule.coe_add, map_add])
      (fun c x d => by rw [Submodule.coe_smul, map_smul]) with hBdef
  set w : TensorProduct ℂ H ↥S →ₗ[ℂ] K := TensorProduct.lift B with hwdef
  have hwmk : ∀ (x : H) (d : ↥S), w (x ⊗ₜ[ℂ] d) = ϱ (ketbra x e₀) (d : K) := fun x d => rfl
  have hadj : ∀ b : H →L[ℂ] H, ContinuousLinearMap.adjoint (ϱ b) = ϱ (star b) := by
    intro b
    rw [← ContinuousLinearMap.star_eq_adjoint, hmapstar]
  have hw : ∀ z z' : TensorProduct ℂ H ↥S, ⟪w z, w z'⟫ = ⟪z, z'⟫ := by
    have base : ∀ (x : H) (d : ↥S) (z' : TensorProduct ℂ H ↥S),
        ⟪w (x ⊗ₜ[ℂ] d), w z'⟫ = ⟪x ⊗ₜ[ℂ] d, z'⟫ := by
      intro x d z'
      induction z' using TensorProduct.induction_on with
      | zero =>
          rw [map_zero, inner_zero_right (𝕜 := ℂ) (w (x ⊗ₜ[ℂ] d))]
          exact (inner_zero_right (𝕜 := ℂ) (x ⊗ₜ[ℂ] d)).symm
      | tmul x' d' =>
          rw [hwmk, hwmk, TensorProduct.inner_tmul,
            ← ContinuousLinearMap.adjoint_inner_right, hadj]
          have hcomp : ϱ (star (ketbra x e₀)) (ϱ (ketbra x' e₀) (d' : K))
              = ϱ (star (ketbra x e₀) * ketbra x' e₀) (d' : K) := by
            rw [hmapmul]; rfl
          rw [hcomp, ketbra_star, ketbra_mul, ← hp₀, hmapsmul,
            ContinuousLinearMap.smul_apply, inner_smul_right, (hSmem _).mp d'.2]
          rfl
      | add u v hu hv =>
          rw [map_add, inner_add_right (𝕜 := ℂ) (w (x ⊗ₜ[ℂ] d)) (w u) (w v), hu, hv]
          exact (inner_add_right (𝕜 := ℂ) (x ⊗ₜ[ℂ] d) u v).symm
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        intro z'
        rw [map_zero, inner_zero_left (𝕜 := ℂ) (w z')]
        exact (inner_zero_left (𝕜 := ℂ) z').symm
    | tmul x d => exact base x d
    | add u v hu hv =>
        intro z'
        rw [map_add, inner_add_left (𝕜 := ℂ) (w u) (w v) (w z'), hu z', hv z']
        exact (inner_add_left (𝕜 := ℂ) u v z').symm
  obtain ⟨W, hWcoe, hWnorm⟩ := exists_hilbTensor_isometry w hw
  have hWmk : ∀ (x : H) (d : ↥S), W (hilbTensorMk x (d : ↥S)) = ϱ (ketbra x e₀) (d : K) :=
    fun x d => hWcoe (x ⊗ₜ[ℂ] d)
  have hmulapp : ∀ (b b' : H →L[ℂ] H) (y : K), ϱ b (ϱ b' y) = ϱ (b * b') y := by
    intro b b' y; rw [hmapmul]; rfl
  -- the (closed) range `M` of `W`
  set M : Submodule ℂ K := LinearMap.range (W : hilbTensor H ↥S →ₗ[ℂ] K) with hMdef
  have hMrange : (M : Set K) = Set.range ⇑W := LinearMap.coe_range _
  have hWiso : Isometry ⇑W := AddMonoidHomClass.isometry_of_norm W hWnorm
  have hMcomplete : IsComplete (M : Set K) := by
    rw [hMrange]; exact hWiso.isUniformInducing.isComplete_range
  haveI : CompleteSpace ↥M := hMcomplete.completeSpace_coe
  have hMtop : ∀ y : K, y ∈ M :=
    nmiu_forall_mem ϱ e₀ he₀ M (by
      intro x η hη
      exact ⟨hilbTensorMk x (⟨η, (hSmem η).mpr hη⟩ : ↥S), hWmk x ⟨η, (hSmem η).mpr hη⟩⟩)
  have hWsurj : Function.Surjective ⇑W := fun y => hMtop y
  -- `W` is a unitary
  have hWadjW : (ContinuousLinearMap.adjoint W).comp W = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    refine ext_inner_left ℂ fun y => ?_
    show ⟪y, ContinuousLinearMap.adjoint W (W v)⟫ = ⟪y, (1 : hilbTensor H ↥S →L[ℂ] _) v⟫
    rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.one_apply]
    exact ((⟨W.toLinearMap, hWnorm⟩ : hilbTensor H ↥S →ₗᵢ[ℂ] K)).inner_map_map y v
  have hWadjW' : ∀ v, ContinuousLinearMap.adjoint W (W v) = v := fun v => by
    have := congrArg (fun T : hilbTensor H ↥S →L[ℂ] hilbTensor H ↥S => T v) hWadjW
    simpa using this
  have hWWadj : W.comp (ContinuousLinearMap.adjoint W) = 1 := by
    refine ContinuousLinearMap.ext fun y => ?_
    obtain ⟨v, rfl⟩ := hWsurj y
    show W (ContinuousLinearMap.adjoint W (W v)) = _
    rw [hWadjW']
    rfl
  refine ⟨↥S, inferInstance, inferInstance, inferInstance,
    ContinuousLinearMap.adjoint W, ?_, ?_, ?_⟩
  · rw [ContinuousLinearMap.adjoint_adjoint]; exact hWWadj
  · rw [ContinuousLinearMap.adjoint_adjoint]; exact hWadjW
  · intro a
    have hintertwine : W.comp (tensorCLM a 1) = (ϱ a).comp W := by
      refine hilbTensor_ext ?_
      intro x d
      show W (tensorCLM a 1 (hilbTensorMk x d)) = ϱ a (W (hilbTensorMk x d))
      rw [tensorCLM_mk, hWmk, hWmk, hmulapp, mul_ketbra]
      rfl
    have hconj : conjOperator (ContinuousLinearMap.adjoint W) (tensorCLM a 1)
        = W.comp ((tensorCLM a 1).comp (ContinuousLinearMap.adjoint W)) := by
      show (ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint W)).comp
        ((tensorCLM a 1).comp (ContinuousLinearMap.adjoint W)) = _
      rw [ContinuousLinearMap.adjoint_adjoint]
    rw [hconj, ← ContinuousLinearMap.comp_assoc, hintertwine,
      ContinuousLinearMap.comp_assoc, hWWadj]
    exact (mul_one (ϱ a)).symm


end TypeIAuxMain
end TypeIAux


/-! ### Auxiliary development for 138VIII (Kraus)

The slice maps of the thesis's proof: for a unit vector `e` of `𝒦'` the "ket"
operator `Q_e : ℋ → ℋ ⊗ 𝒦'`, `x ↦ x ⊗ e`, has `Q_e a Q_e* = a ⊗ |e⟩⟨e|`, so
that the Kraus operators of `φ(a) = V*(a ⊗ 1)V` are `Vᵢ = Q_{eᵢ}* V` and the
partial sums `∑_{i∈F} Vᵢ* a Vᵢ` are `V* (a ⊗ P_F) V`.  What the convergence
needs is that `a ⊗ P_F ↑ a ⊗ 1`, which is proved here from `(1 ⊗ P_F)ξ → ξ`
(density plus the uniform bound `‖1 ⊗ P_F‖ ≤ 1`) and **44VI**
`vna_supremum_uwlimit`.  See PROVING-LOG.md. -/

section KrausAux

variable {H K Z : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `hilbTensorMk` is additive in its first argument. -/
theorem hilbTensorMk_add_left (x x' : H) (y : K) :
    hilbTensorMk (x + x') y = hilbTensorMk x y + hilbTensorMk (K := K) x' y := by
  unfold hilbTensorMk
  rw [TensorProduct.add_tmul, UniformSpace.Completion.coe_add]

theorem hilbTensorMk_add_right (x : H) (y y' : K) :
    hilbTensorMk x (y + y') = hilbTensorMk x y + hilbTensorMk (K := K) x y' := by
  unfold hilbTensorMk
  rw [TensorProduct.tmul_add, UniformSpace.Completion.coe_add]

theorem hilbTensorMk_sub_right (x : H) (y y' : K) :
    hilbTensorMk x (y - y') = hilbTensorMk x y - hilbTensorMk (K := K) x y' := by
  unfold hilbTensorMk
  rw [TensorProduct.tmul_sub, UniformSpace.Completion.coe_sub]

theorem hilbTensorMk_smul_left (c : ℂ) (x : H) (y : K) :
    hilbTensorMk (c • x) y = c • hilbTensorMk (K := K) x y := by
  unfold hilbTensorMk
  rw [← TensorProduct.smul_tmul']
  exact (UniformSpace.Completion.coe_smul c _)

theorem hilbTensorMk_smul_right (c : ℂ) (x : H) (y : K) :
    hilbTensorMk x (c • y) = c • hilbTensorMk (K := K) x y := by
  unfold hilbTensorMk
  rw [TensorProduct.tmul_smul]
  exact (UniformSpace.Completion.coe_smul c _)

private theorem norm_inner_self' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (z : E) : ‖(⟪z, z⟫ : ℂ)‖ = ‖z‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]

theorem norm_hilbTensorMk (x : H) (y : K) : ‖hilbTensorMk x y‖ = ‖x‖ * ‖y‖ := by
  have h := congrArg (fun z : ℂ => ‖z‖) (hilbTensor_inner_mk x x y y)
  simp only [norm_mul, norm_inner_self'] at h
  have h3 : ‖hilbTensorMk x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by rw [h, mul_pow]
  have := congrArg Real.sqrt h3
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at this

/-- The "ket" operator `|·⟩ ⊗ e : H → H ⊗ K`, `x ↦ x ⊗ e`. -/
noncomputable def hilbTensorKet (e : K) : H →L[ℂ] hilbTensor H K :=
  LinearMap.mkContinuous
    { toFun := fun x => hilbTensorMk x e
      map_add' := fun x x' => hilbTensorMk_add_left x x' e
      map_smul' := fun c x => hilbTensorMk_smul_left c x e } ‖e‖
    (fun x => by
      show ‖hilbTensorMk x e‖ ≤ ‖e‖ * ‖x‖
      rw [norm_hilbTensorMk]; exact le_of_eq (mul_comm _ _))

@[simp] theorem hilbTensorKet_apply (e : K) (x : H) :
    hilbTensorKet e x = hilbTensorMk x e := rfl

/-- The adjoint of the ket operator is the slice map `x ⊗ y ↦ ⟪e,y⟫ x`. -/
theorem hilbTensorKet_adjoint_mk (e : K) (x : H) (y : K) :
    ContinuousLinearMap.adjoint (hilbTensorKet (H := H) e) (hilbTensorMk x y) = ⟪e, y⟫ • x := by
  refine ext_inner_right ℂ fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, hilbTensorKet_apply, hilbTensor_inner_mk,
    inner_smul_left, inner_conj_symm]
  ring

/-- `hilbTensor_ext` for a target in an arbitrary universe (needed for `Z = ℂ`). -/
theorem hilbTensor_ext' {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {f g : hilbTensor H K →L[ℂ] Z}
    (h : ∀ x y, f (hilbTensorMk x y) = g (hilbTensorMk x y)) : f = g := by
  have hEq : Set.EqOn ⇑f ⇑g
      (Set.range (fun z : TensorProduct ℂ H K => ((z : hilbTensor H K)))) := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero =>
        simp only []
        rw [show ((0 : TensorProduct ℂ H K) : hilbTensor H K) = 0 from
          UniformSpace.Completion.coe_zero]
        simp
    | tmul x y => exact h x y
    | add z z' hz hz' => simp only [UniformSpace.Completion.coe_add, map_add, hz, hz']
  exact DFunLike.coe_injective
    (Continuous.ext_on hilbTensor_denseRange_coe f.continuous g.continuous hEq)

/-- Adjoints on `H ⊗ K` are determined by elementary tensors. -/
theorem hilbTensor_adjoint_eq {T S : hilbTensor H K →L[ℂ] hilbTensor H K}
    (h : ∀ x₁ x₂ y₁ y₂, ⟪S (hilbTensorMk x₁ x₂), hilbTensorMk y₁ y₂⟫
        = ⟪hilbTensorMk x₁ x₂, T (hilbTensorMk y₁ y₂)⟫) :
    ContinuousLinearMap.adjoint T = S := by
  have hB : ∀ (y₁ : H) (y₂ : K) (x : hilbTensor H K),
      ⟪S x, hilbTensorMk y₁ y₂⟫ = ⟪x, T (hilbTensorMk y₁ y₂)⟫ := by
    intro y₁ y₂
    have hext : ((innerSL ℂ (hilbTensorMk y₁ y₂)).comp S)
        = innerSL ℂ (T (hilbTensorMk y₁ y₂)) := by
      refine hilbTensor_ext' fun x₁ x₂ => ?_
      simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
      have h2 := congrArg (starRingEnd ℂ) (h x₁ x₂ y₁ y₂)
      rwa [inner_conj_symm, inner_conj_symm] at h2
    intro x
    have h3 := congrArg (fun f : hilbTensor H K →L[ℂ] ℂ => f x) hext
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h3
    have h4 := congrArg (starRingEnd ℂ) h3
    rwa [inner_conj_symm, inner_conj_symm] at h4
  have hfull : ∀ x y : hilbTensor H K, ⟪S x, y⟫ = ⟪x, T y⟫ := by
    intro x
    have hext : innerSL ℂ (S x) = (innerSL ℂ x).comp T := by
      refine hilbTensor_ext' fun y₁ y₂ => ?_
      simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
      exact hB y₁ y₂ x
    intro y
    have h3 := congrArg (fun f : hilbTensor H K →L[ℂ] ℂ => f y) hext
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using h3
  exact ((ContinuousLinearMap.eq_adjoint_iff S T).mpr hfull).symm

variable (H K) in
theorem tensorCLM_one : tensorCLM (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  refine hilbTensor_ext fun x y => ?_
  rw [tensorCLM_mk]
  rfl

theorem tensorCLM_mul (a c : H →L[ℂ] H) (b d : K →L[ℂ] K) :
    tensorCLM a b * tensorCLM (K := K) c d = tensorCLM (a * c) (b * d) := by
  refine hilbTensor_ext fun x y => ?_
  rw [ContinuousLinearMap.mul_apply, tensorCLM_mk, tensorCLM_mk, tensorCLM_mk]
  rfl

theorem tensorCLM_adjoint (a : H →L[ℂ] H) (b : K →L[ℂ] K) :
    ContinuousLinearMap.adjoint (tensorCLM a b)
      = tensorCLM (ContinuousLinearMap.adjoint a) (ContinuousLinearMap.adjoint b) := by
  refine hilbTensor_adjoint_eq fun x₁ x₂ y₁ y₂ => ?_
  rw [tensorCLM_mk, tensorCLM_mk, hilbTensor_inner_mk, hilbTensor_inner_mk,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

theorem tensorCLM_star (a : H →L[ℂ] H) (b : K →L[ℂ] K) :
    star (tensorCLM a b) = tensorCLM (K := K) (star a) (star b) := by
  simp only [ContinuousLinearMap.star_eq_adjoint]
  exact tensorCLM_adjoint a b

theorem tensorCLM_add_right (a : H →L[ℂ] H) (b b' : K →L[ℂ] K) :
    tensorCLM a (b + b') = tensorCLM (K := K) a b + tensorCLM a b' := by
  refine hilbTensor_ext fun x y => ?_
  rw [tensorCLM_mk]
  show hilbTensorMk (a x) (b y + b' y) = _
  rw [hilbTensorMk_add_right]
  rw [ContinuousLinearMap.add_apply, tensorCLM_mk, tensorCLM_mk]

theorem tensorCLM_sub_right (a : H →L[ℂ] H) (b b' : K →L[ℂ] K) :
    tensorCLM a (b - b') = tensorCLM (K := K) a b - tensorCLM a b' := by
  refine hilbTensor_ext fun x y => ?_
  rw [tensorCLM_mk]
  show hilbTensorMk (a x) (b y - b' y) = _
  rw [hilbTensorMk_sub_right, ContinuousLinearMap.sub_apply, tensorCLM_mk, tensorCLM_mk]

theorem tensorCLM_zero_right (a : H →L[ℂ] H) :
    tensorCLM a (0 : K →L[ℂ] K) = 0 := by
  refine hilbTensor_ext fun x y => ?_
  rw [tensorCLM_mk]
  show hilbTensorMk (a x) 0 = _
  unfold hilbTensorMk
  rw [TensorProduct.tmul_zero]
  simp

theorem tensorCLM_sum_right {ι : Type*} (a : H →L[ℂ] H) (s : Finset ι)
    (b : ι → (K →L[ℂ] K)) :
    tensorCLM a (∑ i ∈ s, b i) = ∑ i ∈ s, tensorCLM a (b i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using tensorCLM_zero_right (K := K) a
  | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, tensorCLM_add_right, ih]

/-- `Q_e a Q_e* = a ⊗ |e⟩⟨e|`: the slice maps turn `ad` into a tensor factor. -/
theorem conjOperator_ketAdjoint (a : H →L[ℂ] H) (e : K) :
    conjOperator (ContinuousLinearMap.adjoint (hilbTensorKet (H := H) e)) a
      = tensorCLM a (ketbra e e) := by
  refine hilbTensor_ext fun x y => ?_
  show ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint (hilbTensorKet e))
      (a (ContinuousLinearMap.adjoint (hilbTensorKet e) (hilbTensorMk x y))) = _
  rw [ContinuousLinearMap.adjoint_adjoint, hilbTensorKet_adjoint_mk, map_smul,
    hilbTensorKet_apply, hilbTensorMk_smul_left, tensorCLM_mk, ketbra_apply',
    hilbTensorMk_smul_right]

/-- `a ⊗ b ≥ 0` for `a, b ≥ 0`. -/
theorem tensorCLM_nonneg {a : H →L[ℂ] H} {b : K →L[ℂ] K} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ tensorCLM a b := by
  have hca : CFC.sqrt a * CFC.sqrt a = a := CFC.sqrt_mul_sqrt_self a ha
  have hcb : CFC.sqrt b * CFC.sqrt b = b := CFC.sqrt_mul_sqrt_self b hb
  have hsa : star (CFC.sqrt a) = CFC.sqrt a :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  have hsb : star (CFC.sqrt b) = CFC.sqrt b :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq
  have h : tensorCLM a b = star (tensorCLM (CFC.sqrt a) (CFC.sqrt b))
      * tensorCLM (CFC.sqrt a) (CFC.sqrt b) := by
    rw [tensorCLM_star, hsa, hsb, tensorCLM_mul, hca, hcb]
  rw [h]
  exact star_mul_self_nonneg (tensorCLM (CFC.sqrt a) (CFC.sqrt b))

/-- The "co-ket" operator `x ⊗ · : K → H ⊗ K`, `y ↦ x ⊗ y`. -/
noncomputable def hilbTensorKet' (x : H) : K →L[ℂ] hilbTensor H K :=
  LinearMap.mkContinuous
    { toFun := fun y => hilbTensorMk x y
      map_add' := fun y y' => hilbTensorMk_add_right x y y'
      map_smul' := fun c y => hilbTensorMk_smul_right c x y } ‖x‖
    (fun y => by
      show ‖hilbTensorMk x y‖ ≤ ‖x‖ * ‖y‖
      rw [norm_hilbTensorMk])

@[simp] theorem hilbTensorKet'_apply (x : H) (y : K) :
    hilbTensorKet' x y = hilbTensorMk x y := rfl

theorem tensorCLM_mono {a : H →L[ℂ] H} {b b' : K →L[ℂ] K} (ha : 0 ≤ a) (h : b ≤ b') :
    tensorCLM a b ≤ tensorCLM a b' := by
  have h0 : 0 ≤ tensorCLM a (b' - b) := tensorCLM_nonneg ha (sub_nonneg.mpr h)
  rw [tensorCLM_sub_right] at h0
  exact sub_nonneg.mp h0

section Partial

variable {ι : Type u} (bb : HilbertBasis ι ℂ K)

/-- The partial-sum projections `P_F = ∑_{i∈F} |bᵢ⟩⟨bᵢ|` of a Hilbert basis. -/
noncomputable def basisProj (F : Finset ι) : K →L[ℂ] K :=
  ∑ i ∈ F, ketbra (bb i) (bb i)

theorem isStarProjection_basisProj (F : Finset ι) : IsStarProjection (basisProj bb F) :=
  isStarProjection_sum F _ (fun i => isStarProjection_ketbra (bb.orthonormal.1 i))
    (fun i _ j _ hij => ketbra_orth bb.orthonormal hij)

theorem basisProj_apply (F : Finset ι) (y : K) :
    basisProj bb F y = ∑ i ∈ F, ⟪bb i, y⟫ • bb i := by
  rw [basisProj, ContinuousLinearMap.sum_apply]
  rfl

theorem tendsto_basisProj (y : K) :
    Filter.Tendsto (fun F : Finset ι => basisProj bb F y) atTop (𝓝 y) := by
  have h : HasSum (fun i => ⟪bb i, y⟫ • bb i) y := by
    simpa only [HilbertBasis.repr_apply_apply] using bb.hasSum_repr y
  simp only [basisProj_apply]
  exact h

variable (H)

theorem tensorProj_mk (F : Finset ι) (x : H) (y : K) :
    tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) (hilbTensorMk x y)
      = hilbTensorMk x (basisProj bb F y) := by
  rw [tensorCLM_mk]; rfl

theorem tensorProj_star (F : Finset ι) :
    star (tensorCLM (1 : H →L[ℂ] H) (basisProj bb F))
      = tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) := by
  rw [tensorCLM_star, star_one, (isStarProjection_basisProj bb F).2]

theorem tensorProj_idem (F : Finset ι) :
    tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) * tensorCLM (1 : H →L[ℂ] H) (basisProj bb F)
      = tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) := by
  rw [tensorCLM_mul, one_mul, (isStarProjection_basisProj bb F).1]

theorem norm_tensorProj_le (F : Finset ι) (η : hilbTensor H K) :
    ‖tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) η‖ ≤ ‖η‖ := by
  set R := tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) with hR
  have hsa : ContinuousLinearMap.adjoint R = R := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact tensorProj_star H bb F
  have hidem : R (R η) = R η := by
    have h2 := congrArg (fun T : hilbTensor H K →L[ℂ] hilbTensor H K => T η)
      (tensorProj_idem H bb F)
    simpa [ContinuousLinearMap.mul_apply] using h2
  have h1 : (⟪R η, R η⟫ : ℂ) = ⟪R η, η⟫ := by
    have h := ContinuousLinearMap.adjoint_inner_left R η (R η)
    rw [hsa] at h
    rw [← h, hidem]
  have h2 : ‖R η‖ ^ 2 ≤ ‖R η‖ * ‖η‖ := by
    rw [← norm_inner_self' (R η), h1]
    exact norm_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (R η)) with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith [h2]

theorem tensorProj_conj (a : H →L[ℂ] H) (F : Finset ι) :
    tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) * tensorCLM a 1
        * tensorCLM (1 : H →L[ℂ] H) (basisProj bb F)
      = tensorCLM a (basisProj bb F) := by
  rw [tensorCLM_mul, tensorCLM_mul, one_mul, mul_one, mul_one,
    (isStarProjection_basisProj bb F).1]

theorem basisProj_nonneg (F : Finset ι) : (0 : K →L[ℂ] K) ≤ basisProj bb F := by
  have h := isStarProjection_basisProj bb F
  have h2 : basisProj bb F = star (basisProj bb F) * basisProj bb F := by rw [h.2, h.1]
  rw [h2]
  exact star_mul_self_nonneg (basisProj bb F)

theorem basisProj_mono {F G : Finset ι} (h : F ⊆ G) :
    basisProj bb F ≤ basisProj bb G := by
  classical
  have hnn : ∀ i : ι, (0 : K →L[ℂ] K) ≤ ketbra (bb i) (bb i) := by
    intro i
    have hp := isStarProjection_ketbra (bb.orthonormal.1 i)
    have h2 : ketbra (bb i) (bb i) = star (ketbra (bb i) (bb i)) * ketbra (bb i) (bb i) := by
      rw [hp.2, hp.1]
    rw [h2]
    exact star_mul_self_nonneg _
  have hsd : ∑ i ∈ G \ F, ketbra (bb i) (bb i) + ∑ i ∈ F, ketbra (bb i) (bb i)
      = ∑ i ∈ G, ketbra (bb i) (bb i) := Finset.sum_sdiff h
  have h0 : (0 : K →L[ℂ] K) ≤ ∑ i ∈ G \ F, ketbra (bb i) (bb i) :=
    Finset.sum_nonneg fun i _ => hnn i
  rw [basisProj, basisProj, ← hsd]
  simpa using add_le_add_right h0 (∑ i ∈ F, ketbra (bb i) (bb i))

theorem tendsto_tensorProj (η : hilbTensor H K) :
    Filter.Tendsto (fun F : Finset ι => tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) η)
      atTop (𝓝 η) := by
  classical
  -- first on the algebraic tensor product
  have halg : ∀ z : TensorProduct ℂ H K,
      Filter.Tendsto (fun F : Finset ι =>
        tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) ((z : hilbTensor H K)))
        atTop (𝓝 ((z : hilbTensor H K))) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [show ((0 : TensorProduct ℂ H K) : hilbTensor H K) = 0 from
          UniformSpace.Completion.coe_zero]
        simpa using tendsto_const_nhds (x := (0 : hilbTensor H K))
          (f := (atTop : Filter (Finset ι)))
    | tmul x y =>
        have hmk : ((x ⊗ₜ[ℂ] y : TensorProduct ℂ H K) : hilbTensor H K)
            = hilbTensorMk x y := rfl
        rw [hmk]
        have := ((hilbTensorKet' (K := K) x).continuous.tendsto y).comp
          (tendsto_basisProj bb y)
        simpa only [Function.comp_def, hilbTensorKet'_apply, tensorProj_mk] using this
    | add z z' hz hz' =>
        rw [UniformSpace.Completion.coe_add]
        simpa only [map_add] using hz.add hz'
  -- then everywhere, by density and the uniform bound
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨z, hz⟩ := Metric.denseRange_iff.mp
    (hilbTensor_denseRange_coe (H := H) (K := K)) η (ε / 3) (by linarith)
  have hzη : ‖η - ((z : hilbTensor H K))‖ < ε / 3 := by
    rw [← dist_eq_norm]; exact hz
  obtain ⟨F₀, hF₀⟩ := Metric.tendsto_atTop.mp (halg z) (ε / 3) (by linarith)
  refine ⟨F₀, fun F hF => ?_⟩
  have h1 : ‖tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) ((z : hilbTensor H K))
      - ((z : hilbTensor H K))‖ < ε / 3 := by
    rw [← dist_eq_norm]; exact hF₀ F hF
  have h2 : ‖tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) (η - ((z : hilbTensor H K)))‖
      < ε / 3 := lt_of_le_of_lt (norm_tensorProj_le H bb F _) hzη
  rw [dist_eq_norm]
  have hsplit : tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) η - η
      = tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) (η - ((z : hilbTensor H K)))
        + (tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) ((z : hilbTensor H K))
            - ((z : hilbTensor H K)))
        + (((z : hilbTensor H K)) - η) := by
    rw [map_sub]; abel
  rw [hsplit]
  have h3 : ‖((z : hilbTensor H K)) - η‖ < ε / 3 := by
    rw [norm_sub_rev]; exact hzη
  calc ‖_ + _ + _‖ ≤ ‖tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) (η - ((z : hilbTensor H K)))
          + (tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) ((z : hilbTensor H K))
            - ((z : hilbTensor H K)))‖ + ‖((z : hilbTensor H K)) - η‖ := norm_add_le _ _
    _ ≤ ‖tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) (η - ((z : hilbTensor H K)))‖
          + ‖tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) ((z : hilbTensor H K))
            - ((z : hilbTensor H K))‖ + ‖((z : hilbTensor H K)) - η‖ := by
        gcongr; exact norm_add_le _ _
    _ < ε := by linarith

end Partial

end KrausAux

section UWAux

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem uwTendsto_smul' {ι : Type*} {l : Filter ι} {f : ι → A} {a : A} (c : ℂ)
    (h : UWTendsto f l a) : UWTendsto (fun i => c • f i) l (c • a) := by
  rw [uwTendsto_iff] at h ⊢
  intro ω
  have h1 := (h ω).const_mul c
  have hrw : ∀ b : A, (ω (c • b) : ℂ) = c * ω b := fun b =>
    (map_smul ω.toPositiveLinearMap c b).trans (smul_eq_mul _ _)
  simp only [hrw]
  exact h1

theorem uwTendsto_add' {ι : Type*} {l : Filter ι} {f g : ι → A} {a b : A}
    (hf : UWTendsto f l a) (hg : UWTendsto g l b) :
    UWTendsto (fun i => f i + g i) l (a + b) := by
  rw [uwTendsto_iff] at hf hg ⊢
  intro ω
  simpa only [npFunctional_add] using (hf ω).add (hg ω)

/-- A monotone net of self-adjoint elements converges ultraweakly to its supremum
(**44VI** transported from the index set `D` to an arbitrary directed index). -/
theorem uwTendsto_of_monotone_isLUB [VonNeumannAlgebra A] {ι : Type*} [Nonempty ι]
    [SemilatticeSup ι] (x : ι → selfAdjoint A) (hmono : Monotone x) (L : selfAdjoint A)
    (hlub : IsLUB (Set.range x) L) :
    UWTendsto (fun i => ((x i : A))) atTop (L : A) := by
  set D : Set (selfAdjoint A) := Set.range x with hD
  have hne : D.Nonempty := Set.range_nonempty x
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨x (i ⊔ j), ⟨i ⊔ j, rfl⟩, hmono le_sup_left, hmono le_sup_right⟩
  have hh : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, ⟨L, hlub.1⟩⟩
  have hsup : dirSup D hh = L := (isLUB_dirSup D hh).unique hlub
  have hbase := vna_supremum_uwlimit D hh
  rw [hsup] at hbase
  have hg : Filter.Tendsto (fun i : ι => (⟨x i, ⟨i, rfl⟩⟩ : D)) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun d => ?_
    obtain ⟨i₀, hi₀⟩ := d.2
    refine ⟨i₀, fun j hj => ?_⟩
    show d ≤ (⟨x j, ⟨j, rfl⟩⟩ : D)
    rw [← Subtype.coe_le_coe, ← hi₀]
    exact hmono hj
  exact hbase.comp hg

end UWAux


/-! ## Parsec 1380: consequences of Stinespring

**138I** (dils.tex:597): introduction — nothing to formalize.
**138III**–**138V** are the proof of **138II** — not converted. -/

section TypeI

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **138II** (`nmiu-between-type-I`, dils.tex:608, Proposition): every
non-zero nmiu-map `ϱ : B(ℋ) → B(𝒦)` between the bounded operators on
Hilbert spaces is of the form `ϱ(a) = U* (a ⊗ 1) U` for some Hilbert space
`𝒦'` and unitary `U : 𝒦 → ℋ ⊗ 𝒦'`. -/
theorem nmiu_between_type_I (ϱ : NMIUMap (H →L[ℂ] H) (K →L[ℂ] K))
    (hnz : ∃ a, ϱ a ≠ 0) :
    ∃ (K' : Type u) (_ : NormedAddCommGroup K') (_ : InnerProductSpace ℂ K')
      (_ : CompleteSpace K') (U : K →L[ℂ] hilbTensor H K'),
      (ContinuousLinearMap.adjoint U).comp U = 1 ∧
      U.comp (ContinuousLinearMap.adjoint U) = 1 ∧
      ∀ a : H →L[ℂ] H, ϱ a = conjOperator U (tensorCLM a 1) := by
  by_cases hH : Nontrivial H
  · obtain ⟨x, hx⟩ := @exists_ne H hH 0
    have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    refine nmiu_between_type_I_aux ϱ (‖x‖⁻¹ • x) ?_
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn]
  · -- `ℋ = 0` forces `B(ℋ) = 0`, hence `1 = ϱ(1) = ϱ(0) = 0` in `B(𝒦)`, hence
    -- `ϱ = 0`, contradicting the hypothesis.
    rw [not_nontrivial_iff_subsingleton] at hH
    exfalso
    obtain ⟨a, ha⟩ := hnz
    have h1 : (1 : H →L[ℂ] H) = 0 := by
      ext z
      exact Subsingleton.elim _ _
    have h1K : (1 : K →L[ℂ] K) = 0 := by
      have h := map_one ϱ.toStarAlgHom
      rw [h1, map_zero] at h
      exact h.symm
    exact ha (by rw [show ϱ a = ϱ a * 1 from (mul_one _).symm, h1K, mul_zero])

/-- Normalising a non-zero vector, with a *complex* scalar (so that the
`ℂ`-linear maps below apply to it). -/
private theorem norm_normalize {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {v : E} (hv : v ≠ 0) : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- **138VI** (`typei-inner-auto`, dils.tex:719, Corollary): the
nmiu-isomorphisms `B(ℋ) → B(𝒦)` are precisely the maps `ad_U` for a unitary
`U : 𝒦 → ℋ`. -/
theorem typei_inner_auto (ϱ : NMIUMap (H →L[ℂ] H) (K →L[ℂ] K)) :
    Function.Bijective ⇑ϱ ↔
      ∃ U : K →L[ℂ] H,
        (ContinuousLinearMap.adjoint U).comp U = 1 ∧
        U.comp (ContinuousLinearMap.adjoint U) = 1 ∧
        ∀ a : H →L[ℂ] H, ϱ a = conjOperator U a := by
  have hcoe : ⇑ϱ = ⇑ϱ.toStarAlgHom := rfl
  have hmapadd : ∀ b b' : H →L[ℂ] H, ϱ (b + b') = ϱ b + ϱ b' := fun b b' => by
    simpa [hcoe] using map_add ϱ.toStarAlgHom b b'
  have hmapsmul : ∀ (c : ℂ) (b : H →L[ℂ] H), ϱ (c • b) = c • ϱ b := fun c b => by
    simpa [hcoe] using map_smul ϱ.toStarAlgHom c b
  have hmapmul : ∀ b b' : H →L[ℂ] H, ϱ (b * b') = ϱ b * ϱ b' := fun b b' => by
    simpa [hcoe] using map_mul ϱ.toStarAlgHom b b'
  have hmapstar : ∀ b : H →L[ℂ] H, ϱ (star b) = star (ϱ b) := fun b => by
    simpa [hcoe] using map_star ϱ.toStarAlgHom b
  have hmulapp : ∀ (b b' : H →L[ℂ] H) (y : K), ϱ b (ϱ b' y) = ϱ (b * b') y := by
    intro b b' y; rw [hmapmul]; rfl
  have hadj : ∀ b : H →L[ℂ] H, ContinuousLinearMap.adjoint (ϱ b) = ϱ (star b) := by
    intro b; rw [← ContinuousLinearMap.star_eq_adjoint, hmapstar]
  constructor
  · intro hbij
    by_cases hH : Nontrivial H
    · -- pick a unit vector `e₀` and the projection `p₀ = |e₀⟩⟨e₀|`
      obtain ⟨x₁, hx₁⟩ := @exists_ne H hH 0
      obtain ⟨e₀, he₀⟩ : ∃ e₀ : H, ‖e₀‖ = 1 := ⟨_, norm_normalize hx₁⟩
      have he₀ne : e₀ ≠ 0 := fun h => one_ne_zero (by rw [← he₀, h, norm_zero])
      have he₀e₀ : ⟪e₀, e₀⟫ = (1 : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K, he₀]; norm_num
      set p₀ : H →L[ℂ] H := ketbra e₀ e₀ with hp₀
      have hp₀idem : p₀ * p₀ = p₀ := by rw [hp₀, ketbra_mul, he₀e₀, one_smul]
      -- `ϱ(p₀) ≠ 0` by injectivity, so `𝒦' = ϱ(p₀)𝒦` has a unit vector `d₀`
      have hmapzero : ϱ (0 : H →L[ℂ] H) = 0 := by
        simpa [hcoe] using map_zero ϱ.toStarAlgHom
      have hp₀ne : ϱ p₀ ≠ 0 := by
        intro h
        have h0 : p₀ = 0 := hbij.1 (by rw [h, hmapzero])
        have hz := congrArg (fun T : H →L[ℂ] H => T e₀) h0
        simp only [hp₀, ketbra_apply', he₀e₀, one_smul,
          ContinuousLinearMap.zero_apply] at hz
        exact he₀ne hz
      obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ, ϱ p₀ ξ ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hp₀ne (ContinuousLinearMap.ext hc)
      obtain ⟨d₀, hd₀, hfix⟩ : ∃ d₀ : K, ‖d₀‖ = 1 ∧ ϱ p₀ d₀ = d₀ :=
        ⟨((‖ϱ p₀ ξ₀‖⁻¹ : ℝ) : ℂ) • ϱ p₀ ξ₀, norm_normalize hξ₀, by
          rw [map_smul, hmulapp, hp₀idem]⟩
      have hd₀d₀ : ⟪d₀, d₀⟫ = (1 : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K, hd₀]; norm_num
      -- the fixed space of `ϱ(p₀)` is the line `ℂ d₀`
      have hline : ∀ η : K, ϱ p₀ η = η → η = ⟪d₀, η⟫ • d₀ := by
        intro η hη
        set ζ : K := η - ⟪d₀, η⟫ • d₀ with hζ
        have hζfix : ϱ p₀ ζ = ζ := by rw [hζ, map_sub, map_smul, hη, hfix]
        have hζorth : ⟪d₀, ζ⟫ = 0 := by
          rw [hζ, inner_sub_right, inner_smul_right, hd₀d₀, mul_one, sub_self]
        by_contra hne
        have hζne : ζ ≠ 0 := fun h => hne (by rw [← sub_eq_zero, ← hζ, h])
        obtain ⟨d, hd, hdfix, hdorth⟩ :
            ∃ d : K, ‖d‖ = 1 ∧ ϱ p₀ d = d ∧ ⟪d₀, d⟫ = (0 : ℂ) :=
          ⟨((‖ζ‖⁻¹ : ℝ) : ℂ) • ζ, norm_normalize hζne, by rw [map_smul, hζfix],
            by rw [inner_smul_right, hζorth, mul_zero]⟩
        obtain ⟨a, ha⟩ := hbij.2 (ketbra d d₀)
        -- `p₀ a p₀ = ⟪e₀, a e₀⟫ p₀`, so `d = ϱ(p₀ a p₀) d₀ = ⟪e₀,a e₀⟫ d₀`
        have hpap : p₀ * a * p₀ = ⟪e₀, a e₀⟫ • p₀ := by
          rw [hp₀, ketbra_mul_op, ketbra_mul, ContinuousLinearMap.adjoint_inner_left]
        have h1 : ϱ (p₀ * a * p₀) d₀ = d := by
          rw [← hmulapp, ← hmulapp, ha, hfix]
          show ϱ p₀ (⟪d₀, d₀⟫ • d) = d
          rw [hd₀d₀, one_smul, hdfix]
        have h2 : ϱ (p₀ * a * p₀) d₀ = ⟪e₀, a e₀⟫ • d₀ := by
          rw [hpap, hmapsmul]
          show ⟪e₀, a e₀⟫ • ϱ p₀ d₀ = _
          rw [hfix]
        have h3 : d = ⟪e₀, a e₀⟫ • d₀ := by rw [← h1, h2]
        have h4 : (0 : ℂ) = ⟪e₀, a e₀⟫ := by
          rw [← hdorth, h3, inner_smul_right, hd₀d₀, mul_one]
        rw [← h4, zero_smul] at h3
        rw [h3, norm_zero] at hd
        exact one_ne_zero hd.symm
      -- the isometry `V x = ϱ(|x⟩⟨e₀|) d₀`
      set Vl : H →ₗ[ℂ] K :=
        { toFun := fun x => ϱ (ketbra x e₀) d₀
          map_add' := fun x x' => by rw [ketbra_add_left, hmapadd]; rfl
          map_smul' := fun c x => by rw [ketbra_smul_left, hmapsmul]; rfl } with hVl
      have hVinner : ∀ x y : H, ⟪Vl x, Vl y⟫ = ⟪x, y⟫ := by
        intro x y
        show ⟪ϱ (ketbra x e₀) d₀, ϱ (ketbra y e₀) d₀⟫ = _
        rw [← ContinuousLinearMap.adjoint_inner_right, hadj, hmulapp, ketbra_star,
          ketbra_mul, ← hp₀, hmapsmul]
        show ⟪d₀, ⟪x, y⟫ • ϱ p₀ d₀⟫ = _
        rw [hfix, inner_smul_right, hd₀d₀, mul_one]
      have hVnorm : ∀ x : H, ‖Vl x‖ = ‖x‖ := by
        intro x
        have h2 : ‖Vl x‖ ^ 2 = ‖x‖ ^ 2 := by
          rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hVinner]
        have := congrArg Real.sqrt h2
        rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
      set V : H →L[ℂ] K := Vl.mkContinuousOfExistsBound ⟨1, fun x => by
        rw [hVnorm]; simp⟩ with hVdef
      have hVapp : ∀ x : H, V x = ϱ (ketbra x e₀) d₀ := fun x => rfl
      have hVnorm' : ∀ x : H, ‖V x‖ = ‖x‖ := hVnorm
      -- `V` is surjective, by the same argument as in 138II
      set M : Submodule ℂ K := LinearMap.range (V : H →ₗ[ℂ] K) with hMdef
      have hMrange : (M : Set K) = Set.range ⇑V := LinearMap.coe_range _
      have hViso : Isometry ⇑V := AddMonoidHomClass.isometry_of_norm V hVnorm'
      have hMcomplete : IsComplete (M : Set K) := by
        rw [hMrange]; exact hViso.isUniformInducing.isComplete_range
      haveI : CompleteSpace ↥M := hMcomplete.completeSpace_coe
      have hMtop : ∀ y : K, y ∈ M :=
        nmiu_forall_mem ϱ e₀ he₀ M (by
          intro x η hη
          have hηl : η = ⟪d₀, η⟫ • d₀ := hline η hη
          refine ⟨⟪d₀, η⟫ • x, ?_⟩
          show V (⟪d₀, η⟫ • x) = ϱ (ketbra x e₀) η
          rw [map_smul, hVapp, ← map_smul (ϱ (ketbra x e₀)), ← hηl])
      have hVsurj : Function.Surjective ⇑V := fun y => hMtop y
      have hVadjV : (ContinuousLinearMap.adjoint V).comp V = 1 := by
        refine ContinuousLinearMap.ext fun v => ?_
        refine ext_inner_left ℂ fun y => ?_
        show ⟪y, ContinuousLinearMap.adjoint V (V v)⟫ = ⟪y, (1 : H →L[ℂ] H) v⟫
        rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.one_apply]
        exact hVinner y v
      have hVadjV' : ∀ v, ContinuousLinearMap.adjoint V (V v) = v := fun v => by
        have := congrArg (fun T : H →L[ℂ] H => T v) hVadjV
        simpa using this
      have hVVadj : V.comp (ContinuousLinearMap.adjoint V) = 1 := by
        refine ContinuousLinearMap.ext fun y => ?_
        obtain ⟨v, rfl⟩ := hVsurj y
        show V (ContinuousLinearMap.adjoint V (V v)) = _
        rw [hVadjV']
        rfl
      exact ⟨ContinuousLinearMap.adjoint V, by
          rw [ContinuousLinearMap.adjoint_adjoint]; exact hVVadj, by
          rw [ContinuousLinearMap.adjoint_adjoint]; exact hVadjV, fun a => by
        have hintertwine : V.comp a = (ϱ a).comp V := by
          refine ContinuousLinearMap.ext fun x => ?_
          show V (a x) = ϱ a (V x)
          rw [hVapp, hVapp, hmulapp, mul_ketbra]
        show ϱ a = (ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint V)).comp
          (a.comp (ContinuousLinearMap.adjoint V))
        rw [ContinuousLinearMap.adjoint_adjoint, ← ContinuousLinearMap.comp_assoc,
          hintertwine, ContinuousLinearMap.comp_assoc, hVVadj]
        exact (mul_one (ϱ a)).symm⟩
    · -- `ℋ = 0`: then `B(ℋ) = 0`, so `1 = ϱ(1) = 0` in `B(𝒦)` and everything is `0`
      rw [not_nontrivial_iff_subsingleton] at hH
      have h1 : (1 : H →L[ℂ] H) = 0 := by
        ext z; exact Subsingleton.elim _ _
      have h1K : (1 : K →L[ℂ] K) = 0 := by
        have h := map_one ϱ.toStarAlgHom
        rw [h1, map_zero] at h
        exact h.symm
      have hsubK : ∀ T : K →L[ℂ] K, T = 0 := fun T => by
        rw [show T = T * 1 from (mul_one _).symm, h1K, mul_zero]
      have hsubH : ∀ T : H →L[ℂ] H, T = 0 := fun T => by
        rw [show T = T * 1 from (mul_one _).symm, h1, mul_zero]
      exact ⟨0, by rw [hsubK ((ContinuousLinearMap.adjoint 0).comp 0), h1K],
        by rw [hsubH ((0 : K →L[ℂ] H).comp (ContinuousLinearMap.adjoint 0)), h1],
        fun a => by rw [hsubK (ϱ a), hsubK (conjOperator 0 a)]⟩
  · rintro ⟨U, hUU, hUU', hϱ⟩
    have hA : ∀ x : H, U (ContinuousLinearMap.adjoint U x) = x := fun x => by
      have h := congrArg (fun T : H →L[ℂ] H => T x) hUU'
      simpa using h
    have hB : ∀ v : K, ContinuousLinearMap.adjoint U (U v) = v := fun v => by
      have h := congrArg (fun T : K →L[ℂ] K => T v) hUU
      simpa using h
    constructor
    · intro a b hab
      have h : U.comp ((conjOperator U a).comp (ContinuousLinearMap.adjoint U))
          = U.comp ((conjOperator U b).comp (ContinuousLinearMap.adjoint U)) := by
        rw [← hϱ a, ← hϱ b, hab]
      have hrec : ∀ c : H →L[ℂ] H,
          U.comp ((conjOperator U c).comp (ContinuousLinearMap.adjoint U)) = c := by
        intro c
        refine ContinuousLinearMap.ext fun x => ?_
        show U (ContinuousLinearMap.adjoint U (c (U (ContinuousLinearMap.adjoint U x)))) = c x
        rw [hA, hA]
      rw [hrec a, hrec b] at h
      exact h
    · intro c
      refine ⟨U.comp (c.comp (ContinuousLinearMap.adjoint U)), ?_⟩
      rw [hϱ]
      refine ContinuousLinearMap.ext fun v => ?_
      show ContinuousLinearMap.adjoint U (U (c (ContinuousLinearMap.adjoint U (U v)))) = c v
      rw [hB, hB]

/-- **138VII** (`physics-stinespring`, dils.tex:725, Exercise*): for every
ncp-map `φ : B(ℋ) → B(𝒦)` there are a Hilbert space `𝒦'` and a bounded
operator `V : 𝒦 → ℋ ⊗ 𝒦'` such that `φ(a) = V* (a ⊗ 1) V`.

(The second half — every quantum channel on trace-class operators is of the
form `Φ(ϱ) = Tr_{𝒦'}[U* (ϱ ⊗ |v₀⟩⟨v₀|) U]` — is not converted: trace-class
operators are not yet available in this formalization.) -/
theorem physics_stinespring (φ : NCPMap (H →L[ℂ] H) (K →L[ℂ] K)) :
    ∃ (K' : Type u) (_ : NormedAddCommGroup K') (_ : InnerProductSpace ℂ K')
      (_ : CompleteSpace K') (V : K →L[ℂ] hilbTensor H K'),
      ∀ a : H →L[ℂ] H, φ a = conjOperator V (tensorCLM a 1) := by
  -- Stinespring (**135IV**) followed by **138II**, as the exercise directs.
  set f : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K) := φ.toCompletelyPositiveMap.toLinearMap with hf
  have hcp : IsCompletelyPositiveMap f :=
    (cp_iff f).out 1 0 |>.mp fun N M hM =>
      φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hnn : PreservesDirSups ⇑f := φ.preservesDirSups'
  obtain ⟨𝒦, h1, h2, h3, ϱ, V₀, heq⟩ := stinespring_normal f hcp hnn
  letI := h1; letI := h2; letI := h3
  by_cases hz : ∃ a, ϱ a ≠ 0
  · obtain ⟨K', i1, i2, i3, U, -, hUU, hU⟩ := nmiu_between_type_I ϱ hz
    refine ⟨K', i1, i2, i3, U.comp V₀, fun a => ?_⟩
    have h := heq a
    rw [hU a] at h
    rw [show (φ a) = f a from rfl, h]
    show (ContinuousLinearMap.adjoint V₀).comp
        (((ContinuousLinearMap.adjoint U).comp ((tensorCLM a 1).comp U)).comp V₀) = _
    show _ = (ContinuousLinearMap.adjoint (U.comp V₀)).comp ((tensorCLM a 1).comp (U.comp V₀))
    rw [ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_assoc]
  · -- the dilating space is trivial, so `φ = 0`
    push_neg at hz
    refine ⟨↥(⊥ : Submodule ℂ K), inferInstance, inferInstance, inferInstance, 0, fun a => ?_⟩
    have h := heq a
    rw [hz a] at h
    rw [show (φ a) = f a from rfl, h]
    show (ContinuousLinearMap.adjoint V₀).comp ((0 : 𝒦 →L[ℂ] 𝒦).comp V₀) = _
    show _ = (ContinuousLinearMap.adjoint (0 : K →L[ℂ] hilbTensor H _)).comp
      ((tensorCLM a 1).comp 0)
    simp

/-- **138VIII** (`kraus-exercise`, dils.tex:742, Exercise* (Kraus'
decomposition)): every ncp-map `φ : B(ℋ) → B(𝒦)` is of the form
`φ(a) = ∑ᵢ Vᵢ* a Vᵢ` for bounded operators `Vᵢ : 𝒦 → ℋ` whose partial sums
`∑ᵢ Vᵢ* Vᵢ` are bounded, the sum converging ultraweakly. -/
theorem kraus_decomposition (φ : NCPMap (H →L[ℂ] H) (K →L[ℂ] K)) :
    ∃ (ι : Type u) (V : ι → (K →L[ℂ] H)),
      (∃ M : ℝ, ∀ s : Finset ι, ‖∑ i ∈ s, conjOperator (V i) 1‖ ≤ M) ∧
      ∀ a : H →L[ℂ] H,
        UWTendsto (fun s : Finset ι => ∑ i ∈ s, conjOperator (V i) a)
          atTop (φ a) := by
  classical
  obtain ⟨K', i1, i2, i3, V₀, hV₀⟩ := physics_stinespring φ
  letI := i1; letI := i2; letI := i3
  obtain ⟨sset, bb, -⟩ := exists_hilbertBasis ℂ K'
  set f : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K) := φ.toCompletelyPositiveMap.toLinearMap with hf
  have hfφ : ∀ a, φ a = f a := fun _ => rfl
  -- conjugation by a composite
  have hcc : ∀ (S : hilbTensor H K' →L[ℂ] H) (a : H →L[ℂ] H),
      conjOperator (S.comp V₀) a = conjOperator V₀ (conjOperator S a) := by
    intro S a
    show (ContinuousLinearMap.adjoint (S.comp V₀)).comp (a.comp (S.comp V₀))
        = (ContinuousLinearMap.adjoint V₀).comp
            (((ContinuousLinearMap.adjoint S).comp (a.comp S)).comp V₀)
    rw [ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_assoc]
  -- `ad_{V₀}` is positive and monotone
  have hadpos : ∀ T : hilbTensor H K' →L[ℂ] hilbTensor H K',
      0 ≤ T → 0 ≤ conjOperator V₀ T := by
    intro T hT
    rw [ContinuousLinearMap.nonneg_iff_isPositive] at hT ⊢
    exact hT.adjoint_conj V₀
  have hadmono : ∀ T T' : hilbTensor H K' →L[ℂ] hilbTensor H K',
      T ≤ T' → conjOperator V₀ T ≤ conjOperator V₀ T' := by
    intro T T' h
    have h0 := hadpos (T' - T) (sub_nonneg.mpr h)
    rw [map_sub] at h0
    exact sub_nonneg.mp h0
  set W : ↥sset → (K →L[ℂ] H) :=
    fun i => (ContinuousLinearMap.adjoint (hilbTensorKet (H := H) (bb i))).comp V₀ with hW
  -- the partial sums are the conjugates of `a ⊗ P_F`
  have hsum : ∀ (F : Finset ↥sset) (a : H →L[ℂ] H),
      ∑ i ∈ F, conjOperator (W i) a = conjOperator V₀ (tensorCLM a (basisProj bb F)) := by
    intro F a
    rw [basisProj, tensorCLM_sum_right, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW]
    simp only []
    rw [hcc, conjOperator_ketAdjoint]
  refine ⟨↥sset, W, ⟨‖conjOperator V₀ (1 : hilbTensor H K' →L[ℂ] hilbTensor H K')‖,
    fun F => ?_⟩, ?_⟩
  · -- the norm bound
    rw [hsum]
    refine CStarAlgebra.norm_le_norm_of_nonneg_of_le
      (hadpos _ (tensorCLM_nonneg zero_le_one (basisProj_nonneg bb F))) ?_
    have h1 : tensorCLM (1 : H →L[ℂ] H) (basisProj bb F)
        ≤ (1 : hilbTensor H K' →L[ℂ] hilbTensor H K') := by
      have := tensorCLM_mono (a := (1 : H →L[ℂ] H)) zero_le_one
        (isStarProjection_basisProj bb F).le_one
      rwa [tensorCLM_one] at this
    exact hadmono _ _ h1
  · -- the ultraweak convergence
    -- (i) the positive case, by monotone convergence to the supremum
    have hpos : ∀ a : H →L[ℂ] H, 0 ≤ a →
        UWTendsto (fun F : Finset ↥sset => ∑ i ∈ F, conjOperator (W i) a) atTop (φ a) := by
      intro a ha
      have hnn : ∀ F : Finset ↥sset,
          0 ≤ conjOperator V₀ (tensorCLM a (basisProj bb F)) := fun F =>
        hadpos _ (tensorCLM_nonneg ha (basisProj_nonneg bb F))
      have hsaT : ∀ F : Finset ↥sset,
          IsSelfAdjoint (conjOperator V₀ (tensorCLM a (basisProj bb F))) := fun F =>
        IsSelfAdjoint.of_nonneg (hnn F)
      have hφa : (φ a : K →L[ℂ] K) = conjOperator V₀ (tensorCLM a 1) := hV₀ a
      have hsaφ : IsSelfAdjoint (φ a : K →L[ℂ] K) := by
        rw [hφa]
        exact IsSelfAdjoint.of_nonneg (hadpos _ (tensorCLM_nonneg ha zero_le_one))
      -- monotone
      have hmono : Monotone fun F : Finset ↥sset =>
          (⟨conjOperator V₀ (tensorCLM a (basisProj bb F)), hsaT F⟩ :
            selfAdjoint (K →L[ℂ] K)) := by
        intro F G hFG
        rw [← Subtype.coe_le_coe]
        exact hadmono _ _ (tensorCLM_mono ha (basisProj_mono bb hFG))
      -- the quadratic-form limit
      have hlim : ∀ ξ : K,
          Filter.Tendsto (fun F : Finset ↥sset =>
            (⟪(conjOperator V₀ (tensorCLM a (basisProj bb F))) ξ, ξ⟫ : ℂ))
            atTop (𝓝 (⟪(φ a : K →L[ℂ] K) ξ, ξ⟫ : ℂ)) := by
        intro ξ
        set η : hilbTensor H K' := V₀ ξ with hη
        have hRsa : ∀ F : Finset ↥sset,
            ContinuousLinearMap.adjoint (tensorCLM (1 : H →L[ℂ] H) (basisProj bb F))
              = tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) := by
          intro F
          rw [← ContinuousLinearMap.star_eq_adjoint]
          exact tensorProj_star H bb F
        have hkey : ∀ F : Finset ↥sset,
            (⟪(conjOperator V₀ (tensorCLM a (basisProj bb F))) ξ, ξ⟫ : ℂ)
              = ⟪(tensorCLM a 1) (tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) η),
                  tensorCLM (1 : H →L[ℂ] H) (basisProj bb F) η⟫ := by
          intro F
          have h1 : (conjOperator V₀ (tensorCLM a (basisProj bb F))) ξ
              = ContinuousLinearMap.adjoint V₀ ((tensorCLM a (basisProj bb F)) η) := rfl
          rw [h1, ContinuousLinearMap.adjoint_inner_left]
          rw [← tensorProj_conj H bb a F]
          simp only [ContinuousLinearMap.mul_apply]
          rw [← hRsa F]
          rw [ContinuousLinearMap.adjoint_inner_left, hRsa F]
        have hcont : Continuous fun ζ : hilbTensor H K' => (⟪(tensorCLM a 1) ζ, ζ⟫ : ℂ) := by
          exact Continuous.inner ((tensorCLM a 1).continuous) continuous_id
        have hlim0 := (hcont.tendsto η).comp (tendsto_tensorProj H bb η)
        simp only [Function.comp_def] at hlim0
        have hφ' : (⟪(φ a : K →L[ℂ] K) ξ, ξ⟫ : ℂ) = ⟪(tensorCLM a 1) η, η⟫ := by
          rw [hφa]
          have : (conjOperator V₀ (tensorCLM a 1)) ξ
              = ContinuousLinearMap.adjoint V₀ ((tensorCLM a 1) η) := rfl
          rw [this, ContinuousLinearMap.adjoint_inner_left]
        rw [hφ']
        simpa only [hkey] using hlim0
      -- the supremum
      have hlub : IsLUB (Set.range fun F : Finset ↥sset =>
          (⟨conjOperator V₀ (tensorCLM a (basisProj bb F)), hsaT F⟩ :
            selfAdjoint (K →L[ℂ] K))) ⟨(φ a : K →L[ℂ] K), hsaφ⟩ := by
        constructor
        · rintro _ ⟨F, rfl⟩
          rw [← Subtype.coe_le_coe]
          show conjOperator V₀ (tensorCLM a (basisProj bb F)) ≤ (φ a : K →L[ℂ] K)
          rw [hφa]
          exact hadmono _ _ (tensorCLM_mono ha (isStarProjection_basisProj bb F).le_one)
        · rintro t ht
          rw [← Subtype.coe_le_coe]
          show (φ a : K →L[ℂ] K) ≤ (t : K →L[ℂ] K)
          rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff']
          refine ⟨t.2.sub hsaφ, fun ξ => ?_⟩
          have hle : ∀ F : Finset ↥sset,
              (⟪(conjOperator V₀ (tensorCLM a (basisProj bb F))) ξ, ξ⟫ : ℂ)
                ≤ ⟪(t : K →L[ℂ] K) ξ, ξ⟫ := by
            intro F
            have h := ht ⟨F, rfl⟩
            rw [← Subtype.coe_le_coe] at h
            rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff'] at h
            have h2 := h.2 ξ
            rw [ContinuousLinearMap.sub_apply, inner_sub_left] at h2
            exact sub_nonneg.mp h2
          have hfin := le_of_tendsto (hlim ξ) (Filter.Eventually.of_forall hle)
          rw [ContinuousLinearMap.sub_apply, inner_sub_left]
          exact sub_nonneg.mpr hfin
      have := uwTendsto_of_monotone_isLUB
        (fun F : Finset ↥sset =>
          (⟨conjOperator V₀ (tensorCLM a (basisProj bb F)), hsaT F⟩ :
            selfAdjoint (K →L[ℂ] K))) hmono ⟨(φ a : K →L[ℂ] K), hsaφ⟩ hlub
      simpa only [hsum] using this
    -- (ii) linearity in `a`
    have hadd : ∀ a b : H →L[ℂ] H,
        UWTendsto (fun F : Finset ↥sset => ∑ i ∈ F, conjOperator (W i) a) atTop (φ a) →
        UWTendsto (fun F : Finset ↥sset => ∑ i ∈ F, conjOperator (W i) b) atTop (φ b) →
        UWTendsto (fun F : Finset ↥sset => ∑ i ∈ F, conjOperator (W i) (a + b)) atTop
          (φ (a + b)) := by
      intro a b ha hb
      have hEq : (fun F : Finset ↥sset => ∑ i ∈ F, conjOperator (W i) (a + b))
          = fun F : Finset ↥sset => (∑ i ∈ F, conjOperator (W i) a)
              + (∑ i ∈ F, conjOperator (W i) b) := by
        funext F
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => map_add _ _ _
      have hφ' : (φ (a + b) : K →L[ℂ] K) = (φ a : K →L[ℂ] K) + φ b := by
        rw [hfφ, hfφ, hfφ, map_add]
      rw [hEq, hφ']
      exact uwTendsto_add' ha hb
    have hsmul : ∀ (c : ℂ) (a : H →L[ℂ] H),
        UWTendsto (fun F : Finset ↥sset => ∑ i ∈ F, conjOperator (W i) a) atTop (φ a) →
        UWTendsto (fun F : Finset ↥sset => ∑ i ∈ F, conjOperator (W i) (c • a)) atTop
          (φ (c • a)) := by
      intro c a ha
      have hEq : (fun F : Finset ↥sset => ∑ i ∈ F, conjOperator (W i) (c • a))
          = fun F : Finset ↥sset => c • (∑ i ∈ F, conjOperator (W i) a) := by
        funext F
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
      have hφ' : (φ (c • a) : K →L[ℂ] K) = c • (φ a : K →L[ℂ] K) := by
        rw [hfφ, hfφ, map_smul]
      rw [hEq, hφ']
      exact uwTendsto_smul' c ha
    -- (iii) every element is a complex combination of four positives
    have hsaCase : ∀ b : H →L[ℂ] H, IsSelfAdjoint b →
        UWTendsto (fun F : Finset ↥sset => ∑ i ∈ F, conjOperator (W i) b) atTop (φ b) := by
      intro b hb
      have hdec : b = b⁺ + (-1 : ℂ) • b⁻ := by
        rw [neg_one_smul, ← sub_eq_add_neg, CFC.posPart_sub_negPart b hb]
      have h := hadd _ _ (hpos _ (CFC.posPart_nonneg b))
        (hsmul (-1 : ℂ) _ (hpos _ (CFC.negPart_nonneg b)))
      rwa [← hdec] at h
    intro a
    have h1 := hsaCase ((realPart a : H →L[ℂ] H)) (realPart a).2
    have h2 := hsaCase ((imaginaryPart a : H →L[ℂ] H)) (imaginaryPart a).2
    have h3 := hadd _ _ h1 (hsmul Complex.I _ h2)
    rwa [realPart_add_I_smul_imaginaryPart a] at h3

/-- **138VIII** (`kraus-exercise`, dils.tex:742, Exercise*), finite
dimensional case: for finite-dimensional `ℋ` and `𝒦` the number of Kraus
operators can be chosen `≤ dim ℋ · dim 𝒦`. -/
theorem kraus_decomposition_findim [FiniteDimensional ℂ H]
    [FiniteDimensional ℂ K] (φ : NCPMap (H →L[ℂ] H) (K →L[ℂ] K)) :
    ∃ n : ℕ, n ≤ Module.finrank ℂ H * Module.finrank ℂ K ∧
      ∃ V : Fin n → (K →L[ℂ] H),
        ∀ a : H →L[ℂ] H, φ a = ∑ i, conjOperator (V i) a :=
  sorry

end TypeI

/-! ## Parsec 1390: normal Stinespring dilations -/

section NormalStinespring

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **139I** (dils.tex:778, Definition): a **normal Stinespring dilation**
of an ncp-map `φ : 𝒜 → B(ℋ)` (here: of the bare map `⇑φ`): a triple
`(𝒦, ϱ, V)` with `𝒦` a Hilbert space, `ϱ : 𝒜 → B(𝒦)` an nmiu-map and
`V : ℋ → 𝒦` a bounded operator with `φ = ad_V ∘ ϱ`. -/
structure StinespringDilation (φ : 𝒜 → (H →L[ℂ] H)) : Type (u + 1) where
  /-- The dilating Hilbert space `𝒦`. -/
  K : Type u
  [nacg : NormedAddCommGroup K]
  [ips : InnerProductSpace ℂ K]
  [cs : CompleteSpace K]
  /-- The normal representation `ϱ : 𝒜 → B(𝒦)`. -/
  ρ : NMIUMap 𝒜 (K →L[ℂ] K)
  /-- The bounded operator `V : ℋ → 𝒦`. -/
  V : H →L[ℂ] K
  /-- `φ = ad_V ∘ ϱ`. -/
  eq : ∀ a : 𝒜, φ a = conjOperator V (ρ a)

attribute [instance] StinespringDilation.nacg StinespringDilation.ips
  StinespringDilation.cs

/-- **139I** (dils.tex:778, Definition), continued: a Stinespring dilation
`(𝒦, ϱ, V)` is **minimal** if the linear span of
`ϱ(𝒜)Vℋ = {ϱ(a)Vx : a ∈ 𝒜, x ∈ ℋ}` is dense in `𝒦`. -/
def StinespringDilation.Minimal {φ : 𝒜 → (H →L[ℂ] H)}
    (D : StinespringDilation φ) : Prop :=
  Dense (Submodule.span ℂ
    {k : D.K | ∃ (a : 𝒜) (x : H), k = D.ρ a (D.V x)} : Set D.K)

/-- **139I** (dils.tex:778, Definition), embedded claims: every ncp-map
`φ : 𝒜 → B(ℋ)` has a normal Stinespring dilation (by **135IV**), and (by
restricting an arbitrary dilation to the closure of the span of `ϱ(𝒜)Vℋ`)
even a minimal one. -/
theorem exists_minimal_stinespringDilation [VonNeumannAlgebra 𝒜]
    (φ : NCPMap 𝒜 (H →L[ℂ] H)) :
    ∃ D : StinespringDilation ⇑φ, D.Minimal := by
  -- **135IV**.2, in the form `stinespring_normal_aux` (parsec 1370 above),
  -- already produces a *minimal* dilation: the span of `ϱ(𝒜)Vℋ` contains the
  -- image of `η`, which is dense.
  set f : 𝒜 →ₗ[ℂ] (H →L[ℂ] H) := φ.toCompletelyPositiveMap.toLinearMap with hf
  have hcp : IsCompletelyPositiveMap f :=
    (cp_iff f).out 1 0 |>.mp fun N M hM =>
      φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hnn : PreservesDirSups ⇑f := φ.preservesDirSups'
  obtain ⟨𝒦, h1, h2, h3, ϱ, V, heq, -, hmin⟩ := stinespring_normal_aux f hcp hnn
  exact ⟨⟨𝒦, ϱ, V, heq⟩, hmin⟩

/-- **139III** (`dils-univlemma`, dils.tex:823, Lemma): for nmiu-maps
`ϱ : 𝒜 → ℬ`, `ϱ' : 𝒜 → 𝒞` between von Neumann algebras and an ncp-map
`σ : 𝒞 → ℬ` with `σ ∘ ϱ' = ϱ` we have
`σ(ϱ'(a₁) c ϱ'(a₂)) = ϱ(a₁) σ(c) ϱ(a₂)`.

**139II** (dils.tex:805): discussion — nothing to formalize.
**139IV** is the proof — not converted. -/
theorem dils_univlemma {ℬ 𝒞 : Type u}
    [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]
    (ϱ : NMIUMap 𝒜 ℬ) (ϱ' : NMIUMap 𝒜 𝒞) (σ : NCPMap 𝒞 ℬ)
    (h : ∀ a, σ (ϱ' a) = ϱ a) (a₁ a₂ : 𝒜) (c : 𝒞) :
    σ (ϱ' a₁ * c * ϱ' a₂) = ϱ a₁ * σ c * ϱ a₂ := by
  -- dils.tex:833 (**139IV**), transcribed.
  set f : 𝒞 →ₗ[ℂ] ℬ := σ.toCompletelyPositiveMap.toLinearMap with hf
  have hfc : ∀ x : 𝒞, f x = σ x := fun _ => rfl
  have hcp : IsCompletelyPositiveMap f :=
    (cp_iff f).out 1 0 |>.mp fun N M hM =>
      σ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hu : f 1 = 1 := by
    have h1 : σ (ϱ' (1 : 𝒜)) = ϱ 1 := h 1
    rw [show (ϱ' (1 : 𝒜)) = 1 from map_one ϱ'.toStarAlgHom,
      show (ϱ (1 : 𝒜)) = 1 from map_one ϱ.toStarAlgHom] at h1
    exact h1
  have hp : IsPositiveMap f := astara_pos_basic_2_cp f hcp
  have hi : ∀ x : 𝒞, f (star x) = star (f x) := cstar_p_implies_i f hp
  -- `σ(ϱ'(a)* ϱ'(a)) = σ(ϱ'(a* a)) = ϱ(a* a) = ϱ(a)* ϱ(a) = σ(ϱ'(a))* σ(ϱ'(a))`,
  -- so Choi's lemma **34XVIII**.2 applies at `ϱ'(a)`.
  have hmulR : ∀ (a : 𝒜) (x : 𝒞), σ (x * ϱ' a) = σ x * ϱ a := by
    intro a x
    have hkey : f (star (ϱ' a) * ϱ' a) = star (f (ϱ' a)) * f (ϱ' a) := by
      rw [show star (ϱ' a) * ϱ' a = ϱ' (star a * a) by
        rw [show (ϱ' (star a * a)) = ϱ' (star a) * ϱ' a from
            map_mul ϱ'.toStarAlgHom _ _,
          show (ϱ' (star a)) = star (ϱ' a) from map_star ϱ'.toStarAlgHom _]]
      rw [hfc, hfc, h, h, show (ϱ (star a * a)) = ϱ (star a) * ϱ a from
        map_mul ϱ.toStarAlgHom _ _, show (ϱ (star a)) = star (ϱ a) from
        map_star ϱ.toStarAlgHom _]
    have := choi_2 f hcp hu (ϱ' a) hkey x
    rw [hfc, hfc, hfc, h] at this
    exact this
  -- taking adjoints: `σ(ϱ'(a) x) = ϱ(a) σ(x)`
  have hmulL : ∀ (a : 𝒜) (x : 𝒞), σ (ϱ' a * x) = ϱ a * σ x := by
    intro a x
    have h1 := hmulR (star a) (star x)
    rw [show (ϱ' (star a)) = star (ϱ' a) from map_star ϱ'.toStarAlgHom _,
      show (ϱ (star a)) = star (ϱ a) from map_star ϱ.toStarAlgHom _,
      ← star_mul, ← hfc, ← hfc, hi, hi] at h1
    have h2 := congrArg star h1
    rw [star_star] at h2
    rwa [star_mul, star_star, star_star, hfc] at h2
  rw [hmulR, hmulL]

/-! ### Infrastructure for **139V**

The author's proof of **139V** works with formal sums `∑ᵢ ϱ(aᵢ)Vxᵢ`; we
package these as the image of the algebraic tensor product `𝒜 ⊗ ℋ` under
the linear map `sdMap` below, which lets the norm identity of dils.tex:895
be stated as `‖sdMap D t‖ = ‖sdMap D' t‖` and the mediating isometry be
obtained from `LinearMap.extendOfNorm`. -/

section UnivStinespring

variable {φ : 𝒜 → (H →L[ℂ] H)}

/-- Auxiliary for **139V**: the linear map `𝒜 ⊗ ℋ → 𝒦`, `a ⊗ x ↦ ϱ(a)Vx`,
of a Stinespring dilation; its range is the linear span of `ϱ(𝒜)Vℋ`. -/
private noncomputable def sdMap (D : StinespringDilation φ) :
    TensorProduct ℂ 𝒜 H →ₗ[ℂ] D.K :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ (fun (a : 𝒜) (x : H) => D.ρ a (D.V x))
    (fun a b x => by
      rw [show D.ρ (a + b) = D.ρ a + D.ρ b from map_add D.ρ.toStarAlgHom a b]
      rfl)
    (fun c a x => by
      rw [show D.ρ (c • a) = c • D.ρ a from map_smul D.ρ.toStarAlgHom c a]
      rfl)
    (fun a x y => by rw [map_add, map_add])
    (fun c a x => by rw [map_smul, map_smul])

private theorem sdMap_tmul (D : StinespringDilation φ) (a : 𝒜) (x : H) :
    sdMap D (a ⊗ₜ[ℂ] x) = D.ρ a (D.V x) := rfl

/-- The inner product of two elementary tensors depends only on `φ`
(dils.tex:895): `⟪ϱ(a)Vx, ϱ(b)Vy⟫ = ⟪x, φ(a*b)y⟫`. -/
private theorem sdMap_inner_tmul (D : StinespringDilation φ) (a b : 𝒜)
    (x y : H) :
    (⟪sdMap D (a ⊗ₜ[ℂ] x), sdMap D (b ⊗ₜ[ℂ] y)⟫ : ℂ)
      = ⟪x, φ (star a * b) y⟫ := by
  rw [sdMap_tmul, sdMap_tmul, ← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint,
    show star (D.ρ a) = D.ρ (star a) from (map_star D.ρ.toStarAlgHom a).symm,
    show D.ρ (star a) (D.ρ b (D.V y)) = D.ρ (star a * b) (D.V y) from by
      rw [show D.ρ (star a * b) = D.ρ (star a) * D.ρ b from
        map_mul D.ρ.toStarAlgHom _ _]; rfl,
    ← ContinuousLinearMap.adjoint_inner_right, D.eq]
  rfl

/-- Consequently two Stinespring dilations of the same map give the same
inner products on `𝒜 ⊗ ℋ`. -/
private theorem sdMap_inner_eq (D D' : StinespringDilation φ)
    (s t : TensorProduct ℂ 𝒜 H) :
    (⟪sdMap D s, sdMap D t⟫ : ℂ) = ⟪sdMap D' s, sdMap D' t⟫ := by
  induction s with
  | zero => simp
  | add s₁ s₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | tmul a x =>
    induction t with
    | zero => simp
    | add t₁ t₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | tmul b y => rw [sdMap_inner_tmul, sdMap_inner_tmul]

private theorem sdMap_norm_eq (D D' : StinespringDilation φ)
    (t : TensorProduct ℂ 𝒜 H) : ‖sdMap D' t‖ = ‖sdMap D t‖ := by
  have h := sdMap_inner_eq D D' t t
  have h1 : ‖sdMap D t‖ ^ 2 = ‖sdMap D' t‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
    exact congrArg Complex.re h
  nlinarith [norm_nonneg (sdMap D t), norm_nonneg (sdMap D' t)]

private theorem sdMap_range (D : StinespringDilation φ) :
    LinearMap.range (sdMap D) =
      Submodule.span ℂ {k : D.K | ∃ (a : 𝒜) (x : H), k = D.ρ a (D.V x)} := by
  rw [LinearMap.range_eq_map, ← TensorProduct.span_tmul_eq_top ℂ 𝒜 H,
    Submodule.map_span]
  congr 1
  ext k
  constructor
  · rintro ⟨_, ⟨a, x, rfl⟩, rfl⟩
    exact ⟨a, x, rfl⟩
  · rintro ⟨a, x, rfl⟩
    exact ⟨a ⊗ₜ[ℂ] x, ⟨a, x, rfl⟩, rfl⟩

private theorem sdMap_denseRange {D : StinespringDilation φ}
    (hmin : D.Minimal) : DenseRange (sdMap D) := by
  have h : Set.range (sdMap D) = (Submodule.span ℂ
      {k : D.K | ∃ (a : 𝒜) (x : H), k = D.ρ a (D.V x)} : Set D.K) := by
    rw [show Set.range (sdMap D)
      = ((LinearMap.range (sdMap D) : Submodule ℂ D.K) : Set D.K) from rfl,
      sdMap_range]
  rw [DenseRange, h]
  exact hmin

end UnivStinespring

/-- **139V** (`dils-univ-stinespring`, dils.tex:863, Proposition): if
`(𝒦, ϱ, V)` and `(𝒦', ϱ', V')` are normal Stinespring dilations of the same
ncp-map `φ : 𝒜 → B(ℋ)` and `(𝒦, ϱ, V)` is minimal, then there is a unique
isometry `S : 𝒦 → 𝒦'` with `SV = V'` and `ϱ = ad_S ∘ ϱ'`.

**139VI**–**139VIII** are the proof — not converted. -/
theorem dils_univ_stinespring (φ : NCPMap 𝒜 (H →L[ℂ] H))
    (D D' : StinespringDilation ⇑φ) (hmin : D.Minimal) :
    ∃! S : D.K →L[ℂ] D'.K,
      Isometry S ∧ S.comp D.V = D'.V ∧
        ∀ a : 𝒜, D.ρ a = conjOperator S (D'.ρ a) := by
  have hdense : DenseRange (sdMap D) := sdMap_denseRange hmin
  have hbound : ∃ C : ℝ, ∀ t, ‖sdMap D' t‖ ≤ C * ‖sdMap D t‖ :=
    ⟨1, fun t => by rw [one_mul, sdMap_norm_eq D D' t]⟩
  -- `‖∑ᵢ ϱ(aᵢ)Vxᵢ‖ = ‖∑ᵢ ϱ'(aᵢ)V'xᵢ‖` (dils.tex:895) gives the isometry
  set S : D.K →L[ℂ] D'.K := LinearMap.extendOfNorm (sdMap D') (sdMap D) with hSdef
  have hSt : ∀ t, S (sdMap D t) = sdMap D' t :=
    fun t => LinearMap.extendOfNorm_eq hdense hbound t
  have hSnorm : ∀ k : D.K, ‖S k‖ = ‖k‖ := fun k =>
    hdense.induction_on k (isClosed_eq (by fun_prop) (by fun_prop))
      (fun t => by rw [hSt, sdMap_norm_eq D D' t])
  have hSinner : ∀ k l : D.K, (⟪S k, S l⟫ : ℂ) = ⟪k, l⟫ :=
    (LinearIsometry.mk S.toLinearMap hSnorm).inner_map_map
  have hSadj : ∀ k : D.K, ContinuousLinearMap.adjoint S (S k) = k := by
    intro k
    refine ext_inner_left ℂ fun v => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, hSinner]
  -- `SV = V'`, since `V x = ϱ(1)Vx`
  have hV : ∀ x : H, sdMap D ((1 : 𝒜) ⊗ₜ[ℂ] x) = D.V x := by
    intro x
    rw [sdMap_tmul, show D.ρ (1 : 𝒜) = 1 from map_one D.ρ.toStarAlgHom]
    rfl
  have hV' : ∀ x : H, sdMap D' ((1 : 𝒜) ⊗ₜ[ℂ] x) = D'.V x := by
    intro x
    rw [sdMap_tmul, show D'.ρ (1 : 𝒜) = 1 from map_one D'.ρ.toStarAlgHom]
    rfl
  have hSV : S.comp D.V = D'.V := by
    refine ContinuousLinearMap.ext fun x => ?_
    rw [ContinuousLinearMap.comp_apply, ← hV, hSt, hV']
  -- `S ϱ(a) = ϱ'(a) S` (dils.tex:917)
  have hkey : ∀ (a : 𝒜) (t : TensorProduct ℂ 𝒜 H),
      S (D.ρ a (sdMap D t)) = D'.ρ a (sdMap D' t) := by
    intro a t
    induction t with
    | zero => simp
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b x =>
      rw [sdMap_tmul, sdMap_tmul,
        show D.ρ a (D.ρ b (D.V x)) = sdMap D ((a * b) ⊗ₜ[ℂ] x) from by
          rw [sdMap_tmul, show D.ρ (a * b) = D.ρ a * D.ρ b from
            map_mul D.ρ.toStarAlgHom _ _]; rfl,
        hSt, sdMap_tmul,
        show D'.ρ (a * b) = D'.ρ a * D'.ρ b from map_mul D'.ρ.toStarAlgHom _ _]
      rfl
  have hintw : ∀ (a : 𝒜) (k : D.K), S (D.ρ a k) = D'.ρ a (S k) := fun a k =>
    hdense.induction_on k (isClosed_eq (by fun_prop) (by fun_prop))
      (fun t => by rw [hkey a t, hSt])
  have hρ : ∀ a : 𝒜, D.ρ a = conjOperator S (D'.ρ a) := by
    intro a
    refine ContinuousLinearMap.ext fun k => ?_
    change D.ρ a k = ContinuousLinearMap.adjoint S ((D'.ρ a).comp S k)
    rw [ContinuousLinearMap.comp_apply, ← hintw a k, hSadj]
  refine ⟨S, ⟨AddMonoidHomClass.isometry_of_norm S hSnorm, hSV, hρ⟩, ?_⟩
  -- Uniqueness.  Any `T` as in the statement already satisfies
  -- `T ϱ(a)Vx = ϱ'(a)V'x`, which pins it down on the dense span.
  rintro T ⟨hTiso, hTV, hTρ⟩
  have hTnorm : ∀ k : D.K, ‖T k‖ = ‖k‖ := fun k => by
    simpa using hTiso.dist_eq k 0
  have hTinner : ∀ k l : D.K, (⟪T k, T l⟫ : ℂ) = ⟪k, l⟫ :=
    (LinearIsometry.mk T.toLinearMap hTnorm).inner_map_map
  have hTtmul : ∀ t : TensorProduct ℂ 𝒜 H, T (sdMap D t) = sdMap D' t := by
    intro t
    induction t with
    | zero => simp
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b x =>
      set y : D'.K := sdMap D' (b ⊗ₜ[ℂ] x) with hy
      set u : D.K := sdMap D (b ⊗ₜ[ℂ] x) with hu
      -- `u = T* y`: indeed `ϱ(b)Vx = T*ϱ'(b)T V x = T*ϱ'(b)V'x`
      have hTu : ContinuousLinearMap.adjoint T y = u := by
        have h1 : D.ρ b (D.V x) =
            ContinuousLinearMap.adjoint T ((D'.ρ b) (T (D.V x))) := by
          have := hTρ b
          have h2 := congrArg (fun (P : D.K →L[ℂ] D.K) => P (D.V x)) this
          simpa [conjOperator] using h2
        rw [hu, hy, sdMap_tmul, sdMap_tmul, h1,
          show T (D.V x) = D'.V x from by
            rw [← hTV]; rfl]
      -- `‖y − T u‖² = ⟪y,y⟫ − ⟪u,u⟫ = 0` by the norm identity
      have hyy : (⟪y, y⟫ : ℂ) = ⟪u, u⟫ :=
        sdMap_inner_eq D' D (b ⊗ₜ[ℂ] x) (b ⊗ₜ[ℂ] x)
      have hzero : (⟪y - T u, y - T u⟫ : ℂ) = 0 := by
        rw [inner_sub_sub_self]
        rw [show (⟪T u, y⟫ : ℂ) = ⟪u, u⟫ from by
              rw [← ContinuousLinearMap.adjoint_inner_right, hTu],
          show (⟪y, T u⟫ : ℂ) = ⟪u, u⟫ from by
              rw [← ContinuousLinearMap.adjoint_inner_left, hTu],
          hTinner, hyy]
        ring
      exact (sub_eq_zero.mp (inner_self_eq_zero.mp hzero)).symm
  refine ContinuousLinearMap.ext fun k => ?_
  refine hdense.induction_on k (isClosed_eq (by fun_prop) (by fun_prop))
    fun t => ?_
  rw [hTtmul t, hSt]

/-- **139IX** (`exc-chris-univ-prop`, dils.tex:945, Exercise*): the
universal property **139V** makes the minimal Stinespring dilation a
universal arrow, i.e. the inclusion `Rep → Rep_cp` (of normal
representations into ncpu-maps `φ : 𝒜 → B(ℋ)` with morphisms
`(m, S) : φ → φ'` given by an nmiu-map `m` and an isometry `S` with
`φ = ad_S ∘ φ' ∘ m`) has a left adjoint.  Stated as: for every ncpu-map `φ`
there is a normal representation `ψ : 𝒜 → B(𝒦)` and a morphism
`(id, S₀) : φ → ψ` through which every morphism from `φ` to a normal
representation factors uniquely.

**139IXa** (Remarks), **139X**: discussion — nothing to formalize. -/
theorem exc_chris_univ_prop [VonNeumannAlgebra 𝒜]
    (φ : NCPMap 𝒜 (H →L[ℂ] H)) (hu : φ 1 = 1) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ψ : NMIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (S₀ : H →L[ℂ] 𝒦),
      Isometry S₀ ∧ (∀ a, φ a = conjOperator S₀ (ψ a)) ∧
      ∀ (𝒜' K' : Type u) (_ : CStarAlgebra 𝒜') (_ : PartialOrder 𝒜')
        (_ : StarOrderedRing 𝒜') (_ : NormedAddCommGroup K')
        (_ : InnerProductSpace ℂ K') (_ : CompleteSpace K')
        (ψ' : NMIUMap 𝒜' (K' →L[ℂ] K')) (m : NMIUMap 𝒜 𝒜') (S : H →L[ℂ] K'),
        Isometry S → (∀ a, φ a = conjOperator S (ψ' (m a))) →
        ∃! p : NMIUMap 𝒜 𝒜' × (𝒦 →L[ℂ] K'),
          (∀ a, p.1 a = m a) ∧ Isometry p.2 ∧ p.2.comp S₀ = S ∧
            ∀ a, ψ a = conjOperator p.2 (ψ' (p.1 a)) := by
  -- `bsols.tex`, solution `exc-chris-univ-prop`: take a *minimal* normal
  -- Stinespring dilation `(𝒦, ϱ, V)` of `φ` (**135IV**.2, **139I**); the unit
  -- is `η_φ = (id, V)`, and the mediating pair for `(m, S)` is `(m, T)` with
  -- `T` the isometry provided by **139V**.
  set f : 𝒜 →ₗ[ℂ] (H →L[ℂ] H) := φ.toCompletelyPositiveMap.toLinearMap with hf
  have hcp : IsCompletelyPositiveMap f :=
    (cp_iff f).out 1 0 |>.mp fun N M hM =>
      φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hnn : PreservesDirSups ⇑f := φ.preservesDirSups'
  obtain ⟨𝒦, h1, h2, h3, ϱ, V, heq, hiso, hmin⟩ :=
    stinespring_normal_aux f hcp hnn
  refine ⟨𝒦, h1, h2, h3, ϱ, V, hiso hu, heq, ?_⟩
  intro 𝒜' K' i1 i2 i3 i4 i5 i6 ψ' m S hSiso hS
  -- the second dilation `(𝒦', ϱ' ∘ m, S)`; the composite is normal by
  -- `preservesDirSups_pmap_comp` (vn.tex **48II**'s toolbox)
  set ρ' : NMIUMap 𝒜 (K' →L[ℂ] K') :=
    { toStarAlgHom := ψ'.toStarAlgHom.comp m.toStarAlgHom
      preservesDirSups' :=
        preservesDirSups_pmap_comp (starAlgHomP m.toStarAlgHom)
          m.preservesDirSups' (starAlgHomP ψ'.toStarAlgHom)
          ψ'.preservesDirSups' } with hρ'
  obtain ⟨T, ⟨hT1, hT2, hT3⟩, hTu⟩ :=
    dils_univ_stinespring φ ⟨𝒦, ϱ, V, heq⟩ ⟨K', ρ', S, hS⟩ hmin
  refine ⟨(m, T), ⟨fun _ => rfl, hT1, hT2, hT3⟩, ?_⟩
  rintro ⟨m'', T''⟩ ⟨hq1, hq2, hq3, hq4⟩
  have hm : m'' = m := DFunLike.ext _ _ hq1
  subst hm
  have hT : T'' = T := hTu T'' ⟨hq2, hq3, hq4⟩
  rw [hT]

end NormalStinespring

section EssUniq

variable {H K K' : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

/-- **139XI** (`ess-uniq-pur`, dils.tex:998, Exercise* (Essential uniqueness
of purification)): if `V, W : 𝒦 → ℋ ⊗ 𝒦'` are bounded operators with
`V*(a ⊗ 1)V = φ(a) = W*(a ⊗ 1)W` for all `a ∈ B(ℋ)`, then `V = (1 ⊗ U) W`
for some unitary `U : 𝒦' → 𝒦'`. -/
theorem ess_uniq_pur (φ : NCPMap (H →L[ℂ] H) (K →L[ℂ] K))
    (V W : K →L[ℂ] hilbTensor H K')
    (hV : ∀ a : H →L[ℂ] H, φ a = conjOperator V (tensorCLM a 1))
    (hW : ∀ a : H →L[ℂ] H, φ a = conjOperator W (tensorCLM a 1)) :
    ∃ U : K' →L[ℂ] K',
      (ContinuousLinearMap.adjoint U).comp U = 1 ∧
      U.comp (ContinuousLinearMap.adjoint U) = 1 ∧
      V = (tensorCLM 1 U).comp W :=
  sorry

end EssUniq

/-! ## Parsec 1400: Paschke dilations

**140I** (dils.tex:1027): introduction — nothing to formalize. -/

section Paschke

variable {𝒜 ℬ : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **140II** (`def-paschke`, dils.tex:1049, Definition), the data: a
**Paschke triple** over von Neumann algebras `𝒜`, `ℬ`: a von Neumann
algebra `𝒫` with an nmiu-map `ϱ : 𝒜 → 𝒫` and an ncp-map `h : 𝒫 → ℬ`.
(The von Neumann algebra structure is carried as a proof field `vn` so that
triples can be written down in statements; all algebras live in one
universe `u`, over which the universal property below quantifies.) -/
structure PaschkeTriple (𝒜 ℬ : Type u)
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] :
    Type (u + 1) where
  /-- The dilating von Neumann algebra `𝒫`. -/
  P : Type u
  [pc : CStarAlgebra P]
  [pp : PartialOrder P]
  [ps : StarOrderedRing P]
  /-- `𝒫` is a von Neumann algebra. -/
  vn : VonNeumannAlgebra P
  /-- The nmiu-part `ϱ : 𝒜 → 𝒫`. -/
  ρ : NMIUMap 𝒜 P
  /-- The ncp-part `h : 𝒫 → ℬ`. -/
  h : NCPMap P ℬ

attribute [instance] PaschkeTriple.pc PaschkeTriple.pp PaschkeTriple.ps

/-- **140II** (`def-paschke`, dils.tex:1049, Definition): a Paschke triple
`(𝒫, ϱ, h)` is a **Paschke dilation** of an ncp-map `φ : 𝒜 → ℬ` when
`φ = h ∘ ϱ` and for every triple `(𝒫', ϱ', h')` with `φ = h' ∘ ϱ'` there is
a unique mediating ncp-map `σ : 𝒫' → 𝒫` with `σ ∘ ϱ' = ϱ` and
`h ∘ σ = h'`. -/
def IsPaschkeDilationOf (D : PaschkeTriple 𝒜 ℬ) (φ : 𝒜 → ℬ) : Prop :=
  (∀ a, D.h (D.ρ a) = φ a) ∧
  ∀ D' : PaschkeTriple 𝒜 ℬ, (∀ a, D'.h (D'.ρ a) = φ a) →
    ∃! σ : NCPMap D'.P D.P,
      (∀ a, σ (D'.ρ a) = D.ρ a) ∧ ∀ c, D.h (σ c) = D'.h c

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ### Infrastructure: `ad_V` as an ncp-map

Complete positivity of `T ↦ V* T V` is **34V**.2 (`ad_cp_2`); normality
follows from **48II** (`normal_faithful`), because `⟪y, V* T V y⟫ =
⟪Vy, T(Vy)⟫` is again a vector functional (vn.tex 42V.2). -/

/-- `ad_V : B(𝒦) → B(ℋ)` as a positive linear map. -/
private noncomputable def adP {X Y : Type u} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] [CompleteSpace Y] (V : X →L[ℂ] Y) :
    (Y →L[ℂ] Y) →ₚ[ℂ] (X →L[ℂ] X) where
  toLinearMap := conjOperator V
  monotone' := fun T T' hT => by
    have h := astara_pos_basic_2_cp (conjOperator V) (ad_cp_2 V) (T' - T)
      (sub_nonneg.mpr hT)
    rw [map_sub] at h
    exact sub_nonneg.mp h

private theorem adP_apply {X Y : Type u} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] [CompleteSpace Y] (V : X →L[ℂ] Y)
    (T : Y →L[ℂ] Y) : adP V T = conjOperator V T := rfl

private theorem adP_normal {X Y : Type u} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] [CompleteSpace Y] (V : X →L[ℂ] Y) :
    PreservesDirSups ⇑(adP V) := by
  set Ω : Set (NPFunctional (X →L[ℂ] X)) :=
    {ν | ∃ y ∈ (Set.univ : Set X), ν = vectorNP y} with hΩdef
  have hfaith : FaithfulCollection Ω :=
    faithfulCollection_vectorNP Set.univ
      (fun R h => ContinuousLinearMap.ext fun y => h y (Set.mem_univ y))
  refine (normal_faithful Ω hfaith (adP V)).mpr ?_
  rintro ν ⟨y, -, rfl⟩
  have hpt : ∀ T : Y →L[ℂ] Y, (vectorNP y (adP V T) : ℂ) = vectorNP (V y) T := by
    intro T
    have happ : (conjOperator V T) y
        = ContinuousLinearMap.adjoint V (T (V y)) := rfl
    rw [vectorNP_apply, vectorNP_apply, adP_apply, happ,
      ContinuousLinearMap.adjoint_inner_right]
  intro D s hne hdir hlub
  have h := (vectorNP (V y)).preservesDirSups' D s hne hdir hlub
  simp only [hpt]
  exact h

/-- `ad_V : B(𝒦) → B(ℋ)` as an ncp-map. -/
private noncomputable def adNCP {X Y : Type u} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] [CompleteSpace Y] (V : X →L[ℂ] Y) :
    NCPMap (Y →L[ℂ] Y) (X →L[ℂ] X) where
  toCompletelyPositiveMap :=
    { toLinearMap := conjOperator V
      map_cstarMatrix_nonneg' := (cp_iff (conjOperator V)).out 0 1 |>.mp
        (ad_cp_2 V) }
  preservesDirSups' := adP_normal V

private theorem adNCP_apply {X Y : Type u} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] [CompleteSpace Y] (V : X →L[ℂ] Y)
    (T : Y →L[ℂ] Y) : adNCP V T = conjOperator V T := by rfl

private theorem conjOperator_conjOperator {X Y Z : Type u}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (V : X →L[ℂ] Y) (S : Y →L[ℂ] Z) (T : Z →L[ℂ] Z) :
    conjOperator V (conjOperator S T) = conjOperator (S.comp V) T := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp [conjOperator, ContinuousLinearMap.adjoint_comp]

set_option maxHeartbeats 1000000 in
-- The proof assembles several bundled structures (an ncp-map out of
-- `cp_iff`/`cp_comp`, an nmiu-composite) whose defeq checks are costly.
/-- **140III** (`stinespring-is-paschke`, dils.tex:1074, Theorem): if
`(𝒦, ϱ, V)` is a minimal normal Stinespring dilation of an ncp-map
`φ : 𝒜 → B(ℋ)`, then `(B(𝒦), ϱ, ad_V)` is a Paschke dilation of `φ`.

**140IV**–**140VI** are the author's proof, transcribed here. -/
theorem stinespring_is_paschke [VonNeumannAlgebra 𝒜]
    (φ : NCPMap 𝒜 (H →L[ℂ] H)) (D : StinespringDilation ⇑φ)
    (hmin : D.Minimal) :
    ∃ (vnK : VonNeumannAlgebra (D.K →L[ℂ] D.K))
      (h : NCPMap (D.K →L[ℂ] D.K) (H →L[ℂ] H)),
      (∀ T, h T = conjOperator D.V T) ∧
      IsPaschkeDilationOf ⟨D.K →L[ℂ] D.K, vnK, D.ρ, h⟩ ⇑φ := by
  -- dils.tex:1082 (**140IV**–**140VI**), transcribed.
  have hdense : DenseRange (sdMap D) := sdMap_denseRange hmin
  refine ⟨inferInstance, adNCP D.V, fun _ => rfl, fun a => (D.eq a).symm,
    fun D' hD' => ?_⟩
  letI := D'.vn
  -- **140V** (uniqueness): by **139III** the inner products
  -- `⟪ϱ(α)Vy, σ(c) ϱ(a)Vx⟫ = ⟪y, h'(ϱ'(α*) c ϱ'(a)) x⟫` do not depend on `σ`,
  -- and the vectors `∑ᵢ ϱ(aᵢ)Vxᵢ` are dense by minimality.
  have huniq : ∀ σ₁ σ₂ : NCPMap D'.P (D.K →L[ℂ] D.K),
      ((∀ a, σ₁ (D'.ρ a) = D.ρ a) ∧ ∀ c, conjOperator D.V (σ₁ c) = D'.h c) →
      ((∀ a, σ₂ (D'.ρ a) = D.ρ a) ∧ ∀ c, conjOperator D.V (σ₂ c) = D'.h c) →
      σ₁ = σ₂ := by
    intro σ₁ σ₂ hp₁ hp₂
    have key : ∀ σ : NCPMap D'.P (D.K →L[ℂ] D.K),
        (∀ a, σ (D'.ρ a) = D.ρ a) → (∀ c, conjOperator D.V (σ c) = D'.h c) →
        ∀ (c : D'.P) (a α : 𝒜) (x y : H),
          (⟪sdMap D (α ⊗ₜ[ℂ] y), σ c (sdMap D (a ⊗ₜ[ℂ] x))⟫ : ℂ)
            = ⟪y, D'.h (D'.ρ (star α) * c * D'.ρ a) x⟫ := by
      intro σ hσ1 hσ2 c a α x y
      have hadj : ContinuousLinearMap.adjoint (D.ρ α) = D.ρ (star α) := by
        rw [← ContinuousLinearMap.star_eq_adjoint]
        exact (map_star D.ρ.toStarAlgHom α).symm
      have hstep : ContinuousLinearMap.adjoint D.V
            (D.ρ (star α) (σ c (D.ρ a (D.V x))))
          = conjOperator D.V (D.ρ (star α) * σ c * D.ρ a) x := rfl
      rw [sdMap_tmul, sdMap_tmul,
        ← ContinuousLinearMap.adjoint_inner_right (D.ρ α) (D.V y), hadj,
        ← ContinuousLinearMap.adjoint_inner_right D.V y, hstep,
        ← dils_univlemma D.ρ D'.ρ σ hσ1 (star α) a c, hσ2]
    refine DFunLike.ext _ _ fun c => ?_
    have hinner : ∀ s t : TensorProduct ℂ 𝒜 H,
        (⟪sdMap D t, σ₁ c (sdMap D s)⟫ : ℂ) = ⟪sdMap D t, σ₂ c (sdMap D s)⟫ := by
      intro s t
      induction s with
      | zero => simp
      | add s₁ s₂ ha hb => simp only [map_add, inner_add_right, ha, hb]
      | tmul a x =>
        induction t with
        | zero => simp
        | add t₁ t₂ ha hb => simp only [map_add, inner_add_left, ha, hb]
        | tmul α y =>
          rw [key σ₁ hp₁.1 hp₁.2 c a α x y, key σ₂ hp₂.1 hp₂.2 c a α x y]
    have hk : ∀ (k : D.K) (t : TensorProduct ℂ 𝒜 H),
        (⟪sdMap D t, σ₁ c k⟫ : ℂ) = ⟪sdMap D t, σ₂ c k⟫ := fun k t =>
      hdense.induction_on k (isClosed_eq (by fun_prop) (by fun_prop))
        (fun s => hinner s t)
    have hl : ∀ k l : D.K, (⟪l, σ₁ c k⟫ : ℂ) = ⟪l, σ₂ c k⟫ := fun k l =>
      hdense.induction_on l (isClosed_eq (by fun_prop) (by fun_prop))
        (fun t => hk k t)
    exact ContinuousLinearMap.ext fun k => ext_inner_left ℂ fun l => hl k l
  -- **140VI** (existence): a minimal normal Stinespring dilation `(𝒦̃, ϱ̃, Ṽ)`
  -- of `h'` makes `(𝒦̃, ϱ̃ ∘ ϱ', Ṽ)` one of `φ`; **139V** then gives the
  -- isometry `S` and `σ = ad_S ∘ ϱ̃`.
  obtain ⟨E, -⟩ := exists_minimal_stinespringDilation D'.h
  set Lρ : D'.P →ₗ[ℂ] (E.K →L[ℂ] E.K) :=
    { toFun := fun c => E.ρ c
      map_add' := fun x y => map_add E.ρ.toStarAlgHom x y
      map_smul' := fun r x => map_smul E.ρ.toStarAlgHom r x } with hLρ
  have hLρcp : IsCompletelyPositiveMap Lρ :=
    cp_of_mi Lρ (fun x y => map_mul E.ρ.toStarAlgHom x y)
      (fun x => map_star E.ρ.toStarAlgHom x)
  set ρ₂ : NMIUMap 𝒜 (E.K →L[ℂ] E.K) :=
    { toStarAlgHom := E.ρ.toStarAlgHom.comp D'.ρ.toStarAlgHom
      preservesDirSups' :=
        preservesDirSups_pmap_comp (starAlgHomP D'.ρ.toStarAlgHom)
          D'.ρ.preservesDirSups' (starAlgHomP E.ρ.toStarAlgHom)
          E.ρ.preservesDirSups' } with hρ₂
  have hD₂eq : ∀ a : 𝒜, φ a = conjOperator E.V (ρ₂ a) := by
    intro a
    rw [← hD' a]
    exact E.eq (D'.ρ a)
  obtain ⟨S, ⟨-, hSV, hSρ⟩, -⟩ :=
    dils_univ_stinespring φ D ⟨E.K, ρ₂, E.V, hD₂eq⟩ hmin
  set σ : NCPMap D'.P (D.K →L[ℂ] D.K) :=
    { toCompletelyPositiveMap :=
        { toLinearMap := (conjOperator S).comp Lρ
          map_cstarMatrix_nonneg' :=
            (cp_iff ((conjOperator S).comp Lρ)).out 0 1 |>.mp
              (cp_comp Lρ (conjOperator S) hLρcp (ad_cp_2 S)) }
      preservesDirSups' :=
        preservesDirSups_pmap_comp (starAlgHomP E.ρ.toStarAlgHom)
          E.ρ.preservesDirSups' (adP S) (adP_normal S) } with hσdef
  have hσ1 : ∀ a : 𝒜, σ (D'.ρ a) = D.ρ a := fun a => (hSρ a).symm
  have hσ2 : ∀ c : D'.P, conjOperator D.V (σ c) = D'.h c := by
    intro c
    have h1 : conjOperator D.V (σ c)
        = conjOperator (S.comp D.V) (E.ρ c) :=
      conjOperator_conjOperator D.V S (E.ρ c)
    rw [h1, show S.comp D.V = E.V from hSV]
    exact (E.eq c).symm
  exact ⟨σ, ⟨hσ1, hσ2⟩, fun τ hτ => huniq τ σ hτ ⟨hσ1, hσ2⟩⟩

/-! **140VIII** (`paschke-unique-up-to-iso`) is proved at the foot of this
file, as `paschke_unique_up_to_iso`: it needs the identity and composition
of ncp-maps, whose (private) constructions come below.

**140VII** (dils.tex:1157): discussion; **140IX** is the proof. -/

/-! ### Infrastructure: the identity ncp-map

`Theses.A.Proc.Measurement` has these (as `isLUB_val_of_isLUB`,
`preservesDirSups_id`, `exists_ncpId`), but `Theses.A.Proc` is not in this
chapter's import path, so the three short proofs are repeated here. -/

/-- The supremum of a nonempty set of self-adjoint elements computed in
`sa(A)` is its supremum in `A`. -/
private theorem isLUB_val_of_isLUB {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {D : Set (selfAdjoint A)}
    {s : selfAdjoint A} (hne : D.Nonempty) (h : IsLUB D s) :
    IsLUB (Subtype.val '' D) ((s : selfAdjoint A) : A) := by
  obtain ⟨d₀, hd₀⟩ := hne
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mpr (h.1 hd)
  · have hu0 : ((d₀ : selfAdjoint A) : A) ≤ u := hu ⟨d₀, hd₀, rfl⟩
    have husa : IsSelfAdjoint u := by
      have hd : IsSelfAdjoint (u - ((d₀ : selfAdjoint A) : A)) :=
        IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hu0)
      simpa using hd.add d₀.2
    have hub : (⟨u, husa⟩ : selfAdjoint A) ∈ upperBounds D :=
      fun e he => hu ⟨e, he, rfl⟩
    exact h.2 hub

/-- The identity map is normal. -/
private theorem preservesDirSups_id {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :
    PreservesDirSups (fun a : A => a) := fun _ _ hne _ hlub =>
  isLUB_val_of_isLUB hne hlub

/-- The identity map is an ncp-map. -/
private theorem exists_ncpId (A : Type*) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : ∃ f : NCPMap A A, ∀ a : A, f a = a :=
  ⟨{ toCompletelyPositiveMap :=
       { toLinearMap := LinearMap.id
         map_cstarMatrix_nonneg' := fun _ _ hM => by simpa using hM }
     preservesDirSups' := preservesDirSups_id }, fun _ => rfl⟩

/-- Multiplication by a positive real is an order isomorphism of a
C*-algebra (auxiliary for `exists_ncpSmul`). -/
private theorem smul_le_smul_iff_pos {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {l : ℝ} (hl : 0 < l) (x y : A) :
    (l : ℂ) • x ≤ (l : ℂ) • y ↔ x ≤ y := by
  have main : ∀ (m : ℝ), 0 ≤ m → ∀ u v : A, u ≤ v → (m : ℂ) • u ≤ (m : ℂ) • v := by
    intro m hm u v huv
    have h0 : (0 : A) ≤ (m : ℂ) • (v - u) :=
      cstar_positive_1 _ (sub_nonneg.mpr huv) m hm
    rw [smul_sub] at h0
    rwa [← sub_nonneg]
  refine ⟨fun h => ?_, main l hl.le x y⟩
  have h' := main l⁻¹ (inv_nonneg.mpr hl.le) _ _ h
  rwa [smul_smul, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hl.ne',
    Complex.ofReal_one, one_smul, one_smul] at h'

/-- A positive real multiple of an ncp-map is an ncp-map. -/
private theorem exists_ncpSmul {A B : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : NCPMap A B) {l : ℝ} (hl : 0 < l) :
    ∃ g : NCPMap A B, ∀ a, g a = (l : ℂ) • f a := by
  refine ⟨{ toCompletelyPositiveMap :=
              { toLinearMap := (l : ℂ) • (f.toCompletelyPositiveMap.toLinearMap)
                map_cstarMatrix_nonneg' := fun k M hM => ?_ }
            preservesDirSups' := ?_ }, fun _ => rfl⟩
  · have h1 : (0 : CStarMatrix (Fin k) (Fin k) B)
        ≤ M.map f.toCompletelyPositiveMap.toLinearMap :=
      f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' k M hM
    have h2 : M.map ((l : ℂ) • f.toCompletelyPositiveMap.toLinearMap)
        = (l : ℂ) • M.map f.toCompletelyPositiveMap.toLinearMap := rfl
    rw [h2]
    exact cstar_positive_1 _ h1 l hl.le
  · intro D s hne hdir hlub
    have h := f.preservesDirSups' D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact (smul_le_smul_iff_pos hl _ _).mpr (h.1 ⟨d, hd, rfl⟩)
    · intro u hu
      have hu' : (l : ℂ)⁻¹ • u ∈ upperBounds ((fun d : selfAdjoint A => f d) '' D) := by
        rintro _ ⟨d, hd, rfl⟩
        have := hu ⟨d, hd, rfl⟩
        have hle : (l : ℂ) • (f d) ≤ (l : ℂ) • ((l : ℂ)⁻¹ • u) := by
          rwa [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hl.ne'), one_smul]
        exact (smul_le_smul_iff_pos hl _ _).mp hle
      have := h.2 hu'
      have hle : (l : ℂ) • f s ≤ (l : ℂ) • ((l : ℂ)⁻¹ • u) :=
        (smul_le_smul_iff_pos hl _ _).mpr this
      rwa [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hl.ne'), one_smul] at hle

/-- An ncp-map, as a positive linear map (auxiliary for
`exists_ncpCompNMIU`). -/
private noncomputable def ncpP {A B : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : NCPMap A B) : A →ₚ[ℂ] B where
  toLinearMap := f.toCompletelyPositiveMap.toLinearMap
  monotone' := fun x y hxy => by
    have hcp : IsCompletelyPositiveMap f.toCompletelyPositiveMap.toLinearMap :=
      (cp_iff _).out 1 0 |>.mp fun N M hM =>
        f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
    have h := astara_pos_basic_2_cp _ hcp (y - x) (sub_nonneg.mpr hxy)
    rw [map_sub] at h
    exact sub_nonneg.mp h

/-- The composition of an nmiu-map with an ncp-map is an ncp-map. -/
private theorem exists_ncpCompNMIU {A B C : Type u} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (f : NCPMap B C) (g : NMIUMap A B) :
    ∃ k : NCPMap A C, ∀ a, k a = f (g a) := by
  set Lg : A →ₗ[ℂ] B :=
    { toFun := fun a => g a
      map_add' := fun x y => map_add g.toStarAlgHom x y
      map_smul' := fun r x => map_smul g.toStarAlgHom r x } with hLg
  have hLgcp : IsCompletelyPositiveMap Lg :=
    cp_of_mi Lg (fun x y => map_mul g.toStarAlgHom x y)
      (fun x => map_star g.toStarAlgHom x)
  set Lf : B →ₗ[ℂ] C := f.toCompletelyPositiveMap.toLinearMap with hLf
  have hLfcp : IsCompletelyPositiveMap Lf :=
    (cp_iff Lf).out 1 0 |>.mp fun N M hM =>
      f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  exact ⟨{ toCompletelyPositiveMap :=
             { toLinearMap := Lf.comp Lg
               map_cstarMatrix_nonneg' :=
                 (cp_iff (Lf.comp Lg)).out 0 1 |>.mp
                   (cp_comp Lg Lf hLgcp hLfcp) }
           preservesDirSups' :=
             preservesDirSups_pmap_comp (starAlgHomP g.toStarAlgHom)
               g.preservesDirSups' (ncpP f) f.preservesDirSups' },
    fun _ => rfl⟩

/-- **140X** (`paschke-basics`, dils.tex:1204, Exercise), part 1:
`(ℬ, ϱ, id)` is a Paschke dilation of an nmiu-map `ϱ : 𝒜 → ℬ`. -/
theorem paschke_basics_1 (vnB : VonNeumannAlgebra ℬ) (ϱ : NMIUMap 𝒜 ℬ) :
    ∃ h : NCPMap ℬ ℬ, (∀ b, h b = b) ∧
      IsPaschkeDilationOf ⟨ℬ, vnB, ϱ, h⟩ ⇑ϱ := by
  obtain ⟨idB, hid⟩ := exists_ncpId ℬ
  -- `bsols.tex`, solution `paschke-basics`.1: "clearly `σ ≡ h'` fits the bill"
  refine ⟨idB, hid, fun a => hid _, fun D' hD' => ⟨D'.h, ⟨hD', fun c => hid _⟩, ?_⟩⟩
  rintro σ ⟨-, hσ⟩
  refine DFunLike.ext _ _ fun c => ?_
  have h := hσ c
  rwa [hid] at h

/-- **140X** (`paschke-basics`, dils.tex:1204, Exercise), part 2: if
`(𝒫, ϱ, h)` is a Paschke dilation (of some map), then `(𝒫, id, h)` is a
Paschke dilation of `h`. -/
theorem paschke_basics_2 (φ : 𝒜 → ℬ) (D : PaschkeTriple 𝒜 ℬ)
    (hD : IsPaschkeDilationOf D φ) :
    ∃ ι : NMIUMap D.P D.P, (∀ c, ι c = c) ∧
      IsPaschkeDilationOf ⟨D.P, D.vn, ι, D.h⟩ ⇑D.h := by
  -- `bsols.tex`, solution `paschke-basics`.2, transcribed.
  obtain ⟨idP, hidP⟩ := exists_ncpId D.P
  refine ⟨{ toStarAlgHom := StarAlgHom.id ℂ D.P
            preservesDirSups' := preservesDirSups_id },
    fun _ => rfl, fun _ => rfl, ?_⟩
  intro D' hD'
  -- "Consider `ϱ' ∘ ϱ` and `h'`": a Paschke triple over `𝒜` again.
  set ρE : NMIUMap 𝒜 D'.P :=
    { toStarAlgHom := D'.ρ.toStarAlgHom.comp D.ρ.toStarAlgHom
      preservesDirSups' :=
        preservesDirSups_pmap_comp (starAlgHomP D.ρ.toStarAlgHom)
          D.ρ.preservesDirSups' (starAlgHomP D'.ρ.toStarAlgHom)
          D'.ρ.preservesDirSups' } with hρE
  have hρEapp : ∀ a : 𝒜, ρE a = D'.ρ (D.ρ a) := fun _ => rfl
  have hE : ∀ a : 𝒜, D'.h (ρE a) = φ a := by
    intro a
    rw [hρEapp, hD' (D.ρ a), hD.1 a]
  -- "By the universal property of the original dilation, there is a unique
  -- ncp-map `σ : 𝒫' → 𝒫` with `σ ∘ ϱ' ∘ ϱ = ϱ` and `h ∘ σ = h'`."
  obtain ⟨σ, ⟨hσ1, hσ2⟩, hσu⟩ := hD.2 ⟨D'.P, D'.vn, ρE, D'.h⟩ hE
  -- "`id` is the unique ncp-map with `id ∘ ϱ = ϱ` and `h ∘ id = h`; and
  -- `σ ∘ ϱ'` is one such, so `σ ∘ ϱ' = id`."
  obtain ⟨τ, hτ⟩ := exists_ncpCompNMIU σ D'.ρ
  have hτid : ∀ c : D.P, σ (D'.ρ c) = c := by
    obtain ⟨σ₀, hσ₀, hσ₀u⟩ := hD.2 D hD.1
    have h1 : τ = idP :=
      (hσ₀u τ ⟨fun a => by rw [hτ]; exact hσ1 a,
          fun c => by rw [hτ, hσ2, hD' c]⟩).trans
        (hσ₀u idP ⟨fun a => by rw [hidP], fun c => by rw [hidP]⟩).symm
    intro c
    rw [← hτ c, h1, hidP]
  refine ⟨σ, ⟨hτid, hσ2⟩, ?_⟩
  -- uniqueness: any such `σ'` mediates for the original dilation too
  rintro σ' ⟨hσ'1, hσ'2⟩
  exact hσu σ' ⟨fun a => by rw [hρEapp]; exact hσ'1 (D.ρ a), hσ'2⟩

/-! ### Infrastructure: the abstract direct sum

**140X**.3 represents `ℬ₁ ⊕ ℬ₂` and `𝒫₁ ⊕ 𝒫₂` abstractly, by a von Neumann
algebra together with two nmiu-projections whose pairing is a bijection —
this avoids instance diamonds on product types, at the cost of having to
*derive* the properties of a biproduct from the bijection.  The one that
matters is that such a pair **reflects** positivity (`pair_nonneg_reflect`):
if `p₁ c ≥ 0` and `p₂ c ≥ 0` then `c ≥ 0`, because `pᵢ c = star bᵢ * bᵢ` and
a preimage `d` of `(b₁, b₂)` has `star d * d = c` by injectivity.  Everything
else — order reflection, and the pairing `⟨σ₁, σ₂⟩` of two ncp-maps being
again ncp — follows from it. -/

section Biproduct

variable {P P₁ P₂ : Type u}
  [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  [CStarAlgebra P₁] [PartialOrder P₁] [StarOrderedRing P₁]
  [CStarAlgebra P₂] [PartialOrder P₂] [StarOrderedRing P₂]

private theorem ncp_add {A B : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : NCPMap A B) (x y : A) : f (x + y) = f x + f y :=
  map_add f.toCompletelyPositiveMap.toLinearMap x y

private theorem ncp_smul {A B : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : NCPMap A B) (z : ℂ) (x : A) : f (z • x) = z • f x :=
  map_smul f.toCompletelyPositiveMap.toLinearMap z x

/-- An nmiu-map is monotone. -/
private theorem nmiu_monotone (f : NMIUMap P P₁) : Monotone ⇑f :=
  (starAlgHomP f.toStarAlgHom).monotone'

private theorem nmiu_mul (f : NMIUMap P P₁) (x y : P) : f (x * y) = f x * f y :=
  map_mul f.toStarAlgHom x y

private theorem nmiu_star (f : NMIUMap P P₁) (x : P) : f (star x) = star (f x) :=
  map_star f.toStarAlgHom x

private theorem nmiu_sub (f : NMIUMap P P₁) (x y : P) : f (x - y) = f x - f y :=
  map_sub f.toStarAlgHom x y

private theorem nmiu_add (f : NMIUMap P P₁) (x y : P) : f (x + y) = f x + f y :=
  map_add f.toStarAlgHom x y

private theorem nmiu_smul (f : NMIUMap P P₁) (z : ℂ) (x : P) : f (z • x) = z • f x :=
  map_smul f.toStarAlgHom z x

private theorem nmiu_sum {ι : Type*} (f : NMIUMap P P₁) (s : Finset ι) (g : ι → P) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) :=
  map_sum f.toStarAlgHom g s

/-- Positivity is *reflected* by a pair of nmiu-maps whose pairing is a
bijection: this is what makes the abstract representation of `𝒫₁ ⊕ 𝒫₂` in
**140X**.3 usable. -/
private theorem pair_nonneg_reflect (p₁ : NMIUMap P P₁) (p₂ : NMIUMap P P₂)
    (hp : Function.Bijective fun c : P => (p₁ c, p₂ c)) {c : P}
    (h1 : 0 ≤ p₁ c) (h2 : 0 ≤ p₂ c) : 0 ≤ c := by
  obtain ⟨b₁, hb₁⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h1
  obtain ⟨b₂, hb₂⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h2
  obtain ⟨d, hd⟩ := hp.2 (b₁, b₂)
  have hd1 : p₁ d = b₁ := congrArg Prod.fst hd
  have hd2 : p₂ d = b₂ := congrArg Prod.snd hd
  have hc : c = star d * d := by
    refine hp.1 ?_
    have e1 : p₁ (star d * d) = p₁ c := by
      rw [nmiu_mul, nmiu_star, hd1, ← hb₁]
    have e2 : p₂ (star d * d) = p₂ c := by
      rw [nmiu_mul, nmiu_star, hd2, ← hb₂]
    simp only [e1, e2]
  rw [hc]
  exact star_mul_self_nonneg d

private theorem pair_le_reflect (p₁ : NMIUMap P P₁) (p₂ : NMIUMap P P₂)
    (hp : Function.Bijective fun c : P => (p₁ c, p₂ c)) {c c' : P}
    (h1 : p₁ c ≤ p₁ c') (h2 : p₂ c ≤ p₂ c') : c ≤ c' := by
  rw [← sub_nonneg]
  refine pair_nonneg_reflect p₁ p₂ hp ?_ ?_
  · rw [nmiu_sub]; exact sub_nonneg.mpr h1
  · rw [nmiu_sub]; exact sub_nonneg.mpr h2

/-- The inverse of the pairing `c ↦ (p₁ c, p₂ c)`. -/
private noncomputable def pairInv (p₁ : NMIUMap P P₁) (p₂ : NMIUMap P P₂)
    (hp : Function.Bijective fun c : P => (p₁ c, p₂ c)) (b₁ : P₁) (b₂ : P₂) : P :=
  (Equiv.ofBijective _ hp).symm (b₁, b₂)

private theorem pairInv_spec (p₁ : NMIUMap P P₁) (p₂ : NMIUMap P P₂)
    (hp : Function.Bijective fun c : P => (p₁ c, p₂ c)) (b₁ : P₁) (b₂ : P₂) :
    p₁ (pairInv p₁ p₂ hp b₁ b₂) = b₁ ∧ p₂ (pairInv p₁ p₂ hp b₁ b₂) = b₂ := by
  have h := (Equiv.ofBijective _ hp).apply_symm_apply (b₁, b₂)
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Pairing two ncp-maps into an abstract direct sum. -/
private theorem exists_ncpPair {Q : Type u} [CStarAlgebra Q] [PartialOrder Q]
    [StarOrderedRing Q] (p₁ : NMIUMap P P₁) (p₂ : NMIUMap P P₂)
    (hp : Function.Bijective fun c : P => (p₁ c, p₂ c))
    (σ₁ : NCPMap Q P₁) (σ₂ : NCPMap Q P₂) :
    ∃ σ : NCPMap Q P, ∀ x, p₁ (σ x) = σ₁ x ∧ p₂ (σ x) = σ₂ x := by
  set f : Q → P := fun x => pairInv p₁ p₂ hp (σ₁ x) (σ₂ x) with hf
  have hs1 : ∀ x, p₁ (f x) = σ₁ x := fun x => (pairInv_spec p₁ p₂ hp _ _).1
  have hs2 : ∀ x, p₂ (f x) = σ₂ x := fun x => (pairInv_spec p₁ p₂ hp _ _).2
  have hinj : ∀ c c' : P, p₁ c = p₁ c' → p₂ c = p₂ c' → c = c' := by
    intro c c' h1 h2
    exact hp.1 (by simp only [h1, h2])
  have hadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    refine hinj _ _ ?_ ?_
    · rw [hs1, nmiu_add, hs1, hs1, ncp_add]
    · rw [hs2, nmiu_add, hs2, hs2, ncp_add]
  have hsmul : ∀ (z : ℂ) x, f (z • x) = z • f x := by
    intro z x
    refine hinj _ _ ?_ ?_
    · rw [hs1, nmiu_smul, hs1, ncp_smul]
    · rw [hs2, nmiu_smul, hs2, ncp_smul]
  set L : Q →ₗ[ℂ] P := { toFun := f, map_add' := hadd, map_smul' := hsmul } with hL
  have hLapp : ∀ x, L x = f x := fun _ => rfl
  -- complete positivity, from that of `σ₁` and `σ₂` and `pair_nonneg_reflect`
  have hcp1 : ∀ (n : ℕ) (a : Fin n → Q) (b : Fin n → P₁),
      0 ≤ ∑ i, ∑ j, star (b i) * σ₁ (star (a i) * a j) * b j :=
    (cp_iff σ₁.toCompletelyPositiveMap.toLinearMap).out 1 0 |>.mp fun N M hM =>
      σ₁.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hcp2 : ∀ (n : ℕ) (a : Fin n → Q) (b : Fin n → P₂),
      0 ≤ ∑ i, ∑ j, star (b i) * σ₂ (star (a i) * a j) * b j :=
    (cp_iff σ₂.toCompletelyPositiveMap.toLinearMap).out 1 0 |>.mp fun N M hM =>
      σ₂.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have key1 : ∀ (n : ℕ) (a : Fin n → Q) (b : Fin n → P),
      p₁ (∑ i, ∑ j, star (b i) * f (star (a i) * a j) * b j)
        = ∑ i, ∑ j, star (p₁ (b i)) * σ₁ (star (a i) * a j) * p₁ (b j) := by
    intro n a b
    rw [nmiu_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [nmiu_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [nmiu_mul, nmiu_mul, nmiu_star, hs1]
  have key2 : ∀ (n : ℕ) (a : Fin n → Q) (b : Fin n → P),
      p₂ (∑ i, ∑ j, star (b i) * f (star (a i) * a j) * b j)
        = ∑ i, ∑ j, star (p₂ (b i)) * σ₂ (star (a i) * a j) * p₂ (b j) := by
    intro n a b
    rw [nmiu_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [nmiu_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [nmiu_mul, nmiu_mul, nmiu_star, hs2]
  have hLcp : IsCompletelyPositiveMap L := by
    intro n a b
    have hgoal : (∑ i, ∑ j, star (b i) * L (star (a i) * a j) * b j)
        = ∑ i, ∑ j, star (b i) * f (star (a i) * a j) * b j := by
      simp only [hLapp]
    rw [hgoal]
    refine pair_nonneg_reflect p₁ p₂ hp ?_ ?_
    · rw [key1]; exact hcp1 n a _
    · rw [key2]; exact hcp2 n a _
  -- normality
  have hnorm : PreservesDirSups f := by
    intro D s hne hdir hlub
    have h1 := σ₁.preservesDirSups' D s hne hdir hlub
    have h2 := σ₂.preservesDirSups' D s hne hdir hlub
    have hu1 : ∀ d ∈ D, σ₁ (d : Q) ≤ σ₁ (s : Q) := fun d hd => h1.1 ⟨d, hd, rfl⟩
    have hu2 : ∀ d ∈ D, σ₂ (d : Q) ≤ σ₂ (s : Q) := fun d hd => h2.1 ⟨d, hd, rfl⟩
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      refine pair_le_reflect p₁ p₂ hp ?_ ?_
      · rw [hs1, hs1]; exact hu1 d hd
      · rw [hs2, hs2]; exact hu2 d hd
    · intro u hu
      have hu' : ∀ d ∈ D, f (d : Q) ≤ u := fun d hd => hu ⟨d, hd, rfl⟩
      refine pair_le_reflect p₁ p₂ hp ?_ ?_
      · rw [hs1]
        refine h1.2 ?_
        rintro _ ⟨d, hd, rfl⟩
        exact le_of_eq_of_le (hs1 (d : Q)).symm (nmiu_monotone p₁ (hu' d hd))
      · rw [hs2]
        refine h2.2 ?_
        rintro _ ⟨d, hd, rfl⟩
        exact le_of_eq_of_le (hs2 (d : Q)).symm (nmiu_monotone p₂ (hu' d hd))
  exact ⟨{ toCompletelyPositiveMap :=
             { toLinearMap := L
               map_cstarMatrix_nonneg' := (cp_iff L).out 0 1 |>.mp hLcp }
           preservesDirSups' := hnorm },
    fun x => ⟨hs1 x, hs2 x⟩⟩

/-- The composition of an ncp-map with an nmiu-map *after* it is an
ncp-map (the mirror image of `exists_ncpCompNMIU`). -/
private theorem exists_nmiuCompNCP {Q : Type u} [CStarAlgebra Q] [PartialOrder Q]
    [StarOrderedRing Q] (g : NMIUMap P P₁) (f : NCPMap Q P) :
    ∃ k : NCPMap Q P₁, ∀ a, k a = g (f a) := by
  set Lf : Q →ₗ[ℂ] P := f.toCompletelyPositiveMap.toLinearMap with hLf
  have hLfcp : IsCompletelyPositiveMap Lf :=
    (cp_iff Lf).out 1 0 |>.mp fun N M hM =>
      f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  set Lg : P →ₗ[ℂ] P₁ :=
    { toFun := fun a => g a
      map_add' := fun x y => map_add g.toStarAlgHom x y
      map_smul' := fun r x => map_smul g.toStarAlgHom r x } with hLg
  have hLgcp : IsCompletelyPositiveMap Lg :=
    cp_of_mi Lg (fun x y => map_mul g.toStarAlgHom x y)
      (fun x => map_star g.toStarAlgHom x)
  exact ⟨{ toCompletelyPositiveMap :=
             { toLinearMap := Lg.comp Lf
               map_cstarMatrix_nonneg' :=
                 (cp_iff (Lg.comp Lf)).out 0 1 |>.mp
                   (cp_comp Lf Lg hLfcp hLgcp) }
           preservesDirSups' :=
             preservesDirSups_pmap_comp (ncpP f) f.preservesDirSups'
               (starAlgHomP g.toStarAlgHom) g.preservesDirSups' },
    fun _ => rfl⟩

end Biproduct

/-- **140X** (`paschke-basics`, dils.tex:1204, Exercise), part 3: if
`(𝒫ᵢ, ϱᵢ, hᵢ)` is a Paschke dilation of `φᵢ : 𝒜 → ℬᵢ` (i = 1,2), then
`(𝒫₁ ⊕ 𝒫₂, ⟨ϱ₁, ϱ₂⟩, h₁ ⊕ h₂)` is a Paschke dilation of `⟨φ₁, φ₂⟩ : 𝒜 →
ℬ₁ ⊕ ℬ₂`.  (The direct sums are represented abstractly: von Neumann
algebras `ℬp`, `𝒫p` whose nmiu projections `πᵢ`, `pᵢ` pair bijectively
into the set-theoretic product, avoiding instance diamonds on product
types.) -/
theorem paschke_basics_3 {ℬ₁ ℬ₂ ℬp : Type u}
    [CStarAlgebra ℬ₁] [PartialOrder ℬ₁] [StarOrderedRing ℬ₁]
    [CStarAlgebra ℬ₂] [PartialOrder ℬ₂] [StarOrderedRing ℬ₂]
    [CStarAlgebra ℬp] [PartialOrder ℬp] [StarOrderedRing ℬp]
    (φ₁ : 𝒜 → ℬ₁) (φ₂ : 𝒜 → ℬ₂) (φ : 𝒜 → ℬp)
    (D₁ : PaschkeTriple 𝒜 ℬ₁) (D₂ : PaschkeTriple 𝒜 ℬ₂)
    (D : PaschkeTriple 𝒜 ℬp)
    (h₁ : IsPaschkeDilationOf D₁ φ₁) (h₂ : IsPaschkeDilationOf D₂ φ₂)
    (π₁ : NMIUMap ℬp ℬ₁) (π₂ : NMIUMap ℬp ℬ₂)
    (hπ : Function.Bijective fun b : ℬp => (π₁ b, π₂ b))
    (p₁ : NMIUMap D.P D₁.P) (p₂ : NMIUMap D.P D₂.P)
    (hp : Function.Bijective fun c : D.P => (p₁ c, p₂ c))
    (hφ : ∀ a, π₁ (φ a) = φ₁ a ∧ π₂ (φ a) = φ₂ a)
    (hρ : ∀ a, p₁ (D.ρ a) = D₁.ρ a ∧ p₂ (D.ρ a) = D₂.ρ a)
    (hh : ∀ c, π₁ (D.h c) = D₁.h (p₁ c) ∧ π₂ (D.h c) = D₂.h (p₂ c)) :
    IsPaschkeDilationOf D φ := by
  -- `bsols.tex`, solution `paschke-basics`.3, transcribed.

  have hinjB : ∀ b b' : ℬp, π₁ b = π₁ b' → π₂ b = π₂ b' → b = b' := by
    intro b b' e1 e2; exact hπ.1 (by simp only [e1, e2])
  have hinjP : ∀ c c' : D.P, p₁ c = p₁ c' → p₂ c = p₂ c' → c = c' := by
    intro c c' e1 e2; exact hp.1 (by simp only [e1, e2])
  constructor
  · -- `h₁ ⊕ h₂ ∘ ⟨ϱ₁, ϱ₂⟩ = ⟨φ₁, φ₂⟩`
    intro a
    refine hinjB _ _ ?_ ?_
    · rw [(hh _).1, (hρ a).1, h₁.1 a, (hφ a).1]
    · rw [(hh _).2, (hρ a).2, h₂.1 a, (hφ a).2]
  · intro D' hD'
    obtain ⟨k₁, hk₁⟩ := exists_nmiuCompNCP π₁ D'.h
    obtain ⟨k₂, hk₂⟩ := exists_nmiuCompNCP π₂ D'.h
    have hD'1 : ∀ a, k₁ (D'.ρ a) = φ₁ a := by
      intro a; rw [hk₁, hD' a, (hφ a).1]
    have hD'2 : ∀ a, k₂ (D'.ρ a) = φ₂ a := by
      intro a; rw [hk₂, hD' a, (hφ a).2]
    obtain ⟨σ₁, ⟨hσ₁a, hσ₁b⟩, huniq₁⟩ :=
      h₁.2 ⟨D'.P, D'.vn, D'.ρ, k₁⟩ hD'1
    obtain ⟨σ₂, ⟨hσ₂a, hσ₂b⟩, huniq₂⟩ :=
      h₂.2 ⟨D'.P, D'.vn, D'.ρ, k₂⟩ hD'2
    obtain ⟨σ, hσ⟩ := exists_ncpPair p₁ p₂ hp σ₁ σ₂
    refine ⟨σ, ⟨?_, ?_⟩, ?_⟩
    · intro a
      refine hinjP _ _ ?_ ?_
      · rw [(hσ _).1, hσ₁a a, (hρ a).1]
      · rw [(hσ _).2, hσ₂a a, (hρ a).2]
    · intro c
      refine hinjB _ _ ?_ ?_
      · rw [(hh _).1, (hσ _).1, hσ₁b c, hk₁]
      · rw [(hh _).2, (hσ _).2, hσ₂b c, hk₂]
    · rintro σ' ⟨hσ'a, hσ'b⟩
      obtain ⟨t₁, ht₁⟩ := exists_nmiuCompNCP p₁ σ'
      obtain ⟨t₂, ht₂⟩ := exists_nmiuCompNCP p₂ σ'
      have he₁ : t₁ = σ₁ := by
        refine huniq₁ t₁ ⟨fun a => ?_, fun c => ?_⟩
        · rw [ht₁, hσ'a a, (hρ a).1]
        · rw [ht₁, ← (hh (σ' c)).1, hσ'b c, hk₁]
      have he₂ : t₂ = σ₂ := by
        refine huniq₂ t₂ ⟨fun a => ?_, fun c => ?_⟩
        · rw [ht₂, hσ'a a, (hρ a).2]
        · rw [ht₂, ← (hh (σ' c)).2, hσ'b c, hk₂]
      refine DFunLike.ext _ _ fun c => ?_
      refine hinjP _ _ ?_ ?_
      · rw [← ht₁, he₁, ← (hσ c).1]
      · rw [← ht₂, he₂, ← (hσ c).2]

/-- **140X** (`paschke-basics`, dils.tex:1204, Exercise), part 4: if
`(𝒫, ϱ, h)` is a Paschke dilation of `φ` and `λ > 0`, then `(𝒫, ϱ, λh)` is
a Paschke dilation of `λφ`.

**140XI** (dils.tex:1236, Examples): forward references to
`paschke-tensor`, `paschke-corner`, `paschke-pure`,
`dils-filter-basics-exercise` — not converted here. -/
theorem paschke_basics_4 (φ : 𝒜 → ℬ) (D : PaschkeTriple 𝒜 ℬ)
    (hD : IsPaschkeDilationOf D φ) (l : ℝ) (hl : 0 < l) :
    ∃ h' : NCPMap D.P ℬ, (∀ c, h' c = (l : ℂ) • D.h c) ∧
      IsPaschkeDilationOf ⟨D.P, D.vn, D.ρ, h'⟩ (fun a => (l : ℂ) • φ a) := by
  -- `bsols.tex`, solution `paschke-basics`.4
  have hlne : ((l : ℂ)) ≠ 0 := by exact_mod_cast hl.ne'
  obtain ⟨h', hh'⟩ := exists_ncpSmul D.h hl
  refine ⟨h', hh', fun a => by rw [hh', hD.1 a], fun D' hD' => ?_⟩
  -- "then `λ⁻¹ h' ∘ ϱ' = φ`", so the original universal property applies
  obtain ⟨k, hk⟩ := exists_ncpSmul D'.h (inv_pos.mpr hl)
  have hk' : ∀ c, D'.h c = (l : ℂ) • k c := by
    intro c
    rw [hk, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hlne, one_smul]
  have hD'' : ∀ a, k (D'.ρ a) = φ a := by
    intro a
    rw [hk, hD' a, smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hlne, one_smul]
  obtain ⟨σ, ⟨hσ1, hσ2⟩, hσu⟩ :=
    hD.2 ⟨D'.P, D'.vn, D'.ρ, k⟩ hD''
  refine ⟨σ, ⟨hσ1, fun c => ?_⟩, ?_⟩
  · rw [hh', hσ2 c, ← hk' c]
  · rintro τ ⟨hτ1, hτ2⟩
    refine hσu τ ⟨hτ1, fun c => ?_⟩
    have h := hτ2 c
    rw [hh'] at h
    change D.h (τ c) = k c
    rw [hk, ← h, smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hlne, one_smul]

/-! ### **140VIII**: Paschke dilations are unique up to a unique
nmiu-isomorphism -/

/-- The composition of two ncp-maps is an ncp-map (the two mixed versions
are `exists_ncpCompNMIU` and `exists_nmiuCompNCP`). -/
private theorem exists_ncpComp {A B C : Type u} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (f : NCPMap B C) (g : NCPMap A B) :
    ∃ k : NCPMap A C, ∀ a, k a = f (g a) := by
  set Lg : A →ₗ[ℂ] B := g.toCompletelyPositiveMap.toLinearMap with hLg
  set Lf : B →ₗ[ℂ] C := f.toCompletelyPositiveMap.toLinearMap with hLf
  have hLgcp : IsCompletelyPositiveMap Lg :=
    (cp_iff Lg).out 1 0 |>.mp fun N M hM =>
      g.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hLfcp : IsCompletelyPositiveMap Lf :=
    (cp_iff Lf).out 1 0 |>.mp fun N M hM =>
      f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  exact ⟨{ toCompletelyPositiveMap :=
             { toLinearMap := Lf.comp Lg
               map_cstarMatrix_nonneg' :=
                 (cp_iff (Lf.comp Lg)).out 0 1 |>.mp
                   (cp_comp Lg Lf hLgcp hLfcp) }
           preservesDirSups' :=
             preservesDirSups_pmap_comp (ncpP g) g.preservesDirSups'
               (ncpP f) f.preservesDirSups' },
    fun _ => rfl⟩

/-- **140VIII** (`paschke-unique-up-to-iso`, dils.tex:1176, Lemma): two
Paschke dilations `(𝒫₁, ϱ₁, h₁)`, `(𝒫₂, ϱ₂, h₂)` of the same ncp-map `φ`
are related by a unique nmiu-isomorphism `ϑ : 𝒫₁ → 𝒫₂` with `ϑ ∘ ϱ₁ = ϱ₂`
and `h₂ ∘ ϑ = h₁`.

The author's proof (**140IX**) is transcribed up to its last step: the
mediating maps `σ : 𝒫₁ → 𝒫₂` and `τ : 𝒫₂ → 𝒫₁` compose to the identities
because `τ ∘ σ` and `id` both mediate `(𝒫₁,ϱ₁,h₁)` to itself, and `σ` is
unital because `σ(1) = σ(ϱ₁ 1) = ϱ₂ 1 = 1`.  For the last step the author
cites `iso` (proc.tex:878 = **99IX**), which lives in `A/Proc` — off this
chapter's import path (QUESTIONS **D3**).  Instead we run the standard
Kadison–Schwarz argument, which needs only `ncp_cp_cs` (**34XIV**) from
`A/VN`: for unital `σ`, `σ(x)*σ(x) ≤ σ(x*x)`, and applying `τ` (monotone,
also unital) to that inequality gives `x*x ≤ τ(σ(x)*σ(x)) ≤ τ(σ(x*x)) =
x*x`, so `σ(x*x) = σ(x)*σ(x)` by injectivity of `τ`.  The defect
`d(x,y) = σ(x*y) − σ(x)*σ(y)` is sesquilinear and vanishes on the
diagonal, so `d(x,y) = −d(y,x)` and (replacing `y` by `iy`) also
`d(x,y) = d(y,x)`; hence `d = 0` and `σ` is multiplicative. -/
theorem paschke_unique_up_to_iso (φ : 𝒜 → ℬ) (D₁ D₂ : PaschkeTriple 𝒜 ℬ)
    (h₁ : IsPaschkeDilationOf D₁ φ) (h₂ : IsPaschkeDilationOf D₂ φ) :
    ∃! ϑ : NMIUMap D₁.P D₂.P,
      Function.Bijective ⇑ϑ ∧ (∀ a, ϑ (D₁.ρ a) = D₂.ρ a) ∧
        ∀ c, D₂.h (ϑ c) = D₁.h c := by
  obtain ⟨σ, ⟨hσρ, hσh⟩, hσu⟩ := h₂.2 D₁ h₁.1
  obtain ⟨τ, ⟨hτρ, hτh⟩, -⟩ := h₁.2 D₂ h₂.1
  obtain ⟨id₁, hid₁⟩ := exists_ncpId D₁.P
  obtain ⟨id₂, hid₂⟩ := exists_ncpId D₂.P
  -- "It is easy to see `σ₁ ∘ σ₂` satisfies the same defining property as
  -- the unique mediating map `id`."
  have hτσ : ∀ c : D₁.P, τ (σ c) = c := by
    obtain ⟨ts, hts⟩ := exists_ncpComp τ σ
    obtain ⟨m, -, hmu⟩ := h₁.2 D₁ h₁.1
    have e1 : ts = m := hmu ts ⟨fun a => by rw [hts, hσρ, hτρ],
      fun c => by rw [hts, hτh, hσh]⟩
    have e2 : id₁ = m := hmu id₁ ⟨fun a => by rw [hid₁], fun c => by rw [hid₁]⟩
    intro c
    have h := DFunLike.congr_fun (e1.trans e2.symm) c
    rw [hts, hid₁] at h
    exact h
  have hστ : ∀ c : D₂.P, σ (τ c) = c := by
    obtain ⟨st, hst⟩ := exists_ncpComp σ τ
    obtain ⟨m, -, hmu⟩ := h₂.2 D₂ h₂.1
    have e1 : st = m := hmu st ⟨fun a => by rw [hst, hτρ, hσρ],
      fun c => by rw [hst, hσh, hτh]⟩
    have e2 : id₂ = m := hmu id₂ ⟨fun a => by rw [hid₂], fun c => by rw [hid₂]⟩
    intro c
    have h := DFunLike.congr_fun (e1.trans e2.symm) c
    rw [hst, hid₂] at h
    exact h
  have hσinj : Function.Injective ⇑σ := fun x y hxy => by
    have h : τ (σ x) = τ (σ y) := by rw [hxy]
    rwa [hτσ, hτσ] at h
  have hτinj : Function.Injective ⇑τ := fun x y hxy => by
    have h : σ (τ x) = σ (τ y) := by rw [hxy]
    rwa [hστ, hστ] at h
  -- "`ϑ(1) = ϑ(ϱ₁(1)) = ϱ₂(1) = 1`, and so `ϑ` is unital."
  have hρ₁1 : (D₁.ρ 1 : D₁.P) = 1 := map_one D₁.ρ.toStarAlgHom
  have hρ₂1 : (D₂.ρ 1 : D₂.P) = 1 := map_one D₂.ρ.toStarAlgHom
  have hσ1 : (σ 1 : D₂.P) = 1 := by
    have h := hσρ 1; rwa [hρ₁1, hρ₂1] at h
  have hτ1 : (τ 1 : D₁.P) = 1 := by
    have h := hτρ 1; rwa [hρ₂1, hρ₁1] at h
  have hσ0 : (σ 0 : D₂.P) = 0 := map_zero σ.toCompletelyPositiveMap.toLinearMap
  have hσadd : ∀ x y : D₁.P, (σ (x + y) : D₂.P) = σ x + σ y := ncp_add σ
  have hσsmul : ∀ (c : ℂ) (x : D₁.P), (σ (c • x) : D₂.P) = c • σ x :=
    fun c x => ncp_smul σ c x
  -- Kadison–Schwarz with equality on `x* x`
  have key : ∀ x : D₁.P, (σ (star x * x) : D₂.P) = star (σ x) * σ x := by
    rcases subsingleton_or_nontrivial D₂.P with _ | _
    · exact fun x => Subsingleton.elim _ _
    haveI : Nontrivial D₁.P :=
      ⟨⟨0, 1, fun h => zero_ne_one (α := D₂.P) (by rw [← hσ0, ← hσ1, h])⟩⟩
    intro x
    have hks : star (σ x : D₂.P) * σ x ≤ σ (star x * x) := by
      have h := ncp_cp_cs σ x
      rwa [hσ1, norm_one, one_smul] at h
    have hτks : star (x : D₁.P) * x ≤ τ (star (σ x) * σ x) := by
      have h := ncp_cp_cs τ (σ x)
      rw [hτ1, norm_one, one_smul, hτσ] at h
      exact h
    have hmono : τ (star (σ x) * σ x) ≤ τ (σ (star x * x)) := by
      have h := (ncpPositive τ).monotone' hks
      simpa using h
    refine (hτinj (le_antisymm hmono ?_)).symm
    rw [hτσ]
    exact hτks
  -- multiplicativity by polarization of the defect
  have main : ∀ x y : D₁.P, (σ (star x * y) : D₂.P) - star (σ x) * σ y = 0 := by
    obtain ⟨d, hdd⟩ : ∃ d : D₁.P → D₁.P → D₂.P,
        ∀ x y, d x y = (σ (star x * y) : D₂.P) - star (σ x) * σ y :=
      ⟨_, fun _ _ => rfl⟩
    have hdiag : ∀ x, d x x = 0 := fun x => by rw [hdd, key x, sub_self]
    have hadd₂ : ∀ x y z, d x (y + z) = d x y + d x z := by
      intro x y z; simp only [hdd, mul_add, hσadd]; abel
    have hadd₁ : ∀ x y z, d (x + y) z = d x z + d y z := by
      intro x y z; simp only [hdd, star_add, add_mul, hσadd]; abel
    have hsmul₂ : ∀ (c : ℂ) (x y), d x (c • y) = c • d x y := by
      intro c x y
      simp only [hdd, mul_smul_comm, hσsmul, smul_sub]
    have hsmul₁ : ∀ (c : ℂ) (x y), d (c • x) y = star c • d x y := by
      intro c x y
      simp only [hdd, star_smul, smul_mul_assoc, hσsmul, smul_sub]
    have hanti : ∀ x y, d x y + d y x = 0 := by
      intro x y
      have h := hdiag (x + y)
      rw [hadd₁ x y (x + y), hadd₂ x x y, hadd₂ y x y, hdiag x, hdiag y] at h
      simp only [zero_add, add_zero] at h
      exact h
    have hsymm : ∀ x y, d x y = d y x := by
      intro x y
      have h := hanti x (Complex.I • y)
      rw [hsmul₂ Complex.I x y, hsmul₁ Complex.I y x] at h
      have hI : (star Complex.I : ℂ) = -Complex.I := by
        simpa using Complex.conj_I
      rw [hI, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h
      rcases smul_eq_zero.mp h with h0 | h0
      · exact absurd h0 Complex.I_ne_zero
      · exact sub_eq_zero.mp h0
    intro x y
    have h2 : (2 : ℂ) • d x y = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hsymm x y]
      exact hanti x y
    have hd0 : d x y = 0 := by
      rcases smul_eq_zero.mp h2 with h0 | h0
      · exact absurd h0 (by norm_num)
      · exact h0
    rw [← hdd]
    exact hd0
  have hmul : ∀ x y : D₁.P, (σ (star x * y) : D₂.P) = star (σ x) * σ y :=
    fun x y => sub_eq_zero.mp (main x y)
  have hmulfull : ∀ x y : D₁.P, (σ (x * y) : D₂.P) = σ x * σ y := by
    intro x y
    have h := hmul (star x) y
    rw [star_star, ncp_star σ x, star_star] at h
    exact h
  have hcomm : ∀ r : ℂ,
      (σ (algebraMap ℂ D₁.P r) : D₂.P) = algebraMap ℂ D₂.P r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      hσsmul, hσ1]
  refine ⟨{ toStarAlgHom :=
              { toFun := fun c => σ c
                map_one' := hσ1
                map_mul' := hmulfull
                map_zero' := map_zero σ.toCompletelyPositiveMap.toLinearMap
                map_add' := hσadd
                commutes' := hcomm
                map_star' := fun c => ncp_star σ c }
            preservesDirSups' := σ.preservesDirSups' },
    ⟨⟨hσinj, fun y => ⟨τ y, hστ y⟩⟩, hσρ, hσh⟩, ?_⟩
  rintro ϑ' ⟨-, hϑ'ρ, hϑ'h⟩
  obtain ⟨k, hk⟩ := exists_ncpCompNMIU id₂ ϑ'
  have hkσ : k = σ :=
    hσu k ⟨fun a => by rw [hk, hid₂, hϑ'ρ], fun c => by rw [hk, hid₂, hϑ'h]⟩
  refine DFunLike.ext _ _ fun c => ?_
  have h := DFunLike.congr_fun hkσ c
  rw [hk, hid₂] at h
  exact h

end Paschke

end Theses.B.Dils

