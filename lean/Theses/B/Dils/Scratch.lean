import Theses.B.Dils.Stinespring

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u

namespace Theses.B.Dils

section Scratch

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The sesquilinear form `[a ⊗ x, b ⊗ y] = ⟪x, φ(a*b) y⟫` on `𝒜 ⊙ ℋ`. -/
noncomputable def stForm (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) :
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
theorem stForm_tmul (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) (a b : 𝒜) (x y : H) :
    stForm φ (a ⊗ₜ[ℂ] x) (b ⊗ₜ[ℂ] y) = ⟪x, φ (star a * b) y⟫ := rfl

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
/-- Every element of `𝒜 ⊙ ℋ` is a finite sum `∑ᵢ aᵢ ⊗ xᵢ`. -/
theorem exists_fin_rep (t : TensorProduct ℂ 𝒜 H) :
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
theorem stForm_sum (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) {m n : ℕ}
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
theorem cp_inner_nonneg (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
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
theorem stForm_nonneg (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositiveMap φ) (t : TensorProduct ℂ 𝒜 H) :
    0 ≤ stForm φ t t := by
  obtain ⟨n, a, x, rfl⟩ := exists_fin_rep t
  rw [stForm_sum]
  exact cp_inner_nonneg φ hφ a x

/-- Conjugate symmetry of `[·,·]` (dils.tex:410), from the fact that a
positive map preserves the involution (**10IV**). -/
theorem stForm_symm (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) (hp : IsPositiveMap φ)
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
noncomputable def rho0 (b : 𝒜) :
    TensorProduct ℂ 𝒜 H →ₗ[ℂ] TensorProduct ℂ 𝒜 H :=
  TensorProduct.map (LinearMap.mulLeft ℂ b) LinearMap.id

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
theorem rho0_tmul (b a : 𝒜) (x : H) :
    rho0 (H := H) b (a ⊗ₜ[ℂ] x) = (b * a) ⊗ₜ[ℂ] x := rfl

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
theorem rho0_sum (b : 𝒜) {n : ℕ} (a : Fin n → 𝒜) (x : Fin n → H) :
    rho0 b (∑ i, a i ⊗ₜ[ℂ] x i) = ∑ i, (b * a i) ⊗ₜ[ℂ] x i := by
  rw [map_sum]
  simp only [rho0_tmul]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
theorem rho0_one : rho0 (H := H) (1 : 𝒜) = LinearMap.id := by
  refine TensorProduct.ext' fun a x => ?_
  rw [rho0_tmul, one_mul]
  rfl

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
theorem rho0_mul (b b' : 𝒜) :
    rho0 (H := H) (b * b') = (rho0 b).comp (rho0 b') := by
  refine TensorProduct.ext' fun a x => ?_
  rw [rho0_tmul]
  rw [LinearMap.comp_apply, rho0_tmul, rho0_tmul, mul_assoc]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CompleteSpace H] in
/-- The adjointness computation of dils.tex:495:
`[ϱ₀(b*) s, t] = [s, ϱ₀(b) t]`. -/
theorem stForm_rho0_adj (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) (b : 𝒜)
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
theorem stForm_rho0_le (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
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
theorem stinespring_aux (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
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
theorem stinespring_normal_aux [VonNeumannAlgebra 𝒜]
    (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) (hφ : IsCompletelyPositiveMap φ)
    (hn : PreservesDirSups ⇑φ) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ϱ : NMIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (V : H →L[ℂ] 𝒦),
      (∀ a : 𝒜, φ a = conjOperator V (ϱ a)) ∧
      Dense (Submodule.span ℂ
        {k : 𝒦 | ∃ (a : 𝒜) (x : H), k = ϱ a (V x)} : Set 𝒦) := by
  obtain ⟨𝒦, hn1, hn2, hn3, ϱ, V, heq, -, hmin, hsep, hvec⟩ := stinespring_aux φ hφ
  have hp : IsPositiveMap φ := astara_pos_basic_2_cp φ hφ
  have hnormal : PreservesDirSups ⇑ϱ := by
    refine starAlgHom_preservesDirSups_of_vectors ϱ
      {k : 𝒦 | ∃ (a : 𝒜) (x : H), k = ϱ a (V x)} ?_ ?_
    · rintro R hR
      exact hsep R fun a x => hR _ ⟨a, x, rfl⟩
    · rintro y ⟨a, x, rfl⟩
      exact ⟨compNP (adPos a) (adPos_normal a)
        (compNP (toPos φ hp) hn (vectorNP x)), fun b => hvec a x b⟩
  refine ⟨𝒦, hn1, hn2, hn3, ⟨ϱ, hnormal⟩, V, ?_, ?_⟩
  · exact heq
  · exact hmin

theorem stinespring_T (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H)) (hφ : IsCompletelyPositiveMap φ) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ϱ : MIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (V : H →L[ℂ] 𝒦),
      ∀ a : 𝒜, φ a = conjOperator V (ϱ a) := by
  obtain ⟨𝒦, h1, h2, h3, ϱ, V, heq, -, -, -, -⟩ := stinespring_aux φ hφ
  exact ⟨𝒦, h1, h2, h3, ϱ, V, heq⟩

theorem stinespring_unital_T (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositiveMap φ) (hu : φ 1 = 1) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ϱ : MIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (V : H →L[ℂ] 𝒦),
      Isometry V ∧ ∀ a : 𝒜, φ a = conjOperator V (ϱ a) := by
  obtain ⟨𝒦, h1, h2, h3, ϱ, V, heq, hiso, -, -, -⟩ := stinespring_aux φ hφ
  exact ⟨𝒦, h1, h2, h3, ϱ, V, hiso hu, heq⟩

theorem stinespring_normal_T [VonNeumannAlgebra 𝒜] (φ : 𝒜 →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositiveMap φ) (hn : PreservesDirSups ⇑φ) :
    ∃ (𝒦 : Type u) (_ : NormedAddCommGroup 𝒦) (_ : InnerProductSpace ℂ 𝒦)
      (_ : CompleteSpace 𝒦) (ϱ : NMIUMap 𝒜 (𝒦 →L[ℂ] 𝒦)) (V : H →L[ℂ] 𝒦),
      ∀ a : 𝒜, φ a = conjOperator V (ϱ a) := by
  obtain ⟨𝒦, h1, h2, h3, ϱ, V, heq, -⟩ := stinespring_normal_aux φ hφ hn
  exact ⟨𝒦, h1, h2, h3, ϱ, V, heq⟩

theorem exists_minimal_T [VonNeumannAlgebra 𝒜] (φ : NCPMap 𝒜 (H →L[ℂ] H)) :
    ∃ D : StinespringDilation ⇑φ, D.Minimal := by
  set f : 𝒜 →ₗ[ℂ] (H →L[ℂ] H) := φ.toCompletelyPositiveMap.toLinearMap with hf
  have hcp : IsCompletelyPositiveMap f :=
    (cp_iff f).out 1 0 |>.mp fun N M hM =>
      φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hnn : PreservesDirSups ⇑f := φ.preservesDirSups'
  obtain ⟨𝒦, h1, h2, h3, ϱ, V, heq, hmin⟩ := stinespring_normal_aux f hcp hnn
  exact ⟨⟨𝒦, ϱ, V, heq⟩, hmin⟩

end Scratch

end Theses.B.Dils
