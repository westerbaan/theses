/-
Rieffel–van Daele scaffolding: the real-subspace machinery of

  M. A. Rieffel and A. van Daele, *A bounded operator approach to
  Tomita–Takesaki theory*, Pacific J. Math. **69** (1977) 187–221,

§2 and §3 up to Proposition 3.1.

This file is *machinery*, not a thesis point: it contains no von Neumann
algebras and no tensor products.  It is the first half of the single-algebra
package that the Rieffel–van Daele route to the commutation theorem needs; see
`docs/COMMUTATION-THEOREM.md` §4.

Everything is built on Mathlib's `Mathlib/Analysis/InnerProductSpace/StandardSubspace.lean`
(Y. Tanimoto, 2026), which supplies the real inner product space structure on a
complex Hilbert space, `ClosedSubmodule ℝ H`, `ClosedSubmodule.mulI` and the
`StandardSubspace` structure.

## Main definitions

For a closed *real* subspace `K` of a complex Hilbert space `H`:

* `Theses.RvD.P K`, `Theses.RvD.Q K` : the real-orthogonal projections onto `K`
  and onto `i K`, as elements of `H →L[ℝ] H`.
* `Theses.RvD.R K : H →L[ℂ] H` : `P + Q`, which is *complex* linear.
* `Theses.RvD.A K : H →L[ℝ] H` : `P - Q`, which is *conjugate* linear.
* `Theses.RvD.T K : H →L[ℂ] H` : `(R (2 - R)) ^ (1/2)`, by the complex
  continuous functional calculus.
* `Theses.RvD.J K : H →L[ℝ] H` : the continuous extension of `T ζ ↦ (P - Q) ζ`.
* `Theses.RvD.a K`, `Theses.RvD.b K` : `(R/2) ^ (1/2)` and `((2 - R)/2) ^ (1/2)`.

## Main results

* `R_isPositive`, `R_nonneg`, `R_le_two` : `0 ≤ R ≤ 2` (RvD Prop. 2.2);
  `A_smul_I` : `P - Q` is conjugate linear (RvD Prop. 3.1).
* `R_injective`, `two_sub_R_injective` : `R` and `2 - R` are injective — the first uses that
  `K + iK` is dense, the second that `K ∩ iK = 0` (RvD Prop. 2.2(1)).
* `T_injective`, `T_denseRange`, `P_comm_T`, `Q_comm_T`, `R_comm_T`, `A_comm_T`.
* `J_T`, `J_norm`, `J_smul` (conjugate linearity), `J_J` (involution) and `J_R` :
  `J R = (2 - R) J` (RvD Prop. 3.1); `Jequiv` bundles `J` as an `H ≃ₗᵢ⋆[ℂ] H`.
* `isModularPair_a_b` : `(a, b)` is a modular pair in the sense of
  `Theses/A/VN/Modular.lean` — the hand-off point.  `modularPair_data` is the same
  statement spelled out, with no dependency on that file.

The definition of `J` deliberately uses only the *complex* functional calculus of `R`
(`T` is `CFC.sqrt` of the complex-linear `R (2 - R)`); no functional calculus in the real
C⋆-algebra `B(H_ℝ)` is needed anywhere, and none exists in Mathlib.  The one step that looks
as if it needed one — that `T` commutes with the merely real-linear `P` — is obtained from
`cfc_mem`, applied to the commutant of `P` inside `B(H)` viewed as a closed *real*
⋆-subalgebra (`symCommutant`).
-/
import Theses.Common
import Theses.A.VN.Modular

open scoped ComplexInnerProductSpace
open Complex ClosedSubmodule

namespace Theses.RvD

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## The real inner product and multiplication by `i` -/

/-- Multiplication by `i` is a real-orthogonal transformation. -/
lemma real_inner_smul_I (x y : H) : inner ℝ (I • x) (I • y) = inner ℝ x y := by
  simp [inner_real_eq_re_inner]

/-- Membership in `i K`. -/
@[simp] lemma smul_I_mem_mulI_iff (K : ClosedSubmodule ℝ H) (y : H) :
    I • y ∈ K.mulI ↔ y ∈ K := by
  have := ClosedSubmodule.mem_mapEquiv_iff' (scalarSMulCLE H UnitI) K y
  simpa [Units.smul_def] using this

lemma mem_mulI_iff (K : ClosedSubmodule ℝ H) (x : H) : x ∈ K.mulI ↔ (-I) • x ∈ K := by
  constructor
  · intro hx
    have : I • ((-I) • x) ∈ K.mulI := by
      simpa [smul_smul] using hx
    exact (smul_I_mem_mulI_iff K _).1 this
  · intro hx
    have := (smul_I_mem_mulI_iff K _).2 hx
    simpa [smul_smul] using this

/-- A real-linear map commuting with multiplication by `i` is complex linear. -/
lemma smul_complex_of_smul_I {f : H →L[ℝ] H} (h : ∀ x, f (I • x) = I • f x) (c : ℂ) (x : H) :
    f (c • x) = c • f x := by
  have hs : ∀ (r : ℝ) (y : H), ((r : ℂ)) • y = r • y := fun r y => by
    rw [← Complex.coe_algebraMap, algebraMap_smul]
  have hc : ((c.re : ℂ) + (c.im : ℂ) * I) = c := Complex.re_add_im c
  calc f (c • x) = f ((c.re : ℝ) • x + (c.im : ℝ) • (I • x)) := by
        rw [← hs, ← hs, smul_smul, ← add_smul, hc]
    _ = (c.re : ℝ) • f x + (c.im : ℝ) • f (I • x) := by rw [map_add, map_smul, map_smul]
    _ = c • f x := by
        rw [h, ← hs c.re (f x), ← hs c.im (I • f x), smul_smul, ← add_smul, hc]

/-- A real-linear map anticommuting with multiplication by `i` is conjugate linear. -/
lemma smul_conj_of_smul_I {f : H →L[ℝ] H} (h : ∀ x, f (I • x) = -(I • f x)) (c : ℂ) (x : H) :
    f (c • x) = (starRingEnd ℂ) c • f x := by
  have hs : ∀ (r : ℝ) (y : H), ((r : ℂ)) • y = r • y := fun r y => by
    rw [← Complex.coe_algebraMap, algebraMap_smul]
  have hc : ((c.re : ℂ) + (c.im : ℂ) * I) = c := Complex.re_add_im c
  have hc' : ((c.re : ℂ) - (c.im : ℂ) * I) = (starRingEnd ℂ) c := by
    simp [Complex.ext_iff]
  calc f (c • x) = f ((c.re : ℝ) • x + (c.im : ℝ) • (I • x)) := by
        rw [← hs, ← hs, smul_smul, ← add_smul, hc]
    _ = (c.re : ℝ) • f x + (c.im : ℝ) • f (I • x) := by rw [map_add, map_smul, map_smul]
    _ = (starRingEnd ℂ) c • f x := by
        rw [h, smul_neg, ← hs c.re (f x), ← hs c.im (I • f x), smul_smul, ← neg_smul, ← add_smul,
          ← sub_eq_add_neg, hc']

variable [CompleteSpace H] (K : ClosedSubmodule ℝ H)

/-- The real-orthogonal projection onto the closed real subspace `K`. -/
noncomputable def P : H →L[ℝ] H := K.toSubmodule.starProjection

/-- The real-orthogonal projection onto `i K`. -/
noncomputable def Q : H →L[ℝ] H := K.mulI.toSubmodule.starProjection

lemma P_apply_mem (x : H) : P K x ∈ K := K.toSubmodule.starProjection_apply_mem x

lemma P_eq_self {K : ClosedSubmodule ℝ H} {x : H} (hx : x ∈ K) : P K x = x :=
  Submodule.starProjection_eq_self_iff.2 hx

lemma P_inner_eq_zero (v : H) {w : H} (hw : w ∈ K) : inner ℝ (v - P K v) w = 0 :=
  K.toSubmodule.starProjection_inner_eq_zero v w hw

/-- The engine of Rieffel–van Daele: `i P = Q i`. -/
lemma Q_smul_I (x : H) : Q K (I • x) = I • P K x := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact (smul_I_mem_mulI_iff K _).2 (P_apply_mem K x)
  · intro w hw
    obtain ⟨w₀, hw₀, rfl⟩ : ∃ w₀ ∈ K, w = I • w₀ :=
      ⟨(-I) • w, (mem_mulI_iff K w).1 hw, by simp [smul_smul]⟩
    have : I • x - I • P K x = I • (x - P K x) := by rw [smul_sub]
    rw [this, real_inner_smul_I]
    exact P_inner_eq_zero K x hw₀

lemma Q_eq_P_mulI : Q K = P K.mulI := rfl

lemma P_eq_Q_mulI : P K = Q K.mulI := by
  simp only [Q, P, mulI_mulI_eq]

lemma P_smul_I (x : H) : P K (I • x) = I • Q K x := by
  rw [P_eq_Q_mulI, Q_smul_I, ← Q_eq_P_mulI]

lemma P_symm (x y : H) : inner ℝ (P K x) y = inner ℝ x (P K y) :=
  Submodule.inner_starProjection_left_eq_right _ x y

lemma Q_symm (x y : H) : inner ℝ (Q K x) y = inner ℝ x (Q K y) :=
  Submodule.inner_starProjection_left_eq_right _ x y

@[simp] lemma P_idem (x : H) : P K (P K x) = P K x := P_eq_self (P_apply_mem K x)

@[simp] lemma Q_idem (x : H) : Q K (Q K x) = Q K x := P_idem K.mulI x

lemma inner_P_self (x : H) : inner ℝ (P K x) x = ‖P K x‖ ^ 2 := by
  rw [← P_idem K x, P_symm, P_idem, real_inner_self_eq_norm_sq]

lemma inner_Q_self (x : H) : inner ℝ (Q K x) x = ‖Q K x‖ ^ 2 := inner_P_self K.mulI x

/-! ## `R = P + Q` is complex linear -/

/-- `P + Q`, as a real-linear map. -/
noncomputable def Rre : H →L[ℝ] H := P K + Q K

@[simp] lemma Rre_apply (x : H) : Rre K x = P K x + Q K x := rfl

lemma Rre_smul_I (x : H) : Rre K (I • x) = I • Rre K x := by
  rw [Rre_apply, Rre_apply, P_smul_I, Q_smul_I, smul_add, add_comm]

/-- **RvD Prop. 3.1**: `R = P + Q` is complex linear. -/
noncomputable def R : H →L[ℂ] H where
  toFun := Rre K
  map_add' := map_add _
  map_smul' := smul_complex_of_smul_I (Rre_smul_I K)
  cont := (Rre K).continuous

@[simp] lemma R_apply (x : H) : R K x = P K x + Q K x := rfl

/-! ## `A = P - Q` is conjugate linear -/

/-- `P - Q`, as a real-linear map; it is conjugate linear (`A_smul_I`). -/
noncomputable def A : H →L[ℝ] H := P K - Q K

@[simp] lemma A_apply (x : H) : A K x = P K x - Q K x := rfl

/-- **RvD Prop. 3.1**: `P - Q` is conjugate linear. -/
lemma A_smul_I (x : H) : A K (I • x) = -(I • A K x) := by
  rw [A_apply, A_apply, P_smul_I, Q_smul_I, smul_sub, neg_sub]

lemma A_symm (x y : H) : inner ℝ (A K x) y = inner ℝ x (A K y) := by
  simp only [A_apply, inner_sub_left, inner_sub_right, P_symm, Q_symm]

/-! ## `R` is positive with `0 ≤ R ≤ 2` -/

lemma R_symm (x y : H) : inner ℝ (R K x) y = inner ℝ x (R K y) := by
  simp only [R_apply, inner_add_left, inner_add_right, P_symm, Q_symm]

omit [CompleteSpace H] in
/-- The imaginary part of the complex inner product, in terms of the real one. -/
lemma im_inner (u v : H) : (⟪u, v⟫).im = inner ℝ u ((-I) • v) := by
  rw [inner_real_eq_re_inner, inner_smul_right]
  simp

omit [CompleteSpace H] in
/-- A complex-linear operator symmetric for the *real* inner product is symmetric for the
complex one. -/
lemma isSymmetric_of_real_symm (f : H →L[ℂ] H) (h : ∀ x y, inner ℝ (f x) y = inner ℝ x (f y)) :
    (f : H →ₗ[ℂ] H).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  apply Complex.ext
  · exact h x y
  · rw [im_inner, im_inner, h x ((-I) • y), map_smul]

lemma R_isSymmetric : (R K : H →ₗ[ℂ] H).IsSymmetric := isSymmetric_of_real_symm _ (R_symm K)

lemma R_isSelfAdjoint : IsSelfAdjoint (R K) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (R_isSymmetric K)

lemma R_isPositive : (R K).IsPositive := by
  refine ⟨R_isSymmetric K, fun x => ?_⟩
  have h : (R K).reApplyInnerSelf x = ‖P K x‖ ^ 2 + ‖Q K x‖ ^ 2 := by
    have : (R K).reApplyInnerSelf x = inner ℝ (R K x) x := rfl
    rw [this, R_apply, inner_add_left, inner_P_self, inner_Q_self]
  rw [h]
  positivity

lemma R_nonneg : 0 ≤ R K := (ContinuousLinearMap.nonneg_iff_isPositive _).2 (R_isPositive K)

lemma two_sub_R_apply (x : H) : (2 - R K) x = (x - P K x) + (x - Q K x) := by
  have h2 : ((2 : H →L[ℂ] H)) x = x + x := by simp [two_smul]
  have h : (2 - R K) x = ((2 : H →L[ℂ] H)) x - R K x := by simp
  rw [h, h2, R_apply]
  abel

lemma inner_sub_P_self (x : H) : inner ℝ (x - P K x) x = ‖x - P K x‖ ^ 2 := by
  have h0 : inner ℝ (x - P K x) (P K x) = 0 := P_inner_eq_zero K x (P_apply_mem K x)
  have h1 : inner ℝ (x - P K x) (x - P K x)
      = inner ℝ (x - P K x) x - inner ℝ (x - P K x) (P K x) := inner_sub_right ..
  rw [← real_inner_self_eq_norm_sq, h1, h0, sub_zero]

lemma inner_sub_Q_self (x : H) : inner ℝ (x - Q K x) x = ‖x - Q K x‖ ^ 2 :=
  inner_sub_P_self K.mulI x

lemma two_sub_R_symm (x y : H) : inner ℝ ((2 - R K) x) y = inner ℝ x ((2 - R K) y) := by
  simp only [two_sub_R_apply, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    P_symm, Q_symm]

lemma two_sub_R_isPositive : (2 - R K).IsPositive := by
  refine ⟨isSymmetric_of_real_symm _ (two_sub_R_symm K), fun x => ?_⟩
  · have h : (2 - R K).reApplyInnerSelf x = ‖x - P K x‖ ^ 2 + ‖x - Q K x‖ ^ 2 := by
      have : (2 - R K).reApplyInnerSelf x = inner ℝ ((2 - R K) x) x := rfl
      rw [this, two_sub_R_apply, inner_add_left, inner_sub_P_self, inner_sub_Q_self]
    rw [h]
    positivity

/-- **RvD Prop. 2.2**: `R ≤ 2`. -/
lemma R_le_two : R K ≤ 2 := (ContinuousLinearMap.le_def _ _).2 (two_sub_R_isPositive K)

/-! ## Injectivity of `R` and of `2 - R` -/

private lemma sq_add_sq_eq_zero {a b : ℝ} (ha : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

/-- **RvD Prop. 2.2(1)**: `R` is injective, because `K + iK` is dense. -/
lemma R_injective (hcyc : K ⊔ K.mulI = ⊤) : Function.Injective (R K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h0 : ‖P K x‖ ^ 2 + ‖Q K x‖ ^ 2 = 0 := by
    have : inner ℝ (R K x) x = ‖P K x‖ ^ 2 + ‖Q K x‖ ^ 2 := by
      rw [R_apply, inner_add_left, inner_P_self, inner_Q_self]
    rw [← this, hx]
    simp
  obtain ⟨h1, h2⟩ := sq_add_sq_eq_zero h0
  have hP : P K x = 0 := norm_eq_zero.1 h1
  have hQ : Q K x = 0 := norm_eq_zero.1 h2
  have hx1 : x ∈ Kᗮ := by
    rw [← ClosedSubmodule.mem_orthogonal_toSubmodule_iff,
      ← Submodule.ker_starProjection K.toSubmodule]
    exact LinearMap.mem_ker.2 hP
  have hx2 : x ∈ K.mulIᗮ := by
    rw [← ClosedSubmodule.mem_orthogonal_toSubmodule_iff,
      ← Submodule.ker_starProjection K.mulI.toSubmodule]
    exact LinearMap.mem_ker.2 hQ
  have hmem : x ∈ (Kᗮ ⊓ K.mulIᗮ : ClosedSubmodule ℝ H) := ⟨hx1, hx2⟩
  rw [ClosedSubmodule.inf_orthogonal, hcyc, ClosedSubmodule.top_orthogonal_eq_bot] at hmem
  simpa using hmem

/-- **RvD Prop. 2.2(1)**: `2 - R` is injective, because `K ∩ iK = 0`. -/
lemma two_sub_R_injective (hsep : K ⊓ K.mulI = ⊥) :
    Function.Injective ((2 : H →L[ℂ] H) - R K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h0 : ‖x - P K x‖ ^ 2 + ‖x - Q K x‖ ^ 2 = 0 := by
    have : inner ℝ ((2 - R K) x) x = ‖x - P K x‖ ^ 2 + ‖x - Q K x‖ ^ 2 := by
      rw [two_sub_R_apply, inner_add_left, inner_sub_P_self, inner_sub_Q_self]
    rw [← this, hx]
    simp
  obtain ⟨h1, h2⟩ := sq_add_sq_eq_zero h0
  have hP : P K x = x := (sub_eq_zero.1 (norm_eq_zero.1 h1)).symm
  have hQ : Q K x = x := (sub_eq_zero.1 (norm_eq_zero.1 h2)).symm
  have hmem : x ∈ (K ⊓ K.mulI : ClosedSubmodule ℝ H) :=
    ⟨hP ▸ P_apply_mem K x, hQ ▸ P_apply_mem K.mulI x⟩
  rw [hsep] at hmem
  simpa using hmem

/-! ## `A ^ 2 = R (2 - R)` -/

lemma A_A_apply (x : H) : A K (A K x) = (R K * (2 - R K)) x := by
  simp only [mul_apply_eq_comp, A_apply, two_sub_R_apply, R_apply, map_sub,
    map_add, P_idem, Q_idem]
  abel

/-! ## `T = (R (2 - R)) ^ (1/2)` -/

lemma RtwoR_symm (x y : H) :
    inner ℝ ((R K * (2 - R K)) x) y = inner ℝ x ((R K * (2 - R K)) y) := by
  rw [← A_A_apply, ← A_A_apply, A_symm K (A K x) y, ← A_symm K x (A K y)]

lemma RtwoR_isPositive : (R K * (2 - R K)).IsPositive := by
  refine ⟨isSymmetric_of_real_symm _ (RtwoR_symm K), fun x => ?_⟩
  have h : (R K * (2 - R K)).reApplyInnerSelf x = ‖A K x‖ ^ 2 := by
    have h0 : (R K * (2 - R K)).reApplyInnerSelf x = inner ℝ ((R K * (2 - R K)) x) x := rfl
    rw [h0, ← A_A_apply, A_symm, real_inner_self_eq_norm_sq]
  rw [h]
  positivity

lemma RtwoR_nonneg : 0 ≤ R K * (2 - R K) :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).2 (RtwoR_isPositive K)

/-- `T = (R (2 - R)) ^ (1/2)`, by the *complex* continuous functional calculus. -/
noncomputable def T : H →L[ℂ] H := CFC.sqrt (R K * (2 - R K))

lemma T_nonneg : 0 ≤ T K := CFC.sqrt_nonneg _

lemma T_isSelfAdjoint : IsSelfAdjoint (T K) := .of_nonneg (T_nonneg K)

lemma T_mul_T : T K * T K = R K * (2 - R K) := CFC.sqrt_mul_sqrt_self _ (RtwoR_nonneg K)

/-- `T ^ 2 = (P - Q) ^ 2`. -/
lemma T_T_apply (x : H) : T K (T K x) = A K (A K x) := by
  rw [A_A_apply, ← T_mul_T]
  rfl

lemma T_symm (x y : H) : inner ℝ (T K x) y = inner ℝ x (T K y) := by
  have h := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (T_isSelfAdjoint K) x y
  simp only [ContinuousLinearMap.coe_coe] at h
  exact congrArg Complex.re h

/-- The identity that makes `J` well defined: `‖(P - Q) ζ‖ = ‖T ζ‖`. -/
lemma norm_A_eq_norm_T (x : H) : ‖A K x‖ = ‖T K x‖ := by
  have h1 : ‖A K x‖ ^ 2 = ‖T K x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, A_symm, T_symm, T_T_apply]
  exact le_antisymm (by nlinarith [norm_nonneg (A K x), norm_nonneg (T K x)])
    (by nlinarith [norm_nonneg (A K x), norm_nonneg (T K x)])

lemma RtwoR_injective (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤) :
    Function.Injective ⇑(R K * (2 - R K)) := fun _ _ h =>
  two_sub_R_injective K hsep (R_injective K hcyc h)

lemma T_injective (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤) :
    Function.Injective (T K) := by
  intro x y h
  refine RtwoR_injective K hsep hcyc ?_
  show (R K * (2 - R K)) x = (R K * (2 - R K)) y
  rw [← T_mul_T]
  show T K (T K x) = T K (T K y)
  rw [h]

/-- A self-adjoint injective operator has dense range. -/
lemma denseRange_of_isSelfAdjoint_injective {X : H →L[ℂ] H} (hX : IsSelfAdjoint X)
    (hinj : Function.Injective X) : DenseRange X := by
  have h1 : (LinearMap.range (X : H →ₗ[ℂ] H))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hXx : X x = 0 := by
      have h := hx (X (X x)) ⟨X x, rfl⟩
      have h2 : (⟪X (X x), x⟫ : ℂ) = ⟪X x, X x⟫ :=
        ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hX _ _
      rw [h2] at h
      exact inner_self_eq_zero.mp h
    have : X x = X 0 := by rw [hXx, map_zero]
    exact hinj this
  have h2 : (LinearMap.range (X : H →ₗ[ℂ] H)).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.2 h1
  have h3 : closure (Set.range X) = Set.univ := by
    have := congrArg (fun U : Submodule ℂ H => (U : Set H)) h2
    simpa [Submodule.topologicalClosure_coe, LinearMap.coe_range] using this
  exact dense_iff_closure_eq.2 h3

lemma T_denseRange (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤) :
    DenseRange (T K) :=
  denseRange_of_isSelfAdjoint_injective (T_isSelfAdjoint K) (T_injective K hsep hcyc)

lemma RtwoR_denseRange (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤) :
    DenseRange ⇑(R K * (2 - R K)) :=
  denseRange_of_isSelfAdjoint_injective (RtwoR_isPositive K).isSelfAdjoint
    (RtwoR_injective K hsep hcyc)

/-! ## `T` commutes with `P`, `Q`, `R` and `A`

`T` is a continuous function of `R (2 - R)` by the complex functional calculus, and `P`, `Q`
commute with `R (2 - R)`; the transfer from the operator to its square root is by the fact that
`cfc f a` lies in the closed ⋆-subalgebra generated by `a`, applied to the commutant of `P`
inside `B(H)` — a *closed real* ⋆-subalgebra, since `P` is real-linear only. -/

section Commutant

variable (f : H →L[ℝ] H) (hf : ∀ x y, inner ℝ (f x) y = inner ℝ x (f y))

/-- The commutant of a real-symmetric bounded real-linear operator `f`, inside `B(H)`:
a closed real ⋆-subalgebra. -/
def symCommutant : StarSubalgebra ℝ (H →L[ℂ] H) where
  carrier := {X | ∀ x, f (X x) = X (f x)}
  mul_mem' := by
    intro X Y hX hY x
    show f (X (Y x)) = X (Y (f x))
    rw [hX, hY]
  one_mem' := by intro x; rfl
  add_mem' := by
    intro X Y hX hY x
    show f (X x + Y x) = X (f x) + Y (f x)
    rw [map_add, hX, hY]
  zero_mem' := by intro x; simp
  algebraMap_mem' := by
    intro r x
    show f (r • x) = r • f x
    rw [map_smul]
  star_mem' := by
    intro X hX x
    have hadj : ∀ (Y : H →L[ℂ] H) (u v : H), inner ℝ ((star Y) u) v = inner ℝ u (Y v) := by
      intro Y u v
      have : (⟪(star Y) u, v⟫ : ℂ) = ⟪u, Y v⟫ := by
        rw [ContinuousLinearMap.star_eq_adjoint]
        exact ContinuousLinearMap.adjoint_inner_left Y v u
      exact congrArg Complex.re this
    refine ext_inner_right ℝ fun y => ?_
    calc inner ℝ (f ((star X) x)) y = inner ℝ ((star X) x) (f y) := hf _ _
      _ = inner ℝ x (X (f y)) := hadj X x (f y)
      _ = inner ℝ x (f (X y)) := by rw [hX]
      _ = inner ℝ (f x) (X y) := (hf x (X y)).symm
      _ = inner ℝ ((star X) (f x)) y := (hadj X (f x) y).symm

lemma mem_symCommutant_iff {X : H →L[ℂ] H} :
    X ∈ symCommutant f hf ↔ ∀ x, f (X x) = X (f x) := Iff.rfl

lemma isClosed_symCommutant : IsClosed ((symCommutant f hf : StarSubalgebra ℝ (H →L[ℂ] H)) :
    Set (H →L[ℂ] H)) := by
  have h : ((symCommutant f hf : StarSubalgebra ℝ (H →L[ℂ] H)) : Set (H →L[ℂ] H))
      = ⋂ x : H, {X : H →L[ℂ] H | f (X x) = X (f x)} := by
    ext X
    simp [mem_symCommutant_iff]
  rw [h]
  exact isClosed_iInter fun x => isClosed_eq (by fun_prop) (by fun_prop)

lemma cfc_mem_symCommutant (g : ℝ → ℝ) {X : H →L[ℂ] H} (hX : X ∈ symCommutant f hf) :
    cfc g X ∈ symCommutant f hf := by
  have := isClosed_symCommutant f hf
  exact cfc_mem (𝕜 := ℝ) (𝕜' := ℝ) g hX

end Commutant

lemma T_eq_cfc :
    T K = cfc (fun t : ℝ => ((NNReal.sqrt t.toNNReal : NNReal) : ℝ)) (R K * (2 - R K)) := by
  simp only [T, CFC.sqrt_eq_cfc]
  exact cfc_nnreal_eq_real _ _ (RtwoR_nonneg K)

lemma P_comm_RtwoR (x : H) : P K ((R K * (2 - R K)) x) = (R K * (2 - R K)) (P K x) := by
  simp only [← A_A_apply, A_apply, map_sub, P_idem, Q_idem]
  abel

lemma Q_comm_RtwoR (x : H) : Q K ((R K * (2 - R K)) x) = (R K * (2 - R K)) (Q K x) := by
  simp only [← A_A_apply, A_apply, map_sub, P_idem, Q_idem]
  abel

lemma P_comm_T (x : H) : P K (T K x) = T K (P K x) := by
  have hmem : (R K * (2 - R K)) ∈ symCommutant (P K) (P_symm K) := P_comm_RtwoR K
  have := cfc_mem_symCommutant (P K) (P_symm K)
    (fun t : ℝ => ((NNReal.sqrt t.toNNReal : NNReal) : ℝ)) hmem
  rw [← T_eq_cfc] at this
  exact this x

lemma Q_comm_T (x : H) : Q K (T K x) = T K (Q K x) := by
  have hmem : (R K * (2 - R K)) ∈ symCommutant (Q K) (Q_symm K) := Q_comm_RtwoR K
  have := cfc_mem_symCommutant (Q K) (Q_symm K)
    (fun t : ℝ => ((NNReal.sqrt t.toNNReal : NNReal) : ℝ)) hmem
  rw [← T_eq_cfc] at this
  exact this x

lemma A_comm_T (x : H) : A K (T K x) = T K (A K x) := by
  simp only [A_apply, map_sub, P_comm_T, Q_comm_T]

lemma R_comm_T (x : H) : R K (T K x) = T K (R K x) := by
  simp only [R_apply, map_add, P_comm_T, Q_comm_T]

lemma A_R_apply (x : H) : A K (R K x) = (2 - R K) (A K x) := by
  simp only [A_apply, R_apply, two_sub_R_apply, map_add, map_sub, P_idem, Q_idem]
  abel

/-! ## The conjugation `J`

`J` is defined as the continuous extension of `T ζ ↦ (P - Q) ζ`, which is legitimate because
`T ^ 2 = (P - Q) ^ 2` (so the assignment is isometric) and `T` has dense range.  Note that only
the *complex* functional calculus of `R` is used. -/

/-- The Tomita conjugation `J`: the continuous extension of `T ζ ↦ (P - Q) ζ`. -/
noncomputable def J : H →L[ℝ] H :=
  LinearMap.extendOfNorm (A K).toLinearMap ((T K).restrictScalars ℝ).toLinearMap

section Conjugation

variable (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤)

include hsep hcyc

/-- The defining property of `J`. -/
lemma J_T (x : H) : J K (T K x) = A K x :=
  LinearMap.extendOfNorm_eq (f := (A K).toLinearMap)
    (e := ((T K).restrictScalars ℝ).toLinearMap) (T_denseRange K hsep hcyc)
    ⟨1, fun y => by rw [one_mul]; exact le_of_eq (norm_A_eq_norm_T K y)⟩ x

/-- `J` is a real isometry. -/
lemma J_norm (x : H) : ‖J K x‖ = ‖x‖ := by
  refine (T_denseRange K hsep hcyc).induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro ζ
  rw [J_T K hsep hcyc, norm_A_eq_norm_T]

/-- `J` is conjugate linear. -/
lemma J_smul_I (x : H) : J K (I • x) = -(I • J K x) := by
  refine (T_denseRange K hsep hcyc).induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro ζ
  have h1 : I • T K ζ = T K (I • ζ) := (map_smul (T K) I ζ).symm
  rw [h1, J_T K hsep hcyc, J_T K hsep hcyc, A_smul_I]

lemma J_smul (c : ℂ) (x : H) : J K (c • x) = (starRingEnd ℂ) c • J K x :=
  smul_conj_of_smul_I (J_smul_I K hsep hcyc) c x

/-- `J` is an involution. -/
lemma J_J (x : H) : J K (J K x) = x := by
  refine (RtwoR_denseRange K hsep hcyc).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro ζ
  have hS : (R K * (2 - R K)) ζ = T K (T K ζ) := ((T_T_apply K ζ).trans (A_A_apply K ζ)).symm
  rw [hS, J_T K hsep hcyc, A_comm_T, J_T K hsep hcyc, T_T_apply]

/-- **RvD Prop. 3.1**: `J R = (2 - R) J`. -/
lemma J_R (x : H) : J K (R K x) = (2 - R K) (J K x) := by
  refine (T_denseRange K hsep hcyc).induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro ζ
  rw [R_comm_T, J_T K hsep hcyc, J_T K hsep hcyc, A_R_apply]

/-- `A = P - Q` factors as `J T`: this is the polar decomposition of `P - Q`. -/
lemma A_eq_J_T (x : H) : A K x = J K (T K x) := (J_T K hsep hcyc x).symm

/-- `J`, bundled as a conjugate-linear isometric involution of `H`. -/
noncomputable def Jequiv : H ≃ₗᵢ⋆[ℂ] H where
  toFun := J K
  map_add' := map_add _
  map_smul' := J_smul K hsep hcyc
  invFun := J K
  left_inv := J_J K hsep hcyc
  right_inv := J_J K hsep hcyc
  norm_map' := J_norm K hsep hcyc

@[simp] lemma Jequiv_apply (x : H) : Jequiv K hsep hcyc x = J K x := rfl

end Conjugation

/-! ## The modular pair `(a, b)`

This is the hand-off point to `Theses/A/VN/Modular.lean`: `(a, b)` is positive, commuting,
injective, with `a ^ 2 + b ^ 2 = 1`, i.e. a *modular pair* in the sense of Rieffel–van Daele,
and `Δ ^ (1/2) = b a⁻¹` on `ran a`. -/

/-- `a = (R / 2) ^ (1/2)`. -/
noncomputable def a : H →L[ℂ] H := CFC.sqrt ((2⁻¹ : ℝ) • R K)

/-- `b = ((2 - R) / 2) ^ (1/2)`. -/
noncomputable def b : H →L[ℂ] H := CFC.sqrt ((2⁻¹ : ℝ) • (2 - R K))

lemma half_R_nonneg : 0 ≤ (2⁻¹ : ℝ) • R K := smul_nonneg (by norm_num) (R_nonneg K)

lemma half_two_sub_R_nonneg : 0 ≤ (2⁻¹ : ℝ) • ((2 : H →L[ℂ] H) - R K) :=
  smul_nonneg (by norm_num)
    ((ContinuousLinearMap.nonneg_iff_isPositive _).2 (two_sub_R_isPositive K))

lemma a_nonneg : 0 ≤ a K := CFC.sqrt_nonneg _

lemma b_nonneg : 0 ≤ b K := CFC.sqrt_nonneg _

lemma a_mul_a : a K * a K = (2⁻¹ : ℝ) • R K := CFC.sqrt_mul_sqrt_self _ (half_R_nonneg K)

lemma b_mul_b : b K * b K = (2⁻¹ : ℝ) • ((2 : H →L[ℂ] H) - R K) :=
  CFC.sqrt_mul_sqrt_self _ (half_two_sub_R_nonneg K)

/-- `a ^ 2 + b ^ 2 = 1`. -/
lemma a_mul_a_add_b_mul_b : a K * a K + b K * b K = 1 := by
  rw [a_mul_a, b_mul_b, ← smul_add, show R K + (2 - R K) = 2 from by abel,
    show ((2 : H →L[ℂ] H)) = (2 : ℝ) • (1 : H →L[ℂ] H) from by rw [two_smul]; norm_num,
    smul_smul]
  norm_num

lemma commute_R_two_sub_R : Commute (R K) ((2 : H →L[ℂ] H) - R K) := by
  unfold Commute SemiconjBy
  noncomm_ring

/-- `a` and `b` commute: both are continuous functions of `R`. -/
lemma commute_a_b : Commute (a K) (b K) := by
  have hc : Commute ((2⁻¹ : ℝ) • R K) ((2⁻¹ : ℝ) • ((2 : H →L[ℂ] H) - R K)) :=
    ((commute_R_two_sub_R K).smul_left _).smul_right _
  have h1 : Commute (a K) ((2⁻¹ : ℝ) • ((2 : H →L[ℂ] H) - R K)) := by
    rw [a, CFC.sqrt_eq_cfc]
    exact hc.cfc_nnreal _
  have h2 : Commute (b K) (a K) := by
    rw [b, CFC.sqrt_eq_cfc]
    exact h1.symm.cfc_nnreal _
  exact h2.symm

lemma a_injective (hcyc : K ⊔ K.mulI = ⊤) : Function.Injective (a K) := by
  intro u v huv
  have h : ((2⁻¹ : ℝ) • R K) u = ((2⁻¹ : ℝ) • R K) v := by
    rw [← a_mul_a]
    show a K (a K u) = a K (a K v)
    rw [huv]
  simp only [smul_apply] at h
  exact R_injective K hcyc (smul_right_injective H (by norm_num : (2⁻¹ : ℝ) ≠ 0) h)

lemma b_injective (hsep : K ⊓ K.mulI = ⊥) : Function.Injective (b K) := by
  intro u v huv
  have h : ((2⁻¹ : ℝ) • ((2 : H →L[ℂ] H) - R K)) u = ((2⁻¹ : ℝ) • ((2 : H →L[ℂ] H) - R K)) v := by
    rw [← b_mul_b]
    show b K (b K u) = b K (b K v)
    rw [huv]
  simp only [smul_apply] at h
  exact two_sub_R_injective K hsep (smul_right_injective H (by norm_num : (2⁻¹ : ℝ) ≠ 0) h)

/-- The five properties of a modular pair, spelled out in elementary terms: the *statement*
names nothing from `Theses/A/VN/Modular.lean`, though this file does import it (line 53), so
there is no import-graph independence here.

(This is the unbundled twin of `isModularPair_a_b` below — same proof term, same hypotheses —
and it currently has no consumer; see `docs/DEAD-LIMBS.md` §8.  An earlier version of this
docstring claimed "no dependency on `Theses/A/VN/Modular.lean`", which the import contradicts.
Corrected 2026-08-26.) -/
theorem modularPair_data (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤) :
    0 ≤ a K ∧ 0 ≤ b K ∧ Commute (a K) (b K) ∧ Function.Injective (a K) ∧
      Function.Injective (b K) ∧ a K * a K + b K * b K = 1 :=
  ⟨a_nonneg K, b_nonneg K, commute_a_b K, a_injective K hcyc, b_injective K hsep,
    a_mul_a_add_b_mul_b K⟩

/-- **The hand-off to `Theses/A/VN/Modular.lean`**:
`(a, b) = ((R/2)^{1/2}, ((2-R)/2)^{1/2})` is a *modular pair* — positive, commuting, injective,
with `a ^ 2 + b ^ 2 = 1`.  The associated `opRatio a b` is `Δ ^ (1/2)`. -/
theorem isModularPair_a_b (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤) :
    IsModularPair (a K) (b K) :=
  ⟨a_nonneg K, b_nonneg K, commute_a_b K, a_injective K hcyc, b_injective K hsep,
    a_mul_a_add_b_mul_b K⟩

/-! ## Wrappers for Mathlib's `StandardSubspace`

A `StandardSubspace H` (Mathlib) is exactly a closed real subspace `K` with `K ⊓ iK = ⊥` and
`K ⊔ iK = ⊤`, so it packages the two hypotheses used above. -/

section Std

variable (S : StandardSubspace H)

/-- The Tomita conjugation of a standard subspace: a conjugate-linear isometric involution. -/
noncomputable def stdConj : H ≃ₗᵢ⋆[ℂ] H :=
  Jequiv S.toClosedSubmodule S.IsSeparating S.IsCyclic

@[simp] lemma stdConj_apply (x : H) : stdConj S x = J S.toClosedSubmodule x := rfl

lemma stdConj_stdConj (x : H) : stdConj S (stdConj S x) = x :=
  J_J S.toClosedSubmodule S.IsSeparating S.IsCyclic x

/-- `J R = (2 - R) J` for a standard subspace. -/
lemma stdConj_R (x : H) :
    stdConj S (R S.toClosedSubmodule x) = (2 - R S.toClosedSubmodule) (stdConj S x) :=
  J_R S.toClosedSubmodule S.IsSeparating S.IsCyclic x

/-- The modular pair of a standard subspace. -/
theorem stdIsModularPair : IsModularPair (a S.toClosedSubmodule) (b S.toClosedSubmodule) :=
  isModularPair_a_b S.toClosedSubmodule S.IsSeparating S.IsCyclic

end Std

end Theses.RvD
