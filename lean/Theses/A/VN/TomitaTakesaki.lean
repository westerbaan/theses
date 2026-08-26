/-
**Tomita's theorem** `J M J = M'`, in the bounded-operator formulation of

  M. A. Rieffel and A. van Daele, *A bounded operator approach to
  Tomita–Takesaki theory*, Pacific J. Math. **69** (1977) 187–221,

§4 (Lemma 4.3, Corollary 4.4, Lemma 4.9, Theorem 4.2(1)).

**This file has no thesis counterpart.**  It continues
`Theses/A/VN/Tomita.lean` (which proves RvD Prop. 4.1 and the Appendix
Proposition) towards the commutation theorem; see `docs/COMMUTATION-THEOREM.md`.

## Part I — the conjugation `J` as a ∗-antiautomorphism of `B(ℋ)`

For a closed real subspace `K` of a complex Hilbert space, with no von Neumann algebra in
sight:

* `J_real_symm`, `J_inner_swap`, `J_inner_map_map` : **RvD Prop. 3.1**,
  `⟪J ξ, η⟫ = ⟪J η, ξ⟫` and `⟪J ξ, J η⟫ = ⟪η, ξ⟫`.
* `adJ` : the ℂ-linear bounded operator `x ↦ J x J`, with `adJ_adJ`, `adJ_mul`, `adJ_star`,
  `adJ_one`, `adJ_add`, `adJ_smul` — a conjugate-linear involutive ∗-automorphism of `B(ℋ)`.
* `inner_J_mem_K_real` : for `ξ, η ∈ K`, `⟪J ξ, η⟫` is real.  This is the inclusion
  `J K ⊆ (iK)^⊥` used in RvD Lemma 4.9, read off from `𝒦 = a (fix J)` and `J a = b J`.

## Part II — RvD Lemma 4.9 and Theorem 4.2(1)

* `J_omega` : `J ω = ω`.
* `adJ_flip_sa`, `adJ_flip_right` : `⟪ω, y (J x J) ω⟫ = ⟪x (J y J) ω, ω⟫`, first for
  self-adjoint `x, y ∈ M` and then for arbitrary `y ∈ M`, both sides being ℂ-linear in `y`.
* `lemma_4_9` : **RvD Lemma 4.9**, `J M J ⊆ M'`, *given* `J M' J ⊆ M`.
* `tomita_JMJ`, `tomita_JM'J` : **RvD Theorem 4.2(1)**, `J M J = M'` and `J M' J = M`,
  given the same hypothesis.

## Part III — RvD Lemma 4.3 and Corollary 4.4

The hypothesis `J M' J ⊆ M` is RvD Lemma 4.8 at `t = 0`.  Its chain begins with Lemma 4.3,
a Hahn–Banach separation modelled on Sakai's linear Radon–Nikodym theorem, and this part
proves it, together with Corollary 4.4.

* `continuous_uw_inner_apply` : `x ↦ ⟪η, x ζ⟫` is ultraweakly continuous (polarisation into
  the vector np-functionals `vectorNP`).
* `isClosed_image_of_uwCompact`, `..._real` : the image of an ultraweakly compact set of
  operators under a map that is *weakly* continuous into `ℋ` is **norm**-closed.
* `isClosed_uw_of_bicommutant` : `M'' = M` makes `M` ultraweakly closed (**88VI**).
* `sepSet` : `P (λ · M_sa,≤1 · ω)`, with `sepSet_nonempty`, `sepSet_convex`,
  `sepSet_isClosed`.
* `exists_separating_of_notMem` : the strict separation, by the nearest-point projection in
  the *real* Hilbert space `ℋ`, with the separating vector taken in `M_sa ω`.
* `absOp`, `signApprox`, `norm_mul_signApprox_sub_absOp_le` : `h · h(|h|+ε)⁻¹ → |h|` in
  norm, the continuous substitute for the polar decomposition `h = u |h|` inside `M`.
* `inner_le_inner_absOp` : RvD's estimate `⟪h ω, x' ω⟫_ℝ ≤ ⟪ω, |h| ω⟫_ℝ` for `0 ≤ x' ≤ 1`
  in `M'`.
* `lemma_4_3_unit`, `lemma_4_3` : **RvD Lemma 4.3**.
* `Q_commutant_orbit`, `cor_4_4_sa`, `cor_4_4` : **RvD Corollary 4.4**, `J T x' ω = x ω`
  and `J T x'^* ω = x^* ω` for some `x ∈ M`.

## Two departures from the paper, both deliberate

1. Rieffel–van Daele separate in the **predual** of `M`, where the ball is weak-∗ compact.
   Here the separation is carried out in `ℋ` itself, by the nearest-point projection onto a
   closed convex set; ultraweak compactness of the ball of `M` (**77III**) is used only to
   know that `sepSet` is closed.  No predual, and no Hahn–Banach theorem, is needed.
2. Rieffel–van Daele use the polar decomposition `h = u|h|` of a self-adjoint `h ∈ M`,
   which needs a Borel functional calculus inside `M`.  Here `u` is replaced by the
   continuous `u_ε = h (|h| + ε)⁻¹`; only `‖h u_ε − |h|‖ ≤ ε` is used, and that is the
   continuous functional calculus alone.

## What is still missing

Lemma 4.5 (`T J x' J T = λ(2−R) x R + λ̄ R x (2−R)`), Lemma 4.6 (the Cauchy formula on the
strip `|Re z| ≤ 1/2`), Lemma 4.7 and Lemma 4.8.  Lemma 4.8 — even at `t = 0`, which is all
Theorem 4.2(1) needs — genuinely requires the unitary group `Δ^{it}`: its proof is a
Fourier inversion in `t`.
-/
import Theses.A.VN.Tomita

set_option linter.unusedSectionVars false

open Complex ClosedSubmodule Theses.A.VN
open scoped ComplexInnerProductSpace ComplexOrder

namespace Theses.RvD

/-! ## Part I: the conjugation `J` as a ∗-antiautomorphism of `B(ℋ)` -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (K : ClosedSubmodule ℝ H)

section JInner

variable (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤)

include hsep hcyc

omit hsep hcyc in
/-- `⟪x* u, v⟫ = ⟪u, x v⟫`. -/
lemma inner_star_left (Y : H →L[ℂ] H) (u v : H) : (⟪(star Y) u, v⟫ : ℂ) = ⟪u, Y v⟫ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left Y v u

omit hsep hcyc in
/-- `⟪x u, v⟫ = ⟪u, x* v⟫`. -/
lemma inner_apply_left (Y : H →L[ℂ] H) (u v : H) : (⟪Y u, v⟫ : ℂ) = ⟪u, (star Y) v⟫ := by
  have h := inner_star_left (star Y) u v
  rwa [star_star] at h

/-- `J` is symmetric for the *real* inner product: `⟪J ξ, η⟫_ℝ = ⟪ξ, J η⟫_ℝ`.
On `ran T` this is `A = J T` together with `A T = T A` and the symmetry of `A` and `T`;
both sides are continuous, and `ran T` is dense. -/
lemma J_real_symm (x y : H) : inner ℝ (J K x) y = inner ℝ x (J K y) := by
  -- first on `ran T × ran T`
  have base : ∀ u v : H, inner ℝ (J K (T K u)) (T K v) = inner ℝ (T K u) (J K (T K v)) := by
    intro u v
    rw [J_T K hsep hcyc, J_T K hsep hcyc]
    calc inner ℝ (A K u) (T K v) = inner ℝ u (A K (T K v)) := A_symm K u (T K v)
      _ = inner ℝ u (T K (A K v)) := by rw [A_comm_T]
      _ = inner ℝ (T K u) (A K v) := (T_symm K u (A K v)).symm
  -- extend in the second variable
  have step : ∀ u : H, ∀ y : H, inner ℝ (J K (T K u)) y = inner ℝ (T K u) (J K y) := by
    intro u
    refine fun y => (T_denseRange K hsep hcyc).induction_on y
      (isClosed_eq (by fun_prop) (by fun_prop)) (base u)
  -- extend in the first variable
  refine (T_denseRange K hsep hcyc).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) (fun u => step u y)

/-- **RvD Prop. 3.1**: `⟪J ξ, η⟫ = ⟪J η, ξ⟫`.  The real parts agree by `J_real_symm` and
the symmetry of the real inner product; the imaginary parts agree because `J` is conjugate
linear. -/
lemma J_inner_swap (x y : H) : (⟪J K x, y⟫ : ℂ) = ⟪J K y, x⟫ := by
  refine Complex.ext ?_ ?_
  · show (inner ℝ (J K x) y : ℝ) = inner ℝ (J K y) x
    rw [J_real_symm K hsep hcyc, real_inner_comm]
  · rw [im_inner, im_inner]
    have h1 : inner ℝ (J K x) ((-I) • y) = inner ℝ x (J K ((-I) • y)) :=
      J_real_symm K hsep hcyc _ _
    have h2 : J K ((-I : ℂ) • y) = (I : ℂ) • J K y := by
      rw [J_smul K hsep hcyc]
      simp
    have h3 : inner ℝ (J K y) ((-I) • x) = inner ℝ ((I : ℂ) • (J K y)) ((I : ℂ) • ((-I) • x)) :=
      (real_inner_smul_I _ _).symm
    rw [h1, h2, h3, real_inner_comm]
    congr 1
    rw [smul_smul]
    simp

/-- `J` is antiunitary: `⟪J ξ, J η⟫ = ⟪η, ξ⟫`. -/
lemma J_inner_map_map (x y : H) : (⟪J K x, J K y⟫ : ℂ) = ⟪y, x⟫ := by
  rw [J_inner_swap K hsep hcyc, J_J K hsep hcyc]

/-! ### `J x J` -/

/-- `J x J`, as a real-linear map. -/
noncomputable def adJre (x : H →L[ℂ] H) : H →L[ℝ] H :=
  (J K) ∘L (x.restrictScalars ℝ) ∘L (J K)

@[simp] lemma adJre_apply (x : H →L[ℂ] H) (ζ : H) : adJre K x ζ = J K (x (J K ζ)) := rfl

lemma adJre_smul_I (x : H →L[ℂ] H) (ζ : H) : adJre K x (I • ζ) = I • adJre K x ζ := by
  show J K (x (J K (I • ζ))) = I • J K (x (J K ζ))
  rw [J_smul_I K hsep hcyc, map_neg, map_smul, map_neg, J_smul_I K hsep hcyc, neg_neg]

/-- **`J x J`**, as a bounded ℂ-linear operator.  It is ℂ-linear because two conjugations
compose. -/
noncomputable def adJ (x : H →L[ℂ] H) : H →L[ℂ] H where
  toFun := adJre K x
  map_add' := map_add _
  map_smul' := smul_complex_of_smul_I (adJre_smul_I K hsep hcyc x)
  cont := (adJre K x).continuous

@[simp] lemma adJ_apply (x : H →L[ℂ] H) (ζ : H) :
    adJ K hsep hcyc x ζ = J K (x (J K ζ)) := rfl

@[simp] lemma adJ_one : adJ K hsep hcyc 1 = 1 := by
  ext ζ; simp [J_J K hsep hcyc]

lemma adJ_adJ (x : H →L[ℂ] H) : adJ K hsep hcyc (adJ K hsep hcyc x) = x := by
  ext ζ; simp [J_J K hsep hcyc]

lemma adJ_mul (x y : H →L[ℂ] H) :
    adJ K hsep hcyc (x * y) = adJ K hsep hcyc x * adJ K hsep hcyc y := by
  ext ζ
  show J K ((x * y) (J K ζ)) = J K (x (J K (J K (y (J K ζ)))))
  rw [J_J K hsep hcyc]
  rfl

/-- `(J x J)* = J x* J`. -/
lemma adJ_star (x : H →L[ℂ] H) :
    adJ K hsep hcyc (star x) = star (adJ K hsep hcyc x) := by
  refine ContinuousLinearMap.ext fun ζ => ?_
  refine ext_inner_right ℂ fun η => ?_
  have hstar : ∀ (Y : H →L[ℂ] H) (u v : H), (⟪(star Y) u, v⟫ : ℂ) = ⟪u, Y v⟫ := by
    intro Y u v
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_left Y v u
  rw [hstar (adJ K hsep hcyc x) ζ η]
  show (⟪J K ((star x) (J K ζ)), η⟫ : ℂ) = ⟪ζ, J K (x (J K η))⟫
  rw [J_inner_swap K hsep hcyc]
  calc (⟪J K η, (star x) (J K ζ)⟫ : ℂ) = ⟪x (J K η), J K ζ⟫ := by
        have h := hstar (star x) (J K η) (J K ζ)
        rw [star_star] at h
        exact h.symm
    _ = ⟪J K (J K (x (J K η))), J K ζ⟫ := by rw [J_J K hsep hcyc]
    _ = ⟪ζ, J K (x (J K η))⟫ := J_inner_map_map K hsep hcyc _ _

/-- `J (·) J` is conjugate linear. -/
lemma adJ_smul (c : ℂ) (x : H →L[ℂ] H) :
    adJ K hsep hcyc (c • x) = (starRingEnd ℂ) c • adJ K hsep hcyc x := by
  ext ζ
  show J K ((c • x) (J K ζ)) = (starRingEnd ℂ) c • J K (x (J K ζ))
  show J K (c • x (J K ζ)) = _
  rw [J_smul K hsep hcyc]

lemma adJ_add (x y : H →L[ℂ] H) :
    adJ K hsep hcyc (x + y) = adJ K hsep hcyc x + adJ K hsep hcyc y := by
  ext ζ
  show J K ((x + y) (J K ζ)) = J K (x (J K ζ)) + J K (y (J K ζ))
  show J K (x (J K ζ) + y (J K ζ)) = _
  rw [map_add]

/-- **`J K ⊆ (i K)^⊥`**, in the form used by RvD Lemma 4.9: for `ξ, η ∈ K` the number
`⟪J ξ, η⟫` is real.  Writing `ξ = a u` and `η = a v` with `J u = u`, `J v = v`
(`mem_K_iff`), `J ξ = b u` and `⟪b u, a v⟫ = ⟪u, a b v⟫` with `J (a b v) = a b v`; and `J`
is antiunitary, so `⟪u, w⟫ = ⟪w, u⟫` whenever `J u = u` and `J w = w`. -/
lemma inner_J_mem_K_real {ξ η : H} (hξ : ξ ∈ K) (hη : η ∈ K) :
    (⟪J K ξ, η⟫ : ℂ).im = 0 := by
  obtain ⟨u, hu, rfl⟩ := (mem_K_iff K hsep hcyc ξ).1 hξ
  obtain ⟨v, hv, rfl⟩ := (mem_K_iff K hsep hcyc η).1 hη
  have hJab : J K (a K (b K v)) = a K (b K v) := by
    rw [J_a K hsep hcyc, J_b K hsep hcyc, hv]
    exact commute_apply (commute_a_b K).symm v
  have hval : (⟪J K (a K u), a K v⟫ : ℂ) = ⟪u, a K (b K v)⟫ := by
    rw [J_a K hsep hcyc, hu]
    have h1 : (⟪b K u, a K v⟫ : ℂ) = ⟪u, b K (a K v)⟫ := by
      have := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (IsSelfAdjoint.of_nonneg (b_nonneg K)) u (a K v)
      simpa using this
    rw [h1]
    congr 1
    exact commute_apply (commute_a_b K).symm v
  rw [hval]
  have hsym : (⟪u, a K (b K v)⟫ : ℂ) = ⟪a K (b K v), u⟫ := by
    have h := J_inner_map_map K hsep hcyc u (a K (b K v))
    rw [hu, hJab] at h
    exact h
  have h3 : (⟪a K (b K v), u⟫ : ℂ) = (starRingEnd ℂ) ⟪u, a K (b K v)⟫ :=
    (inner_conj_symm _ _).symm
  rw [h3] at hsym
  have h4 := congrArg Complex.im hsym
  simp only [Complex.conj_im] at h4
  linarith

end JInner

/-! ## Part II: von Neumann algebras — RvD Lemma 4.9 and Theorem 4.2(1) -/

section BH

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (ω : ℋ)

/-- Two vectors with the same inner products against a dense set are equal. -/
lemma eq_of_inner_eq_on_dense {S : Set ℋ} (hS : Dense S) {u v : ℋ}
    (h : ∀ w ∈ S, (⟪w, u⟫ : ℂ) = ⟪w, v⟫) : u = v := by
  have hcl : IsClosed {w : ℋ | (⟪w, u⟫ : ℂ) = ⟪w, v⟫} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have huniv : {w : ℋ | (⟪w, u⟫ : ℂ) = ⟪w, v⟫} = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hS.closure_eq]
    exact hcl.closure_subset_iff.2 h
  have hmem : (⟪u - v, u⟫ : ℂ) = ⟪u - v, v⟫ := by
    have : (u - v) ∈ {w : ℋ | (⟪w, u⟫ : ℂ) = ⟪w, v⟫} := by rw [huniv]; trivial
    exact this
  have hzero : (⟪u - v, u - v⟫ : ℂ) = 0 := by rw [inner_sub_right, hmem, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 hzero)

section Tomita2

variable (hsep : Ksub M ω ⊓ (Ksub M ω).mulI = ⊥) (hcyc : Ksub M ω ⊔ (Ksub M ω).mulI = ⊤)

include hsep hcyc

/-- `J x J` for the standard subspace `𝒦 = closure (M_sa ω)`. -/
noncomputable abbrev vnAdJ (x : ℋ →L[ℂ] ℋ) : ℋ →L[ℂ] ℋ := adJ (Ksub M ω) hsep hcyc x

@[simp] lemma vnAdJ_apply (x : ℋ →L[ℂ] ℋ) (ζ : ℋ) :
    vnAdJ M ω hsep hcyc x ζ = J (Ksub M ω) (x (J (Ksub M ω) ζ)) := rfl

lemma vnAdJ_add (x y : ℋ →L[ℂ] ℋ) :
    vnAdJ M ω hsep hcyc (x + y) = vnAdJ M ω hsep hcyc x + vnAdJ M ω hsep hcyc y :=
  adJ_add _ hsep hcyc x y

lemma vnAdJ_smul (c : ℂ) (x : ℋ →L[ℂ] ℋ) :
    vnAdJ M ω hsep hcyc (c • x) = (starRingEnd ℂ) c • vnAdJ M ω hsep hcyc x :=
  adJ_smul _ hsep hcyc c x

lemma vnAdJ_mul (x y : ℋ →L[ℂ] ℋ) :
    vnAdJ M ω hsep hcyc (x * y) = vnAdJ M ω hsep hcyc x * vnAdJ M ω hsep hcyc y :=
  adJ_mul _ hsep hcyc x y

lemma vnAdJ_star (x : ℋ →L[ℂ] ℋ) :
    vnAdJ M ω hsep hcyc (star x) = star (vnAdJ M ω hsep hcyc x) :=
  adJ_star _ hsep hcyc x

lemma vnAdJ_vnAdJ (x : ℋ →L[ℂ] ℋ) :
    vnAdJ M ω hsep hcyc (vnAdJ M ω hsep hcyc x) = x :=
  adJ_adJ _ hsep hcyc x

/-- `J (x + i y) J = J x J - i J y J`. -/
lemma vnAdJ_sa_decomp (p q : ℋ →L[ℂ] ℋ) :
    vnAdJ M ω hsep hcyc (p + I • q)
      = vnAdJ M ω hsep hcyc p + (-I : ℂ) • vnAdJ M ω hsep hcyc q := by
  rw [vnAdJ_add, vnAdJ_smul]
  simp

/-! ### `J ω = ω` -/

omit hsep hcyc in
/-- `ω ∈ 𝒦`, since `1 ∈ M` is self-adjoint. -/
lemma omega_mem_Ksub : ω ∈ Ksub M ω := by
  have := mem_Ksub_of_sa M ω (one_mem M) (IsSelfAdjoint.one (ℋ →L[ℂ] ℋ))
  simpa using this

/-- `Q ω = 0`: `ω = 1 ω` lies in `M'_sa ω ⊆ (i𝒦)^⊥`. -/
lemma Q_omega : Q (Ksub M ω) ω = 0 := by
  have h1 : (1 : ℋ →L[ℂ] ℋ) ∈ commutantSA M := by
    rw [mem_commutantSA]; intro m _; rw [mul_one, one_mul]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _) ?_
  intro w hw
  obtain ⟨w₀, hw₀, rfl⟩ : ∃ w₀ ∈ Ksub M ω, w = (I : ℂ) • w₀ :=
    ⟨(-I : ℂ) • w, (mem_mulI_iff (Ksub M ω) w).1 hw, by simp [smul_smul]⟩
  rw [sub_zero, real_inner_comm]
  have := real_inner_mulI_orbit M ω h1 (IsSelfAdjoint.one (ℋ →L[ℂ] ℋ)) hw₀
  simpa using this

lemma R_omega : R (Ksub M ω) ω = ω := by
  rw [R_apply, Q_omega M ω hsep hcyc, add_zero]
  exact P_eq_self (omega_mem_Ksub M ω)

lemma two_sub_R_omega : ((2 : ℋ →L[ℂ] ℋ) - R (Ksub M ω)) ω = ω := by
  rw [two_sub_R_apply, P_eq_self (omega_mem_Ksub M ω), Q_omega M ω hsep hcyc, sub_self, zero_add,
    sub_zero]


lemma T_omega : T (Ksub M ω) ω = ω := by
  set K := Ksub M ω with hK
  have hsq : T K (T K ω) = ω := by
    rw [T_T_apply, A_A_apply]
    show (R K * (2 - R K)) ω = ω
    show R K (((2 : ℋ →L[ℂ] ℋ) - R K) ω) = ω
    rw [two_sub_R_omega M ω hsep hcyc, R_omega M ω hsep hcyc]
  set ζ : ℋ := T K ω - ω with hζ
  have hkey : T K ζ + ζ = 0 := by
    rw [hζ, map_sub, hsq]
    abel
  have hpos : (0 : ℝ) ≤ inner ℝ (T K ζ) ζ :=
    ((ContinuousLinearMap.nonneg_iff_isPositive (T K)).1 (T_nonneg K)).2 ζ
  have hz : inner ℝ (T K ζ) ζ + ‖ζ‖ ^ 2 = 0 := by
    have : inner ℝ (T K ζ + ζ) ζ = (0 : ℝ) := by rw [hkey]; simp
    rwa [inner_add_left, real_inner_self_eq_norm_sq] at this
  have : ζ = 0 := by
    have h0 : ‖ζ‖ ^ 2 ≤ 0 := by linarith
    have : ‖ζ‖ = 0 := by nlinarith [norm_nonneg ζ]
    exact norm_eq_zero.1 this
  rw [hζ] at this
  exact sub_eq_zero.1 this

/-- **`J ω = ω`** (RvD, first line of Lemma 4.9). -/
lemma J_omega : J (Ksub M ω) ω = ω := by
  have := J_T (Ksub M ω) hsep hcyc ω
  rw [T_omega M ω hsep hcyc] at this
  rw [this, A_apply, P_eq_self (omega_mem_Ksub M ω), Q_omega M ω hsep hcyc, sub_zero]

@[simp] lemma vnAdJ_omega (x : ℋ →L[ℂ] ℋ) : vnAdJ M ω hsep hcyc x ω = J (Ksub M ω) (x ω) := by
  rw [vnAdJ_apply, J_omega M ω hsep hcyc]

/-- `⟪ω, J v⟫ = ⟪v, ω⟫`, since `J ω = ω` and `⟪J ξ, η⟫ = ⟪J η, ξ⟫`. -/
lemma inner_omega_J (v : ℋ) : (⟪ω, J (Ksub M ω) v⟫ : ℂ) = ⟪v, ω⟫ := by
  have h1 : (⟪J (Ksub M ω) v, ω⟫ : ℂ) = ⟪ω, v⟫ := by
    rw [J_inner_swap (Ksub M ω) hsep hcyc, J_omega M ω hsep hcyc]
  have h2 := inner_conj_symm (𝕜 := ℂ) ω (J (Ksub M ω) v)
  rw [h1] at h2
  rw [← h2, ← inner_conj_symm (𝕜 := ℂ) v ω]

/-! ### The flip identity `⟪ω, y (J x J) ω⟫ = ⟪x (J y J) ω, ω⟫` -/

/-- **The flip identity, for self-adjoint `x, y ∈ M`.**  `⟪J xω, yω⟫` is real because
`J 𝒦 ⊆ (i𝒦)^⊥` (`inner_J_mem_K_real`), and `⟪J xω, yω⟫ = ⟪J yω, xω⟫` by RvD Prop. 3.1;
rewriting both sides with `J xω = (J x J) ω` gives the claim. -/
lemma adJ_flip_sa {x y : ℋ →L[ℂ] ℋ} (hx : x ∈ M) (hxs : IsSelfAdjoint x)
    (hy : y ∈ M) (hys : IsSelfAdjoint y) :
    (⟪ω, y (vnAdJ M ω hsep hcyc x ω)⟫ : ℂ) = ⟪x (vnAdJ M ω hsep hcyc y ω), ω⟫ := by
  set K := Ksub M ω with hK
  have hxK : x ω ∈ K := mem_Ksub_of_sa M ω hx hxs
  have hyK : y ω ∈ K := mem_Ksub_of_sa M ω hy hys
  have him : (⟪J K (x ω), y ω⟫ : ℂ).im = 0 := inner_J_mem_K_real K hsep hcyc hxK hyK
  have hreal : (⟪y ω, J K (x ω)⟫ : ℂ) = ⟪J K (x ω), y ω⟫ := by
    have e := inner_conj_symm (𝕜 := ℂ) (y ω) (J K (x ω))
    rw [← e]
    exact Complex.conj_eq_iff_im.2 him
  have hL : (⟪ω, y (vnAdJ M ω hsep hcyc x ω)⟫ : ℂ) = ⟪y ω, J K (x ω)⟫ := by
    rw [vnAdJ_omega M ω hsep hcyc]
    have := inner_star_left y ω (J K (x ω))
    rw [hys.star_eq] at this
    exact this.symm
  have hR : (⟪x (vnAdJ M ω hsep hcyc y ω), ω⟫ : ℂ) = ⟪J K (y ω), x ω⟫ := by
    rw [vnAdJ_omega M ω hsep hcyc]
    have := inner_apply_left x (J K (y ω)) ω
    rw [hxs.star_eq] at this
    exact this
  rw [hL, hR, hreal, J_inner_swap K hsep hcyc]

/-- The flip identity for self-adjoint `x ∈ M` and **arbitrary** `Y ∈ M`: both sides are
ℂ-linear in `Y`. -/
lemma adJ_flip_right {x : ℋ →L[ℂ] ℋ} (hx : x ∈ M) (hxs : IsSelfAdjoint x)
    {Y : ℋ →L[ℂ] ℋ} (hY : Y ∈ M) :
    (⟪ω, Y (vnAdJ M ω hsep hcyc x ω)⟫ : ℂ) = ⟪x (vnAdJ M ω hsep hcyc Y ω), ω⟫ := by
  obtain ⟨p, hp, q, hq, hps, hqs, rfl⟩ := exists_sa_decomp M Y hY
  have e1 := adJ_flip_sa M ω hsep hcyc hx hxs hp hps
  have e2 := adJ_flip_sa M ω hsep hcyc hx hxs hq hqs
  rw [vnAdJ_sa_decomp M ω hsep hcyc p q]
  simp only [add_apply, smul_apply, map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_I, map_neg]
  linear_combination e1 + I * e2

/-! ### RvD Lemma 4.9 -/

section FourNine

variable (hMdense : Dense {y : ℋ | ∃ x ∈ M, y = x ω})
  (hM'dense : Dense {y : ℋ | ∃ x ∈ commutantSA M, y = x ω})
  (hadJ : ∀ x' ∈ commutantSA M, vnAdJ M ω hsep hcyc x' ∈ M)

include hM'dense hadJ

/-- The heart of RvD Lemma 4.9: for self-adjoint `x, y ∈ M`, the operator `J y J` commutes
with `x` *on the vector `ω`*.  Substituting `y (J y' J)` for `y` in the flip identity, with
`y' ∈ M'` and `J y' J ∈ M` by hypothesis, both sides collapse to inner products against
`y' ω`; since `M' ω` is dense, the two vectors agree. -/
lemma adJ_orbit_comm_sa {x y : ℋ →L[ℂ] ℋ} (hx : x ∈ M) (hxs : IsSelfAdjoint x)
    (hy : y ∈ M) (hys : IsSelfAdjoint y) :
    (x * vnAdJ M ω hsep hcyc y) ω = (vnAdJ M ω hsep hcyc y * x) ω := by
  set K := Ksub M ω with hK
  set Jy := vnAdJ M ω hsep hcyc y with hJy
  refine eq_of_inner_eq_on_dense hM'dense ?_
  rintro _ ⟨y', hy', rfl⟩
  have hJy'M : vnAdJ M ω hsep hcyc y' ∈ M := hadJ y' hy'
  have hYM : y * vnAdJ M ω hsep hcyc y' ∈ M := mul_mem hy hJy'M
  have e := adJ_flip_right M ω hsep hcyc hx hxs hYM
  -- the left-hand side
  have hL : (⟪ω, (y * vnAdJ M ω hsep hcyc y') (vnAdJ M ω hsep hcyc x ω)⟫ : ℂ)
      = ⟪y' ω, (x * Jy) ω⟫ := by
    have h1 : (vnAdJ M ω hsep hcyc y') (vnAdJ M ω hsep hcyc x ω) = J K ((y' * x) ω) := by
      show (vnAdJ M ω hsep hcyc y' * vnAdJ M ω hsep hcyc x) ω = _
      rw [← vnAdJ_mul, vnAdJ_omega]
    have h2 : (y * vnAdJ M ω hsep hcyc y') (vnAdJ M ω hsep hcyc x ω)
        = J K (Jy ((y' * x) ω)) := by
      show y ((vnAdJ M ω hsep hcyc y') (vnAdJ M ω hsep hcyc x ω)) = _
      rw [h1, hJy]
      show _ = J K (J K (y (J K ((y' * x) ω))))
      rw [J_J K hsep hcyc]
    rw [h2, inner_omega_J M ω hsep hcyc]
    have h3 : (y' * x) ω = (x * y') ω := by
      rw [(mem_commutantSA.1 hy' x hx)]
    rw [h3]
    have h4 : Jy ((x * y') ω) = (Jy * x) (y' ω) := rfl
    rw [h4, inner_apply_left]
    congr 1
    rw [star_mul, hxs.star_eq, hJy, ← vnAdJ_star, hys.star_eq]
  -- the right-hand side
  have hR : (⟪x (vnAdJ M ω hsep hcyc (y * vnAdJ M ω hsep hcyc y') ω), ω⟫ : ℂ)
      = ⟪y' ω, (Jy * x) ω⟫ := by
    have h1 : vnAdJ M ω hsep hcyc (y * vnAdJ M ω hsep hcyc y') = Jy * y' := by
      rw [vnAdJ_mul, vnAdJ_vnAdJ, hJy]
    rw [h1]
    have h2 : x ((Jy * y') ω) = (x * Jy) (y' ω) := rfl
    rw [h2, inner_apply_left]
    congr 1
    rw [star_mul, hxs.star_eq, hJy, ← vnAdJ_star, hys.star_eq]
  rw [← hL, ← hR]
  exact e

/-- The same, for arbitrary `x ∈ M`: both sides are ℂ-linear in `x`. -/
lemma adJ_orbit_comm {x y : ℋ →L[ℂ] ℋ} (hx : x ∈ M) (hy : y ∈ M) (hys : IsSelfAdjoint y) :
    (x * vnAdJ M ω hsep hcyc y) ω = (vnAdJ M ω hsep hcyc y * x) ω := by
  obtain ⟨h, hh, k, hk, hhs, hks, rfl⟩ := exists_sa_decomp M x hx
  have e1 := adJ_orbit_comm_sa M ω hsep hcyc hM'dense hadJ hh hhs hy hys
  have e2 := adJ_orbit_comm_sa M ω hsep hcyc hM'dense hadJ hk hks hy hys
  show (h + I • k) (vnAdJ M ω hsep hcyc y ω) = vnAdJ M ω hsep hcyc y ((h + I • k) ω)
  have e1' : h (vnAdJ M ω hsep hcyc y ω) = vnAdJ M ω hsep hcyc y (h ω) := e1
  have e2' : k (vnAdJ M ω hsep hcyc y ω) = vnAdJ M ω hsep hcyc y (k ω) := e2
  simp only [add_apply, smul_apply, map_add, map_smul, e1', e2']

include hMdense

/-- **RvD Lemma 4.9** for self-adjoint `y`. -/
lemma adJ_mem_commutant_sa {y : ℋ →L[ℂ] ℋ} (hy : y ∈ M) (hys : IsSelfAdjoint y) :
    vnAdJ M ω hsep hcyc y ∈ commutantSA M := by
  rw [mem_commutantSA]
  intro m hm
  refine (clm_ext_of_dense hMdense ?_).symm
  rintro _ ⟨z, hz, rfl⟩
  have h1 := adJ_orbit_comm M ω hsep hcyc hM'dense hadJ hz hy hys
  have h2 := adJ_orbit_comm M ω hsep hcyc hM'dense hadJ (mul_mem hm hz) hy hys
  have h1' : z (vnAdJ M ω hsep hcyc y ω) = vnAdJ M ω hsep hcyc y (z ω) := h1
  have h2' : m (z (vnAdJ M ω hsep hcyc y ω)) = vnAdJ M ω hsep hcyc y (m (z ω)) := h2
  show vnAdJ M ω hsep hcyc y (m (z ω)) = m (vnAdJ M ω hsep hcyc y (z ω))
  rw [← h2', h1']

/-- **RvD Lemma 4.9**: `J M J ⊆ M'`, given `J M' J ⊆ M`. -/
theorem lemma_4_9 {y : ℋ →L[ℂ] ℋ} (hy : y ∈ M) :
    vnAdJ M ω hsep hcyc y ∈ commutantSA M := by
  obtain ⟨p, hp, q, hq, hps, hqs, rfl⟩ := exists_sa_decomp M y hy
  rw [vnAdJ_sa_decomp]
  exact add_mem (adJ_mem_commutant_sa M ω hsep hcyc hMdense hM'dense hadJ hp hps)
    (SMulMemClass.smul_mem _ (adJ_mem_commutant_sa M ω hsep hcyc hMdense hM'dense hadJ hq hqs))

/-- **RvD Theorem 4.2(1)**, the conjugation half of Tomita's theorem: `J M J = M'`.
The hypothesis `hadJ` is `J M' J ⊆ M`, which is RvD Lemma 4.8 at `t = 0`; everything else
is `lemma_4_9`. -/
theorem tomita_JMJ :
    (fun x => vnAdJ M ω hsep hcyc x) '' (M : Set (ℋ →L[ℂ] ℋ))
      = commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact lemma_4_9 M ω hsep hcyc hMdense hM'dense hadJ hy
  · intro x' hx'
    have hx'M : x' ∈ commutantSA M := hx'
    exact ⟨vnAdJ M ω hsep hcyc x', hadJ x' hx'M, vnAdJ_vnAdJ M ω hsep hcyc x'⟩

/-- `J M' J = M`, the other half of the same statement. -/
theorem tomita_JM'J :
    (fun x => vnAdJ M ω hsep hcyc x) '' (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x', hx', rfl⟩
    exact hadJ x' hx'
  · intro y hy
    refine ⟨vnAdJ M ω hsep hcyc y, ?_, vnAdJ_vnAdJ M ω hsep hcyc y⟩
    exact lemma_4_9 M ω hsep hcyc hMdense hM'dense hadJ hy

end FourNine

end Tomita2

/-! ## Part III: towards RvD Lemma 4.3

The remaining input to Theorem 4.2(1) is `J M' J ⊆ M`, RvD Lemma 4.8 at `t = 0`.  Its
first step is Lemma 4.3, a Hahn–Banach separation modelled on Sakai's linear
Radon–Nikodym theorem.  This part builds the two ingredients of that separation which are
not already in the tree: the ultraweak continuity of the vector functionals of `B(ℋ)`, and
the fact that the image of an ultraweakly compact set of operators under a map that is
weakly continuous into `ℋ` is *norm*-closed. -/

section Predual

open Filter Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `x ↦ ⟪η, x ζ⟫` is ultraweakly continuous: by polarisation it is a linear combination of
the vector np-functionals `x ↦ ⟪z, x z⟫`. -/
theorem continuous_uw_inner_apply {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] (ζ η : ℋ) :
    @Continuous (ℋ →L[ℂ] ℋ) ℂ (ultraweak (ℋ →L[ℂ] ℋ)) _ (fun x => (⟪η, x ζ⟫ : ℂ)) := by
  let _inst : TopologicalSpace (ℋ →L[ℂ] ℋ) := ultraweak (ℋ →L[ℂ] ℋ)
  have key : ∀ x : ℋ →L[ℂ] ℋ, (⟪η, x ζ⟫ : ℂ)
      = (vectorNP (ζ + η) x + I * vectorNP (ζ + (I : ℂ) • η) x
          - vectorNP (ζ - η) x - I * vectorNP (ζ - (I : ℂ) • η) x) / 4 := by
    intro x
    simp only [vectorNP_apply, map_add, map_sub, map_smul, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [key]
  have hc : ∀ z : ℋ, Continuous fun x : ℋ →L[ℂ] ℋ => (vectorNP z x : ℂ) :=
    fun z => continuous_ultraweak_npFunctional (vectorNP z)
  exact (((((hc _).add (continuous_const.mul (hc _))).sub (hc _)).sub
    (continuous_const.mul (hc _)))).div_const 4

/-- **Compactness transfer.**  If `S` is ultraweakly compact and `g : A → ℋ` is such that
every `x ↦ ⟪η, g x⟫` is ultraweakly continuous, then `g '' S` is *norm*-closed in `ℋ`.
A cluster point `x₀ ∈ S` of the pulled-back filter has `⟪η, g x₀⟫ = ⟪η, v⟫` for every `η`,
because a cluster point of a convergent filter in a Hausdorff space is its limit. -/
theorem isClosed_image_of_uwCompact {ℋ : Type*} [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] {S : Set A} (hS : @IsCompact A (ultraweak A) S)
    (g : A → ℋ) (hg : ∀ η : ℋ, @Continuous A ℂ (ultraweak A) _ (fun x => (⟪η, g x⟫ : ℂ))) :
    IsClosed (g '' S) := by
  let _inst : TopologicalSpace A := ultraweak A
  rw [isClosed_iff_clusterPt]
  intro v hv
  set G : Filter ℋ := 𝓝 v ⊓ 𝓟 (g '' S) with hG
  have hGne : G.NeBot := hv
  have hmem : g '' S ∈ G := Filter.mem_inf_of_right (Filter.mem_principal_self _)
  have hne : (Filter.comap g G ⊓ 𝓟 S).NeBot :=
    Filter.comap_inf_principal_neBot_of_image_mem hGne hmem
  obtain ⟨x₀, hx₀S, hclus⟩ := hS (f := Filter.comap g G ⊓ 𝓟 S) inf_le_right
  refine ⟨x₀, hx₀S, ?_⟩
  refine ext_inner_left ℂ fun η => ?_
  have htend : Filter.Tendsto (fun x => (⟪η, g x⟫ : ℂ)) (Filter.comap g G ⊓ 𝓟 S)
      (𝓝 (⟪η, v⟫ : ℂ)) := by
    have h1 : Filter.Tendsto g (Filter.comap g G ⊓ 𝓟 S) (𝓝 v) :=
      (Filter.tendsto_comap.mono_left inf_le_left).mono_right inf_le_left
    exact (Continuous.tendsto (by fun_prop : Continuous fun w : ℋ => (⟪η, w⟫ : ℂ)) v).comp h1
  have hcl := hclus.map (hg η).continuousAt htend
  exact t2_iff_nhds.mp inferInstance hcl

/-- The real-inner-product form of `isClosed_image_of_uwCompact`, which is what the
separation argument of RvD Lemma 4.3 needs: there the map `g` involves the *real*-linear
projection `P` and is only ℝ-linear. -/
theorem isClosed_image_of_uwCompact_real {ℋ : Type*} [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] {S : Set A} (hS : @IsCompact A (ultraweak A) S)
    (g : A → ℋ)
    (hg : ∀ η : ℋ, @Continuous A ℝ (ultraweak A) _ (fun x => (inner ℝ η (g x) : ℝ))) :
    IsClosed (g '' S) := by
  let _inst : TopologicalSpace A := ultraweak A
  rw [isClosed_iff_clusterPt]
  intro v hv
  set G : Filter ℋ := 𝓝 v ⊓ 𝓟 (g '' S) with hG
  have hGne : G.NeBot := hv
  have hmem : g '' S ∈ G := Filter.mem_inf_of_right (Filter.mem_principal_self _)
  have hne : (Filter.comap g G ⊓ 𝓟 S).NeBot :=
    Filter.comap_inf_principal_neBot_of_image_mem hGne hmem
  obtain ⟨x₀, hx₀S, hclus⟩ := hS (f := Filter.comap g G ⊓ 𝓟 S) inf_le_right
  refine ⟨x₀, hx₀S, ?_⟩
  refine ext_inner_left ℝ fun η => ?_
  have htend : Filter.Tendsto (fun x => (inner ℝ η (g x) : ℝ)) (Filter.comap g G ⊓ 𝓟 S)
      (𝓝 (inner ℝ η v : ℝ)) := by
    have h1 : Filter.Tendsto g (Filter.comap g G ⊓ 𝓟 S) (𝓝 v) :=
      (Filter.tendsto_comap.mono_left inf_le_left).mono_right inf_le_left
    exact (Continuous.tendsto (by fun_prop : Continuous fun w : ℋ => (inner ℝ η w : ℝ)) v).comp h1
  have hcl := hclus.map (hg η).continuousAt htend
  exact t2_iff_nhds.mp inferInstance hcl

/-- The ultraweak closure of a ∗-subalgebra of `B(ℋ)` is its bicommutant (**88VI**), so a
∗-subalgebra equal to its own bicommutant is ultraweakly closed. -/
theorem isClosed_uw_of_bicommutant {ℋ : Type*} [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ))
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ))) :
    @IsClosed (ℋ →L[ℂ] ℋ) (ultraweak (ℋ →L[ℂ] ℋ)) (M : Set (ℋ →L[ℂ] ℋ)) := by
  let _inst : TopologicalSpace (ℋ →L[ℂ] ℋ) := ultraweak (ℋ →L[ℂ] ℋ)
  have h := (double_commutant M).2.1
  rw [hM] at h
  exact closure_eq_iff_isClosed.mp h.symm

end Predual

/-! ### The compact convex set of RvD Lemma 4.3 -/

section SepSet

open Filter Topology

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (ω : ℋ) (lam : ℂ)

/-- The convex set separated in RvD Lemma 4.3: the image under the real-orthogonal
projection `P` onto `𝒦 = closure (M_sa ω)` of `{λ x ω : x ∈ M_sa, ‖x‖ ≤ 1}`.  It is written
as the image of the *whole* unit ball of `M` under `x ↦ P (λ ((x + x*)/2) ω)` so that
ultraweak compactness of the ball applies directly. -/
noncomputable def sepSet : Set ℋ :=
  (fun x : ℋ →L[ℂ] ℋ => P (Ksub M ω) (lam • ((2⁻¹ : ℂ) • (x ω + (star x) ω)))) ''
    (Metric.closedBall (0 : ℋ →L[ℂ] ℋ) 1 ∩ (M : Set (ℋ →L[ℂ] ℋ)))

lemma sepSet_subset_Ksub : sepSet M ω lam ⊆ (Ksub M ω : Set ℋ) := by
  rintro _ ⟨x, -, rfl⟩
  exact P_apply_mem _ _

lemma sepSet_nonempty : (sepSet M ω lam).Nonempty :=
  ⟨_, ⟨0, ⟨by simp, zero_mem M⟩, rfl⟩⟩

/-- Every element of `sepSet` is `P (λ y ω)` for a self-adjoint `y ∈ M` of norm `≤ 1`. -/
lemma exists_sa_of_mem_sepSet {c : ℋ} (hc : c ∈ sepSet M ω lam) :
    ∃ y ∈ M, IsSelfAdjoint y ∧ ‖y‖ ≤ 1 ∧ c = P (Ksub M ω) (lam • (y ω)) := by
  obtain ⟨x, ⟨hxb, hxM⟩, rfl⟩ := hc
  have hxn : ‖x‖ ≤ 1 := by simpa using hxb
  refine ⟨(2⁻¹ : ℂ) • (x + star x), SMulMemClass.smul_mem _ (add_mem hxM (M.star_mem' hxM)), ?_,
    ?_, ?_⟩
  · rw [IsSelfAdjoint, star_smul, star_add, star_star, add_comm,
      show star (2⁻¹ : ℂ) = 2⁻¹ by rw [Complex.star_def, map_inv₀, map_ofNat]]
  · calc ‖(2⁻¹ : ℂ) • (x + star x)‖ = 2⁻¹ * ‖x + star x‖ := by rw [norm_smul]; norm_num
      _ ≤ 2⁻¹ * (‖x‖ + ‖star x‖) := by
          have := norm_add_le x (star x); nlinarith [norm_nonneg (x + star x)]
      _ ≤ 1 := by rw [norm_star]; linarith
  · rfl

/-- Conversely, `P (λ y ω)` lies in `sepSet` for self-adjoint `y ∈ M` of norm `≤ 1`. -/
lemma mem_sepSet_of_sa {y : ℋ →L[ℂ] ℋ} (hy : y ∈ M) (hys : IsSelfAdjoint y) (hn : ‖y‖ ≤ 1) :
    P (Ksub M ω) (lam • (y ω)) ∈ sepSet M ω lam := by
  refine ⟨y, ⟨by simpa using hn, hy⟩, ?_⟩
  show P (Ksub M ω) (lam • ((2⁻¹ : ℂ) • (y ω + (star y) ω))) = P (Ksub M ω) (lam • (y ω))
  rw [hys.star_eq]
  congr 2
  show (2⁻¹ : ℂ) • (y ω + y ω) = y ω
  module

lemma sepSet_convex : Convex ℝ (sepSet M ω lam) := by
  rintro _ ⟨x, ⟨hxb, hxM⟩, rfl⟩ _ ⟨z, ⟨hzb, hzM⟩, rfl⟩ s t hs ht hst
  refine ⟨(s : ℂ) • x + (t : ℂ) • z, ⟨?_, add_mem (SMulMemClass.smul_mem _ hxM)
    (SMulMemClass.smul_mem _ hzM)⟩, ?_⟩
  · have hxn : ‖x‖ ≤ 1 := by simpa using hxb
    have hzn : ‖z‖ ≤ 1 := by simpa using hzb
    have h1 : ‖(s : ℂ) • x + (t : ℂ) • z‖ ≤ s * ‖x‖ + t * ‖z‖ := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_smul, norm_smul]
      simp [abs_of_nonneg hs, abs_of_nonneg ht]
    have : s * ‖x‖ + t * ‖z‖ ≤ 1 := by nlinarith
    simpa using le_trans h1 this
  · have hop : ∀ w : ℋ →L[ℂ] ℋ, ∀ r : ℝ, ((r : ℂ) • w) ω + (star ((r : ℂ) • w)) ω
        = r • (w ω + (star w) ω) := by
      intro w r
      rw [star_smul, Complex.star_def, Complex.conj_ofReal]
      show (r : ℂ) • w ω + (r : ℂ) • (star w) ω = r • (w ω + (star w) ω)
      rw [← smul_add, ← Complex.coe_algebraMap, algebraMap_smul]
    have hsum : ((s : ℂ) • x + (t : ℂ) • z) ω + (star ((s : ℂ) • x + (t : ℂ) • z)) ω
        = s • (x ω + (star x) ω) + t • (z ω + (star z) ω) := by
      rw [star_add, add_apply, add_apply]
      rw [show ((s : ℂ) • x) ω + ((t : ℂ) • z) ω
          + ((star ((s : ℂ) • x)) ω + (star ((t : ℂ) • z)) ω)
        = (((s : ℂ) • x) ω + (star ((s : ℂ) • x)) ω)
          + (((t : ℂ) • z) ω + (star ((t : ℂ) • z)) ω) by abel]
      rw [hop x s, hop z t]
    show P (Ksub M ω) (lam • ((2⁻¹ : ℂ) • (((s : ℂ) • x + (t : ℂ) • z) ω
        + (star ((s : ℂ) • x + (t : ℂ) • z)) ω)))
      = s • P (Ksub M ω) (lam • ((2⁻¹ : ℂ) • (x ω + (star x) ω)))
        + t • P (Ksub M ω) (lam • ((2⁻¹ : ℂ) • (z ω + (star z) ω)))
    rw [hsum]
    have hexp : lam • ((2⁻¹ : ℂ) • (s • (x ω + (star x) ω) + t • (z ω + (star z) ω)))
        = s • (lam • ((2⁻¹ : ℂ) • (x ω + (star x) ω)))
          + t • (lam • ((2⁻¹ : ℂ) • (z ω + (star z) ω))) := by
      rw [smul_add, smul_add, smul_comm (2⁻¹ : ℂ) s, smul_comm (2⁻¹ : ℂ) t,
        smul_comm lam s, smul_comm lam t]
    rw [hexp, map_add,
      ContinuousLinearMap.map_smul (P (Ksub M ω)) s (lam • ((2⁻¹ : ℂ) • (x ω + (star x) ω))),
      ContinuousLinearMap.map_smul (P (Ksub M ω)) t (lam • ((2⁻¹ : ℂ) • (z ω + (star z) ω)))]

/-- **`sepSet` is closed**: it is the image of the ultraweakly compact set
`ball ∩ M` under a map that is weakly continuous into `ℋ`. -/
lemma sepSet_isClosed
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ))) :
    IsClosed (sepSet M ω lam) := by
  let _inst : TopologicalSpace (ℋ →L[ℂ] ℋ) := ultraweak (ℋ →L[ℂ] ℋ)
  refine isClosed_image_of_uwCompact_real
    (vn_ball_compact.inter_right (isClosed_uw_of_bicommutant M hM)) _ ?_
  intro η
  have hEq : ∀ x : ℋ →L[ℂ] ℋ,
      (inner ℝ η (P (Ksub M ω) (lam • ((2⁻¹ : ℂ) • (x ω + (star x) ω)))) : ℝ)
        = (lam * 2⁻¹ * ((⟪P (Ksub M ω) η, x ω⟫ : ℂ)
            + (starRingEnd ℂ) (⟪ω, x (P (Ksub M ω) η)⟫ : ℂ))).re := by
    intro x
    rw [← P_symm, inner_real_eq_re_inner]
    congr 1
    rw [inner_smul_right, inner_smul_right, inner_add_right]
    have hstarx : (⟪P (Ksub M ω) η, (star x) ω⟫ : ℂ)
        = (starRingEnd ℂ) (⟪ω, x (P (Ksub M ω) η)⟫ : ℂ) := by
      rw [← inner_apply_left x (P (Ksub M ω) η) ω]
      exact (inner_conj_symm _ _).symm
    rw [hstarx]
    ring
  have h1 : @Continuous (ℋ →L[ℂ] ℋ) ℂ (ultraweak (ℋ →L[ℂ] ℋ)) _
      (fun x => (⟪P (Ksub M ω) η, x ω⟫ : ℂ)) :=
    continuous_uw_inner_apply ω (P (Ksub M ω) η)
  have h2 : @Continuous (ℋ →L[ℂ] ℋ) ℂ (ultraweak (ℋ →L[ℂ] ℋ)) _
      (fun x => (⟪ω, x (P (Ksub M ω) η)⟫ : ℂ)) :=
    continuous_uw_inner_apply (P (Ksub M ω) η) ω
  exact ((Complex.continuous_re.comp
    (continuous_const.mul (h1.add (Complex.continuous_conj.comp h2)))).congr
    fun x => (hEq x).symm)

/-- **The separation step of RvD Lemma 4.3.**  If `P (x' ω)` is *not* of the form
`P (λ y ω)` with `y ∈ M` self-adjoint of norm `≤ 1`, then — `sepSet` being nonempty, convex
and closed — the nearest-point projection in the real Hilbert space `ℋ` separates it
strictly, and the separating vector may be taken in `M_sa ω` because it may be taken in
`𝒦 = closure (M_sa ω)`.

This is the point where the present development departs from Rieffel–van Daele: they
separate in the predual of `M`, using that the ball of `M` is weak-∗ compact there.  Here
the separation is carried out in `ℋ` itself, and the compactness is used only to know that
`sepSet` is closed (`sepSet_isClosed`).  No predual is needed. -/
theorem exists_separating_of_notMem
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    {x' : ℋ →L[ℂ] ℋ} (hnot : P (Ksub M ω) (x' ω) ∉ sepSet M ω lam) :
    ∃ h ∈ M, IsSelfAdjoint h ∧ ∃ δ > 0, ∀ y ∈ M, IsSelfAdjoint y → ‖y‖ ≤ 1 →
      inner ℝ (h ω) (lam • (y ω)) ≤ inner ℝ (h ω) (x' ω) - δ := by
  set K := Ksub M ω with hK
  set p : ℋ := P K (x' ω) with hp
  -- the nearest point of `sepSet` to `p`
  obtain ⟨c₀, hc₀, hmin⟩ := exists_norm_eq_iInf_of_complete_convex (sepSet_nonempty M ω lam)
    (sepSet_isClosed M ω lam hM).isComplete (sepSet_convex M ω lam) p
  have hvar : ∀ c ∈ sepSet M ω lam, inner ℝ (p - c₀) (c - c₀) ≤ (0 : ℝ) :=
    (norm_eq_iInf_iff_real_inner_le_zero (sepSet_convex M ω lam) hc₀).1 hmin
  set w : ℋ := p - c₀ with hw
  have hwne : w ≠ 0 := by
    intro hz
    refine hnot ?_
    show p ∈ sepSet M ω lam
    rw [sub_eq_zero.1 hz]
    exact hc₀
  set δ : ℝ := ‖w‖ ^ 2 with hδ
  have hδpos : 0 < δ := by positivity
  -- strict separation, with the gap `δ`
  have hsep : ∀ c ∈ sepSet M ω lam, inner ℝ w c ≤ inner ℝ w p - δ := by
    intro c hc
    have h1 := hvar c hc
    rw [inner_sub_right] at h1
    have h2 : (inner ℝ w c₀ : ℝ) = inner ℝ w p - δ := by
      have : c₀ = p - w := by rw [hw]; abel
      rw [this, inner_sub_right, hδ, real_inner_self_eq_norm_sq]
    linarith [h1, h2.symm.le, h2.le]
  -- move the separating vector into `𝒦`
  set w₀ : ℋ := P K w with hw₀
  have hsep' : ∀ y ∈ M, IsSelfAdjoint y → ‖y‖ ≤ 1 →
      inner ℝ w₀ (lam • (y ω)) ≤ inner ℝ w₀ (x' ω) - δ := by
    intro y hy hys hyn
    have hc := hsep _ (mem_sepSet_of_sa M ω lam hy hys hyn)
    have e1 : (inner ℝ w (P K (lam • (y ω))) : ℝ) = inner ℝ w₀ (lam • (y ω)) := by
      rw [hw₀, P_symm]
    have e2 : (inner ℝ w p : ℝ) = inner ℝ w₀ (x' ω) := by rw [hw₀, P_symm, hp]
    rw [e1, e2] at hc
    exact hc
  -- approximate `w₀ ∈ 𝒦 = closure (M_sa ω)` by an element of `M_sa ω`
  set C : ℝ := ‖lam‖ * ‖ω‖ + ‖x' ω‖ + 1 with hC
  have hCpos : 0 < C := by
    have : (0 : ℝ) ≤ ‖lam‖ * ‖ω‖ := by positivity
    have h2 : (0 : ℝ) ≤ ‖x' ω‖ := norm_nonneg _
    rw [hC]; linarith
  set ε : ℝ := δ / 2 / C with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hw₀K : w₀ ∈ K := P_apply_mem K w
  have hmemcl : w₀ ∈ closure ((saOrbit M ω : Submodule ℝ ℋ) : Set ℋ) := by
    have hco : (K : Set ℋ) = closure ((saOrbit M ω : Submodule ℝ ℋ) : Set ℋ) :=
      Submodule.topologicalClosure_coe _
    rw [← hco]; exact hw₀K
  obtain ⟨v, hv, hvd⟩ := Metric.mem_closure_iff.1 hmemcl ε hεpos
  obtain ⟨h, hhM, hhs, rfl⟩ := hv
  rw [dist_eq_norm] at hvd
  refine ⟨h, hhM, hhs, δ / 2, by linarith, ?_⟩
  intro y hy hys hyn
  have hd1 : |(inner ℝ (w₀ - h ω) (lam • (y ω)) : ℝ)| ≤ ε * (‖lam‖ * ‖ω‖) := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    have hy1 : ‖lam • (y ω)‖ ≤ ‖lam‖ * ‖ω‖ := by
      rw [norm_smul]
      have : ‖y ω‖ ≤ ‖ω‖ := le_trans (y.le_opNorm ω) (by nlinarith [norm_nonneg ω])
      exact mul_le_mul_of_nonneg_left this (norm_nonneg lam)
    have hnw : ‖w₀ - h ω‖ ≤ ε := le_of_lt hvd
    exact mul_le_mul hnw hy1 (norm_nonneg _) (le_of_lt hεpos)
  have hd2 : |(inner ℝ (w₀ - h ω) (x' ω) : ℝ)| ≤ ε * ‖x' ω‖ := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    exact mul_le_mul_of_nonneg_right (le_of_lt hvd) (norm_nonneg _)
  have hexp1 : (inner ℝ (h ω) (lam • (y ω)) : ℝ)
      = inner ℝ w₀ (lam • (y ω)) - inner ℝ (w₀ - h ω) (lam • (y ω)) := by
    rw [inner_sub_left]; ring
  have hexp2 : (inner ℝ (h ω) (x' ω) : ℝ)
      = inner ℝ w₀ (x' ω) - inner ℝ (w₀ - h ω) (x' ω) := by
    rw [inner_sub_left]; ring
  have hkey := hsep' y hy hys hyn
  have habs1 := abs_le.1 hd1
  have habs2 := abs_le.1 hd2
  have hεC : ε * C ≤ δ / 2 := by
    rw [hε, div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hCpos), mul_one]
  have hsum : ε * (‖lam‖ * ‖ω‖) + ε * ‖x' ω‖ ≤ δ / 2 := by
    have : ε * (‖lam‖ * ‖ω‖) + ε * ‖x' ω‖ ≤ ε * C := by rw [hC]; nlinarith [hεpos.le]
    linarith
  rw [hexp1, hexp2]
  linarith [habs1.1, habs1.2, habs2.1, habs2.2]

end SepSet

/-! ### The contradiction: the regularised sign of `h` -/

section SignApprox

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-- `|h|`, by the real continuous functional calculus. -/
noncomputable def absOp (h : ℋ →L[ℂ] ℋ) : ℋ →L[ℂ] ℋ := cfc (fun t : ℝ => |t|) h

/-- The regularised sign `t ↦ t / (|t| + ε)` of `h`.  Rieffel–van Daele use the polar
decomposition `h = u |h|` of `h` inside `M`, which needs a Borel functional calculus; this
continuous substitute is enough, because only `h u → |h|` in norm is used. -/
noncomputable def signApprox (h : ℋ →L[ℂ] ℋ) (ε : ℝ) : ℋ →L[ℂ] ℋ :=
  cfc (fun t : ℝ => t / (|t| + ε)) h

lemma absOp_nonneg (h : ℋ →L[ℂ] ℋ) : 0 ≤ absOp h :=
  cfc_nonneg (fun x _ => abs_nonneg x)

lemma absOp_isSelfAdjoint (h : ℋ →L[ℂ] ℋ) : IsSelfAdjoint (absOp h) :=
  .of_nonneg (absOp_nonneg h)

lemma le_absOp {h : ℋ →L[ℂ] ℋ} (hhs : IsSelfAdjoint h) : h ≤ absOp h := by
  have hid : cfc (fun t : ℝ => t) h = h := cfc_id' ℝ h
  have hle : cfc (fun t : ℝ => t) h ≤ cfc (fun t : ℝ => |t|) h :=
    cfc_mono (a := h) (fun x _ => le_abs_self x)
  rw [hid] at hle
  exact hle

private lemma cont_signApprox {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun t : ℝ => t / (|t| + ε)) :=
  continuous_id.div (by fun_prop) (fun t => by positivity)

private lemma cont_mul_signApprox {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun t : ℝ => t * (t / (|t| + ε))) :=
  continuous_id.mul (cont_signApprox hε)

lemma signApprox_isSelfAdjoint (h : ℋ →L[ℂ] ℋ) (ε : ℝ) : IsSelfAdjoint (signApprox h ε) :=
  cfc_predicate _ h

lemma norm_signApprox_le {h : ℋ →L[ℂ] ℋ} {ε : ℝ} (hε : 0 < ε) : ‖signApprox h ε‖ ≤ 1 := by
  refine norm_cfc_le (𝕜 := ℝ) zero_le_one fun x _ => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |x| + ε)]
  rw [div_le_one (by positivity)]
  linarith [abs_nonneg x]

/-- `h · sign_ε(h) → |h|` in norm, at rate `ε`. -/
lemma norm_mul_signApprox_sub_absOp_le {h : ℋ →L[ℂ] ℋ} (hhs : IsSelfAdjoint h) {ε : ℝ}
    (hε : 0 < ε) : ‖h * signApprox h ε - absOp h‖ ≤ ε := by
  have hid : cfc (fun t : ℝ => t) h = h := cfc_id' ℝ h
  have hmul : h * signApprox h ε = cfc (fun t : ℝ => t * (t / (|t| + ε))) h := by
    have hm := cfc_mul (R := ℝ) (A := ℋ →L[ℂ] ℋ) (fun t : ℝ => t)
      (fun t : ℝ => t / (|t| + ε)) h continuousOn_id (cont_signApprox hε).continuousOn
    rw [hm, hid]
    rfl
  rw [hmul, absOp,
    ← cfc_sub (R := ℝ) (fun t : ℝ => t * (t / (|t| + ε))) (fun t : ℝ => |t|) h
      (cont_mul_signApprox hε).continuousOn (by fun_prop)]
  refine norm_cfc_le (𝕜 := ℝ) hε.le fun x _ => ?_
  have hpos : (0 : ℝ) < |x| + ε := by positivity
  have hsq : x * (x / (|x| + ε)) - |x| = -(ε * |x|) / (|x| + ε) := by
    field_simp
    nlinarith [abs_mul_abs_self x, sq_abs x]
  rw [Real.norm_eq_abs, hsq, abs_div, abs_of_nonneg hpos.le, div_le_iff₀ hpos, abs_neg,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ε * |x|)]
  nlinarith [abs_nonneg x, hε.le]

/-- Real symmetry of a self-adjoint bounded operator. -/
lemma real_inner_sa {T : ℋ →L[ℂ] ℋ} (hT : IsSelfAdjoint T) (u v : ℋ) :
    inner ℝ (T u) v = inner ℝ u (T v) := by
  have h := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT u v
  simp only [ContinuousLinearMap.coe_coe] at h
  exact congrArg Complex.re h

/-- The real quadratic form is monotone in the operator. -/
lemma real_inner_le_of_le {T S : ℋ →L[ℂ] ℋ} (hTS : T ≤ S) (ξ : ℋ) :
    inner ℝ (T ξ) ξ ≤ inner ℝ (S ξ) ξ := by
  have hpos := (ContinuousLinearMap.le_def T S).1 hTS
  have h0 : (0 : ℝ) ≤ (S - T).reApplyInnerSelf ξ := hpos.2 ξ
  have he : (S - T).reApplyInnerSelf ξ = inner ℝ (S ξ) ξ - inner ℝ (T ξ) ξ := by
    show (inner ℝ ((S - T) ξ) ξ : ℝ) = _
    rw [sub_apply, inner_sub_left]
  linarith [he ▸ h0]

/-- **RvD's estimate**: for `0 ≤ x' ≤ 1` commuting with the self-adjoint `h`,
`⟪h ω, x' ω⟫_ℝ ≤ ⟪ω, |h| ω⟫_ℝ`.  Insert `x' = (x'^{1/2})²`, use `h ≤ |h|`, move
`x'^{1/2}` back out, and finally use `x' ≤ 1` against `|h|^{1/2} ω`. -/
theorem inner_le_inner_absOp (ω : ℋ) {h x' : ℋ →L[ℂ] ℋ} (hhs : IsSelfAdjoint h)
    (hx'0 : 0 ≤ x') (hx'1 : x' ≤ 1) (hcomm : Commute h x') :
    (inner ℝ (h ω) (x' ω) : ℝ) ≤ inner ℝ ω (absOp h ω) := by
  set s : ℋ →L[ℂ] ℋ := CFC.sqrt x' with hsdef
  set k : ℋ →L[ℂ] ℋ := CFC.sqrt (absOp h) with hkdef
  have hssa : IsSelfAdjoint s := .of_nonneg (CFC.sqrt_nonneg _)
  have hksa : IsSelfAdjoint k := .of_nonneg (CFC.sqrt_nonneg _)
  have hss : s * s = x' := CFC.sqrt_mul_sqrt_self x' hx'0
  have hkk : k * k = absOp h := CFC.sqrt_mul_sqrt_self _ (absOp_nonneg h)
  have hcsh : Commute s h := by rw [hsdef, CFC.sqrt_eq_cfc]; exact hcomm.symm.cfc_nnreal _
  have habsS : Commute (absOp h) s := by
    rw [absOp]; exact (hcsh.symm).cfc_real _
  have hcks : Commute k s := by rw [hkdef, CFC.sqrt_eq_cfc]; exact habsS.cfc_nnreal _
  -- step 1
  have step1 : (inner ℝ (h ω) (x' ω) : ℝ) = inner ℝ (h (s ω)) (s ω) := by
    have hx : x' ω = s (s ω) := by rw [← hss]; rfl
    rw [hx, ← real_inner_sa hssa (h ω) (s ω)]
    congr 1
    exact commute_apply hcsh ω
  -- step 3
  have step3 : (inner ℝ (absOp h (s ω)) (s ω) : ℝ) = inner ℝ (x' (k ω)) (k ω) := by
    have h1 : absOp h (s ω) = k (k (s ω)) := by rw [← hkk]; rfl
    rw [h1, real_inner_sa hksa (k (s ω)) (s ω)]
    have h2 : k (s ω) = s (k ω) := commute_apply hcks ω
    rw [h2, ← real_inner_sa hssa (s (k ω)) (k ω)]
    congr 1
    show s (s (k ω)) = x' (k ω)
    rw [← hss]; rfl
  have step5 : (inner ℝ ((1 : ℋ →L[ℂ] ℋ) (k ω)) (k ω) : ℝ) = inner ℝ ω (absOp h ω) := by
    show (inner ℝ (k ω) (k ω) : ℝ) = _
    rw [← real_inner_sa hksa (k ω) ω, real_inner_comm ω (k (k ω))]
    congr 1
    show k (k ω) = absOp h ω
    rw [← hkk]; rfl
  calc (inner ℝ (h ω) (x' ω) : ℝ) = inner ℝ (h (s ω)) (s ω) := step1
    _ ≤ inner ℝ (absOp h (s ω)) (s ω) := real_inner_le_of_le (le_absOp hhs) _
    _ = inner ℝ (x' (k ω)) (k ω) := step3
    _ ≤ inner ℝ ((1 : ℋ →L[ℂ] ℋ) (k ω)) (k ω) := real_inner_le_of_le hx'1 _
    _ = inner ℝ ω (absOp h ω) := step5

end SignApprox

/-! ### RvD Lemma 4.3 -/

section Lemma43

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (ω : ℋ)

/-- **RvD Lemma 4.3**, for `0 ≤ x' ≤ 1` in `M'` and `Re λ = 1`: there is a self-adjoint
`y ∈ M` of norm `≤ 1` with `⟪z ω, x' ω⟫_ℝ = ⟪z ω, λ y ω⟫_ℝ` for all `z ∈ M_sa` — stated as
the equality of the two projections onto `𝒦 = closure (M_sa ω)`.

The proof is Rieffel–van Daele's, with two substitutions.  The Hahn–Banach separation is
carried out in `ℋ` rather than in the predual of `M` (`exists_separating_of_notMem`), and
the polar decomposition `h = u |h|` inside `M`, which needs a Borel functional calculus, is
replaced by the continuous regularisation `u_ε = h (|h| + ε)⁻¹`, for which `h u_ε → |h|` in
norm (`norm_mul_signApprox_sub_absOp_le`). -/
theorem lemma_4_3_unit
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    {x' : ℋ →L[ℂ] ℋ} (hx'M : x' ∈ commutantSA M) (hx'0 : 0 ≤ x') (hx'1 : x' ≤ 1)
    {lam : ℂ} (hlam : lam.re = 1) :
    ∃ y ∈ M, IsSelfAdjoint y ∧ ‖y‖ ≤ 1 ∧
      P (Ksub M ω) (x' ω) = P (Ksub M ω) (lam • (y ω)) := by
  by_contra hcon
  push Not at hcon
  have hnot : P (Ksub M ω) (x' ω) ∉ sepSet M ω lam := by
    intro hmem
    obtain ⟨y, hyM, hys, hyn, hyeq⟩ := exists_sa_of_mem_sepSet M ω lam hmem
    exact hcon y hyM hys hyn hyeq
  obtain ⟨h, hhM, hhs, δ, hδ, hsep⟩ := exists_separating_of_notMem M ω lam hM hnot
  have hMcl : IsClosed ((M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) : Set (ℋ →L[ℂ] ℋ)) := by
    rw [← hM]; exact Set.isClosed_centralizer _
  have _instcl := hMcl
  set ε : ℝ := δ / (2 * (‖ω‖ ^ 2 + 1)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  set y : ℋ →L[ℂ] ℋ := signApprox h ε with hy
  have hyM : y ∈ M := by rw [hy, signApprox]; exact cfc_mem _ hhM
  have hys : IsSelfAdjoint y := signApprox_isSelfAdjoint h ε
  have hyn : ‖y‖ ≤ 1 := norm_signApprox_le hεpos
  have hkey := hsep y hyM hys hyn
  have hcy : Commute h y := by
    rw [hy, signApprox]
    exact ((Commute.refl h).cfc_real _).symm
  have hhy : IsSelfAdjoint (h * y) := by
    show star (h * y) = h * y
    rw [star_mul, hys.star_eq, hhs.star_eq]
    exact hcy.symm.eq
  -- the left-hand side of the separation inequality is `⟪ω, h y ω⟫`
  have hLHS : (inner ℝ (h ω) (lam • (y ω)) : ℝ) = inner ℝ ω ((h * y) ω) := by
    have e1 : (⟪h ω, y ω⟫ : ℂ) = ⟪ω, (h * y) ω⟫ := by
      have e := inner_apply_left h ω (y ω)
      rw [hhs.star_eq] at e
      exact e
    have e2 : (⟪ω, (h * y) ω⟫ : ℂ).im = 0 := by
      have h1 := inner_apply_left (h * y) ω ω
      rw [hhy.star_eq] at h1
      have h2 := inner_conj_symm (𝕜 := ℂ) ((h * y) ω) ω
      rw [h1] at h2
      have h3 := congrArg Complex.im h2
      simp only [Complex.conj_im] at h3
      linarith
    rw [inner_real_eq_re_inner, inner_real_eq_re_inner, inner_smul_right, e1, Complex.mul_re,
      e2, hlam]
    ring
  -- `h y` is within `ε ‖ω‖²` of `|h|`
  have habs : |(inner ℝ ω ((h * y) ω) : ℝ) - inner ℝ ω (absOp h ω)| ≤ ε * ‖ω‖ ^ 2 := by
    have e : (inner ℝ ω ((h * y) ω) : ℝ) - inner ℝ ω (absOp h ω)
        = inner ℝ ω ((h * y - absOp h) ω) := by
      rw [sub_apply, inner_sub_right]
    rw [e]
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    have h1 : ‖(h * y - absOp h) ω‖ ≤ ε * ‖ω‖ := by
      refine le_trans ((h * y - absOp h).le_opNorm ω) ?_
      have hb := norm_mul_signApprox_sub_absOp_le hhs hεpos
      rw [← hy] at hb
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg ω)
    calc ‖ω‖ * ‖(h * y - absOp h) ω‖ ≤ ‖ω‖ * (ε * ‖ω‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg ω)
      _ = ε * ‖ω‖ ^ 2 := by ring
  -- and RvD's estimate bounds the right-hand side by `⟪ω, |h| ω⟫`
  have hcomm : Commute h x' := mem_commutantSA.1 hx'M h hhM
  have hest := inner_le_inner_absOp ω hhs hx'0 hx'1 hcomm
  obtain ⟨hab1, hab2⟩ := abs_le.1 habs
  have hcontra : δ ≤ ε * ‖ω‖ ^ 2 := by rw [hLHS] at hkey; linarith
  have hsmall : ε * ‖ω‖ ^ 2 < δ := by
    rw [hεdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg ‖ω‖, hδ]
  linarith

/-- **RvD Lemma 4.3** for arbitrary self-adjoint `x' ∈ M'`: the unit case applies to the
two elements `(2‖x'‖+1)⁻¹ (x' + ‖x'‖)` and `1` of the order interval `[0,1]` of `M'`, and
the conclusion is real-linear in `x'`. -/
theorem lemma_4_3
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    {x' : ℋ →L[ℂ] ℋ} (hx'M : x' ∈ commutantSA M) (hx's : IsSelfAdjoint x')
    {lam : ℂ} (hlam : lam.re = 1) :
    ∃ y ∈ M, IsSelfAdjoint y ∧ P (Ksub M ω) (x' ω) = P (Ksub M ω) (lam • (y ω)) := by
  set N : ℝ := ‖x'‖ with hN
  set c : ℝ := 2 * N + 1 with hc
  have hNnn : 0 ≤ N := norm_nonneg _
  have hcpos : 0 < c := by rw [hc]; linarith
  have halg : (algebraMap ℝ (ℋ →L[ℂ] ℋ)) N = (N : ℝ) • (1 : ℋ →L[ℂ] ℋ) :=
    Algebra.algebraMap_eq_smul_one N
  -- the shifted element
  set u : ℋ →L[ℂ] ℋ := (c⁻¹ : ℝ) • (x' + (N : ℝ) • 1) with hu
  have hshift0 : (0 : ℋ →L[ℂ] ℋ) ≤ x' + (N : ℝ) • 1 := by
    have h := hx's.neg_algebraMap_norm_le_self
    rw [halg] at h
    have : (0 : ℋ →L[ℂ] ℋ) ≤ x' - (-((N : ℝ) • (1 : ℋ →L[ℂ] ℋ))) := sub_nonneg.2 h
    simpa using this
  have hshift1 : x' + (N : ℝ) • 1 ≤ ((2 * N : ℝ)) • (1 : ℋ →L[ℂ] ℋ) := by
    have h := hx's.le_algebraMap_norm_self
    rw [halg] at h
    have : x' + (N : ℝ) • (1 : ℋ →L[ℂ] ℋ) ≤ (N : ℝ) • (1 : ℋ →L[ℂ] ℋ)
        + (N : ℝ) • (1 : ℋ →L[ℂ] ℋ) := add_le_add h le_rfl
    rw [← add_smul] at this
    simpa [two_mul] using this
  have hu0 : (0 : ℋ →L[ℂ] ℋ) ≤ u := by
    rw [hu]
    exact smul_nonneg (by positivity) hshift0
  have hu1 : u ≤ 1 := by
    rw [hu]
    have h1 : (c⁻¹ : ℝ) • (x' + (N : ℝ) • 1) ≤ (c⁻¹ : ℝ) • (((2 * N : ℝ)) • (1 : ℋ →L[ℂ] ℋ)) :=
      smul_le_smul_of_nonneg_left hshift1 (by positivity)
    refine le_trans h1 ?_
    rw [smul_smul]
    have h2 : c⁻¹ * (2 * N) ≤ 1 := by
      rw [inv_mul_le_iff₀ hcpos, hc]; linarith
    have h3 : ((c⁻¹ * (2 * N) : ℝ)) • (1 : ℋ →L[ℂ] ℋ) ≤ (1 : ℝ) • (1 : ℋ →L[ℂ] ℋ) := by
      have hnn : (0 : ℋ →L[ℂ] ℋ) ≤ 1 := zero_le_one
      exact smul_le_smul_of_nonneg_right h2 hnn
    simpa using h3
  have hsm : ∀ (r : ℝ) (T : ℋ →L[ℂ] ℋ), (r : ℝ) • T = ((r : ℂ)) • T := by
    intro r T; rw [← Complex.coe_algebraMap, algebraMap_smul]
  have huM : u ∈ commutantSA M := by
    rw [hu, hsm, hsm]
    exact SMulMemClass.smul_mem _ (add_mem hx'M (SMulMemClass.smul_mem _ (one_mem _)))
  have h1M : (1 : ℋ →L[ℂ] ℋ) ∈ commutantSA M := one_mem _
  obtain ⟨yu, hyuM, hyus, -, hyu⟩ := lemma_4_3_unit M ω hM huM hu0 hu1 hlam
  obtain ⟨y1, hy1M, hy1s, -, hy1⟩ :=
    lemma_4_3_unit M ω hM h1M (zero_le_one) (le_refl (1 : ℋ →L[ℂ] ℋ)) hlam
  refine ⟨(c : ℂ) • yu - (N : ℂ) • y1, sub_mem (SMulMemClass.smul_mem _ hyuM)
    (SMulMemClass.smul_mem _ hy1M), ?_, ?_⟩
  · rw [IsSelfAdjoint, star_sub, star_smul, star_smul, hyus.star_eq, hy1s.star_eq]
    simp [Complex.conj_ofReal]
  · -- `x' ω = c • (u ω) - N • ω`
    have hxω : x' ω = (c : ℝ) • (u ω) - (N : ℝ) • ((1 : ℋ →L[ℂ] ℋ) ω) := by
      have : (c : ℝ) • (u ω) = (x' + (N : ℝ) • (1 : ℋ →L[ℂ] ℋ)) ω := by
        rw [hu, smul_apply, smul_smul, mul_inv_cancel₀ (ne_of_gt hcpos), one_smul]
      rw [this, add_apply, smul_apply]
      abel
    have hyω : ((c : ℂ) • yu - (N : ℂ) • y1) ω
        = (c : ℝ) • (yu ω) - (N : ℝ) • (y1 ω) := by
      rw [sub_apply, smul_apply, smul_apply, ← Complex.coe_algebraMap, algebraMap_smul,
        algebraMap_smul]
    rw [hxω, hyω]
    have hlin : lam • ((c : ℝ) • (yu ω) - (N : ℝ) • (y1 ω))
        = (c : ℝ) • (lam • (yu ω)) - (N : ℝ) • (lam • (y1 ω)) := by
      rw [smul_sub, smul_comm lam (c : ℝ), smul_comm lam (N : ℝ)]
    rw [hlin, map_sub, map_sub, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
      ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, hyu, hy1]

end Lemma43

/-! ### RvD Corollary 4.4 -/

section Cor44

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (ω : ℋ)

/-- `Q (x' ω) = 0` for self-adjoint `x' ∈ M'`: this is `M'_sa ω ⊆ (i𝒦)^⊥`, the last clause
of RvD Prop. 4.1. -/
lemma Q_commutant_orbit {x' : ℋ →L[ℂ] ℋ} (hx'M : x' ∈ commutantSA M)
    (hx's : IsSelfAdjoint x') : Q (Ksub M ω) (x' ω) = 0 := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _) ?_
  intro w hw
  obtain ⟨w₀, hw₀, rfl⟩ : ∃ w₀ ∈ Ksub M ω, w = (I : ℂ) • w₀ :=
    ⟨(-I : ℂ) • w, (mem_mulI_iff (Ksub M ω) w).1 hw, by simp [smul_smul]⟩
  rw [sub_zero, real_inner_comm]
  exact real_inner_mulI_orbit M ω hx'M hx's hw₀

variable (hsep : Ksub M ω ⊓ (Ksub M ω).mulI = ⊥) (hcyc : Ksub M ω ⊔ (Ksub M ω).mulI = ⊤)

include hsep hcyc

/-- **RvD Corollary 4.4** for self-adjoint `x' ∈ M'`: `J T x' ω = x ω` for some
self-adjoint `x ∈ M`.  Since `Q x' ω = 0`, `J T = P - Q` sends `x' ω` to `P x' ω`, and
Lemma 4.3 with `λ = 1` says that this is `x ω`. -/
theorem cor_4_4_sa
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    {x' : ℋ →L[ℂ] ℋ} (hx'M : x' ∈ commutantSA M) (hx's : IsSelfAdjoint x') :
    ∃ x ∈ M, IsSelfAdjoint x ∧ J (Ksub M ω) (T (Ksub M ω) (x' ω)) = x ω := by
  obtain ⟨y, hyM, hys, hyeq⟩ := lemma_4_3 M ω hM hx'M hx's (lam := 1) (by simp)
  refine ⟨y, hyM, hys, ?_⟩
  rw [← A_eq_J_T (Ksub M ω) hsep hcyc, A_apply, Q_commutant_orbit M ω hx'M hx's, sub_zero,
    hyeq, one_smul]
  exact P_eq_self (mem_Ksub_of_sa M ω hyM hys)

/-- **RvD Corollary 4.4**: for every `x' ∈ M'` there is `x ∈ M` with `J T x' ω = x ω` and
`J T x'^* ω = x^* ω`.  The self-adjoint case extends by conjugate linearity of `J T`. -/
theorem cor_4_4
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    {x' : ℋ →L[ℂ] ℋ} (hx'M : x' ∈ commutantSA M) :
    ∃ x ∈ M, J (Ksub M ω) (T (Ksub M ω) (x' ω)) = x ω ∧
      J (Ksub M ω) (T (Ksub M ω) ((star x') ω)) = (star x) ω := by
  obtain ⟨h', hh', k', hk', hh's, hk's, rfl⟩ := exists_sa_decomp (commutantSA M) x' hx'M
  obtain ⟨xh, hxhM, hxhs, hxh⟩ := cor_4_4_sa M ω hsep hcyc hM hh' hh's
  obtain ⟨xk, hxkM, hxks, hxk⟩ := cor_4_4_sa M ω hsep hcyc hM hk' hk's
  refine ⟨xh - (I : ℂ) • xk, sub_mem hxhM (SMulMemClass.smul_mem _ hxkM), ?_, ?_⟩
  · have hap : (h' + (I : ℂ) • k') ω = h' ω + (I : ℂ) • (k' ω) := by
      rw [add_apply, smul_apply]
    rw [hap, map_add, map_smul, map_add, J_smul (Ksub M ω) hsep hcyc, hxh, hxk, Complex.conj_I,
      sub_apply, smul_apply]
    module
  · have hst : star (h' + (I : ℂ) • k') = h' - (I : ℂ) • k' := by
      rw [star_add, star_smul, hh's.star_eq, hk's.star_eq, Complex.star_def, Complex.conj_I,
        neg_smul, ← sub_eq_add_neg]
    have hst2 : star (xh - (I : ℂ) • xk) = xh + (I : ℂ) • xk := by
      rw [star_sub, star_smul, hxhs.star_eq, hxks.star_eq, Complex.star_def, Complex.conj_I,
        neg_smul, sub_neg_eq_add]
    rw [hst, hst2]
    have hap : (h' - (I : ℂ) • k') ω = h' ω - (I : ℂ) • (k' ω) := by
      rw [sub_apply, smul_apply]
    rw [hap, map_sub, map_smul, map_sub, J_smul (Ksub M ω) hsep hcyc, hxh, hxk, Complex.conj_I,
      add_apply, smul_apply]
    module

end Cor44

end BH

end Theses.RvD


