/-
**Tomita's involution for a von Neumann algebra with a cyclic and separating vector**,
in the bounded-operator formulation of

  M. A. Rieffel and A. van Daele, *A bounded operator approach to
  Tomita–Takesaki theory*, Pacific J. Math. **69** (1977) 187–221,

§4 (Proposition 4.1) and the Appendix (Proposition (3)).

**This file has no thesis counterpart.**  It is the point where the real-subspace
machinery of `Theses/A/VN/StandardSubspace.lean` and the unbounded operator
`D_{a,b} = Δ^{1/2}` of `Theses/A/VN/Modular.lean` are attached to an actual von
Neumann algebra; see `docs/COMMUTATION-THEOREM.md` §4.

## The setting

`M` is a unital ∗-subalgebra of `B(ℋ)` which is its own bicommutant, and `ω : ℋ`
is cyclic and separating for `M`.  Put `𝒦 = closure (M_sa ω)`, a closed *real*
subspace of `ℋ` (`Ksub`).

## Main results

* `Ksub_sup_mulI_eq_top` : `𝒦 ⊔ i𝒦 = ⊤` — this is the **cyclicity** of `ω`.
* `dense_commutant_orbit` : the **separating** property of `ω`, together with
  `M'' = M`, makes `M' ω` dense (the classical `[M'ω] ∈ M''` device, supplied by
  `exists_cyclic_projection`).
* `Ksub_inf_mulI_eq_bot` : density of `M' ω` gives `𝒦 ⊓ i𝒦 = ⊥`.
* `standardSubspace` : **RvD Prop. 4.1** — `𝒦` is a `StandardSubspace ℋ`.  Hence
  `StandardSubspace.lean`'s `isModularPair_a_b` applies and `D = D_{a,b}` is
  `Δ_ω^{1/2}`.
* `orbit_mem_domain`, `J_D_orbit` : **RvD Appendix Prop. (3)** — for `x ∈ M`,
  `x ω ∈ dom Δ_ω^{1/2}` and `J (Δ_ω^{1/2} (x ω)) = x* ω`.  Together with
  `exists_mem_K_repr` (`dom Δ_ω^{1/2} = 𝒦 + i𝒦`) and `J_D_apply`
  (`J Δ_ω^{1/2} (η + iη') = η - iη'`) this *is* the statement `S_ω = J Δ_ω^{1/2}`,
  written entirely with the ℂ-linear unbounded `D` and the bounded conjugate-linear
  `J`.  **No conjugate-linear unbounded operator is defined anywhere**: see the
  note below.
* `orbit_hasCore` : `M ω` is a **core** for `Δ_ω^{1/2}`.
* `bicommutant_eq_of_uwClosed` : the bicommutant hypothesis is ultraweak closedness (**88VI**).
* Part IV bundles the three hypotheses: `modularSqrt` (`Δ_ω^{1/2}`), `modularConj` (`J_ω`, a
  conjugate-linear isometric involution), `modularSqrt_hasCore`,
  `modularConj_modularSqrt_orbit` and `modularConj_modularSqrt`.

## Why there is no `S_ω`

Mathlib's `LinearPMap` is single-ring, so a densely defined *conjugate-linear*
operator has no home in it.  It is not needed: `S_ω` is only ever used through
`J S_ω` and `S_ω`'s graph, and `J` is bounded and involutive, so every statement
about `S_ω` transposes to one about `D` and `J`.  Concretely, `S_ω = J D` means
`dom D = 𝒦 + i𝒦` (`exists_mem_K_repr`, `mem_domain_of_repr`) together with
`J (D (η + iη')) = η - iη'` (`J_D_apply`); and `S_ω (x ω) = x* ω` becomes
`J (D (x ω)) = x* ω` (`J_D_orbit`).

## The bounded identities behind all of this

The bridge from the real-subspace side to the modular pair is
`P = a² + a b J` (`P_eq`), whose ingredients are `T = 2 a b` (`T_eq_smul_a_b`)
and `J a = b J` (`J_a`); the latter is `J a J = b`, proved by exhibiting `J a J`
as a positive operator whose square is `(2 - R)/2` and invoking uniqueness of
positive square roots.  From `P = a² + abJ` one reads off `𝒦 = a (fix J)`
(`mem_K_iff`), and then `ran a = 𝒦 + i𝒦` and the formula for `J D` are two lines
of algebra.
-/
import Theses.A.VN.NormalFunctionals
import Theses.A.VN.StandardSubspace

open Complex ClosedSubmodule Theses.A.VN
open scoped ComplexInnerProductSpace ComplexOrder

namespace Theses.RvD

/-! ## Part I: bounded identities relating `P`, `J`, `a` and `b`

Everything in this part is about a closed real subspace `K` of a complex Hilbert space and
uses no von Neumann algebras. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (K : ClosedSubmodule ℝ H)

lemma a_b_nonneg : (0 : H →L[ℂ] H) ≤ a K * b K :=
  Commute.mul_nonneg (a_nonneg K) (b_nonneg K) (commute_a_b K)

lemma T_eq_smul_a_b : T K = (2 : ℝ) • (a K * b K) := by
  show CFC.sqrt (R K * (2 - R K)) = _
  refine CFC.sqrt_unique ?_ ?_
  · have hab : a K * b K * (a K * b K) = (a K * a K) * (b K * b K) := by
      have := (commute_a_b K).symm
      simp only [mul_assoc]
      rw [← mul_assoc (b K) (a K) (b K), (commute_a_b K).symm.eq, mul_assoc]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hab, a_mul_a, b_mul_b, smul_mul_assoc,
      mul_smul_comm, smul_smul, smul_smul]
    norm_num
  · exact smul_nonneg (by norm_num) (a_b_nonneg K)

/-- `J a J`, as a real-linear map. -/
noncomputable def Phire : H →L[ℝ] H := (J K) ∘L ((a K).restrictScalars ℝ) ∘L (J K)

@[simp] lemma Phire_apply (x : H) : Phire K x = J K (a K (J K x)) := rfl

lemma a_real_symm (x y : H) : inner ℝ (a K x) y = inner ℝ x (a K y) := by
  have h := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (IsSelfAdjoint.of_nonneg (a_nonneg K)) x y
  simp only [ContinuousLinearMap.coe_coe] at h
  exact congrArg Complex.re h

lemma a_a_apply (x : H) : a K (a K x) = (2⁻¹ : ℝ) • (R K x) := by
  have := congrArg (fun f : H →L[ℂ] H => f x) (a_mul_a K)
  simpa using this

lemma b_b_apply (x : H) : b K (b K x) = (2⁻¹ : ℝ) • (((2 : H →L[ℂ] H) - R K) x) := by
  have := congrArg (fun f : H →L[ℂ] H => f x) (b_mul_b K)
  simpa using this

lemma a_a_add_b_b_apply (x : H) : a K (a K x) + b K (b K x) = x := by
  have := congrArg (fun f : H →L[ℂ] H => f x) (a_mul_a_add_b_mul_b K)
  simpa using this

section JAB

variable (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤)

include hsep hcyc

/-- `J` as a real linear isometry. -/
noncomputable def Jli : H →ₗᵢ[ℝ] H where
  toLinearMap := (J K).toLinearMap
  norm_map' := J_norm K hsep hcyc

lemma J_inner_real (x y : H) : inner ℝ (J K x) (J K y) = inner ℝ x y :=
  (Jli K hsep hcyc).inner_map_map x y

lemma Phire_smul_I (x : H) : Phire K (I • x) = I • Phire K x := by
  show J K (a K (J K (I • x))) = I • J K (a K (J K x))
  rw [J_smul_I K hsep hcyc, map_neg, map_smul, map_neg, J_smul_I K hsep hcyc, neg_neg]

/-- `J a J`, as a complex-linear map. -/
noncomputable def Phi : H →L[ℂ] H where
  toFun := Phire K
  map_add' := map_add _
  map_smul' := smul_complex_of_smul_I (Phire_smul_I K hsep hcyc)
  cont := (Phire K).continuous

@[simp] lemma Phi_apply (x : H) : Phi K hsep hcyc x = J K (a K (J K x)) := rfl

lemma Phi_symm (x y : H) :
    inner ℝ (Phi K hsep hcyc x) y = inner ℝ x (Phi K hsep hcyc y) := by
  have hx : x = J K (J K x) := (J_J K hsep hcyc x).symm
  have hy : y = J K (J K y) := (J_J K hsep hcyc y).symm
  show inner ℝ (J K (a K (J K x))) y = inner ℝ x (J K (a K (J K y)))
  calc inner ℝ (J K (a K (J K x))) y
      = inner ℝ (J K (a K (J K x))) (J K (J K y)) := by rw [← hy]
    _ = inner ℝ (a K (J K x)) (J K y) := J_inner_real K hsep hcyc _ _
    _ = inner ℝ (J K x) (a K (J K y)) := a_real_symm K _ _
    _ = inner ℝ (J K (J K x)) (J K (a K (J K y))) := (J_inner_real K hsep hcyc _ _).symm
    _ = inner ℝ x (J K (a K (J K y))) := by rw [← hx]

lemma Phi_nonneg : (0 : H →L[ℂ] H) ≤ Phi K hsep hcyc := by
  refine (ContinuousLinearMap.nonneg_iff_isPositive _).2
    ⟨isSymmetric_of_real_symm _ (Phi_symm K hsep hcyc), fun x => ?_⟩
  have h : (Phi K hsep hcyc).reApplyInnerSelf x = inner ℝ (a K (J K x)) (J K x) := by
    have h0 : (Phi K hsep hcyc).reApplyInnerSelf x = inner ℝ (Phi K hsep hcyc x) x := rfl
    have hx : x = J K (J K x) := (J_J K hsep hcyc x).symm
    rw [h0, Phi_apply]
    calc inner ℝ (J K (a K (J K x))) x
        = inner ℝ (J K (a K (J K x))) (J K (J K x)) := by rw [← hx]
      _ = inner ℝ (a K (J K x)) (J K x) := J_inner_real K hsep hcyc _ _
  rw [h]
  exact ((ContinuousLinearMap.nonneg_iff_isPositive (a K)).1 (a_nonneg K)).2 (J K x)

lemma Phi_mul_Phi : Phi K hsep hcyc * Phi K hsep hcyc = (2⁻¹ : ℝ) • ((2 : H →L[ℂ] H) - R K) := by
  ext x
  show J K (a K (J K (J K (a K (J K x))))) = ((2⁻¹ : ℝ) • ((2 : H →L[ℂ] H) - R K)) x
  rw [J_J K hsep hcyc]
  have h : a K (a K (J K x)) = (2⁻¹ : ℝ) • (R K (J K x)) := by
    have := congrArg (fun f : H →L[ℂ] H => f (J K x)) (a_mul_a K)
    simpa using this
  rw [h, map_smul, J_R K hsep hcyc, J_J K hsep hcyc]
  simp

lemma Phi_eq_b : Phi K hsep hcyc = b K := by
  have h := Phi_mul_Phi K hsep hcyc
  rw [← b_mul_b K] at h
  exact (CFC.mul_self_eq_mul_self_iff _ _ (Phi_nonneg K hsep hcyc) (b_nonneg K)).1 h

/-- `J a = b J`. -/
lemma J_a (x : H) : J K (a K x) = b K (J K x) := by
  have h := congrArg (fun f : H →L[ℂ] H => f (J K x)) (Phi_eq_b K hsep hcyc)
  simp only [Phi_apply, J_J K hsep hcyc] at h
  exact h

/-- `J b = a J`. -/
lemma J_b (x : H) : J K (b K x) = a K (J K x) := by
  have h := J_a K hsep hcyc (J K x)
  rw [J_J K hsep hcyc] at h
  rw [← h, J_J K hsep hcyc]

/-- `A = P - Q` in terms of `a`, `b` and `J`: `A = 2 a b J`. -/
lemma A_eq (x : H) : A K x = (2 : ℝ) • (a K (b K (J K x))) := by
  rw [← J_T K hsep hcyc, T_eq_smul_a_b]
  show J K ((2 : ℝ) • (a K (b K x))) = _
  rw [map_smul, J_a K hsep hcyc, J_b K hsep hcyc]
  congr 1
  exact (commute_apply (commute_a_b K).symm (J K x))

/-- **The bridge between the projection `P` and the modular pair.**  `P = a² + a b J`. -/
lemma P_eq (x : H) : P K x = a K (a K x) + a K (b K (J K x)) := by
  have h2 : (2 : ℝ) • P K x = R K x + A K x := by
    rw [R_apply, A_apply, two_smul]; abel
  have h3 : (2 : ℝ) • (a K (a K x) + a K (b K (J K x))) = R K x + A K x := by
    rw [smul_add, a_a_apply, smul_smul, A_eq K hsep hcyc]
    norm_num
  exact smul_right_injective H (by norm_num : (2 : ℝ) ≠ 0) (h2.trans h3.symm)

/-- **RvD**: `K` is exactly the image under `a` of the fixed-point set of `J`. -/
lemma mem_K_iff (η : H) : η ∈ K ↔ ∃ ξ : H, J K ξ = ξ ∧ a K ξ = η := by
  constructor
  · intro hη
    refine ⟨a K η + b K (J K η), ?_, ?_⟩
    · rw [map_add, J_a K hsep hcyc, J_b K hsep hcyc, J_J K hsep hcyc]
      exact add_comm _ _
    · rw [map_add, ← P_eq K hsep hcyc, P_eq_self hη]
  · rintro ⟨ξ, hξ, rfl⟩
    have h : P K (a K ξ) = a K ξ := by
      rw [P_eq K hsep hcyc, J_a K hsep hcyc, hξ, ← map_add, a_a_add_b_b_apply]
    exact h ▸ P_apply_mem K (a K ξ)

/-! ### The domain of `D` is `K + iK`, and `J D` is the Tomita involution -/

/-- Shorthand for the modular pair attached to a standard closed real subspace. -/
noncomputable abbrev mp : IsModularPair (a K) (b K) := isModularPair_a_b K hsep hcyc

theorem mem_domain_of_mem_K {η : H} (hη : η ∈ K) : η ∈ (mp K hsep hcyc).D.domain := by
  obtain ⟨ξ, -, rfl⟩ := (mem_K_iff K hsep hcyc η).1 hη
  exact (mp K hsep hcyc).mem_D_domain ξ

/-- Every element of `dom D = ran a` is `η + i η'` with `η, η' ∈ K`. -/
theorem exists_mem_K_repr {ζ : H} (hζ : ζ ∈ (mp K hsep hcyc).D.domain) :
    ∃ η ∈ K, ∃ η' ∈ K, ζ = η + I • η' := by
  obtain ⟨ξ, rfl⟩ : ∃ ξ, a K ξ = ζ := hζ
  set p : H := (2⁻¹ : ℂ) • (ξ + J K ξ) with hp
  set q : H := (-I / 2 : ℂ) • (ξ - J K ξ) with hq
  have hJp : J K p = p := by
    rw [hp, J_smul K hsep hcyc, map_add, J_J K hsep hcyc,
      show (starRingEnd ℂ) (2⁻¹ : ℂ) = 2⁻¹ by rw [map_inv₀, map_ofNat], add_comm]
  have hJq : J K q = q := by
    rw [hq, J_smul K hsep hcyc, map_sub, J_J K hsep hcyc,
      show (starRingEnd ℂ) (-I / 2 : ℂ) = I / 2 by
        rw [map_div₀, map_neg, Complex.conj_I, map_ofNat]; ring]
    module
  refine ⟨a K p, (mem_K_iff K hsep hcyc _).2 ⟨p, hJp, rfl⟩,
    a K q, (mem_K_iff K hsep hcyc _).2 ⟨q, hJq, rfl⟩, ?_⟩
  rw [← map_smul, ← map_add]
  congr 1
  rw [hp, hq]
  match_scalars <;> simp [Complex.ext_iff] <;> ring

/-- Conversely `K + iK ⊆ dom D`. -/
theorem mem_domain_of_repr {η η' : H} (hη : η ∈ K) (hη' : η' ∈ K) :
    η + I • η' ∈ (mp K hsep hcyc).D.domain :=
  Submodule.add_mem _ (mem_domain_of_mem_K K hsep hcyc hη)
    (Submodule.smul_mem _ _ (mem_domain_of_mem_K K hsep hcyc hη'))

/-- **The Tomita involution, in bounded form.**  On `dom D = K + iK`, the operator `J D`
sends `η + i η'` to `η - i η'` for `η, η' ∈ K`. -/
theorem J_D_apply {η η' : H} (hη : η ∈ K) (hη' : η' ∈ K)
    (h : η + I • η' ∈ (mp K hsep hcyc).D.domain) :
    J K ((mp K hsep hcyc).D ⟨η + I • η', h⟩) = η - I • η' := by
  obtain ⟨ξ, hJξ, rfl⟩ := (mem_K_iff K hsep hcyc η).1 hη
  obtain ⟨ξ', hJξ', rfl⟩ := (mem_K_iff K hsep hcyc η').1 hη'
  have hval : (mp K hsep hcyc).D ⟨a K ξ + I • a K ξ', h⟩ = b K (ξ + I • ξ') := by
    refine (mp K hsep hcyc).D_apply' _ (ξ + I • ξ') ?_
    rw [map_add, map_smul]
  rw [hval, J_b K hsep hcyc, map_add, J_smul K hsep hcyc, hJξ, hJξ', map_add,
    map_smul, Complex.conj_I]
  module

end JAB

/-! ## Part II: von Neumann algebras, cyclic and separating vectors, and RvD Prop. 4.1 -/

variable {A : Type*} [CStarAlgebra A]

/-- The commutant of a ∗-subalgebra, bundled as a ∗-subalgebra. -/
def commutantSA (M : StarSubalgebra ℂ A) : StarSubalgebra ℂ A where
  toSubalgebra := Subalgebra.centralizer ℂ (M : Set A)
  star_mem' := by
    intro x hx m hm
    have h1 := congrArg star (hx (star m) (M.star_mem' hm))
    rw [star_mul, star_mul, star_star] at h1
    exact h1.symm

@[simp] lemma coe_commutantSA (M : StarSubalgebra ℂ A) :
    (commutantSA M : Set A) = commutant A (M : Set A) := rfl

lemma mem_commutantSA {M : StarSubalgebra ℂ A} {x : A} :
    x ∈ commutantSA M ↔ ∀ m ∈ M, m * x = x * m := Iff.rfl

section BH

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (ω : ℋ)

/-- `ω` is **cyclic** for `M`: the orbit `M ω` is dense. -/
def IsCyclicVector : Prop := Dense {y : ℋ | ∃ x ∈ M, y = x ω}

/-- `ω` is **separating** for `M`: `x ω = 0` forces `x = 0`. -/
def IsSeparatingVector : Prop := ∀ x ∈ M, x ω = 0 → x = 0

/-- The real subspace `M_sa ω`. -/
def saOrbit : Submodule ℝ ℋ where
  carrier := {y : ℋ | ∃ x ∈ M, IsSelfAdjoint x ∧ y = x ω}
  add_mem' := by
    rintro _ _ ⟨x, hx, hxs, rfl⟩ ⟨y, hy, hys, rfl⟩
    exact ⟨x + y, add_mem hx hy, hxs.add hys, rfl⟩
  zero_mem' := ⟨0, zero_mem _, IsSelfAdjoint.zero _, by simp⟩
  smul_mem' := by
    rintro r _ ⟨x, hx, hxs, rfl⟩
    refine ⟨(r : ℂ) • x, SMulMemClass.smul_mem _ hx, ?_, ?_⟩
    · rw [IsSelfAdjoint, star_smul, hxs.star_eq, Complex.star_def, Complex.conj_ofReal]
    · rw [smul_apply, ← Complex.coe_algebraMap, algebraMap_smul]

lemma mem_saOrbit_iff {y : ℋ} :
    y ∈ saOrbit M ω ↔ ∃ x ∈ M, IsSelfAdjoint x ∧ y = x ω := Iff.rfl

lemma saOrbit_apply {x : ℋ →L[ℂ] ℋ} (hx : x ∈ M) (hxs : IsSelfAdjoint x) :
    x ω ∈ saOrbit M ω := ⟨x, hx, hxs, rfl⟩

/-- **RvD Prop. 4.1**, the subspace: `𝒦 = closure (M_sa ω)`. -/
noncomputable def Ksub : ClosedSubmodule ℝ ℋ := (saOrbit M ω).closure

lemma saOrbit_le_Ksub : saOrbit M ω ≤ (Ksub M ω).toSubmodule :=
  (saOrbit M ω).le_topologicalClosure

lemma mem_Ksub_of_sa {x : ℋ →L[ℂ] ℋ} (hx : x ∈ M) (hxs : IsSelfAdjoint x) :
    x ω ∈ Ksub M ω := saOrbit_le_Ksub M ω (saOrbit_apply M ω hx hxs)

/-- The real and imaginary parts of `x`. -/
lemma exists_sa_decomp (x : ℋ →L[ℂ] ℋ) (hx : x ∈ M) :
    ∃ h ∈ M, ∃ k ∈ M, IsSelfAdjoint h ∧ IsSelfAdjoint k ∧ x = h + I • k := by
  have hs : star x ∈ M := M.star_mem' hx
  refine ⟨(2⁻¹ : ℂ) • (x + star x), SMulMemClass.smul_mem _ (add_mem hx hs),
    (-I / 2 : ℂ) • (x - star x), SMulMemClass.smul_mem _ (sub_mem hx hs), ?_, ?_, ?_⟩
  · rw [IsSelfAdjoint, star_smul, star_add, star_star, add_comm,
      show star (2⁻¹ : ℂ) = 2⁻¹ by rw [Complex.star_def, map_inv₀, map_ofNat]]
  · rw [IsSelfAdjoint, star_smul, star_sub, star_star,
      show star (-I / 2 : ℂ) = I / 2 by
        rw [Complex.star_def, map_div₀, map_neg, Complex.conj_I, map_ofNat]; ring]
    rw [smul_sub, smul_sub]
    match_scalars <;> ring
  · rw [smul_smul]
    match_scalars <;> simp [Complex.ext_iff] <;> ring

/-! ### The two halves of RvD Prop. 4.1 -/

/-- The cyclicity of `ω` gives `𝒦 ⊔ i𝒦 = ⊤`. -/
theorem Ksub_sup_mulI_eq_top (hcyc : IsCyclicVector M ω) :
    Ksub M ω ⊔ (Ksub M ω).mulI = ⊤ := by
  refine le_antisymm le_top fun ζ _ => ?_
  rw [ClosedSubmodule.mem_sup]
  set N : Submodule ℝ ℋ := (Ksub M ω).toSubmodule ⊔ (Ksub M ω).mulI.toSubmodule with hN
  have hsub : {y : ℋ | ∃ x ∈ M, y = x ω} ⊆ (N : Set ℋ) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨h, hh, k, hk, hhs, hks, rfl⟩ := exists_sa_decomp M x hx
    have h1 : h ω ∈ N :=
      Submodule.mem_sup_left (mem_Ksub_of_sa M ω hh hhs)
    have h2 : (I : ℂ) • (k ω) ∈ N :=
      Submodule.mem_sup_right ((smul_I_mem_mulI_iff (Ksub M ω) _).2 (mem_Ksub_of_sa M ω hk hks))
    have : (h + I • k) ω = h ω + (I : ℂ) • (k ω) := by
      rw [add_apply, smul_apply]
    rw [this]
    exact Submodule.add_mem N h1 h2
  have := closure_mono hsub
  rw [hcyc.closure_eq] at this
  exact this (Set.mem_univ ζ)

/-- For `x ∈ M` and `y ∈ M'` self-adjoint, `⟪x ω, y ω⟫` is real. -/
lemma inner_sa_orbit_im {x y : ℋ →L[ℂ] ℋ} (hx : x ∈ M) (hxs : IsSelfAdjoint x)
    (hy : y ∈ commutantSA M) (hys : IsSelfAdjoint y) : (⟪x ω, y ω⟫).im = 0 := by
  have hxsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hxs
  have hysym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hys
  have hcomm : x (y ω) = y (x ω) := by
    have := congrArg (fun f : ℋ →L[ℂ] ℋ => f ω) (mem_commutantSA.1 hy x hx)
    simpa using this
  have h1 : (⟪x ω, y ω⟫ : ℂ) = ⟪y ω, x ω⟫ := by
    calc (⟪x ω, y ω⟫ : ℂ) = ⟪ω, x (y ω)⟫ := hxsym ω (y ω)
      _ = ⟪ω, y (x ω)⟫ := by rw [hcomm]
      _ = ⟪y ω, x ω⟫ := (hysym ω (x ω)).symm
  have h2 : (⟪x ω, y ω⟫ : ℂ) = (starRingEnd ℂ) ⟪x ω, y ω⟫ := by
    rw [inner_conj_symm]; exact h1
  have h3 := congrArg Complex.im h2
  simp only [Complex.conj_im] at h3
  linarith

/-- `i 𝒦 ⟂ M'_sa ω` for the *real* inner product. -/
lemma real_inner_mulI_orbit {y : ℋ →L[ℂ] ℋ} (hy : y ∈ commutantSA M) (hys : IsSelfAdjoint y)
    {w : ℋ} (hw : w ∈ Ksub M ω) : inner ℝ ((I : ℂ) • w) (y ω) = 0 := by
  have hclosed : IsClosed {v : ℋ | inner ℝ ((I : ℂ) • v) (y ω) = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hsub : (saOrbit M ω : Set ℋ) ⊆ {v : ℋ | inner ℝ ((I : ℂ) • v) (y ω) = 0} := by
    rintro _ ⟨x, hx, hxs, rfl⟩
    have him := inner_sa_orbit_im M ω hx hxs hy hys
    show (⟪(I : ℂ) • (x ω), y ω⟫).re = 0
    rw [inner_smul_left]
    simp [Complex.mul_re, him]
  have hmem : w ∈ closure (saOrbit M ω : Set ℋ) := by
    have : (Ksub M ω : Set ℋ) = closure (saOrbit M ω : Set ℋ) :=
      Submodule.topologicalClosure_coe _
    rw [← this]
    exact hw
  exact hclosed.closure_subset_iff.2 hsub hmem

/-- The separating property of `ω` — in the form "`M' ω` is dense" — gives `𝒦 ⊓ i𝒦 = ⊥`. -/
theorem Ksub_inf_mulI_eq_bot (hd : Dense {y : ℋ | ∃ x ∈ commutantSA M, y = x ω}) :
    Ksub M ω ⊓ (Ksub M ω).mulI = ⊥ := by
  refine le_antisymm (fun ζ hζ => ?_) bot_le
  obtain ⟨hζK, hζmI⟩ := hζ
  have keySA : ∀ y ∈ commutantSA M, IsSelfAdjoint y → (⟪ζ, y ω⟫ : ℂ) = 0 := by
    intro y hy hys
    have h1 : inner ℝ ζ (y ω) = 0 := by
      have hw : ((-I : ℂ)) • ζ ∈ Ksub M ω := (mem_mulI_iff (Ksub M ω) ζ).1 hζmI
      have := real_inner_mulI_orbit M ω hy hys hw
      rwa [smul_smul, show (I : ℂ) * (-I) = 1 by simp, one_smul] at this
    have h2 : inner ℝ ((I : ℂ) • ζ) (y ω) = 0 := real_inner_mulI_orbit M ω hy hys hζK
    have h2' : (⟪ζ, y ω⟫ : ℂ).im = 0 := by
      have he : inner ℝ ((I : ℂ) • ζ) (y ω) = (⟪ζ, y ω⟫ : ℂ).im := by
        show (⟪(I : ℂ) • ζ, y ω⟫ : ℂ).re = _
        rw [inner_smul_left]
        simp [Complex.mul_re]
      rw [he] at h2
      exact h2
    refine Complex.ext ?_ ?_
    · simpa only [Complex.zero_re, ← inner_real_eq_re_inner] using h1
    · simpa only [Complex.zero_im] using h2'
  have key : ∀ y ∈ commutantSA M, (⟪ζ, y ω⟫ : ℂ) = 0 := by
    intro y hy
    obtain ⟨h, hh, k, hk, hhs, hks, rfl⟩ := exists_sa_decomp (commutantSA M) y hy
    have : (h + I • k) ω = h ω + (I : ℂ) • (k ω) := by
      rw [add_apply, smul_apply]
    rw [this, inner_add_right, inner_smul_right, keySA h hh hhs, keySA k hk hks]
    simp
  have hZ : IsClosed {v : ℋ | (⟪ζ, v⟫ : ℂ) = 0} := isClosed_eq (by fun_prop) continuous_const
  have hsubZ : {y : ℋ | ∃ x ∈ commutantSA M, y = x ω} ⊆ {v : ℋ | (⟪ζ, v⟫ : ℂ) = 0} := by
    rintro _ ⟨x, hx, rfl⟩
    exact key x hx
  have : ζ ∈ {v : ℋ | (⟪ζ, v⟫ : ℂ) = 0} := by
    have := hZ.closure_subset_iff.2 hsubZ
    rw [hd.closure_eq] at this
    exact this (Set.mem_univ ζ)
  exact inner_self_eq_zero.1 this

/-- **Separating implies `M' ω` dense.**  The projection onto `closure (M' ω)` lies in `M'' = M`
and fixes `ω`, so its complement kills `ω` and hence vanishes.  (The classical `[Sx] ∈ S□`
device is `exists_cyclic_projection`.) -/
theorem dense_commutant_orbit (hsepv : IsSeparatingVector M ω)
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ))) :
    Dense {y : ℋ | ∃ x ∈ commutantSA M, y = x ω} := by
  obtain ⟨q, -, hqc, hqω, hfix⟩ := exists_cyclic_projection (commutantSA M) ω
  have hqM : q ∈ M := by
    have h : q ∈ commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ))) := hqc
    rw [hM] at h
    exact h
  have h1 : (1 : ℋ →L[ℂ] ℋ) - q = 0 := by
    refine hsepv _ (sub_mem (one_mem M) hqM) ?_
    rw [sub_apply, one_apply_eq_self, hqω, sub_self]
  have hq1 : q = 1 := (sub_eq_zero.1 h1).symm
  rw [hq1] at hfix
  refine dense_iff_closure_eq.2 ?_
  rw [← hfix]
  ext y
  simp

/-- The bicommutant hypothesis below is exactly ultraweak closedness, by **88VI**
`double_commutant`. -/
theorem bicommutant_eq_of_uwClosed
    (h : @IsClosed _ (ultraweak (ℋ →L[ℂ] ℋ)) (M : Set (ℋ →L[ℂ] ℋ))) :
    commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)) := by
  rw [(double_commutant M).2.1, @IsClosed.closure_eq _ (ultraweak (ℋ →L[ℂ] ℋ)) _ h]

/-! ### RvD Prop. 4.1 -/

/-- **RvD Prop. 4.1**: for a von Neumann algebra `M ⊆ B(ℋ)` with a cyclic and separating vector
`ω`, the closed real subspace `𝒦 = closure (M_sa ω)` is **standard**: `𝒦 ⊓ i𝒦 = ⊥` and
`𝒦 ⊔ i𝒦 = ⊤`.  Separating gives the first, cyclic the second. -/
theorem isStandard (hcycv : IsCyclicVector M ω) (hsepv : IsSeparatingVector M ω)
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ))) :
    Ksub M ω ⊓ (Ksub M ω).mulI = ⊥ ∧ Ksub M ω ⊔ (Ksub M ω).mulI = ⊤ :=
  ⟨Ksub_inf_mulI_eq_bot M ω (dense_commutant_orbit M ω hsepv hM),
    Ksub_sup_mulI_eq_top M ω hcycv⟩

/-- **RvD Prop. 4.1**, packaged as one of Mathlib's `StandardSubspace`s. -/
noncomputable def standardSubspace (hcycv : IsCyclicVector M ω) (hsepv : IsSeparatingVector M ω)
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ))) : StandardSubspace ℋ where
  toClosedSubmodule := Ksub M ω
  IsSeparating := (isStandard M ω hcycv hsepv hM).1
  IsCyclic := (isStandard M ω hcycv hsepv hM).2

@[simp] lemma standardSubspace_toClosedSubmodule (hcycv : IsCyclicVector M ω)
    (hsepv : IsSeparatingVector M ω)
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ))) :
    (standardSubspace M ω hcycv hsepv hM).toClosedSubmodule = Ksub M ω := rfl

/-! ## Part III: `S_ω = J Δ_ω^{1/2}` and `M ω` as a core

The Tomita involution `x ω ↦ x* ω` is never defined as an operator: it appears only through
`J ∘ D`, which is what `J_D_orbit` says. -/

/-- The complex subspace `M ω`. -/
def orbitSub : Submodule ℂ ℋ where
  carrier := {y : ℋ | ∃ x ∈ M, y = x ω}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, add_mem hx hy, rfl⟩
  zero_mem' := ⟨0, zero_mem M, by simp⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    exact ⟨c • x, SMulMemClass.smul_mem _ hx, rfl⟩

@[simp] lemma mem_orbitSub_iff {y : ℋ} : y ∈ orbitSub M ω ↔ ∃ x ∈ M, y = x ω := Iff.rfl

lemma coe_orbitSub : (orbitSub M ω : Set ℋ) = {y : ℋ | ∃ x ∈ M, y = x ω} := rfl

/-- The decomposition `x ω = η + i η'` with `η, η' ∈ 𝒦` and `x* ω = η - i η'`. -/
theorem exists_K_repr_orbit {x : ℋ →L[ℂ] ℋ} (hx : x ∈ M) :
    ∃ η ∈ Ksub M ω, ∃ η' ∈ Ksub M ω, x ω = η + I • η' ∧ (star x) ω = η - I • η' := by
  obtain ⟨h, hh, k, hk, hhs, hks, rfl⟩ := exists_sa_decomp M x hx
  refine ⟨h ω, mem_Ksub_of_sa M ω hh hhs, k ω, mem_Ksub_of_sa M ω hk hks, ?_, ?_⟩
  · rw [add_apply, smul_apply]
  · rw [star_add, star_smul, hhs.star_eq, hks.star_eq, Complex.star_def, Complex.conj_I,
      add_apply, smul_apply, neg_smul, ← sub_eq_add_neg]

section Tomita

variable (hsep : Ksub M ω ⊓ (Ksub M ω).mulI = ⊥) (hcyc : Ksub M ω ⊔ (Ksub M ω).mulI = ⊤)

include hsep hcyc

/-- For `x ∈ M`, `x ω` lies in the domain of `Δ_ω^{1/2}`. -/
theorem orbit_mem_domain {x : ℋ →L[ℂ] ℋ} (hx : x ∈ M) :
    x ω ∈ (mp (Ksub M ω) hsep hcyc).D.domain := by
  obtain ⟨η, hη, η', hη', hx1, -⟩ := exists_K_repr_orbit M ω hx
  rw [hx1]
  exact mem_domain_of_repr _ hsep hcyc hη hη'

/-- **RvD Appendix Prop. (3)** on `M ω`: `J Δ_ω^{1/2} (x ω) = x* ω`.  This is the statement
`S_ω = J Δ_ω^{1/2}`, with `S_ω` never named. -/
theorem J_D_orbit {x : ℋ →L[ℂ] ℋ} (hx : x ∈ M)
    (h : x ω ∈ (mp (Ksub M ω) hsep hcyc).D.domain) :
    J (Ksub M ω) ((mp (Ksub M ω) hsep hcyc).D ⟨x ω, h⟩) = (star x) ω := by
  obtain ⟨η, hη, η', hη', hx1, hx2⟩ := exists_K_repr_orbit M ω hx
  have h' : η + I • η' ∈ (mp (Ksub M ω) hsep hcyc).D.domain :=
    mem_domain_of_repr _ hsep hcyc hη hη'
  have heq : (mp (Ksub M ω) hsep hcyc).D ⟨x ω, h⟩
      = (mp (Ksub M ω) hsep hcyc).D ⟨η + I • η', h'⟩ := by
    congr 1
    exact Subtype.ext hx1
  rw [heq, J_D_apply _ hsep hcyc hη hη' h', hx2]

/-- **`M ω` is a core for `Δ_ω^{1/2}`.**  The graph of `Δ_ω^{1/2}` is the image of `𝒦 × 𝒦`
under the continuous real-linear map `Λ (η, η') = (η + iη', J (η - iη'))`, and the image of
`M_sa ω × M_sa ω` already lies in the graph of the restriction to `M ω`; since `M_sa ω` is
dense in `𝒦`, the restriction has the whole graph in its closure. -/
theorem orbit_hasCore : (mp (Ksub M ω) hsep hcyc).D.HasCore (orbitSub M ω) := by
  set K := Ksub M ω with hK
  set D := (mp K hsep hcyc).D with hD
  set S := orbitSub M ω with hS
  have hSle : S ≤ D.domain := by
    rintro _ ⟨x, hx, rfl⟩
    exact orbit_mem_domain M ω hsep hcyc hx
  refine ⟨hSle, ?_⟩
  have hres_le : D.domRestrict S ≤ D := LinearPMap.domRestrict_le
  have hDclosed : D.IsClosed := (mp K hsep hcyc).isClosed
  have hcl : (D.domRestrict S).IsClosable := hDclosed.isClosable.leIsClosable hres_le
  refine LinearPMap.eq_of_eq_graph ?_
  rw [← hcl.graph_closure_eq_closure_graph]
  refine SetLike.ext' ?_
  rw [Submodule.topologicalClosure_coe]
  set Λ : ℋ × ℋ → ℋ × ℋ := fun p => (p.1 + I • p.2, J K (p.1 - I • p.2)) with hΛ
  have hΛcont : Continuous Λ := by fun_prop
  set S₀ : Set ℋ := (saOrbit M ω : Set ℋ) with hS₀
  have hKcl : (K : Set ℋ) = closure S₀ := Submodule.topologicalClosure_coe _
  -- `Λ` sends `M_sa ω × M_sa ω` into the graph of the restriction
  have hstep : Λ '' (S₀ ×ˢ S₀) ⊆ ((D.domRestrict S).graph : Set (ℋ × ℋ)) := by
    rintro _ ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    obtain ⟨h, hh, hhs, rfl⟩ := hu
    obtain ⟨k, hk, hks, rfl⟩ := hv
    have hz : h + I • k ∈ M := add_mem hh (SMulMemClass.smul_mem _ hk)
    have hzω : (h + I • k) ω = h ω + I • (k ω) := by rw [add_apply, smul_apply]
    have hmemD : (h + I • k) ω ∈ D.domain := orbit_mem_domain M ω hsep hcyc hz
    have hmemS : (h + I • k) ω ∈ S := ⟨h + I • k, hz, rfl⟩
    have hJD := J_D_orbit M ω hsep hcyc hz hmemD
    have hstar : star (h + I • k) ω = h ω - I • (k ω) := by
      rw [star_add, star_smul, hhs.star_eq, hks.star_eq, Complex.star_def, Complex.conj_I,
        add_apply, smul_apply, neg_smul, ← sub_eq_add_neg]
    have hDval : D ⟨(h + I • k) ω, hmemD⟩ = J K (h ω - I • (k ω)) := by
      rw [← hstar, ← hJD, J_J K hsep hcyc]
    refine (LinearPMap.mem_graph_iff' _).2 ⟨⟨(h + I • k) ω, ⟨hmemS, hmemD⟩⟩, ?_⟩
    have hval : (D.domRestrict S) ⟨(h + I • k) ω, ⟨hmemS, hmemD⟩⟩ = D ⟨(h + I • k) ω, hmemD⟩ :=
      LinearPMap.domRestrict_apply rfl
    rw [Prod.ext_iff]
    refine ⟨hzω, ?_⟩
    rw [hval, hDval]
  -- the graph of `D` is contained in `Λ '' (𝒦 × 𝒦)`
  have hgraphD : (D.graph : Set (ℋ × ℋ)) ⊆ Λ '' ((K : Set ℋ) ×ˢ (K : Set ℋ)) := by
    rintro ⟨ζ, y⟩ hxy
    obtain ⟨z, hz⟩ := (LinearPMap.mem_graph_iff' D).1 hxy
    obtain ⟨η, hη, η', hη', hrepr⟩ := exists_mem_K_repr K hsep hcyc z.2
    have h' : η + I • η' ∈ D.domain := mem_domain_of_repr K hsep hcyc hη hη'
    have hzeq : z = ⟨η + I • η', h'⟩ := Subtype.ext hrepr
    have hJz : J K (D z) = η - I • η' := by
      rw [hzeq]; exact J_D_apply K hsep hcyc hη hη' h'
    refine ⟨(η, η'), ⟨hη, hη'⟩, ?_⟩
    have h1 : (z : ℋ) = η + I • η' := hrepr
    have h2 : D z = J K (η - I • η') := by rw [← hJz, J_J K hsep hcyc]
    rw [← hz, hΛ]
    exact Prod.ext h1.symm h2.symm
  refine Set.Subset.antisymm ?_ ?_
  · calc closure ((D.domRestrict S).graph : Set (ℋ × ℋ))
        ⊆ closure (D.graph : Set (ℋ × ℋ)) :=
          closure_mono (LinearPMap.le_graph_of_le hres_le)
      _ = _ := hDclosed.closure_eq
  · intro q hq
    have h1 : q ∈ Λ '' ((K : Set ℋ) ×ˢ (K : Set ℋ)) := hgraphD hq
    rw [hKcl, ← closure_prod_eq] at h1
    have h2 : Λ '' (closure (S₀ ×ˢ S₀)) ⊆ closure (Λ '' (S₀ ×ˢ S₀)) :=
      image_closure_subset_closure_image hΛcont
    exact closure_mono hstep (h2 h1)

end Tomita

/-! ## Part IV: the package

The three hypotheses `ω` cyclic, `ω` separating and `M'' = M` in one place. -/

section Package

variable (hcycv : IsCyclicVector M ω) (hsepv : IsSeparatingVector M ω)
  (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
    = (M : Set (ℋ →L[ℂ] ℋ)))

include hcycv hsepv hM

private lemma pkg_sep : Ksub M ω ⊓ (Ksub M ω).mulI = ⊥ := (isStandard M ω hcycv hsepv hM).1

private lemma pkg_cyc : Ksub M ω ⊔ (Ksub M ω).mulI = ⊤ := (isStandard M ω hcycv hsepv hM).2

/-- The modular operator `Δ_ω^{1/2}` of a von Neumann algebra with a cyclic and separating
vector: Rieffel–van Daele's `b a⁻¹` for the standard subspace `𝒦 = closure (M_sa ω)`. -/
noncomputable def modularSqrt : ℋ →ₗ.[ℂ] ℋ :=
  (mp (Ksub M ω) (pkg_sep M ω hcycv hsepv hM) (pkg_cyc M ω hcycv hsepv hM)).D

/-- The Tomita conjugation `J_ω`: a conjugate-linear isometric involution of `ℋ`. -/
noncomputable def modularConj : ℋ ≃ₗᵢ⋆[ℂ] ℋ :=
  Jequiv (Ksub M ω) (pkg_sep M ω hcycv hsepv hM) (pkg_cyc M ω hcycv hsepv hM)

@[simp] lemma modularConj_apply (x : ℋ) :
    modularConj M ω hcycv hsepv hM x = J (Ksub M ω) x := rfl

/-- `Δ_ω^{1/2}` is positive, injective and self-adjoint with dense range. -/
theorem modularSqrt_isSelfAdjoint : IsSelfAdjoint (modularSqrt M ω hcycv hsepv hM) :=
  IsModularPair.isSelfAdjoint _

theorem modularSqrt_inner_nonneg (x : (modularSqrt M ω hcycv hsepv hM).domain) :
    0 ≤ ⟪modularSqrt M ω hcycv hsepv hM x, (x : ℋ)⟫ :=
  IsModularPair.inner_nonneg _ x

/-- **`M ω` is a core for `Δ_ω^{1/2}`.** -/
theorem modularSqrt_hasCore :
    (modularSqrt M ω hcycv hsepv hM).HasCore (orbitSub M ω) :=
  orbit_hasCore M ω (pkg_sep M ω hcycv hsepv hM) (pkg_cyc M ω hcycv hsepv hM)

/-- **`S_ω = J_ω Δ_ω^{1/2}`** on `M ω`: `J_ω (Δ_ω^{1/2} (x ω)) = x* ω`. -/
theorem modularConj_modularSqrt_orbit {x : ℋ →L[ℂ] ℋ} (hx : x ∈ M)
    (h : x ω ∈ (modularSqrt M ω hcycv hsepv hM).domain) :
    modularConj M ω hcycv hsepv hM (modularSqrt M ω hcycv hsepv hM ⟨x ω, h⟩) = (star x) ω :=
  J_D_orbit M ω (pkg_sep M ω hcycv hsepv hM) (pkg_cyc M ω hcycv hsepv hM) hx h

/-- `x ω ∈ dom Δ_ω^{1/2}` for every `x ∈ M`. -/
theorem orbit_mem_modularSqrt_domain {x : ℋ →L[ℂ] ℋ} (hx : x ∈ M) :
    x ω ∈ (modularSqrt M ω hcycv hsepv hM).domain :=
  orbit_mem_domain M ω (pkg_sep M ω hcycv hsepv hM) (pkg_cyc M ω hcycv hsepv hM) hx

/-- **`dom Δ_ω^{1/2} = 𝒦 + i𝒦`**, one inclusion. -/
theorem exists_Ksub_repr {ζ : ℋ} (hζ : ζ ∈ (modularSqrt M ω hcycv hsepv hM).domain) :
    ∃ η ∈ Ksub M ω, ∃ η' ∈ Ksub M ω, ζ = η + I • η' :=
  exists_mem_K_repr (Ksub M ω) (pkg_sep M ω hcycv hsepv hM) (pkg_cyc M ω hcycv hsepv hM) hζ

/-- **`dom Δ_ω^{1/2} = 𝒦 + i𝒦`**, the other inclusion. -/
theorem mem_modularSqrt_domain {η η' : ℋ} (hη : η ∈ Ksub M ω) (hη' : η' ∈ Ksub M ω) :
    η + I • η' ∈ (modularSqrt M ω hcycv hsepv hM).domain :=
  mem_domain_of_repr (Ksub M ω) (pkg_sep M ω hcycv hsepv hM) (pkg_cyc M ω hcycv hsepv hM) hη hη'

/-- **`S_ω = J_ω Δ_ω^{1/2}`** in full: on `dom Δ_ω^{1/2} = 𝒦 + i𝒦`, `J_ω Δ_ω^{1/2}` sends
`η + iη'` to `η - iη'`. -/
theorem modularConj_modularSqrt {η η' : ℋ} (hη : η ∈ Ksub M ω) (hη' : η' ∈ Ksub M ω)
    (h : η + I • η' ∈ (modularSqrt M ω hcycv hsepv hM).domain) :
    modularConj M ω hcycv hsepv hM (modularSqrt M ω hcycv hsepv hM ⟨η + I • η', h⟩)
      = η - I • η' :=
  J_D_apply (Ksub M ω) (pkg_sep M ω hcycv hsepv hM) (pkg_cyc M ω hcycv hsepv hM) hη hη' h

end Package

end BH

end Theses.RvD
