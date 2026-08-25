/-
**Rieffel–van Daele, §4, Lemmas 4.5 and 4.6.**

  M. A. Rieffel and A. van Daele, *A bounded operator approach to
  Tomita–Takesaki theory*, Pacific J. Math. **69** (1977) 187–221,
  pp. 202–204.

**This file has no thesis counterpart.**  It continues `Theses/A/VN/TomitaTakesaki.lean`
(RvD Lemma 4.3, Corollary 4.4, Lemma 4.9 and Theorem 4.2(1)) towards the commutation
theorem; see `docs/COMMUTATION-THEOREM.md`.

## Part I — RvD Lemma 4.5

`lemma_4_5`: for `x' ∈ M'` and any `λ` with `Re λ > 0` there is an `x ∈ M` with

  `T (J x' J) T = λ (2 − R) x R + λ̄ R x (2 − R)`.

This is pure algebra on top of `cor_4_4`; no `Δ^{it}` and no functional calculus beyond what
`StandardSubspace.lean` already builds.  The chain is RvD's:

* `T_J` : `T J = J T = A = P − Q` (the two commute, being equal on the dense `ran T`).
* `A_orbit`, `A_commutant_orbit` : RvD's `T J u ω = (2 − R) u^* ω` for `u ∈ M` and
  `T J u' ω = R u'^* ω` for `u' ∈ M'` — `P u ω = u ω` resp. `Q u' ω = 0`, extended off the
  self-adjoint part by conjugate linearity of `A`.
* `lemma_4_3_bilin` : Lemma 4.3 in the form `⟪y ω, x' ω⟫ = λ ⟪y ω, x ω⟫ + λ̄ ⟪x ω, y ω⟫`,
  obtained from `lemma_4_3` at `λ / Re λ` and halved (RvD's "with `x` replaced by `x/2`").
* `lemma_4_3_two` : the same after replacing `y` by `z^* y`, RvD's equation on p. 203.
* `lemma_4_5_sa`, `lemma_4_5` : substituting `y ω = J T y' ω`, `z ω = J T z' ω` from
  Corollary 4.4 and using `⟪J ξ, η⟫ = ⟪J η, ξ⟫` (RvD Prop. 3.1), then cyclicity of `ω` for
  `M'` twice.

The hypothesis `hM'dense` — `M' ω` dense, i.e. `ω` cyclic for `M'` — is
`Tomita.dense_commutant_orbit M ω hsepv hM`.

*A note on conventions.*  Mathlib's inner product is conjugate linear in the **first**
variable, Rieffel–van Daele's in the second, so `lemma_4_3` transcribed here is RvD's Lemma
4.3 with `λ` replaced by `λ̄`.  The statement of `lemma_4_5` is unaffected: it quantifies over
all `λ` with `Re λ > 0`, a set stable under conjugation, and the proof feeds `λ̄` to
`lemma_4_3_two`.

## Part II — RvD Lemma 4.6

`lemma_4_6`: for `λ = e^{iφ/2}` with `|φ| < π`, and `f` bounded and continuous on the closed
strip `|Re z| ≤ 1/2` and holomorphic inside it,

  `f 0 = ∫ e^{−φt} (e^{πt} + e^{−πt})⁻¹ (λ f (it + 1/2) + λ̄ f (it − 1/2)) dt`.

This is Haagerup's simplification of RvD's argument, and it is the analytic heart of §4.  The
proof is the one RvD sketch, made rectangular because Mathlib's Cauchy–Goursat theorem is for
rectangles:

* `sinq` : `z ↦ sin (π z)/z`, extended by `π` at `0` — as `dslope` of `z ↦ sin (π z)` it is
  entire, and it is nonvanishing on `|Re z| < 1`.  `stripNum φ f = π e^{iφz} f / sinq` is then
  RvD's `z g(z)` with the pole already removed: it is continuous on the closed strip,
  holomorphic inside, and equal to `f 0` at `0`.
* `bdry T h` : the integral of `h` over `∂([−1/2,1/2] × [−T,T])`, in the shape
  `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` produces.
  `bdry_eq_zero` is that theorem, applied to `dslope (stripNum φ f) 0`; by
  `Complex.differentiableOn_dslope` no exceptional set is needed at all.
* `bdry_inv` : `∮ dz/z = 2 π i`, by the fundamental theorem of calculus with the
  antiderivative `t ↦ ½ log (t² + c²) − i arctan (t/c)` on each side, and
  `Real.arctan_inv_of_pos` to add the four arctangents to `2π`.
* `bdry_stripG` : `∮ g = 2 π i f 0` for **every** `T > 0`, since
  `dslope (stripNum φ f) 0 = g − f 0 · (·)⁻¹` off `0`.
* `tendsto_hor`, `tendsto_ver` : `‖sin w‖ ≥ sinh |Im w|` makes the two horizontal sides
  `O(e^{(|φ|−π)T})`, and `1/cosh(πy) ≤ 2 e^{−π|y|}` makes the vertical integrands dominated
  by `e^{−(π−|φ|)|y|}`, hence integrable on `ℝ`; `intervalIntegral_tendsto_integral` then
  identifies the limit.
* `strip_contour_limit`, `lemma_4_6` : uniqueness of limits, then `sin (π(±½ + iy)) = ±cosh πy`
  and `e^{iφ(±½+iy)} = λ^{±1} e^{−φy}` turn the difference of the two vertical integrands into
  RvD's integrand.

**Not needed for either lemma: `Δ^{it}`.**  Lemma 4.7 is where it enters.
-/
import Theses.A.VN.TomitaTakesaki

set_option linter.unusedSectionVars false

open Complex ClosedSubmodule Theses.A.VN
open scoped ComplexInnerProductSpace ComplexOrder

namespace Theses.RvD

/-! ## Part I: RvD Lemma 4.5 -/

section TJ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (K : ClosedSubmodule ℝ H)
variable (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤)

include hsep hcyc

/-- `T J = A`: `J T = A` is the defining property of `J`, and `T` commutes with `A`, hence
(on the dense range of `T`, hence everywhere) with `J`. -/
lemma T_J (x : H) : T K (J K x) = A K x := by
  have hcont1 : Continuous fun x : H => T K (J K x) := (T K).continuous.comp (J K).continuous
  have hcont2 : Continuous fun x : H => A K x := (A K).continuous
  have heq : Set.EqOn (fun x : H => T K (J K x)) (fun x : H => A K x) (Set.range (T K)) := by
    rintro _ ⟨u, rfl⟩
    show T K (J K (T K u)) = A K (T K u)
    rw [J_T K hsep hcyc, A_comm_T]
  exact congrFun (hcont1.ext_on (T_denseRange K hsep hcyc) hcont2 heq) x

end TJ

section Lemma45

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (ω : ℋ)

/-- `A (u ω) = (2 − R) (u* ω)` for `u ∈ M`, RvD's `T J u ω = (2 − R) u* ω`.  For
self-adjoint `u` this is `P (u ω) = u ω`; the general case is conjugate linearity of `A`. -/
lemma A_orbit {u : ℋ →L[ℂ] ℋ} (hu : u ∈ M) :
    A (Ksub M ω) (u ω) = ((2 : ℋ →L[ℂ] ℋ) - R (Ksub M ω)) ((star u) ω) := by
  have sa : ∀ v ∈ M, IsSelfAdjoint v →
      A (Ksub M ω) (v ω) = ((2 : ℋ →L[ℂ] ℋ) - R (Ksub M ω)) (v ω) := by
    intro v hv hvs
    have hP : P (Ksub M ω) (v ω) = v ω := P_eq_self (mem_Ksub_of_sa M ω hv hvs)
    rw [A_apply, two_sub_R_apply, hP, sub_self, zero_add]
  obtain ⟨h, hh, k, hk, hhs, hks, rfl⟩ := exists_sa_decomp M u hu
  have hap : (h + (I : ℂ) • k) ω = h ω + (I : ℂ) • (k ω) := by
    rw [add_apply, smul_apply]
  have hstar : star (h + (I : ℂ) • k) = h - (I : ℂ) • k := by
    rw [star_add, star_smul, hhs.star_eq, hks.star_eq, Complex.star_def, Complex.conj_I,
      neg_smul, ← sub_eq_add_neg]
  have hap2 : (h - (I : ℂ) • k) ω = h ω - (I : ℂ) • (k ω) := by
    rw [sub_apply, smul_apply]
  rw [hap, hstar, hap2, map_add, A_smul_I, sa h hh hhs, sa k hk hks, map_sub, map_smul]
  abel

/-- `A (u' ω) = R (u'* ω)` for `u' ∈ M'`, RvD's `T J u' ω = R u'* ω`.  For self-adjoint `u'`
this is `Q (u' ω) = 0`. -/
lemma A_commutant_orbit {u : ℋ →L[ℂ] ℋ} (hu : u ∈ commutantSA M) :
    A (Ksub M ω) (u ω) = R (Ksub M ω) ((star u) ω) := by
  have sa : ∀ v ∈ commutantSA M, IsSelfAdjoint v →
      A (Ksub M ω) (v ω) = R (Ksub M ω) (v ω) := by
    intro v hv hvs
    rw [A_apply, R_apply, Q_commutant_orbit M ω hv hvs, sub_zero, add_zero]
  obtain ⟨h, hh, k, hk, hhs, hks, rfl⟩ := exists_sa_decomp (commutantSA M) u hu
  have hap : (h + (I : ℂ) • k) ω = h ω + (I : ℂ) • (k ω) := by
    rw [add_apply, smul_apply]
  have hstar : star (h + (I : ℂ) • k) = h - (I : ℂ) • k := by
    rw [star_add, star_smul, hhs.star_eq, hks.star_eq, Complex.star_def, Complex.conj_I,
      neg_smul, ← sub_eq_add_neg]
  have hap2 : (h - (I : ℂ) • k) ω = h ω - (I : ℂ) • (k ω) := by
    rw [sub_apply, smul_apply]
  rw [hap, hstar, hap2, map_add, A_smul_I, sa h hh hhs, sa k hk hks, map_sub, map_smul]
  abel

/-- **RvD Lemma 4.3**, in the bilinear form the next lemma consumes.  For self-adjoint
`x' ∈ M'` and `Re λ > 0` there is a self-adjoint `x ∈ M` with

  `⟪y ω, x' ω⟫ = λ ⟪y ω, x ω⟫ + λ̄ ⟪x ω, y ω⟫`   for all self-adjoint `y ∈ M`.

`lemma_4_3` is applied with `λ / Re λ`, whose real part is `1`, and `x` is `1 / (2 Re λ)`
times the operator it returns — RvD's "Lemma 4.3 with `x` replaced by `x/2`". -/
theorem lemma_4_3_bilin
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    {x' : ℋ →L[ℂ] ℋ} (hx'M : x' ∈ commutantSA M) (hx's : IsSelfAdjoint x')
    {lam : ℂ} (hlam : 0 < lam.re) :
    ∃ x ∈ M, IsSelfAdjoint x ∧ ∀ y ∈ M, IsSelfAdjoint y →
      (⟪y ω, x' ω⟫ : ℂ)
        = lam * ⟪y ω, x ω⟫ + (starRingEnd ℂ) lam * ⟪x ω, y ω⟫ := by
  have hsm : ∀ (c : ℝ) (X : ℋ →L[ℂ] ℋ), (c : ℝ) • X = ((c : ℂ)) • X := by
    intro c X; rw [← Complex.coe_algebraMap, algebraMap_smul]
  have hsmv : ∀ (c : ℝ) (u : ℋ), (c : ℝ) • u = ((c : ℂ)) • u := by
    intro c u; rw [← Complex.coe_algebraMap, algebraMap_smul]
  set r : ℝ := lam.re with hr
  have hrpos : 0 < r := hlam
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hmu : ((r : ℂ)⁻¹ * lam).re = 1 := by
    rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, ← hr]
    field_simp
  obtain ⟨y₀, hy₀M, hy₀s, hproj⟩ := lemma_4_3 M ω hM hx'M hx's (lam := (r : ℂ)⁻¹ * lam) hmu
  refine ⟨((2 * r)⁻¹ : ℝ) • y₀, ?_, ?_, ?_⟩
  · rw [hsm]; exact SMulMemClass.smul_mem _ hy₀M
  · rw [IsSelfAdjoint, star_smul, hy₀s.star_eq]; simp
  · intro y hy hys
    have hyK : y ω ∈ Ksub M ω := mem_Ksub_of_sa M ω hy hys
    -- the two real inner products agree, by `P`
    have hreal : inner ℝ (x' ω) (y ω)
        = inner ℝ (((r : ℂ)⁻¹ * lam) • (y₀ ω)) (y ω) := by
      have e1 : ∀ v : ℋ, inner ℝ v (y ω) = inner ℝ (P (Ksub M ω) v) (y ω) := by
        intro v; rw [P_symm, P_eq_self hyK]
      rw [e1 (x' ω), e1 (((r : ℂ)⁻¹ * lam) • (y₀ ω)), hproj]
    set v : ℂ := ⟪y ω, y₀ ω⟫ with hv
    have hconj : (⟪y₀ ω, y ω⟫ : ℂ) = (starRingEnd ℂ) v := (inner_conj_symm _ _).symm
    -- the real part of `⟪y ω, x' ω⟫`
    have hre : (⟪y ω, x' ω⟫ : ℂ).re = (((r : ℂ)⁻¹ * lam) * v).re := by
      have h1 : inner ℝ (x' ω) (y ω) = (⟪y ω, x' ω⟫ : ℂ).re := by
        rw [real_inner_comm, inner_real_eq_re_inner]
      have h2 : inner ℝ (((r : ℂ)⁻¹ * lam) • (y₀ ω)) (y ω)
          = (((r : ℂ)⁻¹ * lam) * v).re := by
        rw [inner_real_eq_re_inner, inner_smul_left, hconj, ← map_mul, Complex.conj_re]
      rw [← h1, hreal, h2]
    -- and `⟪y ω, x' ω⟫` is real
    have him : (⟪y ω, x' ω⟫ : ℂ).im = 0 := by
      have hc : Commute y x' := mem_commutantSA.1 hx'M y hy
      have hyx : IsSelfAdjoint (y * x') := by
        show star (y * x') = y * x'
        rw [star_mul, hx's.star_eq, hys.star_eq]
        exact hc.symm.eq
      have e1 : (⟪y ω, x' ω⟫ : ℂ) = ⟪ω, (y * x') ω⟫ := by
        have e := inner_apply_left y ω (x' ω)
        rw [hys.star_eq] at e
        exact e
      have h1 := inner_apply_left (y * x') ω ω
      rw [hyx.star_eq] at h1
      have h2 := inner_conj_symm (𝕜 := ℂ) ((y * x') ω) ω
      rw [h1] at h2
      have h3 := congrArg Complex.im h2
      simp only [Complex.conj_im] at h3
      rw [e1]
      linarith
    have hlhs : (⟪y ω, x' ω⟫ : ℂ) = ((((r : ℂ)⁻¹ * lam) * v).re : ℂ) := by
      apply Complex.ext <;> simp [hre, him]
    have hcsmul : ((((2 * r)⁻¹ : ℝ) • y₀ : ℋ →L[ℂ] ℋ)) ω
        = ((((2 * r)⁻¹ : ℝ) : ℂ)) • (y₀ ω) := by
      rw [hsm, smul_apply]
    rw [hlhs, hcsmul, inner_smul_right, inner_smul_left, hconj, ← hv,
      Complex.conj_ofReal]
    -- pure algebra in `ℂ` from here on
    have hsum : lam * ((((2 * r)⁻¹ : ℝ) : ℂ) * v)
        + (starRingEnd ℂ) lam * ((((2 * r)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) v)
        = ((((2 * r)⁻¹ : ℝ) : ℂ)) * (lam * v + (starRingEnd ℂ) (lam * v)) := by
      rw [map_mul]; ring
    have hrneC : (r : ℂ) ≠ 0 := by exact_mod_cast hrne
    rw [hsum, Complex.add_conj, ← Complex.ofReal_inv, mul_assoc, Complex.re_ofReal_mul]
    push_cast
    field_simp

/-- **RvD Lemma 4.3**, in the two-variable form used in the proof of Lemma 4.5: RvD's
`⟨y ω, x' z ω⟩ = λ ⟨y ω, z x ω⟩ + λ̄ ⟨y x ω, z ω⟩`.  Two extensions of `lemma_4_3_bilin`:
first from self-adjoint `y ∈ M` to arbitrary `y ∈ M` (all three terms are conjugate linear
in `y`, once the third `y` is changed to `y*`), then substituting `z* y` for `y`. -/
theorem lemma_4_3_two
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    {x' : ℋ →L[ℂ] ℋ} (hx'M : x' ∈ commutantSA M) (hx's : IsSelfAdjoint x')
    {lam : ℂ} (hlam : 0 < lam.re) :
    ∃ x ∈ M, IsSelfAdjoint x ∧ ∀ y ∈ M, ∀ z ∈ M,
      (⟪y ω, x' (z ω)⟫ : ℂ)
        = lam * ⟪y ω, (z * x) ω⟫ + (starRingEnd ℂ) lam * ⟪(y * x) ω, z ω⟫ := by
  obtain ⟨x, hxM, hxs, hbil⟩ := lemma_4_3_bilin M ω hM hx'M hx's hlam
  refine ⟨x, hxM, hxs, ?_⟩
  -- first, arbitrary `y ∈ M`, with the third `y` replaced by `y*`
  have step1 : ∀ y ∈ M, (⟪y ω, x' ω⟫ : ℂ)
      = lam * ⟪y ω, x ω⟫ + (starRingEnd ℂ) lam * ⟪x ω, (star y) ω⟫ := by
    intro y hy
    obtain ⟨h, hh, k, hk, hhs, hks, rfl⟩ := exists_sa_decomp M y hy
    have hap : (h + (I : ℂ) • k) ω = h ω + (I : ℂ) • (k ω) := by rw [add_apply, smul_apply]
    have hstar : star (h + (I : ℂ) • k) = h - (I : ℂ) • k := by
      rw [star_add, star_smul, hhs.star_eq, hks.star_eq, Complex.star_def, Complex.conj_I,
        neg_smul, ← sub_eq_add_neg]
    have hap2 : (h - (I : ℂ) • k) ω = h ω - (I : ℂ) • (k ω) := by rw [sub_apply, smul_apply]
    rw [hap, hstar, hap2, inner_add_left, inner_add_left, inner_sub_right, inner_smul_left,
      inner_smul_left, inner_smul_right, hbil h hh hhs, hbil k hk hks, Complex.conj_I]
    ring
  intro y hy z hz
  have hzy : star z * y ∈ M := mul_mem (star_mem hz) hy
  have h := step1 (star z * y) hzy
  have e0 : (star z * y) ω = (star z) (y ω) := by rw [mul_apply_eq_comp]
  have e1 : (⟪(star z) (y ω), x' ω⟫ : ℂ) = ⟪y ω, x' (z ω)⟫ := by
    rw [inner_star_left]
    have hc : Commute z x' := (mem_commutantSA.1 hx'M z hz)
    have : z (x' ω) = x' (z ω) := by
      have := congrArg (fun (X : ℋ →L[ℂ] ℋ) => X ω) hc
      simpa [mul_apply_eq_comp] using this
    rw [this]
  have e2 : (⟪(star z) (y ω), x ω⟫ : ℂ) = ⟪y ω, (z * x) ω⟫ := by
    rw [inner_star_left, mul_apply_eq_comp]
  have e3 : star (star z * y) = star y * z := by rw [star_mul, star_star]
  have e4 : (⟪x ω, (star y * z) ω⟫ : ℂ) = ⟪(y * x) ω, z ω⟫ := by
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      ← inner_apply_left y (x ω) (z ω)]
  rw [e0, e1, e2, e3, e4] at h
  exact h

section Five

variable (hsep : Ksub M ω ⊓ (Ksub M ω).mulI = ⊥) (hcyc : Ksub M ω ⊔ (Ksub M ω).mulI = ⊤)

include hsep hcyc

/-- The composite form of `A_orbit` used twice in Lemma 4.5: if `u ∈ M` and `u' ∈ M'` are
related by Corollary 4.4 (`J T u'^* ω = u^* ω`) and `x ∈ M` is self-adjoint, then
`T J (u x) ω = (2 − R) x R u' ω`. -/
lemma A_orbit_mul {x : ℋ →L[ℂ] ℋ} (hxM : x ∈ M) (hxs : IsSelfAdjoint x)
    {u : ℋ →L[ℂ] ℋ} (huM : u ∈ M) {u' : ℋ →L[ℂ] ℋ} (hu'M : u' ∈ commutantSA M)
    (hu : J (Ksub M ω) (T (Ksub M ω) ((star u') ω)) = (star u) ω) :
    A (Ksub M ω) ((u * x) ω)
      = (((2 : ℋ →L[ℂ] ℋ) - R (Ksub M ω)) * x * R (Ksub M ω)) (u' ω) := by
  have hux : u * x ∈ M := mul_mem huM hxM
  have hstar : star (u * x) = x * star u := by rw [star_mul, hxs.star_eq]
  have h1 : A (Ksub M ω) ((u * x) ω)
      = ((2 : ℋ →L[ℂ] ℋ) - R (Ksub M ω)) (x ((star u) ω)) := by
    rw [A_orbit M ω hux, hstar, mul_apply_eq_comp]
  have h2 : (star u) ω = R (Ksub M ω) (u' ω) := by
    rw [← hu, ← A_eq_J_T (Ksub M ω) hsep hcyc,
      A_commutant_orbit M ω (star_mem hu'M), star_star]
  rw [h1, h2, mul_apply_eq_comp, mul_apply_eq_comp]

/-- **RvD Lemma 4.5** for self-adjoint `x' ∈ M'`. -/
theorem lemma_4_5_sa
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    (hM'dense : Dense {y : ℋ | ∃ u ∈ commutantSA M, y = u ω})
    {x' : ℋ →L[ℂ] ℋ} (hx'M : x' ∈ commutantSA M) (hx's : IsSelfAdjoint x')
    {lam : ℂ} (hlam : 0 < lam.re) :
    ∃ x ∈ M, IsSelfAdjoint x ∧
      T (Ksub M ω) * vnAdJ M ω hsep hcyc x' * T (Ksub M ω)
        = lam • (((2 : ℋ →L[ℂ] ℋ) - R (Ksub M ω)) * x * R (Ksub M ω))
          + (starRingEnd ℂ) lam • (R (Ksub M ω) * x * ((2 : ℋ →L[ℂ] ℋ) - R (Ksub M ω))) := by
  have hlam' : 0 < ((starRingEnd ℂ) lam).re := by simpa using hlam
  obtain ⟨x, hxM, hxs, hkey⟩ := lemma_4_3_two M ω hM hx'M hx's hlam'
  refine ⟨x, hxM, hxs, ?_⟩
  set K := Ksub M ω with hK
  set B₁ : ℋ →L[ℂ] ℋ := ((2 : ℋ →L[ℂ] ℋ) - R K) * x * R K with hB₁
  set B₂ : ℋ →L[ℂ] ℋ := R K * x * ((2 : ℋ →L[ℂ] ℋ) - R K) with hB₂
  have hB₂star : star B₁ = B₂ := by
    have hRsa : star (R K) = R K := (R_isSelfAdjoint K).star_eq
    have h2sa : star ((2 : ℋ →L[ℂ] ℋ) - R K) = (2 : ℋ →L[ℂ] ℋ) - R K := by
      rw [star_sub, hRsa]; norm_num
    rw [hB₁, hB₂, star_mul, star_mul, hRsa, h2sa, hxs.star_eq, mul_assoc]
  -- the symmetry of `T`
  have hTsa : ∀ u v : ℋ, (⟪T K u, v⟫ : ℂ) = ⟪u, T K v⟫ := by
    intro u v
    have := inner_apply_left (T K) u v
    rwa [(T_isSelfAdjoint K).star_eq] at this
  -- `⟪p, J q⟫ = ⟪q, J p⟫`
  have hswap2 : ∀ p q : ℋ, (⟪p, J K q⟫ : ℂ) = ⟪q, J K p⟫ := by
    intro p q
    have h := J_inner_swap K hsep hcyc q p
    have h1 := congrArg (starRingEnd ℂ) h
    rwa [inner_conj_symm, inner_conj_symm] at h1
  -- the operator identity, tested against `M' ω × M' ω`
  set Φ : ℋ →L[ℂ] ℋ := T K * vnAdJ M ω hsep hcyc x' * T K
    - (lam • B₁ + (starRingEnd ℂ) lam • B₂) with hΦ
  have hmain : ∀ z' ∈ commutantSA M, ∀ y' ∈ commutantSA M, (⟪Φ (z' ω), y' ω⟫ : ℂ) = 0 := by
    intro z' hz' y' hy'
    obtain ⟨y, hyM, hy1, hy2⟩ := cor_4_4 M ω hsep hcyc hM hy'
    obtain ⟨z, hzM, hz1, hz2⟩ := cor_4_4 M ω hsep hcyc hM hz'
    have hbase := hkey y hyM z hzM
    -- (a) the left-hand side
    have ea : (⟪y ω, x' (z ω)⟫ : ℂ) = ⟪(T K * vnAdJ M ω hsep hcyc x' * T K) (z' ω), y' ω⟫ := by
      rw [← hy1, ← hz1, J_inner_swap K hsep hcyc]
      show (⟪J K (x' (J K (T K (z' ω)))), T K (y' ω)⟫ : ℂ) = _
      rw [← hTsa, mul_apply_eq_comp, mul_apply_eq_comp]
      rfl
    -- (b) the first term on the right
    have eb : (⟪y ω, (z * x) ω⟫ : ℂ) = ⟪B₁ (z' ω), y' ω⟫ := by
      rw [← hy1, J_inner_swap K hsep hcyc, ← hTsa, T_J K hsep hcyc,
        A_orbit_mul M ω hsep hcyc hxM hxs hzM hz' hz2]
    -- (c) the second term on the right
    have ec : (⟪(y * x) ω, z ω⟫ : ℂ) = ⟪B₂ (z' ω), y' ω⟫ := by
      rw [← hz1, hswap2, hTsa, T_J K hsep hcyc,
        A_orbit_mul M ω hsep hcyc hxM hxs hyM hy' hy2, ← hB₂star]
      have := inner_apply_left (star B₁) (z' ω) (y' ω)
      rw [star_star] at this
      exact this.symm
    rw [ea, eb, ec] at hbase
    rw [hΦ]
    show (⟪(T K * vnAdJ M ω hsep hcyc x' * T K) (z' ω) - (lam • B₁ + (starRingEnd ℂ) lam • B₂)
      (z' ω), y' ω⟫ : ℂ) = 0
    rw [inner_sub_left, hbase]
    show _ - (⟪lam • B₁ (z' ω) + (starRingEnd ℂ) lam • B₂ (z' ω), y' ω⟫ : ℂ) = 0
    rw [inner_add_left, inner_smul_left, inner_smul_left, Complex.conj_conj]
    ring
  -- density in the second variable, then in the first
  have hzero : ∀ z' ∈ commutantSA M, Φ (z' ω) = 0 := by
    intro z' hz'
    refine eq_of_inner_eq_on_dense hM'dense ?_
    rintro w ⟨u, hu, rfl⟩
    rw [inner_zero_right, ← inner_conj_symm]
    simp [hmain z' hz' u hu]
  have hall : ∀ v : ℋ, Φ v = 0 := by
    have heq : Set.EqOn (fun v : ℋ => Φ v) (fun _ : ℋ => (0 : ℋ))
        {y : ℋ | ∃ u ∈ commutantSA M, y = u ω} := by
      rintro _ ⟨u, hu, rfl⟩
      exact hzero u hu
    exact congrFun (Φ.continuous.ext_on hM'dense continuous_const heq)
  have : Φ = 0 := by ext v; exact hall v
  rwa [hΦ, sub_eq_zero] at this

/-- **RvD Lemma 4.5**: for every `x' ∈ M'` and every `λ` with `Re λ > 0` there is an `x ∈ M`
with `T J x' J T = λ (2 − R) x R + λ̄ R x (2 − R)`.  The self-adjoint case is
`lemma_4_5_sa`; the general one follows because `x' ↦ J x' J` is conjugate linear. -/
theorem lemma_4_5
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    (hM'dense : Dense {y : ℋ | ∃ u ∈ commutantSA M, y = u ω})
    {x' : ℋ →L[ℂ] ℋ} (hx'M : x' ∈ commutantSA M) {lam : ℂ} (hlam : 0 < lam.re) :
    ∃ x ∈ M,
      T (Ksub M ω) * vnAdJ M ω hsep hcyc x' * T (Ksub M ω)
        = lam • (((2 : ℋ →L[ℂ] ℋ) - R (Ksub M ω)) * x * R (Ksub M ω))
          + (starRingEnd ℂ) lam • (R (Ksub M ω) * x * ((2 : ℋ →L[ℂ] ℋ) - R (Ksub M ω))) := by
  obtain ⟨h', hh', k', hk', hh's, hk's, rfl⟩ := exists_sa_decomp (commutantSA M) x' hx'M
  obtain ⟨xh, hxhM, -, hxh⟩ := lemma_4_5_sa M ω hsep hcyc hM hM'dense hh' hh's hlam
  obtain ⟨xk, hxkM, -, hxk⟩ := lemma_4_5_sa M ω hsep hcyc hM hM'dense hk' hk's hlam
  refine ⟨xh - (I : ℂ) • xk, sub_mem hxhM (SMulMemClass.smul_mem _ hxkM), ?_⟩
  rw [vnAdJ_sa_decomp M ω hsep hcyc, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hxh, hxk]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul]
  module

end Five

end Lemma45

/-! ## Part II: RvD Lemma 4.6 -/

section Lemma46

open MeasureTheory intervalIntegral Filter Topology Set


open MeasureTheory intervalIntegral Filter Topology Set

/-- `z ↦ sin (π z) / z`, extended by its limit `π` at `0`: an entire function, nonvanishing
on the strip `|Re z| < 1`. -/
noncomputable def sinq : ℂ → ℂ := dslope (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z)) 0

lemma differentiable_sinq : Differentiable ℂ sinq := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2 (by fun_prop)

lemma sinq_zero : sinq 0 = (Real.pi : ℂ) := by
  have h : HasDerivAt (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z))
      (Complex.cos ((Real.pi : ℂ) * 0) * (Real.pi : ℂ)) 0 :=
    HasDerivAt.csin (by simpa using (hasDerivAt_id (0 : ℂ)).const_mul ((Real.pi : ℂ)))
  rw [sinq, dslope_same, h.deriv]
  simp

lemma sinq_of_ne {z : ℂ} (hz : z ≠ 0) : sinq z = Complex.sin ((Real.pi : ℂ) * z) / z := by
  rw [sinq, dslope_of_ne _ hz, slope_def_field]
  simp

lemma sin_pi_ne_zero {z : ℂ} (hz : z ≠ 0) (hre : |z.re| < 1) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  intro hs
  rw [Complex.sin_eq_zero_iff] at hs
  obtain ⟨k, hk⟩ := hs
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hzk : z = (k : ℂ) := by
    refine mul_left_cancel₀ hpi ?_
    rw [hk, mul_comm]
  have hk0 : k = 0 := by
    have : |((k : ℤ) : ℝ)| < 1 := by
      rw [hzk] at hre
      simpa using hre
    exact_mod_cast (Int.abs_lt_one_iff.1 (by exact_mod_cast this))
  rw [hk0] at hzk
  simp at hzk
  exact hz hzk

lemma sinq_ne_zero {z : ℂ} (hre : |z.re| < 1) : sinq z ≠ 0 := by
  rcases eq_or_ne z 0 with rfl | h
  · rw [sinq_zero]
    exact_mod_cast Real.pi_ne_zero
  · rw [sinq_of_ne h]
    exact div_ne_zero (sin_pi_ne_zero h hre) h

/-! ### The strip and the auxiliary functions -/

/-- The closed strip `|Re z| ≤ 1/2`. -/
def clStrip : Set ℂ := {z : ℂ | |z.re| ≤ 1 / 2}

/-- The open strip `|Re z| < 1/2`. -/
def opStrip : Set ℂ := {z : ℂ | |z.re| < 1 / 2}

@[simp] lemma mem_clStrip {z : ℂ} : z ∈ clStrip ↔ |z.re| ≤ 1 / 2 := Iff.rfl
@[simp] lemma mem_opStrip {z : ℂ} : z ∈ opStrip ↔ |z.re| < 1 / 2 := Iff.rfl

lemma isOpen_opStrip : IsOpen opStrip := by
  have : opStrip = Complex.re ⁻¹' (Set.Ioo (-(1/2 : ℝ)) (1/2)) := by
    ext z; simp [opStrip, abs_lt]
  rw [this]
  exact isOpen_Ioo.preimage Complex.continuous_re

lemma opStrip_subset_clStrip : opStrip ⊆ clStrip := fun _ hz => le_of_lt (mem_opStrip.1 hz)

lemma zero_mem_opStrip : (0 : ℂ) ∈ opStrip := by norm_num [opStrip]

/-- `F (z) = π z e^{iφz} f(z) / sin (π z)`, written with `sinq` so that the removable
singularity at `0` is already removed: `F 0 = f 0`. -/
noncomputable def stripNum (φ : ℝ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (Real.pi : ℂ) * Complex.exp (I * (φ : ℂ) * z) * f z / sinq z

/-- Haagerup's `g (z) = π e^{iφz} f (z) / sin (π z)`. -/
noncomputable def stripG (φ : ℝ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (Real.pi : ℂ) * Complex.exp (I * (φ : ℂ) * z) * f z / Complex.sin ((Real.pi : ℂ) * z)

lemma stripNum_zero (φ : ℝ) (f : ℂ → ℂ) : stripNum φ f 0 = f 0 := by
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [stripNum, sinq_zero]
  field_simp
  simp

lemma stripNum_eq {z : ℂ} (hz : z ≠ 0) (_hre : |z.re| < 1) (φ : ℝ) (f : ℂ → ℂ) :
    stripNum φ f z = z * stripG φ f z := by
  rw [stripNum, stripG, sinq_of_ne hz, div_div_eq_mul_div]
  field_simp

lemma continuousOn_stripNum {f : ℂ → ℂ} (hf : ContinuousOn f clStrip) (φ : ℝ) :
    ContinuousOn (stripNum φ f) clStrip := by
  refine ContinuousOn.div ?_ (differentiable_sinq.continuous.continuousOn) ?_
  · exact (continuousOn_const.mul (Continuous.continuousOn (by fun_prop))).mul hf
  · intro z hz
    refine sinq_ne_zero ?_
    have := mem_clStrip.1 hz
    linarith

lemma differentiableOn_stripNum {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f opStrip) (φ : ℝ) :
    DifferentiableOn ℂ (stripNum φ f) opStrip := by
  refine DifferentiableOn.div ?_ (differentiable_sinq.differentiableOn) ?_
  · exact (differentiableOn_const _ |>.mul (Differentiable.differentiableOn (by fun_prop))).mul hf
  · intro z hz
    refine sinq_ne_zero ?_
    have := mem_opStrip.1 hz
    linarith

/-! ### The contour -/

/-- The integral over the boundary of the rectangle `[-1/2, 1/2] × [-T, T]`, in the shape
Mathlib's Cauchy–Goursat theorem for rectangles produces. -/
noncomputable def bdry (T : ℝ) (h : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in (-(1/2) : ℝ)..(1/2 : ℝ), h ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
    - (∫ x : ℝ in (-(1/2) : ℝ)..(1/2 : ℝ), h ((x : ℂ) + ((T : ℝ) : ℂ) * I))
    + I * (∫ y : ℝ in (-T)..T, h (((1/2 : ℝ) : ℂ) + (y : ℂ) * I))
    - I * (∫ y : ℝ in (-T)..T, h (((-(1/2) : ℝ) : ℂ) + (y : ℂ) * I))

lemma memStrip_hor {c x : ℝ} (hc : c ≠ 0) (hx : |x| ≤ 1 / 2) :
    ((x : ℂ) + (c : ℂ) * I) ∈ clStrip \ {0} := by
  constructor
  · simpa using hx
  · simp only [Set.mem_singleton_iff]
    intro h
    have : ((x : ℂ) + (c : ℂ) * I).im = 0 := by rw [h]; simp
    simp at this
    exact hc this

lemma memStrip_ver {a y : ℝ} (ha : |a| ≤ 1 / 2) (ha0 : a ≠ 0) :
    ((a : ℂ) + (y : ℂ) * I) ∈ clStrip \ {0} := by
  constructor
  · simpa using ha
  · simp only [Set.mem_singleton_iff]
    intro h
    have : ((a : ℂ) + (y : ℂ) * I).re = 0 := by rw [h]; simp
    simp at this
    exact ha0 this

lemma abs_le_of_mem_uIcc {x : ℝ} (hx : x ∈ Set.uIcc (-(1/2) : ℝ) (1/2 : ℝ)) : |x| ≤ 1 / 2 := by
  rw [Set.uIcc_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2)] at hx
  exact abs_le.2 ⟨hx.1, hx.2⟩

/-- Everything on the contour lies in the closed strip and is nonzero. -/
lemma bdry_congr {T : ℝ} (hT : T ≠ 0) {h₁ h₂ : ℂ → ℂ}
    (h : ∀ z ∈ clStrip \ {0}, h₁ z = h₂ z) : bdry T h₁ = bdry T h₂ := by
  have ehor : ∀ c : ℝ, c ≠ 0 →
      (∫ x : ℝ in (-(1/2) : ℝ)..(1/2 : ℝ), h₁ ((x : ℂ) + (c : ℂ) * I))
        = ∫ x : ℝ in (-(1/2) : ℝ)..(1/2 : ℝ), h₂ ((x : ℂ) + (c : ℂ) * I) := by
    intro c hc
    exact integral_congr fun x hx => h _ (memStrip_hor hc (abs_le_of_mem_uIcc hx))
  have ever : ∀ a : ℝ, |a| ≤ 1/2 → a ≠ 0 →
      (∫ y : ℝ in (-T)..T, h₁ ((a : ℂ) + (y : ℂ) * I))
        = ∫ y : ℝ in (-T)..T, h₂ ((a : ℂ) + (y : ℂ) * I) := by
    intro a ha ha0
    exact integral_congr fun y _ => h _ (memStrip_ver ha ha0)
  rw [bdry, bdry, ehor (-T) (neg_ne_zero.2 hT), ehor T hT,
    ever (1/2) (by norm_num) (by norm_num), ever (-(1/2)) (by norm_num) (by norm_num)]

/-- **Cauchy–Goursat on the rectangle**: `bdry T F = 0` for `F` continuous on the closed strip
and holomorphic inside it. -/
lemma bdry_eq_zero (T : ℝ) {F : ℂ → ℂ}
    (hc : ContinuousOn F clStrip) (hd : DifferentiableOn ℂ F opStrip) :
    bdry T F = 0 := by
  have hCont : ContinuousOn F (Set.uIcc (-(1/2) : ℝ) (1/2) ×ℂ Set.uIcc (-T) T) := by
    refine hc.mono ?_
    rintro z hz
    have := (Complex.mem_reProdIm.1 hz).1
    exact mem_clStrip.2 (abs_le_of_mem_uIcc this)
  have hDiff : ∀ z ∈ (Set.Ioo (min (-(1/2) : ℝ) (1/2)) (max (-(1/2) : ℝ) (1/2)) ×ℂ
      Set.Ioo (min (-T) T) (max (-T) T)) \ ∅, DifferentiableAt ℂ F z := by
    rintro z ⟨hz, -⟩
    have hre := (Complex.mem_reProdIm.1 hz).1
    rw [min_eq_left (by norm_num : (-(1/2) : ℝ) ≤ 1/2),
      max_eq_right (by norm_num : (-(1/2) : ℝ) ≤ 1/2)] at hre
    exact hd.differentiableAt (isOpen_opStrip.mem_nhds (mem_opStrip.2 (abs_lt.2 ⟨hre.1, hre.2⟩)))
  have key := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    F (⟨-(1/2), -T⟩ : ℂ) (⟨1/2, T⟩ : ℂ) ∅ Set.countable_empty hCont hDiff
  simpa [bdry, smul_eq_mul] using key

/-! ### `∮ dz / z = 2 π i` over the boundary of the rectangle -/

lemma inv_line_ne_zero {c x : ℝ} (hc : c ≠ 0) : ((x : ℂ) + (c : ℂ) * I) ≠ 0 := by
  intro h
  have : ((x : ℂ) + (c : ℂ) * I).im = 0 := by rw [h]; simp
  simp at this
  exact hc this

/-- `t ↦ ½ log (t² + c²) − i arctan (t/c)` is an antiderivative of `t ↦ (t + ci)⁻¹`. -/
lemma hasDerivAt_invLine {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => ((Real.log (t ^ 2 + c ^ 2) / 2 : ℝ) : ℂ)
        - I * ((Real.arctan (t / c) : ℝ) : ℂ))
      (((x : ℂ) + (c : ℂ) * I)⁻¹) x := by
  have hpos : (0 : ℝ) < x ^ 2 + c ^ 2 := by positivity
  have hD : (x ^ 2 + c ^ 2 : ℝ) ≠ 0 := ne_of_gt hpos
  have h1 : HasDerivAt (fun t : ℝ => Real.log (t ^ 2 + c ^ 2) / 2) (x / (x ^ 2 + c ^ 2)) x := by
    have hbase : HasDerivAt (fun t : ℝ => t ^ 2 + c ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_id x).pow 2).add_const (c ^ 2)
    have h := (hbase.log (ne_of_gt hpos)).div_const 2
    have e : 2 * x / (x ^ 2 + c ^ 2) / 2 = x / (x ^ 2 + c ^ 2) := by
      field_simp
    rwa [e] at h
  have h2 : HasDerivAt (fun t : ℝ => Real.arctan (t / c)) (c / (x ^ 2 + c ^ 2)) x := by
    have hbase : HasDerivAt (fun t : ℝ => t / c) (1 / c) x := by
      simpa using (hasDerivAt_id x).div_const c
    have h := (Real.hasDerivAt_arctan (x / c)).comp x hbase
    have e : 1 / (1 + (x / c) ^ 2) * (1 / c) = c / (x ^ 2 + c ^ 2) := by
      field_simp
      ring
    rw [e] at h
    exact h
  have hsum := (h1.ofReal_comp).sub (HasDerivAt.const_mul I (h2.ofReal_comp))
  have hval : ((x : ℂ) + (c : ℂ) * I)⁻¹
      = ((x / (x ^ 2 + c ^ 2) : ℝ) : ℂ) - I * ((c / (x ^ 2 + c ^ 2) : ℝ) : ℂ) := by
    refine inv_eq_of_mul_eq_one_right ?_
    have hDC : ((x : ℂ) ^ 2 + (c : ℂ) ^ 2) ≠ 0 := by
      exact_mod_cast hD
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hval]
  exact hsum

lemma continuous_invLine {c : ℝ} (hc : c ≠ 0) :
    Continuous fun x : ℝ => ((x : ℂ) + (c : ℂ) * I)⁻¹ :=
  ((Complex.continuous_ofReal.add continuous_const).inv₀ (fun _ => inv_line_ne_zero hc))

/-- The horizontal side: `∫_{-a}^{a} (x + ci)⁻¹ dx = −2 i arctan (a/c)`. -/
lemma integral_inv_hor {c : ℝ} (hc : c ≠ 0) (a : ℝ) :
    (∫ x : ℝ in (-a)..a, ((x : ℂ) + (c : ℂ) * I)⁻¹)
      = -(2 * I * ((Real.arctan (a / c) : ℝ) : ℂ)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_invLine hc x)
    ((continuous_invLine hc).intervalIntegrable _ _)]
  have hlog : ((-a) ^ 2 + c ^ 2 : ℝ) = a ^ 2 + c ^ 2 := by ring
  rw [hlog, neg_div, Real.arctan_neg]
  push_cast
  ring

/-- The vertical side, obtained from the horizontal one by `b + yi = i (y − bi)`. -/
lemma integral_inv_ver {b : ℝ} (hb : b ≠ 0) (T : ℝ) :
    (∫ y : ℝ in (-T)..T, ((b : ℂ) + (y : ℂ) * I)⁻¹)
      = 2 * ((Real.arctan (T / b) : ℝ) : ℂ) := by
  have hrot : ∀ y : ℝ, ((b : ℂ) + (y : ℂ) * I)⁻¹
      = -I * ((y : ℂ) + ((-b : ℝ) : ℂ) * I)⁻¹ := by
    intro y
    have h : ((b : ℂ) + (y : ℂ) * I) = I * ((y : ℂ) + ((-b : ℝ) : ℂ) * I) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h, mul_inv, Complex.inv_I]
  simp_rw [hrot]
  rw [intervalIntegral.integral_const_mul, integral_inv_hor (neg_ne_zero.2 hb) T]
  have : (T / (-b) : ℝ) = -(T / b) := by rw [div_neg]
  rw [this, Real.arctan_neg]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `∮_{∂R} dz/z = 2 π i`. -/
lemma bdry_inv {T : ℝ} (hT : 0 < T) : bdry T (fun z => z⁻¹) = 2 * (Real.pi : ℂ) * I := by
  have hTne : T ≠ 0 := ne_of_gt hT
  rw [bdry]
  rw [show ((-(1/2) : ℝ)) = -(1/2 : ℝ) from rfl]
  rw [integral_inv_hor (c := -T) (neg_ne_zero.2 hTne) (1/2),
    integral_inv_hor (c := T) hTne (1/2),
    integral_inv_ver (b := 1/2) (by norm_num) T,
    integral_inv_ver (b := -(1/2)) (by norm_num) T]
  have e1 : ((1/2 : ℝ) / (-T)) = -((2*T)⁻¹) := by
    field_simp
  have e2 : ((1/2 : ℝ) / T) = (2*T)⁻¹ := by
    field_simp
  have e3 : (T / (1/2 : ℝ)) = 2 * T := by
    field_simp
  have e4 : (T / (-(1/2) : ℝ)) = -(2 * T) := by
    field_simp
  rw [e1, e2, e3, e4, Real.arctan_neg, Real.arctan_neg,
    Real.arctan_inv_of_pos (by positivity : (0:ℝ) < 2 * T)]
  push_cast
  ring

/-! ### Removing the pole -/

lemma continuousOn_stripG {f : ℂ → ℂ} (hf : ContinuousOn f clStrip) (φ : ℝ) :
    ContinuousOn (stripG φ f) (clStrip \ {0}) := by
  refine ContinuousOn.div ?_ (Continuous.continuousOn (by fun_prop)) ?_
  · exact (continuousOn_const.mul (Continuous.continuousOn (by fun_prop))).mul
      (hf.mono Set.sdiff_subset)
  · rintro z ⟨hz, hz0⟩
    refine sin_pi_ne_zero (by simpa using hz0) ?_
    have := mem_clStrip.1 hz
    linarith

lemma intervalIntegrable_hor {h : ℂ → ℂ} (hh : ContinuousOn h (clStrip \ {0}))
    {c : ℝ} (hc : c ≠ 0) :
    IntervalIntegrable (fun x : ℝ => h ((x : ℂ) + (c : ℂ) * I)) MeasureTheory.volume
      (-(1/2) : ℝ) (1/2 : ℝ) := by
  refine ContinuousOn.intervalIntegrable ?_
  exact hh.comp (by fun_prop) (fun x hx => memStrip_hor hc (abs_le_of_mem_uIcc hx))

lemma intervalIntegrable_ver {h : ℂ → ℂ} (hh : ContinuousOn h (clStrip \ {0}))
    {a : ℝ} (ha : |a| ≤ 1/2) (ha0 : a ≠ 0) (T : ℝ) :
    IntervalIntegrable (fun y : ℝ => h ((a : ℂ) + (y : ℂ) * I)) MeasureTheory.volume (-T) T := by
  refine ContinuousOn.intervalIntegrable ?_
  exact hh.comp (by fun_prop) (fun y _ => memStrip_ver ha ha0)

lemma bdry_sub {T : ℝ} (hT : T ≠ 0) {h₁ h₂ : ℂ → ℂ}
    (hc₁ : ContinuousOn h₁ (clStrip \ {0})) (hc₂ : ContinuousOn h₂ (clStrip \ {0})) :
    bdry T (fun z => h₁ z - h₂ z) = bdry T h₁ - bdry T h₂ := by
  simp only [bdry]
  rw [intervalIntegral.integral_sub (intervalIntegrable_hor hc₁ (neg_ne_zero.2 hT))
        (intervalIntegrable_hor hc₂ (neg_ne_zero.2 hT)),
    intervalIntegral.integral_sub (intervalIntegrable_hor hc₁ hT)
        (intervalIntegrable_hor hc₂ hT),
    intervalIntegral.integral_sub (intervalIntegrable_ver hc₁ (by norm_num) (by norm_num) T)
        (intervalIntegrable_ver hc₂ (by norm_num) (by norm_num) T),
    intervalIntegral.integral_sub (intervalIntegrable_ver hc₁ (a := -(1/2)) (by norm_num)
        (by norm_num) T)
        (intervalIntegrable_ver hc₂ (a := -(1/2)) (by norm_num) (by norm_num) T)]
  ring

lemma bdry_const_mul (T : ℝ) (c : ℂ) (h : ℂ → ℂ) :
    bdry T (fun z => c * h z) = c * bdry T h := by
  simp only [bdry, intervalIntegral.integral_const_mul]
  ring

/-- The key consequence of Cauchy–Goursat: `∮ g = 2 π i f 0`, for every `T > 0`. -/
lemma bdry_stripG {T : ℝ} (hT : 0 < T) {f : ℂ → ℂ}
    (hfc : ContinuousOn f clStrip) (hfd : DifferentiableOn ℂ f opStrip) (φ : ℝ) :
    bdry T (stripG φ f) = 2 * (Real.pi : ℂ) * I * f 0 := by
  have hnbhd : clStrip ∈ nhds (0 : ℂ) :=
    mem_nhds_iff.2 ⟨opStrip, opStrip_subset_clStrip, isOpen_opStrip, zero_mem_opStrip⟩
  have hdiff0 : DifferentiableAt ℂ (stripNum φ f) 0 :=
    (differentiableOn_stripNum hfd φ).differentiableAt
      (isOpen_opStrip.mem_nhds zero_mem_opStrip)
  have hDc : ContinuousOn (dslope (stripNum φ f) 0) clStrip :=
    (continuousOn_dslope hnbhd).2 ⟨continuousOn_stripNum hfc φ, hdiff0⟩
  have hDd : DifferentiableOn ℂ (dslope (stripNum φ f) 0) opStrip :=
    (Complex.differentiableOn_dslope (isOpen_opStrip.mem_nhds zero_mem_opStrip)).2
      (differentiableOn_stripNum hfd φ)
  have h0 : bdry T (dslope (stripNum φ f) 0) = 0 := bdry_eq_zero T hDc hDd
  have hEq : ∀ z ∈ clStrip \ {0},
      dslope (stripNum φ f) 0 z = stripG φ f z - f 0 * z⁻¹ := by
    rintro z ⟨hz, hz0⟩
    have hzne : z ≠ 0 := by simpa using hz0
    have hre : |z.re| < 1 := by have := mem_clStrip.1 hz; linarith
    rw [dslope_of_ne _ hzne, slope_def_field, stripNum_zero, stripNum_eq hzne hre]
    field_simp
    ring
  have hinvc : ContinuousOn (fun z : ℂ => f 0 * z⁻¹) (clStrip \ {0}) := by
    refine continuousOn_const.mul (ContinuousOn.inv₀ continuousOn_id ?_)
    rintro z ⟨-, hz0⟩
    simpa using hz0
  have h1 := bdry_congr (ne_of_gt hT) hEq
  rw [h0] at h1
  rw [bdry_sub (ne_of_gt hT) (continuousOn_stripG hfc φ) hinvc, bdry_const_mul,
    bdry_inv hT] at h1
  have := sub_eq_zero.1 h1.symm
  rw [this]
  ring



/-! ### Norm estimates -/

/-- `‖g z‖ = π e^{-φ Im z} ‖f z‖ / ‖sin (π z)‖`. -/
lemma norm_stripG (φ : ℝ) (f : ℂ → ℂ) (z : ℂ) :
    ‖stripG φ f z‖
      = Real.pi * Real.exp (-(φ * z.im)) * ‖f z‖ / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
  have hre : (I * (φ : ℂ) * z).re = -(φ * z.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [stripG, norm_div, norm_mul, norm_mul, Complex.norm_exp, hre, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg Real.pi_nonneg]

/-- `‖sin w‖ ≥ sinh |Im w|`. -/
lemma norm_sin_lower (z : ℂ) :
    (Real.exp |z.im| - Real.exp (-|z.im|)) / 2 ≤ ‖Complex.sin z‖ := by
  have hnorm : ‖Complex.sin z‖ = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2 := by
    rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, Complex.norm_ofNat]
    ring
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [hnorm]
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  rcases le_total 0 z.im with h | h
  · rw [abs_of_nonneg h]
    calc Real.exp z.im - Real.exp (-z.im) = ‖Complex.exp (-z * I)‖ - ‖Complex.exp (z * I)‖ := by
          rw [h1, h2]
      _ ≤ _ := norm_sub_norm_le _ _
  · rw [abs_of_nonpos h]
    rw [← norm_neg, neg_sub]
    calc Real.exp (-z.im) - Real.exp (- -z.im) = ‖Complex.exp (z * I)‖ - ‖Complex.exp (-z * I)‖ := by
          rw [h1, h2]; congr 1; simp
      _ ≤ _ := norm_sub_norm_le _ _

lemma integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    MeasureTheory.Integrable (fun y : ℝ => Real.exp (-c * |y|)) := by
  rw [← MeasureTheory.integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)),
    MeasureTheory.integrableOn_union]
  constructor
  · refine (integrableOn_exp_mul_Iic hc 0).congr_fun ?_ measurableSet_Iic
    intro y hy
    simp only [Set.mem_Iic] at hy
    show Real.exp (c * y) = Real.exp (-c * |y|)
    rw [abs_of_nonpos hy]
    ring_nf
  · refine (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).congr_fun ?_ measurableSet_Ioi
    intro y hy
    simp only [Set.mem_Ioi] at hy
    show Real.exp (-c * y) = Real.exp (-c * |y|)
    rw [abs_of_pos hy]

/-! ### The horizontal sides vanish -/

lemma nonneg_of_bound {f : ℂ → ℂ} {C : ℝ} (hC : ∀ z ∈ clStrip, ‖f z‖ ≤ C) : 0 ≤ C :=
  le_trans (norm_nonneg (f 0)) (hC 0 (by simp [clStrip]))

/-- On a horizontal side at height `±T` with `T ≥ 1`, `‖g‖ ≤ 4 π C e^{(|φ|−π) T}`. -/
lemma norm_stripG_hor_le {f : ℂ → ℂ} {C : ℝ} (hC : ∀ z ∈ clStrip, ‖f z‖ ≤ C)
    (φ : ℝ) {T x c : ℝ} (hT : 1 ≤ T) (hx : |x| ≤ 1/2) (hc : |c| = T) :
    ‖stripG φ f ((x : ℂ) + (c : ℂ) * I)‖
      ≤ 4 * Real.pi * C * Real.exp ((|φ| - Real.pi) * T) := by
  have hC0 : 0 ≤ C := nonneg_of_bound hC
  have hT0 : (0 : ℝ) < T := by linarith
  set z : ℂ := (x : ℂ) + (c : ℂ) * I with hz
  have hzre : z.re = x := by simp [hz]
  have hzim : z.im = c := by simp [hz]
  have hzmem : z ∈ clStrip := by rw [mem_clStrip, hzre]; exact hx
  -- numerator
  have hnum : Real.pi * Real.exp (-(φ * z.im)) * ‖f z‖
      ≤ Real.pi * Real.exp (|φ| * T) * C := by
    have h1 : Real.exp (-(φ * z.im)) ≤ Real.exp (|φ| * T) := by
      refine Real.exp_le_exp.2 ?_
      calc -(φ * z.im) ≤ |φ * z.im| := neg_le_abs _
        _ = |φ| * T := by rw [abs_mul, hzim, hc]
    have h2 : ‖f z‖ ≤ C := hC z hzmem
    have := mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
    calc Real.pi * Real.exp (-(φ * z.im)) * ‖f z‖
        = Real.pi * (Real.exp (-(φ * z.im)) * ‖f z‖) := by ring
      _ ≤ Real.pi * (Real.exp (|φ| * T) * C) := by
          exact mul_le_mul_of_nonneg_left this Real.pi_nonneg
      _ = Real.pi * Real.exp (|φ| * T) * C := by ring
  -- denominator
  have hden : Real.exp (Real.pi * T) / 4 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
    refine le_trans ?_ (norm_sin_lower ((Real.pi : ℂ) * z))
    have him : ((Real.pi : ℂ) * z).im = Real.pi * T ∨ ((Real.pi : ℂ) * z).im = -(Real.pi * T) := by
      have : ((Real.pi : ℂ) * z).im = Real.pi * c := by simp [hzim]
      rcases abs_eq (le_of_lt hT0) |>.1 hc with h | h
      · left; rw [this, h]
      · right; rw [this, h]; ring
    have habs : |((Real.pi : ℂ) * z).im| = Real.pi * T := by
      rcases him with h | h
      · rw [h, abs_of_nonneg (by positivity)]
      · rw [h, abs_neg, abs_of_nonneg (by positivity)]
    rw [habs]
    have hsmall : Real.exp (-(Real.pi * T)) ≤ Real.exp (Real.pi * T) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      have h1 : (1:ℝ) ≤ 2 * (Real.pi * T) := by nlinarith [Real.pi_gt_three]
      have h2 : (2:ℝ) ≤ Real.exp (2 * (Real.pi * T)) := by
        calc (2:ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
          _ ≤ Real.exp (2 * (Real.pi * T)) := Real.exp_le_exp.2 h1
      calc Real.exp (-(Real.pi * T)) * 2
          ≤ Real.exp (-(Real.pi * T)) * Real.exp (2 * (Real.pi * T)) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = Real.exp (Real.pi * T) := by rw [← Real.exp_add]; congr 1; ring
    linarith
  have hdenpos : (0 : ℝ) < Real.exp (Real.pi * T) / 4 := by positivity
  rw [norm_stripG]
  have hstep : Real.pi * Real.exp (-(φ * z.im)) * ‖f z‖ / ‖Complex.sin ((Real.pi : ℂ) * z)‖
      ≤ (Real.pi * Real.exp (|φ| * T) * C) / (Real.exp (Real.pi * T) / 4) := by
    exact div_le_div₀ (by positivity) hnum hdenpos hden
  refine le_trans hstep (le_of_eq ?_)
  have hexp : Real.exp ((|φ| - Real.pi) * T) = Real.exp (|φ| * T) / Real.exp (Real.pi * T) := by
    rw [← Real.exp_sub]; congr 1; ring
  rw [hexp]
  have hne : Real.exp (Real.pi * T) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- The two horizontal sides of the rectangle contribute nothing in the limit. -/
lemma tendsto_hor {f : ℂ → ℂ} {C : ℝ} (hC : ∀ z ∈ clStrip, ‖f z‖ ≤ C) {φ : ℝ}
    (hφ : |φ| < Real.pi) (c : ℝ → ℝ) (hc : ∀ T : ℝ, 1 ≤ T → |c T| = T) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (-(1/2) : ℝ)..(1/2 : ℝ),
      stripG φ f ((x : ℂ) + ((c T : ℝ) : ℂ) * I)) atTop (nhds 0) := by
  have hlim : Tendsto (fun T : ℝ => 4 * Real.pi * C * Real.exp ((|φ| - Real.pi) * T))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun T : ℝ => (Real.pi - |φ|) * T) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by linarith) tendsto_id
    have h2 : Tendsto (fun T : ℝ => (|φ| - Real.pi) * T) atTop atBot := by
      refine (tendsto_neg_atTop_atBot.comp h1).congr fun T => by
        simp only [Function.comp_apply]; ring
    have h3 : Tendsto (fun T : ℝ => Real.exp ((|φ| - Real.pi) * T)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h2
    simpa using h3.const_mul (4 * Real.pi * C)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  have hbound : ∀ x ∈ Set.uIoc (-(1/2) : ℝ) (1/2 : ℝ),
      ‖stripG φ f ((x : ℂ) + ((c T : ℝ) : ℂ) * I)‖
        ≤ 4 * Real.pi * C * Real.exp ((|φ| - Real.pi) * T) := by
    intro x hx
    refine norm_stripG_hor_le hC φ hT ?_ (hc T hT)
    rw [Set.uIoc_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)] at hx
    exact abs_le.2 ⟨le_of_lt hx.1, hx.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  refine le_trans h (le_of_eq ?_)
  norm_num

/-! ### The vertical sides -/

lemma sin_pi_right (y : ℝ) :
    Complex.sin ((Real.pi : ℂ) * (((1/2 : ℝ) : ℂ) + (y : ℂ) * I))
      = ((Real.cosh (Real.pi * y) : ℝ) : ℂ) := by
  have h : (Real.pi : ℂ) * (((1/2 : ℝ) : ℂ) + (y : ℂ) * I)
      = ((Real.pi * y : ℝ) : ℂ) * I + (Real.pi : ℂ) / 2 := by
    push_cast; ring
  rw [h, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]

lemma sin_pi_left (y : ℝ) :
    Complex.sin ((Real.pi : ℂ) * (((-(1/2) : ℝ) : ℂ) + (y : ℂ) * I))
      = -((Real.cosh (Real.pi * y) : ℝ) : ℂ) := by
  have h : (Real.pi : ℂ) * (((-(1/2) : ℝ) : ℂ) + (y : ℂ) * I)
      = ((Real.pi * y : ℝ) : ℂ) * I - (Real.pi : ℂ) / 2 := by
    push_cast; ring
  rw [h, Complex.sin_sub_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]

lemma norm_sin_pi_ver {a : ℝ} (ha : a = 1/2 ∨ a = -(1/2)) (y : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) * ((a : ℂ) + (y : ℂ) * I))‖ = Real.cosh (Real.pi * y) := by
  have hpos : (0 : ℝ) < Real.cosh (Real.pi * y) := Real.cosh_pos _
  rcases ha with rfl | rfl
  · rw [sin_pi_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  · rw [sin_pi_left, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

lemma inv_cosh_le (t : ℝ) : (Real.cosh t)⁻¹ ≤ 2 * Real.exp (-|t|) := by
  have hpos : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have hge : Real.exp |t| / 2 ≤ Real.cosh t := by
    rw [Real.cosh_eq]
    rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
      have := (Real.exp_pos (-t)).le
      linarith
    · rw [h]
      have := (Real.exp_pos t).le
      linarith
  have hexp : (0 : ℝ) < Real.exp |t| := Real.exp_pos _
  rw [inv_le_iff_one_le_mul₀ hpos]
  have h2 : 2 * Real.exp (-|t|) * (Real.exp |t| / 2) = 1 := by
    rw [Real.exp_neg]
    field_simp
  calc (1 : ℝ) = 2 * Real.exp (-|t|) * (Real.exp |t| / 2) := h2.symm
    _ ≤ 2 * Real.exp (-|t|) * Real.cosh t := by
        refine mul_le_mul_of_nonneg_left hge ?_
        positivity

/-- On the vertical sides, `‖g‖ ≤ 2 π C e^{−(π−|φ|)|y|}`. -/
lemma norm_stripG_ver_le {f : ℂ → ℂ} {C : ℝ} (hC : ∀ z ∈ clStrip, ‖f z‖ ≤ C)
    (φ : ℝ) {a : ℝ} (ha : a = 1/2 ∨ a = -(1/2)) (y : ℝ) :
    ‖stripG φ f ((a : ℂ) + (y : ℂ) * I)‖
      ≤ 2 * Real.pi * C * Real.exp (-(Real.pi - |φ|) * |y|) := by
  have hC0 : 0 ≤ C := nonneg_of_bound hC
  set z : ℂ := (a : ℂ) + (y : ℂ) * I with hz
  have hzre : z.re = a := by simp [hz]
  have hzim : z.im = y := by simp [hz]
  have hzmem : z ∈ clStrip := by
    rw [mem_clStrip, hzre]
    rcases ha with rfl | rfl <;> (rw [abs_le]; constructor <;> norm_num)
  rw [norm_stripG, hzim, norm_sin_pi_ver ha, div_eq_mul_inv]
  have h1 : Real.exp (-(φ * y)) ≤ Real.exp (|φ| * |y|) := by
    refine Real.exp_le_exp.2 ?_
    calc -(φ * y) ≤ |φ * y| := neg_le_abs _
      _ = |φ| * |y| := abs_mul _ _
  have h2 : ‖f z‖ ≤ C := hC z hzmem
  have h3 : (Real.cosh (Real.pi * y))⁻¹ ≤ 2 * Real.exp (-(Real.pi * |y|)) := by
    have := inv_cosh_le (Real.pi * y)
    rwa [abs_mul, abs_of_nonneg Real.pi_nonneg] at this
  have hstep : Real.pi * Real.exp (-(φ * y)) * ‖f z‖ * (Real.cosh (Real.pi * y))⁻¹
      ≤ Real.pi * Real.exp (|φ| * |y|) * C * (2 * Real.exp (-(Real.pi * |y|))) := by
    gcongr
  refine le_trans hstep (le_of_eq ?_)
  have hE : Real.exp (-(Real.pi - |φ|) * |y|)
      = Real.exp (|φ| * |y|) * Real.exp (-(Real.pi * |y|)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hE]
  ring

lemma continuous_stripG_ver {f : ℂ → ℂ} (hfc : ContinuousOn f clStrip) (φ : ℝ)
    {a : ℝ} (ha : a = 1/2 ∨ a = -(1/2)) :
    Continuous fun y : ℝ => stripG φ f ((a : ℂ) + (y : ℂ) * I) := by
  have hmem : ∀ y : ℝ, ((a : ℂ) + (y : ℂ) * I) ∈ clStrip \ {0} := by
    intro y
    refine memStrip_ver ?_ ?_ <;> rcases ha with rfl | rfl <;> norm_num
  exact (continuousOn_stripG hfc φ).comp_continuous (by fun_prop) hmem

lemma integrable_stripG_ver {f : ℂ → ℂ} (hfc : ContinuousOn f clStrip) {C : ℝ}
    (hC : ∀ z ∈ clStrip, ‖f z‖ ≤ C) {φ : ℝ} (hφ : |φ| < Real.pi)
    {a : ℝ} (ha : a = 1/2 ∨ a = -(1/2)) :
    MeasureTheory.Integrable (fun y : ℝ => stripG φ f ((a : ℂ) + (y : ℂ) * I)) := by
  refine MeasureTheory.Integrable.mono'
    (((integrable_exp_neg_mul_abs (c := Real.pi - |φ|) (by linarith)).const_mul
      (2 * Real.pi * C)))
    ((continuous_stripG_ver hfc φ ha).aestronglyMeasurable)
    (MeasureTheory.ae_of_all _ fun y => ?_)
  exact norm_stripG_ver_le hC φ ha y

lemma tendsto_ver {f : ℂ → ℂ} (hfc : ContinuousOn f clStrip) {C : ℝ}
    (hC : ∀ z ∈ clStrip, ‖f z‖ ≤ C) {φ : ℝ} (hφ : |φ| < Real.pi)
    {a : ℝ} (ha : a = 1/2 ∨ a = -(1/2)) :
    Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, stripG φ f ((a : ℂ) + (y : ℂ) * I)) atTop
      (nhds (∫ y : ℝ, stripG φ f ((a : ℂ) + (y : ℂ) * I))) :=
  MeasureTheory.intervalIntegral_tendsto_integral (integrable_stripG_ver hfc hC hφ ha)
    tendsto_neg_atTop_atBot tendsto_id

/-! ### Letting the rectangle exhaust the strip -/

/-- The limit form of the contour identity: `2 π i f 0 = i ∫ g(½+iy) dy − i ∫ g(−½+iy) dy`. -/
theorem strip_contour_limit {f : ℂ → ℂ} (hfc : ContinuousOn f clStrip)
    (hfd : DifferentiableOn ℂ f opStrip) {C : ℝ} (hC : ∀ z ∈ clStrip, ‖f z‖ ≤ C)
    {φ : ℝ} (hφ : |φ| < Real.pi) :
    2 * (Real.pi : ℂ) * I * f 0
      = I * (∫ y : ℝ, stripG φ f (((1/2 : ℝ) : ℂ) + (y : ℂ) * I))
        - I * (∫ y : ℝ, stripG φ f (((-(1/2) : ℝ) : ℂ) + (y : ℂ) * I)) := by
  have h1 : Tendsto (fun T : ℝ => bdry T (stripG φ f)) atTop
      (nhds (2 * (Real.pi : ℂ) * I * f 0)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    exact (bdry_stripG hT hfc hfd φ).symm
  have thA : Tendsto (fun T : ℝ => ∫ x : ℝ in (-(1/2) : ℝ)..(1/2 : ℝ),
      stripG φ f ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) atTop (nhds 0) :=
    tendsto_hor hC hφ (fun T => -T) (fun T hT => by rw [abs_neg, abs_of_nonneg (by linarith)])
  have thB : Tendsto (fun T : ℝ => ∫ x : ℝ in (-(1/2) : ℝ)..(1/2 : ℝ),
      stripG φ f ((x : ℂ) + ((T : ℝ) : ℂ) * I)) atTop (nhds 0) :=
    tendsto_hor hC hφ (fun T => T) (fun T hT => abs_of_nonneg (by linarith))
  have tvR := tendsto_ver hfc hC hφ (a := (1/2 : ℝ)) (Or.inl rfl)
  have tvL := tendsto_ver hfc hC hφ (a := (-(1/2) : ℝ)) (Or.inr rfl)
  have h2 : Tendsto (fun T : ℝ => bdry T (stripG φ f)) atTop
      (nhds (I * (∫ y : ℝ, stripG φ f (((1/2 : ℝ) : ℂ) + (y : ℂ) * I))
        - I * (∫ y : ℝ, stripG φ f (((-(1/2) : ℝ) : ℂ) + (y : ℂ) * I)))) := by
    have := ((thA.sub thB).add (tvR.const_mul I)).sub (tvL.const_mul I)
    simpa [bdry] using this
  exact tendsto_nhds_unique h1 h2

/-- **RvD Lemma 4.6** (Haagerup's form of the Cauchy integral formula on the strip).  For
`λ = e^{iφ/2}` with `−π < φ < π`, and `f` bounded and continuous on `|Re z| ≤ 1/2` and
holomorphic inside,

  `f 0 = ∫ e^{−φt} (e^{πt} + e^{−πt})⁻¹ (λ f (it + 1/2) + λ̄ f (it − 1/2)) dt`. -/
theorem lemma_4_6 {f : ℂ → ℂ} (hfc : ContinuousOn f clStrip)
    (hfd : DifferentiableOn ℂ f opStrip) {C : ℝ} (hC : ∀ z ∈ clStrip, ‖f z‖ ≤ C)
    {φ : ℝ} (hφ : |φ| < Real.pi) {lam : ℂ} (hlam : lam = Complex.exp (I * (φ : ℂ) / 2)) :
    f 0 = ∫ t : ℝ, ((Real.exp (-(φ * t))
        * (Real.exp (Real.pi * t) + Real.exp (-(Real.pi * t)))⁻¹ : ℝ) : ℂ)
      * (lam * f ((t : ℂ) * I + 1/2) + (starRingEnd ℂ) lam * f ((t : ℂ) * I - 1/2)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkey := strip_contour_limit hfc hfd hC hφ
  have hconjlam : (starRingEnd ℂ) lam = Complex.exp (-(I * (φ : ℂ) / 2)) := by
    rw [hlam, ← Complex.exp_conj]
    congr 1
    rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  -- combine the two vertical integrals
  have hint : (∫ y : ℝ, stripG φ f (((1/2 : ℝ) : ℂ) + (y : ℂ) * I))
      - (∫ y : ℝ, stripG φ f (((-(1/2) : ℝ) : ℂ) + (y : ℂ) * I))
      = ∫ y : ℝ, (stripG φ f (((1/2 : ℝ) : ℂ) + (y : ℂ) * I)
          - stripG φ f (((-(1/2) : ℝ) : ℂ) + (y : ℂ) * I)) :=
    (MeasureTheory.integral_sub (integrable_stripG_ver hfc hC hφ (Or.inl rfl))
      (integrable_stripG_ver hfc hC hφ (Or.inr rfl))).symm
  set J : ℂ := ∫ y : ℝ, (stripG φ f (((1/2 : ℝ) : ℂ) + (y : ℂ) * I)
    - stripG φ f (((-(1/2) : ℝ) : ℂ) + (y : ℂ) * I)) with hJ
  have hkey2 : 2 * (Real.pi : ℂ) * I * f 0 = I * J := by
    rw [← hint, mul_sub]
    exact hkey
  have hfinal : f 0 = ((2 * (Real.pi : ℂ))⁻¹) * J := by
    have h3 : (I : ℂ) * (2 * (Real.pi : ℂ) * f 0) = I * J := by rw [← hkey2]; ring
    have h4 : 2 * (Real.pi : ℂ) * f 0 = J := mul_left_cancel₀ Complex.I_ne_zero h3
    rw [← h4]
    field_simp
  -- the pointwise identity
  have hpt : ∀ t : ℝ, ((2 * (Real.pi : ℂ))⁻¹) *
      (stripG φ f (((1/2 : ℝ) : ℂ) + (t : ℂ) * I)
        - stripG φ f (((-(1/2) : ℝ) : ℂ) + (t : ℂ) * I))
      = ((Real.exp (-(φ * t))
          * (Real.exp (Real.pi * t) + Real.exp (-(Real.pi * t)))⁻¹ : ℝ) : ℂ)
        * (lam * f ((t : ℂ) * I + 1/2) + (starRingEnd ℂ) lam * f ((t : ℂ) * I - 1/2)) := by
    intro t
    have hzR : (((1/2 : ℝ) : ℂ) + (t : ℂ) * I) = (t : ℂ) * I + 1/2 := by push_cast; ring
    have hzL : (((-(1/2) : ℝ) : ℂ) + (t : ℂ) * I) = (t : ℂ) * I - 1/2 := by push_cast; ring
    have hexpR : Complex.exp (I * (φ : ℂ) * (((1/2 : ℝ) : ℂ) + (t : ℂ) * I))
        = lam * ((Real.exp (-(φ * t)) : ℝ) : ℂ) := by
      have harg : I * (φ : ℂ) * (((1/2 : ℝ) : ℂ) + (t : ℂ) * I)
          = I * (φ : ℂ) / 2 + ((-(φ * t) : ℝ) : ℂ) := by
        push_cast
        linear_combination ((φ : ℂ) * (t : ℂ)) * Complex.I_sq
      rw [harg, Complex.exp_add, hlam, Complex.ofReal_exp]
    have hexpL : Complex.exp (I * (φ : ℂ) * (((-(1/2) : ℝ) : ℂ) + (t : ℂ) * I))
        = (starRingEnd ℂ) lam * ((Real.exp (-(φ * t)) : ℝ) : ℂ) := by
      have harg : I * (φ : ℂ) * (((-(1/2) : ℝ) : ℂ) + (t : ℂ) * I)
          = -(I * (φ : ℂ) / 2) + ((-(φ * t) : ℝ) : ℂ) := by
        push_cast
        linear_combination ((φ : ℂ) * (t : ℂ)) * Complex.I_sq
      rw [harg, Complex.exp_add, hconjlam, Complex.ofReal_exp]
    have hcosh : (Real.exp (Real.pi * t) + Real.exp (-(Real.pi * t)) : ℝ)
        = 2 * Real.cosh (Real.pi * t) := by
      rw [Real.cosh_eq]; ring
    have hcpos : (0 : ℝ) < Real.cosh (Real.pi * t) := Real.cosh_pos _
    have hcne : ((Real.cosh (Real.pi * t) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (ne_of_gt hcpos)
    rw [stripG, stripG, sin_pi_right, sin_pi_left, hexpR, hexpL, hzR, hzL, hcosh]
    push_cast
    field_simp
    ring
  rw [hfinal, hJ, ← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpt)


end Lemma46

end Theses.RvD
