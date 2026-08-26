/-
The one-parameter group `R^{iz}` and the modular group `Δ^{it}`, by the
*continuous* functional calculus only.

**This file has no thesis counterpart.**  Like `A/VN/Modular.lean` and
`A/VN/StandardSubspace.lean` it is machinery for the Rieffel–van Daele route to
the commutation theorem described in `docs/COMMUTATION-THEOREM.md`.

Reference: Marc A. Rieffel and Alfons van Daele, *A bounded operator approach to
Tomita–Takesaki theory*, Pacific J. Math. **69** (1977) 187–221, Lemma 3.6.

## The point

`Δ = (2 − R) R⁻¹` is unbounded, and `Δ^{it}` is classically produced by the
*Borel* functional calculus, which Mathlib does not have.  It is not needed.
For `Im z ≤ 0` the scalar function `t ↦ t^{1+iz}` is continuous and bounded on
`[0,2]` — its exponent has real part `1 − Im z ≥ 1`, so it extends continuously
by `0` at `t = 0` — so the *continuous* functional calculus already gives
`R^{1+iz}`, and the pointwise bound `|t^{1+iz}|² ≤ 2^{-2 Im z} · t²` on `[0,2]`
gives `‖R^{1+iz} ζ‖ ≤ 2^{-Im z} ‖R ζ‖`.  Hence `R ζ ↦ R^{1+iz} ζ` is bounded on
the dense subspace `ran R` and extends to all of `H` by
`LinearMap.extendOfNorm` — the same device used for `J` in
`A/VN/StandardSubspace.lean` and for the normalisation lemma in
`A/VN/Modular.lean`.  That extension is `R^{iz}`.

## Main definitions

* `Theses.RvD.IsPowBase X`: `X : H →L[ℂ] H` is positive, `≤ 2` and injective —
  the hypotheses satisfied by both `R` and `2 − R` for a standard subspace.
* `Theses.RvD.cpowOp X w`: `X^w := cfc (· ^ w) X`, meaningful for `0 < re w`.
* `Theses.RvD.opPow X z`: `X^{iz}`, the continuous extension of
  `X ζ ↦ X^{1+iz} ζ`.
* `Theses.RvD.modPow K t`: the modular group `Δ^{it} = (2−R)^{it} R^{-it}`.

* `Theses.RvD.jConj K hsep hcyc`: conjugation `x ↦ J x J`, bundled as
  `jConjHom` — a *real* ⋆-algebra endomorphism of `B(H)`, which is what lets
  `cfc` be transported along it.

## Main results

* `IsPowBase.norm_cpowOp_apply_le`, `IsPowBase.norm_cpowOp_apply`: the estimate
  `‖X^{1+iz} ζ‖ ≤ 2^{-Im z} ‖X ζ‖` and, for real `z`, the isometry
  `‖X^{1+iz} ζ‖ = ‖X ζ‖`.
* `IsPowBase.opPow_apply`, `IsPowBase.norm_opPow_apply_le`,
  `IsPowBase.norm_opPow_apply`: the same, transported to the extension.
* `IsPowBase.opPow_mul`, `IsPowBase.opPow_zero`: the group law
  `X^{iz} X^{iz'} = X^{i(z+z')}`, `X^0 = 1`.
* `IsPowBase.opPow_mem_unitary`: `X^{iz}` is unitary for real `z`.
* `IsPowBase.norm_cpowOp_sub_le`: `s ↦ X^{1+is}` is Lipschitz (constant `4`) in
  the operator norm, whence `IsPowBase.continuous_opPow_apply`, the strong
  continuity of `s ↦ X^{is}`.
* `IsPowBase.opPow_commute`: powers of two commuting bases commute.
* `modPow_mem_unitary`, `modPow_add`, `modPow_zero`, `star_modPow`,
  `norm_modPow_apply`, `continuous_modPow_apply`: `Δ^{it}` is a strongly
  continuous one-parameter unitary group.

## On the record only — nothing consumes these

The whole `jConj` layer below (`jConjRe`, `jConj`, `jConjHom` and their
lemmas, ~300 lines) and the two commutation statements built on it,
`jConj_cpowOp` (`J X^w J = (J X J)^{\bar w}`, from `StarAlgHom.map_cfc` for
the *real* calculus after splitting `X^w` into real and imaginary parts,
`IsPowBase.cpowOp_eq_re_add_im`) and `J_modPow` / `jConj_modPow`
(`J Δ^{it} = Δ^{it} J`), have **no consumer anywhere in `Theses/`**.
`A/VN/TomitaFourier.lean` defines `modFlow x' t := Δ^{it}(J x' J)Δ^{-it}`
directly and never performs the rearrangement that would have needed them.
`jConj` also duplicates `A/VN/TomitaTakesaki.lean`'s live `adJ` verbatim.
These three were advertised as "main results" until 2026-08-26; they are
kept as a record of the identity, not as machinery.  See
`docs/DEAD-LIMBS.md` §5b.

## Not here

Holomorphy of `z ↦ R^{1+iz}` on `Im z < 0` (the last clause of RvD Lemma 3.6)
is *not* proved.  It is not a corollary of anything above: the difference
quotient converges to `cfc (fun u => u^w * log u) X`, and both the continuity of
that symbol at `0` and the second-order remainder estimate need uniform control
of `t^{re w} |log t|^k` on `(0,2]` — true, elementary (`t^c |log t| ≤ 1/c`,
`t^c (log t)² ≤ 4/c²`), but several hundred lines of case analysis.  Nothing in
the `Δ^{it}` package below uses it.
-/
import Theses.A.VN.StandardSubspace

open Complex ClosedSubmodule
open scoped ComplexInnerProductSpace ComplexOrder

namespace Theses.RvD

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Bases for the power construction -/

/-- The hypotheses on a bounded operator under which `X^{iz}` is built below: `X` is positive,
bounded by `2` and injective.  Both `R` and `2 - R` satisfy them for a standard subspace. -/
structure IsPowBase (X : H →L[ℂ] H) : Prop where
  nonneg : 0 ≤ X
  le_two : X ≤ 2
  injective : Function.Injective X

namespace IsPowBase

variable {X : H →L[ℂ] H}

theorem isSelfAdjoint (h : IsPowBase X) : IsSelfAdjoint X := .of_nonneg h.nonneg

theorem isStarNormal (h : IsPowBase X) : IsStarNormal X := h.isSelfAdjoint.isStarNormal

/-- The real spectrum of `X` lies in `[0,2]`. -/
theorem spectrum_real_subset (h : IsPowBase X) : spectrum ℝ X ⊆ Set.Icc 0 2 := by
  intro t ht
  refine ⟨?_, ?_⟩
  · exact (StarOrderedRing.nonneg_iff_spectrum_nonneg X h.isSelfAdjoint).1 h.nonneg t ht
  · have hA : algebraMap ℝ (H →L[ℂ] H) 2 = 2 := by
      rw [Algebra.algebraMap_eq_smul_one]
      rw [show ((2 : ℝ) • (1 : H →L[ℂ] H)) = (1 : H →L[ℂ] H) + 1 by module]
      norm_num
    have h2 : X ≤ algebraMap ℝ (H →L[ℂ] H) 2 := hA ▸ h.le_two
    exact (le_algebraMap_iff_spectrum_le h.isSelfAdjoint).1 h2 t ht

/-- Every point of the complex spectrum of `X` is a real number in `[0,2]`. -/
theorem spectrum_complex_repr (h : IsPowBase X) {u : ℂ} (hu : u ∈ spectrum ℂ X) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 2 ∧ u = (t : ℂ) := by
  have himg := (h.isSelfAdjoint.spectrumRestricts (A := H →L[ℂ] H)).algebraMap_image
  rw [← himg] at hu
  obtain ⟨t, ht, rfl⟩ := hu
  exact ⟨t, h.spectrum_real_subset ht, rfl⟩

/-- Points of the complex spectrum have nonnegative real part; this is what the continuity of
`u ↦ u ^ w` needs. -/
theorem spectrum_complex_re_nonneg (h : IsPowBase X) {u : ℂ} (hu : u ∈ spectrum ℂ X) :
    0 ≤ u.re := by
  obtain ⟨t, ht, rfl⟩ := h.spectrum_complex_repr hu
  simpa using ht.1

theorem denseRange (h : IsPowBase X) : DenseRange X :=
  denseRange_of_isSelfAdjoint_injective h.isSelfAdjoint h.injective

end IsPowBase

/-! ## `X^w` by the continuous functional calculus

For `0 < re w` the function `u ↦ u ^ w` is continuous on the closed right half plane — at `0`
because the exponent has positive real part — hence on the spectrum of a positive operator. -/

/-- `X ^ w`, defined by the continuous functional calculus.  Only meaningful for `0 < re w`;
in the application `w = 1 + i z` with `Im z ≤ 0`. -/
noncomputable def cpowOp (X : H →L[ℂ] H) (w : ℂ) : H →L[ℂ] H := cfc (fun u : ℂ => u ^ w) X

namespace IsPowBase

variable {X : H →L[ℂ] H} {w w' : ℂ}

theorem continuousOn_cpow (h : IsPowBase X) (hw : 0 < w.re) :
    ContinuousOn (fun u : ℂ => u ^ w) (spectrum ℂ X) := fun _ hu =>
  (Complex.continuousAt_cpow_const_of_re_pos (Or.inl (h.spectrum_complex_re_nonneg hu))
    hw).continuousWithinAt

theorem cpowOp_one (h : IsPowBase X) : cpowOp X 1 = X := by
  have : (fun u : ℂ => u ^ (1 : ℂ)) = id := by ext u; simp
  rw [cpowOp, this, cfc_id ℂ X h.isStarNormal]

/-- The group law for the bounded powers. -/
theorem cpowOp_mul (h : IsPowBase X) (hw : 0 < w.re) (hw' : 0 < w'.re) :
    cpowOp X w * cpowOp X w' = cpowOp X (w + w') := by
  rw [cpowOp, cpowOp, ← cfc_mul _ _ X (h.continuousOn_cpow hw) (h.continuousOn_cpow hw')]
  refine cfc_congr fun _ hu => ?_
  obtain ⟨t, ht, rfl⟩ := h.spectrum_complex_repr hu
  rcases eq_or_lt_of_le ht.1 with hz | hz
  · have h0 : ((t : ℂ)) = 0 := by rw [← hz]; simp
    rw [h0, Complex.zero_cpow (by intro hc; simp [hc] at hw),
      Complex.zero_cpow (by intro hc; simp [hc] at hw'),
      Complex.zero_cpow (by
        intro hc
        have hre := congrArg Complex.re hc
        simp only [Complex.add_re, Complex.zero_re] at hre
        linarith)]
    ring
  · exact (Complex.cpow_add _ _ (by exact_mod_cast hz.ne')).symm

/-- `X^{\bar w} X^w` is a *real* continuous function of `X`: the modulus squared. -/
theorem star_cpowOp_mul_self (h : IsPowBase X) (hw : 0 < w.re) :
    star (cpowOp X w) * cpowOp X w = cfc (fun t : ℝ => t ^ (2 * w.re)) X := by
  have hc := h.continuousOn_cpow (w := w) hw
  have hcs : ContinuousOn (fun u : ℂ => star (u ^ w)) (spectrum ℂ X) := hc.star
  rw [cpowOp, ← cfc_star, ← cfc_mul _ _ X hcs hc]
  rw [cfc_complex_eq_real (f := fun u : ℂ => star (u ^ w) * u ^ w) X
    (fun u _ => by simp [star_mul, mul_comm]) h.isSelfAdjoint]
  refine cfc_congr fun t ht => ?_
  have ht0 : 0 ≤ t := (h.spectrum_real_subset ht).1
  have hnorm : ‖(t : ℂ) ^ w‖ = t ^ w.re :=
    Complex.norm_cpow_eq_rpow_re_of_nonneg ht0 hw.ne'
  have hre : (star ((t : ℂ) ^ w) * (t : ℂ) ^ w).re = ‖(t : ℂ) ^ w‖ ^ 2 := by
    rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_re]
  rw [hre, hnorm, ← Real.rpow_natCast (t ^ w.re) 2, ← Real.rpow_mul ht0]
  norm_num
  ring_nf

end IsPowBase

/-! ## The estimate `‖X^{1+iz} ζ‖ ≤ 2^{-Im z} ‖X ζ‖`

Everything rests on the pointwise inequality `t^{2 re w} ≤ 2^{2(re w − 1)} t²` on `[0,2]`,
transported by `cfc` monotonicity and read off with the quadratic form. -/

section Estimate

variable {X : H →L[ℂ] H} {w : ℂ}

/-- `‖A ζ‖² = ⟪A* A ζ, ζ⟫_ℝ`. -/
theorem norm_sq_eq_real_inner (A : H →L[ℂ] H) (ζ : H) :
    ‖A ζ‖ ^ 2 = inner ℝ ((star A * A) ζ) ζ := by
  rw [real_inner_eq_re_inner ℂ]
  have hstar : ((star A * A) ζ) = (ContinuousLinearMap.adjoint A) (A ζ) := by
    rw [ContinuousLinearMap.star_eq_adjoint]; rfl
  rw [hstar, ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]

omit [CompleteSpace H] in
/-- The real quadratic form is monotone in the operator. -/
theorem real_inner_le_of_le' {T S : H →L[ℂ] H} (hTS : T ≤ S) (ξ : H) :
    inner ℝ (T ξ) ξ ≤ inner ℝ (S ξ) ξ := by
  have hpos := (ContinuousLinearMap.le_def T S).1 hTS
  have h0 : (0 : ℝ) ≤ (S - T).reApplyInnerSelf ξ := hpos.2 ξ
  have he : (S - T).reApplyInnerSelf ξ = inner ℝ (S ξ) ξ - inner ℝ (T ξ) ξ := by
    show (inner ℝ ((S - T) ξ) ξ : ℝ) = _
    rw [sub_apply, inner_sub_left]
  linarith [he ▸ h0]

/-- The scalar inequality behind the estimate. -/
theorem rpow_le_of_mem_Icc {t r : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 2) (hr : 1 ≤ r) :
    t ^ (2 * r) ≤ ((2 : ℝ) ^ (r - 1)) ^ 2 * t ^ 2 := by
  obtain ⟨ht0, ht2⟩ := ht
  have hC : ((2 : ℝ) ^ (r - 1)) ^ 2 = (2 : ℝ) ^ (2 * r - 2) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (r - 1)) 2, ← Real.rpow_mul (by norm_num)]
    norm_num
    ring_nf
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h, Real.zero_rpow (by positivity)]
    positivity
  · have hsplit : t ^ (2 * r) = t ^ (2 : ℕ) * t ^ (2 * r - 2) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_add h]
      norm_num
    rw [hsplit, hC, mul_comm (((2 : ℝ)) ^ (2 * r - 2)) (t ^ (2 : ℕ))]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ht0 ht2 (by linarith)) (by positivity)

namespace IsPowBase

/-- `X^w` is bounded by `2^{re w − 1}` on the range of `X`.  This is the estimate that makes the
continuous extension possible. -/
theorem norm_cpowOp_apply_le (h : IsPowBase X) (hw : 1 ≤ w.re) (ζ : H) :
    ‖cpowOp X w ζ‖ ≤ (2 : ℝ) ^ (w.re - 1) * ‖X ζ‖ := by
  set C : ℝ := (2 : ℝ) ^ (w.re - 1) with hC
  have hC0 : 0 ≤ C := by positivity
  have hsq : cfc (fun t : ℝ => t ^ (2 * w.re)) X ≤ (C ^ 2 : ℝ) • (X * X) := by
    have hXX : (C ^ 2 : ℝ) • (X * X) = cfc (fun t : ℝ => C ^ 2 * t ^ (2 : ℕ)) X := by
      rw [cfc_const_mul (R := ℝ) _ _ X (by fun_prop),
        cfc_pow (R := ℝ) (fun t : ℝ => t) 2 X (by fun_prop) h.isSelfAdjoint,
        cfc_id' ℝ X h.isSelfAdjoint, pow_two X]
    rw [hXX]
    refine cfc_mono (fun t ht => rpow_le_of_mem_Icc (h.spectrum_real_subset ht) hw)
      (fun t _ => (Real.continuousAt_rpow_const t _ (Or.inr (by linarith))).continuousWithinAt)
      (by fun_prop)
  have hkey : ‖cpowOp X w ζ‖ ^ 2 ≤ (C * ‖X ζ‖) ^ 2 := by
    have h1 : ‖cpowOp X w ζ‖ ^ 2 = inner ℝ ((cfc (fun t : ℝ => t ^ (2 * w.re)) X) ζ) ζ := by
      rw [norm_sq_eq_real_inner, h.star_cpowOp_mul_self (by linarith)]
    have hXn : ‖X ζ‖ ^ 2 = inner ℝ ((X * X) ζ) ζ := by
      rw [norm_sq_eq_real_inner X ζ, h.isSelfAdjoint.star_eq]
    have h2 : inner ℝ (((C ^ 2 : ℝ) • (X * X)) ζ) ζ = C ^ 2 * ‖X ζ‖ ^ 2 := by
      have hsm : (((C ^ 2 : ℝ) • (X * X)) ζ) = (C ^ 2 : ℝ) • ((X * X) ζ) := rfl
      rw [hsm, real_inner_smul_left, hXn]
    rw [h1, mul_pow]
    calc inner ℝ ((cfc (fun t : ℝ => t ^ (2 * w.re)) X) ζ) ζ
        ≤ inner ℝ (((C ^ 2 : ℝ) • (X * X)) ζ) ζ := real_inner_le_of_le' hsq ζ
      _ = C ^ 2 * ‖X ζ‖ ^ 2 := h2
  nlinarith [norm_nonneg (cpowOp X w ζ), norm_nonneg (X ζ), mul_nonneg hC0 (norm_nonneg (X ζ))]

/-- For `re w = 1` — i.e. for `w = 1 + i z` with `z` real — the map `X ζ ↦ X^w ζ` is isometric. -/
theorem norm_cpowOp_apply (h : IsPowBase X) (hw : w.re = 1) (ζ : H) :
    ‖cpowOp X w ζ‖ = ‖X ζ‖ := by
  have hXX : cfc (fun t : ℝ => t ^ (2 * w.re)) X = X * X := by
    have : cfc (fun t : ℝ => t ^ (2 * w.re)) X = cfc (fun t : ℝ => t ^ (2 : ℕ)) X := by
      refine cfc_congr fun t ht => ?_
      have ht0 : 0 ≤ t := (h.spectrum_real_subset ht).1
      rw [hw, ← Real.rpow_natCast t 2]
      norm_num
    rw [this, cfc_pow (R := ℝ) (fun t : ℝ => t) 2 X (by fun_prop) h.isSelfAdjoint,
      cfc_id' ℝ X h.isSelfAdjoint, pow_two X]
  have hXn : ‖X ζ‖ ^ 2 = inner ℝ ((X * X) ζ) ζ := by
    rw [norm_sq_eq_real_inner X ζ, h.isSelfAdjoint.star_eq]
  have h1 : ‖cpowOp X w ζ‖ ^ 2 = ‖X ζ‖ ^ 2 := by
    rw [norm_sq_eq_real_inner, h.star_cpowOp_mul_self (by rw [hw]; norm_num), hXX, hXn]
  have := norm_nonneg (cpowOp X w ζ)
  have := norm_nonneg (X ζ)
  nlinarith

end IsPowBase

end Estimate

/-! ## `X^{iz}` by continuous extension

`X ζ ↦ X^{1+iz} ζ` is bounded by `2^{-Im z}` in `‖X ζ‖`, and `ran X` is dense; the extension is
`X^{iz}`. -/

/-- `X^{iz}`: the continuous extension of `X ζ ↦ X^{1+iz} ζ` off the dense subspace `ran X`.
Meaningful for `Im z ≤ 0`; unitary for `z` real. -/
noncomputable def opPow (X : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  LinearMap.extendOfNorm ((cpowOp X (1 + I * z) : H →L[ℂ] H) : H →ₗ[ℂ] H)
    ((X : H →L[ℂ] H) : H →ₗ[ℂ] H)

namespace IsPowBase

variable {X : H →L[ℂ] H} {z z' : ℂ}

theorem re_one_add_I_mul (z : ℂ) : (1 + I * z).re = 1 - z.im := by simp; ring

theorem one_le_re (hz : z.im ≤ 0) : 1 ≤ (1 + I * z).re := by
  rw [re_one_add_I_mul]; linarith

theorem exists_bound (h : IsPowBase X) (hz : z.im ≤ 0) :
    ∃ C : ℝ, ∀ ζ : H, ‖(cpowOp X (1 + I * z)) ζ‖ ≤ C * ‖X ζ‖ :=
  ⟨(2 : ℝ) ^ ((1 + I * z).re - 1), fun ζ => h.norm_cpowOp_apply_le (one_le_re hz) ζ⟩

/-- The defining property of `X^{iz}`. -/
theorem opPow_apply (h : IsPowBase X) (hz : z.im ≤ 0) (ζ : H) :
    opPow X z (X ζ) = cpowOp X (1 + I * z) ζ :=
  LinearMap.extendOfNorm_eq (f := ((cpowOp X (1 + I * z) : H →L[ℂ] H) : H →ₗ[ℂ] H))
    (e := ((X : H →L[ℂ] H) : H →ₗ[ℂ] H)) h.denseRange (h.exists_bound hz) ζ

/-- `X^{i·0} = 1`. -/
theorem opPow_zero (h : IsPowBase X) : opPow X 0 = 1 := by
  refine LinearMap.extendOfNorm_unique (f := ((cpowOp X (1 + I * (0:ℂ)) : H →L[ℂ] H) : H →ₗ[ℂ] H))
    (e := ((X : H →L[ℂ] H) : H →ₗ[ℂ] H)) h.denseRange 1 ?_ 1 ?_
  · intro ζ
    have hb := h.norm_cpowOp_apply (w := 1 + I * (0 : ℂ)) (by rw [re_one_add_I_mul]; simp) ζ
    simpa using hb.le
  · ext ζ
    simp [h.cpowOp_one]

/-- The estimate, transported to the extension. -/
theorem norm_opPow_apply_le (h : IsPowBase X) (hz : z.im ≤ 0) (ξ : H) :
    ‖opPow X z ξ‖ ≤ (2 : ℝ) ^ (-z.im) * ‖ξ‖ := by
  have := LinearMap.norm_extendOfNorm_apply_le
    (f := ((cpowOp X (1 + I * z) : H →L[ℂ] H) : H →ₗ[ℂ] H))
    (e := ((X : H →L[ℂ] H) : H →ₗ[ℂ] H)) h.denseRange ((2 : ℝ) ^ ((1 + I * z).re - 1))
    (fun ζ => h.norm_cpowOp_apply_le (one_le_re hz) ζ) ξ
  rw [re_one_add_I_mul] at this
  simpa [opPow] using this

/-- For real `z` the extension is isometric. -/
theorem norm_opPow_apply (h : IsPowBase X) (hz : z.im = 0) (ξ : H) :
    ‖opPow X z ξ‖ = ‖ξ‖ := by
  refine h.denseRange.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro ζ
  rw [h.opPow_apply (le_of_eq hz)]
  exact h.norm_cpowOp_apply (by rw [re_one_add_I_mul, hz]; ring) ζ

/-- `cfc` of `X` commutes with `X`. -/
theorem commute_cpowOp (h : IsPowBase X) (w : ℂ) : Commute (cpowOp X w) X :=
  Commute.cfc (Commute.refl X) (by rw [h.isSelfAdjoint.star_eq]; exact Commute.refl X) _

theorem cpowOp_apply_X (h : IsPowBase X) (w : ℂ) (ζ : H) :
    cpowOp X w (X ζ) = X (cpowOp X w ζ) := commute_apply (h.commute_cpowOp w) ζ

theorem isSelfAdjoint_mul_self (h : IsPowBase X) : IsSelfAdjoint (X * X) := by
  show star (X * X) = X * X
  rw [star_mul, h.isSelfAdjoint.star_eq]

theorem denseRange_mul_self (h : IsPowBase X) : DenseRange ⇑(X * X) :=
  denseRange_of_isSelfAdjoint_injective h.isSelfAdjoint_mul_self
    (fun _ _ hab => h.injective (h.injective hab))

/-- **The group law.** -/
theorem opPow_mul (h : IsPowBase X) (hz : z.im ≤ 0) (hz' : z'.im ≤ 0) :
    opPow X z * opPow X z' = opPow X (z + z') := by
  have hsum : (z + z').im ≤ 0 := by simp only [Complex.add_im]; linarith
  refine ContinuousLinearMap.ext fun ξ => ?_
  refine h.denseRange_mul_self.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro ζ
  have hXX : (X * X) ζ = X (X ζ) := rfl
  have hw : (0 : ℝ) < (1 + I * z).re := lt_of_lt_of_le one_pos (one_le_re hz)
  have hw' : (0 : ℝ) < (1 + I * z').re := lt_of_lt_of_le one_pos (one_le_re hz')
  have hws : (0 : ℝ) < (1 + I * (z + z')).re := lt_of_lt_of_le one_pos (one_le_re hsum)
  have hone : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have hleft : (opPow X z * opPow X z') ((X * X) ζ)
      = cpowOp X ((1 + I * z) + (1 + I * z')) ζ := by
    have e1 : (opPow X z * opPow X z') ((X * X) ζ) = opPow X z (opPow X z' (X (X ζ))) := rfl
    rw [e1, h.opPow_apply hz', h.cpowOp_apply_X, h.opPow_apply hz, ← h.cpowOp_mul hw hw']
    rfl
  have hright : opPow X (z + z') ((X * X) ζ)
      = cpowOp X ((1 + I * (z + z')) + 1) ζ := by
    have e2 : cpowOp X ((1 + I * (z + z')) + 1) = cpowOp X (1 + I * (z + z')) * cpowOp X 1 :=
      (h.cpowOp_mul hws hone).symm
    rw [hXX, h.opPow_apply hsum, e2, h.cpowOp_one]
    rfl
  rw [hleft, hright]
  congr 2
  ring

/-- For real `z`, `X^{iz}` is unitary. -/
theorem opPow_mem_unitary (h : IsPowBase X) (hz : z.im = 0) :
    opPow X z ∈ unitary (H →L[ℂ] H) := by
  have hstar : star (opPow X z) * opPow X z = 1 := by
    have h0 : ∀ ξ : H,
        (⟪((star (opPow X z) * opPow X z - 1 : H →L[ℂ] H) : H →ₗ[ℂ] H) ξ, ξ⟫ : ℂ) = 0 := by
      intro ξ
      show (⟪(star (opPow X z) * opPow X z - 1 : H →L[ℂ] H) ξ, ξ⟫ : ℂ) = 0
      rw [sub_apply, inner_sub_left, one_apply_eq_self]
      have h1 : ((star (opPow X z) * opPow X z) ξ) =
          (ContinuousLinearMap.adjoint (opPow X z)) (opPow X z ξ) := by
        rw [ContinuousLinearMap.star_eq_adjoint]; rfl
      rw [h1, ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K,
        inner_self_eq_norm_sq_to_K, h.norm_opPow_apply hz]
      ring
    have hlin := (inner_map_self_eq_zero _).1 h0
    have hA : (star (opPow X z) * opPow X z - 1 : H →L[ℂ] H) = 0 := by
      ext ξ
      simpa using DFunLike.congr_fun hlin ξ
    exact sub_eq_zero.1 hA
  have hnegz : (-z).im = 0 := by simp [hz]
  have hinv : opPow X z * opPow X (-z) = 1 := by
    rw [h.opPow_mul (le_of_eq hz) (le_of_eq hnegz)]
    simpa using h.opPow_zero
  refine ⟨hstar, ?_⟩
  have : star (opPow X z) = opPow X (-z) := by
    calc star (opPow X z) = star (opPow X z) * (opPow X z * opPow X (-z)) := by rw [hinv, mul_one]
      _ = (star (opPow X z) * opPow X z) * opPow X (-z) := by rw [mul_assoc]
      _ = opPow X (-z) := by rw [hstar, one_mul]
  rw [this, hinv]

end IsPowBase

/-! ## Strong continuity

`sup_{t ∈ (0,2]} t·|t^{iδ} − 1| ≤ 4|δ|` makes `s ↦ X^{1+is}` Lipschitz in operator norm; since
the `X^{is}` are isometries, uniform approximation on the dense `ran X` upgrades this to strong
continuity of `s ↦ X^{is}`. -/

section Continuity

/-- `t |log t| ≤ 2` on `[0,2]`: the only place the bound `2` on the spectrum is used
quantitatively. -/
theorem mul_abs_log_le {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) : t * |Real.log t| ≤ 2 := by
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]; simp
  rcases le_or_gt t 1 with h1 | h1
  · have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0 h1
    rw [abs_of_nonpos hlog]
    have hinv : Real.log t⁻¹ ≤ t⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at hinv
    have hmul : t * (-Real.log t) ≤ t * (t⁻¹ - 1) := by nlinarith
    have ht' : t * (t⁻¹ - 1) = 1 - t := by field_simp
    linarith
  · have hlog : 0 ≤ Real.log t := Real.log_nonneg h1.le
    rw [abs_of_nonneg hlog]
    have := Real.log_le_sub_one_of_pos h
    nlinarith

/-- `|e^{ix} − 1| ≤ 2|x|` for real `x`. -/
theorem norm_exp_mul_I_sub_one_le (x : ℝ) : ‖Complex.exp ((x : ℂ) * I) - 1‖ ≤ 2 * |x| := by
  rcases le_or_gt |x| 1 with hx | hx
  · have h1 : ‖((x : ℂ) * I)‖ ≤ 1 := by simpa using hx
    simpa using Complex.norm_exp_sub_one_le h1
  · have h2 : ‖Complex.exp ((x : ℂ) * I) - 1‖ ≤ ‖Complex.exp ((x : ℂ) * I)‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    rw [Complex.norm_exp_ofReal_mul_I] at h2
    simp only [norm_one] at h2
    linarith

theorem one_add_I_mul_ne_zero (r : ℝ) : (1 + I * (r : ℂ)) ≠ 0 := by
  intro hc
  have := congrArg Complex.re hc
  simp at this

/-- The scalar Lipschitz estimate: `|t^{1+is} − t^{1+is'}| ≤ 4 |s − s'|` on `[0,2]`. -/
theorem norm_cpow_sub_cpow_le {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (s s' : ℝ) :
    ‖(t : ℂ) ^ (1 + I * (s : ℂ)) - (t : ℂ) ^ (1 + I * (s' : ℂ))‖ ≤ 4 * |s - s'| := by
  rcases eq_or_lt_of_le ht0 with h | h
  · have h0 : ((t : ℂ)) = 0 := by rw [← h]; simp
    rw [h0, Complex.zero_cpow (one_add_I_mul_ne_zero s),
      Complex.zero_cpow (one_add_I_mul_ne_zero s')]
    simp only [sub_zero, norm_zero]
    positivity
  · set L := Real.log t with hL
    have htne : ((t : ℂ)) ≠ 0 := by exact_mod_cast h.ne'
    have hlog : Complex.log (t : ℂ) = (L : ℂ) := (Complex.ofReal_log ht0).symm
    have key : ∀ r : ℝ, (t : ℂ) ^ (1 + I * (r : ℂ)) = (t : ℂ) * Complex.exp (((L * r : ℝ) : ℂ) * I) := by
      intro r
      rw [Complex.cpow_def_of_ne_zero htne, hlog,
        show ((L : ℂ) * (1 + I * (r : ℂ))) = (L : ℂ) + ((L * r : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_add]
      congr 1
      rw [← Complex.ofReal_exp, Real.exp_log h]
    have hfac : Complex.exp (((L * s : ℝ) : ℂ) * I) - Complex.exp (((L * s' : ℝ) : ℂ) * I)
        = Complex.exp (((L * s' : ℝ) : ℂ) * I) *
          (Complex.exp (((L * (s - s') : ℝ) : ℂ) * I) - 1) := by
      rw [mul_sub, ← Complex.exp_add, mul_one]
      congr 2
      push_cast
      ring
    rw [key s, key s', ← mul_sub, hfac, norm_mul, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    have hbound := norm_exp_mul_I_sub_one_le (L * (s - s'))
    have hnt : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h]
    rw [hnt]
    have habs : |L * (s - s')| = |L| * |s - s'| := abs_mul _ _
    rw [habs] at hbound
    have hlt : t * ‖Complex.exp (((L * (s - s') : ℝ) : ℂ) * I) - 1‖
        ≤ t * (2 * (|L| * |s - s'|)) := by
      exact mul_le_mul_of_nonneg_left hbound h.le
    have hkey : t * (2 * (|L| * |s - s'|)) ≤ 4 * |s - s'| := by
      have h2 := mul_abs_log_le ht0 ht2
      have habs0 : (0 : ℝ) ≤ |s - s'| := abs_nonneg _
      nlinarith
    linarith

namespace IsPowBase

variable {X : H →L[ℂ] H}

theorem re_pos_of_real (s : ℝ) : (0 : ℝ) < (1 + I * (s : ℂ)).re := by
  rw [re_one_add_I_mul]; simp

/-- `s ↦ X^{1+is}` is Lipschitz in the operator norm. -/
theorem norm_cpowOp_sub_le (h : IsPowBase X) (s s' : ℝ) :
    ‖cpowOp X (1 + I * (s : ℂ)) - cpowOp X (1 + I * (s' : ℂ))‖ ≤ 4 * |s - s'| := by
  rw [cpowOp, cpowOp, ← cfc_sub _ _ X (h.continuousOn_cpow (re_pos_of_real s))
    (h.continuousOn_cpow (re_pos_of_real s'))]
  refine norm_cfc_le (by positivity) fun u hu => ?_
  obtain ⟨t, ht, rfl⟩ := h.spectrum_complex_repr hu
  exact norm_cpow_sub_cpow_le ht.1 ht.2 s s'

theorem lipschitzWith_cpowOp (h : IsPowBase X) :
    LipschitzWith 4 (fun s : ℝ => cpowOp X (1 + I * (s : ℂ))) := by
  refine LipschitzWith.of_dist_le_mul fun s s' => ?_
  rw [dist_eq_norm, Real.dist_eq]
  simpa using h.norm_cpowOp_sub_le s s'

theorem continuous_cpowOp (h : IsPowBase X) :
    Continuous (fun s : ℝ => cpowOp X (1 + I * (s : ℂ))) := h.lipschitzWith_cpowOp.continuous

/-- **Strong continuity** of the one-parameter group `s ↦ X^{is}`. -/
theorem continuous_opPow_apply (h : IsPowBase X) (ξ : H) :
    Continuous (fun s : ℝ => opPow X (s : ℂ) ξ) := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨ζ, hζ⟩ := h.denseRange.exists_dist_lt ξ hε
  refine ⟨fun s : ℝ => cpowOp X (1 + I * (s : ℂ)) ζ, ?_, fun s => ?_⟩
  · exact (ContinuousLinearMap.apply ℂ H ζ).continuous.comp h.continuous_cpowOp
  · refine hsub ?_
    have him : ((s : ℂ)).im = 0 := by simp
    have happ : opPow X (s : ℂ) (X ζ) = cpowOp X (1 + I * (s : ℂ)) ζ :=
      h.opPow_apply (le_of_eq him) ζ
    show dist (opPow X (s : ℂ) ξ) (cpowOp X (1 + I * (s : ℂ)) ζ) < ε
    rw [dist_eq_norm, ← happ, ← ContinuousLinearMap.map_sub, h.norm_opPow_apply him,
      ← dist_eq_norm]
    exact hζ

end IsPowBase

end Continuity

/-! ## Conjugation by `J`

`x ↦ J x J` is a *real* ⋆-algebra automorphism of `B(H)` — real, because `J` is conjugate
linear, so complex scalars come out conjugated — and it is isometric, hence continuous.  That is
exactly the input `StarAlgHom.map_cfc` wants, and it turns `RvD Prop. 3.1`, `J R = (2 − R) J`,
into `J f(R) J = f(2 − R)` for every continuous real `f`.

(`A/VN/TomitaTakesaki.lean` builds the same map under the name `adJ`, with the same definition.
The two files are **siblings**, not one downstream of the other: `TomitaTakesaki` imports
`Tomita`, which like this file imports only `StandardSubspace`.  They first meet at
`A/VN/TomitaFourier.lean`, where both are in scope and only `adJ` is used — `jConj` and
everything built on it below is unconsumed.  See `docs/DEAD-LIMBS.md` §5b and §8, which
proposes keeping the single copy in `StandardSubspace.lean`.  An earlier version of this note
said `TomitaTakesaki` was "downstream of this file"; it is not.  Corrected 2026-08-26.) -/

section Conjugation

variable (K : ClosedSubmodule ℝ H) (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤)

include hsep hcyc

/-- `J` as a real linear isometry. -/
noncomputable def Jisometry : H →ₗᵢ[ℝ] H :=
  ⟨(J K).toLinearMap, J_norm K hsep hcyc⟩

theorem real_inner_J_map_map (x y : H) : inner ℝ (J K x) (J K y) = inner ℝ x y :=
  (Jisometry K hsep hcyc).inner_map_map x y

/-- `J` is antiunitary: `⟪J x, J y⟫ = ⟪y, x⟫`. -/
theorem inner_J_map_map (x y : H) : (⟪J K x, J K y⟫ : ℂ) = ⟪y, x⟫ := by
  have hre : ∀ u v : H, (⟪u, v⟫ : ℂ).re = inner ℝ u v := by
    intro u v
    rw [real_inner_eq_re_inner ℂ, RCLike.re_eq_complex_re]
  refine Complex.ext ?_ ?_
  · rw [hre, hre, real_inner_J_map_map K hsep hcyc, real_inner_comm]
  · rw [im_inner, im_inner]
    have hJI : ((-I) : ℂ) • J K y = J K ((I : ℂ) • y) := by
      rw [J_smul_I K hsep hcyc]
      module
    rw [hJI, real_inner_J_map_map K hsep hcyc]
    have h1 := real_inner_smul_I (((-I) : ℂ) • x) y
    rw [smul_smul] at h1
    norm_num at h1
    have h2 : inner ℝ y (((-I) : ℂ) • x) = -inner ℝ ((I : ℂ) • x) y := by
      rw [show ((-I) : ℂ) • x = -((I : ℂ) • x) by module, inner_neg_right, real_inner_comm]
    rw [h2, h1]

/-- `J x J`, as a real-linear map. -/
noncomputable def jConjRe (x : H →L[ℂ] H) : H →L[ℝ] H :=
  (J K) ∘L (x.restrictScalars ℝ) ∘L (J K)

theorem jConjRe_smul_I (x : H →L[ℂ] H) (ζ : H) : jConjRe K x (I • ζ) =
    I • jConjRe K x ζ := by
  show J K (x (J K (I • ζ))) = I • J K (x (J K ζ))
  rw [J_smul_I K hsep hcyc, map_neg, map_smul, map_neg, J_smul_I K hsep hcyc, neg_neg]

/-- **`J x J`**, as a bounded `ℂ`-linear operator: it is `ℂ`-linear because two conjugations
compose. -/
noncomputable def jConj (x : H →L[ℂ] H) : H →L[ℂ] H where
  toFun := jConjRe K x
  map_add' := map_add _
  map_smul' := smul_complex_of_smul_I (jConjRe_smul_I K hsep hcyc x)
  cont := (jConjRe K x).continuous

@[simp] theorem jConj_apply (x : H →L[ℂ] H) (ζ : H) :
    jConj K hsep hcyc x ζ = J K (x (J K ζ)) := rfl

theorem J_apply_eq_jConj (x : H →L[ℂ] H) (ζ : H) :
    J K (x ζ) = jConj K hsep hcyc x (J K ζ) := by
  rw [jConj_apply, J_J K hsep hcyc]

theorem jConj_one : jConj K hsep hcyc 1 = 1 := by
  ext ζ; simp [J_J K hsep hcyc]

theorem jConj_mul (x y : H →L[ℂ] H) :
    jConj K hsep hcyc (x * y) = jConj K hsep hcyc x * jConj K hsep hcyc y := by
  ext ζ
  show J K ((x * y) (J K ζ)) = J K (x (J K (J K (y (J K ζ)))))
  rw [J_J K hsep hcyc]
  rfl

theorem jConj_add (x y : H →L[ℂ] H) :
    jConj K hsep hcyc (x + y) = jConj K hsep hcyc x + jConj K hsep hcyc y := by
  ext ζ
  show J K ((x + y) (J K ζ)) = J K (x (J K ζ)) + J K (y (J K ζ))
  show J K (x (J K ζ) + y (J K ζ)) = _
  rw [map_add]

theorem jConj_zero : jConj K hsep hcyc 0 = 0 := by
  ext ζ; simp

/-- Conjugation by `J` conjugates complex scalars. -/
theorem jConj_smul (c : ℂ) (x : H →L[ℂ] H) :
    jConj K hsep hcyc (c • x) = (starRingEnd ℂ) c • jConj K hsep hcyc x := by
  ext ζ
  show J K ((c • x) (J K ζ)) = (starRingEnd ℂ) c • J K (x (J K ζ))
  show J K (c • x (J K ζ)) = _
  rw [J_smul K hsep hcyc]

/-- `(J x J)* = J x* J`. -/
theorem jConj_star (x : H →L[ℂ] H) :
    jConj K hsep hcyc (star x) = star (jConj K hsep hcyc x) := by
  refine ContinuousLinearMap.ext fun ζ => ?_
  refine ext_inner_right ℂ fun η => ?_
  have hstar : ∀ (Y : H →L[ℂ] H) (u v : H), (⟪(star Y) u, v⟫ : ℂ) = ⟪u, Y v⟫ := by
    intro Y u v
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_left Y v u
  rw [hstar (jConj K hsep hcyc x) ζ η]
  show (⟪J K ((star x) (J K ζ)), η⟫ : ℂ) = ⟪ζ, J K (x (J K η))⟫
  calc (⟪J K ((star x) (J K ζ)), η⟫ : ℂ)
      = ⟪J K ((star x) (J K ζ)), J K (J K η)⟫ := by rw [J_J K hsep hcyc]
    _ = ⟪J K η, (star x) (J K ζ)⟫ := inner_J_map_map K hsep hcyc _ _
    _ = ⟪x (J K η), J K ζ⟫ := by
        have h := hstar (star x) (J K η) (J K ζ)
        rw [star_star] at h
        exact h.symm
    _ = ⟪J K (J K ζ), J K (x (J K η))⟫ := (inner_J_map_map K hsep hcyc _ _).symm
    _ = ⟪ζ, J K (x (J K η))⟫ := by rw [J_J K hsep hcyc]

theorem norm_jConj_le (x : H →L[ℂ] H) : ‖jConj K hsep hcyc x‖ ≤ ‖x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun ζ => ?_
  rw [jConj_apply, J_norm K hsep hcyc]
  calc ‖x (J K ζ)‖ ≤ ‖x‖ * ‖J K ζ‖ := x.le_opNorm _
    _ = ‖x‖ * ‖ζ‖ := by rw [J_norm K hsep hcyc]

/-- Conjugation by `J`, bundled as a *real* ⋆-algebra endomorphism of `B(H)`. -/
noncomputable def jConjHom : (H →L[ℂ] H) →⋆ₐ[ℝ] (H →L[ℂ] H) where
  toFun := jConj K hsep hcyc
  map_one' := jConj_one K hsep hcyc
  map_mul' := jConj_mul K hsep hcyc
  map_zero' := jConj_zero K hsep hcyc
  map_add' := jConj_add K hsep hcyc
  commutes' r := by
    ext ζ
    show J K ((algebraMap ℝ (H →L[ℂ] H) r) (J K ζ)) = (algebraMap ℝ (H →L[ℂ] H) r) ζ
    have hr : ∀ η : H, (algebraMap ℝ (H →L[ℂ] H) r) η = r • η := by
      intro η
      rw [Algebra.algebraMap_eq_smul_one]
      rfl
    rw [hr, hr, map_smul, J_J K hsep hcyc]
  map_star' := jConj_star K hsep hcyc

@[simp] theorem jConjHom_apply (x : H →L[ℂ] H) :
    jConjHom K hsep hcyc x = jConj K hsep hcyc x := rfl

theorem continuous_jConjHom : Continuous (jConjHom K hsep hcyc) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have hsub : jConj K hsep hcyc x - jConj K hsep hcyc y = jConj K hsep hcyc (x - y) := by
    have := jConj_add K hsep hcyc (x - y) y
    rw [sub_add_cancel] at this
    rw [this]
    abel
  show ‖jConj K hsep hcyc x - jConj K hsep hcyc y‖ ≤ ‖x - y‖
  rw [hsub]
  exact norm_jConj_le K hsep hcyc _

/-- **RvD Prop. 3.1 conjugated**: `J R J = 2 − R`. -/
theorem jConj_R : jConj K hsep hcyc (R K) = (2 : H →L[ℂ] H) - R K := by
  ext ζ
  show J K (R K (J K ζ)) = ((2 : H →L[ℂ] H) - R K) ζ
  rw [J_R K hsep hcyc, J_J K hsep hcyc]

theorem jConj_two_sub_R : jConj K hsep hcyc ((2 : H →L[ℂ] H) - R K) = R K := by
  have h1 : jConj K hsep hcyc (jConj K hsep hcyc (R K)) = R K := by
    ext ζ; simp [J_J K hsep hcyc]
  rw [← jConj_R K hsep hcyc]
  exact h1

/-- Conjugation by `J` intertwines the *real* continuous functional calculus of `R` with that of
`2 − R`. -/
theorem jConj_cfc_real {X Y : H →L[ℂ] H} (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y)
    (hXY : jConj K hsep hcyc X = Y) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ X)) :
    jConj K hsep hcyc (cfc f X) = cfc f Y := by
  have := StarAlgHom.map_cfc (R := ℝ) (S := ℝ) (jConjHom K hsep hcyc) f X hf
    (continuous_jConjHom K hsep hcyc) hX (by rw [jConjHom_apply, hXY]; exact hY)
  rw [jConjHom_apply, jConjHom_apply, hXY] at this
  exact this

end Conjugation

/-! ## `J X^w J = (J X J)^{\bar w}`

`cfc` transfers along the *real* ⋆-algebra map `x ↦ J x J`; complex-valued `cfc` is a real and an
imaginary part, and the conjugation flips the sign of the second.  That is `J`'s effect on the
exponent: `w ↦ \bar w`. -/

section ConjPow

/-- For `t ≥ 0`, `t^{\bar w} = \overline{t^w}`. -/
theorem cpow_conj_ofReal {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : w ≠ 0) :
    (t : ℂ) ^ (starRingEnd ℂ w) = starRingEnd ℂ ((t : ℂ) ^ w) := by
  have hwc : (starRingEnd ℂ) w ≠ 0 := by simpa using hw
  rcases eq_or_lt_of_le ht with h | h
  · have h0 : ((t : ℂ)) = 0 := by rw [← h]; simp
    rw [h0, Complex.zero_cpow hw, Complex.zero_cpow hwc]
    simp
  · have hne : ((t : ℂ)) ≠ 0 := by exact_mod_cast h.ne'
    rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne, ← Complex.exp_conj,
      ← Complex.ofReal_log ht, map_mul, Complex.conj_ofReal]

namespace IsPowBase

variable {X : H →L[ℂ] H} {w : ℂ}

/-- The real/imaginary decomposition of `X^w`. -/
theorem cpowOp_eq_re_add_im (h : IsPowBase X) (hw : 0 < w.re) :
    cpowOp X w = cfc (fun t : ℝ => ((t : ℂ) ^ w).re) X
      + I • cfc (fun t : ℝ => ((t : ℂ) ^ w).im) X := by
  have hcont : Continuous (fun t : ℝ => ((t : ℂ) ^ w)) :=
    Complex.continuous_ofReal_cpow_const hw
  have hc1 : Continuous (fun u : ℂ => ((((u.re : ℝ) : ℂ) ^ w).re : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp (hcont.comp Complex.continuous_re))
  have hc2 : Continuous (fun u : ℂ => ((((u.re : ℝ) : ℂ) ^ w).im : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp (hcont.comp Complex.continuous_re))
  have e1 : cfc (fun t : ℝ => ((t : ℂ) ^ w).re) X
      = cfc (fun u : ℂ => ((((u.re : ℝ) : ℂ) ^ w).re : ℂ)) X :=
    cfc_real_eq_complex _ h.isSelfAdjoint
  have e2 : I • cfc (fun t : ℝ => ((t : ℂ) ^ w).im) X
      = cfc (fun u : ℂ => I * ((((u.re : ℝ) : ℂ) ^ w).im : ℂ)) X := by
    rw [cfc_real_eq_complex (fun t : ℝ => ((t : ℂ) ^ w).im) h.isSelfAdjoint,
      cfc_const_mul (R := ℂ) I _ X hc2.continuousOn]
  have hadd : cfc (fun u : ℂ => ((((u.re : ℝ) : ℂ) ^ w).re : ℂ)) X
        + cfc (fun u : ℂ => I * ((((u.re : ℝ) : ℂ) ^ w).im : ℂ)) X
      = cfc (fun u : ℂ => ((((u.re : ℝ) : ℂ) ^ w).re : ℂ)
          + I * ((((u.re : ℝ) : ℂ) ^ w).im : ℂ)) X :=
    (cfc_add (R := ℂ) (a := X) _ _ hc1.continuousOn
      (continuous_const.mul hc2).continuousOn).symm
  rw [e1, e2, hadd]
  refine cfc_congr fun u hu => ?_
  obtain ⟨t, ht, rfl⟩ := h.spectrum_complex_repr hu
  simp only [Complex.ofReal_re]
  rw [mul_comm (I : ℂ)]
  exact (Complex.re_add_im _).symm

end IsPowBase

section ConjTransfer

variable (K : ClosedSubmodule ℝ H) (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤)

include hsep hcyc

/-- Conjugation by `J` turns `X^w` into `(J X J)^{\bar w}`. -/
theorem jConj_cpowOp {X Y : H →L[ℂ] H} (hX : IsPowBase X) (hY : IsPowBase Y)
    (hXY : jConj K hsep hcyc X = Y) {w : ℂ} (hw : 0 < w.re) :
    jConj K hsep hcyc (cpowOp X w) = cpowOp Y (starRingEnd ℂ w) := by
  have hw0 : w ≠ 0 := fun hc => by simp [hc] at hw
  have hwre : (starRingEnd ℂ w).re = w.re := Complex.conj_re w
  have hwpos : 0 < (starRingEnd ℂ w).re := by rw [hwre]; exact hw
  have hcont : Continuous (fun t : ℝ => ((t : ℂ) ^ w)) :=
    Complex.continuous_ofReal_cpow_const hw
  have hre1 : Continuous (fun t : ℝ => ((t : ℂ) ^ w).re) := Complex.continuous_re.comp hcont
  have him1 : Continuous (fun t : ℝ => ((t : ℂ) ^ w).im) := Complex.continuous_im.comp hcont
  rw [hX.cpowOp_eq_re_add_im hw, hY.cpowOp_eq_re_add_im hwpos, jConj_add, jConj_smul,
    jConj_cfc_real K hsep hcyc hX.isSelfAdjoint hY.isSelfAdjoint hXY _ hre1.continuousOn,
    jConj_cfc_real K hsep hcyc hX.isSelfAdjoint hY.isSelfAdjoint hXY _ him1.continuousOn]
  have hre : cfc (fun t : ℝ => ((t : ℂ) ^ (starRingEnd ℂ w)).re) Y
      = cfc (fun t : ℝ => ((t : ℂ) ^ w).re) Y := by
    refine cfc_congr fun t ht => ?_
    rw [cpow_conj_ofReal (hY.spectrum_real_subset ht).1 hw0]
    simp
  have him : cfc (fun t : ℝ => ((t : ℂ) ^ (starRingEnd ℂ w)).im) Y
      = -cfc (fun t : ℝ => ((t : ℂ) ^ w).im) Y := by
    rw [← cfc_neg (fun t : ℝ => ((t : ℂ) ^ w).im) Y]
    refine cfc_congr fun t ht => ?_
    rw [cpow_conj_ofReal (hY.spectrum_real_subset ht).1 hw0]
    simp
  rw [hre, him, Complex.conj_I]
  module

end ConjTransfer

end ConjPow

/-! ## Commuting powers of `X` and `Y` -/

namespace IsPowBase

variable {X Y : H →L[ℂ] H}

theorem commute_cpowOp_right (hX : IsPowBase X) (hcomm : Commute X Y) (v : ℂ) :
    Commute (cpowOp X v) Y :=
  Commute.cfc hcomm (by rw [hX.isSelfAdjoint.star_eq]; exact hcomm) _

theorem commute_cpowOp_cpowOp (hX : IsPowBase X) (hY : IsPowBase Y) (hcomm : Commute X Y)
    (v w : ℂ) : Commute (cpowOp X v) (cpowOp Y w) :=
  (Commute.cfc (hX.commute_cpowOp_right hcomm v).symm
    (by rw [hY.isSelfAdjoint.star_eq]; exact (hX.commute_cpowOp_right hcomm v).symm) _).symm

/-- Powers of two commuting bases commute. -/
theorem opPow_commute (hX : IsPowBase X) (hY : IsPowBase Y) (hcomm : Commute X Y)
    (hdense : DenseRange ⇑(X * Y)) {z z' : ℂ} (hz : z.im ≤ 0) (hz' : z'.im ≤ 0) :
    opPow X z * opPow Y z' = opPow Y z' * opPow X z := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  refine hdense.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro ζ
  have hXY : (X * Y) ζ = X (Y ζ) := rfl
  have hYX : (X * Y) ζ = Y (X ζ) := by
    rw [hXY]
    exact commute_apply hcomm ζ
  have e1 : (opPow X z * opPow Y z') ((X * Y) ζ)
      = cpowOp X (1 + I * z) (cpowOp Y (1 + I * z') ζ) := by
    show opPow X z (opPow Y z' ((X * Y) ζ)) = _
    rw [hYX, hY.opPow_apply hz',
      commute_apply (hY.commute_cpowOp_right hcomm.symm (1 + I * z')) ζ, hX.opPow_apply hz]
  have e2 : (opPow Y z' * opPow X z) ((X * Y) ζ)
      = cpowOp Y (1 + I * z') (cpowOp X (1 + I * z) ζ) := by
    show opPow Y z' (opPow X z ((X * Y) ζ)) = _
    rw [hXY, hX.opPow_apply hz,
      commute_apply (hX.commute_cpowOp_right hcomm (1 + I * z)) ζ, hY.opPow_apply hz']
  rw [e1, e2]
  exact commute_apply (hX.commute_cpowOp_cpowOp hY hcomm _ _) ζ

end IsPowBase

/-! ## The modular group `Δ^{it} = (2−R)^{it} R^{-it}` -/

section Modular

open Filter Topology

variable (K : ClosedSubmodule ℝ H)

/-- The modular group.  `Δ = (2 − R) R⁻¹` in RvD's parametrisation, so
`Δ^{it} = (2 − R)^{it} R^{-it}`; both factors are the bounded operators built above, so no
unbounded operator and no Borel functional calculus occurs. -/
noncomputable def modPow (K : ClosedSubmodule ℝ H) (s : ℝ) : H →L[ℂ] H :=
  opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ) * opPow (R K) (-(s : ℂ))

theorem modPow_apply (s : ℝ) (ξ : H) :
    modPow K s ξ = opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ) (opPow (R K) (-(s : ℂ)) ξ) := rfl

theorem isPowBase_R (hcyc : K ⊔ K.mulI = ⊤) : IsPowBase (R K) :=
  ⟨R_nonneg K, R_le_two K, R_injective K hcyc⟩

theorem isPowBase_two_sub_R (hsep : K ⊓ K.mulI = ⊥) : IsPowBase ((2 : H →L[ℂ] H) - R K) :=
  ⟨(ContinuousLinearMap.nonneg_iff_isPositive _).2 (two_sub_R_isPositive K),
    sub_le_self _ (R_nonneg K), two_sub_R_injective K hsep⟩

theorem commute_two_sub_R_R : Commute ((2 : H →L[ℂ] H) - R K) (R K) :=
  (commute_R_two_sub_R K).symm

variable (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤)

include hsep hcyc

theorem denseRange_two_sub_R_mul_R :
    DenseRange ⇑(((2 : H →L[ℂ] H) - R K) * R K) := by
  rw [(commute_two_sub_R_R K).eq]
  exact RtwoR_denseRange K hsep hcyc

/-- The two factors of `Δ^{it}` commute with each other. -/
theorem opPow_two_sub_R_commute {z z' : ℂ} (hz : z.im ≤ 0) (hz' : z'.im ≤ 0) :
    opPow ((2 : H →L[ℂ] H) - R K) z * opPow (R K) z'
      = opPow (R K) z' * opPow ((2 : H →L[ℂ] H) - R K) z :=
  (isPowBase_two_sub_R K hsep).opPow_commute (isPowBase_R K hcyc)
    (commute_two_sub_R_R K) (denseRange_two_sub_R_mul_R K hsep hcyc) hz hz'

theorem modPow_zero : modPow K 0 = 1 := by
  rw [modPow]
  simp only [Complex.ofReal_zero, neg_zero]
  rw [(isPowBase_two_sub_R K hsep).opPow_zero, (isPowBase_R K hcyc).opPow_zero, one_mul]

/-- **`Δ^{it}` is a one-parameter group.** -/
theorem modPow_add (s s' : ℝ) : modPow K s * modPow K s' = modPow K (s + s') := by
  have h0 : ∀ r : ℝ, ((r : ℂ)).im = 0 := fun r => by simp
  have hn : ∀ r : ℝ, (-(r : ℂ)).im = 0 := fun r => by simp
  rw [modPow, modPow, modPow]
  calc opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ) * opPow (R K) (-(s : ℂ))
        * (opPow ((2 : H →L[ℂ] H) - R K) (s' : ℂ) * opPow (R K) (-(s' : ℂ)))
      = opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ)
        * (opPow (R K) (-(s : ℂ)) * opPow ((2 : H →L[ℂ] H) - R K) (s' : ℂ))
        * opPow (R K) (-(s' : ℂ)) := by noncomm_ring
    _ = opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ)
        * (opPow ((2 : H →L[ℂ] H) - R K) (s' : ℂ) * opPow (R K) (-(s : ℂ)))
        * opPow (R K) (-(s' : ℂ)) := by
          rw [← opPow_two_sub_R_commute K hsep hcyc (le_of_eq (h0 s')) (le_of_eq (hn s))]
    _ = opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ) * opPow ((2 : H →L[ℂ] H) - R K) (s' : ℂ)
        * (opPow (R K) (-(s : ℂ)) * opPow (R K) (-(s' : ℂ))) := by noncomm_ring
    _ = opPow ((2 : H →L[ℂ] H) - R K) ((s : ℂ) + (s' : ℂ))
        * opPow (R K) (-(s : ℂ) + -(s' : ℂ)) := by
          rw [(isPowBase_two_sub_R K hsep).opPow_mul (le_of_eq (h0 s)) (le_of_eq (h0 s')),
            (isPowBase_R K hcyc).opPow_mul (le_of_eq (hn s)) (le_of_eq (hn s'))]
    _ = opPow ((2 : H →L[ℂ] H) - R K) (((s + s' : ℝ) : ℂ))
        * opPow (R K) (-((s + s' : ℝ) : ℂ)) := by
          congr 2 <;> push_cast <;> ring

/-- **`Δ^{it}` is unitary.** -/
theorem modPow_mem_unitary (s : ℝ) : modPow K s ∈ unitary (H →L[ℂ] H) :=
  mul_mem ((isPowBase_two_sub_R K hsep).opPow_mem_unitary (by simp))
    ((isPowBase_R K hcyc).opPow_mem_unitary (by simp))

theorem norm_modPow_apply (s : ℝ) (ξ : H) : ‖modPow K s ξ‖ = ‖ξ‖ := by
  rw [modPow_apply, (isPowBase_two_sub_R K hsep).norm_opPow_apply (by simp),
    (isPowBase_R K hcyc).norm_opPow_apply (by simp)]

omit hsep in
theorem continuous_opPow_R_neg (ξ : H) :
    Continuous (fun s : ℝ => opPow (R K) (-(s : ℂ)) ξ) := by
  have hc := (isPowBase_R K hcyc).continuous_opPow_apply ξ
  have hcomp : (fun s : ℝ => opPow (R K) (-(s : ℂ)) ξ)
      = (fun s : ℝ => opPow (R K) ((s : ℂ)) ξ) ∘ (fun s : ℝ => -s) := by
    funext s
    simp
  rw [hcomp]
  exact hc.comp continuous_neg

/-- **`Δ^{it}` is strongly continuous.** -/
theorem continuous_modPow_apply (ξ : H) : Continuous (fun s : ℝ => modPow K s ξ) := by
  set g : ℝ → H := fun s => opPow (R K) (-(s : ℂ)) ξ with hg
  have hgc : Continuous g := continuous_opPow_R_neg K hcyc ξ
  refine continuous_iff_continuousAt.2 fun s₀ => ?_
  have hsplit : ∀ s : ℝ, modPow K s ξ - modPow K s₀ ξ
      = (opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ) (g s₀)
          - opPow ((2 : H →L[ℂ] H) - R K) (s₀ : ℂ) (g s₀))
        + opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ) (g s - g s₀) := by
    intro s
    rw [modPow_apply, modPow_apply, ContinuousLinearMap.map_sub]
    abel
  have hA : Tendsto (fun s : ℝ => opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ) (g s₀)) (𝓝 s₀)
      (𝓝 (opPow ((2 : H →L[ℂ] H) - R K) (s₀ : ℂ) (g s₀))) :=
    ((isPowBase_two_sub_R K hsep).continuous_opPow_apply (g s₀)).continuousAt
  have h1 : Tendsto (fun s : ℝ => opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ) (g s₀)
      - opPow ((2 : H →L[ℂ] H) - R K) (s₀ : ℂ) (g s₀)) (𝓝 s₀) (𝓝 0) := by
    simpa using hA.sub (tendsto_const_nhds
      (x := opPow ((2 : H →L[ℂ] H) - R K) (s₀ : ℂ) (g s₀)))
  have h2 : Tendsto (fun s : ℝ => opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ) (g s - g s₀)) (𝓝 s₀)
      (𝓝 0) := by
    have hnorm : ∀ s : ℝ, ‖opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ) (g s - g s₀)‖
        = ‖g s - g s₀‖ := fun s => (isPowBase_two_sub_R K hsep).norm_opPow_apply (by simp) _
    refine squeeze_zero_norm (a := fun s : ℝ => ‖g s - g s₀‖) (fun s => le_of_eq (hnorm s)) ?_
    have hc : Tendsto (fun s : ℝ => g s - g s₀) (𝓝 s₀) (𝓝 0) := by
      have hcc : Tendsto (fun s : ℝ => g s - g s₀) (𝓝 s₀) (𝓝 (g s₀ - g s₀)) :=
        Filter.Tendsto.sub (hgc.continuousAt (x := s₀)) tendsto_const_nhds
      simpa using hcc
    simpa using hc.norm
  have h3 : Tendsto (fun s : ℝ => modPow K s ξ - modPow K s₀ ξ) (𝓝 s₀) (𝓝 0) := by
    simpa [hsplit] using h1.add h2
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  exact h3

/-! ### `Δ^{it}` commutes with `J` -/

/-- `J X^{is} = (J X J)^{-is} J`. -/
theorem J_opPow {X Y : H →L[ℂ] H} (hX : IsPowBase X) (hY : IsPowBase Y)
    (hXY : jConj K hsep hcyc X = Y) (s : ℝ) (ξ : H) :
    J K (opPow X (s : ℂ) ξ) = opPow Y (-(s : ℂ)) (J K ξ) := by
  refine hX.denseRange.induction_on ξ
    (isClosed_eq ((J K).continuous.comp (opPow X (s : ℂ)).continuous)
      ((opPow Y (-(s : ℂ))).continuous.comp (J K).continuous)) ?_
  intro ζ
  have him : ((s : ℂ)).im = 0 := by simp
  have himn : ((-(s : ℂ))).im = 0 := by simp
  have hJX : J K (X ζ) = Y (J K ζ) := by
    rw [J_apply_eq_jConj K hsep hcyc, hXY]
  have hexp : (starRingEnd ℂ) (1 + I * (s : ℂ)) = 1 + I * (-(s : ℂ)) := by
    simp
  rw [hX.opPow_apply (le_of_eq him), J_apply_eq_jConj K hsep hcyc,
    jConj_cpowOp K hsep hcyc hX hY hXY (IsPowBase.re_pos_of_real s), hexp, hJX,
    hY.opPow_apply (le_of_eq himn)]

/-- **`J Δ^{it} = Δ^{it} J`**: the modular group commutes with the conjugation. -/
theorem J_modPow (s : ℝ) (ξ : H) : J K (modPow K s ξ) = modPow K s (J K ξ) := by
  have hR := isPowBase_R K hcyc
  have hR' := isPowBase_two_sub_R K hsep
  have step1 : J K (opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ) (opPow (R K) (-(s : ℂ)) ξ))
      = opPow (R K) (-(s : ℂ)) (J K (opPow (R K) (-(s : ℂ)) ξ)) :=
    J_opPow K hsep hcyc hR' hR (jConj_two_sub_R K hsep hcyc) s _
  have step2 : J K (opPow (R K) (-(s : ℂ)) ξ)
      = opPow ((2 : H →L[ℂ] H) - R K) (s : ℂ) (J K ξ) := by
    have hJ := J_opPow K hsep hcyc hR hR' (jConj_R K hsep hcyc) (-s) ξ
    simpa using hJ
  rw [modPow_apply, step1, step2, modPow_apply]
  have hcomm := opPow_two_sub_R_commute K hsep hcyc (z := (s : ℂ)) (z' := -(s : ℂ))
    (by simp) (by simp)
  exact commute_apply (Commute.symm hcomm) (J K ξ)

/-- `Δ^{-it} = (Δ^{it})*`. -/
theorem star_modPow (s : ℝ) : star (modPow K s) = modPow K (-s) := by
  have hu := modPow_mem_unitary K hsep hcyc s
  have hinv : modPow K s * modPow K (-s) = 1 := by
    rw [modPow_add K hsep hcyc]
    simpa using modPow_zero K hsep hcyc
  calc star (modPow K s) = star (modPow K s) * (modPow K s * modPow K (-s)) := by
        rw [hinv, mul_one]
    _ = (star (modPow K s) * modPow K s) * modPow K (-s) := by rw [mul_assoc]
    _ = modPow K (-s) := by rw [hu.1, one_mul]

/-- **`J Δ^{it} J = Δ^{it}`**, the operator form of `J_modPow`. -/
theorem jConj_modPow (s : ℝ) : jConj K hsep hcyc (modPow K s) = modPow K s := by
  ext ζ
  show J K (modPow K s (J K ζ)) = modPow K s ζ
  rw [J_modPow K hsep hcyc s (J K ζ), J_J K hsep hcyc]

end Modular

end Theses.RvD
