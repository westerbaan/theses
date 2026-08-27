/-
**Rieffel–van Daele: the analyticity half of Lemma 3.6, and Lemma 4.7 — hence `J M J = M'`.**

  M. A. Rieffel and A. van Daele, *A bounded operator approach to
  Tomita–Takesaki theory*, Pacific J. Math. **69** (1977) 187–221, pp. 199 and 204.

**This file has no thesis counterpart.**  It supplies the last input to
`A/VN/TomitaFourier.lean`'s `tomita_JMJ_of_lemma_4_7`, and so completes the conjugation half
of Tomita's theorem along the route of `docs/COMMUTATION-THEOREM.md`.

## Part I — two scalar estimates

* `sq_mul_exp_le` : `x² e^{dx} ≤ 4/d²` for `d > 0`, `x ≤ 0` — one line from `1 + y ≤ e^y`,
  and the only thing that controls `t^c (log t)²` near `t = 0`.
* `norm_exp_sub_one_sub_self_le` : `‖e^b − 1 − b‖ ≤ 3‖b‖² e^{‖b‖}` for **every** complex `b`.
  Mathlib's `norm_exp_sub_one_sub_id_le` needs `‖b‖ ≤ 1`, which fails on the range
  `b = h log t` as `t → 0`; the large-`b` case is the triangle inequality.
* `norm_cpow_remainder_le` : hence
  `‖t^{w+h} − t^w − h t^w log t‖ ≤ 3(16/c² + e^{c+1}) ‖h‖²` uniformly for `t ∈ [0,2]`,
  where `c = Re w > 0` and `‖h‖ ≤ min(1, c/2)`.  Writing `t^w = e^{w log t}` turns the
  remainder into `e^{w log t}(e^{h log t} − 1 − h log t)`; the two cases `t ≤ 1`, `t > 1` are
  the two ways the exponents combine.

*A correction to the plan.*  The two scalar estimates recorded in
`docs/COMMUTATION-THEOREM.md` — `t^c |log t| ≤ 1/c` and `t^c (log t)² ≤ 4/c²` on `(0,2]` —
are **false on `(1,2]`**: at `t = 2, c = 1` the first reads `1.386 ≤ 1`, and at `t = 2, c = 3`
the second reads `3.84 ≤ 0.44`.  Both are true on `(0,1]` (the first is Mathlib's
`abs_log_mul_self_rpow_lt`), where the decay of `t^c` does the work; on `(1,2]` `t^c` *grows*
and any bound must grow with `c`.  So the remainder constant is not `2/(Re w)²` but
`3(16/c² + e^{c+1})`.  Nothing is lost: differentiability is a statement at a *fixed* `w`, so
a `w`-dependent constant is all that is ever needed.

## Part II — the derivative symbol

`u ↦ u^w log u` is continuous on `spectrum ℂ X`, including at `0`: `continuousOn_cpow_log`,
via `continuousOn_of_realRestrict` (every spectral point is a real number in `[0,2]`) and
`tendsto_log_mul_rpow_nhdsGT_zero`.

## Part III — holomorphy, RvD Lemma 3.6

`IsPowBase.hasDerivAt_cpowOp` : **`HasDerivAt (fun w ↦ cfc (·^w) X) (cfc (fun u ↦ u^w log u) X) w`
for `Re w > 0`**, in the operator norm.  The continuous functional calculus is isometric, so
`norm_cfc_le` turns Part I's uniform scalar bound into `‖remainder‖ ≤ M‖h‖²` and the
`IsLittleO` is immediate.

## Part IV — `X^w` on the closed half plane, and RvD Lemma 3.6's continuity clause

On the boundary `Re w = 0` the symbol `u ↦ u^w` is discontinuous at `0`, so `cfc` is
unavailable; `powExt X w := opPow X (-i w)` is `ModularGroup.lean`'s `extendOfNorm` device,
the continuous extension of `X ζ ↦ X^{1+w} ζ`.  `powExt_eq_cpowOp` identifies the two on
`Re w > 0`, `norm_powExt_apply_le` is `‖X^w‖ ≤ 2^{Re w}`, `powExt_mul`/`powExt_add_one` are
the bookkeeping, and `continuousOn_powExt_apply` is **strong continuity on `0 ≤ Re w ≤ 1`**:
uniform boundedness transports the norm continuity of `w ↦ X^{1+w}` (Part III) off the dense
`ran X`.  `continuousOn_apply_of_strong` is the same argument for a product.

## Part V — `R^{1/2}(2−R)^{1/2} = T`

`cpowOp_half_mul_eq_T`, by uniqueness of the positive square root: the product is positive
(`Commute.mul_nonneg`, the factors being real powers by `cpowOp_ofReal`) and squares to
`R(2−R)`.

## Part VI — the strip function

`stripOp K x z = R^{-z+1/2}(2−R)^{z+1/2} x R^{z+1/2}(2−R)^{-z+1/2}`, with
`continuousOn_stripOp_apply` on the closed strip, `differentiableAt_stripOpOpen` on the open
one (where `stripOp = stripOpOpen`, all four factors being plain `cfc`),
`norm_stripOp_apply_le` (`≤ 16‖x‖‖ξ‖`, since `|t^w| ≤ 2`), and the three evaluations
`stripOp_zero` (`= T x T`), `stripOp_right` and `stripOp_left`
(`= Δ^{it}(2−R)xRΔ^{-it}` and `= Δ^{it}RxΔ^{-it}(2−R)`).

## Part VII — RvD Lemma 4.7 and `J M J = M'`

`lemma_4_7` : Lemma 4.5 at `λ = e^{iφ/2}` produces `x ∈ M`; Lemma 4.6 applied to
`f z = ⟪η, stripOp x z ξ⟫` produces `⟪Tη, x (Tξ)⟫ = ∫ k(t) ⟪Tη, Δ^{it}Jx'JΔ^{-it}(Tξ)⟫ dt`
— the two `T`'s coming out by `commute_modPow_T` — and two density arguments in `ran T`
strip them off.  The density arguments need the kernel average `kInt` to be continuous in
each slot separately; `kInt_sub_left`/`kInt_sub_right` and `norm_kInt_le` give that.

`tomita_JMJ_unconditional`, `tomita_JM'J_unconditional` : **`J M J = M'` and `J M' J = M`**
for a von Neumann algebra `M` with `ω` cyclic and separating, with no remaining hypothesis.

*The convention trap.*  Mathlib's inner product is conjugate linear in the **first** slot, so
`z ↦ ⟪A(z)ξ, η⟫` is *anti*holomorphic; the function handed to `lemma_4_6` is `⟪η, A(z)ξ⟫`,
and the single conjugation needed at the very end is `integral_conj` (legitimate because the
RvD kernel is real).
-/
import Theses.A.VN.TomitaFourier

set_option linter.unusedSectionVars false

open Complex ClosedSubmodule Theses.A.VN
open scoped ComplexInnerProductSpace ComplexOrder

namespace Theses.RvD

/-! ## Part I: scalar estimates

The two facts that make the symbol `u ↦ u^w log u` continuous at `0` and the second-order
remainder `u^{w+h} - u^w - h u^w log u` quadratic in `h`, uniformly on `[0,2]`. -/

section Scalar

/-- `x² e^{d x} ≤ 4/d²` for `d > 0` and `x ≤ 0`: the maximum of `u ↦ u² e^{-du}` is
`4/(d²e²)`.  One line from `1 + y ≤ e^y`. -/
theorem sq_mul_exp_le {d x : ℝ} (hd : 0 < d) (hx : x ≤ 0) :
    x ^ 2 * Real.exp (d * x) ≤ 4 / d ^ 2 := by
  have h1 : d * (-x) / 2 ≤ Real.exp (d * (-x) / 2) := by
    have := Real.add_one_le_exp (d * (-x) / 2); linarith
  have h0 : 0 ≤ d * (-x) / 2 := by nlinarith
  have h2 : (d * (-x) / 2) ^ 2 ≤ Real.exp (d * (-x) / 2) ^ 2 := by nlinarith
  have h3 : Real.exp (d * (-x) / 2) ^ 2 = Real.exp (-(d * x)) := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [h3] at h2
  have hEE : Real.exp (-(d * x)) * Real.exp (d * x) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (d * x) := Real.exp_pos _
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg x, sq_nonneg d]

/-- `‖e^b - 1 - b‖ ≤ 3 ‖b‖² e^{‖b‖}` for every complex `b`: Mathlib's estimate for `‖b‖ ≤ 1`,
and the triangle inequality for `‖b‖ ≥ 1`. -/
theorem norm_exp_sub_one_sub_self_le (b : ℂ) :
    ‖Complex.exp b - 1 - b‖ ≤ 3 * ‖b‖ ^ 2 * Real.exp ‖b‖ := by
  have hexp : (1 : ℝ) ≤ Real.exp ‖b‖ := Real.one_le_exp (norm_nonneg b)
  rcases le_or_gt ‖b‖ 1 with hb | hb
  · have h := norm_exp_sub_one_sub_id_le hb
    nlinarith [sq_nonneg ‖b‖, norm_nonneg b]
  · have h1 : ‖Complex.exp b‖ ≤ Real.exp ‖b‖ := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.2 ((Complex.re_le_norm b))
    have h2 : ‖Complex.exp b - 1 - b‖ ≤ Real.exp ‖b‖ + 1 + ‖b‖ := by
      calc ‖Complex.exp b - 1 - b‖ ≤ ‖Complex.exp b - 1‖ + ‖b‖ := norm_sub_le _ _
        _ ≤ (‖Complex.exp b‖ + ‖(1 : ℂ)‖) + ‖b‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ Real.exp ‖b‖ + 1 + ‖b‖ := by simp only [norm_one]; linarith
    have h3 : 1 + ‖b‖ ≤ Real.exp ‖b‖ := by
      have := Real.add_one_le_exp ‖b‖; linarith
    have hb2 : (1 : ℝ) ≤ ‖b‖ ^ 2 := by nlinarith
    have h4 : Real.exp ‖b‖ ≤ ‖b‖ ^ 2 * Real.exp ‖b‖ := by
      nlinarith [Real.exp_pos ‖b‖]
    nlinarith [norm_nonneg b]

/-- `t^w = e^{(log t) w}` for `t > 0`. -/
theorem cpow_eq_exp_log {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (t : ℂ) ^ w = Complex.exp (((Real.log t : ℝ) : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne'), Complex.ofReal_log ht.le,
    mul_comm]

/-- **The uniform second-order remainder estimate.**  For `Re w > 0` and `‖h‖ ≤ min(1, Re w/2)`
the Taylor remainder of `t ↦ t^w` in the exponent is `O(‖h‖²)`, uniformly for `t ∈ [0,2]`. -/
theorem norm_cpow_remainder_le {w h : ℂ} (hw : 0 < w.re) (hh1 : ‖h‖ ≤ 1)
    (hh2 : ‖h‖ ≤ w.re / 2) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    ‖(t : ℂ) ^ (w + h) - (t : ℂ) ^ w - h * ((t : ℂ) ^ w * Complex.log (t : ℂ))‖
      ≤ 3 * (16 / w.re ^ 2 + Real.exp (w.re + 1)) * ‖h‖ ^ 2 := by
  have hMnn : (0 : ℝ) ≤ 3 * (16 / w.re ^ 2 + Real.exp (w.re + 1)) := by positivity
  have hhre : |h.re| ≤ ‖h‖ := Complex.abs_re_le_norm h
  rcases eq_or_lt_of_le ht0 with rfl | ht
  · have hwne : w ≠ 0 := fun hc => by rw [hc] at hw; simp at hw
    have hwhne : w + h ≠ 0 := by
      intro hc
      have hre : w.re + h.re = 0 := by
        have : (w + h).re = 0 := by rw [hc]; simp
        simpa using this
      have := abs_le.1 hhre
      linarith
    have h0 : ((0 : ℝ) : ℂ) = 0 := Complex.ofReal_zero
    rw [h0, Complex.zero_cpow hwne, Complex.zero_cpow hwhne]
    simpa using mul_nonneg hMnn (sq_nonneg ‖h‖)
  · set x : ℝ := Real.log t with hxdef
    have hxlt : x < 1 := by
      have h2 : x ≤ Real.log 2 := Real.log_le_log ht ht2
      have := Real.log_two_lt_d9
      linarith
    have hid : (t : ℂ) ^ (w + h) - (t : ℂ) ^ w - h * ((t : ℂ) ^ w * Complex.log (t : ℂ))
        = Complex.exp ((x : ℂ) * w) * (Complex.exp ((x : ℂ) * h) - 1 - (x : ℂ) * h) := by
      rw [cpow_eq_exp_log ht, cpow_eq_exp_log ht, ← Complex.ofReal_log ht.le,
        show ((x : ℂ) * (w + h)) = (x : ℂ) * w + (x : ℂ) * h by ring, Complex.exp_add]
      ring
    have hnorm1 : ‖Complex.exp ((x : ℂ) * w)‖ = Real.exp (x * w.re) := by
      rw [Complex.norm_exp]; congr 1; simp
    have hnorm2 : ‖(x : ℂ) * h‖ = |x| * ‖h‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb := norm_exp_sub_one_sub_self_le ((x : ℂ) * h)
    rw [hnorm2] at hb
    have hkey : x ^ 2 * Real.exp (x * w.re + |x| * ‖h‖)
        ≤ 16 / w.re ^ 2 + Real.exp (w.re + 1) := by
      rcases le_or_gt x 0 with hxs | hxs
      · have habs : |x| = -x := abs_of_nonpos hxs
        have hle : x * w.re + |x| * ‖h‖ ≤ w.re / 2 * x := by
          rw [habs]
          nlinarith
        have h1 : Real.exp (x * w.re + |x| * ‖h‖) ≤ Real.exp (w.re / 2 * x) :=
          Real.exp_le_exp.2 hle
        have h2 : x ^ 2 * Real.exp (w.re / 2 * x) ≤ 4 / (w.re / 2) ^ 2 :=
          sq_mul_exp_le (by linarith) hxs
        have h3 : (4 : ℝ) / (w.re / 2) ^ 2 = 16 / w.re ^ 2 := by
          field_simp; ring
        have h4 : x ^ 2 * Real.exp (x * w.re + |x| * ‖h‖) ≤ x ^ 2 * Real.exp (w.re / 2 * x) := by
          exact mul_le_mul_of_nonneg_left h1 (sq_nonneg x)
        have := Real.exp_pos (w.re + 1)
        linarith [h3 ▸ h2]
      · have habs : |x| = x := abs_of_pos hxs
        have hle : x * w.re + |x| * ‖h‖ ≤ w.re + 1 := by
          rw [habs]
          nlinarith [norm_nonneg h]
        have h1 : Real.exp (x * w.re + |x| * ‖h‖) ≤ Real.exp (w.re + 1) :=
          Real.exp_le_exp.2 hle
        have h2 : x ^ 2 ≤ 1 := by nlinarith
        have hep : (0 : ℝ) < Real.exp (x * w.re + |x| * ‖h‖) := Real.exp_pos _
        have : x ^ 2 * Real.exp (x * w.re + |x| * ‖h‖) ≤ 1 * Real.exp (w.re + 1) := by
          apply mul_le_mul h2 h1 (le_of_lt hep) (by norm_num)
        have hpos : (0 : ℝ) ≤ 16 / w.re ^ 2 := by positivity
        linarith
    rw [hid, norm_mul, hnorm1]
    have hex : (0 : ℝ) < Real.exp (x * w.re) := Real.exp_pos _
    calc Real.exp (x * w.re) * ‖Complex.exp ((x : ℂ) * h) - 1 - (x : ℂ) * h‖
        ≤ Real.exp (x * w.re) * (3 * (|x| * ‖h‖) ^ 2 * Real.exp (|x| * ‖h‖)) :=
          mul_le_mul_of_nonneg_left hb (le_of_lt hex)
      _ = 3 * ‖h‖ ^ 2 * (x ^ 2 * Real.exp (x * w.re + |x| * ‖h‖)) := by
          rw [Real.exp_add, mul_pow, sq_abs]
          ring
      _ ≤ 3 * ‖h‖ ^ 2 * (16 / w.re ^ 2 + Real.exp (w.re + 1)) := by
          exact mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 3 * (16 / w.re ^ 2 + Real.exp (w.re + 1)) * ‖h‖ ^ 2 := by ring

end Scalar

/-! ## Part II: the symbol `u ↦ u^w log u`

The derivative of `w ↦ cfc (·^w) X` is `cfc (fun u => u^w log u) X`, and the first thing to
check is that this symbol is continuous on the spectrum — including at `0`, where
`t^{Re w} |log t| → 0`. -/

section Symbol

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsPowBase

variable {X : H →L[ℂ] H} {w : ℂ}

/-- Every point of the spectrum is a real number in `[0,2]`, so continuity of a symbol on
`spectrum ℂ X` is continuity of its restriction to `[0,2]`. -/
theorem continuousOn_of_realRestrict (h : IsPowBase X) {g : ℂ → ℂ} {F : ℝ → ℂ}
    (hF : ContinuousOn F (Set.Icc 0 2))
    (hgF : ∀ t ∈ Set.Icc (0 : ℝ) 2, g (t : ℂ) = F t) :
    ContinuousOn g (spectrum ℂ X) := by
  have hre : ∀ u ∈ spectrum ℂ X, u.re ∈ Set.Icc (0 : ℝ) 2 ∧ u = ((u.re : ℝ) : ℂ) := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := h.spectrum_complex_repr hu
    simpa using ht
  have hcomp : ContinuousOn (fun u : ℂ => F u.re) (spectrum ℂ X) :=
    hF.comp Complex.continuous_re.continuousOn (fun u hu => (hre u hu).1)
  refine hcomp.congr fun u hu => ?_
  obtain ⟨h1, h2⟩ := hre u hu
  calc g u = g ((u.re : ℝ) : ℂ) := by rw [← h2]
    _ = F u.re := hgF _ h1

/-- The symbol `t ↦ t^w log t` is continuous on `[0,2]`; the only issue is `t = 0`, where
`t^{Re w}|log t| → 0`. -/
theorem continuousOn_realSymbol (hw : 0 < w.re) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ w * ((Real.log t : ℝ) : ℂ)) (Set.Icc 0 2) := by
  set F : ℝ → ℂ := fun t : ℝ => (t : ℂ) ^ w * ((Real.log t : ℝ) : ℂ) with hFdef
  have hwne : w ≠ 0 := fun hc => by rw [hc] at hw; simp at hw
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hzero | htp
  · -- the origin
    have ht0 : t = 0 := hzero.symm
    subst ht0
    have hF0 : F 0 = 0 := by simp [hFdef, Complex.zero_cpow hwne]
    rw [← Set.Ioc_insert_left (a := (2 : ℝ)) (b := (0 : ℝ)) (by norm_num)]
    rw [continuousWithinAt_insert_self, ContinuousWithinAt, hF0]
    refine Filter.Tendsto.mono_left ?_ (nhdsWithin_mono _ Set.Ioc_subset_Ioi_self)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim := (tendsto_log_mul_rpow_nhdsGT_zero (r := w.re) hw).abs
    simp only [abs_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [hFdef]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_nonneg hu0.le hw.ne']
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
    ring
  · -- an interior or right-endpoint point
    refine ContinuousAt.continuousWithinAt ?_
    have hcp : ContinuousAt (fun u : ℂ => u ^ w) ((t : ℝ) : ℂ) :=
      Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simpa using htp.le)) hw
    have h1 : ContinuousAt (fun t : ℝ => ((t : ℝ) : ℂ) ^ w) t :=
      hcp.comp (Complex.continuous_ofReal.continuousAt (x := t))
    have h2 : ContinuousAt (fun t : ℝ => ((Real.log t : ℝ) : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log htp.ne')
    exact h1.mul h2

/-- The derivative symbol is continuous on the spectrum. -/
theorem continuousOn_cpow_log (h : IsPowBase X) (hw : 0 < w.re) :
    ContinuousOn (fun u : ℂ => u ^ w * Complex.log u) (spectrum ℂ X) := by
  refine h.continuousOn_of_realRestrict (continuousOn_realSymbol hw) fun t ht => ?_
  rw [Complex.ofReal_log ht.1]

end IsPowBase

end Symbol

/-! ## Part III: holomorphy of `w ↦ X^w` on `Re w > 0`

**RvD Lemma 3.6, the analyticity clause.**  The continuous functional calculus is isometric
(`norm_cfc_le`), so the operator-norm remainder is the sup of the scalar remainder over the
spectrum, and Part I bounds that by `O(‖k‖²)`. -/

section Holomorphy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsPowBase

variable {X : H →L[ℂ] H} {w : ℂ}

/-- The operator-valued remainder is the functional calculus of the scalar remainder. -/
theorem cpowOp_remainder (h : IsPowBase X) (hw : 0 < w.re) {k : ℂ} (hk : ‖k‖ ≤ w.re / 2) :
    cpowOp X (w + k) - cpowOp X w - k • cfc (fun u : ℂ => u ^ w * Complex.log u) X
      = cfc (fun u : ℂ => u ^ (w + k) - u ^ w - k * (u ^ w * Complex.log u)) X := by
  have hwk : 0 < (w + k).re := by
    have := abs_le.1 (Complex.abs_re_le_norm k)
    simp only [Complex.add_re]
    linarith
  have hc1 : ContinuousOn (fun u : ℂ => u ^ (w + k)) (spectrum ℂ X) := h.continuousOn_cpow hwk
  have hc2 : ContinuousOn (fun u : ℂ => u ^ w) (spectrum ℂ X) := h.continuousOn_cpow hw
  have hc3 : ContinuousOn (fun u : ℂ => u ^ w * Complex.log u) (spectrum ℂ X) :=
    h.continuousOn_cpow_log hw
  have e1 : cfc (fun u : ℂ => u ^ (w + k) - u ^ w - k * (u ^ w * Complex.log u)) X
      = cfc (fun u : ℂ => u ^ (w + k) - u ^ w) X
        - cfc (fun u : ℂ => k * (u ^ w * Complex.log u)) X :=
    cfc_sub (fun u : ℂ => u ^ (w + k) - u ^ w) (fun u : ℂ => k * (u ^ w * Complex.log u)) X
      (hc1.sub hc2) (continuousOn_const.mul hc3)
  have e2 : cfc (fun u : ℂ => u ^ (w + k) - u ^ w) X
      = cfc (fun u : ℂ => u ^ (w + k)) X - cfc (fun u : ℂ => u ^ w) X :=
    cfc_sub (fun u : ℂ => u ^ (w + k)) (fun u : ℂ => u ^ w) X hc1 hc2
  have e3 : cfc (fun u : ℂ => k * (u ^ w * Complex.log u)) X
      = k • cfc (fun u : ℂ => u ^ w * Complex.log u) X :=
    cfc_const_mul k (fun u : ℂ => u ^ w * Complex.log u) X hc3
  simp only [cpowOp]
  rw [e1, e2, e3]

/-- **The derivative of `w ↦ X^w` is `X^w log X`**, for `Re w > 0`. -/
theorem hasDerivAt_cpowOp (h : IsPowBase X) (hw : 0 < w.re) :
    HasDerivAt (fun v : ℂ => cpowOp X v) (cfc (fun u : ℂ => u ^ w * Complex.log u) X) w := by
  set M : ℝ := 3 * (16 / w.re ^ 2 + Real.exp (w.re + 1)) with hM
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hrem : ∀ k : ℂ, ‖k‖ ≤ 1 → ‖k‖ ≤ w.re / 2 →
      ‖cpowOp X (w + k) - cpowOp X w - k • cfc (fun u : ℂ => u ^ w * Complex.log u) X‖
        ≤ M * ‖k‖ ^ 2 := by
    intro k hk1 hk2
    rw [h.cpowOp_remainder hw hk2]
    refine norm_cfc_le (by positivity) fun u hu => ?_
    obtain ⟨t, ht, rfl⟩ := h.spectrum_complex_repr hu
    exact norm_cpow_remainder_le hw hk1 hk2 ht.1 ht.2
  have hsmall : ∀ r : ℝ, 0 < r → ∀ᶠ k : ℂ in nhds (0 : ℂ), ‖k‖ ≤ r := by
    intro r hr
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with k hk
    exact le_of_lt (by simpa [dist_eq_norm] using hk)
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [hsmall 1 one_pos, hsmall (w.re / 2) (by linarith),
    hsmall (ε / (M + 1)) (by positivity)] with k hk1 hk2 hk3
  have hk0 : (0 : ℝ) ≤ ‖k‖ := norm_nonneg k
  have hMk : M * ‖k‖ ≤ ε := by
    have h1 : M * ‖k‖ ≤ M * (ε / (M + 1)) := by
      exact mul_le_mul_of_nonneg_left hk3 hM0
    have h2 : M * (ε / (M + 1)) ≤ ε := by
      rw [mul_div_assoc'] at h1 ⊢
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  calc ‖cpowOp X (w + k) - cpowOp X w - k • cfc (fun u : ℂ => u ^ w * Complex.log u) X‖
      ≤ M * ‖k‖ ^ 2 := hrem k hk1 hk2
    _ = (M * ‖k‖) * ‖k‖ := by ring
    _ ≤ ε * ‖k‖ := mul_le_mul_of_nonneg_right hMk hk0

/-- `w ↦ X^w` is differentiable on the open right half plane. -/
theorem differentiableAt_cpowOp (h : IsPowBase X) (hw : 0 < w.re) :
    DifferentiableAt ℂ (fun v : ℂ => cpowOp X v) w :=
  (h.hasDerivAt_cpowOp hw).differentiableAt

/-- `w ↦ X^w` is norm continuous on the open right half plane. -/
theorem continuousAt_cpowOp (h : IsPowBase X) (hw : 0 < w.re) :
    ContinuousAt (fun v : ℂ => cpowOp X v) w :=
  (h.hasDerivAt_cpowOp hw).continuousAt

end IsPowBase

end Holomorphy

/-! ## Part IV: `X^w` on the closed half plane `Re w ≥ 0`

**RvD Lemma 3.6, the continuity clause.**  On the boundary `Re w = 0` the symbol `u ↦ u^w` is
discontinuous at `0`, so `cfc` is unavailable and `X^w` is the `LinearMap.extendOfNorm`
device of `A/VN/ModularGroup.lean`: `powExt X w := opPow X (-i w)` is the continuous
extension of `X ζ ↦ X^{1+w} ζ`.  It agrees with `cpowOp X w` when `Re w > 0`, is bounded by
`2^{Re w}`, and is *strongly* continuous in `w` — the last because the `X^w` are uniformly
bounded on `0 ≤ Re w ≤ 1` and `w ↦ X^{1+w}` is norm continuous by Part III. -/

section PowExt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `X^w` for `Re w ≥ 0`: the continuous extension of `X ζ ↦ X^{1+w} ζ`, i.e. `opPow X (-i w)`
in the parametrisation of `A/VN/ModularGroup.lean`. -/
noncomputable def powExt (X : H →L[ℂ] H) (w : ℂ) : H →L[ℂ] H := opPow X (-I * w)

/-- The strip `0 ≤ Re w ≤ 1` on which the four exponents of RvD Lemma 4.7 live. -/
def powStrip : Set ℂ := {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1}

@[simp] lemma mem_powStrip {w : ℂ} : w ∈ powStrip ↔ 0 ≤ w.re ∧ w.re ≤ 1 := Iff.rfl

lemma neg_I_mul_I_mul (z : ℂ) : -I * (I * z) = z := by
  have : -I * (I * z) = -(I * I) * z := by ring
  rw [this, Complex.I_mul_I]
  ring

namespace IsPowBase

variable {X : H →L[ℂ] H} {w w' : ℂ}

lemma im_neg_I_mul (w : ℂ) : (-I * w).im = -w.re := by simp

lemma im_neg_I_mul_nonpos (hw : 0 ≤ w.re) : (-I * w).im ≤ 0 := by
  rw [im_neg_I_mul]; linarith

lemma one_add_I_mul_neg_I_mul (w : ℂ) : 1 + I * (-I * w) = 1 + w := by
  have : I * (-I * w) = -(I * I) * w := by ring
  rw [this, Complex.I_mul_I]
  ring

/-- The defining property: `X^w (X ζ) = X^{1+w} ζ`. -/
theorem powExt_apply (h : IsPowBase X) (hw : 0 ≤ w.re) (ζ : H) :
    powExt X w (X ζ) = cpowOp X (1 + w) ζ := by
  rw [powExt, h.opPow_apply (im_neg_I_mul_nonpos hw), one_add_I_mul_neg_I_mul]

/-- `‖X^w ξ‖ ≤ 2^{Re w} ‖ξ‖`. -/
theorem norm_powExt_apply_le (h : IsPowBase X) (hw : 0 ≤ w.re) (ξ : H) :
    ‖powExt X w ξ‖ ≤ (2 : ℝ) ^ w.re * ‖ξ‖ := by
  have := h.norm_opPow_apply_le (z := -I * w) (im_neg_I_mul_nonpos hw) ξ
  rwa [im_neg_I_mul, neg_neg] at this

/-- On `0 ≤ Re w ≤ 1` all the `X^w` are contractions up to the factor `2`. -/
theorem norm_powExt_apply_le_two (h : IsPowBase X) (hw : w ∈ powStrip) (ξ : H) :
    ‖powExt X w ξ‖ ≤ 2 * ‖ξ‖ := by
  refine le_trans (h.norm_powExt_apply_le hw.1 ξ) ?_
  have : (2 : ℝ) ^ w.re ≤ (2 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hw.2
  rw [Real.rpow_one] at this
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

/-- The group law on the closed half plane. -/
theorem powExt_mul (h : IsPowBase X) (hw : 0 ≤ w.re) (hw' : 0 ≤ w'.re) :
    powExt X w * powExt X w' = powExt X (w + w') := by
  rw [powExt, powExt, powExt, h.opPow_mul (im_neg_I_mul_nonpos hw) (im_neg_I_mul_nonpos hw')]
  congr 1
  ring

/-- **Inside the open half plane `X^w` is the plain continuous functional calculus.** -/
theorem powExt_eq_cpowOp (h : IsPowBase X) (hw : 0 < w.re) : powExt X w = cpowOp X w := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  refine h.denseRange.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro ζ
  rw [h.powExt_apply (le_of_lt hw)]
  have : cpowOp X w (X ζ) = (cpowOp X w * cpowOp X 1) ζ := by rw [h.cpowOp_one]; rfl
  rw [this, h.cpowOp_mul hw (by norm_num), add_comm]

/-- `X^1 = X`. -/
theorem powExt_one (h : IsPowBase X) : powExt X 1 = X := by
  rw [h.powExt_eq_cpowOp (by norm_num), h.cpowOp_one]

/-- `X^{w+1} = X^w X`. -/
theorem powExt_add_one (h : IsPowBase X) (hw : 0 ≤ w.re) :
    powExt X (w + 1) = powExt X w * X := by
  rw [← h.powExt_mul hw (w' := 1) (by norm_num), h.powExt_one]

/-- `X^{i t} = X^{it}` in the `opPow` parametrisation. -/
theorem powExt_I_mul (X : H →L[ℂ] H) (t : ℝ) : powExt X (I * (t : ℂ)) = opPow X (t : ℂ) := by
  rw [powExt, neg_I_mul_I_mul]

end IsPowBase

/-! ### Strong continuity in the exponent -/

namespace IsPowBase

variable {X : H →L[ℂ] H} {w : ℂ}

/-- **RvD Lemma 3.6, the continuity clause.**  `w ↦ X^w ξ` is continuous on `0 ≤ Re w ≤ 1`.
Uniform boundedness (`norm_powExt_apply_le_two`) transfers the norm continuity of
`w ↦ X^{1+w}` (Part III) off the dense range of `X`. -/
theorem continuousOn_powExt_apply (h : IsPowBase X) (ξ : H) :
    ContinuousOn (fun w : ℂ => powExt X w ξ) powStrip := by
  rw [Metric.continuousOn_iff]
  intro w₀ hw₀ ε hε
  obtain ⟨ζ, hζ⟩ : ∃ ζ : H, ‖ξ - X ζ‖ < ε / 8 := by
    obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 (h.denseRange ξ) (ε / 8) (by positivity)
    obtain ⟨ζ, rfl⟩ := hy
    exact ⟨ζ, by rwa [dist_eq_norm] at hd⟩
  have hg : ContinuousAt (fun v : ℂ => cpowOp X (1 + v) ζ) w₀ := by
    have h1 : ContinuousAt (fun v : ℂ => cpowOp X v) (1 + w₀) := by
      refine h.continuousAt_cpowOp ?_
      have := hw₀.1
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have h2 : ContinuousAt (fun v : ℂ => (1 : ℂ) + v) w₀ := by fun_prop
    exact ((ContinuousLinearMap.apply ℂ H ζ).continuous.continuousAt).comp (h1.comp h2)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hg (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun w hw hdist => ?_⟩
  have e1 : powExt X w ξ - powExt X w₀ ξ
      = powExt X w (ξ - X ζ) + (powExt X w (X ζ) - powExt X w₀ (X ζ))
        + powExt X w₀ (X ζ - ξ) := by
    simp only [map_sub]
    abel
  have b1 : ‖powExt X w (ξ - X ζ)‖ ≤ 2 * ‖ξ - X ζ‖ := h.norm_powExt_apply_le_two hw _
  have b3 : ‖powExt X w₀ (X ζ - ξ)‖ ≤ 2 * ‖X ζ - ξ‖ := h.norm_powExt_apply_le_two hw₀ _
  have hsymm : ‖X ζ - ξ‖ = ‖ξ - X ζ‖ := norm_sub_rev _ _
  have b2 : ‖powExt X w (X ζ) - powExt X w₀ (X ζ)‖ < ε / 2 := by
    rw [h.powExt_apply hw.1, h.powExt_apply hw₀.1, ← dist_eq_norm]
    exact hδ' hdist
  rw [dist_eq_norm, e1]
  calc ‖powExt X w (ξ - X ζ) + (powExt X w (X ζ) - powExt X w₀ (X ζ))
          + powExt X w₀ (X ζ - ξ)‖
      ≤ ‖powExt X w (ξ - X ζ) + (powExt X w (X ζ) - powExt X w₀ (X ζ))‖
        + ‖powExt X w₀ (X ζ - ξ)‖ := norm_add_le _ _
    _ ≤ ‖powExt X w (ξ - X ζ)‖ + ‖powExt X w (X ζ) - powExt X w₀ (X ζ)‖
        + ‖powExt X w₀ (X ζ - ξ)‖ := by
          gcongr; exact norm_add_le _ _
    _ < ε := by rw [hsymm] at b3; linarith

end IsPowBase

/-- Strong continuity survives multiplication: a uniformly bounded, strongly continuous family
applied to a continuous vector-valued function is continuous. -/
theorem continuousOn_apply_of_strong {S : Set ℂ} {F : ℂ → (H →L[ℂ] H)} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ z ∈ S, ∀ y : H, ‖F z y‖ ≤ C * ‖y‖)
    (hF : ∀ ζ : H, ContinuousOn (fun z : ℂ => F z ζ) S)
    {g : ℂ → H} (hg : ContinuousOn g S) : ContinuousOn (fun z : ℂ => F z (g z)) S := by
  rw [Metric.continuousOn_iff]
  intro z₀ hz₀ ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := (Metric.continuousOn_iff.1 (hF (g z₀))) z₀ hz₀ (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ :=
    (Metric.continuousOn_iff.1 hg) z₀ hz₀ (ε / (2 * (C + 1))) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun z hz hdist => ?_⟩
  have hd1 : dist z z₀ < δ₁ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd2 : dist z z₀ < δ₂ := lt_of_lt_of_le hdist (min_le_right _ _)
  have e1 : F z (g z) - F z₀ (g z₀) = F z (g z - g z₀) + (F z (g z₀) - F z₀ (g z₀)) := by
    simp only [map_sub]; abel
  have b1 : ‖F z (g z - g z₀)‖ ≤ C * ‖g z - g z₀‖ := hb z hz _
  have b1' : ‖g z - g z₀‖ < ε / (2 * (C + 1)) := by
    rw [← dist_eq_norm]; exact h₂ z hz hd2
  have b2 : ‖F z (g z₀) - F z₀ (g z₀)‖ < ε / 2 := by
    rw [← dist_eq_norm]; exact h₁ z hz hd1
  have b1'' : C * ‖g z - g z₀‖ ≤ ε / 2 := by
    have : C * ‖g z - g z₀‖ ≤ C * (ε / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left b1'.le hC
    refine this.trans ?_
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [dist_eq_norm, e1]
  calc ‖F z (g z - g z₀) + (F z (g z₀) - F z₀ (g z₀))‖
      ≤ ‖F z (g z - g z₀)‖ + ‖F z (g z₀) - F z₀ (g z₀)‖ := norm_add_le _ _
    _ < ε := by linarith

end PowExt

/-! ## Part V: `R^{1/2} (2-R)^{1/2} = T`

The one bookkeeping identity that connects the strip function of Lemma 4.7 to RvD's `T`. -/

section Sqrt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsPowBase

variable {X Y : H →L[ℂ] H}

/-- For a positive real exponent the complex power is the real one. -/
theorem cpowOp_ofReal (h : IsPowBase X) (r : ℝ) :
    cpowOp X ((r : ℝ) : ℂ) = cfc (fun t : ℝ => t ^ r) X := by
  have hval : ∀ t : ℝ, 0 ≤ t → ((t : ℝ) : ℂ) ^ ((r : ℝ) : ℂ) = (((t ^ r : ℝ)) : ℂ) :=
    fun t ht => (Complex.ofReal_cpow ht r).symm
  have hstar : ∀ u ∈ spectrum ℂ X, star (u ^ ((r : ℝ) : ℂ)) = u ^ ((r : ℝ) : ℂ) := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := h.spectrum_complex_repr hu
    rw [hval t ht.1, Complex.star_def, Complex.conj_ofReal]
  rw [cpowOp, cfc_complex_eq_real X hstar h.isSelfAdjoint]
  refine cfc_congr fun t ht => ?_
  rw [hval t (h.spectrum_real_subset ht).1, Complex.ofReal_re]

/-- Positive real powers of a positive operator are positive. -/
theorem cpowOp_ofReal_nonneg (h : IsPowBase X) (r : ℝ) :
    0 ≤ cpowOp X ((r : ℝ) : ℂ) := by
  rw [h.cpowOp_ofReal r]
  exact cfc_nonneg fun t ht => Real.rpow_nonneg (h.spectrum_real_subset ht).1 r

/-- `√(XY) = X^{1/2} Y^{1/2}` for commuting power bases. -/
theorem sqrt_mul_eq (hX : IsPowBase X) (hY : IsPowBase Y) (hc : Commute X Y) :
    CFC.sqrt (X * Y) = cpowOp X (1 / 2 : ℂ) * cpowOp Y (1 / 2 : ℂ) := by
  have hhalf : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by norm_num
  have hre : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hpos : (0 : ℝ) < ((1 / 2 : ℂ)).re := by rw [hre]; norm_num
  have hcomm : Commute (cpowOp X (1 / 2 : ℂ)) (cpowOp Y (1 / 2 : ℂ)) :=
    hX.commute_cpowOp_cpowOp hY hc _ _
  refine CFC.sqrt_unique ?_ ?_
  · calc cpowOp X (1 / 2 : ℂ) * cpowOp Y (1 / 2 : ℂ)
          * (cpowOp X (1 / 2 : ℂ) * cpowOp Y (1 / 2 : ℂ))
        = cpowOp X (1 / 2 : ℂ) * (cpowOp Y (1 / 2 : ℂ) * cpowOp X (1 / 2 : ℂ))
          * cpowOp Y (1 / 2 : ℂ) := by noncomm_ring
      _ = (cpowOp X (1 / 2 : ℂ) * cpowOp X (1 / 2 : ℂ))
          * (cpowOp Y (1 / 2 : ℂ) * cpowOp Y (1 / 2 : ℂ)) := by
            rw [← hcomm.eq]; noncomm_ring
      _ = cpowOp X ((1 / 2 : ℂ) + 1 / 2) * cpowOp Y ((1 / 2 : ℂ) + 1 / 2) := by
            rw [hX.cpowOp_mul hpos hpos, hY.cpowOp_mul hpos hpos]
      _ = X * Y := by
            rw [show ((1 / 2 : ℂ) + 1 / 2) = 1 by norm_num, hX.cpowOp_one, hY.cpowOp_one]
  · rw [hhalf]
    exact Commute.mul_nonneg (hX.cpowOp_ofReal_nonneg _)
      (hY.cpowOp_ofReal_nonneg _) (by rw [← hhalf]; exact hcomm)

end IsPowBase

open ClosedSubmodule

variable (K : ClosedSubmodule ℝ H) (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤)

include hsep hcyc

/-- **`R^{1/2}(2-R)^{1/2} = T`.** -/
theorem cpowOp_half_mul_eq_T :
    cpowOp (R K) (1 / 2 : ℂ) * cpowOp ((2 : H →L[ℂ] H) - R K) (1 / 2 : ℂ) = T K := by
  simp only [T]
  exact (IsPowBase.sqrt_mul_eq (isPowBase_R K hcyc) (isPowBase_two_sub_R K hsep)
    (commute_R_two_sub_R K)).symm

/-- The same in the `powExt` parametrisation. -/
theorem powExt_half_mul_eq_T :
    powExt (R K) (1 / 2 : ℂ) * powExt ((2 : H →L[ℂ] H) - R K) (1 / 2 : ℂ) = T K := by
  have hre : (0 : ℝ) < ((1 / 2 : ℂ)).re := by norm_num
  rw [(isPowBase_R K hcyc).powExt_eq_cpowOp hre,
    (isPowBase_two_sub_R K hsep).powExt_eq_cpowOp hre]
  exact cpowOp_half_mul_eq_T K hsep hcyc

end Sqrt

/-! ## Part VI: the strip function of RvD Lemma 4.7

`f(z) = ⟪η, R^{-z+1/2}(2-R)^{z+1/2} x R^{z+1/2}(2-R)^{-z+1/2} ξ⟫` on `|Re z| ≤ 1/2`.

*Convention.*  Mathlib's inner product is conjugate linear in the **first** slot, so it is
`z ↦ ⟪η, A(z) ξ⟫` — not RvD's `⟪A(z) ξ, η⟫` — that is holomorphic. -/

section StripFun

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsPowBase

variable {X : H →L[ℂ] H}

/-- `z ↦ X^{e z} ζ` is continuous wherever `e` lands in `powStrip`. -/
theorem continuousOn_powExt_comp (h : IsPowBase X) {S : Set ℂ} {e : ℂ → ℂ} (he : Continuous e)
    (hmap : Set.MapsTo e S powStrip) (ζ : H) :
    ContinuousOn (fun z : ℂ => powExt X (e z) ζ) S :=
  (h.continuousOn_powExt_apply ζ).comp he.continuousOn hmap

/-- …and it may be composed with a continuous vector-valued function. -/
theorem continuousOn_powExt_mul (h : IsPowBase X) {S : Set ℂ} {e : ℂ → ℂ} (he : Continuous e)
    (hmap : Set.MapsTo e S powStrip) {g : ℂ → H} (hg : ContinuousOn g S) :
    ContinuousOn (fun z : ℂ => powExt X (e z) (g z)) S :=
  continuousOn_apply_of_strong (by norm_num)
    (fun z hz y => h.norm_powExt_apply_le_two (hmap hz) y)
    (fun ζ => h.continuousOn_powExt_comp he hmap ζ) hg

/-- `z ↦ X^{e z}` is norm-holomorphic wherever `e` lands in the open right half plane. -/
theorem differentiableAt_cpowOp_comp (h : IsPowBase X) {e : ℂ → ℂ} {z : ℂ}
    (he : DifferentiableAt ℂ e z) (hre : 0 < (e z).re) :
    DifferentiableAt ℂ (fun v : ℂ => cpowOp X (e v)) z :=
  (h.differentiableAt_cpowOp hre).comp z he

end IsPowBase

open ClosedSubmodule

/-- The exponents of Lemma 4.7 land in `powStrip` on the closed strip. -/
lemma add_half_mem_powStrip {z : ℂ} (hz : z ∈ clStrip) : z + 1 / 2 ∈ powStrip := by
  have := abs_le.1 (mem_clStrip.1 hz)
  refine ⟨?_, ?_⟩ <;> · simp only [Complex.add_re, Complex.div_re]; norm_num; linarith [this.1, this.2]

lemma neg_add_half_mem_powStrip {z : ℂ} (hz : z ∈ clStrip) : -z + 1 / 2 ∈ powStrip := by
  have := abs_le.1 (mem_clStrip.1 hz)
  refine ⟨?_, ?_⟩ <;> · simp only [Complex.add_re, Complex.neg_re, Complex.div_re]; norm_num;
                        linarith [this.1, this.2]

lemma add_half_re_pos {z : ℂ} (hz : z ∈ opStrip) : 0 < (z + 1 / 2).re := by
  have := abs_lt.1 (mem_opStrip.1 hz)
  simp only [Complex.add_re, Complex.div_re]
  norm_num
  linarith [this.1]

lemma neg_add_half_re_pos {z : ℂ} (hz : z ∈ opStrip) : 0 < (-z + 1 / 2).re := by
  have := abs_lt.1 (mem_opStrip.1 hz)
  simp only [Complex.add_re, Complex.neg_re, Complex.div_re]
  norm_num
  linarith [this.2]

variable (K : ClosedSubmodule ℝ H)

/-- RvD's `R^{-z+1/2}(2-R)^{z+1/2} x R^{z+1/2}(2-R)^{-z+1/2}`. -/
noncomputable def stripOp (K : ClosedSubmodule ℝ H) (x : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  powExt (R K) (-z + 1 / 2) * powExt ((2 : H →L[ℂ] H) - R K) (z + 1 / 2) * x
    * powExt (R K) (z + 1 / 2) * powExt ((2 : H →L[ℂ] H) - R K) (-z + 1 / 2)

/-- The same with `cfc` in place of the extension: valid on the *open* strip only. -/
noncomputable def stripOpOpen (K : ClosedSubmodule ℝ H) (x : H →L[ℂ] H) (z : ℂ) :
    H →L[ℂ] H :=
  cpowOp (R K) (-z + 1 / 2) * cpowOp ((2 : H →L[ℂ] H) - R K) (z + 1 / 2) * x
    * cpowOp (R K) (z + 1 / 2) * cpowOp ((2 : H →L[ℂ] H) - R K) (-z + 1 / 2)

variable (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤)

include hsep hcyc

lemma stripOp_apply (x : H →L[ℂ] H) (z : ℂ) (ξ : H) :
    stripOp K x z ξ
      = powExt (R K) (-z + 1 / 2)
          (powExt ((2 : H →L[ℂ] H) - R K) (z + 1 / 2)
            (x (powExt (R K) (z + 1 / 2)
              (powExt ((2 : H →L[ℂ] H) - R K) (-z + 1 / 2) ξ)))) := rfl

/-- **Continuity of the strip function on the closed strip.** -/
theorem continuousOn_stripOp_apply (x : H →L[ℂ] H) (ξ : H) :
    ContinuousOn (fun z : ℂ => stripOp K x z ξ) clStrip := by
  have hR := isPowBase_R K hcyc
  have hR' := isPowBase_two_sub_R K hsep
  have hcp : Continuous (fun z : ℂ => z + 1 / 2) := by fun_prop
  have hcm : Continuous (fun z : ℂ => -z + 1 / 2) := by fun_prop
  have hmp : Set.MapsTo (fun z : ℂ => z + 1 / 2) clStrip powStrip :=
    fun z hz => add_half_mem_powStrip hz
  have hmm : Set.MapsTo (fun z : ℂ => -z + 1 / 2) clStrip powStrip :=
    fun z hz => neg_add_half_mem_powStrip hz
  have g4 : ContinuousOn
      (fun z : ℂ => powExt ((2 : H →L[ℂ] H) - R K) (-z + 1 / 2) ξ) clStrip :=
    hR'.continuousOn_powExt_comp hcm hmm ξ
  have g3 := hR.continuousOn_powExt_mul hcp hmp g4
  have g2 : ContinuousOn (fun z : ℂ => x (powExt (R K) (z + 1 / 2)
      (powExt ((2 : H →L[ℂ] H) - R K) (-z + 1 / 2) ξ))) clStrip :=
    x.continuous.comp_continuousOn g3
  have g1 := hR'.continuousOn_powExt_mul hcp hmp g2
  exact hR.continuousOn_powExt_mul hcm hmm g1

/-- On the open strip all four exponents have positive real part, so `powExt` is `cpowOp`. -/
theorem stripOp_eq_open (x : H →L[ℂ] H) {z : ℂ} (hz : z ∈ opStrip) :
    stripOp K x z = stripOpOpen K x z := by
  have hR := isPowBase_R K hcyc
  have hR' := isPowBase_two_sub_R K hsep
  rw [stripOp, stripOpOpen, hR.powExt_eq_cpowOp (neg_add_half_re_pos hz),
    hR'.powExt_eq_cpowOp (add_half_re_pos hz), hR.powExt_eq_cpowOp (add_half_re_pos hz),
    hR'.powExt_eq_cpowOp (neg_add_half_re_pos hz)]

/-- **Holomorphy of the strip function on the open strip.** -/
theorem differentiableAt_stripOpOpen (x : H →L[ℂ] H) {z : ℂ} (hz : z ∈ opStrip) :
    DifferentiableAt ℂ (fun v : ℂ => stripOpOpen K x v) z := by
  have hR := isPowBase_R K hcyc
  have hR' := isPowBase_two_sub_R K hsep
  have dp : DifferentiableAt ℂ (fun v : ℂ => v + 1 / 2) z := by fun_prop
  have dm : DifferentiableAt ℂ (fun v : ℂ => -v + 1 / 2) z := by fun_prop
  have d1 := hR.differentiableAt_cpowOp_comp dm (neg_add_half_re_pos hz)
  have d2 := hR'.differentiableAt_cpowOp_comp dp (add_half_re_pos hz)
  have d3 := hR.differentiableAt_cpowOp_comp dp (add_half_re_pos hz)
  have d4 := hR'.differentiableAt_cpowOp_comp dm (neg_add_half_re_pos hz)
  exact (((d1.mul d2).mul (differentiableAt_const x)).mul d3).mul d4

/-- The uniform bound on the closed strip: `|t^w| ≤ 2` for `0 ≤ Re w ≤ 1` and `t ∈ [0,2]`,
four times over. -/
theorem norm_stripOp_apply_le (x : H →L[ℂ] H) {z : ℂ} (hz : z ∈ clStrip) (ξ : H) :
    ‖stripOp K x z ξ‖ ≤ 16 * ‖x‖ * ‖ξ‖ := by
  have hR := isPowBase_R K hcyc
  have hR' := isPowBase_two_sub_R K hsep
  have hp := add_half_mem_powStrip hz
  have hm := neg_add_half_mem_powStrip hz
  set v4 := powExt ((2 : H →L[ℂ] H) - R K) (-z + 1 / 2) ξ with hv4
  set v3 := powExt (R K) (z + 1 / 2) v4 with hv3
  set v2 := x v3 with hv2
  set v1 := powExt ((2 : H →L[ℂ] H) - R K) (z + 1 / 2) v2 with hv1
  have b4 : ‖v4‖ ≤ 2 * ‖ξ‖ := hR'.norm_powExt_apply_le_two hm ξ
  have b3 : ‖v3‖ ≤ 2 * (2 * ‖ξ‖) := le_trans (hR.norm_powExt_apply_le_two hp v4) (by linarith)
  have b2 : ‖v2‖ ≤ ‖x‖ * (2 * (2 * ‖ξ‖)) :=
    le_trans (x.le_opNorm v3) (mul_le_mul_of_nonneg_left b3 (norm_nonneg x))
  have b1 : ‖v1‖ ≤ 2 * (‖x‖ * (2 * (2 * ‖ξ‖))) :=
    le_trans (hR'.norm_powExt_apply_le_two hp v2) (by linarith)
  have b0 : ‖stripOp K x z ξ‖ ≤ 2 * (2 * (‖x‖ * (2 * (2 * ‖ξ‖)))) := by
    rw [stripOp_apply K hsep hcyc]
    exact le_trans (hR.norm_powExt_apply_le_two hm v1) (by linarith)
  linarith

/-! ### The three evaluations -/

/-- `f(0) = ⟪η, T x T ξ⟫`. -/
theorem stripOp_zero (x : H →L[ℂ] H) : stripOp K x 0 = T K * x * T K := by
  have h0 : -(0 : ℂ) + 1 / 2 = 1 / 2 := by ring
  have h0' : (0 : ℂ) + 1 / 2 = 1 / 2 := by ring
  have hT := powExt_half_mul_eq_T K hsep hcyc
  rw [stripOp, h0, h0']
  calc powExt (R K) (1 / 2 : ℂ) * powExt ((2 : H →L[ℂ] H) - R K) (1 / 2 : ℂ) * x
        * powExt (R K) (1 / 2 : ℂ) * powExt ((2 : H →L[ℂ] H) - R K) (1 / 2 : ℂ)
      = (powExt (R K) (1 / 2 : ℂ) * powExt ((2 : H →L[ℂ] H) - R K) (1 / 2 : ℂ)) * x
        * (powExt (R K) (1 / 2 : ℂ) * powExt ((2 : H →L[ℂ] H) - R K) (1 / 2 : ℂ)) := by
        noncomm_ring
    _ = T K * x * T K := by rw [hT]

omit hsep hcyc in
lemma modPow_eq_prod (t : ℝ) :
    modPow K t = opPow ((2 : H →L[ℂ] H) - R K) ((t : ℝ) : ℂ) * opPow (R K) (-((t : ℝ) : ℂ)) :=
  rfl

omit hsep hcyc in
lemma modPow_neg_eq_prod (t : ℝ) :
    modPow K (-t)
      = opPow ((2 : H →L[ℂ] H) - R K) (-((t : ℝ) : ℂ)) * opPow (R K) ((t : ℝ) : ℂ) := by
  rw [modPow, Complex.ofReal_neg, neg_neg]

/-- `f(it + 1/2)` is the modular flow of `(2-R) x R`. -/
theorem stripOp_right (x : H →L[ℂ] H) (t : ℝ) :
    stripOp K x ((t : ℂ) * I + 1 / 2)
      = modPow K t * (((2 : H →L[ℂ] H) - R K) * x * R K) * modPow K (-t) := by
  have hR := isPowBase_R K hcyc
  have hR' := isPowBase_two_sub_R K hsep
  set a := opPow ((2 : H →L[ℂ] H) - R K) ((t : ℝ) : ℂ) with ha
  set b := opPow (R K) (-((t : ℝ) : ℂ)) with hb
  set c := opPow ((2 : H →L[ℂ] H) - R K) (-((t : ℝ) : ℂ)) with hc
  set d := opPow (R K) ((t : ℝ) : ℂ) with hd
  -- the four exponents
  have e1 : -((t : ℂ) * I + 1 / 2) + 1 / 2 = I * ((-t : ℝ) : ℂ) := by push_cast; ring
  have e2 : (t : ℂ) * I + 1 / 2 + 1 / 2 = I * ((t : ℝ) : ℂ) + 1 := by ring
  have f1 : powExt (R K) (-((t : ℂ) * I + 1 / 2) + 1 / 2) = b := by
    rw [e1, IsPowBase.powExt_I_mul, hb, Complex.ofReal_neg]
  have f4 : powExt ((2 : H →L[ℂ] H) - R K) (-((t : ℂ) * I + 1 / 2) + 1 / 2) = c := by
    rw [e1, IsPowBase.powExt_I_mul, hc, Complex.ofReal_neg]
  have f2 : powExt ((2 : H →L[ℂ] H) - R K) ((t : ℂ) * I + 1 / 2 + 1 / 2)
      = a * ((2 : H →L[ℂ] H) - R K) := by
    rw [e2, hR'.powExt_add_one (by simp), IsPowBase.powExt_I_mul, ha]
  have f3 : powExt (R K) ((t : ℂ) * I + 1 / 2 + 1 / 2) = d * R K := by
    rw [e2, hR.powExt_add_one (by simp), IsPowBase.powExt_I_mul, hd]
  -- the commutations
  have hba : b * a = a * b := (opPow_two_sub_R_commute K hsep hcyc (by simp) (by simp)).symm
  have hdc : d * c = c * d := (opPow_two_sub_R_commute K hsep hcyc (by simp) (by simp)).symm
  have hdR : d * R K = R K * d :=
    (hR.opPow_commute_right (Commute.refl (R K)) (by simp)).eq
  rw [stripOp, f1, f2, f3, f4, modPow_eq_prod, modPow_neg_eq_prod, ← ha, ← hb, ← hc, ← hd]
  calc b * (a * ((2 : H →L[ℂ] H) - R K)) * x * (d * R K) * c
      = (b * a) * ((2 : H →L[ℂ] H) - R K) * x * (d * R K) * c := by noncomm_ring
    _ = (a * b) * ((2 : H →L[ℂ] H) - R K) * x * (d * R K) * c := by rw [hba]
    _ = (a * b) * ((2 : H →L[ℂ] H) - R K) * x * (R K * d) * c := by rw [hdR]
    _ = (a * b) * ((2 : H →L[ℂ] H) - R K) * x * R K * (d * c) := by noncomm_ring
    _ = (a * b) * ((2 : H →L[ℂ] H) - R K) * x * R K * (c * d) := by rw [hdc]
    _ = a * b * (((2 : H →L[ℂ] H) - R K) * x * R K) * (c * d) := by noncomm_ring

/-- `f(it - 1/2)` is the modular flow of `R x (2-R)`. -/
theorem stripOp_left (x : H →L[ℂ] H) (t : ℝ) :
    stripOp K x ((t : ℂ) * I - 1 / 2)
      = modPow K t * (R K * x * ((2 : H →L[ℂ] H) - R K)) * modPow K (-t) := by
  have hR := isPowBase_R K hcyc
  have hR' := isPowBase_two_sub_R K hsep
  set a := opPow ((2 : H →L[ℂ] H) - R K) ((t : ℝ) : ℂ) with ha
  set b := opPow (R K) (-((t : ℝ) : ℂ)) with hb
  set c := opPow ((2 : H →L[ℂ] H) - R K) (-((t : ℝ) : ℂ)) with hc
  set d := opPow (R K) ((t : ℝ) : ℂ) with hd
  have e1 : -((t : ℂ) * I - 1 / 2) + 1 / 2 = I * ((-t : ℝ) : ℂ) + 1 := by push_cast; ring
  have e2 : (t : ℂ) * I - 1 / 2 + 1 / 2 = I * ((t : ℝ) : ℂ) := by ring
  have f1 : powExt (R K) (-((t : ℂ) * I - 1 / 2) + 1 / 2) = b * R K := by
    rw [e1, hR.powExt_add_one (by simp), IsPowBase.powExt_I_mul, hb, Complex.ofReal_neg]
  have f4 : powExt ((2 : H →L[ℂ] H) - R K) (-((t : ℂ) * I - 1 / 2) + 1 / 2)
      = c * ((2 : H →L[ℂ] H) - R K) := by
    rw [e1, hR'.powExt_add_one (by simp), IsPowBase.powExt_I_mul, hc, Complex.ofReal_neg]
  have f2 : powExt ((2 : H →L[ℂ] H) - R K) ((t : ℂ) * I - 1 / 2 + 1 / 2) = a := by
    rw [e2, IsPowBase.powExt_I_mul, ha]
  have f3 : powExt (R K) ((t : ℂ) * I - 1 / 2 + 1 / 2) = d := by
    rw [e2, IsPowBase.powExt_I_mul, hd]
  have hba : b * a = a * b := (opPow_two_sub_R_commute K hsep hcyc (by simp) (by simp)).symm
  have hdc : d * c = c * d := (opPow_two_sub_R_commute K hsep hcyc (by simp) (by simp)).symm
  have hRa : R K * a = a * R K :=
    ((hR'.opPow_commute_right (commute_two_sub_R_R K) (by simp)).eq).symm
  have hcR' : c * ((2 : H →L[ℂ] H) - R K) = ((2 : H →L[ℂ] H) - R K) * c :=
    (hR'.opPow_commute_right (Commute.refl _) (by simp)).eq
  have hdR' : d * ((2 : H →L[ℂ] H) - R K) = ((2 : H →L[ℂ] H) - R K) * d :=
    (hR.opPow_commute_right (commute_R_two_sub_R K) (by simp)).eq
  rw [stripOp, f1, f2, f3, f4, modPow_eq_prod, modPow_neg_eq_prod, ← ha, ← hb, ← hc, ← hd]
  calc b * R K * a * x * d * (c * ((2 : H →L[ℂ] H) - R K))
      = b * (R K * a) * x * d * (c * ((2 : H →L[ℂ] H) - R K)) := by noncomm_ring
    _ = b * (a * R K) * x * d * (c * ((2 : H →L[ℂ] H) - R K)) := by rw [hRa]
    _ = (b * a) * R K * x * (d * c) * ((2 : H →L[ℂ] H) - R K) := by noncomm_ring
    _ = (a * b) * R K * x * (c * d) * ((2 : H →L[ℂ] H) - R K) := by rw [hba, hdc]
    _ = (a * b) * R K * x * c * (d * ((2 : H →L[ℂ] H) - R K)) := by noncomm_ring
    _ = (a * b) * R K * x * c * (((2 : H →L[ℂ] H) - R K) * d) := by rw [hdR']
    _ = (a * b) * R K * x * (c * ((2 : H →L[ℂ] H) - R K)) * d := by noncomm_ring
    _ = (a * b) * R K * x * (((2 : H →L[ℂ] H) - R K) * c) * d := by rw [hcR']
    _ = a * b * (R K * x * ((2 : H →L[ℂ] H) - R K)) * (c * d) := by noncomm_ring

end StripFun

/-! ## Part VII: RvD Lemma 4.7

Lemma 4.5 produces the `x ∈ M`; Lemma 4.6 applied to `z ↦ ⟪η, stripOp x z ξ⟫` produces the
integral representation with two spare `T`'s, which `commute_modPow_T` and the density of
`ran T` strip off. -/

section Lemma47

open MeasureTheory Filter Topology Set Theses.A.VN

variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-- A Lipschitz-type bound gives continuity. -/
theorem continuous_of_dist_le_mul {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {f : α → β} {L : ℝ} (h : ∀ a b, dist (f a) (f b) ≤ L * dist a b) : Continuous f := by
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨ε / (|L| + 1), by positivity, fun a ha => ?_⟩
  have h1 : L * dist a b ≤ |L| * dist a b :=
    mul_le_mul_of_nonneg_right (le_abs_self L) dist_nonneg
  have h2 : |L| * dist a b ≤ (|L| + 1) * dist a b := by nlinarith [dist_nonneg (x := a) (y := b)]
  have h3 : (|L| + 1) * dist a b < (|L| + 1) * (ε / (|L| + 1)) := by
    exact mul_lt_mul_of_pos_left ha (by positivity)
  have h4 : (|L| + 1) * (ε / (|L| + 1)) = ε := by field_simp
  calc dist (f a) (f b) ≤ L * dist a b := h a b
    _ < ε := by linarith

variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (ω : ℋ)
variable (hsep : Ksub M ω ⊓ (Ksub M ω).mulI = ⊥) (hcyc : Ksub M ω ⊔ (Ksub M ω).mulI = ⊤)

include hsep hcyc

/-- The kernel average, in the shape the density argument needs: linear in the second slot of
the inner product. -/
noncomputable def kInt (x' : ℋ →L[ℂ] ℋ) (φ : ℝ) (u v : ℋ) : ℂ :=
  ∫ s : ℝ, (rvdKernel φ s : ℂ) * ⟪v, modFlow M ω hsep hcyc x' s u⟫

variable {M ω}

lemma continuous_inner_modFlow' (x' : ℋ →L[ℂ] ℋ) (u v : ℋ) :
    Continuous (fun s : ℝ => (⟪v, modFlow M ω hsep hcyc x' s u⟫ : ℂ)) := by
  have h := continuous_inner_modFlow M ω hsep hcyc x' u v
  have he : ∀ s : ℝ, (⟪v, modFlow M ω hsep hcyc x' s u⟫ : ℂ)
      = (starRingEnd ℂ) (⟪modFlow M ω hsep hcyc x' s u, v⟫ : ℂ) := fun s =>
    (inner_conj_symm _ _).symm
  simp only [he]
  exact Complex.continuous_conj.comp h

lemma norm_inner_modFlow_le (x' : ℋ →L[ℂ] ℋ) (u v : ℋ) (s : ℝ) :
    ‖(⟪v, modFlow M ω hsep hcyc x' s u⟫ : ℂ)‖ ≤ ‖x'‖ * ‖u‖ * ‖v‖ := by
  calc ‖(⟪v, modFlow M ω hsep hcyc x' s u⟫ : ℂ)‖
      ≤ ‖v‖ * ‖modFlow M ω hsep hcyc x' s u‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖x'‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (norm_modFlow_apply_le M ω hsep hcyc x' s u) (norm_nonneg _)
    _ = ‖x'‖ * ‖u‖ * ‖v‖ := by ring

lemma integrable_kInt (x' : ℋ →L[ℂ] ℋ) {φ : ℝ} (hφ : |φ| < Real.pi) (u v : ℋ) :
    Integrable (fun s : ℝ => (rvdKernel φ s : ℂ) * ⟪v, modFlow M ω hsep hcyc x' s u⟫) :=
  integrable_rvdKernel_mul (continuous_inner_modFlow' hsep hcyc x' u v)
    (norm_inner_modFlow_le hsep hcyc x' u v) hφ

/-- The `L¹` mass of the RvD kernel's dominating function. -/
noncomputable def kMass (φ : ℝ) : ℝ := ∫ s : ℝ, Real.exp (-(Real.pi - |φ|) * |s|)

lemma norm_kInt_le (x' : ℋ →L[ℂ] ℋ) {φ : ℝ} (hφ : |φ| < Real.pi) (u v : ℋ) :
    ‖kInt M ω hsep hcyc x' φ u v‖ ≤ kMass φ * (‖x'‖ * ‖u‖ * ‖v‖) := by
  set B : ℝ := ‖x'‖ * ‖u‖ * ‖v‖ with hB
  have hB0 : 0 ≤ B := by positivity
  have hc : 0 < Real.pi - |φ| := by linarith
  have hint : Integrable (fun s : ℝ => B * Real.exp (-(Real.pi - |φ|) * |s|)) :=
    (integrable_exp_neg_mul_abs hc).const_mul B
  have hle : ∀ s : ℝ, ‖(rvdKernel φ s : ℂ) * ⟪v, modFlow M ω hsep hcyc x' s u⟫‖
      ≤ B * Real.exp (-(Real.pi - |φ|) * |s|) := by
    intro s
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rvdKernel_pos φ s)]
    calc rvdKernel φ s * ‖(⟪v, modFlow M ω hsep hcyc x' s u⟫ : ℂ)‖
        ≤ Real.exp (-(Real.pi - |φ|) * |s|) * B :=
          mul_le_mul (rvdKernel_le φ s) (norm_inner_modFlow_le hsep hcyc x' u v s)
            (norm_nonneg _) (Real.exp_pos _).le
      _ = B * Real.exp (-(Real.pi - |φ|) * |s|) := by ring
  have h1 : ‖kInt M ω hsep hcyc x' φ u v‖
      ≤ ∫ s : ℝ, B * Real.exp (-(Real.pi - |φ|) * |s|) :=
    MeasureTheory.norm_integral_le_of_norm_le hint (MeasureTheory.ae_of_all _ hle)
  rw [MeasureTheory.integral_const_mul] at h1
  rw [kMass, mul_comm]
  exact h1

/-- The kernel average is additive in the first slot. -/
lemma kInt_sub_left (x' : ℋ →L[ℂ] ℋ) {φ : ℝ} (hφ : |φ| < Real.pi) (u₁ u₂ v : ℋ) :
    kInt M ω hsep hcyc x' φ u₁ v - kInt M ω hsep hcyc x' φ u₂ v
      = kInt M ω hsep hcyc x' φ (u₁ - u₂) v := by
  rw [kInt, kInt, kInt, ← MeasureTheory.integral_sub (integrable_kInt hsep hcyc x' hφ u₁ v)
    (integrable_kInt hsep hcyc x' hφ u₂ v)]
  refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun s => ?_)
  simp only [map_sub, inner_sub_right]
  ring

/-- …and conjugate-additive in the second. -/
lemma kInt_sub_right (x' : ℋ →L[ℂ] ℋ) {φ : ℝ} (hφ : |φ| < Real.pi) (u v₁ v₂ : ℋ) :
    kInt M ω hsep hcyc x' φ u v₁ - kInt M ω hsep hcyc x' φ u v₂
      = kInt M ω hsep hcyc x' φ u (v₁ - v₂) := by
  rw [kInt, kInt, kInt, ← MeasureTheory.integral_sub (integrable_kInt hsep hcyc x' hφ u v₁)
    (integrable_kInt hsep hcyc x' hφ u v₂)]
  refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun s => ?_)
  simp only [inner_sub_left]
  ring

lemma continuous_kInt_left (x' : ℋ →L[ℂ] ℋ) {φ : ℝ} (hφ : |φ| < Real.pi) (v : ℋ) :
    Continuous (fun u : ℋ => kInt M ω hsep hcyc x' φ u v) := by
  refine continuous_of_dist_le_mul (L := kMass φ * (‖x'‖ * ‖v‖)) fun u₁ u₂ => ?_
  rw [dist_eq_norm, kInt_sub_left hsep hcyc x' hφ, dist_eq_norm]
  calc ‖kInt M ω hsep hcyc x' φ (u₁ - u₂) v‖
      ≤ kMass φ * (‖x'‖ * ‖u₁ - u₂‖ * ‖v‖) := norm_kInt_le hsep hcyc x' hφ _ _
    _ = kMass φ * (‖x'‖ * ‖v‖) * ‖u₁ - u₂‖ := by ring

lemma continuous_kInt_right (x' : ℋ →L[ℂ] ℋ) {φ : ℝ} (hφ : |φ| < Real.pi) (u : ℋ) :
    Continuous (fun v : ℋ => kInt M ω hsep hcyc x' φ u v) := by
  refine continuous_of_dist_le_mul (L := kMass φ * (‖x'‖ * ‖u‖)) fun v₁ v₂ => ?_
  rw [dist_eq_norm, kInt_sub_right hsep hcyc x' hφ, dist_eq_norm]
  calc ‖kInt M ω hsep hcyc x' φ u (v₁ - v₂)‖
      ≤ kMass φ * (‖x'‖ * ‖u‖ * ‖v₁ - v₂‖) := norm_kInt_le hsep hcyc x' hφ _ _
    _ = kMass φ * (‖x'‖ * ‖u‖) * ‖v₁ - v₂‖ := by ring

/-! ### Assembling Lemma 4.7 -/

omit hsep hcyc in
lemma inner_T_left (K : ClosedSubmodule ℝ ℋ) (u v : ℋ) :
    (⟪T K u, v⟫ : ℂ) = ⟪u, T K v⟫ := by
  rw [inner_apply_left, (T_isSelfAdjoint K).star_eq]

/-- The two boundary values of the strip function combine, via Lemma 4.5, into the modular
flow conjugated by `T` — and `commute_modPow_T` moves both `T`'s outside. -/
lemma stripOp_combination {x x' : ℋ →L[ℂ] ℋ} {lam : ℂ}
    (hkey : T (Ksub M ω) * vnAdJ M ω hsep hcyc x' * T (Ksub M ω)
      = lam • (((2 : ℋ →L[ℂ] ℋ) - R (Ksub M ω)) * x * R (Ksub M ω))
        + (starRingEnd ℂ) lam • (R (Ksub M ω) * x * ((2 : ℋ →L[ℂ] ℋ) - R (Ksub M ω))))
    (t : ℝ) :
    lam • stripOp (Ksub M ω) x ((t : ℂ) * I + 1 / 2)
        + (starRingEnd ℂ) lam • stripOp (Ksub M ω) x ((t : ℂ) * I - 1 / 2)
      = T (Ksub M ω) * modFlow M ω hsep hcyc x' t * T (Ksub M ω) := by
  set K := Ksub M ω with hKdef
  set cl := (starRingEnd ℂ) lam with hcl
  set A₁ : ℋ →L[ℂ] ℋ := ((2 : ℋ →L[ℂ] ℋ) - R K) * x * R K with hA₁
  set A₂ : ℋ →L[ℂ] ℋ := R K * x * ((2 : ℋ →L[ℂ] ℋ) - R K) with hA₂
  rw [stripOp_right K hsep hcyc x t, stripOp_left K hsep hcyc x t, ← hA₁, ← hA₂]
  have hcomb : lam • (modPow K t * A₁ * modPow K (-t)) + cl • (modPow K t * A₂ * modPow K (-t))
      = modPow K t * (lam • A₁ + cl • A₂) * modPow K (-t) := by
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [hcomb, ← hkey, modFlow]
  have h1 : modPow K t * T K = T K * modPow K t := (commute_modPow_T K hsep hcyc t).eq
  have h2 : T K * modPow K (-t) = modPow K (-t) * T K :=
    ((commute_modPow_T K hsep hcyc (-t)).eq).symm
  calc modPow K t * (T K * vnAdJ M ω hsep hcyc x' * T K) * modPow K (-t)
      = (modPow K t * T K) * vnAdJ M ω hsep hcyc x' * (T K * modPow K (-t)) := by noncomm_ring
    _ = (T K * modPow K t) * vnAdJ M ω hsep hcyc x' * (modPow K (-t) * T K) := by rw [h1, h2]
    _ = T K * (modPow K t * vnAdJ M ω hsep hcyc x' * modPow K (-t)) * T K := by noncomm_ring

variable (M ω)

/-- **RvD Lemma 4.7** (p. 204).  For `x' ∈ M'` and `|φ| < π` there is an `x ∈ M` whose matrix
coefficients are the RvD-kernel average of the modular orbit of `J x' J`.

This is exactly the hypothesis `h47` of `TomitaFourier.tomita_JMJ_of_lemma_4_7`. -/
theorem lemma_4_7
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    (hM'dense : Dense {y : ℋ | ∃ u ∈ commutantSA M, y = u ω})
    {x' : ℋ →L[ℂ] ℋ} (hx' : x' ∈ commutantSA M) {φ : ℝ} (hφ : |φ| < Real.pi) :
    ∃ x ∈ M, ∀ ξ η : ℋ,
      (⟪x ξ, η⟫ : ℂ)
        = ∫ s : ℝ, (rvdKernel φ s : ℂ) * ⟪modFlow M ω hsep hcyc x' s ξ, η⟫ := by
  set K := Ksub M ω with hKdef
  set lam : ℂ := Complex.exp (I * (φ : ℂ) / 2) with hlamdef
  have hlamre : 0 < lam.re := by
    have harg : I * (φ : ℂ) / 2 = (((φ / 2 : ℝ)) : ℂ) * I := by push_cast; ring
    have hab := abs_lt.1 hφ
    rw [hlamdef, harg, Complex.exp_ofReal_mul_I_re]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hab.1], by linarith [hab.2]⟩
  obtain ⟨x, hxM, hkey⟩ := lemma_4_5 M ω hsep hcyc hM hM'dense hx' hlamre
  -- the identity with two spare `T`'s
  have hTT : ∀ ξ η : ℋ,
      (⟪T K η, x (T K ξ)⟫ : ℂ) = kInt M ω hsep hcyc x' φ (T K ξ) (T K η) := by
    intro ξ η
    set f : ℂ → ℂ := fun z => (⟪η, stripOp K x z ξ⟫ : ℂ) with hf
    have hfc : ContinuousOn f clStrip :=
      continuousOn_const.inner (continuousOn_stripOp_apply K hsep hcyc x ξ)
    set L : (ℋ →L[ℂ] ℋ) →L[ℂ] ℂ :=
      (innerSL ℂ η).comp (ContinuousLinearMap.apply ℂ ℋ ξ) with hLdef
    have hLapp : ∀ A : ℋ →L[ℂ] ℋ, L A = (⟪η, A ξ⟫ : ℂ) := fun _ => rfl
    have hfd : DifferentiableOn ℂ f opStrip := by
      intro z hz
      have hdo : DifferentiableAt ℂ (fun v : ℂ => L (stripOpOpen K x v)) z :=
        L.differentiableAt.comp z (differentiableAt_stripOpOpen K hsep hcyc x hz)
      have heq : Set.EqOn f (fun v : ℂ => L (stripOpOpen K x v)) opStrip := by
        intro v hv
        show (⟪η, stripOp K x v ξ⟫ : ℂ) = L (stripOpOpen K x v)
        rw [hLapp, stripOp_eq_open K hsep hcyc x hv]
      exact (hdo.congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (isOpen_opStrip.mem_nhds hz) heq)).differentiableWithinAt
    have hCb : ∀ z ∈ clStrip, ‖f z‖ ≤ ‖η‖ * (16 * ‖x‖ * ‖ξ‖) := by
      intro z hz
      calc ‖f z‖ ≤ ‖η‖ * ‖stripOp K x z ξ‖ := norm_inner_le_norm _ _
        _ ≤ ‖η‖ * (16 * ‖x‖ * ‖ξ‖) :=
            mul_le_mul_of_nonneg_left (norm_stripOp_apply_le K hsep hcyc x hz ξ) (norm_nonneg _)
    have h46 := lemma_4_6 hfc hfd hCb hφ hlamdef
    have hf0 : f 0 = (⟪T K η, x (T K ξ)⟫ : ℂ) := by
      show (⟪η, stripOp K x 0 ξ⟫ : ℂ) = _
      rw [stripOp_zero K hsep hcyc]
      exact (inner_T_left K η (x (T K ξ))).symm
    have hint : ∀ t : ℝ,
        lam * f ((t : ℂ) * I + 1 / 2) + (starRingEnd ℂ) lam * f ((t : ℂ) * I - 1 / 2)
          = (⟪T K η, modFlow M ω hsep hcyc x' t (T K ξ)⟫ : ℂ) := by
      intro t
      have hsplit : lam * f ((t : ℂ) * I + 1 / 2) + (starRingEnd ℂ) lam * f ((t : ℂ) * I - 1 / 2)
          = (⟪η, (lam • stripOp K x ((t : ℂ) * I + 1 / 2)
              + (starRingEnd ℂ) lam • stripOp K x ((t : ℂ) * I - 1 / 2)) ξ⟫ : ℂ) := by
        simp only [hf, add_apply, smul_apply, inner_add_right, inner_smul_right]
      rw [hsplit, stripOp_combination hsep hcyc hkey t]
      exact (inner_T_left K η (modFlow M ω hsep hcyc x' t (T K ξ))).symm
    rw [← hf0, h46, kInt]
    simp only [hint, rvdKernel]
  -- density in the first slot, then in the second
  have hdense : DenseRange (T K) := T_denseRange K hsep hcyc
  have hstep1 : ∀ (u : ℋ) (η : ℋ),
      (⟪T K η, x u⟫ : ℂ) = kInt M ω hsep hcyc x' φ u (T K η) := by
    intro u η
    refine hdense.induction_on u (isClosed_eq ?_ ?_) (fun ζ => hTT ζ η)
    · exact continuous_const.inner x.continuous
    · exact continuous_kInt_left hsep hcyc x' hφ _
  have hall : ∀ (u v : ℋ), (⟪v, x u⟫ : ℂ) = kInt M ω hsep hcyc x' φ u v := by
    intro u v
    refine hdense.induction_on v (isClosed_eq ?_ ?_) (fun ζ => hstep1 u ζ)
    · exact continuous_id.inner continuous_const
    · exact continuous_kInt_right hsep hcyc x' hφ _
  refine ⟨x, hxM, fun ξ η => ?_⟩
  have hc := congrArg (starRingEnd ℂ) (hall ξ η)
  rw [inner_conj_symm] at hc
  rw [hc, kInt, ← integral_conj]
  simp only [map_mul, Complex.conj_ofReal, inner_conj_symm]

/-- **RvD Theorem 4.2(1), unconditionally: `J M J = M'`.**  `TomitaFourier`'s
`tomita_JMJ_of_lemma_4_7` fed with `lemma_4_7`. -/
theorem tomita_JMJ_unconditional
    (hMdense : Dense {y : ℋ | ∃ x ∈ M, y = x ω})
    (hM'dense : Dense {y : ℋ | ∃ x ∈ commutantSA M, y = x ω})
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ))) :
    (fun x => vnAdJ M ω hsep hcyc x) '' (M : Set (ℋ →L[ℂ] ℋ))
      = commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)) :=
  tomita_JMJ_of_lemma_4_7 M ω hsep hcyc hMdense hM'dense hM
    (fun _ hx' _ hφ => lemma_4_7 M ω hsep hcyc hM hM'dense hx' hφ)

/-- **`J M' J = M`**, the other half — a corollary of `tomita_JMJ_unconditional`,
since `adJ` is an involution (`vnAdJ_vnAdJ`): apply `adJ ''` to both sides of
`J M J = M'`. -/
theorem tomita_JM'J_unconditional
    (hMdense : Dense {y : ℋ | ∃ x ∈ M, y = x ω})
    (hM'dense : Dense {y : ℋ | ∃ x ∈ commutantSA M, y = x ω})
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ))) :
    (fun x => vnAdJ M ω hsep hcyc x) '' (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)) := by
  rw [← tomita_JMJ_unconditional M ω hsep hcyc hMdense hM'dense hM, Set.image_image]
  simp only [vnAdJ_vnAdJ, Set.image_id']

end Lemma47

end Theses.RvD
