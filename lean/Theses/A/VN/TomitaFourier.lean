/-
**Rieffel–van Daele, §4: Lemma 4.8** — the Fourier step, and Tomita's theorem modulo
Lemma 4.7.

  M. A. Rieffel and A. van Daele, *A bounded operator approach to
  Tomita–Takesaki theory*, Pacific J. Math. **69** (1977) 187–221, pp. 204–205.

**This file has no thesis counterpart.**  It continues `Theses/A/VN/TomitaStrip.lean`
(RvD Lemmas 4.5 and 4.6) towards the commutation theorem; see
`docs/COMMUTATION-THEOREM.md`.

## Part I — uniqueness for the two-sided Laplace transform on a strip

Self-contained real analysis, with no von Neumann algebra in sight.

* `lapl h z = ∫ e^{-zt} h(t) dt`, the two-sided Laplace transform.
* `integrable_laplTerm`, `differentiableAt_lapl` : for `‖h t‖ ≤ C e^{-c|t|}` the integral
  converges and is **holomorphic** on the strip `|Re z| < c`.  Holomorphy is differentiation
  under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), dominated on
  a ball inside the strip by `C |t| e^{-(c-ρ)|t|}`; the auxiliary
  `integrable_abs_mul_exp_neg_mul_abs` is that dominating function's integrability.
* `eq_zero_of_lapl_eq_zero_on_real` : **if the transform vanishes on the real interval
  `(-c, c)` then `h = 0`.**  The strip is convex, hence preconnected, so
  `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` propagates the vanishing
  from the real axis to the whole strip; on the imaginary axis the transform *is* the Fourier
  transform of `h` (`Real.fourier_real_eq_integral_exp_smul` at `z = 2πiw`), so
  `𝓕 h = 0`, and `Continuous.fourierInv_fourier_eq` inverts it.

## Part II — the RvD kernel

* `rvdKernel φ t = e^{-φt}(e^{πt} + e^{-πt})^{-1}`, in exactly the shape `lemma_4_6`
  produces.  `inv_coshSum_le` is `(2 cosh πt)^{-1} ≤ e^{-π|t|}`, which is what makes the
  kernel-weighted function decay at the rate Part I needs; `rvdKernel_le` and
  `integrable_rvdKernel_mul` are the corresponding integrability.
* `eq_zero_of_rvdKernel_integral_eq_zero` : **RvD Lemma 4.8's analytic step.**  A bounded
  continuous `g` with `∫ e^{-φt}(e^{πt}+e^{-πt})^{-1} g(t) dt = 0` for every `φ ∈ (-π, π)`
  is zero.  This is Part I applied to `h(t) = (e^{πt}+e^{-πt})^{-1} g(t)`.

## Part III — RvD Lemma 4.8, and Theorem 4.2(1) modulo Lemma 4.7

* `modFlow M ω hsep hcyc x' t = Δ^{it} (J x' J) Δ^{-it}`, with `modFlow_zero`,
  `norm_modFlow_apply_le` and — the one nonobvious point —
  `inner_modFlow`/`continuous_inner_modFlow`: writing
  `⟪Δ^{it} y Δ^{-it} ξ, η⟫ = ⟪y (Δ^{-it} ξ), Δ^{-it} η⟫` moves *both* unitaries to the same
  side of the inner product, so continuity in `t` is `continuous_modPow_apply` twice and no
  joint-continuity argument is needed.
* `lemma_4_8` : **RvD Lemma 4.8**, `Δ^{it} J x' J Δ^{-it} ∈ M`, given Lemma 4.7 in the weak
  form `h47`.  RvD's proof verbatim: `y' ∈ M'` commutes with the `x ∈ M` that Lemma 4.7
  exhibits as the kernel average of the modular orbit, so
  `g(t) = ⟪[y', Δ^{it} J x' J Δ^{-it}] ξ, η⟫` has vanishing kernel average for every
  `φ ∈ (-π, π)`; Part II forces `g ≡ 0`, so `Δ^{it} J x' J Δ^{-it} ∈ M'' = M`.
* `adJ_commutant_subset` : Lemma 4.8 at `t = 0`, i.e. `J M' J ⊆ M` — precisely the
  hypothesis `hadJ` that `TomitaTakesaki.tomita_JMJ` takes.
* `tomita_JMJ_of_lemma_4_7` : **RvD Theorem 4.2(1)**, `J M J = M'`, conditional on nothing
  but Lemma 4.7.

## Part IV — `Δ^{it} T = T Δ^{it}`

* `IsPowBase.opPow_commute_right` : anything commuting with a power base `X` commutes with
  `X^{iz}` (the two sides agree on the dense `ran X`), and hence
* `commute_R_T`, `commute_two_sub_R_T`, `commute_modPow_T` : `Δ^{it}` commutes with `T`.
  This is what lets the two `T`'s be stripped off at the end of Lemma 4.7's proof.

## What Lemma 4.7 needs

`lemma_4_7` is not in this file: `A/VN/TomitaAnalytic.lean` proves it, and with it
`tomita_JMJ_unconditional`.  What it costs is worth recording, because the paper hides it.

The identity-theorem step of Lemma 4.8 is holomorphy in the **Fourier parameter**, not
holomorphy of `Δ^{iz}`: RvD's `F(z) = ∫ e^{-zt}(e^{πt}+e^{-πt})^{-1} g(t) dt` is analytic in
`z` on `|Re z| < π` purely by dominated convergence, which is `differentiableAt_lapl` above.
Nothing in Part I, II or III uses holomorphy of an operator-valued power.

Lemma 4.7 does, and that is easy to miss.  RvD (p. 204) prove its integral representation by
applying Lemma 4.6 to

  `f(z) = ⟪R^{-z+1/2} (2-R)^{z+1/2} x R^{z+1/2} (2-R)^{-z+1/2} ξ, η⟫`,   `|Re z| ≤ 1/2`,

and the paper's justification is the single sentence "from Lemma 3.6 it follows that `f`
satisfies the requirements of Lemma 4.6".  Those requirements are `ContinuousOn f clStrip`,
`DifferentiableOn ℂ f opStrip` and a bound — i.e. **exactly RvD Lemma 3.6's continuity and
analyticity clauses**, which `A/VN/ModularGroup.lean` does not prove.  So holomorphy of the
operator powers *is* on the critical path for `J M J = M'`; it is consumed by 4.7, not by 4.8.

Three features of that dependency, all used in `A/VN/TomitaAnalytic.lean`:

1. **Inside the open strip nothing but `cfc` is needed.**  For `|Re z| < 1/2` all four
   exponents `±z + 1/2` have real part in `(0,1)`, *strictly* positive, so each factor is
   `cpowOp` — a plain continuous functional calculus — and `DifferentiableOn ℂ f opStrip`
   reduces to holomorphy of `w ↦ cfc (·^w) X` on `Re w > 0`.  The `LinearMap.extendOfNorm`
   device (`opPow`) is needed only on the *boundary* `Re z = ±1/2`, where one exponent
   becomes purely imaginary, and there only for **continuity**, not for differentiability.
2. **A convention trap for whoever reads `f`.**  Mathlib's inner product is conjugate
   linear in the *first* variable, so `z ↦ ⟪A(z) ξ, η⟫` is *anti*holomorphic when `A` is
   holomorphic.  The function fed to `lemma_4_6` must therefore be
   `f z = ⟪η, A(z) ξ⟫`, not RvD's `⟪A(z) ξ, η⟫`.  (This does not affect `h47` below, whose
   kernel is real, so the two forms are complex conjugates of one another and either may be
   used.)
3. Boundedness is free: for `X` with spectrum in `[0,2]` and `0 ≤ Re w ≤ 1`,
   `|t^w| = t^{Re w} ≤ 2`, so `‖cpowOp X w‖ ≤ 2` and `‖f z‖ ≤ 16 ‖x‖ ‖ξ‖ ‖η‖` on the closed
   strip.

The one ingredient of Lemma 4.7 that lives here rather than there is
`Commute (modPow K t) (T K)`, Part IV below.
-/
import Theses.A.VN.TomitaStrip
import Theses.A.VN.ModularGroup

set_option linter.unusedSectionVars false

open Complex ClosedSubmodule Theses.A.VN
open scoped ComplexInnerProductSpace ComplexOrder

namespace Theses.RvD

/-! ## Part I: uniqueness for the two-sided Laplace transform on a strip -/

section FourierUniqueness

open MeasureTheory Filter Topology Set

/-- `∫ e^{-z t} h(t) dt`, the two-sided Laplace transform of `h`. -/
noncomputable def lapl (h : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t : ℝ, Complex.exp (-(z * (t : ℂ))) * h t

variable {h : ℝ → ℂ} {C c : ℝ}

/-- The constant in an exponential-decay bound is nonnegative. -/
lemma nonneg_of_expBound (hb : ∀ t : ℝ, ‖h t‖ ≤ C * Real.exp (-c * |t|)) : 0 ≤ C := by
  have := hb 0
  simpa using le_trans (norm_nonneg _) this

lemma re_neg_mul_ofReal (z : ℂ) (t : ℝ) : (-(z * (t : ℂ))).re = -(z.re * t) := by
  simp

/-- The pointwise bound on the integrand of the Laplace transform. -/
lemma norm_laplTerm_le (hb : ∀ t : ℝ, ‖h t‖ ≤ C * Real.exp (-c * |t|)) (z : ℂ) (t : ℝ) :
    ‖Complex.exp (-(z * (t : ℂ))) * h t‖ ≤ C * Real.exp (-(c - |z.re|) * |t|) := by
  have hC : 0 ≤ C := nonneg_of_expBound hb
  rw [norm_mul, Complex.norm_exp, re_neg_mul_ofReal]
  have h1 : Real.exp (-(z.re * t)) ≤ Real.exp (|z.re| * |t|) := by
    refine Real.exp_le_exp.2 ?_
    calc -(z.re * t) ≤ |z.re * t| := neg_le_abs _
      _ = |z.re| * |t| := abs_mul _ _
  calc Real.exp (-(z.re * t)) * ‖h t‖
      ≤ Real.exp (|z.re| * |t|) * (C * Real.exp (-c * |t|)) := by
        refine mul_le_mul h1 (hb t) (norm_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (-(c - |z.re|) * |t|) := by
        rw [show (-(c - |z.re|) * |t|) = |z.re| * |t| + -c * |t| by ring, Real.exp_add]
        ring

/-- `t ↦ |t| e^{-c|t|}` is integrable for `c > 0`. -/
lemma integrable_abs_mul_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    MeasureTheory.Integrable (fun t : ℝ => |t| * Real.exp (-c * |t|)) := by
  have hmaj : MeasureTheory.Integrable (fun t : ℝ => (2 / c) * Real.exp (-(c / 2) * |t|)) :=
    (integrable_exp_neg_mul_abs (by linarith)).const_mul _
  refine hmaj.mono' ?_ ?_
  · exact ((continuous_abs.mul ((Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)))).aestronglyMeasurable)
  · filter_upwards with t
    have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
    have hkey : |t| ≤ (2 / c) * Real.exp ((c / 2) * |t|) := by
      have h1 : (c / 2) * |t| ≤ Real.exp ((c / 2) * |t|) := by
        have := Real.add_one_le_exp ((c / 2) * |t|)
        linarith
      have hc2 : (0 : ℝ) < 2 / c := by positivity
      calc |t| = (2 / c) * ((c / 2) * |t|) := by field_simp
        _ ≤ (2 / c) * Real.exp ((c / 2) * |t|) := mul_le_mul_of_nonneg_left h1 hc2.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc |t| * Real.exp (-c * |t|)
        ≤ ((2 / c) * Real.exp ((c / 2) * |t|)) * Real.exp (-c * |t|) := by
          exact mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
      _ = (2 / c) * Real.exp (-(c / 2) * |t|) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- The Laplace integrand is integrable on the strip `|Re z| < c`. -/
lemma integrable_laplTerm (hcont : Continuous h)
    (hb : ∀ t : ℝ, ‖h t‖ ≤ C * Real.exp (-c * |t|)) {z : ℂ} (hz : |z.re| < c) :
    MeasureTheory.Integrable (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * h t) := by
  refine ((integrable_exp_neg_mul_abs (c := c - |z.re|) (by linarith)).const_mul C).mono'
    ?_ ?_
  · exact ((Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).neg)).mul hcont).aestronglyMeasurable
  · filter_upwards with t using norm_laplTerm_le hb z t

/-- The `z`-derivative of the Laplace integrand. -/
lemma hasDerivAt_laplTerm (t : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-(w * (t : ℂ))) * h t)
      ((-(t : ℂ)) * Complex.exp (-(z * (t : ℂ))) * h t) z := by
  have hfun : (fun w : ℂ => -(w * (t : ℂ))) = (fun w : ℂ => (-(t : ℂ)) * w) := by
    funext w; ring
  have h1 : HasDerivAt (fun w : ℂ => -(w * (t : ℂ))) (-(t : ℂ)) z := by
    rw [hfun]
    simpa using (hasDerivAt_id z).const_mul (-(t : ℂ))
  have e : (-(t : ℂ)) * Complex.exp (-(z * (t : ℂ))) * h t
      = Complex.exp (-(z * (t : ℂ))) * (-(t : ℂ)) * h t := by ring
  rw [e]
  exact (h1.cexp).mul_const (h t)

/-- **The Laplace transform is holomorphic on the strip `|Re z| < c`.**  Differentiation under
the integral sign, dominated by `C |t| e^{-(c-ρ)|t|}` on a ball inside the strip. -/
lemma differentiableAt_lapl (hcont : Continuous h)
    (hb : ∀ t : ℝ, ‖h t‖ ≤ C * Real.exp (-c * |t|)) {z₀ : ℂ} (hz : |z₀.re| < c) :
    DifferentiableAt ℂ (lapl h) z₀ := by
  have hC : 0 ≤ C := nonneg_of_expBound hb
  set ε : ℝ := (c - |z₀.re|) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  set ρ : ℝ := |z₀.re| + ε with hρdef
  have hρc : ρ < c := by rw [hρdef, hεdef]; linarith
  have hmem : ∀ w ∈ Metric.ball z₀ ε, |w.re| < ρ := by
    intro w hw
    have h1 : |w.re - z₀.re| ≤ ‖w - z₀‖ := by
      simpa using Complex.abs_re_le_norm (w - z₀)
    have h2 : ‖w - z₀‖ < ε := by simpa [Complex.dist_eq] using hw
    have h3 : |w.re| - |z₀.re| ≤ |w.re - z₀.re| := abs_sub_abs_le_abs_sub _ _
    rw [hρdef]; linarith
  have hbound : ∀ᵐ t : ℝ, ∀ w ∈ Metric.ball z₀ ε,
      ‖(-(t : ℂ)) * Complex.exp (-(w * (t : ℂ))) * h t‖
        ≤ C * (|t| * Real.exp (-(c - ρ) * |t|)) := by
    filter_upwards with t w hw
    have hwre := hmem w hw
    have e1 : ‖(-(t : ℂ)) * Complex.exp (-(w * (t : ℂ))) * h t‖
        = |t| * ‖Complex.exp (-(w * (t : ℂ))) * h t‖ := by
      rw [mul_assoc, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    rw [e1]
    have e2 := norm_laplTerm_le hb w t
    have e3 : Real.exp (-(c - |w.re|) * |t|) ≤ Real.exp (-(c - ρ) * |t|) := by
      refine Real.exp_le_exp.2 ?_
      have : -(c - |w.re|) ≤ -(c - ρ) := by linarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg t)
    calc |t| * ‖Complex.exp (-(w * (t : ℂ))) * h t‖
        ≤ |t| * (C * Real.exp (-(c - |w.re|) * |t|)) :=
          mul_le_mul_of_nonneg_left e2 (abs_nonneg t)
      _ ≤ |t| * (C * Real.exp (-(c - ρ) * |t|)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e3 hC) (abs_nonneg t)
      _ = C * (|t| * Real.exp (-(c - ρ) * |t|)) := by ring
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (t : ℝ) => Complex.exp (-(w * (t : ℂ))) * h t)
    (F' := fun (w : ℂ) (t : ℝ) => (-(t : ℂ)) * Complex.exp (-(w * (t : ℂ))) * h t)
    (bound := fun t : ℝ => C * (|t| * Real.exp (-(c - ρ) * |t|)))
    (Metric.ball_mem_nhds z₀ hεpos)
    (Filter.Eventually.of_forall (fun w =>
      ((Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).neg)).mul hcont).aestronglyMeasurable))
    (integrable_laplTerm hcont hb hz)
    (((Complex.continuous_ofReal.neg).mul (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).neg))).mul hcont).aestronglyMeasurable
    hbound
    ((integrable_abs_mul_exp_neg_mul_abs (c := c - ρ) (by linarith)).const_mul C)
    (Filter.Eventually.of_forall (fun t w _ => hasDerivAt_laplTerm t w))
  exact hres.2.differentiableAt

/-- `h` itself is integrable under an exponential-decay bound. -/
lemma integrable_of_expBound (hcont : Continuous h)
    (hb : ∀ t : ℝ, ‖h t‖ ≤ C * Real.exp (-c * |t|)) (hc : 0 < c) :
    MeasureTheory.Integrable h := by
  refine ((integrable_exp_neg_mul_abs hc).const_mul C).mono' hcont.aestronglyMeasurable ?_
  filter_upwards with t using hb t

/-- The open strip `|Re z| < c`. -/
def laplStrip (c : ℝ) : Set ℂ := {z : ℂ | |z.re| < c}

lemma mem_laplStrip {z : ℂ} : z ∈ laplStrip c ↔ |z.re| < c := Iff.rfl

lemma isOpen_laplStrip (c : ℝ) : IsOpen (laplStrip c) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

lemma laplStrip_eq_preimage (c : ℝ) :
    laplStrip c = (Complex.reCLM : ℂ →L[ℝ] ℝ) ⁻¹' (Set.Ioo (-c) c) := by
  ext z
  simp [laplStrip, abs_lt, Set.mem_Ioo, and_comm]

lemma convex_laplStrip (c : ℝ) : Convex ℝ (laplStrip c) := by
  rw [laplStrip_eq_preimage]
  exact (convex_Ioo (-c) c).linear_preimage (Complex.reCLM : ℂ →L[ℝ] ℝ).toLinearMap

lemma isPreconnected_laplStrip (c : ℝ) : IsPreconnected (laplStrip c) :=
  (convex_laplStrip c).isPreconnected

open FourierTransform

/-- **Uniqueness for the two-sided Laplace transform on a strip.**  This is the analytic core of
RvD Lemma 4.8: an exponentially decaying continuous function whose two-sided Laplace transform
vanishes on the *real* interval `(-c, c)` vanishes identically.

The proof is RvD's: the transform is holomorphic on the strip `|Re z| < c` (differentiation under
the integral sign), so vanishing on a real interval forces it to vanish on the whole strip by the
identity theorem; on the imaginary axis it is the Fourier transform of `h`, which is therefore
zero, and the Fourier transform is injective on continuous integrable functions. -/
theorem eq_zero_of_lapl_eq_zero_on_real (hcont : Continuous h) (hc : 0 < c)
    (hb : ∀ t : ℝ, ‖h t‖ ≤ C * Real.exp (-c * |t|))
    (hzero : ∀ φ : ℝ, |φ| < c → lapl h (φ : ℂ) = 0) :
    h = 0 := by
  -- holomorphy on the strip
  have hdiff : DifferentiableOn ℂ (lapl h) (laplStrip c) := fun z hz =>
    (differentiableAt_lapl hcont hb (mem_laplStrip.1 hz)).differentiableWithinAt
  have hana : AnalyticOnNhd ℂ (lapl h) (laplStrip c) :=
    hdiff.analyticOnNhd (isOpen_laplStrip c)
  -- the transform vanishes near `0` along the real axis
  have hfreqR : ∀ᶠ x : ℝ in nhdsWithin 0 {(0 : ℝ)}ᶜ, lapl h ((x : ℝ) : ℂ) = 0 := by
    have hnb : ∀ᶠ x : ℝ in nhds (0 : ℝ), |x| < c := by
      have : Continuous fun x : ℝ => |x| := continuous_abs
      exact (this.tendsto 0).eventually_lt_const (by simpa using hc)
    filter_upwards [nhdsWithin_le_nhds hnb] with x hx using hzero x hx
  have htend : Filter.Tendsto (fun x : ℝ => ((x : ℝ) : ℂ))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using Complex.ofReal_ne_zero.2 hx
  have hfreq : ∃ᶠ z : ℂ in nhdsWithin 0 {(0 : ℂ)}ᶜ, lapl h z = 0 :=
    htend.frequently hfreqR.frequently
  -- the identity theorem
  have hzero0 : (0 : ℂ) ∈ laplStrip c := by simpa [mem_laplStrip] using hc
  have heq : Set.EqOn (lapl h) 0 (laplStrip c) :=
    hana.eqOn_zero_of_preconnected_of_frequently_eq_zero (isPreconnected_laplStrip c) hzero0 hfreq
  -- on the imaginary axis the transform is the Fourier transform
  have hint : MeasureTheory.Integrable h := integrable_of_expBound hcont hb hc
  have hfour : 𝓕 h = 0 := by
    funext w
    have hmem : (((2 * Real.pi * w : ℝ) : ℂ) * Complex.I) ∈ laplStrip c := by
      simpa [mem_laplStrip] using hc
    have h0 := heq hmem
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [Pi.zero_apply] at h0 ⊢
    rw [← h0, lapl]
    refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun t => ?_)
    simp only [smul_eq_mul]
    have harg : ((-2 * Real.pi * t * w : ℝ) : ℂ) * Complex.I
        = -(((2 * Real.pi * w : ℝ) : ℂ) * Complex.I * (t : ℂ)) := by
      push_cast; ring
    rw [harg]
  have hfourint : MeasureTheory.Integrable (𝓕 h) := by
    rw [hfour]; exact MeasureTheory.integrable_zero _ _ _
  have hinv := hcont.fourierInv_fourier_eq hint hfourint
  rw [hfour] at hinv
  rw [← hinv]
  funext w
  simp [Real.fourierInv_eq]

end FourierUniqueness

/-! ## Part II: the RvD kernel and Lemma 4.8's analytic step -/

section Kernel

open MeasureTheory Filter Topology Set

/-- RvD's kernel `e^{-φ t} (e^{π t} + e^{-π t})^{-1}`, in exactly the shape `lemma_4_6`
produces it. -/
noncomputable def rvdKernel (φ t : ℝ) : ℝ :=
  Real.exp (-(φ * t)) * (Real.exp (Real.pi * t) + Real.exp (-(Real.pi * t)))⁻¹

lemma coshSum_pos (t : ℝ) : (0 : ℝ) < Real.exp (Real.pi * t) + Real.exp (-(Real.pi * t)) := by
  positivity

/-- `(e^{πt} + e^{-πt})^{-1} ≤ e^{-π|t|}`. -/
lemma inv_coshSum_le (t : ℝ) :
    (Real.exp (Real.pi * t) + Real.exp (-(Real.pi * t)))⁻¹ ≤ Real.exp (-(Real.pi * |t|)) := by
  have hpos := coshSum_pos t
  have hge : Real.exp (Real.pi * |t|) ≤ Real.exp (Real.pi * t) + Real.exp (-(Real.pi * t)) := by
    rcases abs_cases t with ⟨ht, -⟩ | ⟨ht, -⟩
    · rw [ht]; have := (Real.exp_pos (-(Real.pi * t))).le; linarith
    · rw [ht]
      have h1 : Real.pi * -t = -(Real.pi * t) := by ring
      rw [h1]
      have := (Real.exp_pos (Real.pi * t)).le; linarith
  have h2 : Real.exp (-(Real.pi * |t|)) = 1 / Real.exp (Real.pi * |t|) := by
    rw [Real.exp_neg, one_div]
  rw [h2, ← one_div (Real.exp (Real.pi * t) + Real.exp (-(Real.pi * t)))]
  exact one_div_le_one_div_of_le (Real.exp_pos _) hge

lemma continuous_rvdKernel (φ : ℝ) : Continuous (rvdKernel φ) := by
  unfold rvdKernel
  refine (Real.continuous_exp.comp (by fun_prop)).mul ?_
  exact (((Real.continuous_exp.comp (by fun_prop)).add
    (Real.continuous_exp.comp (by fun_prop))).inv₀ (fun t => (coshSum_pos t).ne'))

/-- **RvD Lemma 4.8, the analytic step.**  A bounded continuous function whose RvD-kernel
averages all vanish is zero.  This is the Fourier inversion at the heart of Lemma 4.8: the
transform `z ↦ ∫ e^{-z t}(e^{πt}+e^{-πt})^{-1} g(t) dt` is holomorphic on `|Re z| < π`,
vanishes on the real interval `(-π, π)`, hence on the whole strip by the identity theorem,
hence on the imaginary axis, where it is the Fourier transform of
`t ↦ (e^{πt}+e^{-πt})^{-1} g(t)`. -/
theorem eq_zero_of_rvdKernel_integral_eq_zero {g : ℝ → ℂ} (hgc : Continuous g) {B : ℝ}
    (hB : ∀ t : ℝ, ‖g t‖ ≤ B)
    (h0 : ∀ φ : ℝ, |φ| < Real.pi → (∫ t : ℝ, (rvdKernel φ t : ℂ) * g t) = 0) :
    g = 0 := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  set k : ℝ → ℝ := fun t => (Real.exp (Real.pi * t) + Real.exp (-(Real.pi * t)))⁻¹ with hk
  set h : ℝ → ℂ := fun t => ((k t : ℝ) : ℂ) * g t with hhdef
  have hkc : Continuous k := by
    refine (((Real.continuous_exp.comp (by fun_prop)).add
      (Real.continuous_exp.comp (by fun_prop))).inv₀ (fun t => (coshSum_pos t).ne'))
  have hhc : Continuous h := (Complex.continuous_ofReal.comp hkc).mul hgc
  have hhb : ∀ t : ℝ, ‖h t‖ ≤ B * Real.exp (-Real.pi * |t|) := by
    intro t
    have hkpos : 0 < k t := inv_pos.2 (coshSum_pos t)
    rw [hhdef]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkpos]
    calc k t * ‖g t‖ ≤ Real.exp (-(Real.pi * |t|)) * B :=
          mul_le_mul (inv_coshSum_le t) (hB t) (norm_nonneg _) (Real.exp_pos _).le
      _ = B * Real.exp (-Real.pi * |t|) := by rw [show -Real.pi * |t| = -(Real.pi * |t|) by ring]; ring
  have hlap : ∀ φ : ℝ, |φ| < Real.pi → lapl h (φ : ℂ) = 0 := by
    intro φ hφ
    rw [lapl, ← h0 φ hφ]
    refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun t => ?_)
    have harg : -((φ : ℂ) * (t : ℂ)) = ((-(φ * t) : ℝ) : ℂ) := by push_cast; ring
    have e1 : ((rvdKernel φ t : ℝ) : ℂ)
        = Complex.exp (-((φ : ℂ) * (t : ℂ))) * (((k t : ℝ)) : ℂ) := by
      rw [rvdKernel, Complex.ofReal_mul, Complex.ofReal_exp, ← harg]
    show Complex.exp (-((φ : ℂ) * (t : ℂ))) * (((k t : ℝ) : ℂ) * g t)
        = ((rvdKernel φ t : ℝ) : ℂ) * g t
    rw [e1]; ring
  have := eq_zero_of_lapl_eq_zero_on_real hhc Real.pi_pos hhb hlap
  funext t
  have ht : h t = 0 := by rw [this]; rfl
  have hkne : (((k t : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ne_of_gt (inv_pos.2 (coshSum_pos t)))
  have := mul_eq_zero.1 ht
  rcases this with h1 | h1
  · exact absurd h1 hkne
  · simpa using h1

/-! ### Integrability against the RvD kernel -/

lemma rvdKernel_pos (φ t : ℝ) : 0 < rvdKernel φ t := by
  rw [rvdKernel]
  have := coshSum_pos t
  positivity

lemma rvdKernel_le (φ t : ℝ) : rvdKernel φ t ≤ Real.exp (-(Real.pi - |φ|) * |t|) := by
  rw [rvdKernel]
  have h1 : Real.exp (-(φ * t)) ≤ Real.exp (|φ| * |t|) := by
    refine Real.exp_le_exp.2 ?_
    calc -(φ * t) ≤ |φ * t| := neg_le_abs _
      _ = |φ| * |t| := abs_mul _ _
  calc Real.exp (-(φ * t)) * (Real.exp (Real.pi * t) + Real.exp (-(Real.pi * t)))⁻¹
      ≤ Real.exp (|φ| * |t|) * Real.exp (-(Real.pi * |t|)) :=
        mul_le_mul h1 (inv_coshSum_le t) (le_of_lt (inv_pos.2 (coshSum_pos t)))
          (Real.exp_pos _).le
    _ = Real.exp (-(Real.pi - |φ|) * |t|) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- Anything bounded and continuous is integrable against the RvD kernel, for `|φ| < π`. -/
lemma integrable_rvdKernel_mul {G : ℝ → ℂ} (hGc : Continuous G) {B : ℝ}
    (hGb : ∀ t : ℝ, ‖G t‖ ≤ B) {φ : ℝ} (hφ : |φ| < Real.pi) :
    MeasureTheory.Integrable (fun t : ℝ => (rvdKernel φ t : ℂ) * G t) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hGb 0)
  refine ((integrable_exp_neg_mul_abs (c := Real.pi - |φ|) (by linarith)).const_mul B).mono'
    ?_ ?_
  · exact ((Complex.continuous_ofReal.comp (continuous_rvdKernel φ)).mul hGc).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rvdKernel_pos φ t)]
    calc rvdKernel φ t * ‖G t‖
        ≤ Real.exp (-(Real.pi - |φ|) * |t|) * B :=
          mul_le_mul (rvdKernel_le φ t) (hGb t) (norm_nonneg _) (Real.exp_pos _).le
      _ = B * Real.exp (-(Real.pi - |φ|) * |t|) := by ring

end Kernel

/-! ## Part III: RvD Lemma 4.8 -/

section Lemma48

open MeasureTheory Filter Topology Set

variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable (M : StarSubalgebra ℂ (ℋ →L[ℂ] ℋ)) (ω : ℋ)
variable (hsep : Ksub M ω ⊓ (Ksub M ω).mulI = ⊥) (hcyc : Ksub M ω ⊔ (Ksub M ω).mulI = ⊤)

include hsep hcyc

/-- **RvD's `Δ^{it} (J x' J) Δ^{-it}`**, the modular flow of `J x' J`. -/
noncomputable def modFlow (x' : ℋ →L[ℂ] ℋ) (t : ℝ) : ℋ →L[ℂ] ℋ :=
  modPow (Ksub M ω) t * vnAdJ M ω hsep hcyc x' * modPow (Ksub M ω) (-t)

lemma modFlow_apply (x' : ℋ →L[ℂ] ℋ) (t : ℝ) (ξ : ℋ) :
    modFlow M ω hsep hcyc x' t ξ
      = modPow (Ksub M ω) t (vnAdJ M ω hsep hcyc x' (modPow (Ksub M ω) (-t) ξ)) := rfl

/-- At `t = 0` the modular flow is `J x' J` itself — this is the case Theorem 4.2(1) consumes. -/
lemma modFlow_zero (x' : ℋ →L[ℂ] ℋ) :
    modFlow M ω hsep hcyc x' 0 = vnAdJ M ω hsep hcyc x' := by
  rw [modFlow, neg_zero, modPow_zero _ hsep hcyc, one_mul, mul_one]

/-- `‖J x J ζ‖ ≤ ‖x‖ ‖ζ‖`: `J` is a real isometry. -/
lemma norm_vnAdJ_apply_le (x' : ℋ →L[ℂ] ℋ) (ζ : ℋ) :
    ‖vnAdJ M ω hsep hcyc x' ζ‖ ≤ ‖x'‖ * ‖ζ‖ := by
  rw [vnAdJ_apply, J_norm (Ksub M ω) hsep hcyc]
  calc ‖x' (J (Ksub M ω) ζ)‖ ≤ ‖x'‖ * ‖J (Ksub M ω) ζ‖ := x'.le_opNorm _
    _ = ‖x'‖ * ‖ζ‖ := by rw [J_norm (Ksub M ω) hsep hcyc]

/-- The modular flow is bounded by `‖x'‖`, uniformly in `t`. -/
lemma norm_modFlow_apply_le (x' : ℋ →L[ℂ] ℋ) (t : ℝ) (ξ : ℋ) :
    ‖modFlow M ω hsep hcyc x' t ξ‖ ≤ ‖x'‖ * ‖ξ‖ := by
  rw [modFlow_apply, norm_modPow_apply _ hsep hcyc]
  calc ‖vnAdJ M ω hsep hcyc x' (modPow (Ksub M ω) (-t) ξ)‖
      ≤ ‖x'‖ * ‖modPow (Ksub M ω) (-t) ξ‖ := norm_vnAdJ_apply_le M ω hsep hcyc x' _
    _ = ‖x'‖ * ‖ξ‖ := by rw [norm_modPow_apply _ hsep hcyc]

/-- The matrix coefficient of the modular flow, with both unitaries moved to the *same* side.
This is what makes its continuity in `t` immediate. -/
lemma inner_modFlow (x' : ℋ →L[ℂ] ℋ) (t : ℝ) (ξ η : ℋ) :
    (⟪modFlow M ω hsep hcyc x' t ξ, η⟫ : ℂ)
      = ⟪vnAdJ M ω hsep hcyc x' (modPow (Ksub M ω) (-t) ξ), modPow (Ksub M ω) (-t) η⟫ := by
  rw [modFlow_apply, inner_apply_left (modPow (Ksub M ω) t)]
  congr 1
  rw [star_modPow _ hsep hcyc]

/-- **The matrix coefficients of the modular flow are continuous in `t`.** -/
lemma continuous_inner_modFlow (x' : ℋ →L[ℂ] ℋ) (ξ η : ℋ) :
    Continuous (fun t : ℝ => (⟪modFlow M ω hsep hcyc x' t ξ, η⟫ : ℂ)) := by
  have hc : Continuous fun t : ℝ => modPow (Ksub M ω) (-t) ξ :=
    (continuous_modPow_apply (Ksub M ω) hsep hcyc ξ).comp continuous_neg
  have hd : Continuous fun t : ℝ => modPow (Ksub M ω) (-t) η :=
    (continuous_modPow_apply (Ksub M ω) hsep hcyc η).comp continuous_neg
  simp only [inner_modFlow M ω hsep hcyc]
  exact ((vnAdJ M ω hsep hcyc x').continuous.comp hc).inner hd

/-! ### RvD Lemma 4.8 -/

/-- **RvD Lemma 4.8**: `Δ^{it} J x' J Δ^{-it} ∈ M` for every `x' ∈ M'` and every real `t`,
*given RvD Lemma 4.7* in the weak form `h47`.

RvD's proof verbatim: `y' ∈ M'` commutes with the operator `x ∈ M` that Lemma 4.7 exhibits
as the kernel average of the modular orbit, so the commutator coefficient
`g(t) = ⟪[y', Δ^{it} J x' J Δ^{-it}] ξ, η⟫` has vanishing kernel average for every
`φ ∈ (−π, π)`; `eq_zero_of_rvdKernel_integral_eq_zero` then forces `g ≡ 0`, so
`Δ^{it} J x' J Δ^{-it}` lies in `M'' = M`. -/
theorem lemma_4_8
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    {x' : ℋ →L[ℂ] ℋ}
    (h47 : ∀ φ : ℝ, |φ| < Real.pi → ∃ x ∈ M, ∀ ξ η : ℋ,
      (⟪x ξ, η⟫ : ℂ)
        = ∫ s : ℝ, (rvdKernel φ s : ℂ) * ⟪modFlow M ω hsep hcyc x' s ξ, η⟫)
    (t : ℝ) : modFlow M ω hsep hcyc x' t ∈ M := by
  -- the commutator coefficient vanishes identically in `s`
  have key : ∀ y' ∈ commutantSA M, ∀ ξ η : ℋ, ∀ s : ℝ,
      (⟪(y' * modFlow M ω hsep hcyc x' s) ξ, η⟫ : ℂ)
        = ⟪(modFlow M ω hsep hcyc x' s * y') ξ, η⟫ := by
    intro y' hy' ξ η
    set A : ℝ → ℋ →L[ℂ] ℋ := fun s => modFlow M ω hsep hcyc x' s with hA
    have hA' : ∀ s : ℝ, modFlow M ω hsep hcyc x' s = A s := fun _ => rfl
    set G : ℝ → ℂ := fun s => (⟪(y' * A s) ξ, η⟫ : ℂ) - ⟪(A s * y') ξ, η⟫ with hG
    -- the two halves, with the unitaries moved so that continuity is visible
    have hL : ∀ s : ℝ, (⟪(y' * A s) ξ, η⟫ : ℂ) = ⟪A s ξ, (star y') η⟫ := fun s =>
      inner_apply_left y' (A s ξ) η
    have hR : ∀ s : ℝ, (⟪(A s * y') ξ, η⟫ : ℂ) = ⟪A s (y' ξ), η⟫ := fun _ => rfl
    have hGc : Continuous G := by
      simp only [hG, hL, hR]
      exact (continuous_inner_modFlow M ω hsep hcyc x' ξ ((star y') η)).sub
        (continuous_inner_modFlow M ω hsep hcyc x' (y' ξ) η)
    -- the uniform bound
    set B : ℝ := ‖y'‖ * ‖x'‖ * ‖ξ‖ * ‖η‖ with hB
    have hGb : ∀ s : ℝ, ‖G s‖ ≤ 2 * B := by
      intro s
      have hb1 : ‖(⟪(y' * A s) ξ, η⟫ : ℂ)‖ ≤ B := by
        calc ‖(⟪(y' * A s) ξ, η⟫ : ℂ)‖ ≤ ‖(y' * A s) ξ‖ * ‖η‖ := norm_inner_le_norm _ _
          _ ≤ (‖y'‖ * (‖x'‖ * ‖ξ‖)) * ‖η‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              calc ‖(y' * A s) ξ‖ = ‖y' (A s ξ)‖ := rfl
                _ ≤ ‖y'‖ * ‖A s ξ‖ := y'.le_opNorm _
                _ ≤ ‖y'‖ * (‖x'‖ * ‖ξ‖) :=
                    mul_le_mul_of_nonneg_left
                      (norm_modFlow_apply_le M ω hsep hcyc x' s ξ) (norm_nonneg _)
          _ = B := by rw [hB]; ring
      have hb2 : ‖(⟪(A s * y') ξ, η⟫ : ℂ)‖ ≤ B := by
        calc ‖(⟪(A s * y') ξ, η⟫ : ℂ)‖ ≤ ‖(A s * y') ξ‖ * ‖η‖ := norm_inner_le_norm _ _
          _ ≤ (‖x'‖ * (‖y'‖ * ‖ξ‖)) * ‖η‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              calc ‖(A s * y') ξ‖ = ‖A s (y' ξ)‖ := rfl
                _ ≤ ‖x'‖ * ‖y' ξ‖ := norm_modFlow_apply_le M ω hsep hcyc x' s _
                _ ≤ ‖x'‖ * (‖y'‖ * ‖ξ‖) :=
                    mul_le_mul_of_nonneg_left (y'.le_opNorm _) (norm_nonneg _)
          _ = B := by rw [hB]; ring
      calc ‖G s‖ ≤ ‖(⟪(y' * A s) ξ, η⟫ : ℂ)‖ + ‖(⟪(A s * y') ξ, η⟫ : ℂ)‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add hb1 hb2
        _ = 2 * B := by ring
    -- the kernel averages all vanish
    have hzero : ∀ φ : ℝ, |φ| < Real.pi → (∫ s : ℝ, (rvdKernel φ s : ℂ) * G s) = 0 := by
      intro φ hφ
      obtain ⟨x, hxM, hx⟩ := h47 φ hφ
      have hint1 : MeasureTheory.Integrable
          (fun s : ℝ => (rvdKernel φ s : ℂ) * (⟪(y' * A s) ξ, η⟫ : ℂ)) := by
        refine integrable_rvdKernel_mul (B := ‖y'‖ * (‖x'‖ * ‖ξ‖) * ‖η‖) ?_ (fun s => ?_) hφ
        · simp only [hL]
          exact continuous_inner_modFlow M ω hsep hcyc x' ξ ((star y') η)
        · calc ‖(⟪(y' * A s) ξ, η⟫ : ℂ)‖ ≤ ‖(y' * A s) ξ‖ * ‖η‖ := norm_inner_le_norm _ _
            _ ≤ (‖y'‖ * (‖x'‖ * ‖ξ‖)) * ‖η‖ := by
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                calc ‖(y' * A s) ξ‖ = ‖y' (A s ξ)‖ := rfl
                  _ ≤ ‖y'‖ * ‖A s ξ‖ := y'.le_opNorm _
                  _ ≤ ‖y'‖ * (‖x'‖ * ‖ξ‖) :=
                      mul_le_mul_of_nonneg_left
                        (norm_modFlow_apply_le M ω hsep hcyc x' s ξ) (norm_nonneg _)
      have hint2 : MeasureTheory.Integrable
          (fun s : ℝ => (rvdKernel φ s : ℂ) * (⟪(A s * y') ξ, η⟫ : ℂ)) := by
        refine integrable_rvdKernel_mul (B := ‖x'‖ * (‖y'‖ * ‖ξ‖) * ‖η‖) ?_ (fun s => ?_) hφ
        · simp only [hR]
          exact continuous_inner_modFlow M ω hsep hcyc x' (y' ξ) η
        · calc ‖(⟪(A s * y') ξ, η⟫ : ℂ)‖ ≤ ‖(A s * y') ξ‖ * ‖η‖ := norm_inner_le_norm _ _
            _ ≤ (‖x'‖ * (‖y'‖ * ‖ξ‖)) * ‖η‖ := by
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                calc ‖(A s * y') ξ‖ = ‖A s (y' ξ)‖ := rfl
                  _ ≤ ‖x'‖ * ‖y' ξ‖ := norm_modFlow_apply_le M ω hsep hcyc x' s _
                  _ ≤ ‖x'‖ * (‖y'‖ * ‖ξ‖) :=
                      mul_le_mul_of_nonneg_left (y'.le_opNorm _) (norm_nonneg _)
      -- `y'` commutes with `x`
      have hcomm : x * y' = y' * x := mem_commutantSA.1 hy' x hxM
      have e1 : (⟪(y' * x) ξ, η⟫ : ℂ)
          = ∫ s : ℝ, (rvdKernel φ s : ℂ) * (⟪(y' * A s) ξ, η⟫ : ℂ) := by
        have h1 : (⟪(y' * x) ξ, η⟫ : ℂ) = ⟪x ξ, (star y') η⟫ := inner_apply_left y' (x ξ) η
        rw [h1, hx ξ ((star y') η)]
        refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun s => ?_)
        simp only [hA', hL]
      have e2 : (⟪(x * y') ξ, η⟫ : ℂ)
          = ∫ s : ℝ, (rvdKernel φ s : ℂ) * (⟪(A s * y') ξ, η⟫ : ℂ) := by
        have h1 : (⟪(x * y') ξ, η⟫ : ℂ) = ⟪x (y' ξ), η⟫ := rfl
        rw [h1, hx (y' ξ) η]
        refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun s => ?_)
        simp only [hA', hR]
      have e3 : (∫ s : ℝ, (rvdKernel φ s : ℂ) * (⟪(y' * A s) ξ, η⟫ : ℂ))
          = ∫ s : ℝ, (rvdKernel φ s : ℂ) * (⟪(A s * y') ξ, η⟫ : ℂ) := by
        rw [← e1, ← e2, hcomm]
      have hsplit : (fun s : ℝ => (rvdKernel φ s : ℂ) * G s)
          = fun s : ℝ => (rvdKernel φ s : ℂ) * (⟪(y' * A s) ξ, η⟫ : ℂ)
              - (rvdKernel φ s : ℂ) * (⟪(A s * y') ξ, η⟫ : ℂ) := by
        funext s
        rw [hG]
        ring
      rw [hsplit, MeasureTheory.integral_sub hint1 hint2, e3, sub_self]
    have := eq_zero_of_rvdKernel_integral_eq_zero hGc hGb hzero
    intro s
    have hs : G s = 0 := by rw [this]; rfl
    rw [hG] at hs
    exact sub_eq_zero.1 hs
  -- `Δ^{it} J x' J Δ^{-it}` commutes with everything in `M'`, hence lies in `M'' = M`
  rw [← SetLike.mem_coe, ← hM, commutant, Set.mem_centralizer_iff]
  intro y' hy'
  have hy'SA : y' ∈ commutantSA M := by
    rw [← SetLike.mem_coe, coe_commutantSA]; exact hy'
  ext ξ
  exact ext_inner_right ℂ (fun η => key y' hy'SA ξ η t)

/-- **RvD Lemma 4.8 at `t = 0`**: `J M' J ⊆ M`.  This is exactly the hypothesis `hadJ` of
`tomita_JMJ`, so it is the last missing input to Tomita's theorem. -/
theorem adJ_commutant_subset
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    (h47 : ∀ x' ∈ commutantSA M, ∀ φ : ℝ, |φ| < Real.pi → ∃ x ∈ M, ∀ ξ η : ℋ,
      (⟪x ξ, η⟫ : ℂ)
        = ∫ s : ℝ, (rvdKernel φ s : ℂ) * ⟪modFlow M ω hsep hcyc x' s ξ, η⟫) :
    ∀ x' ∈ commutantSA M, vnAdJ M ω hsep hcyc x' ∈ M := by
  intro x' hx'
  have h := lemma_4_8 M ω hsep hcyc hM (h47 x' hx') 0
  rwa [modFlow_zero] at h

/-- **RvD Theorem 4.2(1)**, `J M J = M'`, conditional only on RvD Lemma 4.7.  Everything else
— Lemma 4.9, Lemma 4.8's Fourier step, and Theorem 4.2(1) itself — is discharged. -/
theorem tomita_JMJ_of_lemma_4_7
    (hMdense : Dense {y : ℋ | ∃ x ∈ M, y = x ω})
    (hM'dense : Dense {y : ℋ | ∃ x ∈ commutantSA M, y = x ω})
    (hM : commutant (ℋ →L[ℂ] ℋ) (commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)))
      = (M : Set (ℋ →L[ℂ] ℋ)))
    (h47 : ∀ x' ∈ commutantSA M, ∀ φ : ℝ, |φ| < Real.pi → ∃ x ∈ M, ∀ ξ η : ℋ,
      (⟪x ξ, η⟫ : ℂ)
        = ∫ s : ℝ, (rvdKernel φ s : ℂ) * ⟪modFlow M ω hsep hcyc x' s ξ, η⟫) :
    (fun x => vnAdJ M ω hsep hcyc x) '' (M : Set (ℋ →L[ℂ] ℋ))
      = commutant (ℋ →L[ℂ] ℋ) (M : Set (ℋ →L[ℂ] ℋ)) :=
  tomita_JMJ M ω hsep hcyc hMdense hM'dense (adJ_commutant_subset M ω hsep hcyc hM h47)

end Lemma48

/-! ## Part IV: `Δ^{it}` commutes with `T`

The second of the two ingredients Lemma 4.7 needs beyond RvD Lemma 3.6.  At the end of its
proof RvD strip the two `T`'s off `⟪T x T ξ, η⟫ = ∫ k ⟪Δ^{it} T (J x' J) T Δ^{-it} ξ, η⟫`,
which is legitimate exactly because `Δ^{it}` and `T` are both functions of `R`. -/

section CommuteT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If `Y` commutes with a power base `X`, then it commutes with `X^{iz}`: the two sides agree
on the dense range of `X`, where `X^{iz}` is the honest continuous functional calculus. -/
theorem IsPowBase.opPow_commute_right {X Y : H →L[ℂ] H} (hX : IsPowBase X)
    (hcomm : Commute X Y) {z : ℂ} (hz : z.im ≤ 0) : Commute (opPow X z) Y := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  refine hX.denseRange.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro ζ
  have hYX : Y (X ζ) = X (Y ζ) := congrArg (fun A : H →L[ℂ] H => A ζ) hcomm.eq.symm
  show opPow X z (Y (X ζ)) = Y (opPow X z (X ζ))
  rw [hYX, hX.opPow_apply hz, hX.opPow_apply hz]
  exact congrArg (fun A : H →L[ℂ] H => A ζ) (hX.commute_cpowOp_right hcomm (1 + I * z)).eq

variable (K : ClosedSubmodule ℝ H)

/-- `R` commutes with `T = (R(2-R))^{1/2}`. -/
theorem commute_R_T : Commute (R K) (T K) :=
  ContinuousLinearMap.ext fun x => R_comm_T K x

/-- `2 - R` commutes with `T`. -/
theorem commute_two_sub_R_T : Commute ((2 : H →L[ℂ] H) - R K) (T K) := by
  have h : R K * T K = T K * R K := (commute_R_T K).eq
  show ((2 : H →L[ℂ] H) - R K) * T K = T K * ((2 : H →L[ℂ] H) - R K)
  rw [sub_mul, mul_sub, h, two_mul, mul_two]

variable (hsep : K ⊓ K.mulI = ⊥) (hcyc : K ⊔ K.mulI = ⊤)

include hsep hcyc

/-- **`Δ^{it} T = T Δ^{it}`.** -/
theorem commute_modPow_T (t : ℝ) : Commute (modPow K t) (T K) := by
  rw [modPow]
  exact Commute.mul_left
    ((isPowBase_two_sub_R K hsep).opPow_commute_right (commute_two_sub_R_T K) (by simp))
    ((isPowBase_R K hcyc).opPow_commute_right (commute_R_T K) (by simp))

end CommuteT

end Theses.RvD
