/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 1: C*-algebras — cstar.tex, lines 1714–3886.

  §Positive Elements
    Holomorphic Functions (parsecs 120–150: 𝒜-valued holomorphic functions,
                           power series, Goursat's theorem, Cauchy's integral
                           formula, Taylor expansion)
    Spectral Radius       (parsec 160: ‖a‖ = spectral radius for self-adjoint
                           a, Gelfand–Mazur; parsecs 170–200: consequences for
                           positive elements, order ideals, states)
    The Square Root       (parsecs 230–260: existence and uniqueness of √a,
                           positive and negative parts, a*a ≥ 0, vector
                           states, commutative C*-algebras)

All statements of parsecs 130 and 160–260 are proved.  Seven remain `sorry`,
all in parsecs 140–150 and all behind **14IV** `goursat`: `goursat` itself,
`invint_2`, `invint_2'`, `invint_3`, `invint_4`, `cauchy_formula` and `taylor`.
See CONVENTIONS.md for the numbering (**16II** = parsec 160, point 20) and
naming conventions.
-/
import Theses.A.CStar.Basic

open scoped ComplexOrder ComplexInnerProductSpace ComplexStarModule NNReal ENNReal
open Filter Topology

namespace Theses.A.CStar

/-! ## Parsec 120: holomorphic 𝒜-valued functions

**12I** (cstar.tex:1717): introduction — nothing to formalize.

**12II** (cstar.tex:1739, Setting): an *𝒜-valued function* is a partial map
`f : ℂ → 𝒜` with open domain; it is *holomorphic* at `x` when the difference
quotients `(f x - f y)/(x - y)` norm-converge as `y → x`, and the limit is its
*derivative* `f' x`.  In Mathlib this is differentiability of `f : ℂ → 𝒜` on
an open set `U` (`DifferentiableOn ℂ f U`, pointwise `HasDerivAt f f' x`),
where `𝒜` is any complex Banach space — in this file always a C*-algebra, as
in the thesis. -/

section Holomorphic

variable {𝒜 : Type*} [CStarAlgebra 𝒜]

/-- **12III** (cstar.tex:1769, Exercise), part 1 (sums): the sum of functions
holomorphic at `z` is holomorphic at `z`, with `(f + g)' = f' + g'`. -/
theorem holomorphic_add (f g : ℂ → 𝒜) (f' g' : 𝒜) (z : ℂ)
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) :
    HasDerivAt (fun w => f w + g w) (f' + g') z :=
  hf.add hg

/-- **12III** (cstar.tex:1769, Exercise), part 1 (products): the product of
functions holomorphic at `z` is holomorphic, with the Leibniz rule for the
derivative. -/
theorem holomorphic_mul (f g : ℂ → 𝒜) (f' g' : 𝒜) (z : ℂ)
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) :
    HasDerivAt (fun w => f w * g w) (f' * g z + f z * g') z :=
  hf.mul hg

/-- **12III** (cstar.tex:1769, Exercise), part 2: the function `z ↦ z`
(as the 𝒜-valued function `z ↦ z·1`) is holomorphic with derivative `1`. -/
theorem holomorphic_id (z : ℂ) :
    HasDerivAt (fun w => algebraMap ℂ 𝒜 w) (1 : 𝒜) z :=
  by
    simpa [Algebra.algebraMap_eq_smul_one] using (hasDerivAt_id z).smul_const (1 : 𝒜)

/-- **12III** (cstar.tex:1769, Exercise), part 3: constant functions are
holomorphic with derivative `0`. -/
theorem holomorphic_const (a : 𝒜) (z : ℂ) :
    HasDerivAt (fun _ : ℂ => a) (0 : 𝒜) z :=
  hasDerivAt_const z a

/-- **12III** (cstar.tex:1769, Exercise), part 4: a polynomial
`z ↦ ∑_{i ≤ n} zⁱ aᵢ` with coefficients in `𝒜` is holomorphic, with
derivative `z ↦ ∑ i zⁱ⁻¹ aᵢ`. -/
theorem holomorphic_polynomial (n : ℕ) (a : ℕ → 𝒜) (z : ℂ) :
    HasDerivAt (fun w => ∑ i ∈ Finset.range (n + 1), w ^ i • a i)
      (∑ i ∈ Finset.range (n + 1), ((i : ℂ) * z ^ (i - 1)) • a i) z :=
  by
    exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_pow i z).smul_const (a i)

/-! ## Parsec 130: power series -/

/-- The *radius of convergence* `R = (limsupₙ ‖aₙ‖^{1/n})⁻¹ ∈ [0,∞]` of a
power series `∑ₙ aₙ zⁿ` over `𝒜` (**13II**, `hadamard`, cstar.tex:1806). -/
noncomputable def radiusOfConvergence (a : ℕ → 𝒜) : ℝ≥0∞ :=
  (Filter.atTop.limsup fun n : ℕ => (‖a n‖₊ : ℝ≥0∞) ^ (1 / (n : ℝ)))⁻¹

/-- The power series `∑ₙ aₙ zⁿ` over `𝒜` as a Mathlib `FormalMultilinearSeries`;
the bridge used by **13II**, **13VI** and **15VII** below. -/
private noncomputable def fpsOfCoeffs (a : ℕ → 𝒜) : FormalMultilinearSeries ℂ ℂ 𝒜 :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n)

private theorem fpsOfCoeffs_apply (a : ℕ → 𝒜) (n : ℕ) (y : ℂ) :
    (fpsOfCoeffs a n fun _ => y) = y ^ n • a n := by
  simp [fpsOfCoeffs]

private theorem fpsOfCoeffs_norm (a : ℕ → 𝒜) (n : ℕ) : ‖fpsOfCoeffs a n‖ = ‖a n‖ := by
  simp [fpsOfCoeffs]

private theorem fpsOfCoeffs_coeff (a : ℕ → 𝒜) (n : ℕ) : (fpsOfCoeffs a).coeff n = a n := by
  simp [fpsOfCoeffs, FormalMultilinearSeries.coeff]

private theorem fpsOfCoeffs_nnnorm (a : ℕ → 𝒜) (n : ℕ) : ‖fpsOfCoeffs a n‖₊ = ‖a n‖₊ := by
  ext; simpa using fpsOfCoeffs_norm a n

/-- The thesis's Cauchy–Hadamard formula defining `radiusOfConvergence` is
literally Mathlib's `FormalMultilinearSeries.radius_inv_eq_limsup`. -/
private theorem radiusOfConvergence_eq (a : ℕ → 𝒜) :
    radiusOfConvergence a = (fpsOfCoeffs a).radius := by
  have hfun : (fun n : ℕ => ((‖a n‖₊ : ℝ≥0∞) ^ (1 / (n : ℝ))))
      = fun n : ℕ => (((‖fpsOfCoeffs a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0)) : ℝ≥0∞) := by
    funext n
    rw [ENNReal.coe_rpow_of_nonneg _ (by positivity), fpsOfCoeffs_nnnorm]
  rw [radiusOfConvergence, hfun, ← (fpsOfCoeffs a).radius_inv_eq_limsup, inv_inv]

/-- If `∑ₙ aₙ (z - w)ⁿ` sums to `f z` throughout `ball w r`, then `f` is
represented on that ball by the formal power series `fpsOfCoeffs a`. -/
private theorem fpsOfCoeffs_hasFPowerSeriesOnBall (a : ℕ → 𝒜) (f : ℂ → 𝒜) (w : ℂ) (r : ℝ)
    (hr : 0 < r)
    (hsmall : ∀ z ∈ Metric.ball w r, HasSum (fun n : ℕ => (z - w) ^ n • a n) (f z)) :
    HasFPowerSeriesOnBall f (fpsOfCoeffs a) w (ENNReal.ofReal r) := by
  have key : ∀ y : ℂ, ‖y‖ < r → HasSum (fun n : ℕ => y ^ n • a n) (f (w + y)) := by
    intro y hy
    have := hsmall (w + y) (by simp [Metric.mem_ball, dist_eq_norm, hy])
    simpa using this
  refine
    { r_le := ?_
      r_pos := ENNReal.ofReal_pos.mpr hr
      hasSum := ?_ }
  · -- the thesis's own argument for **13II**.2: the terms of a convergent
    -- series are bounded, so `r` does not exceed the radius of convergence
    refine ENNReal.le_of_forall_nnreal_lt fun u hu => ?_
    have hur : (u : ℝ) < r := by
      rw [← ENNReal.ofReal_coe_nnreal] at hu
      exact (ENNReal.ofReal_lt_ofReal_iff hr).mp hu
    have hs := key ((u : ℝ) : ℂ) (by simpa [abs_of_nonneg u.coe_nonneg] using hur)
    refine (fpsOfCoeffs a).le_radius_of_tendsto (l := 0) ?_
    have h0 := hs.summable.tendsto_atTop_zero.norm
    simpa [fpsOfCoeffs_coeff, norm_smul, abs_of_nonneg u.coe_nonneg, mul_comm] using h0
  · intro y hy
    rw [Metric.eball_ofReal, mem_ball_zero_iff] at hy
    simpa [fpsOfCoeffs_coeff] using key y hy

/-- **13II** (`hadamard`, cstar.tex:1806, Theorem), part 1: the series
`∑ₙ aₙ zⁿ` converges absolutely for `|z| < R`. -/
theorem hadamard_1 (a : ℕ → 𝒜) (z : ℂ)
    (hz : (‖z‖₊ : ℝ≥0∞) < radiusOfConvergence a) :
    Summable fun n : ℕ => ‖a n‖ * ‖z‖ ^ n :=
  by
    -- the thesis's `ε`-and-geometric-tail argument is Mathlib's
    -- `FormalMultilinearSeries.summable_norm_mul_pow`
    rw [radiusOfConvergence_eq] at hz
    simpa [fpsOfCoeffs_coeff] using (fpsOfCoeffs a).summable_norm_mul_pow (r := ‖z‖₊) hz

/-- **13II** (`hadamard`, cstar.tex:1806, Theorem), part 2: if `∑ₙ aₙ zⁿ`
converges then `|z| ≤ R`. -/
theorem hadamard_2 (a : ℕ → 𝒜) (z : ℂ)
    (hz : Summable fun n : ℕ => z ^ n • a n) :
    (‖z‖₊ : ℝ≥0∞) ≤ radiusOfConvergence a :=
  by
    -- exactly the thesis's argument: the terms `‖aₙ‖|z|ⁿ` of a convergent
    -- series tend to `0`, hence are bounded, hence `|z| ≤ R`
    rw [radiusOfConvergence_eq]
    refine (fpsOfCoeffs a).le_radius_of_tendsto (r := ‖z‖₊) (l := 0) ?_
    have h0 := hz.tendsto_atTop_zero.norm
    simpa [fpsOfCoeffs_coeff, norm_smul, mul_comm] using h0

/-- **13IV** (cstar.tex:1868, Proposition): the function given by a power
series `∑ₙ aₙ zⁿ` is holomorphic on the disk `|z| < R`, with derivative
`∑ₙ n aₙ zⁿ⁻¹`. -/
theorem powerSeries_hasDerivAt (a : ℕ → 𝒜) (z : ℂ)
    (hz : (‖z‖₊ : ℝ≥0∞) < radiusOfConvergence a) :
    HasDerivAt (fun w : ℂ => ∑' n : ℕ, w ^ n • a n)
      (∑' n : ℕ, ((n : ℂ) * z ^ (n - 1)) • a n) z :=
  by
    -- Divergence from the thesis's proof (cstar.tex:1868), which dominates the
    -- difference quotients uniformly by `2 ∑ₙ n‖aₙ‖ rⁿ⁻¹`.  Here: the series
    -- is its own power-series expansion on `ball 0 R`, so it is differentiable
    -- there, and `HasFPowerSeriesOnBall.fderiv` identifies its derivative with
    -- the term-wise derivative through `derivSeries_coeff_one`.
    rw [radiusOfConvergence_eq] at hz
    set p : FormalMultilinearSeries ℂ ℂ 𝒜 := fpsOfCoeffs a with hpdef
    have hpos : 0 < p.radius := lt_of_le_of_lt zero_le hz
    have hfun : (fun w : ℂ => ∑' n : ℕ, w ^ n • a n) = p.sum := by
      funext w
      exact (tsum_congr fun n => fpsOfCoeffs_apply a n w).symm
    have hp : HasFPowerSeriesOnBall (fun w : ℂ => ∑' n : ℕ, w ^ n • a n) p 0 p.radius := by
      rw [hfun]; exact p.hasFPowerSeriesOnBall hpos
    have hzmem : z ∈ Metric.eball (0 : ℂ) p.radius := by
      simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm] using hz
    -- the sum is differentiable at `z`
    have hdiff : DifferentiableAt ℂ (fun w : ℂ => ∑' n : ℕ, w ^ n • a n) z :=
      (hp.analyticOnNhd z hzmem).differentiableAt
    have hda := hdiff.hasFDerivAt.hasDerivAt
    -- and its derivative is the term-wise derivative
    have hsum := hp.fderiv.hasSum_sub hzmem
    have hsum1 := (ContinuousLinearMap.apply ℂ 𝒜 (1 : ℂ)).hasSum hsum
    simp only [ContinuousLinearMap.apply_apply, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      smul_apply, FormalMultilinearSeries.derivSeries_coeff_one, sub_zero] at hsum1
    have hg : HasSum (fun n : ℕ => ((n : ℂ) * z ^ (n - 1)) • a n)
        ((fderiv ℂ (fun w : ℂ => ∑' n : ℕ, w ^ n • a n) z) 1) := by
      have hshift : (fun b : ℕ => ((((b + 1) : ℕ) : ℂ) * z ^ ((b + 1) - 1)) • a (b + 1))
          = fun b : ℕ => z ^ b • ((b + 1) • p.coeff (b + 1)) := by
        funext b
        rw [hpdef, fpsOfCoeffs_coeff, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
        push_cast
        ring_nf
      have h2 : HasSum (fun b : ℕ => ((((b + 1) : ℕ) : ℂ) * z ^ ((b + 1) - 1)) • a (b + 1))
          ((fderiv ℂ (fun w : ℂ => ∑' n : ℕ, w ^ n • a n) z) 1) := by
        rw [hshift]; exact hsum1
      have h3 := (hasSum_nat_add_iff (f := fun n : ℕ => ((n : ℂ) * z ^ (n - 1)) • a n) 1).mp h2
      simpa using h3
    rw [hg.tsum_eq]
    exact hda

/-- **13VI** (`powerseries-uniqueness-coeffients`, cstar.tex:1958, Exercise):
if a power series `∑ₙ aₙ zⁿ` sums to `0` on some disk around `0` of positive
radius, then all its coefficients vanish. -/
theorem powerseries_uniqueness_coeffients (a : ℕ → 𝒜) (r : ℝ) (hr : 0 < r)
    (h : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => z ^ n • a n) 0) :
    ∀ n, a n = 0 :=
  by
    -- Divergence from the thesis's proof (cstar.tex:1958): the hint there is
    -- to differentiate the series repeatedly, which would make this depend on
    -- **13IV** `powerSeries_hasDerivAt` (still `sorry`).  In Lean the series
    -- represents the zero function on `ball 0 r`, and
    -- `HasFPowerSeriesAt.eq_zero` gives the conclusion outright.
    have hpow : HasFPowerSeriesOnBall (0 : ℂ → 𝒜) (fpsOfCoeffs a) 0 (ENNReal.ofReal r) := by
      refine fpsOfCoeffs_hasFPowerSeriesOnBall a 0 0 r hr ?_
      intro z hz
      rw [Metric.mem_ball, dist_zero_right] at hz
      simpa using h z hz
    have hzero : fpsOfCoeffs a = 0 := hpow.hasFPowerSeriesAt.eq_zero
    intro n
    have hn : fpsOfCoeffs a n = 0 := by rw [hzero]; rfl
    rw [fpsOfCoeffs, ContinuousMultilinearMap.mkPiRing_eq_zero_iff] at hn
    exact hn

/-! ## Parsec 140: integration and Goursat's theorem

**14II** (cstar.tex:2000, Exercise): the construction of the integral
`∫ f ∈ 𝒜` of a continuous `f : [0,1] → 𝒜` via 𝒜-valued step functions
(parts 1–3) is in Mathlib the Bochner integral `∫ t in (0:ℝ)..1, f t` of the
`MeasureTheory` library; part 4 is stated below. -/

/-- **14II** (cstar.tex:2000, Exercise), part 4: `∫ a f = a ∫ f` for
continuous `f : [0,1] → ℂ` and `a ∈ 𝒜`. -/
theorem integral_scalar_smul (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc 0 1))
    (a : 𝒜) :
    ∫ t in (0:ℝ)..1, f t • a = (∫ t in (0:ℝ)..1, f t) • a :=
  intervalIntegral.integral_smul_const f a

/-- **14III** (cstar.tex:2094, Definition): the integral
`∫_w^{w'} f = (w' - w) ∫₀¹ f(w + t(w' - w)) dt` of an 𝒜-valued function
along the line segment `[w, w']`. -/
noncomputable def segIntegral (f : ℂ → 𝒜) (w w' : ℂ) : 𝒜 :=
  (w' - w) • ∫ t in (0:ℝ)..1, f (w + (t : ℂ) * (w' - w))

/-- **14III** (cstar.tex:2094, Definition): the integral
`∫_T f = ∫_{w₀}^{w₁} f + ∫_{w₁}^{w₂} f + ∫_{w₂}^{w₀} f` of an 𝒜-valued
function along the triangle `T` with vertices `w₀, w₁, w₂`. -/
noncomputable def triIntegral (f : ℂ → 𝒜) (w₀ w₁ w₂ : ℂ) : 𝒜 :=
  segIntegral f w₀ w₁ + segIntegral f w₁ w₂ + segIntegral f w₂ w₀

/-- **14III** (cstar.tex:2094, Definition): `∠(w₀, z, w₁)`, the number of
radians in `(-π, π]` needed to rotate the ray from `z` through `w₀`
counterclockwise around `z` to hit `w₁` — here `arg ((w₁ - z)/(w₀ - z))`. -/
noncomputable def measuredAngle (w₀ z w₁ : ℂ) : ℝ :=
  Complex.arg ((w₁ - z) / (w₀ - z))

/-- **14III** (cstar.tex:2094, Definition): the *winding number* of the
triangle with vertices `w₀, w₁, w₂` around a point `z` not on its boundary:
`2π wn_T(z) = ∠(w₀,z,w₁) + ∠(w₁,z,w₂) + ∠(w₂,z,w₀)`. -/
noncomputable def windingNumber (w₀ w₁ w₂ z : ℂ) : ℝ :=
  (measuredAngle w₀ z w₁ + measuredAngle w₁ z w₂ + measuredAngle w₂ z w₀) /
    (2 * Real.pi)

/-- **14IV** (`goursat`, cstar.tex:2177, Goursat's Theorem): `∫_T f = 0` for
a holomorphic 𝒜-valued function `f` and a triangle `T` whose closure (convex
hull of its vertices) lies inside `dom(f)`. -/
theorem goursat {U : Set ℂ} (hU : IsOpen U) (f : ℂ → 𝒜)
    (hf : DifferentiableOn ℂ f U) (w₀ w₁ w₂ : ℂ)
    (hT : convexHull ℝ {w₀, w₁, w₂} ⊆ U) :
    triIntegral f w₀ w₁ w₂ = 0 :=
  sorry

/-- **14VIII** (`invint`, cstar.tex:2302, Exercise), part 1: for a non-zero
complex number `z`, `z⁻¹ = (Re z - i Im z)/(Re z² + Im z²)`. -/
theorem invint_1 (z : ℂ) (hz : z ≠ 0) :
    z⁻¹ = ((z.re : ℂ) - (z.im : ℂ) * Complex.I) /
      ((z.re : ℂ) ^ 2 + (z.im : ℂ) ^ 2) :=
  by
    have h1 : ((z.re : ℂ) ^ 2 + (z.im : ℂ) ^ 2) = (Complex.normSq z : ℂ) := by
      rw [Complex.normSq_apply]; push_cast; ring
    have h2 : ((z.re : ℂ) - (z.im : ℂ) * Complex.I) = (starRingEnd ℂ) z := by
      apply Complex.ext <;> simp
    rw [h1, h2, Complex.inv_def, div_eq_mul_inv, Complex.ofReal_inv]

/-- **14VIII** (`invint`, cstar.tex:2302, Exercise), part 2 (vertical
segment): `∫_a^{a+ib} z⁻¹ dz = i arctan(b/a) + log|a+ib| - log|ia|` for real
`a ≠ 0` and `b`. -/
theorem invint_2 (a b : ℝ) (ha : a ≠ 0) :
    segIntegral (fun z : ℂ => z⁻¹) (a : ℂ) ((a : ℂ) + (b : ℂ) * Complex.I) =
      (Real.arctan (b / a) : ℂ) * Complex.I +
        (Real.log ‖(a : ℂ) + (b : ℂ) * Complex.I‖ : ℂ) -
        (Real.log ‖(a : ℂ) * Complex.I‖ : ℂ) :=
  sorry

/-- **14VIII** (`invint`, cstar.tex:2302, Exercise), part 2 (horizontal
segment): `∫_{a+ib}^{ib} z⁻¹ dz = i arctan(a/b) + log|ib| - log|a+ib|` for
real `a` and `b ≠ 0`. -/
theorem invint_2' (a b : ℝ) (hb : b ≠ 0) :
    segIntegral (fun z : ℂ => z⁻¹) ((a : ℂ) + (b : ℂ) * Complex.I)
        ((b : ℂ) * Complex.I) =
      (Real.arctan (a / b) : ℂ) * Complex.I +
        (Real.log ‖(b : ℂ) * Complex.I‖ : ℂ) -
        (Real.log ‖(a : ℂ) + (b : ℂ) * Complex.I‖ : ℂ) :=
  sorry

/-- **14VIII** (`invint`, cstar.tex:2302, Exercise), part 3:
`∫_w^{w'} (z - z₀)⁻¹ dz = i ∠(w, z₀, w') + log(|w' - z₀|/|w - z₀|)` when
`z₀ ∉ [w, w']`. -/
theorem invint_3 (w w' z₀ : ℂ) (hz₀ : z₀ ∉ segment ℝ w w') :
    segIntegral (fun z => (z - z₀)⁻¹) w w' =
      (measuredAngle w z₀ w' : ℂ) * Complex.I +
        (Real.log (‖w' - z₀‖ / ‖w - z₀‖) : ℂ) :=
  sorry

/-- **14VIII** (`invint`, cstar.tex:2302, Exercise), part 4:
`(2πi)⁻¹ ∫_T (z - z₀)⁻¹ dz = wn_T(z₀)` for a triangle `T` and a point `z₀`
off its boundary. -/
theorem invint_4 (w₀ w₁ w₂ z₀ : ℂ)
    (h : z₀ ∉ segment ℝ w₀ w₁ ∪ segment ℝ w₁ w₂ ∪ segment ℝ w₂ w₀) :
    triIntegral (fun z => (z - z₀)⁻¹) w₀ w₁ w₂ =
      2 * (Real.pi : ℂ) * Complex.I * (windingNumber w₀ w₁ w₂ z₀ : ℂ) :=
  sorry

/-! ## Parsec 150: Cauchy's integral formula and Taylor expansion -/

/-- **15I** (`cauchy-formula`, cstar.tex:2396, Theorem (Cauchy's Integral
Formula)): for a holomorphic 𝒜-valued function `f` defined on (an open set
containing) the closed regular `N`-gon with centre `c`, circumradius `r` and
vertices `wₙ = c + r·exp(2πin/N)`, and a point `z₀` in the interior of the
`N`-gon, `f(z₀) = (2πi)⁻¹ ∑_{n<N} ∫_{wₙ}^{wₙ₊₁} f(z)/(z - z₀) dz`. -/
theorem cauchy_formula {U : Set ℂ} (hU : IsOpen U) (f : ℂ → 𝒜)
    (hf : DifferentiableOn ℂ f U) (N : ℕ) (hN : 3 ≤ N) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (w : ℕ → ℂ)
    (hw : ∀ n, w n = c + (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * n / N))
    (hUw : convexHull ℝ (Set.range w) ⊆ U) (z₀ : ℂ)
    (hz₀ : z₀ ∈ interior (convexHull ℝ (Set.range w))) :
    f z₀ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      ∑ n ∈ Finset.range N,
        segIntegral (fun z => (z - z₀)⁻¹ • f z) (w n) (w (n + 1)) :=
  sorry

/-- **15V** (`taylor`, cstar.tex:2465, Proposition): a holomorphic 𝒜-valued
function `f` defined on the closed regular `K`-gon with vertices `w₀, …,
w_{K-1}` equals, on any open disk with centre `v` inside the `K`-gon, the
power series in `z - v` whose coefficients are the polygon integrals
`(2πi)⁻¹ ∑_k ∫_{w_k}^{w_{k+1}} f(u)/(u - v)^{n+1} du`. -/
theorem taylor {U : Set ℂ} (hU : IsOpen U) (f : ℂ → 𝒜)
    (hf : DifferentiableOn ℂ f U) (K : ℕ) (hK : 3 ≤ K) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (w : ℕ → ℂ)
    (hw : ∀ n, w n = c + (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * n / K))
    (hUw : convexHull ℝ (Set.range w) ⊆ U) (v : ℂ) (s : ℝ) (hs : 0 < s)
    (hball : Metric.ball v s ⊆ interior (convexHull ℝ (Set.range w)))
    (z : ℂ) (hz : z ∈ Metric.ball v s) :
    HasSum
      (fun n : ℕ => (z - v) ^ n •
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          ∑ k ∈ Finset.range K,
            segIntegral (fun u => ((u - v) ^ (n + 1))⁻¹ • f u) (w k) (w (k + 1))))
      (f z) :=
  sorry

/-- **15VII** (`rigid-expansion`, cstar.tex:2514, Proposition): if a
holomorphic 𝒜-valued function `f` is given by a power series
`∑ₙ aₙ (z - w)ⁿ` on some disk around `w` of radius `r > 0`, then the same
formula holds on any larger disk around `w` of radius `R > r` that still fits
inside `dom(f)`. -/
theorem rigid_expansion {U : Set ℂ} (hU : IsOpen U) (f : ℂ → 𝒜)
    (hf : DifferentiableOn ℂ f U) (a : ℕ → 𝒜) (w : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hsmall : ∀ z ∈ Metric.ball w r, HasSum (fun n : ℕ => (z - w) ^ n • a n) (f z))
    (hball : Metric.ball w R ⊆ U) (z : ℂ) (hz : z ∈ Metric.ball w R) :
    HasSum (fun n : ℕ => (z - w) ^ n • a n) (f z) :=
  by
    -- Divergence from the thesis's proof (cstar.tex:2514): the thesis derives
    -- this from **15V** `taylor` and **13VI**
    -- `powerseries_uniqueness_coeffients`, both still `sorry` here.  In Lean
    -- neither is needed: `DifferentiableOn.hasFPowerSeriesOnBall` (Cauchy's
    -- integral formula, stated in Mathlib for any complete complex normed
    -- space) supplies a power-series expansion of `f` on any closed ball
    -- inside `dom(f)`, and `HasFPowerSeriesAt.eq_formalMultilinearSeries`
    -- identifies its coefficients with `a` using `hsmall`.  The argument uses
    -- neither `hU` nor `hrR`.
    have hpow := fpsOfCoeffs_hasFPowerSeriesOnBall a f w r hr hsmall
    -- `f` is also represented by `cauchyPowerSeries f w R'` on any closed ball
    -- around `w` that lies inside `ball w R` and contains `z`
    have hzw : ‖z - w‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    obtain ⟨R', hR'1, hR'2⟩ := exists_between hzw
    have hR'0 : 0 < R' := lt_of_le_of_lt (norm_nonneg _) hR'1
    set RR : ℝ≥0 := ⟨R', hR'0.le⟩ with hRR
    have hsub : Metric.closedBall w (RR : ℝ) ⊆ U := by
      refine subset_trans ?_ hball
      intro v hv
      simp only [Metric.mem_closedBall] at hv
      simp only [Metric.mem_ball]
      exact lt_of_le_of_lt hv hR'2
    have hq : HasFPowerSeriesOnBall f (cauchyPowerSeries f w RR) w RR :=
      (hf.mono hsub).hasFPowerSeriesOnBall (by exact_mod_cast hR'0)
    -- the two power series agree, so the given one converges to `f z`
    have heq : fpsOfCoeffs a = cauchyPowerSeries f w RR :=
      hpow.hasFPowerSeriesAt.eq_formalMultilinearSeries hq.hasFPowerSeriesAt
    have hzmem : z ∈ Metric.eball w (RR : ℝ≥0∞) := by
      rw [Metric.eball_coe, Metric.mem_ball, dist_eq_norm]
      exact hR'1
    have hsum := hq.hasSum_sub hzmem
    rw [← heq] at hsum
    simpa [fpsOfCoeffs_coeff] using hsum

/-! ## Parsec 160: the spectral radius -/

/-- **16II** (`norm-spectrum`, cstar.tex:2566, Proposition): for a
self-adjoint element `a` of a C*-algebra,
`‖a‖ = sup { |λ| : λ ∈ spec(a) }`, the *spectral radius* of `a` (Mathlib:
`spectralRadius ℂ a`, valued in `ℝ≥0∞`). -/
theorem norm_spectrum (a : 𝒜) (ha : IsSelfAdjoint a) :
    spectralRadius ℂ a = (‖a‖₊ : ℝ≥0∞) :=
  ha.spectralRadius_eq_nnnorm

/-! **16IV** (cstar.tex:2625, Remark): for non-self-adjoint `a` the formula
may fail (e.g. `[[0,1],[0,0]]`); the general formula
`sup |spec(a)| = limsup ‖aⁿ‖^{1/n}` is not needed here.  Not converted. -/

/-- **16V** (`spectrum-non-empty`, cstar.tex:2646, Exercise): the spectrum of
a self-adjoint element of a C*-algebra `𝒜 ≠ {0}` is non-empty.  (Mathlib
proves this for arbitrary elements: `spectrum.nonempty`.)

The hypothesis `𝒜 ≠ {0}` — here `[Nontrivial 𝒜]` — is **erratum 160.50**;
without it the statement is false for the trivial C*-algebra, where every
element is invertible and so `spec(a) = ∅`. -/
theorem spectrum_nonempty [Nontrivial 𝒜] (a : 𝒜) (ha : IsSelfAdjoint a) :
    (spectrum ℂ a).Nonempty :=
  spectrum.nonempty a

/-- **16VI** (cstar.tex:2650, Exercise): for self-adjoint `a` and `λ ∈ ℝ`:
`spec(a) ⊆ {λ}` iff `a = λ`.

The printed statement had `spec(a) = {λ}`; **erratum 160.60** weakens it to
`spec(a) ⊆ {λ}`, which makes the exercise true for the trivial C*-algebra as
well (there `spec(a) = ∅ ⊆ {λ}` and `a = 0 = λ`), so no nontriviality split
is needed. -/
theorem spectrum_eq_singleton_iff (a : 𝒜) (ha : IsSelfAdjoint a) (lam : ℝ) :
    spectrum ℂ a ⊆ {(lam : ℂ)} ↔ a = algebraMap ℂ 𝒜 (lam : ℂ) :=
  by
    have hlam : IsSelfAdjoint (algebraMap ℂ 𝒜 (lam : ℂ)) := by
      rw [IsSelfAdjoint, ← algebraMap_star_comm, Complex.star_def,
        Complex.conj_ofReal]
    have hb : IsSelfAdjoint (a - algebraMap ℂ 𝒜 (lam : ℂ)) := ha.sub hlam
    constructor
    · intro h
      -- `spec(a - λ) = spec(a) - {λ} ⊆ {0}`, so the spectral radius of the
      -- self-adjoint element `a - λ` — its norm, by **16III** — vanishes.
      have hspec : ∀ z ∈ spectrum ℂ (a - algebraMap ℂ 𝒜 (lam : ℂ)), z = 0 := by
        intro z hz
        rw [← spectrum.sub_singleton_eq] at hz
        obtain ⟨w, hw, s, hs, rfl⟩ := hz
        rw [Set.mem_singleton_iff] at hs
        obtain rfl : s = (lam : ℂ) := hs
        obtain rfl : w = (lam : ℂ) := h hw
        simp
      have hr : spectralRadius ℂ (a - algebraMap ℂ 𝒜 (lam : ℂ)) ≤ 0 := by
        refine iSup₂_le fun z hz => ?_
        simp [hspec z hz]
      rw [hb.spectralRadius_eq_nnnorm, nonpos_iff_eq_zero, ENNReal.coe_eq_zero,
        nnnorm_eq_zero, sub_eq_zero] at hr
      exact hr
    · rintro rfl z hz
      rw [Set.mem_singleton_iff]
      by_contra hne
      refine spectrum.mem_iff.mp hz ?_
      rw [← map_sub]
      exact ((sub_ne_zero.mpr hne).isUnit).map (algebraMap ℂ 𝒜)

/-- **16VII** (cstar.tex:2658, Theorem (Gelfand–Mazur for C*-algebras)):
if every non-zero element of a C*-algebra `𝒜` is invertible, then `𝒜 = ℂ`
or `𝒜 = {0}` — here: every element of `𝒜` is a scalar.  (**16VIa**,
cstar.tex:2655, Exercise, asks to prove this from **16VI**; it is merged into
this statement.) -/
theorem gelfand_mazur (h : ∀ a : 𝒜, a ≠ 0 → IsUnit a) :
    ∀ a : 𝒜, ∃ z : ℂ, a = algebraMap ℂ 𝒜 z :=
  by
    intro a
    rcases subsingleton_or_nontrivial 𝒜 with _ | _
    · exact ⟨0, Subsingleton.elim _ _⟩
    · obtain ⟨z, hz⟩ := spectrum.nonempty a
      refine ⟨z, ?_⟩
      rw [spectrum.mem_iff] at hz
      by_contra hne
      exact hz (h _ (sub_ne_zero.mpr (Ne.symm hne)))

/-! **16VIII** (`gelfand-mazur-predicament`, cstar.tex:2663, Remark): why the
usual Banach-algebra route to Gelfand's representation theorem is avoided —
nothing to formalize. -/

/-! ## Parsec 170 (`cstar-positive-2`): positive elements, continued -/

/-- **17II** (`real-pos-ineq`, cstar.tex:2709, Exercise): `|λ - t| ≤ t` iff
`λ ∈ [0, 2t]`, for `λ, t ∈ ℝ`. -/
theorem real_pos_ineq (lam t : ℝ) : |lam - t| ≤ t ↔ lam ∈ Set.Icc 0 (2 * t) :=
  by
    rw [abs_le, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      constructor <;> linarith

/-- Auxiliary (**16II**): for a self-adjoint element `b` and `t ≥ 0`,
`‖b‖ ≤ t` iff every spectral value of `b` has modulus at most `t`. -/
private theorem norm_le_iff_spectrum_norm_le (b : 𝒜) (hb : IsSelfAdjoint b)
    (t : ℝ) (ht : 0 ≤ t) : ‖b‖ ≤ t ↔ ∀ z ∈ spectrum ℂ b, ‖z‖ ≤ t :=
  by
    constructor
    · intro h z hz
      have h1 : ((‖z‖₊ : ℝ≥0∞)) ≤ spectralRadius ℂ b :=
        le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ b) => (‖k‖₊ : ℝ≥0∞)) z hz
      rw [hb.spectralRadius_eq_nnnorm, ENNReal.coe_le_coe] at h1
      exact le_trans (by exact_mod_cast h1) h
    · intro h
      set T : NNReal := ⟨t, ht⟩ with hT
      have h1 : spectralRadius ℂ b ≤ (T : ℝ≥0∞) := by
        refine iSup₂_le fun z hz => ?_
        refine ENNReal.coe_le_coe.mpr ?_
        rw [hT]
        exact h z hz
      rw [hb.spectralRadius_eq_nnnorm, ENNReal.coe_le_coe] at h1
      exact h1

/-- Auxiliary: a real scalar is a self-adjoint element of a C*-algebra
(the version of `Basic.isSelfAdjoint_algebraMap_ofReal` that does not need an
order on `𝒜`). -/
private theorem isSelfAdjoint_algebraMap_ofReal' (r : ℝ) :
    IsSelfAdjoint (algebraMap ℂ 𝒜 (r : ℂ)) :=
  by rw [IsSelfAdjoint, ← algebraMap_star_comm, Complex.star_def, Complex.conj_ofReal]

/-- **17III** (`pos-spectrum`, cstar.tex:2714, Proposition): for self-adjoint
`a` and `t ∈ [0,∞)`: `‖a - t‖ ≤ t` iff `spec(a) ⊆ [0, 2t]`. -/
theorem pos_spectrum (a : 𝒜) (ha : IsSelfAdjoint a) (t : ℝ) (ht : 0 ≤ t) :
    ‖a - algebraMap ℂ 𝒜 (t : ℂ)‖ ≤ t ↔
      spectrum ℂ a ⊆ {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 2 * t ∧ z = r} :=
  by
    have hb : IsSelfAdjoint (a - algebraMap ℂ 𝒜 (t : ℂ)) :=
      ha.sub (isSelfAdjoint_algebraMap_ofReal' t)
    rw [norm_le_iff_spectrum_norm_le _ hb t ht]
    constructor
    · intro h z hz
      have hz' : z - (t : ℂ) ∈ spectrum ℂ (a - algebraMap ℂ 𝒜 (t : ℂ)) := by
        rw [← spectrum.sub_singleton_eq]
        exact ⟨z, hz, (t : ℂ), rfl, rfl⟩
      have hnorm := h _ hz'
      have hre : z = (z.re : ℂ) := ha.mem_spectrum_eq_re hz
      have habs : |z.re - t| ≤ t := by
        rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, ← hre]
        exact hnorm
      exact ⟨z.re, ((real_pos_ineq z.re t).mp habs).1,
        ((real_pos_ineq z.re t).mp habs).2, hre⟩
    · intro h w hw
      rw [← spectrum.sub_singleton_eq] at hw
      obtain ⟨z, hz, s, hs, rfl⟩ := hw
      obtain ⟨r, hr0, hr2, hrz⟩ := h hz
      rw [Set.mem_singleton_iff] at hs
      subst hs
      show ‖z - (t : ℂ)‖ ≤ t
      rw [hrz, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact (real_pos_ineq r t).mpr ⟨hr0, hr2⟩

/-! ### The order-free core of the 23II iteration

The iteration `b₀ = 0`, `b_{n+1} = ½(a + bₙ²)` of **23II** (parsec 230) and
its convergence estimates use nothing but the norm — no order at all.  They
are therefore stated here, at parsec 170, so that the audit of the thesis's
own notion of positivity below (`ThesisPos`) can use them; the order-dependent
part of **23II** stays at parsec 230 where it belongs. -/

section SqrtIterationCore

/-- The iteration `b₀ = 0`, `b_{n+1} = ½(a + bₙ²)` converging to
`1 - √(1-a)` (**23II**, cstar.tex:3485). -/
noncomputable def sqrtApproxSeq (a : 𝒜) : ℕ → 𝒜
  | 0 => 0
  | n + 1 => (2 : ℂ)⁻¹ • (a + sqrtApproxSeq a n ^ 2)

/-- Auxiliary for **23II**: the real iteration `r₀ = 0`, `r_{n+1} = ½(1+rₙ²)`,
i.e. the thesis's `qₙ(1)` (cstar.tex:3546). -/
private noncomputable def sqrtApproxReal : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 + sqrtApproxReal n ^ 2) / 2

private theorem sqrtApproxReal_zero : sqrtApproxReal 0 = 0 := rfl

private theorem sqrtApproxReal_succ (n : ℕ) :
    sqrtApproxReal (n + 1) = (1 + sqrtApproxReal n ^ 2) / 2 := rfl

private theorem sqrtApproxReal_nonneg (n : ℕ) : 0 ≤ sqrtApproxReal n := by
  induction n with
  | zero => rw [sqrtApproxReal_zero]
  | succ n ih => rw [sqrtApproxReal_succ]; positivity

private theorem sqrtApproxReal_le_one (n : ℕ) : sqrtApproxReal n ≤ 1 := by
  induction n with
  | zero => rw [sqrtApproxReal_zero]; norm_num
  | succ n ih =>
    have h0 := sqrtApproxReal_nonneg n
    rw [sqrtApproxReal_succ]
    nlinarith

private theorem sqrtApproxReal_mono : Monotone sqrtApproxReal := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [sqrtApproxReal_succ]
  nlinarith [sq_nonneg (1 - sqrtApproxReal n)]

private theorem norm_one_le' : ‖(1 : 𝒜)‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial 𝒜 with _ | _
  · rw [Subsingleton.elim (1 : 𝒜) 0, norm_zero]; norm_num
  · rw [norm_one]

private theorem sqrtApproxSeq_zero (a : 𝒜) : sqrtApproxSeq a 0 = 0 := rfl

private theorem sqrtApproxSeq_succ (a : 𝒜) (n : ℕ) :
    sqrtApproxSeq a (n + 1) = (2 : ℂ)⁻¹ • (a + sqrtApproxSeq a n ^ 2) := rfl

private theorem sqrtApproxSeq_commute (a c : 𝒜) (hc : c * a = a * c) (n : ℕ) :
    c * sqrtApproxSeq a n = sqrtApproxSeq a n * c := by
  induction n with
  | zero => rw [sqrtApproxSeq_zero, mul_zero, zero_mul]
  | succ n ih =>
    rw [sqrtApproxSeq_succ, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, hc,
      sq, ← mul_assoc, ih, mul_assoc, ih, ← mul_assoc]

private theorem sqrtApproxSeq_self_commute (a : 𝒜) (m n : ℕ) :
    sqrtApproxSeq a m * sqrtApproxSeq a n = sqrtApproxSeq a n * sqrtApproxSeq a m :=
  sqrtApproxSeq_commute a _ (sqrtApproxSeq_commute a a rfl m).symm n

private theorem sqrtApproxSeq_norm_le (a : 𝒜) (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖sqrtApproxSeq a n‖ ≤ sqrtApproxReal n := by
  induction n with
  | zero => rw [sqrtApproxSeq_zero, sqrtApproxReal_zero, norm_zero]
  | succ n ih =>
    have hb0 : (0 : ℝ) ≤ ‖sqrtApproxSeq a n‖ := norm_nonneg _
    have hsq : ‖sqrtApproxSeq a n ^ 2‖ ≤ ‖sqrtApproxSeq a n‖ ^ 2 := by
      rw [sq, sq]; exact norm_mul_le _ _
    have hadd : ‖a + sqrtApproxSeq a n ^ 2‖ ≤ 1 + sqrtApproxReal n ^ 2 := by
      refine le_trans (norm_add_le _ _) ?_
      have := sqrtApproxReal_nonneg n
      nlinarith
    rw [sqrtApproxSeq_succ, norm_smul, sqrtApproxReal_succ]
    have hc : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by norm_num
    rw [hc]
    linarith

private theorem sqrtApproxSeq_dist (a : 𝒜) (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n‖
      ≤ sqrtApproxReal (n + 1) - sqrtApproxReal n := by
  induction n with
  | zero =>
    rw [sqrtApproxSeq_zero, sqrtApproxSeq_succ, sqrtApproxSeq_zero,
      sqrtApproxReal_zero, sqrtApproxReal_succ, sqrtApproxReal_zero]
    have hc : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by norm_num
    rw [sub_zero, sub_zero, norm_smul, hc]
    have hz : ((0 : 𝒜) ^ 2) = 0 := by norm_num
    have hz' : ((0 : ℝ) ^ 2) = 0 := by norm_num
    rw [hz, add_zero, hz']
    linarith
  | succ n ih =>
    have key : sqrtApproxSeq a (n + 2) - sqrtApproxSeq a (n + 1)
        = (2 : ℂ)⁻¹ • (sqrtApproxSeq a (n + 1) *
            (sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n)
          + (sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n) * sqrtApproxSeq a n) := by
      rw [sqrtApproxSeq_succ a (n + 1), sqrtApproxSeq_succ a n, ← smul_sub]
      congr 1
      noncomm_ring
    have hd0 : (0 : ℝ) ≤ sqrtApproxReal (n + 1) - sqrtApproxReal n :=
      sub_nonneg.mpr (sqrtApproxReal_mono (Nat.le_succ n))
    have hn1 := sqrtApproxSeq_norm_le a ha (n + 1)
    have hn0 := sqrtApproxSeq_norm_le a ha n
    have hr0 := sqrtApproxReal_nonneg n
    have hr1 := sqrtApproxReal_nonneg (n + 1)
    have hbound : ‖sqrtApproxSeq a (n + 1) *
          (sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n)
        + (sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n) * sqrtApproxSeq a n‖
        ≤ (sqrtApproxReal (n + 1) + sqrtApproxReal n) *
            (sqrtApproxReal (n + 1) - sqrtApproxReal n) := by
      refine le_trans (norm_add_le _ _) ?_
      have h1 := norm_mul_le (sqrtApproxSeq a (n + 1))
        (sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n)
      have h2 := norm_mul_le (sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n)
        (sqrtApproxSeq a n)
      have hd := ih
      have hdn : (0 : ℝ) ≤ ‖sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n‖ :=
        norm_nonneg _
      nlinarith [norm_nonneg (sqrtApproxSeq a (n + 1)), norm_nonneg (sqrtApproxSeq a n)]
    have hc : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by norm_num
    have hr2 : sqrtApproxReal (n + 2) = (1 + sqrtApproxReal (n + 1) ^ 2) / 2 :=
      sqrtApproxReal_succ (n + 1)
    have hr1' : sqrtApproxReal (n + 1) = (1 + sqrtApproxReal n ^ 2) / 2 :=
      sqrtApproxReal_succ n
    have hkey2 : (sqrtApproxReal (n + 1) + sqrtApproxReal n) *
        (sqrtApproxReal (n + 1) - sqrtApproxReal n)
        = 2 * (sqrtApproxReal (n + 2) - sqrtApproxReal (n + 1)) := by
      rw [hr2, hr1']; ring
    rw [key, norm_smul, hc]
    linarith

private theorem sqrtApproxSeq_cauchy (a : 𝒜) (ha : ‖a‖ ≤ 1) :
    CauchySeq (sqrtApproxSeq a) := by
  refine cauchySeq_of_summable_dist ?_
  have hsum : Summable fun n => sqrtApproxReal (n + 1) - sqrtApproxReal n := by
    refine summable_of_sum_range_le (c := 1)
      (fun n => sub_nonneg.mpr (sqrtApproxReal_mono (Nat.le_succ n))) fun n => ?_
    rw [Finset.sum_range_sub sqrtApproxReal, sqrtApproxReal_zero, sub_zero]
    exact sqrtApproxReal_le_one n
  refine Summable.of_nonneg_of_le (fun n => dist_nonneg) (fun n => ?_) hsum
  rw [dist_eq_norm, norm_sub_rev]
  exact sqrtApproxSeq_dist a ha n

end SqrtIterationCore

/-! ### The thesis's own notion of positivity: a bootstrapping audit

In Lean, `0 ≤ a` is Mathlib's *star order*: `a` is a finite sum of elements of
the form `star s * s`.  The thesis instead **defines** `a` to be positive when
`a` is self-adjoint and `‖a - t‖ ≤ t` for some `t ∈ ℝ` (**9IV**,
`cstar-positive-def`, cstar.tex:1130); that the two notions agree is thesis
**25I** (`cstar-positive-final`, cstar.tex:3750), sixteen parsecs further on,
and one of the deepest results of the chapter.  Encoding "positive" as `0 ≤`
therefore silently imports **25I** — and with it **19III**+**24IV**, which
`star_mul_self_nonneg` makes true by definition — into every parsec below 250.

`ThesisPos` below is the thesis's notion, and this block proves `ThesisPos ↔
(0 ≤ ·)` (`thesisPos_iff_nonneg`) from the thesis's own development, in the
thesis's own order:

* parsec 110 (`spectrum_self_adjoint_real_2`/`_3`) and parsec 170
  (`pos_spectrum`, **17III**) for the spectral characterisation and the cone
  laws;
* the order-free core of the 23II iteration above for the square root
  (**23II**, parsec 230);
* the thesis's `astara-non-negative` argument (**19III**, parsec 190) and its
  `astara-positive` argument (**24IV**, parsec 240) for `ThesisPos (a* a)`.

Mathlib's `StarOrderedRing.nonneg_iff_spectrum_nonneg` (its CFC-backed form of
**25I**) is *never* used here.  `star_mul_self_nonneg` and
`StarOrderedRing.nonneg_iff` are used only in the final bridge, and only to
unfold Mathlib's *definition* of `0 ≤`; no thesis content is taken from them.

Once `thesisPos_iff_nonneg` is available, every `0 ≤` in this file is
certified to be the thesis's notion of positivity, and the parsec-170
statements below can be proved without appealing to **25I**. -/

section ThesisPositive

/-- The thesis's *definition* of a positive element (**9IV**,
`cstar-positive-def`, cstar.tex:1130): a self-adjoint `a` with `‖a - t‖ ≤ t`
for some `t ∈ ℝ`. -/
private def ThesisPos (a : 𝒜) : Prop :=
  IsSelfAdjoint a ∧ ∃ t : ℝ, ‖a - algebraMap ℂ 𝒜 (t : ℂ)‖ ≤ t

/-- Auxiliary for **17V**.3 → 2: if the spectrum of a self-adjoint `a` lies in
`[0,∞)`, then `‖a - t‖ ≤ t` already at `t = ‖a‖`. -/
private theorem thesisPos_norm_of_spectrum {a : 𝒜} (ha : IsSelfAdjoint a)
    (h : spectrum ℂ a ⊆ {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = r}) :
    ‖a - algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ)‖ ≤ ‖a‖ := by
  refine (pos_spectrum a ha ‖a‖ (norm_nonneg a)).mpr fun z hz => ?_
  obtain ⟨r, hr0, hrz⟩ := h hz
  refine ⟨r, hr0, ?_, hrz⟩
  have hzn : ‖z‖ ≤ ‖a‖ :=
    (norm_le_iff_spectrum_norm_le a ha ‖a‖ (norm_nonneg a)).mp le_rfl z hz
  rw [hrz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at hzn
  linarith

/-- **17V**.1 ↔ 3 for the thesis's notion of positivity, by the thesis's own
route: `pos_spectrum` (**17III**) in both directions. -/
private theorem thesisPos_iff_spectrum {a : 𝒜} (ha : IsSelfAdjoint a) :
    ThesisPos a ↔ spectrum ℂ a ⊆ {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = r} := by
  constructor
  · rintro ⟨-, t, ht⟩
    have ht0 : 0 ≤ t := le_trans (norm_nonneg _) ht
    intro z hz
    obtain ⟨r, hr0, -, hrz⟩ := (pos_spectrum a ha t ht0).mp ht hz
    exact ⟨r, hr0, hrz⟩
  · exact fun h => ⟨ha, ‖a‖, thesisPos_norm_of_spectrum ha h⟩

private theorem ThesisPos.spectrum_subset {a : 𝒜} (h : ThesisPos a) :
    spectrum ℂ a ⊆ {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = r} :=
  (thesisPos_iff_spectrum h.1).mp h

/-- **17V**.1 → 2 in the form used below. -/
private theorem ThesisPos.norm_le {a : 𝒜} (h : ThesisPos a) :
    ‖a - algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ)‖ ≤ ‖a‖ :=
  thesisPos_norm_of_spectrum h.1 h.spectrum_subset

/-! #### The cone laws (**17VI**), for `ThesisPos` -/

private theorem thesisPos_algebraMap {r : ℝ} (hr : 0 ≤ r) :
    ThesisPos (algebraMap ℂ 𝒜 (r : ℂ)) :=
  ⟨isSelfAdjoint_algebraMap_ofReal' r, r, by simpa using hr⟩

private theorem thesisPos_zero : ThesisPos (0 : 𝒜) := by
  have h := thesisPos_algebraMap (𝒜 := 𝒜) (r := 0) le_rfl
  simpa using h

private theorem thesisPos_one : ThesisPos (1 : 𝒜) := by
  have h := thesisPos_algebraMap (𝒜 := 𝒜) (r := 1) zero_le_one
  simpa using h

private theorem thesisPos_add {a b : 𝒜} (ha : ThesisPos a) (hb : ThesisPos b) :
    ThesisPos (a + b) := by
  obtain ⟨hsa, s, hs⟩ := ha
  obtain ⟨hsb, t, ht⟩ := hb
  refine ⟨hsa.add hsb, s + t, ?_⟩
  have hc : (((s + t : ℝ)) : ℂ) = (s : ℂ) + (t : ℂ) := by push_cast; ring
  have he : a + b - algebraMap ℂ 𝒜 (((s + t : ℝ)) : ℂ)
      = (a - algebraMap ℂ 𝒜 (s : ℂ)) + (b - algebraMap ℂ 𝒜 (t : ℂ)) := by
    rw [hc, map_add]
    abel
  rw [he]
  exact le_trans (norm_add_le _ _) (add_le_add hs ht)

private theorem thesisPos_ofReal_smul {r : ℝ} (hr : 0 ≤ r) {a : 𝒜} (ha : ThesisPos a) :
    ThesisPos (((r : ℝ) : ℂ) • a) := by
  obtain ⟨hsa, t, ht⟩ := ha
  have hrsa : IsSelfAdjoint ((r : ℝ) : ℂ) := by
    rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal]
  refine ⟨hrsa.smul hsa, r * t, ?_⟩
  have he : ((r : ℝ) : ℂ) • a - algebraMap ℂ 𝒜 (((r * t : ℝ)) : ℂ)
      = ((r : ℝ) : ℂ) • (a - algebraMap ℂ 𝒜 (t : ℂ)) := by
    rw [smul_sub, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul]
    push_cast
    ring_nf
  rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left ht hr

/-- **17VI**.1 for `ThesisPos`: the thesis's positive cone is proper. -/
private theorem thesisPos_antisymm {a : 𝒜} (h : ThesisPos a) (h' : ThesisPos (-a)) :
    a = 0 := by
  have hz : ‖a‖ ≤ 0 := by
    refine (norm_le_iff_spectrum_norm_le a h.1 0 le_rfl).mpr fun z hz => ?_
    obtain ⟨r, hr0, hrz⟩ := h.spectrum_subset hz
    have hmem : -z ∈ spectrum ℂ (-a) := by
      rw [← spectrum.neg_eq]
      exact Set.neg_mem_neg.mpr hz
    obtain ⟨s, hs0, hsz⟩ := h'.spectrum_subset hmem
    have hrs : -(r : ℝ) = s := by
      have : (-(r : ℝ) : ℂ) = ((s : ℝ) : ℂ) := by rw [← hrz, ← hsz]
      exact_mod_cast this
    have hr : r = 0 := by linarith
    rw [hrz, hr]
    simp
  simpa using norm_le_zero_iff.mp hz

/-- **17VI**.2 for `ThesisPos`: the thesis's positive cone is closed
(the thesis's own argument, asols.tex:1727). -/
private theorem isClosed_thesisPos : IsClosed {a : 𝒜 | ThesisPos a} := by
  have hset : {a : 𝒜 | ThesisPos a}
      = {a : 𝒜 | star a = a} ∩
        {a : 𝒜 | ‖a - algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ)‖ ≤ ‖a‖} := by
    ext a
    exact ⟨fun h => ⟨h.1, h.norm_le⟩, fun h => ⟨h.1, ‖a‖, h.2⟩⟩
  rw [hset]
  refine IsClosed.inter (isClosed_eq continuous_star continuous_id) (isClosed_le ?_ ?_)
  · exact (continuous_id.sub ((continuous_algebraMap ℂ 𝒜).comp
      (Complex.continuous_ofReal.comp continuous_norm))).norm
  · exact continuous_norm

/-! #### The norm–order correspondence (**17VI**.3a) for `ThesisPos` -/

private theorem thesisPos_sub_of_norm_le {a : 𝒜} (ha : IsSelfAdjoint a) {t : ℝ}
    (h : ‖a‖ ≤ t) : ThesisPos (algebraMap ℂ 𝒜 (t : ℂ) - a) :=
  ⟨(isSelfAdjoint_algebraMap_ofReal' t).sub ha, t, by simpa using h⟩

private theorem thesisPos_add_of_norm_le {a : 𝒜} (ha : IsSelfAdjoint a) {t : ℝ}
    (h : ‖a‖ ≤ t) : ThesisPos (algebraMap ℂ 𝒜 (t : ℂ) + a) :=
  ⟨(isSelfAdjoint_algebraMap_ofReal' t).add ha, t, by simpa using h⟩

private theorem norm_le_of_thesisPos_pair {a : 𝒜} (ha : IsSelfAdjoint a) {t : ℝ}
    (ht : 0 ≤ t) (h1 : ThesisPos (algebraMap ℂ 𝒜 (t : ℂ) - a))
    (h2 : ThesisPos (algebraMap ℂ 𝒜 (t : ℂ) + a)) : ‖a‖ ≤ t := by
  refine (norm_le_iff_spectrum_norm_le a ha t ht).mpr fun z hz => ?_
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, z = (x : ℂ) := ⟨z.re, ha.mem_spectrum_eq_re hz⟩
  have hm1 : (t : ℂ) - (x : ℂ) ∈ spectrum ℂ (algebraMap ℂ 𝒜 (t : ℂ) - a) := by
    rw [← spectrum.singleton_sub_eq]
    exact ⟨(t : ℂ), rfl, (x : ℂ), hz, rfl⟩
  have hm2 : (t : ℂ) + (x : ℂ) ∈ spectrum ℂ (algebraMap ℂ 𝒜 (t : ℂ) + a) := by
    rw [← spectrum.singleton_add_eq]
    exact ⟨(t : ℂ), rfl, (x : ℂ), hz, rfl⟩
  obtain ⟨r1, hr1, he1⟩ := h1.spectrum_subset hm1
  obtain ⟨r2, hr2, he2⟩ := h2.spectrum_subset hm2
  have hv1 : t - x = r1 := by exact_mod_cast he1
  have hv2 : t + x = r2 := by exact_mod_cast he2
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-! #### Squares and odd powers (**11XV**.2–3, parsec 110) -/

/-- **17VI**.4a for `ThesisPos`, by the thesis's own route: **11XV**.2. -/
private theorem thesisPos_sq {a : 𝒜} (ha : IsSelfAdjoint a) : ThesisPos (a ^ 2) := by
  refine (thesisPos_iff_spectrum (ha.pow 2)).mpr fun z hz => ?_
  by_contra hcon
  simp only [Set.mem_setOf_eq] at hcon
  push_neg at hcon
  have hu := spectrum_self_adjoint_real_2 a ha 2 even_two z hcon
  rw [spectrum.mem_iff] at hz
  exact hz (by simpa using hu.neg)

/-- **17VI**.4c for `ThesisPos`, by the thesis's own route: **11XV**.3. -/
private theorem thesisPos_of_pow_odd {a : 𝒜} (ha : IsSelfAdjoint a) {n : ℕ}
    (hn : Odd n) (h : ThesisPos (a ^ n)) : ThesisPos a := by
  refine (thesisPos_iff_spectrum ha).mpr fun z hz => ?_
  by_contra hcon
  simp only [Set.mem_setOf_eq] at hcon
  push_neg at hcon
  have hpow : ∀ w : ℂ, (∀ r : ℝ, 0 ≤ r → w ≠ r) → IsUnit (a ^ n - algebraMap ℂ 𝒜 w) := by
    intro w hw
    have hns : w ∉ spectrum ℂ (a ^ n) := fun hmem => by
      obtain ⟨r, hr0, hrw⟩ := h.spectrum_subset hmem
      exact hw r hr0 hrw
    rw [spectrum.notMem_iff] at hns
    simpa using hns.neg
  have hu := (spectrum_self_adjoint_real_3 a ha n hn).mp hpow z hcon
  rw [spectrum.mem_iff] at hz
  exact hz (by simpa using hu.neg)

/-! #### The square root (**23II**/**23VII**, parsec 230) for `ThesisPos`

The iteration of **23II** is run here against the thesis's own notion of
positivity.  Only the *existence* half is needed, and only its order-free
estimates (above) are used; the order-theoretic `ineq-square-root` clause of
**23II** is not needed at all for what follows. -/

private theorem isSelfAdjoint_star_mul_self' (a : 𝒜) : IsSelfAdjoint (star a * a) := by
  rw [IsSelfAdjoint, star_mul, star_star]

/-- `‖y‖ ≤ t` for a thesis-positive `y` below `t` (**17VI**.3a/3c). -/
private theorem norm_le_of_thesisPos_sub {y : 𝒜} (hy : ThesisPos y) {t : ℝ} (ht : 0 ≤ t)
    (h : ThesisPos (algebraMap ℂ 𝒜 (t : ℂ) - y)) : ‖y‖ ≤ t :=
  norm_le_of_thesisPos_pair hy.1 ht h (thesisPos_add (thesisPos_algebraMap ht) hy)

/-- The existence half of **23II** for `ThesisPos`: for thesis-positive `a`
with `‖a‖ ≤ 1` the iteration `b₀ = 0`, `b_{n+1} = ½(a + bₙ²)` converges to a
thesis-positive `b` with `‖b‖ ≤ 1` and `(1-b)² = 1-a`, commuting with
everything that commutes with `a`. -/
private theorem thesisSqrt_iteration {a : 𝒜} (hp : ThesisPos a) (hn : ‖a‖ ≤ 1) :
    ∃ b : 𝒜, ThesisPos b ∧ ‖b‖ ≤ 1 ∧ (1 - b) ^ 2 = 1 - a ∧
      ∀ c : 𝒜, c * a = a * c → c * b = b * c := by
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete (sqrtApproxSeq_cauchy a hn)
  have hhalf : ((2 : ℂ))⁻¹ = (((1 / 2 : ℝ)) : ℂ) := by norm_num
  have hpn : ∀ n, ThesisPos (sqrtApproxSeq a n) := by
    intro n
    induction n with
    | zero => rw [sqrtApproxSeq_zero]; exact thesisPos_zero
    | succ n ih =>
      rw [sqrtApproxSeq_succ, hhalf]
      exact thesisPos_ofReal_smul (by norm_num) (thesisPos_add hp (thesisPos_sq ih.1))
  refine ⟨b, isClosed_thesisPos.mem_of_tendsto hb (Filter.Eventually.of_forall hpn), ?_, ?_, ?_⟩
  · have hlim : Tendsto (fun n => ‖sqrtApproxSeq a n‖) atTop (𝓝 ‖b‖) := hb.norm
    refine le_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
    exact le_trans (sqrtApproxSeq_norm_le a hn n) (sqrtApproxReal_le_one n)
  · have hrec : b = (2 : ℂ)⁻¹ • (a + b ^ 2) := by
      have hl : Tendsto (fun n => sqrtApproxSeq a (n + 1)) atTop (𝓝 b) :=
        hb.comp (Filter.tendsto_add_atTop_nat 1)
      have hr : Tendsto (fun n => sqrtApproxSeq a (n + 1)) atTop
          (𝓝 ((2 : ℂ)⁻¹ • (a + b ^ 2))) := by
        simp only [sqrtApproxSeq_succ]
        exact ((hb.pow 2).const_add a).const_smul _
      exact tendsto_nhds_unique hl hr
    have h2 : a + b ^ 2 = b + b := by
      have h3 : (2 : ℂ) • ((2 : ℂ)⁻¹ • (a + b ^ 2)) = (2 : ℂ) • b := by rw [← hrec]
      have he : (2 : ℂ) * (2 : ℂ)⁻¹ = 1 := by norm_num
      rw [smul_smul, he, one_smul, two_smul] at h3
      exact h3
    have hsq : (1 - b) ^ 2 = 1 - (b + b) + b ^ 2 := by noncomm_ring
    rw [hsq, ← h2]
    abel
  · intro c hc
    have hl : Tendsto (fun n => c * sqrtApproxSeq a n) atTop (𝓝 (c * b)) := hb.const_mul c
    have hr : Tendsto (fun n => sqrtApproxSeq a n * c) atTop (𝓝 (b * c)) := hb.mul_const c
    refine tendsto_nhds_unique hl ?_
    simpa only [sqrtApproxSeq_commute a c hc] using hr

/-- **23VII** for `ThesisPos`: every thesis-positive element has a
thesis-positive square root, commuting with everything that commutes with it.
(Uniqueness is not needed below and is not claimed here.) -/
private theorem thesisSqrt_exists {x : 𝒜} (hx : ThesisPos x) :
    ∃ m : 𝒜, ThesisPos m ∧ m ^ 2 = x ∧ ∀ c : 𝒜, c * x = x * c → c * m = m * c := by
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | h0
  · have hx0 : x = 0 := norm_eq_zero.mp h0.symm
    exact ⟨0, thesisPos_zero, by simp [hx0], by simp⟩
  · have hs0 : (0 : ℝ) < ‖x‖ := h0
    set s : ℝ := ‖x‖ with hs
    have hy : ThesisPos (((s⁻¹ : ℝ) : ℂ) • x) :=
      thesisPos_ofReal_smul (le_of_lt (inv_pos.mpr hs0)) hx
    set y : 𝒜 := ((s⁻¹ : ℝ) : ℂ) • x with hydef
    have hyn : ‖y‖ = 1 := by
      rw [hydef, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (inv_pos.mpr hs0)), ← hs, inv_mul_cancel₀ (ne_of_gt hs0)]
    have hone : algebraMap ℂ 𝒜 (((1 : ℝ)) : ℂ) = 1 := by norm_num
    have hay : ThesisPos (1 - y) := by
      have := thesisPos_sub_of_norm_le hy.1 (t := 1) (le_of_eq hyn)
      rwa [hone] at this
    have han : ‖1 - y‖ ≤ 1 := by
      refine norm_le_of_thesisPos_sub hay zero_le_one ?_
      rw [hone]
      simpa using hy
    obtain ⟨b, hb, hbn, hb2, hbc⟩ := thesisSqrt_iteration hay han
    have hm0 : ThesisPos (1 - b) := by
      have := thesisPos_sub_of_norm_le hb.1 hbn
      rwa [hone] at this
    have hm0sq : (1 - b) ^ 2 = y := by rw [hb2]; abel
    refine ⟨((Real.sqrt s : ℝ) : ℂ) • (1 - b),
      thesisPos_ofReal_smul (Real.sqrt_nonneg s) hm0, ?_, ?_⟩
    · have hsmulsq : ∀ (r : ℂ) (z : 𝒜), (r • z) ^ 2 = (r * r) • z ^ 2 := by
        intro r z; rw [sq, sq, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [hsmulsq, hm0sq, hydef, smul_smul]
      have hcc : ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt s : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ) = 1 := by
        have : Real.sqrt s * Real.sqrt s * s⁻¹ = 1 := by
          rw [Real.mul_self_sqrt (le_of_lt hs0), mul_inv_cancel₀ (ne_of_gt hs0)]
        exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) this
      rw [hcc, one_smul]
    · intro c hc
      have hcy : c * y = y * c := by
        rw [hydef, mul_smul_comm, smul_mul_assoc, hc]
      have hca : c * (1 - y) = (1 - y) * c := by
        rw [mul_sub, sub_mul, mul_one, one_mul, hcy]
      have hcb := hbc c hca
      rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul, hcb]

/-- The thesis's `square-commuting-monotone` (cstar.tex:3573) for `ThesisPos`:
the product of two commuting thesis-positive elements is thesis-positive,
because each is a square whose root commutes with the other. -/
private theorem thesisPos_mul_of_commute {x y : 𝒜} (hx : ThesisPos x) (hy : ThesisPos y)
    (hxy : x * y = y * x) : ThesisPos (x * y) := by
  obtain ⟨d, hd, hdsq, hdc⟩ := thesisSqrt_exists hx
  obtain ⟨e, he, hesq, hec⟩ := thesisSqrt_exists hy
  have hdy : d * y = y * d := (hdc y hxy.symm).symm
  have hde : d * e = e * d := hec d hdy
  have hsa : IsSelfAdjoint (d * e) := by
    rw [IsSelfAdjoint, star_mul, hd.1.star_eq, he.1.star_eq, ← hde]
  have hprod : x * y = (d * e) ^ 2 := by
    rw [← hdsq, ← hesq, sq, sq, sq]
    calc d * d * (e * e) = d * (d * e) * e := by noncomm_ring
      _ = d * (e * d) * e := by rw [hde]
      _ = d * e * (d * e) := by noncomm_ring
  rw [hprod]
  exact thesisPos_sq hsa

/-- **17VI**.4d for `ThesisPos`: powers of a thesis-positive element are
thesis-positive. -/
private theorem thesisPos_pow {a : 𝒜} (ha : ThesisPos a) : ∀ n : ℕ, ThesisPos (a ^ n)
  | 0 => by simpa using thesisPos_one
  | (n + 1) => by
      rw [pow_succ]
      exact thesisPos_mul_of_commute (thesisPos_pow ha n) ha (by rw [← pow_succ, pow_succ'])

/-! #### **19III** and **24IV** for `ThesisPos` -/

/-- Auxiliary: `x + x = y + y` implies `x = y` (the algebra is a `ℂ`-vector
space).  Used to divide the thesis's identities by two. -/
private theorem eq_of_add_self_eq {x y : 𝒜} (hxy : x + x = y + y) : x = y := by
  have h2 : ((2 : ℂ))⁻¹ • ((2 : ℂ) • x) = ((2 : ℂ))⁻¹ • ((2 : ℂ) • y) := by
    rw [two_smul, two_smul, hxy]
  rwa [smul_smul, smul_smul, show ((2 : ℂ))⁻¹ * 2 = 1 by norm_num, one_smul, one_smul] at h2

/-- **19III** (`astara-non-negative`, cstar.tex:2838, Lemma) for the thesis's
notion of positivity, transcribing the thesis's argument at parsec 190:
`a*a ≤ 0` implies `a = 0`.  Note that the Lean statement `astara_non_negative`
below is *not* this: with Mathlib's star order `0 ≤ star a * a` holds by
definition, so that statement is a triviality, whereas this one is not. -/
private theorem thesisPos_astara_non_negative {b : 𝒜} (h : ThesisPos (-(star b * b))) :
    b = 0 := by
  have hsa2 : IsSelfAdjoint (b * star b) := by
    simpa using isSelfAdjoint_star_mul_self' (star b)

  -- `spec(b*b) ⊆ (-∞,0]` gives `spec(bb*) ⊆ (-∞,0]` by `prod_spec` (**19Ia**,
  -- stated below at parsec 190; Mathlib's form of it is cited here because
  -- this block is placed early in the file for technical reasons only).
  have h2 : ThesisPos (-(b * star b)) := by
    refine (thesisPos_iff_spectrum hsa2.neg).mpr fun z hz => ?_
    have hz' : -z ∈ spectrum ℂ (b * star b) := by
      have hzz : z ∈ -spectrum ℂ (b * star b) := by rw [spectrum.neg_eq]; exact hz
      exact Set.mem_neg.mp hzz
    by_cases hz0 : (-z) = 0
    · exact ⟨0, le_rfl, by simpa using neg_eq_zero.mp hz0⟩
    · have hd : -z ∈ spectrum ℂ (b * star b) \ {0} :=
        Set.mem_sdiff_of_mem hz' (by simpa using hz0)
      rw [spectrum.nonzero_mul_comm b (star b)] at hd
      have hmem : -z ∈ spectrum ℂ (star b * b) := Set.mem_of_mem_sdiff hd
      refine h.spectrum_subset ?_
      rw [← spectrum.neg_eq]
      exact Set.mem_neg.mpr (by simpa using hmem)
  -- on the other hand `b*b + bb* = ½((b+b*)² + (i(b-b*))²) ≥ 0`
  have hsum : ThesisPos (star b * b + b * star b) := by
    have hp : IsSelfAdjoint (b + star b) := by
      rw [IsSelfAdjoint, star_add, star_star]; abel
    have hq : IsSelfAdjoint (Complex.I • (b - star b)) := by
      rw [IsSelfAdjoint, star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I,
        neg_smul, smul_sub, smul_sub, neg_sub]
    have hexp : (b + star b) ^ 2 + (Complex.I • (b - star b)) ^ 2
        = (star b * b + b * star b) + (star b * b + b * star b) := by
      have h1 : (Complex.I • (b - star b)) ^ 2
          = (Complex.I * Complex.I) • (b - star b) ^ 2 := by
        rw [sq, sq, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [h1, Complex.I_mul_I, neg_one_smul]
      noncomm_ring
    have hps : ThesisPos ((star b * b + b * star b) + (star b * b + b * star b)) := by
      rw [← hexp]
      exact thesisPos_add (thesisPos_sq hp) (thesisPos_sq hq)
    -- and a self-adjoint `x` with `x + x` positive is positive
    have hhalf := thesisPos_ofReal_smul (𝒜 := 𝒜) (r := 1 / 2) (by norm_num) hps
    have hcalc : (((1 / 2 : ℝ)) : ℂ) •
        ((star b * b + b * star b) + (star b * b + b * star b))
        = star b * b + b * star b := by
      rw [← two_smul ℂ, smul_smul]
      norm_num
    rwa [hcalc] at hhalf
  have hzero : star b * b + b * star b = 0 := by
    refine thesisPos_antisymm hsum ?_
    have hrw : (-(star b * b)) + (-(b * star b)) = -(star b * b + b * star b) := by abel
    rw [← hrw]
    exact thesisPos_add h h2
  have hstar : star b * b = 0 := by
    refine thesisPos_antisymm ?_ h
    have he : star b * b = -(b * star b) := by
      have hx : star b * b = -(b * star b) + 0 := by rw [← hzero]; abel
      simpa using hx
    rw [he]
    exact h2
  have hnb : ‖b‖ * ‖b‖ = 0 := by
    rw [← CStarRing.norm_star_mul_self, hstar, norm_zero]
  have hn0 : ‖b‖ = 0 := by nlinarith [norm_nonneg b]
  exact norm_eq_zero.mp hn0

/-- **24IV** (`astara-positive`, cstar.tex:3725, Lemma) for the thesis's
notion of positivity, transcribing the thesis's argument: `a*a` is positive.

The thesis takes `b := a ((a*a)_-)^{1/2}`; here the negative part is reached
directly as `u := |h| - h` (with `h := a*a` and `|h|` the square root of `h²`
from **23VII**), and `b := a u` already does the job, `u` being positive
because `u³ = 2|h|u²` is a product of commuting positives (**11XV**.3). -/
private theorem thesisPos_star_mul_self (a : 𝒜) : ThesisPos (star a * a) := by
  set h : 𝒜 := star a * a with hdef
  have hsa : IsSelfAdjoint h := isSelfAdjoint_star_mul_self' a
  -- `m := |h|`, a thesis-positive square root of `h²`, commuting with `h`
  obtain ⟨m, hm, hm2, hmc⟩ := thesisSqrt_exists (thesisPos_sq hsa)
  have hmh : h * m = m * h := hmc h (by noncomm_ring)
  set u : 𝒜 := m - h with hu
  have husa : IsSelfAdjoint u := hm.1.sub hsa
  have hhu : h * u = u * h := by rw [hu, mul_sub, sub_mul, hmh]
  -- the thesis's `h h₋ = -(h₋)²`, in the form `2 h u = -u²`
  have hkey : h * u + h * u = -(u ^ 2) := by
    have hexp : u ^ 2 = m ^ 2 - m * h - h * m + h ^ 2 := by rw [hu]; noncomm_ring
    rw [hm2, ← hmh] at hexp
    rw [hexp, hu]
    noncomm_ring
  -- `u² = 2 m u = 2 u m`, whence `m` and `u` commute
  have hmsum : m = u + h := by rw [hu]; abel
  have h1 : m * u + m * u = u ^ 2 := by
    have hmu' : m * u = u * u + h * u := by rw [hmsum]; noncomm_ring
    rw [hmu']
    have hre : u * u + h * u + (u * u + h * u) = u * u + u * u + (h * u + h * u) := by abel
    rw [hre, hkey, sq]
    abel
  have h2 : u * m + u * m = u ^ 2 := by
    have hmu' : u * m = u * u + u * h := by rw [hmsum]; noncomm_ring
    rw [hmu', ← hhu]
    have hre : u * u + h * u + (u * u + h * u) = u * u + u * u + (h * u + h * u) := by abel
    rw [hre, hkey, sq]
    abel
  have hmu : m * u = u * m := eq_of_add_self_eq (by rw [h1, h2])
  -- `u ≥ 0`, because `u³ = 2 m u²` is a product of commuting positives
  have hu3 : ThesisPos (u ^ 3) := by
    have hcube : u ^ 3 = m * u ^ 2 + m * u ^ 2 := by
      have he : u ^ 3 = (m * u + m * u) * u := by rw [h1]; exact pow_succ u 2
      rw [he, sq]
      noncomm_ring
    have hmc2 : m * u ^ 2 = u ^ 2 * m := by
      rw [sq, ← mul_assoc, hmu, mul_assoc, hmu, mul_assoc]
    have hpos : ThesisPos (m * u ^ 2) :=
      thesisPos_mul_of_commute hm (thesisPos_sq husa) hmc2
    rw [hcube]
    exact thesisPos_add hpos hpos
  have hup : ThesisPos u := thesisPos_of_pow_odd husa (by decide) hu3
  -- the thesis's `b := a (h₋)^{1/2}`; here `b := a u` already works
  have hbb : star (a * u) * (a * u) = h * u ^ 2 := by
    have hb1 : star (a * u) * (a * u) = u * h * u := by
      rw [star_mul, husa.star_eq, hdef]; noncomm_ring
    rw [hb1, ← hhu, mul_assoc, ← sq]
  have hbneg : ThesisPos (-(star (a * u) * (a * u))) := by
    have hsum2 : (-(star (a * u) * (a * u))) + (-(star (a * u) * (a * u))) = u ^ 3 := by
      rw [hbb, ← neg_add]
      have hfac : h * u ^ 2 + h * u ^ 2 = (h * u + h * u) * u := by
        rw [sq]; noncomm_ring
      rw [hfac, hkey]
      noncomm_ring
    have hhalf := thesisPos_ofReal_smul (𝒜 := 𝒜) (r := 1 / 2) (by norm_num) (hsum2 ▸ hu3)
    have hcalc : (((1 / 2 : ℝ)) : ℂ) •
        ((-(star (a * u) * (a * u))) + (-(star (a * u) * (a * u))))
        = -(star (a * u) * (a * u)) := by
      rw [← two_smul ℂ, smul_smul]
      norm_num
    rwa [hcalc] at hhalf
  have hb0 : a * u = 0 := thesisPos_astara_non_negative hbneg
  have hzero2 : h * u ^ 2 = 0 := by rw [← hbb, hb0]; simp
  have hu3z : u ^ 3 = 0 := by
    have hfac : h * u ^ 2 + h * u ^ 2 = -(u ^ 3) := by
      have he : h * u ^ 2 + h * u ^ 2 = (h * u + h * u) * u := by rw [sq]; noncomm_ring
      rw [he, hkey, neg_mul, ← pow_succ]
    have hz : -(u ^ 3) = 0 := by rw [← hfac, hzero2, add_zero]
    exact neg_eq_zero.mp hz
  have hu0 : u = 0 := by
    have hn2 : ‖u ^ 2‖ = ‖u‖ ^ 2 := by
      rw [sq, sq, ← CStarRing.norm_star_mul_self, husa.star_eq]
    have hs2 : IsSelfAdjoint (u ^ 2) := husa.pow 2
    have hn4 : ‖u ^ 4‖ = ‖u ^ 2‖ ^ 2 := by
      rw [show u ^ 4 = u ^ 2 * u ^ 2 by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add],
        sq (‖u ^ 2‖), ← CStarRing.norm_star_mul_self, hs2.star_eq]
    have hu4 : u ^ 4 = 0 := by rw [pow_succ, hu3z, zero_mul]
    rw [hu4, norm_zero, hn2] at hn4
    have hq : ‖u‖ ^ 2 = 0 := by nlinarith [sq_nonneg (‖u‖ ^ 2)]
    have hn0 : ‖u‖ = 0 := by nlinarith [norm_nonneg u]
    exact norm_eq_zero.mp hn0
  have hmeq : m = h := sub_eq_zero.mp (by rw [← hu]; exact hu0)
  rw [← hmeq]
  exact hm

/-! #### **25I**: the thesis's notion of positivity is Mathlib's `0 ≤` -/

section Bridge

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **25I**, cheap half: a thesis-positive element is nonnegative in Mathlib's
star order.  This is a matter of unfolding Mathlib's *definition* of `0 ≤`:
a thesis-positive `a` is a square `m²` by **23VII**, hence `star m * m`, hence
`0 ≤ a` by `star_mul_self_nonneg`, which carries no thesis content.  It rests
on the square root (parsec 230) and nothing later. -/
private theorem ThesisPos.nonneg {a : 𝒜} (h : ThesisPos a) : 0 ≤ a := by
  obtain ⟨m, hm, hm2, -⟩ := thesisSqrt_exists h
  have hms : star m * m = m ^ 2 := by rw [hm.1.star_eq, sq]
  rw [← hm2, ← hms]
  exact star_mul_self_nonneg m

/-- **25I**, expensive half: an element nonnegative in Mathlib's star order is
thesis-positive.  This is the real statement: an element of the star-positive
cone is a sum of elements `star s * s`, and each of those is thesis-positive by
**24IV** above — the theorem proved from the thesis's own parsec-190 and
parsec-230 development.  `StarOrderedRing.nonneg_iff` used here is again only
the *definition* of Mathlib's order. -/
private theorem thesisPos_of_nonneg {a : 𝒜} (h : 0 ≤ a) : ThesisPos a := by
  rw [StarOrderedRing.nonneg_iff] at h
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact thesisPos_star_mul_self s
  | zero => exact thesisPos_zero
  | add x y _ _ hx hy => exact thesisPos_add hx hy

/-- **25I** (`cstar-positive-final`, cstar.tex:3750, Exercise), the part that
the encoding of positivity as `0 ≤` presupposes: the thesis's notion of
positivity and Mathlib's star order agree.  Proofs below cite the two halves
separately wherever only one is needed, so that the dependency on **24IV**
stays visible. -/
private theorem thesisPos_iff_nonneg (a : 𝒜) : ThesisPos a ↔ 0 ≤ a :=
  ⟨ThesisPos.nonneg, thesisPos_of_nonneg⟩

end Bridge

end ThesisPositive

section Order

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- Auxiliary (**17V**.3): a self-adjoint element is positive iff its complex
spectrum consists of nonnegative reals. -/
private theorem nonneg_iff_spectrum_ofReal_nonneg (a : 𝒜) (ha : IsSelfAdjoint a) :
    0 ≤ a ↔ spectrum ℂ a ⊆ {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = r} :=
  by
    -- The thesis proves this at parsec 170, from `pos-spectrum` (**17III**)
    -- alone; what the Lean encoding adds is the identification of `0 ≤ a` with
    -- the thesis's notion of positivity, which is **25I** and is supplied by
    -- `thesisPos_iff_nonneg` above (proved from the thesis's own development,
    -- not from Mathlib's `StarOrderedRing.nonneg_iff_spectrum_nonneg`).
    rw [← thesisPos_iff_nonneg, thesisPos_iff_spectrum ha]

/-- **17V** (`cstar-positive-1`, cstar.tex:2732, Exercise): for a
self-adjoint element `a` of a C*-algebra the following are equivalent:
(1) `‖a - t‖ ≤ t` for some `t ≥ ‖a‖/2`; (2) `‖a - t‖ ≤ t` for all
`t ≥ ‖a‖/2`; (3) `spec(a) ⊆ [0,∞)`; (4) `a` is positive. -/
theorem cstar_positive_tfae (a : 𝒜) (ha : IsSelfAdjoint a) :
    List.TFAE [
      ∃ t : ℝ, ‖a‖ / 2 ≤ t ∧ ‖a - algebraMap ℂ 𝒜 (t : ℂ)‖ ≤ t,
      ∀ t : ℝ, ‖a‖ / 2 ≤ t → ‖a - algebraMap ℂ 𝒜 (t : ℂ)‖ ≤ t,
      spectrum ℂ a ⊆ {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = r},
      0 ≤ a] :=
  by
    have hhalf : (0 : ℝ) ≤ ‖a‖ / 2 := by positivity
    tfae_have 1 → 3 := by
      rintro ⟨t, hts, ht⟩
      have ht0 : 0 ≤ t := le_trans hhalf hts
      intro z hz
      obtain ⟨r, hr0, _, hrz⟩ := (pos_spectrum a ha t ht0).mp ht hz
      exact ⟨r, hr0, hrz⟩
    -- The thesis proves 1 ⟹ 3 ⟹ 2 ⟹ 1 from `pos-spectrum` (**17III**) and
    -- `spectrum-basic` alone; only the bridge 3 ↔ 4 to Mathlib's star order
    -- `0 ≤ a` needs more (see the note on **25I** in the report).
    tfae_have 3 → 2 := by
      intro h t hts
      have ht0 : 0 ≤ t := le_trans hhalf hts
      refine (pos_spectrum a ha t ht0).mpr ?_
      intro z hz
      obtain ⟨r, hr0, hrz⟩ := h hz
      refine ⟨r, hr0, ?_, hrz⟩
      have hzn : ‖z‖ ≤ ‖a‖ :=
        (norm_le_iff_spectrum_norm_le a ha ‖a‖ (norm_nonneg a)).mp le_rfl z hz
      rw [hrz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at hzn
      linarith
    tfae_have 2 → 1 := fun h => ⟨‖a‖ / 2, le_rfl, h _ le_rfl⟩
    tfae_have 3 ↔ 4 := (nonneg_iff_spectrum_ofReal_nonneg a ha).symm
    tfae_finish

/-- **17VI** (`positive-basic-2`, cstar.tex:2756, Exercise), part 1:
`0 ≤ a ≤ 0` entails `a = 0`. -/
theorem positive_basic_2_1 (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 0) : a = 0 :=
  le_antisymm h1 h0

/-- **17VI** (`positive-basic-2`, cstar.tex:2756, Exercise), part 2: the set
`𝒜₊` of positive elements is closed. -/
theorem positive_basic_2_2 : IsClosed {a : 𝒜 | 0 ≤ a} :=
  by
    have hset : {a : 𝒜 | 0 ≤ a} = {a : 𝒜 | ThesisPos a} := by
      ext a; exact (thesisPos_iff_nonneg a).symm
    rw [hset]
    exact isClosed_thesisPos

/-- **17VI** (`positive-basic-2`, cstar.tex:2756, Exercise), part 3a: for
self-adjoint `a` and `λ ∈ [0,∞)`: `-λ ≤ a ≤ λ` iff `‖a‖ ≤ λ`. -/
theorem positive_basic_2_3a (a : 𝒜) (ha : IsSelfAdjoint a) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    (-(algebraMap ℂ 𝒜 (lam : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (lam : ℂ)) ↔
      ‖a‖ ≤ lam :=
  by
    -- the thesis's own argument (asols.tex:1745), through the spectrum
    constructor
    · rintro ⟨h1, h2⟩
      refine norm_le_of_thesisPos_pair ha hlam
        (thesisPos_of_nonneg (sub_nonneg.mpr h2)) ?_
      have h3 : (0 : 𝒜) ≤ algebraMap ℂ 𝒜 (lam : ℂ) + a := by
        have h4 := sub_nonneg.mpr h1
        rwa [sub_neg_eq_add, add_comm] at h4
      exact thesisPos_of_nonneg h3
    · intro h
      refine ⟨?_, ?_⟩
      · have h1 := (thesisPos_add_of_norm_le ha h).nonneg
        rw [← sub_neg_eq_add, sub_nonneg] at h1
        exact neg_le.mp h1
      · have h2 := (thesisPos_sub_of_norm_le ha h).nonneg
        rwa [sub_nonneg] at h2

/-- **17VI** (`positive-basic-2`, cstar.tex:2756, Exercise), part 3b:
`‖a‖ = inf { λ ≥ 0 : -λ ≤ a ≤ λ }` for self-adjoint `a` (so `sa(𝒜)` is a
complete Archimedean order unit space).

The infimum runs over `λ ≥ 0`, not over all `λ ∈ ℝ`: that is **erratum
170.60**.  With the range restricted, the set is `[‖a‖, ∞)` in *every*
C*-algebra, the trivial one included, so — unlike the printed form — this
needs no `Subsingleton`/`Nontrivial` case split. -/
theorem positive_basic_2_3b (a : 𝒜) (ha : IsSelfAdjoint a) :
    ‖a‖ = sInf {lam : ℝ | 0 ≤ lam ∧
      -(algebraMap ℂ 𝒜 (lam : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (lam : ℂ)} :=
  by
    have hset : {lam : ℝ | 0 ≤ lam ∧
        -(algebraMap ℂ 𝒜 (lam : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (lam : ℂ)}
          = Set.Ici ‖a‖ := by
      ext lam
      simp only [Set.mem_setOf_eq, Set.mem_Ici]
      constructor
      · rintro ⟨h0, h1, h2⟩
        exact (positive_basic_2_3a a ha lam h0).mp ⟨h1, h2⟩
      · intro h
        refine ⟨le_trans (norm_nonneg a) h, ?_⟩
        exact (positive_basic_2_3a a ha ‖a‖ (norm_nonneg a)).mpr le_rfl |>.imp
          (fun hx => le_trans (neg_le_neg (algebraMap_ofReal_mono h)) hx)
          (fun hx => le_trans hx (algebraMap_ofReal_mono h))
    rw [hset, csInf_Ici]


/-- **17VI** (`positive-basic-2`, cstar.tex:2756, Exercise), part 3c:
`0 ≤ a ≤ b` entails `‖a‖ ≤ ‖b‖`. -/
theorem positive_basic_2_3c (a b : 𝒜) (h0 : 0 ≤ a) (hab : a ≤ b) :
    ‖a‖ ≤ ‖b‖ :=
  by
    -- the thesis's argument: `-‖b‖ ≤ 0 ≤ a ≤ b ≤ ‖b‖`, then **17VI**.3a
    have hb : (0 : 𝒜) ≤ b := le_trans h0 hab
    have hbsa : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg hb
    have hasa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg h0
    refine norm_le_of_thesisPos_pair hasa (norm_nonneg b) ?_ ?_
    · have h1 : ThesisPos (algebraMap ℂ 𝒜 ((‖b‖ : ℝ) : ℂ) - b) :=
        thesisPos_sub_of_norm_le hbsa le_rfl
      have h2 : ThesisPos (b - a) := thesisPos_of_nonneg (sub_nonneg.mpr hab)
      have h3 := thesisPos_add h1 h2
      have he : algebraMap ℂ 𝒜 ((‖b‖ : ℝ) : ℂ) - b + (b - a)
          = algebraMap ℂ 𝒜 ((‖b‖ : ℝ) : ℂ) - a := by abel
      rwa [he] at h3
    · exact thesisPos_add (thesisPos_algebraMap (norm_nonneg b))
        (thesisPos_of_nonneg h0)

/-- **17VI** (`positive-basic-2`, cstar.tex:2756, Exercise), part 4a: `a²`
is positive for self-adjoint `a`. -/
theorem positive_basic_2_4a (a : 𝒜) (ha : IsSelfAdjoint a) : 0 ≤ a ^ 2 :=
  by
    -- the thesis's route (**11XV**.2): `spec(a²) ⊆ [0,∞)`, not the Lean
    -- triviality `a² = star a * a`
    exact (thesisPos_sq ha).nonneg

/-- **17VI** (`positive-basic-2`, cstar.tex:2756, Exercise), part 4b: `aⁿ`
is positive for self-adjoint `a` and even `n`. -/
theorem positive_basic_2_4b (a : 𝒜) (ha : IsSelfAdjoint a) (n : ℕ)
    (hn : Even n) : 0 ≤ a ^ n :=
  by
    obtain ⟨m, rfl⟩ := hn
    have h : a ^ (m + m) = (a ^ m) ^ 2 := by rw [← pow_mul, Nat.mul_two]
    rw [h]
    exact (thesisPos_sq (ha.pow m)).nonneg

/-- **17VI** (`positive-basic-2`, cstar.tex:2756, Exercise), part 4c: for
self-adjoint `a` and odd `n`: `aⁿ` is positive iff `a` is positive. -/
theorem positive_basic_2_4c (a : 𝒜) (ha : IsSelfAdjoint a) (n : ℕ)
    (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  by
    -- the thesis's route (**11XV**.3) in both directions
    constructor
    · intro h
      exact (thesisPos_of_pow_odd ha hn (thesisPos_of_nonneg h)).nonneg
    · intro h
      exact (thesisPos_pow (thesisPos_of_nonneg h) n).nonneg

/-- **17VI** (`positive-basic-2`, cstar.tex:2756, Exercise), part 4d: `aⁿ` is
positive for positive `a` and every `n`. -/
theorem positive_basic_2_4d (a : 𝒜) (ha : 0 ≤ a) (n : ℕ) : 0 ≤ a ^ n :=
  (thesisPos_pow (thesisPos_of_nonneg ha) n).nonneg

/-- **17VI** (`positive-basic-2`, cstar.tex:2756, Exercise), part 5: for
invertible `a`: `a ≥ 0` iff `a⁻¹ ≥ 0`. -/
theorem positive_basic_2_5 (a : 𝒜) (ha : IsUnit a) :
    0 ≤ a ↔ 0 ≤ Ring.inverse a :=
  by
    -- the thesis's route (asols.tex:1834): `spec(a⁻¹) = spec(a)⁻¹`, via
    -- **17V**.3; `CFC.inv_nonneg` would import the functional calculus
    obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit]
    have hkey : ∀ v : 𝒜ˣ, (0 : 𝒜) ≤ (v : 𝒜) → (0 : 𝒜) ≤ ((v⁻¹ : 𝒜ˣ) : 𝒜) := by
      intro v hv
      have hvsa : IsSelfAdjoint ((v : 𝒜)) := IsSelfAdjoint.of_nonneg hv
      have hvu : star v = v := Units.ext (by rw [Units.coe_star, hvsa.star_eq])
      have hisa : IsSelfAdjoint (((v⁻¹ : 𝒜ˣ) : 𝒜)) := by
        show star (((v⁻¹ : 𝒜ˣ)) : 𝒜) = _
        rw [← Units.coe_star_inv, hvu]
      refine (nonneg_iff_spectrum_ofReal_nonneg _ hisa).mpr fun z hz => ?_
      rw [← spectrum.map_inv v] at hz
      obtain ⟨r, hr0, hrz⟩ :=
        (nonneg_iff_spectrum_ofReal_nonneg _ hvsa).mp hv (Set.mem_inv.mp hz)
      refine ⟨r⁻¹, inv_nonneg.mpr hr0, ?_⟩
      rw [Complex.ofReal_inv, ← hrz, inv_inv]
    constructor
    · exact hkey u
    · intro h
      have h2 := hkey u⁻¹ h
      rwa [inv_inv] at h2

/-- **17VI** (`positive-basic-2`, cstar.tex:2756, Exercise), part 6: a
positive element `a` is invertible iff `a ≥ 1/n` for some `n > 0`. -/
theorem positive_basic_2_6 (a : 𝒜) (ha : 0 ≤ a) :
    IsUnit a ↔ ∃ n : ℕ, 0 < n ∧ algebraMap ℂ 𝒜 ((n : ℂ)⁻¹) ≤ a :=
  by
    -- The author's route (asols.tex:1834): `1/n ≤ a` iff `spec(a) ⊆ [1/n, ∞)`,
    -- and `a` is invertible iff `0 ∉ spec(a)`; the spectrum is closed, so a
    -- spectrum inside `[0,∞)` avoiding `0` avoids a whole disc around `0`.
    -- This uses only **17V**.3 ↔ 4 and the closedness of the spectrum, not
    -- the operator-monotonicity of `(·)⁻¹`, which is **25II**.3.
    have hcast : ∀ n : ℕ, ((n : ℂ))⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by
      intro n; push_cast; ring
    have hsub : ∀ n : ℕ, IsSelfAdjoint (a - algebraMap ℂ 𝒜 (((n : ℝ)⁻¹ : ℝ) : ℂ)) :=
      fun n => (IsSelfAdjoint.of_nonneg ha).sub (isSelfAdjoint_algebraMap_ofReal' _)
    constructor
    · intro hu
      have h0 : (0 : ℂ) ∉ spectrum ℂ a := (spectrum.zero_notMem_iff ℂ).mpr hu
      obtain ⟨ε, hε, hball⟩ :=
        Metric.isOpen_iff.mp (spectrum.isClosed (𝕜 := ℂ) a).isOpen_compl 0 h0
      obtain ⟨n, hn⟩ := exists_nat_gt ε⁻¹
      have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
      have hn0 : 0 < n := by exact_mod_cast hnpos
      have hεn : (n : ℝ)⁻¹ < ε := by
        rw [inv_eq_one_div, div_lt_iff₀ hnpos]
        nlinarith [mul_lt_mul_of_pos_left hn hε, inv_mul_cancel₀ (ne_of_gt hε)]
      refine ⟨n, hn0, ?_⟩
      rw [hcast n, ← sub_nonneg]
      refine (nonneg_iff_spectrum_ofReal_nonneg _ (hsub n)).mpr ?_
      intro z hz
      rw [← spectrum.sub_singleton_eq] at hz
      obtain ⟨w, hw, s, hs, rfl⟩ := hz
      rw [Set.mem_singleton_iff] at hs
      subst hs
      obtain ⟨r, hr0, hrw⟩ :=
        (nonneg_iff_spectrum_ofReal_nonneg a (IsSelfAdjoint.of_nonneg ha)).mp ha hw
      have hwn : ε ≤ ‖w‖ := by
        by_contra hlt
        push_neg at hlt
        exact hball (by simpa [Metric.mem_ball, dist_eq_norm] using hlt) hw
      rw [hrw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at hwn
      refine ⟨r - (n : ℝ)⁻¹, by linarith, ?_⟩
      rw [hrw]
      push_cast
      ring
    · rintro ⟨n, hn, hle⟩
      rw [hcast n] at hle
      have hnpos : (0 : ℝ) < (n : ℝ)⁻¹ := by
        have h : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      by_contra hnu
      have h0 : (0 : ℂ) ∈ spectrum ℂ a := (spectrum.zero_mem_iff ℂ).mpr hnu
      have hmem : (0 : ℂ) - (((n : ℝ)⁻¹ : ℝ) : ℂ)
          ∈ spectrum ℂ (a - algebraMap ℂ 𝒜 (((n : ℝ)⁻¹ : ℝ) : ℂ)) := by
        rw [← spectrum.sub_singleton_eq]
        exact ⟨0, h0, _, rfl, rfl⟩
      obtain ⟨r, hr0, hrz⟩ := (nonneg_iff_spectrum_ofReal_nonneg _ (hsub n)).mp
        (sub_nonneg.mpr hle) hmem
      have hreal : (0 : ℝ) - (n : ℝ)⁻¹ = r := by
        have he : (((0 : ℝ) - (n : ℝ)⁻¹ : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
          push_cast
          push_cast at hrz
          exact hrz
        exact Complex.ofReal_inj.mp he
      linarith

end Order

/-! ## Parsec 190: `a*a` cannot be negative

**18I** (cstar.tex:2808): moved to `cstar-product-2` (20aI below) — nothing to
formalize.  **19I** (cstar.tex:2812): introduction — nothing to formalize. -/

/-- **19Ia** (`prod-spec`, cstar.tex:2819, Lemma): for elements `a`, `b` of a
C*-algebra, `spec(ab) \ {0} = spec(ba) \ {0}`. -/
theorem prod_spec (a b : 𝒜) :
    spectrum ℂ (a * b) \ {0} = spectrum ℂ (b * a) \ {0} :=
  spectrum.nonzero_mul_comm a b

/-- **19III** (`astara-non-negative`, cstar.tex:2838, Lemma):
`a* a ≤ 0` implies `a = 0`. -/
theorem astara_non_negative [PartialOrder 𝒜] [StarOrderedRing 𝒜] (a : 𝒜)
    (h : star a * a ≤ 0) : a = 0 :=
  by
    have h0 := star_mul_self_nonneg a
    have heq : star a * a = 0 := le_antisymm h h0
    have hn : ‖a‖ * ‖a‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, heq, norm_zero]
    have hz : ‖a‖ = 0 := by nlinarith [norm_nonneg a]
    exact norm_eq_zero.mp hz

end Holomorphic

/-! ## Parsec 200: positive maps are bounded; bipositive maps -/

section Maps

variable {𝒜 ℬ : Type*} [CStarAlgebra 𝒜] [CStarAlgebra ℬ]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **20II** (`weak-russo-dye`, cstar.tex:2869, Lemma), part 1: a positive
map `f : 𝒜 → ℬ` between C*-algebras satisfies `‖f(a)‖ ≤ ‖f(1)‖ ‖a‖` for
self-adjoint `a`. -/
theorem weak_russo_dye_1 (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) (a : 𝒜)
    (ha : IsSelfAdjoint a) : ‖f a‖ ≤ ‖f 1‖ * ‖a‖ :=
  by
    have hfsa : IsSelfAdjoint (f a) := by
      -- `a = (‖a‖ + a) - ‖a‖` with both terms positive (**17VI**.3a); the
      -- positive/negative parts are only available at parsec 240
      have hp1 : (0 : 𝒜) ≤ algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ) + a :=
        (thesisPos_add_of_norm_le ha le_rfl).nonneg
      have hp0 : (0 : 𝒜) ≤ algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ) :=
        (thesisPos_algebraMap (norm_nonneg a)).nonneg
      have he : f a = f (algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ) + a)
          - f (algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ)) := by
        rw [map_add]; abel
      rw [he]
      exact (IsSelfAdjoint.of_nonneg (hf _ hp1)).sub (IsSelfAdjoint.of_nonneg (hf _ hp0))
    have hmono : ∀ x y : 𝒜, x ≤ y → f x ≤ f y := by
      intro x y h
      have h2 := hf _ (sub_nonneg.mpr h)
      rw [map_sub, sub_nonneg] at h2
      exact h2
    have hM : (0:ℝ) ≤ ‖f 1‖ * ‖a‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hup : a ≤ algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ) := by
      rw [← algebraMap_real_eq]; exact ha.le_algebraMap_norm_self
    have hlow : -(algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ)) ≤ a := by
      rw [← algebraMap_real_eq]; exact ha.neg_algebraMap_norm_le_self
    have hfalg : f (algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ)) = ((‖a‖ : ℝ) : ℂ) • f 1 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul]
    have hf1 : f 1 ≤ algebraMap ℂ ℬ ((‖f 1‖ : ℝ) : ℂ) := by
      rw [← algebraMap_real_eq]
      exact (IsSelfAdjoint.of_nonneg (hf 1 zero_le_one)).le_algebraMap_norm_self
    have hkey : ((‖a‖ : ℝ) : ℂ) • f 1 ≤ algebraMap ℂ ℬ (((‖f 1‖ * ‖a‖ : ℝ)) : ℂ) := by
      have h3 : (0 : ℬ) ≤ ((‖a‖ : ℝ) : ℂ) • (algebraMap ℂ ℬ ((‖f 1‖ : ℝ) : ℂ) - f 1) :=
        ofReal_smul_nonneg (sub_nonneg.mpr hf1) (norm_nonneg a)
      rw [smul_sub, sub_nonneg] at h3
      refine h3.trans (le_of_eq ?_)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul,
        ← Complex.ofReal_mul, mul_comm]
    rw [norm_le_iff_neg_algebraMap_le hfsa hM]
    constructor
    · have h4 := hmono _ _ hlow
      rw [map_neg, hfalg] at h4
      exact (neg_le_neg hkey).trans h4
    · have h5 := hmono _ _ hup
      rw [hfalg] at h5
      exact h5.trans hkey

/-- **20II** (`weak-russo-dye`, cstar.tex:2869, Lemma), part 2: a positive
map `f : 𝒜 → ℬ` is bounded, with `‖f(a)‖ ≤ 2 ‖f(1)‖ ‖a‖` for all `a`. -/
theorem weak_russo_dye_2 (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) (a : 𝒜) :
    ‖f a‖ ≤ 2 * ‖f 1‖ * ‖a‖ :=
  by
    have hdec : a = (ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜) :=
      (realPart_add_I_smul_imaginaryPart a).symm
    have h1 := weak_russo_dye_1 f hf (ℜ a : 𝒜) (ℜ a).property
    have h2 := weak_russo_dye_1 f hf (ℑ a : 𝒜) (ℑ a).property
    obtain ⟨hre, him⟩ := cstar_involution_basic_12 a
    have hfa : f a = f (ℜ a : 𝒜) + Complex.I • f (ℑ a : 𝒜) := by
      conv_lhs => rw [hdec]
      rw [map_add, map_smul]
    rw [hfa]
    have hsm : ‖Complex.I • f (ℑ a : 𝒜)‖ = ‖f (ℑ a : 𝒜)‖ := by
      rw [norm_smul]; simp
    calc ‖f (ℜ a : 𝒜) + Complex.I • f (ℑ a : 𝒜)‖
        ≤ ‖f (ℜ a : 𝒜)‖ + ‖Complex.I • f (ℑ a : 𝒜)‖ := norm_add_le _ _
      _ = ‖f (ℜ a : 𝒜)‖ + ‖f (ℑ a : 𝒜)‖ := by rw [hsm]
      _ ≤ ‖f 1‖ * ‖a‖ + ‖f 1‖ * ‖a‖ := by
          exact add_le_add (h1.trans (by nlinarith [norm_nonneg (f 1)]))
            (h2.trans (by nlinarith [norm_nonneg (f 1)]))
      _ = 2 * ‖f 1‖ * ‖a‖ := by ring

/-! **20IV** (`russo-dye-remark`, cstar.tex:2892, Remark): the factor 2 can
be dropped — proved for cp-maps at 34XVI (`cp_russo_dye`) and for positive
maps at 34aVIII (`russo_dye_cor`); not converted separately. -/

/-- **20V** (`norm-mi-map`, cstar.tex:2904, Lemma), part 1: every miu-map
between C*-algebras is positive. -/
theorem norm_mi_map_positive (ρ : 𝒜 →⋆ₐ[ℂ] ℬ) (a : 𝒜) (ha : 0 ≤ a) :
    0 ≤ ρ a :=
  by
    -- The thesis's argument (cstar.tex:2910) is spectral: `spec(ρ a) ⊆ spec a`
    -- because `ρ` carries invertibles to invertibles.  The square root, which
    -- would give `ρ a = ρ(√a)* ρ(√a)`, is only available at **23VII**, three
    -- parsecs later.
    have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
    have hρsa : IsSelfAdjoint (ρ a) := by
      rw [IsSelfAdjoint, ← map_star, hsa.star_eq]
    refine (nonneg_iff_spectrum_ofReal_nonneg _ hρsa).mpr fun z hz =>
      (nonneg_iff_spectrum_ofReal_nonneg a hsa).mp ha ?_
    exact AlgHom.spectrum_apply_subset (ρ : 𝒜 →ₐ[ℂ] ℬ) a hz

/-- **20V** (`norm-mi-map`, cstar.tex:2904, Lemma), part 2: every miu-map
between C*-algebras is bounded with `‖ρ‖ ≤ 1`, i.e. `‖ρ(a)‖ ≤ ‖a‖`. -/
theorem norm_mi_map_contractive (ρ : 𝒜 →⋆ₐ[ℂ] ℬ) (a : 𝒜) : ‖ρ a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le ρ a

/-! Auxiliary facts about pu-maps, shared by **20VI** and **21VII**. -/

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- A unital linear map fixes the scalars. -/
private theorem map_algebraMap_of_unital (f : 𝒜 →ₗ[ℂ] ℬ) (hu : f 1 = 1) (z : ℂ) :
    f (algebraMap ℂ 𝒜 z) = algebraMap ℂ ℬ z := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, hu]

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- The key equivalence behind **20VI**.3 ⇒ .1: for self-adjoint `a` whose norm
is at most `2λ`, positivity of `a` is the *norm* condition `‖λ - a‖ ≤ λ`.  This
is `positive-basic-2`.3a applied to `λ - a`; the hypothesis `‖a‖ ≤ 2λ` is what
the thesis supplies through weak Russo–Dye. -/
private theorem nonneg_iff_norm_algebraMap_sub_le (a : 𝒜) (ha : IsSelfAdjoint a)
    (lam : ℝ) (hlam : 0 ≤ lam) (h2 : ‖a‖ ≤ 2 * lam) :
    ‖algebraMap ℂ 𝒜 (lam : ℂ) - a‖ ≤ lam ↔ 0 ≤ a := by
  have hsa : IsSelfAdjoint (algebraMap ℂ 𝒜 (lam : ℂ) - a) :=
    (isSelfAdjoint_algebraMap_ofReal lam).sub ha
  rw [← positive_basic_2_3a _ hsa lam hlam]
  constructor
  · rintro ⟨-, h⟩
    have h' := sub_le_sub_left h (algebraMap ℂ 𝒜 (lam : ℂ))
    simpa using h'
  · intro h
    refine ⟨?_, by simpa using h⟩
    have h2' := ((positive_basic_2_3a a ha (2 * lam) (by linarith)).mpr h2).2
    have hcast : algebraMap ℂ 𝒜 ((2 * lam : ℝ) : ℂ)
        = algebraMap ℂ 𝒜 (lam : ℂ) + algebraMap ℂ 𝒜 (lam : ℂ) := by
      rw [show ((2 * lam : ℝ) : ℂ) = (lam : ℂ) + (lam : ℂ) by push_cast; ring, map_add]
    rw [hcast] at h2'
    have h3 := sub_le_sub_left h2' (algebraMap ℂ 𝒜 (lam : ℂ))
    simpa using h3

/-- A positive linear map is monotone. -/
private theorem map_mono_of_pos (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) {x y : 𝒜}
    (h : x ≤ y) : f x ≤ f y := by
  have h' := hf _ (sub_nonneg.mpr h)
  rw [map_sub] at h'
  exact sub_nonneg.mp h'

/-- A positive linear map preserves self-adjointness (**10IV**). -/
private theorem isSelfAdjoint_map_of_pos (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f)
    {a : 𝒜} (ha : IsSelfAdjoint a) : IsSelfAdjoint (f a) := by
  rw [IsSelfAdjoint, ← cstar_p_implies_i f hf a, ha.star_eq]

/-- Weak Russo–Dye (**20II**.2) for a *unital* positive map: `‖f a‖ ≤ 2‖a‖`. -/
private theorem norm_map_le_two_mul (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f)
    (hu : f 1 = 1) (a : 𝒜) : ‖f a‖ ≤ 2 * ‖a‖ := by
  have h := weak_russo_dye_2 f hf a
  rw [hu] at h
  nlinarith [norm_nonneg a, norm_nonneg (1 : ℬ), norm_one_le' (𝒜 := ℬ)]

/-- A pu-map is contractive on self-adjoint elements: `-‖a‖ ≤ a ≤ ‖a‖` is
carried to `-‖a‖ ≤ f a ≤ ‖a‖`. -/
private theorem norm_map_le_of_isSelfAdjoint (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f)
    (hu : f 1 = 1) (a : 𝒜) (ha : IsSelfAdjoint a) : ‖f a‖ ≤ ‖a‖ := by
  obtain ⟨hl, hr⟩ := (positive_basic_2_3a a ha ‖a‖ (norm_nonneg a)).mpr le_rfl
  refine (positive_basic_2_3a (f a) (isSelfAdjoint_map_of_pos f hf ha) ‖a‖
    (norm_nonneg a)).mp ⟨?_, ?_⟩
  · have h := map_mono_of_pos f hf hl
    rwa [map_neg, map_algebraMap_of_unital f hu] at h
  · have h := map_mono_of_pos f hf hr
    rwa [map_algebraMap_of_unital f hu] at h

/-- **20VI** (`cstar-isometry`, cstar.tex:2934, Lemma): for a pu-map
`f : 𝒜 → ℬ` the following are equivalent: (1) `f` is *bipositive*
(`f(a) ≥ 0` iff `a ≥ 0`); (2) `f` is an isometry on `sa(𝒜)`; (3) `f` is an
isometry on `𝒜₊`.

(**20X**, cstar.tex:2994, Warning: such `f` need not preserve the norm of
arbitrary elements; not converted.) -/
theorem cstar_isometry (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f)
    (hu : f 1 = 1) :
    List.TFAE [
      ∀ a : 𝒜, 0 ≤ f a ↔ 0 ≤ a,
      ∀ a : 𝒜, IsSelfAdjoint a → ‖f a‖ = ‖a‖,
      ∀ a : 𝒜, 0 ≤ a → ‖f a‖ = ‖a‖] := by
  -- the thesis's argument (cstar.tex:2950), verbatim
  tfae_have 2 → 3 := fun h a ha => h a (IsSelfAdjoint.of_nonneg ha)
  tfae_have 1 → 2 := by
    -- `-λ ≤ a ≤ λ` iff `-λ ≤ f a ≤ λ`, because `f` is bipositive and unital
    intro h1 a ha
    have hfa : IsSelfAdjoint (f a) := isSelfAdjoint_map_of_pos f hf ha
    refine le_antisymm ?_ ?_
    · obtain ⟨hl, hr⟩ := (positive_basic_2_3a a ha ‖a‖ (norm_nonneg a)).mpr le_rfl
      refine (positive_basic_2_3a (f a) hfa ‖a‖ (norm_nonneg a)).mp ⟨?_, ?_⟩
      · have h := map_mono_of_pos f hf hl
        rwa [map_neg, map_algebraMap_of_unital f hu] at h
      · have h := map_mono_of_pos f hf hr
        rwa [map_algebraMap_of_unital f hu] at h
    · obtain ⟨hl, hr⟩ :=
        (positive_basic_2_3a (f a) hfa ‖f a‖ (norm_nonneg _)).mpr le_rfl
      refine (positive_basic_2_3a a ha ‖f a‖ (norm_nonneg _)).mp ⟨?_, ?_⟩
      · refine neg_le_iff_add_nonneg.mpr ((h1 _).mp ?_)
        rw [map_add, map_algebraMap_of_unital f hu]
        exact neg_le_iff_add_nonneg.mp hl
      · refine sub_nonneg.mp ((h1 _).mp ?_)
        rw [map_sub, map_algebraMap_of_unital f hu]
        exact sub_nonneg.mpr hr
  tfae_have 3 → 1 := by
    intro h3
    -- for self-adjoint `a`: `‖ ‖a‖ - a ‖ = ‖ ‖a‖ - f a ‖`, and each side is
    -- `≤ ‖a‖` exactly when the corresponding element is positive
    have hsacase : ∀ a : 𝒜, IsSelfAdjoint a → (0 ≤ f a ↔ 0 ≤ a) := by
      intro a ha
      have hfa : IsSelfAdjoint (f a) := isSelfAdjoint_map_of_pos f hf ha
      have hb : (0 : 𝒜) ≤ algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ) - a :=
        sub_nonneg.mpr ((positive_basic_2_3a a ha ‖a‖ (norm_nonneg a)).mpr le_rfl).2
      have heq := h3 _ hb
      rw [map_sub, map_algebraMap_of_unital f hu] at heq
      rw [← nonneg_iff_norm_algebraMap_sub_le a ha ‖a‖ (norm_nonneg a)
          (by linarith [norm_nonneg a]),
        ← nonneg_iff_norm_algebraMap_sub_le (f a) hfa ‖a‖ (norm_nonneg a)
          (norm_map_le_two_mul f hf hu a), heq]
    -- the general case reduces to it: `f` is injective on self-adjoints, so
    -- `f a` self-adjoint forces `a` self-adjoint
    intro a
    refine ⟨fun hfa => ?_, hf a⟩
    have hfasa : IsSelfAdjoint (f a) := IsSelfAdjoint.of_nonneg hfa
    have hd : f (Complex.I • (star a - a)) = 0 := by
      rw [map_smul, map_sub, cstar_p_implies_i f hf, hfasa.star_eq, sub_self, smul_zero]
    have hcsa : IsSelfAdjoint (Complex.I • (star a - a)) := by
      show star (Complex.I • (star a - a)) = _
      rw [star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I]
      module
    have h1 : (0 : 𝒜) ≤ Complex.I • (star a - a) := (hsacase _ hcsa).mp (by rw [hd])
    have h2 : (0 : 𝒜) ≤ -(Complex.I • (star a - a)) := by
      refine (hsacase _ hcsa.neg).mp ?_
      rw [map_neg, hd, neg_zero]
    have hc : Complex.I • (star a - a) = (0 : 𝒜) :=
      positive_basic_2_1 _ h1 (neg_nonneg.mp h2)
    have hsa : IsSelfAdjoint a := by
      show star a = a
      refine sub_eq_zero.mp ?_
      rcases smul_eq_zero.mp hc with h | h
      · exact absurd h Complex.I_ne_zero
      · exact h
    exact (hsacase a hsa).mp hfa
  tfae_finish

end Maps

/-! ## Parsec 20a (201): products and equalisers of C*-algebras -/

section Products

/-- **20aI** (`cstar-product-2`, cstar.tex:3015, Exercise), part 1: the
direct sum `⊕ᵢ 𝒜ᵢ` (Mathlib: `lp 𝒜 ∞`, cf. **3V**) is the categorical
product in `CStar_miu`: for every C*-algebra `ℬ` and family of miu-maps
`fᵢ : ℬ → 𝒜ᵢ` there is a unique miu-map `g : ℬ → ⊕ᵢ 𝒜ᵢ` with `πᵢ ∘ g = fᵢ`
(and similarly in `cCStar_miu`). -/
theorem cstar_product_2_miu {ι : Type*} {𝒜 : ι → Type*}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, Nontrivial (𝒜 i)] {ℬ : Type*}
    [CStarAlgebra ℬ] (f : ∀ i, ℬ →⋆ₐ[ℂ] 𝒜 i) :
    ∃! g : ℬ →⋆ₐ[ℂ] lp 𝒜 ∞, ∀ (i : ι) (b : ℬ),
      (g b : ∀ i, 𝒜 i) i = f i b :=
  by
    have hmem : ∀ b : ℬ, Memℓp (fun i => f i b) ∞ := fun b =>
      memℓp_infty ⟨‖b‖, by
        rintro y ⟨i, rfl⟩
        exact NonUnitalStarAlgHom.norm_apply_le (f i) b⟩
    refine ⟨{ toFun := fun b => ⟨fun i => f i b, hmem b⟩
              map_one' := by ext i; simp
              map_mul' := fun x y => by ext i; simp
              map_zero' := by ext i; simp
              map_add' := fun x y => by ext i; exact map_add (f i) x y
              commutes' := fun r => by ext i; simp [Algebra.algebraMap_eq_smul_one]
              map_star' := fun x => by ext i; simpa using map_star (f i) x },
            fun i b => rfl, ?_⟩
    intro g' hg'
    ext b i
    exact hg' i b

/-- Auxiliary: `⊕ᵢ 𝒜ᵢ` is a C*-algebra.  Mathlib supplies the `NormedRing`
instance (`Mathlib/Analysis/CStarAlgebra/lpSpace.lean`) and the commutative
case, but not this one. -/
noncomputable instance lpInftyCStarAlgebra {ι : Type*} {𝒜 : ι → Type*}
    [∀ i, Nontrivial (𝒜 i)] [∀ i, CStarAlgebra (𝒜 i)] : CStarAlgebra (lp 𝒜 ∞) where

/-- **20aI** (`cstar-product-2`, cstar.tex:3015, Exercise), part 2 (key step
for the `pu`-variant): an element of `⊕ᵢ 𝒜ᵢ` is positive iff all of its
components are. -/
theorem cstar_product_2_positive {ι : Type*} {𝒜 : ι → Type*}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, Nontrivial (𝒜 i)]
    [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [PartialOrder (lp 𝒜 ∞)] [StarOrderedRing (lp 𝒜 ∞)] (a : lp 𝒜 ∞) :
    0 ≤ a ↔ ∀ i, 0 ≤ (a : ∀ i, 𝒜 i) i :=
  by
    constructor
    · intro h
      rw [StarOrderedRing.nonneg_iff] at h
      induction h using AddSubmonoid.closure_induction with
      | mem x hx =>
          obtain ⟨s, rfl⟩ := hx
          intro i
          show (0 : 𝒜 i) ≤ star ((s : ∀ i, 𝒜 i) i) * ((s : ∀ i, 𝒜 i) i)
          exact star_mul_self_nonneg _
      | zero => intro i; exact le_of_eq rfl
      | add x y _ _ hx hy =>
          intro i
          show (0 : 𝒜 i) ≤ (x : ∀ i, 𝒜 i) i + (y : ∀ i, 𝒜 i) i
          exact add_nonneg (hx i) (hy i)
    · intro h
      -- The thesis's own criterion (**17V**, parsec 170) reads positivity off the
      -- norm: `0 ≤ x` iff `‖x - t‖ ≤ t` for every `t ≥ ‖x‖/2`.  On `⊕ᵢ 𝒜ᵢ` the
      -- norm is a supremum, so a single `t` works for all components at once.
      -- No square root — and in particular no continuous functional calculus,
      -- which the thesis only reaches at parsec 270 — is needed.
      set t : ℝ := ‖a‖ / 2 with ht
      have ht0 : 0 ≤ t := by positivity
      have hti : ∀ i, ‖(a : ∀ i, 𝒜 i) i‖ / 2 ≤ t := by
        intro i
        have := lp.norm_apply_le_norm ENNReal.top_ne_zero a i
        rw [ht]; linarith
      have hai : ∀ i, ‖(a : ∀ i, 𝒜 i) i - algebraMap ℂ (𝒜 i) (t : ℂ)‖ ≤ t := by
        intro i
        have hi : (0 : 𝒜 i) ≤ (a : ∀ i, 𝒜 i) i ↔
            ∀ s : ℝ, ‖(a : ∀ i, 𝒜 i) i‖ / 2 ≤ s →
              ‖(a : ∀ i, 𝒜 i) i - algebraMap ℂ (𝒜 i) (s : ℂ)‖ ≤ s :=
          (cstar_positive_tfae ((a : ∀ i, 𝒜 i) i) (IsSelfAdjoint.of_nonneg (h i))).out 3 1
        exact hi.mp (h i) t (hti i)
      have hsa : IsSelfAdjoint a := by
        refine lp.ext ?_
        rw [lp.coeFn_star]
        funext i
        exact (IsSelfAdjoint.of_nonneg (h i)).star_eq
      have hmain : (∃ s : ℝ, ‖a‖ / 2 ≤ s ∧ ‖a - algebraMap ℂ (lp 𝒜 ∞) (s : ℂ)‖ ≤ s) ↔
          (0 : lp 𝒜 ∞) ≤ a := (cstar_positive_tfae a hsa).out 0 3
      refine hmain.mp ⟨t, le_rfl, ?_⟩
      refine lp.norm_le_of_forall_le ht0 fun i => ?_
      have hco : ((a - algebraMap ℂ (lp 𝒜 ∞) (t : ℂ) : lp 𝒜 ∞) : ∀ i, 𝒜 i) i
          = (a : ∀ i, 𝒜 i) i - algebraMap ℂ (𝒜 i) (t : ℂ) := by
        rw [lp.coeFn_sub]
        rfl
      rw [hco]
      exact hai i

/-- **20aII** (`cstar-equaliser-1`, cstar.tex:3044, Exercise): for miu-maps
`f, g : 𝒜 → ℬ` the set `ℰ = {a : f(a) = g(a)}` is a (closed) C*-subalgebra
of `𝒜`; its inclusion is the equaliser of `f` and `g` in `CStar_miu` and
`CStar_pu` (the universal property is set-theoretically immediate once `ℰ` is
a closed subalgebra).

(**20aIII**, `cstar-no-pu-equalisers`, cstar.tex:3058, Remark: pu-maps need
not have equalisers, shown at 84aI in vn.tex; not converted here.) -/
theorem cstar_equaliser_1 {𝒜 ℬ : Type*} [CStarAlgebra 𝒜] [CStarAlgebra ℬ]
    (f g : 𝒜 →⋆ₐ[ℂ] ℬ) :
    ∃ S : StarSubalgebra ℂ 𝒜,
      (S : Set 𝒜) = {a : 𝒜 | f a = g a} ∧ IsClosed (S : Set 𝒜) :=
  by
    have hc : ∀ φ : 𝒜 →⋆ₐ[ℂ] ℬ, Continuous φ := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ 1
        (fun a => by simpa using NonUnitalStarAlgHom.norm_apply_le φ a)
    have hset : (StarAlgHom.equalizer f g : Set 𝒜) = {a : 𝒜 | f a = g a} := by
      ext a; exact StarAlgHom.mem_equalizer f g a
    exact ⟨StarAlgHom.equalizer f g, hset, hset ▸ isClosed_eq (hc f) (hc g)⟩

end Products

/-! ## Parsec 210: separating collections of maps -/

section Separating

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
variable {ι : Type*} {ℬf : ι → Type*} [∀ i, CStarAlgebra (ℬf i)]
  [∀ i, PartialOrder (ℬf i)] [∀ i, StarOrderedRing (ℬf i)]

/-- **21II** (`separating`, cstar.tex:3098, Definition), part 1: a collection
`Ω` of linear maps on a C*-algebra `𝒜` (formalized as an indexed family with
possibly varying codomains) is *order separating* if `a` is positive iff
`ω(a) ≥ 0` for all `ω ∈ Ω`. -/
def OrderSeparating (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i) : Prop :=
  ∀ a : 𝒜, 0 ≤ a ↔ ∀ i, 0 ≤ ω i a

/-- **21II** (`separating`, cstar.tex:3098, Definition), part 2: `Ω` is
*separating* if `a = 0` iff `ω(a) = 0` for all `ω ∈ Ω`. -/
def Separating (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i) : Prop :=
  ∀ a : 𝒜, a = 0 ↔ ∀ i, ω i a = 0

/-- **21II** (`separating`, cstar.tex:3098, Definition), part 3: `Ω` is
*faithful* if a positive `a` is zero iff `ω(a) = 0` for all `ω ∈ Ω`. -/
def Faithful (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i) : Prop :=
  ∀ a : 𝒜, 0 ≤ a → (a = 0 ↔ ∀ i, ω i a = 0)

/-- **21II** (`separating`, cstar.tex:3098, Definition), part 4: `Ω` is
*centre separating* if a positive `a` is zero iff `ω(b* a b) = 0` for all
`ω ∈ Ω` and `b ∈ 𝒜`. -/
def CentreSeparating (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i) : Prop :=
  ∀ a : 𝒜, 0 ≤ a → (a = 0 ↔ ∀ (i) (b : 𝒜), ω i (star b * a * b) = 0)

/-- **21II** (`separating`, cstar.tex:3098, Definition), noted implication:
order separating collections are separating. -/
theorem OrderSeparating.separating (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i)
    (h : OrderSeparating ω) : Separating ω :=
  by
    intro a
    constructor
    · intro ha i
      rw [ha, map_zero]
    · intro hzero
      have h1 : 0 ≤ a := (h a).mpr fun i => by rw [hzero i]
      have h2 : 0 ≤ -a := (h (-a)).mpr fun i => by rw [map_neg, hzero i, neg_zero]
      exact le_antisymm (neg_nonneg.mp h2) h1

/-- **21II** (`separating`, cstar.tex:3098, Definition), noted implication:
separating collections are faithful. -/
theorem Separating.faithful (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i) (h : Separating ω) :
    Faithful ω :=
  fun a _ => h a

/-- **21II** (`separating`, cstar.tex:3098, Definition), noted implication:
faithful collections are centre separating. -/
theorem Faithful.centreSeparating (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i) (h : Faithful ω) :
    CentreSeparating ω :=
  by
    intro a ha
    constructor
    · rintro rfl i b
      simp
    · intro hb
      refine (h a ha).mpr fun i => ?_
      simpa using hb i 1

/-! **21III**–**21IV** (cstar.tex:3140, Examples): the states, the
multiplicative states (on a commutative C*-algebra), and the vector
functionals (on B(H)) are order separating — stated at 22VIII, 27–, and 25III
respectively; the four levels of separation differ — not converted. -/

/-- **21V** (`separating-self-adjoint`, cstar.tex:3217, Exercise): given a
separating collection `Ω` of involution preserving maps on `𝒜`, an element
`a` is self-adjoint iff `ω(a)` is self-adjoint for all `ω ∈ Ω`. -/
theorem separating_self_adjoint (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i) (hΩ : Separating ω)
    (hstar : ∀ i (a : 𝒜), ω i (star a) = star (ω i a)) (a : 𝒜) :
    IsSelfAdjoint a ↔ ∀ i, IsSelfAdjoint (ω i a) :=
  by
    constructor
    · intro hsa i
      rw [isSelfAdjoint_iff, ← hstar i a, hsa.star_eq]
    · intro hall
      have hd : star a - a = 0 := by
        refine (hΩ _).mpr fun i => ?_
        rw [map_sub, hstar i a, (hall i).star_eq, sub_self]
      exact sub_eq_zero.mp hd

/-- **21VII** (`order-separating-norm`, cstar.tex:3232, Proposition): for a
collection `Ω` of pu-maps on `𝒜` the following are equivalent:
(1) `Ω` is order separating; (2) `‖a‖ = sup_ω ‖ω(a)‖` for self-adjoint `a`;
(3) `‖a‖ = sup_ω ‖ω(a)‖` for positive `a`. -/
theorem order_separating_norm (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i)
    (hpos : ∀ i (a : 𝒜), 0 ≤ a → 0 ≤ ω i a) (hu : ∀ i, ω i 1 = 1) :
    List.TFAE [
      OrderSeparating ω,
      ∀ a : 𝒜, IsSelfAdjoint a → ‖a‖ = ⨆ i, ‖ω i a‖,
      ∀ a : 𝒜, 0 ≤ a → ‖a‖ = ⨆ i, ‖ω i a‖] := by
  -- The thesis (cstar.tex:3247) applies **20VI** to the single pu-map
  -- `⟨ω⟩ : 𝒜 → ⊕_ω ℬ_ω` into the C*-product, where positivity is pointwise
  -- and the norm is the supremum.  Since the ℓ^∞-product of an arbitrary
  -- family is not available in the tree (it is exactly the gap recorded for
  -- `vonNeumannAlgebra_lp_infty`), we run **20VI**'s *argument* on the family
  -- directly; the three steps are the same.  Note no index is needed: for
  -- empty `ι` all three conditions force `𝒜` to be trivial, and the proof
  -- below covers that case without a split (`⨆ over ∅ = 0` in `ℝ`).
  have hbdd : ∀ a : 𝒜, IsSelfAdjoint a → BddAbove (Set.range fun i => ‖ω i a‖) :=
    fun a ha => ⟨‖a‖, by
      rintro x ⟨i, rfl⟩
      exact norm_map_le_of_isSelfAdjoint (ω i) (hpos i) (hu i) a ha⟩
  have hsupnn : ∀ a : 𝒜, 0 ≤ ⨆ i, ‖ω i a‖ :=
    fun a => Real.iSup_nonneg fun i => norm_nonneg _
  tfae_have 2 → 3 := fun h a ha => h a (IsSelfAdjoint.of_nonneg ha)
  tfae_have 1 → 2 := by
    intro h1 a ha
    refine le_antisymm ?_ (Real.iSup_le
      (fun i => norm_map_le_of_isSelfAdjoint (ω i) (hpos i) (hu i) a ha)
      (norm_nonneg a))
    set s : ℝ := ⨆ i, ‖ω i a‖ with hs
    have hi : ∀ i, -(algebraMap ℂ (ℬf i) (s : ℂ)) ≤ ω i a ∧
        ω i a ≤ algebraMap ℂ (ℬf i) (s : ℂ) := fun i =>
      (positive_basic_2_3a (ω i a) (isSelfAdjoint_map_of_pos (ω i) (hpos i) ha) s
        (hsupnn a)).mpr (le_ciSup (hbdd a ha) i)
    refine (positive_basic_2_3a a ha s (hsupnn a)).mp ⟨?_, ?_⟩
    · refine neg_le_iff_add_nonneg.mpr ((h1 _).mpr fun i => ?_)
      rw [map_add, map_algebraMap_of_unital (ω i) (hu i)]
      exact neg_le_iff_add_nonneg.mp (hi i).1
    · refine sub_nonneg.mp ((h1 _).mpr fun i => ?_)
      rw [map_sub, map_algebraMap_of_unital (ω i) (hu i)]
      exact sub_nonneg.mpr (hi i).2
  tfae_have 3 → 1 := by
    intro h3
    have hsacase : ∀ a : 𝒜, IsSelfAdjoint a → (0 ≤ a ↔ ∀ i, 0 ≤ ω i a) := by
      intro a ha
      have hb : (0 : 𝒜) ≤ algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ) - a :=
        sub_nonneg.mpr ((positive_basic_2_3a a ha ‖a‖ (norm_nonneg a)).mpr le_rfl).2
      set b : 𝒜 := algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ) - a with hbdef
      have hbsa : IsSelfAdjoint b := (isSelfAdjoint_algebraMap_ofReal ‖a‖).sub ha
      have hωb : ∀ i, ω i b = algebraMap ℂ (ℬf i) ((‖a‖ : ℝ) : ℂ) - ω i a := by
        intro i; rw [hbdef, map_sub, map_algebraMap_of_unital (ω i) (hu i)]
      have heq := h3 b hb
      rw [← nonneg_iff_norm_algebraMap_sub_le a ha ‖a‖ (norm_nonneg a)
        (by linarith [norm_nonneg a])]
      have hright : (∀ i, 0 ≤ ω i a) ↔ ∀ i, ‖ω i b‖ ≤ ‖a‖ := by
        refine forall_congr' fun i => ?_
        rw [hωb i]
        exact (nonneg_iff_norm_algebraMap_sub_le (ω i a)
          (isSelfAdjoint_map_of_pos (ω i) (hpos i) ha) ‖a‖ (norm_nonneg a)
          (norm_map_le_two_mul (ω i) (hpos i) (hu i) a)).symm
      rw [hright, heq]
      exact ⟨fun h i => le_trans (le_ciSup (hbdd b hbsa) i) h,
        fun h => Real.iSup_le h (norm_nonneg a)⟩
    intro a
    refine ⟨fun ha i => hpos i a ha, fun hall => ?_⟩
    have hsaω : ∀ i, IsSelfAdjoint (ω i a) := fun i => IsSelfAdjoint.of_nonneg (hall i)
    have hd : ∀ i, ω i (Complex.I • (star a - a)) = 0 := by
      intro i
      rw [map_smul, map_sub, cstar_p_implies_i (ω i) (hpos i), (hsaω i).star_eq,
        sub_self, smul_zero]
    have hcsa : IsSelfAdjoint (Complex.I • (star a - a)) := by
      show star (Complex.I • (star a - a)) = _
      rw [star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I]
      module
    have h1 : (0 : 𝒜) ≤ Complex.I • (star a - a) :=
      (hsacase _ hcsa).mpr fun i => by rw [hd i]
    have h2 : (0 : 𝒜) ≤ -(Complex.I • (star a - a)) :=
      (hsacase _ hcsa.neg).mpr fun i => by rw [map_neg, hd i, neg_zero]
    have hc : Complex.I • (star a - a) = (0 : 𝒜) :=
      positive_basic_2_1 _ h1 (neg_nonneg.mp h2)
    have hsa : IsSelfAdjoint a := by
      show star a = a
      refine sub_eq_zero.mp ?_
      rcases smul_eq_zero.mp hc with h | h
      · exact absurd h Complex.I_ne_zero
      · exact h
    exact (hsacase a hsa).mpr hall
  tfae_finish

/-! **21IX** (`warning-norm-states`, cstar.tex:3256, Warning): the formula
`‖a‖ = sup_ω ‖ω(a)‖` may fail for non-self-adjoint `a` — not converted. -/

/-- **21X** (`order-separating-dense-subset`, cstar.tex:3275, Exercise): an
operator norm dense subset `Ω'` of an order separating collection `Ω` of
positive functionals on `𝒜` is order separating too. -/
theorem order_separating_dense_subset (Ω Ω' : Set (𝒜 →L[ℂ] ℂ))
    (hsub : Ω' ⊆ Ω)
    (hdense : ∀ ω ∈ Ω, ∀ ε : ℝ, 0 < ε → ∃ ω' ∈ Ω', ‖ω - ω'‖ < ε)
    (hpos : ∀ ω ∈ Ω, ∀ a : 𝒜, 0 ≤ a → 0 ≤ ω a)
    (hΩ : OrderSeparating fun ω : Ω => ((ω : 𝒜 →L[ℂ] ℂ) : 𝒜 →ₗ[ℂ] ℂ)) :
    OrderSeparating fun ω : Ω' => ((ω : 𝒜 →L[ℂ] ℂ) : 𝒜 →ₗ[ℂ] ℂ) :=
  by
    intro a
    refine ⟨fun ha ω' => hpos _ (hsub ω'.2) a ha, fun H => ?_⟩
    refine (hΩ a).mpr ?_
    rintro ⟨ω, hω⟩
    show (0 : ℂ) ≤ ω a
    rcases eq_or_ne a 0 with rfl | ha0
    · simp
    have hanorm : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha0
    have key : ∀ δ : ℝ, 0 < δ → ∃ w : ℂ, 0 ≤ w ∧ ‖ω a - w‖ ≤ δ := by
      intro δ hδ
      obtain ⟨ω', hω', hlt⟩ := hdense ω hω (δ / ‖a‖) (by positivity)
      refine ⟨ω' a, H ⟨ω', hω'⟩, ?_⟩
      have h1 : ω a - ω' a = (ω - ω') a := by simp
      rw [h1]
      calc ‖(ω - ω') a‖ ≤ ‖ω - ω'‖ * ‖a‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (δ / ‖a‖) * ‖a‖ := mul_le_mul_of_nonneg_right hlt.le (norm_nonneg a)
        _ = δ := by field_simp
    have hre : 0 ≤ (ω a).re := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨w, hw, hle⟩ := key ε hε
      have hwre : 0 ≤ w.re := by simpa using (Complex.le_def.mp hw).1
      have hbd : |(ω a).re - w.re| ≤ ε := by
        refine le_trans ?_ hle
        simpa using Complex.abs_re_le_norm (ω a - w)
      have := abs_le.mp hbd
      linarith [this.1]
    have him : (ω a).im = 0 := by
      have h0 : |(ω a).im| ≤ 0 := by
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨w, hw, hle⟩ := key ε hε
        have hwim : w.im = 0 := (Complex.le_def.mp hw).2.symm
        have hbd : |(ω a).im - w.im| ≤ ε := by
          refine le_trans ?_ hle
          simpa using Complex.abs_im_le_norm (ω a - w)
        rw [hwim, sub_zero] at hbd
        linarith
      simpa using abs_nonpos_iff.mp h0
    rw [Complex.le_def]
    exact ⟨by simpa using hre, by simpa using him.symm⟩

end Separating

/-! ## Parsec 220: order ideals and states -/

section OrderIdeals

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **22II** (cstar.tex:3300, Definition): an *order ideal* of a C*-algebra
`𝒜` is a linear subspace `I` closed under the involution such that
`[-b, b] ⊆ I` for every positive `b ∈ I`. -/
structure IsOrderIdeal (I : Submodule ℂ 𝒜) : Prop where
  star_mem : ∀ b ∈ I, star b ∈ I
  mem_of_mem_interval : ∀ b ∈ I, 0 ≤ b → ∀ a : 𝒜, -b ≤ a → a ≤ b → a ∈ I

/-- **22II** (cstar.tex:3300, Definition): an order ideal is *proper* when it
does not contain `1`. -/
def IsProperOrderIdeal (I : Submodule ℂ 𝒜) : Prop :=
  IsOrderIdeal I ∧ (1 : 𝒜) ∉ I

/-- **22II** (cstar.tex:3300, Definition): a *maximal* order ideal is a
proper order ideal maximal among the proper order ideals. -/
def IsMaximalOrderIdeal (I : Submodule ℂ 𝒜) : Prop :=
  IsProperOrderIdeal I ∧
    ∀ J : Submodule ℂ 𝒜, IsProperOrderIdeal J → I ≤ J → J = I

/-- A *state* of a C*-algebra: a pu-map `ω : 𝒜 → ℂ` (**21III**,
cstar.tex:3140; the term is introduced there and used from parsec 220 on). -/
def IsState (ω : 𝒜 →ₗ[ℂ] ℂ) : Prop :=
  IsPositiveMap ω ∧ ω 1 = 1

-- copy of the file-private `eq_of_add_self_eq`
private theorem eq_of_add_self_eq' {x y : 𝒜} (hxy : x + x = y + y) : x = y := by
  have h : (2 : ℂ)⁻¹ • (x + x) = (2 : ℂ)⁻¹ • (y + y) := by rw [hxy]
  rwa [← two_smul ℂ x, ← two_smul ℂ y, smul_smul, smul_smul,
    inv_mul_cancel₀ (two_ne_zero), one_smul, one_smul] at h

private theorem sub_add_cancel'' (x y : 𝒜) : x - y + y = x := by abel

/-- An element of an order interval `[-b, b]` is self-adjoint. -/
private theorem isSelfAdjoint_of_mem_interval {b c : 𝒜} (h1 : -b ≤ c) (h2 : c ≤ b) :
    IsSelfAdjoint c := by
  have hs1 : IsSelfAdjoint (b - c) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr h2)
  have hs2 : IsSelfAdjoint (c - -b) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr h1)
  have hsum : IsSelfAdjoint (c - -b - (b - c)) := hs2.sub hs1
  have he : c - -b - (b - c) = c + c := by abel
  rw [he] at hsum
  have h := hsum.star_eq
  rw [star_add] at h
  exact eq_of_add_self_eq' h


/-- **22III** (`order-ideal-basic`, cstar.tex:3324, Exercise), part 1: the
kernel of a state is a maximal order ideal. -/
theorem order_ideal_basic_1 (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsState ω) :
    IsMaximalOrderIdeal (LinearMap.ker ω) := by
  obtain ⟨hpos, hone⟩ := hω
  have hstar := cstar_p_implies_i ω hpos
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro b hb
    rw [LinearMap.mem_ker] at hb ⊢
    rw [hstar b, hb, star_zero]
  · intro b hb hb0 a h1 h2
    rw [LinearMap.mem_ker] at hb ⊢
    have hub := hpos _ (sub_nonneg.mpr h2)
    have hlb := hpos _ (sub_nonneg.mpr h1)
    rw [map_sub, hb, zero_sub] at hub
    rw [map_sub, map_neg, hb, neg_zero, sub_zero] at hlb
    exact le_antisymm (neg_nonneg.mp hub) hlb
  · intro h1
    rw [LinearMap.mem_ker, hone] at h1
    exact one_ne_zero h1
  · intro J hJ hle
    by_contra hne
    obtain ⟨x, hxJ, hxk⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle (Ne.symm hne))
    have hx0 : ω x ≠ 0 := fun h => hxk (LinearMap.mem_ker.mpr h)
    have hyJ : (ω x)⁻¹ • x ∈ J := J.smul_mem _ hxJ
    have hy1 : ω ((ω x)⁻¹ • x) = 1 := by
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx0]
    have h1y : (1 : 𝒜) - (ω x)⁻¹ • x ∈ J :=
      hle (LinearMap.mem_ker.mpr (by rw [map_sub, hy1, hone, sub_self]))
    have h1J : (1 : 𝒜) ∈ J := by
      have h := J.add_mem h1y hyJ
      rwa [sub_add_cancel''] at h
    exact hJ.2 h1J

/-- **22III** (`order-ideal-basic`, cstar.tex:3324, Exercise), part 2: every
proper order ideal is contained in a maximal order ideal. -/
theorem order_ideal_basic_2 (I : Submodule ℂ 𝒜) (hI : IsProperOrderIdeal I) :
    ∃ J : Submodule ℂ 𝒜, IsMaximalOrderIdeal J ∧ I ≤ J := by
  have hzorn : ∀ c ⊆ {J : Submodule ℂ 𝒜 | IsProperOrderIdeal J},
      IsChain (· ≤ ·) c → ∀ y ∈ c,
        ∃ ub ∈ {J : Submodule ℂ 𝒜 | IsProperOrderIdeal J}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    have hmem : ∀ x : 𝒜, x ∈ sSup c ↔ ∃ K ∈ c, x ∈ K := fun x =>
      Submodule.mem_sSup_of_directed ⟨y, hy⟩ hchain.directedOn
    refine ⟨sSup c, ⟨⟨?_, ?_⟩, ?_⟩, fun z hz => le_sSup hz⟩
    · intro b hb
      obtain ⟨K, hKc, hbK⟩ := (hmem b).mp hb
      exact Submodule.mem_sSup_of_mem hKc ((hc hKc).1.star_mem b hbK)
    · intro b hb hb0 a h1 h2
      obtain ⟨K, hKc, hbK⟩ := (hmem b).mp hb
      exact Submodule.mem_sSup_of_mem hKc ((hc hKc).1.mem_of_mem_interval b hbK hb0 a h1 h2)
    · intro h1
      obtain ⟨K, hKc, h1K⟩ := (hmem 1).mp h1
      exact (hc hKc).2 h1K
  obtain ⟨m, hIm, hm⟩ := zorn_le_nonempty₀ _ hzorn I hI
  exact ⟨m, ⟨hm.1, fun J hJ hmJ => le_antisymm (hm.2 hJ hmJ) hmJ⟩, hIm⟩

/-! ### The least order ideal `(a)` (22III.3) -/

/-- Elements sandwiched between real multiples of `a`. -/
private def sandwiched (a : 𝒜) : Set 𝒜 :=
  {x | ∃ lam mu : ℝ, lam • a ≤ x ∧ x ≤ mu • a}

private theorem smul_le_smul_left' {r : ℝ} (hr : 0 ≤ r) {x y : 𝒜} (h : x ≤ y) :
    r • x ≤ r • y := by
  have h1 := ofReal_smul_nonneg (sub_nonneg.mpr h) hr
  rw [Complex.coe_smul, smul_sub] at h1
  exact sub_nonneg.mp h1

private theorem sandwiched_zero (a : 𝒜) : (0 : 𝒜) ∈ sandwiched a :=
  ⟨0, 0, by simp⟩

private theorem sandwiched_add {a x y : 𝒜} (hx : x ∈ sandwiched a)
    (hy : y ∈ sandwiched a) : x + y ∈ sandwiched a := by
  obtain ⟨l1, m1, hl1, hm1⟩ := hx
  obtain ⟨l2, m2, hl2, hm2⟩ := hy
  exact ⟨l1 + l2, m1 + m2, by rw [add_smul]; exact add_le_add hl1 hl2,
    by rw [add_smul]; exact add_le_add hm1 hm2⟩

private theorem sandwiched_neg {a x : 𝒜} (hx : x ∈ sandwiched a) :
    -x ∈ sandwiched a := by
  obtain ⟨l, m, hl, hm⟩ := hx
  exact ⟨-m, -l, by rw [neg_smul]; exact neg_le_neg hm,
    by rw [neg_smul]; exact neg_le_neg hl⟩

private theorem sandwiched_real_smul {a x : 𝒜} (r : ℝ) (hx : x ∈ sandwiched a) :
    r • x ∈ sandwiched a := by
  rcases le_total 0 r with hr | hr
  · obtain ⟨l, m, hl, hm⟩ := hx
    exact ⟨r * l, r * m, by rw [mul_smul]; exact smul_le_smul_left' hr hl,
      by rw [mul_smul]; exact smul_le_smul_left' hr hm⟩
  · obtain ⟨l, m, hl, hm⟩ := sandwiched_neg hx
    have hr' : (0 : ℝ) ≤ -r := by linarith
    refine ⟨-r * l, -r * m, ?_, ?_⟩
    · rw [mul_smul, ← neg_smul_neg r x]
      exact smul_le_smul_left' hr' hl
    · rw [mul_smul, ← neg_smul_neg r x]
      exact smul_le_smul_left' hr' hm

/-- **22III**.3: the least order ideal containing a self-adjoint `a`, as a
submodule: `b ∈ (a)` iff both `ℜ b` and `ℑ b` are sandwiched between real
multiples of `a`. -/
private def orderIdealGen (a : 𝒜) : Submodule ℂ 𝒜 where
  carrier := {b | ((ℜ b : 𝒜) ∈ sandwiched a) ∧ ((ℑ b : 𝒜) ∈ sandwiched a)}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero, ZeroMemClass.coe_zero]
    exact ⟨sandwiched_zero a, sandwiched_zero a⟩
  add_mem' := by
    rintro b c ⟨hbr, hbi⟩ ⟨hcr, hci⟩
    constructor
    · rw [map_add, AddSubgroup.coe_add]
      exact sandwiched_add hbr hcr
    · rw [map_add, AddSubgroup.coe_add]
      exact sandwiched_add hbi hci
  smul_mem' := by
    rintro z b ⟨hbr, hbi⟩
    constructor
    · rw [realPart_smul]
      have he : ((z.re • ℜ b - z.im • ℑ b : selfAdjoint 𝒜) : 𝒜)
          = z.re • (ℜ b : 𝒜) + -(z.im • (ℑ b : 𝒜)) := by
        rw [AddSubgroup.coe_sub, selfAdjoint.val_smul, selfAdjoint.val_smul,
          sub_eq_add_neg]
      rw [he]
      exact sandwiched_add (sandwiched_real_smul _ hbr)
        (sandwiched_neg (sandwiched_real_smul _ hbi))
    · rw [imaginaryPart_smul]
      have he : ((z.re • ℑ b + z.im • ℜ b : selfAdjoint 𝒜) : 𝒜)
          = z.re • (ℑ b : 𝒜) + z.im • (ℜ b : 𝒜) := by
        rw [AddSubgroup.coe_add, selfAdjoint.val_smul, selfAdjoint.val_smul]
      rw [he]
      exact sandwiched_add (sandwiched_real_smul _ hbi)
        (sandwiched_real_smul _ hbr)

private theorem mem_orderIdealGen_iff {a b : 𝒜} :
    b ∈ orderIdealGen a ↔
      (ℜ b : 𝒜) ∈ sandwiched a ∧ (ℑ b : 𝒜) ∈ sandwiched a :=
  Iff.rfl

private theorem self_mem_orderIdealGen {a : 𝒜} (ha : IsSelfAdjoint a) :
    a ∈ orderIdealGen a := by
  rw [mem_orderIdealGen_iff]
  constructor
  · rw [ha.coe_realPart]
    exact ⟨1, 1, by rw [one_smul], by rw [one_smul]⟩
  · rw [ha.imaginaryPart, ZeroMemClass.coe_zero]
    exact sandwiched_zero a

private theorem mem_orderIdealGen_iff_of_isSelfAdjoint {a b : 𝒜}
    (hb : IsSelfAdjoint b) :
    b ∈ orderIdealGen a ↔ ∃ lam mu : ℝ, lam • a ≤ b ∧ b ≤ mu • a := by
  rw [mem_orderIdealGen_iff, hb.coe_realPart, hb.imaginaryPart,
    ZeroMemClass.coe_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, sandwiched_zero a⟩⟩

private theorem orderIdealGen_isOrderIdeal {a : 𝒜} :
    IsOrderIdeal (orderIdealGen a) := by
  constructor
  · intro b hb
    obtain ⟨hbr, hbi⟩ := hb
    constructor
    · have h : (ℜ (star b) : 𝒜) = (ℜ b : 𝒜) := by
        rw [realPart_apply_coe, realPart_apply_coe, star_star, add_comm]
      rw [h]
      exact hbr
    · have h : (ℑ (star b) : 𝒜) = -(ℑ b : 𝒜) := by
        rw [imaginaryPart_apply_coe, imaginaryPart_apply_coe, star_star,
          ← smul_neg, ← smul_neg, neg_sub]
      rw [h]
      exact sandwiched_neg hbi
  · intro b hb hb0 c h1 h2
    have hcsa : IsSelfAdjoint c := isSelfAdjoint_of_mem_interval h1 h2
    have hbsa : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg hb0
    obtain ⟨hbr, hbi⟩ := hb
    rw [hbsa.coe_realPart] at hbr
    obtain ⟨l, m, hl, hm⟩ := hbr
    constructor
    · rw [hcsa.coe_realPart]
      refine ⟨-m, m, ?_, le_trans h2 hm⟩
      rw [neg_smul]
      exact le_trans (neg_le_neg hm) h1
    · rw [hcsa.imaginaryPart, ZeroMemClass.coe_zero]
      exact sandwiched_zero a

private theorem orderIdealGen_least {a : 𝒜} (J : Submodule ℂ 𝒜)
    (hJ : IsOrderIdeal J) (haJ : a ∈ J) : orderIdealGen a ≤ J := by
  have hsand : ∀ x : 𝒜, x ∈ sandwiched a → x ∈ J := by
    rintro x ⟨l, m, hl, hm⟩
    have hpos : (0 : 𝒜) ≤ (m - l) • a := by
      rw [sub_smul]
      exact sub_nonneg.mpr (le_trans hl hm)
    have hmem : (m - l) • a ∈ J := by
      have h := J.smul_mem (((m - l : ℝ) : ℂ)) haJ
      rwa [Complex.coe_smul] at h
    have hx : x - l • a ∈ J := by
      refine hJ.mem_of_mem_interval _ hmem hpos _ ?_ ?_
      · exact le_trans (neg_nonpos_of_nonneg hpos) (sub_nonneg.mpr hl)
      · rw [sub_smul]
        exact sub_le_sub_right hm _
    have hla : l • a ∈ J := by
      have h := J.smul_mem (((l : ℝ) : ℂ)) haJ
      rwa [Complex.coe_smul] at h
    have h := J.add_mem hx hla
    rwa [sub_add_cancel''] at h
  intro b hb
  obtain ⟨hbr, hbi⟩ := hb
  have h := J.add_mem (hsand _ hbr) (J.smul_mem Complex.I (hsand _ hbi))
  rwa [realPart_add_I_smul_imaginaryPart] at h


/-- **22III** (`order-ideal-basic`, cstar.tex:3324, Exercise), part 3a: for
self-adjoint `a` there is a least order ideal `(a)` containing `a`, and a
self-adjoint `b` belongs to `(a)` iff `λ a ≤ b ≤ μ a` for some `λ, μ ∈ ℝ`. -/
theorem order_ideal_basic_3a (a : 𝒜) (ha : IsSelfAdjoint a) :
    ∃ I : Submodule ℂ 𝒜, IsOrderIdeal I ∧ a ∈ I ∧
      (∀ J : Submodule ℂ 𝒜, IsOrderIdeal J → a ∈ J → I ≤ J) ∧
      ∀ b : 𝒜, IsSelfAdjoint b →
        (b ∈ I ↔ ∃ lam mu : ℝ, lam • a ≤ b ∧ b ≤ mu • a) :=
  ⟨orderIdealGen a, orderIdealGen_isOrderIdeal, self_mem_orderIdealGen ha,
    fun J hJ haJ => orderIdealGen_least J hJ haJ,
    fun _ hb => mem_orderIdealGen_iff_of_isSelfAdjoint hb⟩

private theorem least_eq_orderIdealGen {a : 𝒜} (ha : IsSelfAdjoint a)
    (I : Submodule ℂ 𝒜) (hI : IsOrderIdeal I) (haI : a ∈ I)
    (hleast : ∀ J : Submodule ℂ 𝒜, IsOrderIdeal J → a ∈ J → I ≤ J) :
    I = orderIdealGen a :=
  le_antisymm (hleast _ orderIdealGen_isOrderIdeal (self_mem_orderIdealGen ha))
    (orderIdealGen_least I hI haI)

private theorem zero_le_one' : (0 : 𝒜) ≤ 1 := zero_le_one

/-- **22III** (`order-ideal-basic`, cstar.tex:3324, Exercise), part 3b: when
`0 ≰ a ≰ 0`, the least order ideal containing `a` is the line `ℂa`. -/
theorem order_ideal_basic_3b (a : 𝒜) (ha : IsSelfAdjoint a)
    (h0 : ¬0 ≤ a) (h0' : ¬a ≤ 0) (I : Submodule ℂ 𝒜) (hI : IsOrderIdeal I)
    (haI : a ∈ I)
    (hleast : ∀ J : Submodule ℂ 𝒜, IsOrderIdeal J → a ∈ J → I ≤ J) :
    I = Submodule.span ℂ {a} := by
  rw [least_eq_orderIdealGen ha I hI haI hleast]
  refine le_antisymm ?_
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (self_mem_orderIdealGen ha)))
  have hsand : ∀ x : 𝒜, x ∈ sandwiched a → x ∈ Submodule.span ℂ {a} := by
    rintro x ⟨l, m, hl, hm⟩
    have hpos : (0 : 𝒜) ≤ (m - l) • a := by
      rw [sub_smul]
      exact sub_nonneg.mpr (le_trans hl hm)
    rcases lt_trichotomy (m - l) 0 with hlt | heq | hgt
    · exfalso
      have hs : (0 : ℝ) < -(m - l) := by linarith
      have h1 : (-(m - l)) • a ≤ 0 := by
        rw [neg_smul]
        exact neg_nonpos_of_nonneg hpos
      have h2 := smul_le_smul_left' (le_of_lt (inv_pos.mpr hs)) h1
      rw [smul_zero, smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul] at h2
      exact h0' h2
    · have hml : m = l := by linarith
      have hx : x = l • a := le_antisymm (by rwa [hml] at hm) hl
      rw [hx, ← Complex.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
    · exfalso
      have h2 := smul_le_smul_left' (le_of_lt (inv_pos.mpr hgt)) hpos
      rw [smul_zero, smul_smul, inv_mul_cancel₀ (ne_of_gt hgt), one_smul] at h2
      exact h0 h2
  rintro b ⟨hbr, hbi⟩
  have h := Submodule.add_mem _ (hsand _ hbr)
    (Submodule.smul_mem _ Complex.I (hsand _ hbi))
  rwa [realPart_add_I_smul_imaginaryPart] at h

/-- If `0 ≤ a` and `1 ≤ m • a` then `a` is invertible (`m` is forced positive
unless `𝒜` is trivial). -/
private theorem isUnit_of_one_le_smul {a : 𝒜} (hpos : 0 ≤ a) {m : ℝ}
    (hm : (1 : 𝒜) ≤ m • a) : IsUnit a := by
  rcases subsingleton_or_nontrivial 𝒜 with hsub | hnt
  · exact isUnit_of_subsingleton a
  have hmpos : 0 < m := by
    by_contra hle
    push_neg at hle
    have h2 : (0 : 𝒜) ≤ (-m) • a := by
      rw [← Complex.coe_smul]
      exact ofReal_smul_nonneg hpos (by linarith)
    rw [neg_smul] at h2
    have h3 : (1 : 𝒜) ≤ 0 := le_trans hm (neg_nonneg.mp h2)
    exact one_ne_zero (α := 𝒜) (le_antisymm h3 zero_le_one')
  have hinv : m⁻¹ • (1 : 𝒜) ≤ a := by
    have h2 := smul_le_smul_left' (le_of_lt (inv_pos.mpr hmpos)) hm
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hmpos), one_smul] at h2
  obtain ⟨n, hn⟩ := exists_nat_gt m
  have hn0 : (0 : ℝ) < n := lt_trans hmpos hn
  refine (positive_basic_2_6 a hpos).mpr ⟨n, by exact_mod_cast hn0, ?_⟩
  have hle2 : ((n : ℝ))⁻¹ ≤ m⁻¹ := by
    apply inv_anti₀ hmpos (le_of_lt hn)
  have hcast : ((n : ℂ))⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [hcast]
  calc algebraMap ℂ 𝒜 (((n : ℝ)⁻¹ : ℝ) : ℂ)
      ≤ algebraMap ℂ 𝒜 ((m⁻¹ : ℝ) : ℂ) := algebraMap_ofReal_mono hle2
    _ = m⁻¹ • (1 : 𝒜) := by
        rw [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
    _ ≤ a := hinv

/-- **22III** (`order-ideal-basic`, cstar.tex:3324, Exercise), part 3c:
`1 ∈ (a)` iff `a` is invertible and either `0 ≤ a` or `a ≤ 0`. -/
theorem order_ideal_basic_3c (a : 𝒜) (ha : IsSelfAdjoint a)
    (I : Submodule ℂ 𝒜) (hI : IsOrderIdeal I) (haI : a ∈ I)
    (hleast : ∀ J : Submodule ℂ 𝒜, IsOrderIdeal J → a ∈ J → I ≤ J) :
    (1 : 𝒜) ∈ I ↔ IsUnit a ∧ (0 ≤ a ∨ a ≤ 0) := by
  rw [least_eq_orderIdealGen ha I hI haI hleast,
    mem_orderIdealGen_iff_of_isSelfAdjoint (IsSelfAdjoint.one 𝒜)]
  constructor
  · rintro ⟨l, m, hl, hm⟩
    have hor : 0 ≤ a ∨ a ≤ 0 := by
      by_contra hno
      push_neg at hno
      obtain ⟨h0, h0'⟩ := hno
      have hnt : Nontrivial 𝒜 := by
        rcases subsingleton_or_nontrivial 𝒜 with hsub | hnt
        · exact absurd (le_of_eq (Subsingleton.elim (0 : 𝒜) a)) h0
        · exact hnt
      have hspan := order_ideal_basic_3b a ha h0 h0' (orderIdealGen a)
        orderIdealGen_isOrderIdeal (self_mem_orderIdealGen ha)
        (fun J hJ haJ => orderIdealGen_least J hJ haJ)
      have h1span : (1 : 𝒜) ∈ Submodule.span ℂ {a} := by
        rw [← hspan]
        exact (mem_orderIdealGen_iff_of_isSelfAdjoint
          (IsSelfAdjoint.one 𝒜)).mpr ⟨l, m, hl, hm⟩
      obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp h1span
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hz
        exact one_ne_zero hz.symm
      have hae : a = z⁻¹ • (1 : 𝒜) := by
        rw [← hz, smul_smul, inv_mul_cancel₀ hz0, one_smul]
      have hreal : (starRingEnd ℂ) z⁻¹ = z⁻¹ := by
        have h1 := ha.star_eq
        rw [hae, star_smul, star_one, Complex.star_def] at h1
        have h2 : ((starRingEnd ℂ) z⁻¹ - z⁻¹) • (1 : 𝒜) = 0 := by
          rw [sub_smul, h1, sub_self]
        rcases smul_eq_zero.mp h2 with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h one_ne_zero
      have hrim : z⁻¹.im = 0 := by
        have h := congrArg Complex.im hreal
        rw [Complex.conj_im] at h
        linarith
      have hzre : z⁻¹ = ((z⁻¹.re : ℝ) : ℂ) := by
        rw [Complex.ext_iff]
        simp [hrim]
      rcases le_total 0 z⁻¹.re with hge | hlt
      · refine h0 ?_
        rw [hae, hzre, Complex.coe_smul]
        have h2 := smul_le_smul_left' hge (zero_le_one' (𝒜 := 𝒜))
        rwa [smul_zero] at h2
      · refine h0' ?_
        rw [hae, hzre, Complex.coe_smul]
        have h2 := smul_le_smul_left' (r := -z⁻¹.re) (by linarith)
          (zero_le_one' (𝒜 := 𝒜))
        rw [smul_zero, neg_smul] at h2
        have h3 := neg_le_neg h2
        rwa [neg_neg, neg_zero] at h3
    refine ⟨?_, hor⟩
    rcases hor with hpos | hneg
    · exact isUnit_of_one_le_smul hpos hm
    · have hu : IsUnit (-a) := by
        refine isUnit_of_one_le_smul (neg_nonneg.mpr hneg) (m := -m) ?_
        rwa [neg_smul_neg]
      have h := hu.neg
      rwa [neg_neg] at h
  · rintro ⟨hu, hor⟩
    rcases hor with hpos | hneg
    · obtain ⟨n, hn0, hle⟩ := (positive_basic_2_6 a hpos).mp hu
      have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
      refine ⟨0, n, by rw [zero_smul]; exact zero_le_one', ?_⟩
      have h2 := smul_le_smul_left' (le_of_lt hn0') hle
      have he : (n : ℝ) • algebraMap ℂ 𝒜 ((n : ℂ))⁻¹ = (1 : 𝒜) := by
        rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, smul_smul]
        rw [show (((n : ℝ) : ℂ)) = ((n : ℂ)) by push_cast; ring]
        rw [mul_inv_cancel₀ (by exact_mod_cast hn0'.ne'), one_smul]
      rwa [he] at h2
    · obtain ⟨n, hn0, hle⟩ :=
        (positive_basic_2_6 (-a) (neg_nonneg.mpr hneg)).mp hu.neg
      have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
      refine ⟨0, -n, by rw [zero_smul]; exact zero_le_one', ?_⟩
      have h2 := smul_le_smul_left' (le_of_lt hn0') hle
      have he : (n : ℝ) • algebraMap ℂ 𝒜 ((n : ℂ))⁻¹ = (1 : 𝒜) := by
        rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, smul_smul]
        rw [show (((n : ℝ) : ℂ)) = ((n : ℂ)) by push_cast; ring]
        rw [mul_inv_cancel₀ (by exact_mod_cast hn0'.ne'), one_smul]
      rw [he] at h2
      rwa [smul_neg, ← neg_smul] at h2

/-- **22III** (`order-ideal-basic`, cstar.tex:3324, Exercise), part 4: every
non-invertible self-adjoint element lies in some maximal order ideal. -/
theorem order_ideal_basic_4 (a : 𝒜) (ha : IsSelfAdjoint a) (hu : ¬IsUnit a) :
    ∃ J : Submodule ℂ 𝒜, IsMaximalOrderIdeal J ∧ a ∈ J := by
  have hproper : IsProperOrderIdeal (orderIdealGen a) := by
    refine ⟨orderIdealGen_isOrderIdeal, fun h1 => ?_⟩
    exact hu ((order_ideal_basic_3c a ha (orderIdealGen a)
      orderIdealGen_isOrderIdeal (self_mem_orderIdealGen ha)
      (fun J hJ haJ => orderIdealGen_least J hJ haJ)).mp h1).1
  obtain ⟨J, hJmax, hJle⟩ := order_ideal_basic_2 _ hproper
  exact ⟨J, hJmax, hJle (self_mem_orderIdealGen ha)⟩

/-- Auxiliary for **22III**.5: in a C*-algebra `≠ {0}` the spectral radius of
a self-adjoint `a` is attained, so `‖a‖` or `-‖a‖` lies in `spec(a)`.

Derived from the thesis's own ingredients — non-emptiness of the spectrum
(**16V**), compactness, `‖a‖ = sup |spec(a)|` (**16III**) and the reality of
`spec(a)` (**11XV**.1) — rather than from Mathlib's
`CStarAlgebra.norm_or_neg_norm_mem_spectrum`, which rests on the continuous
functional calculus and so would import parsec-280 content into parsec 220. -/
private theorem norm_or_neg_norm_mem_spectrum' [Nontrivial 𝒜] (a : 𝒜)
    (ha : IsSelfAdjoint a) :
    ((‖a‖ : ℝ) : ℂ) ∈ spectrum ℂ a ∨ ((-‖a‖ : ℝ) : ℂ) ∈ spectrum ℂ a :=
  by
    obtain ⟨z, hz, hzr⟩ :=
      spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum_nonempty a ha)
    rw [ha.spectralRadius_eq_nnnorm, ENNReal.coe_inj] at hzr
    have hz' : ‖z‖ = ‖a‖ := congrArg NNReal.toReal hzr
    have hre : z = (z.re : ℂ) := ha.mem_spectrum_eq_re hz
    have habs : |z.re| = ‖a‖ := by
      rw [← hz']
      conv_rhs => rw [hre]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rcases abs_eq (norm_nonneg a) |>.mp habs with h | h
    · exact Or.inl (by rwa [← h, ← hre])
    · exact Or.inr (by rwa [← h, ← hre])

/-- **22III** (`order-ideal-basic`, cstar.tex:3324, Exercise), part 5: for
self-adjoint `a` in a C*-algebra `≠ {0}`, `‖a‖ - a` or `‖a‖ + a` is not
invertible.

The hypothesis `𝒜 ≠ {0}` — here `[Nontrivial 𝒜]` — is **erratum 220.30**; in
the trivial C*-algebra every element is invertible, so both disjuncts fail.
The corrected solution cites **16V** for the non-emptiness of `spec(a)`,
which is exactly where the hypothesis is used below. -/
theorem order_ideal_basic_5 [Nontrivial 𝒜] (a : 𝒜) (ha : IsSelfAdjoint a) :
    ¬IsUnit (algebraMap ℂ 𝒜 (‖a‖ : ℂ) - a) ∨
      ¬IsUnit (algebraMap ℂ 𝒜 (‖a‖ : ℂ) + a) :=
  by
    rcases norm_or_neg_norm_mem_spectrum' a ha with h | h
    · exact Or.inl (spectrum.mem_iff.mp h)
    · refine Or.inr ?_
      have he : algebraMap ℂ 𝒜 (‖a‖ : ℂ) + a
          = -(algebraMap ℂ 𝒜 ((-‖a‖ : ℝ) : ℂ) - a) := by
        rw [Complex.ofReal_neg, map_neg]; abel
      rw [he, IsUnit.neg_iff]
      exact spectrum.mem_iff.mp h

/-! ### 22IV: every maximal order ideal is the kernel of a state -/

/-- `x ≼ y` modulo the order ideal `I`: `q x ≤ q y` in the quotient order
from the thesis's proof of **22IV** (cstar.tex:3374). -/
private def QLe (I : Submodule ℂ 𝒜) (x y : 𝒜) : Prop :=
  ∃ c : 𝒜, 0 ≤ c ∧ y - x - c ∈ I

private theorem QLe.of_le {I : Submodule ℂ 𝒜} {x y : 𝒜} (h : x ≤ y) :
    QLe I x y :=
  ⟨y - x, sub_nonneg.mpr h, by rw [sub_self]; exact I.zero_mem⟩

private theorem QLe.refl (I : Submodule ℂ 𝒜) (x : 𝒜) : QLe I x x :=
  QLe.of_le le_rfl

private theorem QLe.trans {I : Submodule ℂ 𝒜} {x y z : 𝒜} (h1 : QLe I x y)
    (h2 : QLe I y z) : QLe I x z := by
  obtain ⟨c1, hc1, hm1⟩ := h1
  obtain ⟨c2, hc2, hm2⟩ := h2
  refine ⟨c1 + c2, add_nonneg hc1 hc2, ?_⟩
  have h := I.add_mem hm1 hm2
  have he : y - x - c1 + (z - y - c2) = z - x - (c1 + c2) := by abel
  rwa [he] at h

private theorem QLe.add {I : Submodule ℂ 𝒜} {x y x' y' : 𝒜} (h : QLe I x y)
    (h' : QLe I x' y') : QLe I (x + x') (y + y') := by
  obtain ⟨c, hc, hm⟩ := h
  obtain ⟨c', hc', hm'⟩ := h'
  refine ⟨c + c', add_nonneg hc hc', ?_⟩
  have hs := I.add_mem hm hm'
  have he : y - x - c + (y' - x' - c') = y + y' - (x + x') - (c + c') := by
    abel
  rwa [he] at hs

private theorem QLe.add_right {I : Submodule ℂ 𝒜} {x y : 𝒜} (h : QLe I x y)
    (z : 𝒜) : QLe I (x + z) (y + z) :=
  h.add (QLe.refl I z)

private theorem QLe.neg {I : Submodule ℂ 𝒜} {x y : 𝒜} (h : QLe I x y) :
    QLe I (-y) (-x) := by
  obtain ⟨c, hc, hm⟩ := h
  refine ⟨c, hc, ?_⟩
  have he : -x - -y - c = y - x - c := by abel
  rwa [he]

private theorem QLe.rsmul {I : Submodule ℂ 𝒜} {x y : 𝒜} {r : ℝ} (hr : 0 ≤ r)
    (h : QLe I x y) : QLe I (r • x) (r • y) := by
  obtain ⟨c, hc, hm⟩ := h
  refine ⟨r • c, ?_, ?_⟩
  · have h1 := ofReal_smul_nonneg hc hr
    rwa [Complex.coe_smul] at h1
  · have h1 := I.smul_mem (((r : ℝ) : ℂ)) hm
    rw [Complex.coe_smul] at h1
    have he : r • (y - x - c) = r • y - r • x - r • c := by
      rw [smul_sub, smul_sub]
    rwa [he] at h1

private theorem QLe.mem_of_antisymm {I : Submodule ℂ 𝒜} (hI : IsOrderIdeal I)
    {x y : 𝒜} (h1 : QLe I x y) (h2 : QLe I y x) : y - x ∈ I := by
  obtain ⟨c1, hc1, hm1⟩ := h1
  obtain ⟨c2, hc2, hm2⟩ := h2
  have hsum := I.add_mem hm1 hm2
  have he : y - x - c1 + (x - y - c2) = -(c1 + c2) := by abel
  rw [he] at hsum
  have hcsum : c1 + c2 ∈ I := by
    have h := I.neg_mem hsum
    rwa [neg_neg] at h
  have hc1I : c1 ∈ I :=
    hI.mem_of_mem_interval _ hcsum (add_nonneg hc1 hc2) _
      (le_trans (neg_nonpos_of_nonneg (add_nonneg hc1 hc2)) hc1)
      (le_add_of_nonneg_right hc2)
  have h := I.add_mem hm1 hc1I
  rwa [sub_add_cancel''] at h

private theorem smul_one_le_smul_one {r s : ℝ} (h : r ≤ s) :
    r • (1 : 𝒜) ≤ s • (1 : 𝒜) := by
  have h1 : (0 : 𝒜) ≤ (s - r) • 1 := by
    rw [← Complex.coe_smul]
    exact ofReal_smul_nonneg zero_le_one' (by linarith)
  rw [sub_smul] at h1
  exact sub_nonneg.mp h1

private theorem QLe.scalar_le {I : Submodule ℂ 𝒜} (hI : IsOrderIdeal I)
    (h1I : (1 : 𝒜) ∉ I) {r s : ℝ}
    (h : QLe I (r • (1 : 𝒜)) (s • (1 : 𝒜))) : r ≤ s := by
  by_contra hlt
  push_neg at hlt
  have h2 : QLe I (s • (1 : 𝒜)) (r • (1 : 𝒜)) :=
    QLe.of_le (smul_one_le_smul_one (le_of_lt hlt))
  have hmem := QLe.mem_of_antisymm hI h h2
  have hmem' : ((s - r : ℝ) : ℂ) • (1 : 𝒜) ∈ I := by
    rw [Complex.coe_smul, sub_smul]
    exact hmem
  have h1' := I.smul_mem (((s - r : ℝ) : ℂ))⁻¹ hmem'
  rw [smul_smul, inv_mul_cancel₀, one_smul] at h1'
  · exact h1I h1'
  · exact_mod_cast sub_ne_zero.mpr (ne_of_lt hlt)

private theorem smul_one_eq_algebraMap (r : ℝ) :
    r • (1 : 𝒜) = algebraMap ℂ 𝒜 ((r : ℝ) : ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]

/-- The order ideal `J` from the proof of **22IV** (cstar.tex:3395):
elements whose real and imaginary parts are `≼`-sandwiched between real
multiples of `d` modulo `I`. -/
private def qSandwiched (I : Submodule ℂ 𝒜) (d : 𝒜) : Set 𝒜 :=
  {x | ∃ lam mu : ℝ, QLe I (lam • d) x ∧ QLe I x (mu • d)}

private theorem qSandwiched_zero (I : Submodule ℂ 𝒜) (d : 𝒜) :
    (0 : 𝒜) ∈ qSandwiched I d :=
  ⟨0, 0, by rw [zero_smul]; exact QLe.refl I 0,
    by rw [zero_smul]; exact QLe.refl I 0⟩

private theorem qSandwiched_add {I : Submodule ℂ 𝒜} {d x y : 𝒜}
    (hx : x ∈ qSandwiched I d) (hy : y ∈ qSandwiched I d) :
    x + y ∈ qSandwiched I d := by
  obtain ⟨l1, m1, hl1, hm1⟩ := hx
  obtain ⟨l2, m2, hl2, hm2⟩ := hy
  exact ⟨l1 + l2, m1 + m2, by rw [add_smul]; exact hl1.add hl2,
    by rw [add_smul]; exact hm1.add hm2⟩

private theorem qSandwiched_neg {I : Submodule ℂ 𝒜} {d x : 𝒜}
    (hx : x ∈ qSandwiched I d) : -x ∈ qSandwiched I d := by
  obtain ⟨l, m, hl, hm⟩ := hx
  exact ⟨-m, -l, by rw [neg_smul]; exact hm.neg,
    by rw [neg_smul]; exact hl.neg⟩

private theorem qSandwiched_real_smul {I : Submodule ℂ 𝒜} {d x : 𝒜} (r : ℝ)
    (hx : x ∈ qSandwiched I d) : r • x ∈ qSandwiched I d := by
  rcases le_total 0 r with hr | hr
  · obtain ⟨l, m, hl, hm⟩ := hx
    exact ⟨r * l, r * m, by rw [mul_smul]; exact hl.rsmul hr,
      by rw [mul_smul]; exact hm.rsmul hr⟩
  · obtain ⟨l, m, hl, hm⟩ := qSandwiched_neg hx
    have hr' : (0 : ℝ) ≤ -r := by linarith
    refine ⟨-r * l, -r * m, ?_, ?_⟩
    · rw [mul_smul, ← neg_smul_neg r x]
      exact hl.rsmul hr'
    · rw [mul_smul, ← neg_smul_neg r x]
      exact hm.rsmul hr'

private def qIdeal (I : Submodule ℂ 𝒜) (d : 𝒜) : Submodule ℂ 𝒜 where
  carrier := {b | ((ℜ b : 𝒜) ∈ qSandwiched I d) ∧ ((ℑ b : 𝒜) ∈ qSandwiched I d)}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero, ZeroMemClass.coe_zero]
    exact ⟨qSandwiched_zero I d, qSandwiched_zero I d⟩
  add_mem' := by
    rintro b c ⟨hbr, hbi⟩ ⟨hcr, hci⟩
    constructor
    · rw [map_add, AddSubgroup.coe_add]
      exact qSandwiched_add hbr hcr
    · rw [map_add, AddSubgroup.coe_add]
      exact qSandwiched_add hbi hci
  smul_mem' := by
    rintro z b ⟨hbr, hbi⟩
    constructor
    · rw [realPart_smul]
      have he : ((z.re • ℜ b - z.im • ℑ b : selfAdjoint 𝒜) : 𝒜)
          = z.re • (ℜ b : 𝒜) + -(z.im • (ℑ b : 𝒜)) := by
        rw [AddSubgroup.coe_sub, selfAdjoint.val_smul, selfAdjoint.val_smul,
          sub_eq_add_neg]
      rw [he]
      exact qSandwiched_add (qSandwiched_real_smul _ hbr)
        (qSandwiched_neg (qSandwiched_real_smul _ hbi))
    · rw [imaginaryPart_smul]
      have he : ((z.re • ℑ b + z.im • ℜ b : selfAdjoint 𝒜) : 𝒜)
          = z.re • (ℑ b : 𝒜) + z.im • (ℜ b : 𝒜) := by
        rw [AddSubgroup.coe_add, selfAdjoint.val_smul, selfAdjoint.val_smul]
      rw [he]
      exact qSandwiched_add (qSandwiched_real_smul _ hbi)
        (qSandwiched_real_smul _ hbr)

private theorem qIdeal_isOrderIdeal {I : Submodule ℂ 𝒜} {d : 𝒜} :
    IsOrderIdeal (qIdeal I d) := by
  constructor
  · intro b hb
    obtain ⟨hbr, hbi⟩ := hb
    constructor
    · have h : (ℜ (star b) : 𝒜) = (ℜ b : 𝒜) := by
        rw [realPart_apply_coe, realPart_apply_coe, star_star, add_comm]
      rw [h]
      exact hbr
    · have h : (ℑ (star b) : 𝒜) = -(ℑ b : 𝒜) := by
        rw [imaginaryPart_apply_coe, imaginaryPart_apply_coe, star_star,
          ← smul_neg, ← smul_neg, neg_sub]
      rw [h]
      exact qSandwiched_neg hbi
  · intro b hb hb0 c h1 h2
    have hcsa : IsSelfAdjoint c := isSelfAdjoint_of_mem_interval h1 h2
    have hbsa : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg hb0
    obtain ⟨hbr, hbi⟩ := hb
    rw [hbsa.coe_realPart] at hbr
    obtain ⟨l, m, hl, hm⟩ := hbr
    constructor
    · rw [hcsa.coe_realPart]
      refine ⟨-m, m, ?_, (QLe.of_le h2).trans hm⟩
      rw [neg_smul]
      exact hm.neg.trans (QLe.of_le h1)
    · rw [hcsa.imaginaryPart, ZeroMemClass.coe_zero]
      exact qSandwiched_zero I d

private theorem mem_qSandwiched_of_mem {I : Submodule ℂ 𝒜} {d x : 𝒜}
    (hx : x ∈ I) : x ∈ qSandwiched I d := by
  refine ⟨0, 0, ⟨0, le_rfl, ?_⟩, ⟨0, le_rfl, ?_⟩⟩
  · rw [zero_smul, sub_zero, sub_zero]
    exact hx
  · rw [zero_smul, zero_sub, sub_zero]
    exact I.neg_mem hx
  -- note: first goal is `x - 0 • d - 0 ∈ I`, second `0 • d - x - 0 ∈ I`

private theorem le_qIdeal {I : Submodule ℂ 𝒜} (hI : IsOrderIdeal I) {d : 𝒜} :
    I ≤ qIdeal I d := by
  intro b hb
  have hstar : star b ∈ I := hI.star_mem b hb
  have hre : (ℜ b : 𝒜) ∈ I := by
    rw [realPart_apply_coe]
    have h := I.smul_mem (((2 : ℝ)⁻¹ : ℝ) : ℂ) (I.add_mem hb hstar)
    rwa [Complex.coe_smul] at h
  have him : (ℑ b : 𝒜) ∈ I := by
    rw [imaginaryPart_apply_coe]
    have h := I.smul_mem (-Complex.I)
      (I.smul_mem ((((2 : ℝ)⁻¹ : ℝ)) : ℂ) (I.sub_mem hb hstar))
    rwa [Complex.coe_smul] at h
  exact ⟨mem_qSandwiched_of_mem hre, mem_qSandwiched_of_mem him⟩

private theorem d_mem_qIdeal {I : Submodule ℂ 𝒜} {d : 𝒜}
    (hd : IsSelfAdjoint d) : d ∈ qIdeal I d := by
  constructor
  · rw [hd.coe_realPart]
    exact ⟨1, 1, by rw [one_smul]; exact QLe.refl I d,
      by rw [one_smul]; exact QLe.refl I d⟩
  · rw [hd.imaginaryPart, ZeroMemClass.coe_zero]
    exact qSandwiched_zero I d

/-- **22IV** (`maximal-ideal-state`, cstar.tex:3367, Lemma): for every
maximal order ideal `I` of a C*-algebra `𝒜` there is a state `ω : 𝒜 → ℂ`
with `ker(ω) = I`. -/
theorem maximal_ideal_state (I : Submodule ℂ 𝒜) (hI : IsMaximalOrderIdeal I) :
    ∃ ω : 𝒜 →ₗ[ℂ] ℂ, IsState ω ∧ LinearMap.ker ω = I := by
  obtain ⟨⟨hord, h1I⟩, hmax⟩ := hI
  -- Step A (`pos-hahn-banach-1`, cstar.tex:3390): for self-adjoint `a`
  -- there is a real `α` with `a - α•1 ∈ I`.
  have hkey : ∀ a : 𝒜, IsSelfAdjoint a → ∃ r : ℝ, a - r • (1 : 𝒜) ∈ I := by
    intro a ha
    set S : Set ℝ := {lam | QLe I a (lam • (1 : 𝒜))} with hS
    have hup : a ≤ ‖a‖ • (1 : 𝒜) := by
      rw [smul_one_eq_algebraMap]
      exact ((positive_basic_2_3a a ha ‖a‖ (norm_nonneg a)).mpr le_rfl).2
    have hlow : -(‖a‖ • (1 : 𝒜)) ≤ a := by
      rw [smul_one_eq_algebraMap]
      exact ((positive_basic_2_3a a ha ‖a‖ (norm_nonneg a)).mpr le_rfl).1
    have hSne : S.Nonempty := ⟨‖a‖, QLe.of_le hup⟩
    have hSbdd : BddBelow S := by
      refine ⟨-‖a‖, fun lam hlam => ?_⟩
      refine QLe.scalar_le hord h1I (r := -‖a‖) (s := lam) ?_
      refine QLe.trans (QLe.of_le ?_) hlam
      rw [neg_smul]
      exact hlow
    set α := sInf S with hα
    have hqle : ∀ ε : ℝ, 0 < ε → QLe I a ((α + ε) • (1 : 𝒜)) := by
      intro ε hε
      obtain ⟨lam, hlamS, hlt⟩ :=
        exists_lt_of_csInf_lt hSne (show α < α + ε by linarith)
      exact QLe.trans hlamS (QLe.of_le (smul_one_le_smul_one (le_of_lt hlt)))
    set d : 𝒜 := α • (1 : 𝒜) - a with hd
    have hdsa : IsSelfAdjoint d := by
      rw [hd, smul_one_eq_algebraMap]
      exact (isSelfAdjoint_algebraMap_ofReal α).sub ha
    have h1J : (1 : 𝒜) ∉ qIdeal I d := by
      rintro ⟨h1r, -⟩
      rw [(IsSelfAdjoint.one 𝒜).coe_realPart] at h1r
      obtain ⟨l, m, -, hm⟩ := h1r
      rcases lt_trichotomy m 0 with hlt | heq | hgt
      · -- μ < 0 (cstar.tex:3407)
        set s : ℝ := (-m)⁻¹ with hs
        have hspos : 0 < s := inv_pos.mpr (by linarith)
        have h2 := hm.rsmul (le_of_lt hspos)
        have he : s • (m • d) = -d := by
          rw [smul_smul, hs,
            show (-m)⁻¹ * m = -1 by
              field_simp
              rw [div_self (ne_of_lt hlt)],
            neg_one_smul]
        rw [he] at h2
        have he2 : -d = a - α • (1 : 𝒜) := by rw [hd]; abel
        rw [he2] at h2
        have h3 := h2.add_right (α • (1 : 𝒜))
        have he3 : a - α • (1 : 𝒜) + α • (1 : 𝒜) = a := by abel
        have he4 : s • (1 : 𝒜) + α • (1 : 𝒜) = (s + α) • (1 : 𝒜) := by
          rw [add_smul]
        rw [he3, he4] at h3
        have h4 := h3.trans (hqle (s / 2) (by linarith))
        have h5 := QLe.scalar_le hord h1I h4
        linarith
      · -- μ = 0 (cstar.tex:3416)
        rw [heq, zero_smul] at hm
        have h2 : QLe I ((1 : ℝ) • (1 : 𝒜)) ((0 : ℝ) • (1 : 𝒜)) := by
          rw [one_smul, zero_smul]
          exact hm
        have h5 := QLe.scalar_le hord h1I h2
        linarith
      · -- μ > 0 (cstar.tex:3418)
        have h2 := hm.rsmul (le_of_lt (inv_pos.mpr hgt))
        have he : m⁻¹ • (m • d) = d := by
          rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hgt), one_smul]
        rw [he] at h2
        have h3 := h2.add_right (a - m⁻¹ • (1 : 𝒜))
        have he3 : m⁻¹ • (1 : 𝒜) + (a - m⁻¹ • (1 : 𝒜)) = a := by abel
        have he4 : d + (a - m⁻¹ • (1 : 𝒜)) = (α - m⁻¹) • (1 : 𝒜) := by
          rw [hd, sub_smul]
          abel
        rw [he3, he4] at h3
        have hmem : (α - m⁻¹) ∈ S := h3
        have h5 := csInf_le hSbdd hmem
        have hminv : 0 < m⁻¹ := inv_pos.mpr hgt
        linarith
    have heqI := hmax (qIdeal I d) ⟨qIdeal_isOrderIdeal, h1J⟩ (le_qIdeal hord)
    have hdI : d ∈ I := by
      rw [← heqI]
      exact d_mem_qIdeal hdsa
    refine ⟨α, ?_⟩
    have h := I.neg_mem hdI
    have he : -d = a - α • (1 : 𝒜) := by rw [hd]; abel
    rwa [he] at h
  -- Step B: uniqueness of the scalar
  have huniq : ∀ (z w : ℂ) (x : 𝒜),
      x - z • (1 : 𝒜) ∈ I → x - w • (1 : 𝒜) ∈ I → z = w := by
    intro z w x hz hw
    by_contra hne
    have hsub := I.sub_mem hz hw
    have he : x - z • (1 : 𝒜) - (x - w • (1 : 𝒜)) = (w - z) • (1 : 𝒜) := by
      rw [sub_smul]
      abel
    rw [he] at hsub
    have h1' := I.smul_mem (w - z)⁻¹ hsub
    rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hne)),
      one_smul] at h1'
    exact h1I h1'
  -- Step C (cstar.tex:3436): existence of the scalar for every element
  have hex : ∀ a : 𝒜, ∃ z : ℂ, a - z • (1 : 𝒜) ∈ I := by
    intro a
    obtain ⟨r, hr⟩ := hkey _ (ℜ a).property
    obtain ⟨s, hs⟩ := hkey _ (ℑ a).property
    have hr' : (ℜ a : 𝒜) - ((r : ℝ) : ℂ) • (1 : 𝒜) ∈ I := by
      rwa [Complex.coe_smul]
    have hs' : (ℑ a : 𝒜) - ((s : ℝ) : ℂ) • (1 : 𝒜) ∈ I := by
      rwa [Complex.coe_smul]
    refine ⟨(r : ℂ) + (s : ℂ) * Complex.I, ?_⟩
    have hmem := I.add_mem hr' (I.smul_mem Complex.I hs')
    have he : (ℜ a : 𝒜) - ((r : ℝ) : ℂ) • (1 : 𝒜)
        + Complex.I • ((ℑ a : 𝒜) - ((s : ℝ) : ℂ) • (1 : 𝒜))
        = a - ((r : ℂ) + (s : ℂ) * Complex.I) • (1 : 𝒜) := by
      rw [smul_sub, smul_smul, add_smul, mul_comm Complex.I ((s : ℝ) : ℂ)]
      conv_rhs => rw [← realPart_add_I_smul_imaginaryPart a]
      abel
    rwa [he] at hmem
  -- Step D: assemble the state
  choose f hf using hex
  have hadd : ∀ x y : 𝒜, f (x + y) = f x + f y := by
    intro x y
    refine huniq _ _ (x + y) (hf (x + y)) ?_
    have h := I.add_mem (hf x) (hf y)
    have he : x - f x • (1 : 𝒜) + (y - f y • (1 : 𝒜))
        = x + y - (f x + f y) • (1 : 𝒜) := by
      rw [add_smul]
      abel
    rwa [he] at h
  have hsmul : ∀ (z : ℂ) (x : 𝒜), f (z • x) = z * f x := by
    intro z x
    refine huniq _ _ (z • x) (hf (z • x)) ?_
    have h := I.smul_mem z (hf x)
    have he : z • (x - f x • (1 : 𝒜)) = z • x - (z * f x) • (1 : 𝒜) := by
      rw [smul_sub, smul_smul]
    rwa [he] at h
  let ω : 𝒜 →ₗ[ℂ] ℂ :=
    { toFun := f
      map_add' := hadd
      map_smul' := fun z x => by rw [hsmul z x]; rfl }
  have hω1 : f 1 = 1 :=
    huniq (f 1) 1 1 (hf 1) (by rw [one_smul, sub_self]; exact I.zero_mem)
  have hpos : ∀ a : 𝒜, 0 ≤ a → 0 ≤ f a := by
    intro a ha0
    have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha0
    have hstar : a - star (f a) • (1 : 𝒜) ∈ I := by
      have h := hord.star_mem _ (hf a)
      rwa [star_sub, hsa.star_eq, star_smul, star_one] at h
    have hreal : star (f a) = f a := huniq _ _ a hstar (hf a)
    have him : (f a).im = 0 := by
      have h := congrArg Complex.im hreal
      rw [Complex.star_def, Complex.conj_im] at h
      linarith
    have hre : 0 ≤ (f a).re := by
      by_contra hlt
      push_neg at hlt
      set r := (f a).re with hr
      have hfa : f a = ((r : ℝ) : ℂ) := by
        rw [Complex.ext_iff]
        simp [him, hr]
      have hb : a - r • (1 : 𝒜) ∈ I := by
        have h := hf a
        rwa [hfa, Complex.coe_smul] at h
      have hb0 : (0 : 𝒜) ≤ (-r) • (1 : 𝒜) := by
        rw [← Complex.coe_smul]
        exact ofReal_smul_nonneg zero_le_one' (by linarith)
      have hble : (-r) • (1 : 𝒜) ≤ a - r • (1 : 𝒜) := by
        rw [neg_smul]
        have h3 : (0 : 𝒜) - r • 1 ≤ a - r • 1 := sub_le_sub_right ha0 _
        rwa [zero_sub] at h3
      have hbpos : (0 : 𝒜) ≤ a - r • (1 : 𝒜) := le_trans hb0 hble
      have hmem := hord.mem_of_mem_interval _ hb hbpos ((-r) • (1 : 𝒜))
        (le_trans (neg_nonpos_of_nonneg hbpos) hb0) hble
      have hmem' : (((-r : ℝ)) : ℂ) • (1 : 𝒜) ∈ I := by
        rw [Complex.coe_smul]
        exact hmem
      have h1' := I.smul_mem ((((-r : ℝ)) : ℂ))⁻¹ hmem'
      rw [smul_smul, inv_mul_cancel₀
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith : (0:ℝ) < -r))),
        one_smul] at h1'
      exact h1I h1'
    rw [Complex.le_def]
    refine ⟨by simpa using hre, by simp [him]⟩
  refine ⟨ω, ⟨fun a ha => hpos a ha, hω1⟩, ?_⟩
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    have h := hf x
    rw [show f x = ω x from rfl, hx, zero_smul, sub_zero] at h
    exact h
  · intro hx
    exact huniq (f x) 0 x (hf x) (by rw [zero_smul, sub_zero]; exact hx)

/-- **22VIII** (`states-order-separating`, cstar.tex:3464, Exercise), part 1:
for every self-adjoint `a` of a C*-algebra `≠ {0}` there is a state `ω` with
`|ω(a)| = ‖a‖`.

The hypothesis `𝒜 ≠ {0}` — here `[Nontrivial 𝒜]` — is **erratum 220.80**: the
trivial C*-algebra has no states at all.  Part 2 below (order separation) is
*not* touched by the erratum; it holds for `{0}` vacuously. -/
theorem states_order_separating_1 [Nontrivial 𝒜] (a : 𝒜)
    (ha : IsSelfAdjoint a) :
    ∃ ω : 𝒜 →ₗ[ℂ] ℂ, IsState ω ∧ ‖ω a‖ = ‖a‖ := by
  have hsan : IsSelfAdjoint (algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ)) :=
    isSelfAdjoint_algebraMap_ofReal ‖a‖
  have hnorm : ∀ ω : 𝒜 →ₗ[ℂ] ℂ, IsState ω →
      ω (algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ)) = ((‖a‖ : ℝ) : ℂ) := by
    intro ω hω
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hω.2, smul_eq_mul, mul_one]
  rcases order_ideal_basic_5 a ha with h | h
  · obtain ⟨J, hJ, hmem⟩ := order_ideal_basic_4 _ (hsan.sub ha) h
    obtain ⟨ω, hω, hker⟩ := maximal_ideal_state J hJ
    refine ⟨ω, hω, ?_⟩
    have h0 : ω (algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ) - a) = 0 := by
      rw [← LinearMap.mem_ker, hker]
      exact hmem
    rw [map_sub, hnorm ω hω, sub_eq_zero] at h0
    rw [← h0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
  · obtain ⟨J, hJ, hmem⟩ := order_ideal_basic_4 _ (hsan.add ha) h
    obtain ⟨ω, hω, hker⟩ := maximal_ideal_state J hJ
    refine ⟨ω, hω, ?_⟩
    have h0 : ω (algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ) + a) = 0 := by
      rw [← LinearMap.mem_ker, hker]
      exact hmem
    rw [map_add, hnorm ω hω] at h0
    have h0' : ω a = -((‖a‖ : ℝ) : ℂ) := eq_neg_of_add_eq_zero_right h0
    rw [h0', norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg a)]

/-- **22VIII** (`states-order-separating`, cstar.tex:3464, Exercise), part 2:
the states of a C*-algebra are order separating. -/
theorem states_order_separating_2 :
    OrderSeparating fun ω : {ω : 𝒜 →ₗ[ℂ] ℂ // IsState ω} =>
      (ω : 𝒜 →ₗ[ℂ] ℂ) := by
  intro a
  constructor
  · intro ha ω
    exact ω.2.1 a ha
  · intro H
    rcases subsingleton_or_nontrivial 𝒜 with hsub | hnt
    · exact le_of_eq (Subsingleton.elim 0 a)
    -- states are involution preserving, so send self-adjoints to reals
    have hsareal : ∀ (ω : 𝒜 →ₗ[ℂ] ℂ), IsState ω → ∀ x : 𝒜,
        IsSelfAdjoint x → (ω x).im = 0 := by
      intro ω hω x hx
      have h := cstar_p_implies_i ω hω.1 x
      rw [hx.star_eq] at h
      have h2 := congrArg Complex.im h
      rw [Complex.star_def, Complex.conj_im] at h2
      linarith
    -- `ℑ a = 0`, using part 1 on `ℑ a`
    have him : (ℑ a : 𝒜) = 0 := by
      obtain ⟨ω, hω, hnorm⟩ :=
        states_order_separating_1 (𝒜 := 𝒜) (ℑ a : 𝒜) (ℑ a).property
      have hωa := H ⟨ω, hω⟩
      have hdec : ω a = ω (ℜ a : 𝒜) + Complex.I * ω (ℑ a : 𝒜) := by
        conv_lhs => rw [← realPart_add_I_smul_imaginaryPart a]
        rw [map_add, map_smul, smul_eq_mul]
      have haim : (ω a).im = 0 := by
        rw [Complex.le_def] at hωa
        simpa using hωa.2.symm
      have hreim : (ω (ℑ a : 𝒜)).re = 0 := by
        have h2 := congrArg Complex.im hdec
        rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          hsareal ω hω _ (ℜ a).property, haim] at h2
        simpa using h2.symm
      have himim : (ω (ℑ a : 𝒜)).im = 0 := hsareal ω hω _ (ℑ a).property
      have hω0 : ω (ℑ a : 𝒜) = 0 := by
        rw [Complex.ext_iff]
        exact ⟨hreim, himim⟩
      have h3 : ‖(ℑ a : 𝒜)‖ = 0 := by
        rw [← hnorm, hω0, norm_zero]
      exact norm_eq_zero.mp h3
    have hasa : IsSelfAdjoint a := by
      have haeq : a = (ℜ a : 𝒜) := by
        conv_lhs => rw [← realPart_add_I_smul_imaginaryPart a]
        rw [him, smul_zero, add_zero]
      rw [haeq]
      exact (ℜ a).property
    -- now the norm argument
    set t := ‖a‖ with ht
    have hx : IsSelfAdjoint (algebraMap ℂ 𝒜 ((t : ℝ) : ℂ) - a) :=
      (isSelfAdjoint_algebraMap_ofReal t).sub hasa
    obtain ⟨ω, hω, hnorm⟩ := states_order_separating_1 (𝒜 := 𝒜) _ hx
    have hval : ω (algebraMap ℂ 𝒜 ((t : ℝ) : ℂ) - a) = ((t : ℝ) : ℂ) - ω a := by
      rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, hω.2, smul_eq_mul,
        mul_one]
    -- ω a is a real number in [0, t]
    have haim : (ω a).im = 0 := hsareal ω hω a hasa
    have hare0 : 0 ≤ (ω a).re := by
      have h := H ⟨ω, hω⟩
      rw [Complex.le_def] at h
      simpa using h.1
    have haret : (ω a).re ≤ t := by
      have hle : a ≤ algebraMap ℂ 𝒜 ((t : ℝ) : ℂ) :=
        ((positive_basic_2_3a a hasa t (norm_nonneg a)).mpr le_rfl).2
      have h2 := hω.1 _ (sub_nonneg.mpr hle)
      rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, hω.2, smul_eq_mul,
        mul_one, Complex.le_def] at h2
      have h3 := h2.1
      simpa using h3
    have hxnorm : ‖algebraMap ℂ 𝒜 ((t : ℝ) : ℂ) - a‖ ≤ t := by
      rw [← hnorm, hval]
      have he : ((t : ℝ) : ℂ) - ω a = (((t - (ω a).re : ℝ)) : ℂ) := by
        rw [Complex.ext_iff]
        simp [haim]
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    exact (nonneg_iff_norm_algebraMap_sub_le a hasa t (norm_nonneg a)
      (by rw [ht]; linarith [norm_nonneg a])).mp hxnorm


end OrderIdeals

/-! ## Parsec 230: the square root -/

section Sqrt

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-! ### Auxiliary development for 23II

Everything in this block follows the thesis's own proof of **23II**
(cstar.tex:3495–3634) and uses nothing beyond parsec 170: the continuous
functional calculus is deliberately *not* used, since **23II** is precisely
what the thesis builds in order to avoid it.

Two small departures from the letter of the thesis, both order-preserving:

* the thesis bounds `‖bₙ - b_N‖` by `qₙ(1) - q_N(1)` using that the
  polynomials `qₙ` have nonnegative coefficients; we instead bound the
  successive differences `‖b_{n+1} - bₙ‖` by `r_{n+1} - rₙ` for the real
  iteration `r₀ = 0`, `r_{n+1} = ½(1 + rₙ²)` by a direct induction.  This
  needs no polynomial algebra and no positivity of coefficients.
* consequently the monotonicity of `b₀ ≤ b₁ ≤ ⋯` (part 2 of **23II**) is
  *not* needed for the existence of the limit, and we derive it after
  `mul_nonneg_of_commute` (the thesis's `square-commuting-monotone`,
  cstar.tex:3573) rather than before.  No circularity is introduced:
  `mul_nonneg_of_commute` rests only on the existence half of the lemma. -/

section SqrtAux

/-- `½·(-)` preserves positivity (`ofReal_smul_nonneg`, i.e. **9X**.1). -/
private theorem half_smul_nonneg {x : 𝒜} (hx : 0 ≤ x) : 0 ≤ (2 : ℂ)⁻¹ • x := by
  have h := ofReal_smul_nonneg hx (r := 1 / 2) (by norm_num)
  have he : (((1 : ℝ) / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  rwa [he] at h

private theorem half_smul_le {x y : 𝒜} (h : x ≤ y) :
    (2 : ℂ)⁻¹ • x ≤ (2 : ℂ)⁻¹ • y := by
  have h2 := half_smul_nonneg (sub_nonneg.mpr h)
  rwa [smul_sub, sub_nonneg] at h2

/-- **17VI**.3a in the form used below: a positive element of norm at most
one is below `1`. -/
private theorem le_one_of_norm_le_one {x : 𝒜} (hsa : IsSelfAdjoint x)
    (h : ‖x‖ ≤ 1) : x ≤ 1 := by
  have h2 := (positive_basic_2_3a x hsa 1 zero_le_one).mpr h
  simpa using h2.2

/-- **17VI**.3c in the form used below. -/
private theorem norm_le_one_of_le_one {x : 𝒜} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ‖x‖ ≤ 1 :=
  le_trans (positive_basic_2_3c x 1 h0 h1) norm_one_le'

private theorem sqrtApproxSeq_nonneg (a : 𝒜) (h0 : 0 ≤ a) (n : ℕ) :
    0 ≤ sqrtApproxSeq a n := by
  induction n with
  | zero => rw [sqrtApproxSeq_zero]
  | succ n ih =>
    rw [sqrtApproxSeq_succ]
    exact half_smul_nonneg
      (add_nonneg h0 (positive_basic_2_4a _ (IsSelfAdjoint.of_nonneg ih)))

/-- The existence half of **23II** (cstar.tex:3495–3570). -/
private theorem sqrt_lemma_exists (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    ∃ b : 𝒜, Tendsto (sqrtApproxSeq a) atTop (𝓝 b) ∧ 0 ≤ b ∧ b ≤ 1 ∧
      (1 - b) ^ 2 = 1 - a ∧ ∀ c : 𝒜, c * a = a * c → c * b = b * c := by
  have ha : ‖a‖ ≤ 1 := norm_le_one_of_le_one h0 h1
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete (sqrtApproxSeq_cauchy a ha)
  refine ⟨b, hb, ?_, ?_, ?_, ?_⟩
  · exact (positive_basic_2_2 (𝒜 := 𝒜)).mem_of_tendsto hb
      (Filter.Eventually.of_forall fun n => sqrtApproxSeq_nonneg a h0 n)
  · have hnb : ‖b‖ ≤ 1 := by
      have hlim : Tendsto (fun n => ‖sqrtApproxSeq a n‖) atTop (𝓝 ‖b‖) := hb.norm
      refine le_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
      exact le_trans (sqrtApproxSeq_norm_le a ha n) (sqrtApproxReal_le_one n)
    refine le_one_of_norm_le_one ?_ hnb
    exact IsSelfAdjoint.of_nonneg ((positive_basic_2_2 (𝒜 := 𝒜)).mem_of_tendsto hb
      (Filter.Eventually.of_forall fun n => sqrtApproxSeq_nonneg a h0 n))
  · have hrec : b = (2 : ℂ)⁻¹ • (a + b ^ 2) := by
      have hl : Tendsto (fun n => sqrtApproxSeq a (n + 1)) atTop (𝓝 b) :=
        hb.comp (Filter.tendsto_add_atTop_nat 1)
      have hr : Tendsto (fun n => sqrtApproxSeq a (n + 1)) atTop
          (𝓝 ((2 : ℂ)⁻¹ • (a + b ^ 2))) := by
        simp only [sqrtApproxSeq_succ]
        exact ((hb.pow 2).const_add a).const_smul _
      exact tendsto_nhds_unique hl hr
    have h2 : a + b ^ 2 = b + b := by
      have h3 : (2 : ℂ) • ((2 : ℂ)⁻¹ • (a + b ^ 2)) = (2 : ℂ) • b := by rw [← hrec]
      have he : (2 : ℂ) * (2 : ℂ)⁻¹ = 1 := by norm_num
      rw [smul_smul, he, one_smul, two_smul] at h3
      exact h3
    have : (1 - b) ^ 2 = 1 - (b + b) + b ^ 2 := by noncomm_ring
    rw [this, ← h2]
    abel
  · intro c hc
    have hl : Tendsto (fun n => c * sqrtApproxSeq a n) atTop (𝓝 (c * b)) :=
      hb.const_mul c
    have hr : Tendsto (fun n => sqrtApproxSeq a n * c) atTop (𝓝 (b * c)) :=
      hb.mul_const c
    refine tendsto_nhds_unique hl ?_
    simpa only [sqrtApproxSeq_commute a c hc] using hr

private theorem smul_sq (r : ℂ) (x : 𝒜) : (r • x) ^ 2 = (r * r) • x ^ 2 := by
  rw [sq, sq, smul_mul_assoc, mul_smul_comm, smul_smul]

private theorem ofReal_smul_le {r : ℝ} (hr : 0 ≤ r) {x y : 𝒜} (h : x ≤ y) :
    ((r : ℝ) : ℂ) • x ≤ ((r : ℝ) : ℂ) • y := by
  have h2 := ofReal_smul_nonneg (sub_nonneg.mpr h) hr
  rwa [smul_sub, sub_nonneg] at h2

private theorem eq_zero_of_sq_eq_zero {x : 𝒜} (hsa : IsSelfAdjoint x)
    (h : x ^ 2 = 0) : x = 0 := by
  have h2 := cstar_involution_basic_13 x hsa
  rw [h, norm_zero] at h2
  have h3 : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp h3

/-- The square root of a positive element of norm at most one, obtained by
applying **23II** to `1 - x` (cstar.tex:3573). -/
private theorem sqrt_unit_exists (x : 𝒜) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ d : 𝒜, 0 ≤ d ∧ d ^ 2 = x ∧ ∀ e : 𝒜, e * x = x * e → e * d = d * e := by
  obtain ⟨b, _, hb0, hb1, hbsq, hbc⟩ :=
    sqrt_lemma_exists (1 - x) (sub_nonneg.mpr hx1) (sub_le_self 1 hx0)
  refine ⟨1 - b, sub_nonneg.mpr hb1, ?_, ?_⟩
  · rw [hbsq]; abel
  · intro e he
    have he' : e * (1 - x) = (1 - x) * e := by
      rw [mul_sub, sub_mul, mul_one, one_mul, he]
    have h := hbc e he'
    rw [mul_sub, sub_mul, mul_one, one_mul, h]

/-- Every positive element has a positive square root commuting with
everything that commutes with it (cstar.tex:3576). -/
private theorem sqrt_exists_core (x : 𝒜) (hx : 0 ≤ x) :
    ∃ d : 𝒜, 0 ≤ d ∧ d ^ 2 = x ∧ ∀ e : 𝒜, e * x = x * e → e * d = d * e := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hs | hs
  · have hx0 : x = 0 := norm_eq_zero.mp hs.symm
    subst hx0
    exact ⟨0, le_rfl, by norm_num, by intro e _; rw [mul_zero, zero_mul]⟩
  · have hsinv : (0 : ℝ) ≤ ‖x‖⁻¹ := by positivity
    have hy0 : 0 ≤ ((‖x‖⁻¹ : ℝ) : ℂ) • x := ofReal_smul_nonneg hx hsinv
    have hyn : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ ≤ 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsinv,
        inv_mul_cancel₀ (ne_of_gt hs)]
    have hy1 : ((‖x‖⁻¹ : ℝ) : ℂ) • x ≤ 1 :=
      le_one_of_norm_le_one (IsSelfAdjoint.of_nonneg hy0) hyn
    obtain ⟨d, hd0, hd2, hdc⟩ := sqrt_unit_exists _ hy0 hy1
    refine ⟨((Real.sqrt ‖x‖ : ℝ) : ℂ) • d,
      ofReal_smul_nonneg hd0 (Real.sqrt_nonneg _), ?_, ?_⟩
    · rw [smul_sq, hd2, ← Complex.ofReal_mul, Real.mul_self_sqrt hs.le, smul_smul,
        ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hs), Complex.ofReal_one,
        one_smul]
    · intro e he
      have he' : e * (((‖x‖⁻¹ : ℝ) : ℂ) • x) = (((‖x‖⁻¹ : ℝ) : ℂ) • x) * e := by
        rw [mul_smul_comm, smul_mul_assoc, he]
      have h := hdc e he'
      rw [mul_smul_comm, smul_mul_assoc, h]

/-- Positive square roots are unique (cstar.tex:3637). -/
private theorem sqrt_unique_core {x s t : 𝒜} (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hs2 : s ^ 2 = x) (ht2 : t ^ 2 = x) (hst : s * t = t * s) : s = t := by
  set v := s - t with hv
  have hvsa : IsSelfAdjoint v :=
    (IsSelfAdjoint.of_nonneg hs0).sub (IsSelfAdjoint.of_nonneg ht0)
  have hvst : v * (s + t) = 0 := by
    rw [hv]
    have he : (s - t) * (s + t) = s ^ 2 - t ^ 2 + (s * t - t * s) := by noncomm_ring
    rw [he, hs2, ht2, hst]
    simp
  have h1 : 0 ≤ v * s * v := by
    have h := star_left_conjugate_nonneg hs0 v
    rwa [hvsa.star_eq] at h
  have h2 : 0 ≤ v * t * v := by
    have h := star_left_conjugate_nonneg ht0 v
    rwa [hvsa.star_eq] at h
  have hsum : v * s * v + v * t * v = 0 := by
    have he : v * s * v + v * t * v = v * (s + t) * v := by noncomm_ring
    rw [he, hvst, zero_mul]
  have h1z : v * s * v = 0 := by
    have heq : v * s * v = -(v * t * v) := by
      rw [eq_neg_iff_add_eq_zero]; exact hsum
    exact le_antisymm (heq ▸ neg_nonpos_of_nonneg h2) h1
  have h2z : v * t * v = 0 := by
    have heq : v * t * v = -(v * s * v) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
    rw [heq, h1z, neg_zero]
  have hv3 : v ^ 3 = 0 := by
    have he : v ^ 3 = v * s * v - v * t * v := by rw [hv]; noncomm_ring
    rw [he, h1z, h2z, sub_zero]
  have hv2 : v ^ 2 = 0 := by
    refine eq_zero_of_sq_eq_zero (hvsa.pow 2) ?_
    have he : (v ^ 2) ^ 2 = v ^ 3 * v := by noncomm_ring
    rw [he, hv3, zero_mul]
  have hv0 : v = 0 := eq_zero_of_sq_eq_zero hvsa hv2
  rw [hv] at hv0
  exact sub_eq_zero.mp hv0

/-- **23II** in the form `square-commuting-monotone` (cstar.tex:3573): the
product of two commuting positive elements is positive. -/
private theorem mul_nonneg_of_commute {x y : 𝒜} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x * y = y * x) : 0 ≤ x * y := by
  obtain ⟨d, hd0, hd2, hdc⟩ := sqrt_exists_core x hx
  obtain ⟨e, he0, he2, hec⟩ := sqrt_exists_core y hy
  have hdy : y * d = d * y := hdc y h.symm
  have hde : Commute d e := hec d hdy.symm
  have hsa : IsSelfAdjoint (d * e) := by
    rw [IsSelfAdjoint, star_mul, (IsSelfAdjoint.of_nonneg he0).star_eq,
      (IsSelfAdjoint.of_nonneg hd0).star_eq, ← hde.eq]
  have hprod : x * y = (d * e) ^ 2 := by
    rw [← hd2, ← he2, hde.mul_pow]
  rw [hprod]
  exact positive_basic_2_4a _ hsa

/-- The corollary of `square-commuting-monotone` (cstar.tex:3588). -/
private theorem sq_le_sq_of_commute {x y : 𝒜} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hcomm : x * y = y * x) (hxy : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  have hd : 0 ≤ y - x := sub_nonneg.mpr hxy
  have h1 : 0 ≤ y * (y - x) :=
    mul_nonneg_of_commute hy hd (by rw [mul_sub, sub_mul, hcomm])
  have h2 : 0 ≤ (y - x) * x :=
    mul_nonneg_of_commute hd hx (by rw [sub_mul, mul_sub, hcomm])
  have hid : y ^ 2 - x ^ 2 = y * (y - x) + (y - x) * x := by noncomm_ring
  have h3 := add_nonneg h1 h2
  rw [← hid, sub_nonneg] at h3
  exact h3

/-- **23II**, the inequality of `ineq-square-root` (cstar.tex:3595). -/
private theorem sqrt_lemma_le (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 1) (b : 𝒜)
    (hlim : Tendsto (sqrtApproxSeq a) atTop (𝓝 b)) (c : 𝒜) (hcsa : IsSelfAdjoint c)
    (hca : c * a = a * c) (hc2 : c ^ 2 ≤ 1 - a) : c ≤ 1 - b := by
  have hc2pos : 0 ≤ c ^ 2 := positive_basic_2_4a c hcsa
  have h1a0 : (0 : 𝒜) ≤ 1 - a := sub_nonneg.mpr h1
  have hn1a : ‖(1 : 𝒜) - a‖ ≤ 1 := norm_le_one_of_le_one h1a0 (sub_le_self 1 h0)
  have hcn : ‖c‖ ≤ 1 := by
    have h := positive_basic_2_3c (c ^ 2) (1 - a) hc2pos hc2
    rw [cstar_involution_basic_13 c hcsa] at h
    nlinarith [norm_nonneg c]
  have hu0 : (0 : 𝒜) ≤ 1 - c := sub_nonneg.mpr (le_one_of_norm_le_one hcsa hcn)
  have hale : a ≤ 1 - c ^ 2 := by
    have h := sub_nonneg.mpr hc2
    have he : (1 - a) - c ^ 2 = (1 - c ^ 2) - a := by abel
    rw [he, sub_nonneg] at h
    exact h
  have hstep : ∀ n, sqrtApproxSeq a n ≤ 1 - c := by
    intro n
    induction n with
    | zero => rw [sqrtApproxSeq_zero]; exact hu0
    | succ n ih =>
      have hbn0 : 0 ≤ sqrtApproxSeq a n := sqrtApproxSeq_nonneg a h0 n
      have hbc : sqrtApproxSeq a n * (1 - c) = (1 - c) * sqrtApproxSeq a n := by
        have h := sqrtApproxSeq_commute a c hca n
        rw [mul_sub, sub_mul, mul_one, one_mul, h]
      have hsq : sqrtApproxSeq a n ^ 2 ≤ (1 - c) ^ 2 :=
        sq_le_sq_of_commute hbn0 hu0 hbc ih
      have hsum := half_smul_le (add_le_add hale hsq)
      have hcalc : (1 : 𝒜) - c ^ 2 + (1 - c) ^ 2 = (1 - c) + (1 - c) := by
        noncomm_ring
      have he : (2 : ℂ)⁻¹ * (2 : ℂ) = 1 := by norm_num
      have hhalf : (2 : ℂ)⁻¹ • ((1 - c) + (1 - c) : 𝒜) = 1 - c := by
        rw [← two_smul ℂ (1 - c : 𝒜), smul_smul, he, one_smul]
      rw [hcalc, hhalf] at hsum
      rw [sqrtApproxSeq_succ]
      exact hsum
  have hcont : Continuous fun x : 𝒜 => 1 - c - x := by fun_prop
  have hset : {x : 𝒜 | x ≤ 1 - c} = (fun x : 𝒜 => 1 - c - x) ⁻¹' {y : 𝒜 | 0 ≤ y} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact (sub_nonneg (a := 1 - c) (b := x)).symm
  have hclosed : IsClosed {x : 𝒜 | x ≤ 1 - c} := by
    rw [hset]; exact (positive_basic_2_2 (𝒜 := 𝒜)).preimage hcont
  have hble : b ≤ 1 - c :=
    hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hstep)
  have h := sub_nonneg.mpr hble
  have he : (1 - c) - b = (1 - b) - c := by abel
  rw [he, sub_nonneg] at h
  exact h

/-- `ineq-square-root` for positive elements of norm at most one. -/
private theorem sqrt_unit_le {x : 𝒜} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {d : 𝒜}
    (hd0 : 0 ≤ d) (hd2 : d ^ 2 = x) {c : 𝒜} (hcsa : IsSelfAdjoint c)
    (hcx : c * x = x * c) (hc2 : c ^ 2 ≤ x) : c ≤ d := by
  obtain ⟨b, hlim, hb0, hb1, hbsq, hbc⟩ :=
    sqrt_lemma_exists (1 - x) (sub_nonneg.mpr hx1) (sub_le_self 1 hx0)
  have hbx : (1 - b) ^ 2 = x := by rw [hbsq]; abel
  have hdx : d * x = x * d := by rw [← hd2, sq, mul_assoc]
  have hd1x : d * (1 - x) = (1 - x) * d := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hdx]
  have hdb : d * (1 - b) = (1 - b) * d := by
    have h := hbc d hd1x
    rw [mul_sub, sub_mul, mul_one, one_mul, h]
  have hdeq : d = 1 - b :=
    sqrt_unique_core hd0 (sub_nonneg.mpr hb1) hd2 hbx hdb
  have hc1x : c * (1 - x) = (1 - x) * c := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hcx]
  have hcle : c ≤ 1 - b := by
    refine sqrt_lemma_le (1 - x) (sub_nonneg.mpr hx1) (sub_le_self 1 hx0) b hlim c
      hcsa hc1x ?_
    have he : (1 : 𝒜) - (1 - x) = x := by abel
    rw [he]; exact hc2
  rw [hdeq]; exact hcle

/-- `ineq-square-root` in general (cstar.tex:3637): if `c` is self-adjoint,
commutes with `x ≥ 0` and `c² ≤ x`, then `c` is below every positive square
root of `x`. -/
private theorem sqrt_le {x : 𝒜} (hx : 0 ≤ x) {d : 𝒜} (hd0 : 0 ≤ d)
    (hd2 : d ^ 2 = x) {c : 𝒜} (hcsa : IsSelfAdjoint c) (hcx : c * x = x * c)
    (hc2 : c ^ 2 ≤ x) : c ≤ d := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hs | hs
  · have hx0 : x = 0 := norm_eq_zero.mp hs.symm
    subst hx0
    have hc0 : c ^ 2 = 0 := le_antisymm hc2 (positive_basic_2_4a c hcsa)
    rw [eq_zero_of_sq_eq_zero hcsa hc0]
    exact hd0
  · have hsq : 0 < Real.sqrt ‖x‖ := Real.sqrt_pos.mpr hs
    have ht0 : (0 : ℝ) ≤ (Real.sqrt ‖x‖)⁻¹ := by positivity
    have hsinv : (0 : ℝ) ≤ ‖x‖⁻¹ := by positivity
    have htt : ((((Real.sqrt ‖x‖)⁻¹ : ℝ) : ℂ)) * ((((Real.sqrt ‖x‖)⁻¹ : ℝ) : ℂ))
        = ((‖x‖⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hs.le]
    have hy0 : 0 ≤ ((‖x‖⁻¹ : ℝ) : ℂ) • x := ofReal_smul_nonneg hx hsinv
    have hyn : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ ≤ 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsinv,
        inv_mul_cancel₀ (ne_of_gt hs)]
    have hy1 : ((‖x‖⁻¹ : ℝ) : ℂ) • x ≤ 1 :=
      le_one_of_norm_le_one (IsSelfAdjoint.of_nonneg hy0) hyn
    have hrsa : IsSelfAdjoint (((Real.sqrt ‖x‖)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
    have hc'sa : IsSelfAdjoint ((((Real.sqrt ‖x‖)⁻¹ : ℝ) : ℂ) • c) := hrsa.smul hcsa
    have hd'0 : 0 ≤ (((Real.sqrt ‖x‖)⁻¹ : ℝ) : ℂ) • d := ofReal_smul_nonneg hd0 ht0
    have hd'2 : ((((Real.sqrt ‖x‖)⁻¹ : ℝ) : ℂ) • d) ^ 2 = ((‖x‖⁻¹ : ℝ) : ℂ) • x := by
      rw [smul_sq, htt, hd2]
    have hc'2 : ((((Real.sqrt ‖x‖)⁻¹ : ℝ) : ℂ) • c) ^ 2 ≤ ((‖x‖⁻¹ : ℝ) : ℂ) • x := by
      rw [smul_sq, htt]
      exact ofReal_smul_le hsinv hc2
    have hc'x : (((Real.sqrt ‖x‖)⁻¹ : ℝ) : ℂ) • c * (((‖x‖⁻¹ : ℝ) : ℂ) • x)
        = ((‖x‖⁻¹ : ℝ) : ℂ) • x * ((((Real.sqrt ‖x‖)⁻¹ : ℝ) : ℂ) • c) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, hcx,
        smul_comm]
    have hstep := sqrt_unit_le hy0 hy1 hd'0 hd'2 hc'sa hc'x hc'2
    have hfin := ofReal_smul_le (Real.sqrt_nonneg ‖x‖) hstep
    have hcancel : ∀ z : 𝒜, ((Real.sqrt ‖x‖ : ℝ) : ℂ) •
        ((((Real.sqrt ‖x‖)⁻¹ : ℝ) : ℂ) • z) = z := by
      intro z
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hsq),
        Complex.ofReal_one, one_smul]
    rw [hcancel, hcancel] at hfin
    exact hfin

/-- The uniqueness half of **23II** (cstar.tex:3616). -/
private theorem sqrt_lemma_unique (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 1) (b : 𝒜)
    (hlim : Tendsto (sqrtApproxSeq a) atTop (𝓝 b)) (hb0 : 0 ≤ b)
    (hbsq : (1 - b) ^ 2 = 1 - a) (b' : 𝒜) (hb'0 : 0 ≤ b') (hb'1 : b' ≤ 1)
    (hb'a : a * b' = b' * a) (hb'sq : (1 - b') ^ 2 = 1 - a) : b = b' := by
  have hb'sa : IsSelfAdjoint b' := IsSelfAdjoint.of_nonneg hb'0
  have hu0 : (0 : 𝒜) ≤ 1 - b' := sub_nonneg.mpr hb'1
  have hle : b ≤ b' := by
    have hsa1 : IsSelfAdjoint (1 - b' : 𝒜) := by
      rw [IsSelfAdjoint, star_sub, star_one, hb'sa.star_eq]
    have h := sqrt_lemma_le a h0 h1 b hlim (1 - b') hsa1
      (by rw [mul_sub, sub_mul, mul_one, one_mul, hb'a]) (le_of_eq hb'sq)
    have h2 := sub_nonneg.mpr h
    have he : (1 - b) - (1 - b') = b' - b := by abel
    rw [he, sub_nonneg] at h2
    exact h2
  have hcomm : b' * b = b * b' := by
    have hl : Tendsto (fun n => b' * sqrtApproxSeq a n) atTop (𝓝 (b' * b)) :=
      hlim.const_mul b'
    have hr : Tendsto (fun n => sqrtApproxSeq a n * b') atTop (𝓝 (b * b')) :=
      hlim.mul_const b'
    refine tendsto_nhds_unique hl ?_
    simpa only [sqrtApproxSeq_commute a b' hb'a.symm] using hr
  have hv0 : (0 : 𝒜) ≤ b' - b := sub_nonneg.mpr hle
  have huv : (1 - b') * (b' - b) = (b' - b) * (1 - b') := by
    have h : (1 - b') * (b' - b) - (b' - b) * (1 - b') = b' * b - b * b' := by
      noncomm_ring
    rw [hcomm, sub_self] at h
    exact sub_eq_zero.mp h
  have huvpos : 0 ≤ (1 - b') * (b' - b) := mul_nonneg_of_commute hu0 hv0 huv
  have hzero : (1 - b') * (b' - b) + (1 - b') * (b' - b) + (b' - b) ^ 2 = 0 := by
    have h : (1 - b') * (b' - b) + (b' - b) * (1 - b') + (b' - b) ^ 2
        = (1 - b) ^ 2 - (1 - b') ^ 2 := by noncomm_ring
    rw [← huv] at h
    rw [h, hbsq, ← hb'sq, sub_self]
  have hvsq : (b' - b) ^ 2 ≤ 0 := by
    have h : (b' - b) ^ 2 = -((1 - b') * (b' - b) + (1 - b') * (b' - b)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hzero
    rw [h]
    exact neg_nonpos_of_nonneg (add_nonneg huvpos huvpos)
  have hvsq0 : (b' - b) ^ 2 = 0 :=
    le_antisymm hvsq
      (positive_basic_2_4a _ (IsSelfAdjoint.of_nonneg hv0))
  have := eq_zero_of_sq_eq_zero (IsSelfAdjoint.of_nonneg hv0) hvsq0
  exact (sub_eq_zero.mp this).symm

end SqrtAux

/-- **23II** (cstar.tex:3485, Lemma), part 1: for `0 ≤ a ≤ 1` there is a
unique `b` with `0 ≤ b ≤ 1`, `ab = ba` and `(1-b)² = 1-a`. -/
theorem sqrt_lemma_existsUnique (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    ∃! b : 𝒜, 0 ≤ b ∧ b ≤ 1 ∧ a * b = b * a ∧ (1 - b) ^ 2 = 1 - a :=
  by
    obtain ⟨b, hlim, hb0, hb1, hbsq, hbc⟩ := sqrt_lemma_exists a h0 h1
    refine ⟨b, ⟨hb0, hb1, hbc a rfl, hbsq⟩, ?_⟩
    rintro b' ⟨hb'0, hb'1, hb'a, hb'sq⟩
    exact (sqrt_lemma_unique a h0 h1 b hlim hb0 hbsq b' hb'0 hb'1 hb'a hb'sq).symm

/-- **23II** (cstar.tex:3485, Lemma), part 2: the sequence
`b₀ ≤ b₁ ≤ ⋯` given by `b₀ = 0`, `b_{n+1} = ½(a + bₙ²)` is monotone. -/
theorem sqrt_lemma_monotone (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    Monotone (sqrtApproxSeq a) :=
  by
    refine monotone_nat_of_le_succ fun n => ?_
    induction n with
    | zero =>
      rw [sqrtApproxSeq_zero, sqrtApproxSeq_succ, sqrtApproxSeq_zero]
      have hz : (a + (0 : 𝒜) ^ 2) = a := by norm_num
      rw [hz]
      exact half_smul_nonneg h0
    | succ n ih =>
      have hb1 := sqrtApproxSeq_nonneg a h0 (n + 1)
      have hbn := sqrtApproxSeq_nonneg a h0 n
      have hd : 0 ≤ sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n := sub_nonneg.mpr ih
      have hcomm : sqrtApproxSeq a (n + 1) * sqrtApproxSeq a n
          = sqrtApproxSeq a n * sqrtApproxSeq a (n + 1) :=
        sqrtApproxSeq_self_commute a (n + 1) n
      have h1' : 0 ≤ sqrtApproxSeq a (n + 1) *
          (sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n) :=
        mul_nonneg_of_commute hb1 hd (by rw [mul_sub, sub_mul, hcomm])
      have h2' : 0 ≤ (sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n) *
          sqrtApproxSeq a n :=
        mul_nonneg_of_commute hd hbn (by rw [sub_mul, mul_sub, hcomm])
      have hkey : sqrtApproxSeq a (n + 2) - sqrtApproxSeq a (n + 1)
          = (2 : ℂ)⁻¹ • (sqrtApproxSeq a (n + 1) *
              (sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n)
            + (sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n) * sqrtApproxSeq a n) := by
        rw [sqrtApproxSeq_succ a (n + 1), sqrtApproxSeq_succ a n, ← smul_sub]
        congr 1
        noncomm_ring
      have h3 := half_smul_nonneg (add_nonneg h1' h2')
      rw [← hkey, sub_nonneg] at h3
      exact h3

/-- **23II** (cstar.tex:3485, Lemma), part 3: the `b` of
`sqrt_lemma_existsUnique` is the norm limit of the sequence `(bₙ)ₙ`. -/
theorem sqrt_lemma_tendsto (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 1) (b : 𝒜)
    (hb : 0 ≤ b ∧ b ≤ 1 ∧ a * b = b * a ∧ (1 - b) ^ 2 = 1 - a) :
    Tendsto (sqrtApproxSeq a) atTop (𝓝 b) :=
  by
    obtain ⟨b₀, hlim, hb₀0, _, hb₀sq, _⟩ := sqrt_lemma_exists a h0 h1
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    rwa [sqrt_lemma_unique a h0 h1 b₀ hlim hb₀0 hb₀sq b hb1 hb2 hb3 hb4] at hlim

/-- **23II** (cstar.tex:3485, Lemma), part 4: any `c` commuting with `a`
commutes with `b`; and if moreover `c* = c` and `c² ≤ 1 - a`, then
`c ≤ 1 - b`. -/
theorem sqrt_lemma_commute (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 1) (b : 𝒜)
    (hb : 0 ≤ b ∧ b ≤ 1 ∧ a * b = b * a ∧ (1 - b) ^ 2 = 1 - a) (c : 𝒜)
    (hc : c * a = a * c) :
    c * b = b * c ∧ (IsSelfAdjoint c → c ^ 2 ≤ 1 - a → c ≤ 1 - b) :=
  by
    have hlim : Tendsto (sqrtApproxSeq a) atTop (𝓝 b) := sqrt_lemma_tendsto a h0 h1 b hb
    refine ⟨?_, fun hcsa hc2 => sqrt_lemma_le a h0 h1 b hlim c hcsa hc hc2⟩
    have hl : Tendsto (fun n => c * sqrtApproxSeq a n) atTop (𝓝 (c * b)) :=
      hlim.const_mul c
    have hr : Tendsto (fun n => sqrtApproxSeq a n * c) atTop (𝓝 (b * c)) :=
      hlim.mul_const c
    refine tendsto_nhds_unique hl ?_
    simpa only [sqrtApproxSeq_commute a c hc] using hr

/-- **23VII** (`sqrt`, cstar.tex:3637, Exercise), part 0 (existence and
uniqueness): every positive `a` has a unique positive square root commuting
with `a`.  (Mathlib's square root via the continuous functional calculus is
`CFC.sqrt a`.) -/
theorem sqrt_existsUnique (a : 𝒜) (ha : 0 ≤ a) :
    ∃! s : 𝒜, 0 ≤ s ∧ s ^ 2 = a ∧ a * s = s * a :=
  by
    obtain ⟨d, hd0, hd2, hdc⟩ := sqrt_exists_core a ha
    refine ⟨d, ⟨hd0, hd2, hdc a rfl⟩, ?_⟩
    rintro s ⟨hs0, hs2, hsa⟩
    exact sqrt_unique_core hs0 hd0 hs2 hd2 (hdc s hsa.symm)

/-- **23VII** (`sqrt`, cstar.tex:3637, Exercise), part 0': Mathlib's
`CFC.sqrt a` is such a square root. -/
theorem sqrt_spec (a : 𝒜) (ha : 0 ≤ a) :
    0 ≤ CFC.sqrt a ∧ CFC.sqrt a ^ 2 = a ∧ a * CFC.sqrt a = CFC.sqrt a * a :=
  by
    have h2 := CFC.sq_sqrt a ha
    refine ⟨CFC.sqrt_nonneg a, h2, ?_⟩
    calc a * CFC.sqrt a = CFC.sqrt a ^ 2 * CFC.sqrt a := by rw [h2]
      _ = CFC.sqrt a * CFC.sqrt a ^ 2 := pow_mul_comm' _ 2
      _ = CFC.sqrt a * a := by rw [h2]

/-- **23VII** (`sqrt`, cstar.tex:3637, Exercise), part 0'': if `c` commutes
with `a ≥ 0` then `c` commutes with `√a`; if in addition `c* = c` and
`c² ≤ a`, then `c ≤ √a`. -/
theorem sqrt_commute (a : 𝒜) (ha : 0 ≤ a) (c : 𝒜) (hc : c * a = a * c) :
    c * CFC.sqrt a = CFC.sqrt a * c ∧
      (IsSelfAdjoint c → c ^ 2 ≤ a → c ≤ CFC.sqrt a) :=
  by
    -- The thesis's square root of `a` (**23II**); the only role Mathlib's
    -- continuous functional calculus plays here is to identify `CFC.sqrt a`
    -- with it, which the *statement* forces.  In particular `CFC.sqrt_le_sqrt`
    -- (the monotonicity of `√`, which is **28III**, cstar.tex:4353, five
    -- parsecs later and itself resting on this very exercise) is not used.
    obtain ⟨d, hd0, hd2, hdc⟩ := sqrt_exists_core a ha
    have hs2 : CFC.sqrt a ^ 2 = a := CFC.sq_sqrt a ha
    have hsa : CFC.sqrt a * a = a * CFC.sqrt a := by
      calc CFC.sqrt a * a = CFC.sqrt a * CFC.sqrt a ^ 2 := by rw [hs2]
        _ = CFC.sqrt a ^ 2 * CFC.sqrt a := by rw [sq, mul_assoc]
        _ = a * CFC.sqrt a := by rw [hs2]
    have hcfc : d = CFC.sqrt a :=
      sqrt_unique_core hd0 (CFC.sqrt_nonneg a) hd2 hs2 (hdc _ hsa).symm
    rw [← hcfc]
    exact ⟨hdc c hc, fun hcsa hle => sqrt_le ha hd0 hd2 hcsa hc hle⟩

/-- **23VII** (`sqrt`, cstar.tex:3637, Exercise), part 1: the product of
commuting positive elements is positive. -/
theorem sqrt_1 (a b : 𝒜) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = b * a) :
    0 ≤ a * b :=
  mul_nonneg_of_commute ha hb hab

/-- **23VII** (`sqrt`, cstar.tex:3637, Exercise), part 2: for `a ≥ 0` and
self-adjoint `b, c` commuting with `a`: `b ≤ c` implies `ab ≤ ac`. -/
theorem sqrt_2 (a : 𝒜) (ha : 0 ≤ a) (b c : 𝒜) (hb : IsSelfAdjoint b)
    (hc : IsSelfAdjoint c) (hba : b * a = a * b) (hca : c * a = a * c)
    (hbc : b ≤ c) : a * b ≤ a * c :=
  by
    have hcomm : a * (c - b) = (c - b) * a := by
      rw [mul_sub, sub_mul, hba, hca]
    have h := mul_nonneg_of_commute ha (sub_nonneg.mpr hbc) hcomm
    rw [mul_sub, sub_nonneg] at h
    exact h

/-- **23VII** (`sqrt`, cstar.tex:3637, Exercise), part 3: for commuting
self-adjoint `a, b` with `0 ≤ a ≤ b`: `a² ≤ b²`.

The hypothesis `0 ≤ a` is **erratum 230.70** (which was for a while mis-keyed
230.50): without it the statement is false already in `𝒜 = ℂ`, where
`a = -2 ≤ 1 = b` but `4 ≰ 1`. -/
theorem sqrt_3 (a b : 𝒜) (ha : 0 ≤ a) (hb : IsSelfAdjoint b)
    (hab : a * b = b * a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  by
    -- the thesis's argument: `b² − a² = b(b−a) + (b−a)a`, and both summands
    -- are products of commuting positive elements, hence positive by part 1.
    have hb0 : (0 : 𝒜) ≤ b := ha.trans h
    have hba : (0 : 𝒜) ≤ b - a := sub_nonneg.mpr h
    have h1 : (0 : 𝒜) ≤ b * (b - a) :=
      mul_nonneg_of_commute hb0 hba (by rw [mul_sub, sub_mul, hab])
    have h2 : (0 : 𝒜) ≤ (b - a) * a :=
      mul_nonneg_of_commute hba ha (by rw [sub_mul, mul_sub, hab])
    have he : b * (b - a) + (b - a) * a = b ^ 2 - a ^ 2 := by noncomm_ring
    rw [← sub_nonneg, ← he]
    exact add_nonneg h1 h2

/-- **23VII** (`sqrt`, cstar.tex:3637, Exercise), part 4: commutativity is
essential in part 3 — the square is not monotone on the positive elements
(example among the operators on ℂ²). -/
theorem sqrt_4 :
    ∃ a b : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      0 ≤ a ∧ 0 ≤ b ∧ a ≤ b ∧ ¬(a ^ 2 ≤ b ^ 2) :=
  by
    -- The thesis's hint with the entries cleared of denominators:
    -- `a = [[1,0],[0,0]]` and `b = a + [[1,1],[1,1]] = [[2,1],[1,1]]`.
    -- Then `b² - a² = [[4,3],[3,2]]`, which has determinant `-1`.
    have hpos : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
        (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) ≤
          Matrix.toEuclideanCLM (𝕜 := ℂ) (star M * M) := by
      intro M
      rw [map_mul, map_star]
      exact star_mul_self_nonneg _
    have hA : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)
        = star (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_apply]
    have hD : (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ) - !![1, 0; 0, 0]
        = star (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_apply] <;> norm_num
    have ha : (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) ≤
        Matrix.toEuclideanCLM (𝕜 := ℂ) (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hA]; exact hpos _
    have hab :
        Matrix.toEuclideanCLM (𝕜 := ℂ) (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ≤
          Matrix.toEuclideanCLM (𝕜 := ℂ) (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [← sub_nonneg, ← map_sub, hD]
      exact hpos _
    refine ⟨_, _, ha, ha.trans hab, hab, ?_⟩
    intro hle
    have hsq : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
        Matrix.toEuclideanCLM (𝕜 := ℂ) M ^ 2 = Matrix.toEuclideanCLM (𝕜 := ℂ) (M * M) := by
      intro M; rw [sq, ← map_mul]
    have hC : (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![2, 1; 1, 1]
        - (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, 0] = !![4, 3; 3, 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
    rw [hsq, hsq, ← sub_nonneg, ← map_sub, hC] at hle
    have hq := ((ContinuousLinearMap.isPositive_iff _).mp
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hle)).2
      (WithLp.toLp 2 ![3, -4] : EuclideanSpace ℂ (Fin 2))
    -- but `⟪(b²-a²) x, x⟫ = -4` at `x = (3, -4)`
    simp only [PiLp.inner_apply, Fin.sum_univ_succ] at hq
    norm_num [Complex.le_def] at hq

/-! ## Parsec 240: positive and negative parts

**24I** (cstar.tex:3683, Definition): for self-adjoint `a`:
`|a| := √(a²)`, the *positive part* `a₊ := ½(|a| + a)` and the *negative
part* `a₋ := ½(|a| - a)`.  In Mathlib: `CFC.abs a` (`= CFC.sqrt (star a * a)`,
which equals `CFC.sqrt (a ^ 2)` for self-adjoint `a`), `a⁺` (`CFC.posPart`)
and `a⁻` (`CFC.negPart`). -/

/-- **24II** (`cstar-pos-neg-part`, cstar.tex:3699, Exercise), part 1:
`-|a| ≤ a ≤ |a|` and `‖|a|‖ = ‖a‖` for self-adjoint `a`. -/
theorem cstar_pos_neg_part_1 (a : 𝒜) (ha : IsSelfAdjoint a) :
    -CFC.abs a ≤ a ∧ a ≤ CFC.abs a ∧ ‖CFC.abs a‖ = ‖a‖ :=
  by
    have h1 : -CFC.abs a ≤ a := by
      have h := CFC.abs_add_self a ha
      have h2 : (0 : 𝒜) ≤ 2 • a⁺ := nsmul_nonneg (CFC.posPart_nonneg a) 2
      rw [← h, add_comm] at h2
      exact neg_le_iff_add_nonneg.mpr h2
    have h2 : a ≤ CFC.abs a := by
      have h := CFC.abs_sub_self a ha
      have h3 : (0 : 𝒜) ≤ 2 • a⁻ := nsmul_nonneg (CFC.negPart_nonneg a) 2
      rw [← h, sub_nonneg] at h3
      exact h3
    refine ⟨h1, h2, ?_⟩
    have hsa : IsSelfAdjoint (CFC.abs a) := .of_nonneg (CFC.abs_nonneg a)
    have h4 := cstar_involution_basic_13 (CFC.abs a) hsa
    rw [sq, CFC.abs_mul_abs, CStarRing.norm_star_mul_self] at h4
    have h5 := congrArg Real.sqrt h4
    rw [← sq, Real.sqrt_sq (norm_nonneg a), Real.sqrt_sq (norm_nonneg _)] at h5
    exact h5.symm

/-- **24II** (`cstar-pos-neg-part`, cstar.tex:3699, Exercise), part 2:
`a₊, a₋ ≥ 0`, `a = a₊ - a₋` and `a₊ a₋ = a₋ a₊ = 0`. -/
theorem cstar_pos_neg_part_2 (a : 𝒜) (ha : IsSelfAdjoint a) :
    0 ≤ a⁺ ∧ 0 ≤ a⁻ ∧ a = a⁺ - a⁻ ∧ a⁺ * a⁻ = 0 ∧ a⁻ * a⁺ = 0 :=
  by
    exact ⟨CFC.posPart_nonneg a, CFC.negPart_nonneg a, (CFC.posPart_sub_negPart a ha).symm,
      CFC.posPart_mul_negPart a, CFC.negPart_mul_posPart a⟩

/-- A `2 × 2` complex matrix as an operator on `ℂ²`. -/
private noncomputable abbrev toCLM2 (M : Matrix (Fin 2) (Fin 2) ℂ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) M

/-- **24II** (`cstar-pos-neg-part`, cstar.tex:3699, Exercise), part 3: the
triangle inequality fails for `|·|`: there are self-adjoint `a, b` with
`|a + b| ≰ |a| + |b|` (example among the operators on ℂ²). -/
theorem cstar_pos_neg_part_3 :
    ∃ a b : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      IsSelfAdjoint a ∧ IsSelfAdjoint b ∧
        ¬(CFC.abs (a + b) ≤ CFC.abs a + CFC.abs b) :=
  by
    -- The thesis's own witnesses: `a = ½[[1,1],[1,1]]` and `b = -[[1,0],[0,0]]`.
    -- Then `a² = a`, so `|a| = a`; `b² = [[1,0],[0,0]] =: p`, so `|b| = p`;
    -- and `(a+b)² = ½·1`, so `|a+b| = s·1` with `s = √2/2`.  But the `(2,2)`
    -- entry of `|a| + |b| - |a+b|` is `½ - s < 0`.
    have hs0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by positivity
    set s : ℝ := Real.sqrt 2 / 2 with hsdef
    have hs2 : (s : ℂ) * (s : ℂ) = 1 / 2 := by
      have h : s * s = 1 / 2 := by
        rw [hsdef]
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have := congrArg (fun r : ℝ => (r : ℂ)) h
      push_cast at this
      simpa using this
    set t : ℝ := Real.sqrt s with htdef
    have ht2 : (t : ℂ) * (t : ℂ) = (s : ℂ) := by
      have h : t * t = s := Real.mul_self_sqrt hs0
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h
    -- `Matrix.toEuclideanCLM` is a star-algebra isomorphism
    have hmul : ∀ M N : Matrix (Fin 2) (Fin 2) ℂ, toCLM2 M * toCLM2 N = toCLM2 (M * N) :=
      fun M N => (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) M N).symm
    have hstar : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, star (toCLM2 M) = toCLM2 (star M) :=
      fun M => (map_star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) M).symm
    have hadd : ∀ M N : Matrix (Fin 2) (Fin 2) ℂ, toCLM2 M + toCLM2 N = toCLM2 (M + N) :=
      fun M N => (map_add (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) M N).symm
    have hsub : ∀ M N : Matrix (Fin 2) (Fin 2) ℂ, toCLM2 M - toCLM2 N = toCLM2 (M - N) :=
      fun M N => (map_sub (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) M N).symm
    -- the matrices
    set MA : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 1/2; 1/2, 1/2] with hMA
    set MB : Matrix (Fin 2) (Fin 2) ℂ := !![-1, 0; 0, 0] with hMB
    set MP : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0] with hMP
    set MS : Matrix (Fin 2) (Fin 2) ℂ := !![(s:ℂ), 0; 0, (s:ℂ)] with hMS
    set MT : Matrix (Fin 2) (Fin 2) ℂ := !![(t:ℂ), 0; 0, (t:ℂ)] with hMT
    -- matrix computations
    have e1 : star MA = MA := by
      rw [hMA]; ext i j
      fin_cases i <;> fin_cases j <;> simp
    have e2 : star MB = MB := by
      rw [hMB]; ext i j
      fin_cases i <;> fin_cases j <;> simp
    have e3 : MA * MA = MA := by
      rw [hMA]; ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
    have e4 : MB * MB = MP := by
      rw [hMB, hMP]; ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    have e5 : MP * MP = MP := by
      rw [hMP]; ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    have e6 : star MP = MP := by
      rw [hMP]; ext i j
      fin_cases i <;> fin_cases j <;> simp
    have e7 : star (MA + MB) = MA + MB := by rw [star_add, e1, e2]
    have e8 : (MA + MB) * (MA + MB) = MS * MS := by
      rw [hMA, hMB, hMS]; ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, hs2] <;> ring_nf
    have e9 : star MT * MT = MS := by
      rw [hMS, hMT]; ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_apply, ht2]
    set MQ : Matrix (Fin 2) (Fin 2) ℂ := !![3/2 - (s:ℂ), 1/2; 1/2, 1/2 - (s:ℂ)] with hMQ
    have e10 : MA + MP - MS = MQ := by
      rw [hMA, hMP, hMS, hMQ]; ext i j
      fin_cases i <;> fin_cases j <;> simp <;> norm_num
    -- positivity of the three operators involved
    have hA0 : (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) ≤ toCLM2 MA := by
      have h := star_mul_self_nonneg (toCLM2 MA)
      rwa [hstar, hmul, e1, e3] at h
    have hP0 : (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) ≤ toCLM2 MP := by
      have h := star_mul_self_nonneg (toCLM2 MP)
      rwa [hstar, hmul, e6, e5] at h
    have hS0 : (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) ≤ toCLM2 MS := by
      have h := star_mul_self_nonneg (toCLM2 MT)
      rwa [hstar, hmul, e9] at h
    refine ⟨toCLM2 MA, toCLM2 MB, ?_, ?_, ?_⟩
    · show star (toCLM2 MA) = toCLM2 MA
      rw [hstar, e1]
    · show star (toCLM2 MB) = toCLM2 MB
      rw [hstar, e2]
    · have habsA : CFC.abs (toCLM2 MA) = toCLM2 MA := by
        rw [CFC.abs]
        exact CFC.sqrt_unique (by rw [hstar, hmul, hmul, e1, e3]) hA0
      have habsB : CFC.abs (toCLM2 MB) = toCLM2 MP := by
        rw [CFC.abs]
        exact CFC.sqrt_unique (by rw [hstar, hmul, hmul, e2, e4, e5]) hP0
      have habsAB : CFC.abs (toCLM2 MA + toCLM2 MB) = toCLM2 MS := by
        rw [CFC.abs]
        refine CFC.sqrt_unique ?_ hS0
        rw [hadd, hstar, hmul, hmul, e7, e8]
      rw [habsA, habsB, habsAB]
      intro hle
      rw [← sub_nonneg, hadd, hsub, e10] at hle
      have hq := ((ContinuousLinearMap.isPositive_iff _).mp
        ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hle)).2
        (WithLp.toLp 2 ![0, 1] : EuclideanSpace ℂ (Fin 2))
      simp only [PiLp.inner_apply, Fin.sum_univ_succ] at hq
      rw [hMQ] at hq
      simp [Matrix.toEuclideanCLM_toLp] at hq
      rw [Complex.le_def] at hq
      have hre := hq.1
      simp [hsdef] at hre
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, hre]

/-- **24IV** (`astara-positive`, cstar.tex:3729, Lemma): `a* a ≥ 0` for every
element `a` of a C*-algebra.  (Mathlib: `star_mul_self_nonneg`.) -/
theorem astara_positive (a : 𝒜) : 0 ≤ star a * a :=
  (thesisPos_star_mul_self a).nonneg

/-! ## Parsec 250: positivity rounded up; vector states -/

/-- **25I** (`cstar-positive-final`, cstar.tex:3750, Exercise): for a
self-adjoint element `a` of a C*-algebra the following are equivalent:
(1) `a` is positive (`‖a - t‖ ≤ t` for some `t ∈ ℝ`); (2) `‖a - t‖ ≤ t`
for all `t ≥ ‖a‖/2`; (3) `a = b²` for some self-adjoint `b`; (4) `a = c* c`
for some `c`; (5) `spec(a) ⊆ [0,∞)`. -/
theorem cstar_positive_final (a : 𝒜) (ha : IsSelfAdjoint a) :
    List.TFAE [
      0 ≤ a,
      ∀ t : ℝ, ‖a‖ / 2 ≤ t → ‖a - algebraMap ℂ 𝒜 (t : ℂ)‖ ≤ t,
      ∃ b : 𝒜, IsSelfAdjoint b ∧ a = b ^ 2,
      ∃ c : 𝒜, a = star c * c,
      spectrum ℂ a ⊆ {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = r}] :=
  by
    tfae_have 1 ↔ 2 := (cstar_positive_tfae a ha).out 3 1
    tfae_have 1 → 3 := by
      intro h
      obtain ⟨d, hd0, hd2, -⟩ := sqrt_exists_core a h
      exact ⟨d, IsSelfAdjoint.of_nonneg hd0, hd2.symm⟩
    tfae_have 3 → 4 := by
      rintro ⟨b, hb, rfl⟩
      exact ⟨b, by rw [hb.star_eq, sq]⟩
    tfae_have 4 → 1 := by
      rintro ⟨c, rfl⟩
      exact star_mul_self_nonneg c
    tfae_have 1 ↔ 5 := nonneg_iff_spectrum_ofReal_nonneg a ha
    tfae_finish

/-- **25II** (`astara-pos-basic-consequences`, cstar.tex:3772, Exercise),
part 1: `b ≤ c` implies `a* b a ≤ a* c a`. -/
theorem astara_pos_basic_1 (a b c : 𝒜) (h : b ≤ c) :
    star a * b * a ≤ star a * c * a :=
  star_left_conjugate_le_conjugate h a

/-- **25II** (`astara-pos-basic-consequences`, cstar.tex:3772, Exercise),
part 2 (mi-maps): every mi-map between C*-algebras is positive. -/
theorem astara_pos_basic_2_mi {ℬ : Type*} [CStarAlgebra ℬ] [PartialOrder ℬ]
    [StarOrderedRing ℬ] (f : 𝒜 →ₗ[ℂ] ℬ) (hm : IsMultiplicativeMap f)
    (hi : IsInvolutionPreserving f) : IsPositiveMap f :=
  by
    intro a ha
    obtain ⟨d, hd0, hd2, -⟩ := sqrt_exists_core a ha
    have hs : d * d = a := by rw [← hd2, sq]
    have h : f a = star (f d) * f d := by
      rw [← hi, (IsSelfAdjoint.of_nonneg hd0).star_eq, ← hm, hs]
    rw [h]
    exact star_mul_self_nonneg _

/-- **25II** (`astara-pos-basic-consequences`, cstar.tex:3772, Exercise),
part 2 (cp-maps): every cp-map between C*-algebras is positive. -/
theorem astara_pos_basic_2_cp {ℬ : Type*} [CStarAlgebra ℬ] [PartialOrder ℬ]
    [StarOrderedRing ℬ] (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsCompletelyPositiveMap f) :
    IsPositiveMap f :=
  by
    intro a ha
    obtain ⟨d, hd0, hd2, -⟩ := sqrt_exists_core a ha
    have hs : d * d = a := by rw [← hd2, sq]
    have h := hf 1 (fun _ => d) (fun _ => 1)
    simpa [(IsSelfAdjoint.of_nonneg hd0).star_eq, hs] using h

/-- **25II** (`astara-pos-basic-consequences`, cstar.tex:3772, Exercise),
part 3: for positive invertible `a, b`: `a ≤ b⁻¹` iff `√b a √b ≤ 1` iff
`‖√a √b‖ ≤ 1` iff `b ≤ a⁻¹` (so `a ≤ b` entails `b⁻¹ ≤ a⁻¹`). -/
theorem astara_pos_basic_3 (a b : 𝒜) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hua : IsUnit a) (hub : IsUnit b) :
    List.TFAE [
      a ≤ Ring.inverse b,
      CFC.sqrt b * a * CFC.sqrt b ≤ 1,
      ‖CFC.sqrt a * CFC.sqrt b‖ ≤ 1,
      b ≤ Ring.inverse a] :=
  by
    have hstar : ‖CFC.sqrt b * CFC.sqrt a‖ = ‖CFC.sqrt a * CFC.sqrt b‖ := by
      rw [← norm_star (CFC.sqrt b * CFC.sqrt a), star_mul,
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq,
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq]
    have key12 : ∀ x y : 𝒜, 0 ≤ x → 0 ≤ y → IsUnit y →
        (x ≤ Ring.inverse y ↔ CFC.sqrt y * x * CFC.sqrt y ≤ 1) := by
      intro x y hx hy huy
      have hsp : IsStrictlyPositive y := ⟨hy, huy⟩
      have hspi : IsStrictlyPositive (Ring.inverse y) := hsp.ringInverse
      have hone : CFC.conjSqrt y (Ring.inverse y) = 1 := by
        have h1 := CFC.conjSqrt_conjSqrt_ringInverse y 1 hsp
        rwa [CFC.conjSqrt_one (Ring.inverse y) hspi.nonneg] at h1
      constructor
      · intro hle
        have h2 := CFC.conjSqrt_le_conjSqrt (c := y) hle
        rwa [hone, CFC.conjSqrt_apply] at h2
      · intro hle
        have h2 := CFC.conjSqrt_le_conjSqrt (c := Ring.inverse y) hle
        rwa [← CFC.conjSqrt_apply, CFC.conjSqrt_ringInverse_conjSqrt y x hsp,
          CFC.conjSqrt_one (Ring.inverse y) hspi.nonneg] at h2
    have key23 : ∀ x y : 𝒜, 0 ≤ x → 0 ≤ y →
        (CFC.sqrt y * x * CFC.sqrt y ≤ 1 ↔ ‖CFC.sqrt x * CFC.sqrt y‖ ≤ 1) := by
      intro x y hx hy
      have heq : star (CFC.sqrt x * CFC.sqrt y) * (CFC.sqrt x * CFC.sqrt y)
          = CFC.sqrt y * x * CFC.sqrt y := by
        rw [star_mul, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)).star_eq,
          (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg y)).star_eq]
        rw [show CFC.sqrt y * CFC.sqrt x * (CFC.sqrt x * CFC.sqrt y)
            = CFC.sqrt y * (CFC.sqrt x * CFC.sqrt x) * CFC.sqrt y by
          simp only [mul_assoc]]
        rw [CFC.sqrt_mul_sqrt_self x hx]
      have hnn : (0 : 𝒜) ≤ CFC.sqrt y * x * CFC.sqrt y :=
        conjugate_nonneg_of_nonneg hx (CFC.sqrt_nonneg y)
      rw [← CStarAlgebra.norm_le_one_iff_of_nonneg _ hnn, ← heq,
        CStarRing.norm_star_mul_self, ← sq, sq_le_one_iff₀ (norm_nonneg _)]
    tfae_have 1 ↔ 2 := key12 a b ha hb hub
    tfae_have 2 ↔ 3 := key23 a b ha hb
    tfae_have 4 ↔ 3 := by rw [key12 b a hb ha hua, key23 b a hb ha, hstar]
    tfae_finish

/-- **25II** (`astara-pos-basic-consequences`, cstar.tex:3772, Exercise),
part 4: `(1+a)⁻¹ a ≤ (1+b)⁻¹ b` for `0 ≤ a ≤ b`. -/
theorem astara_pos_basic_4 (a b : 𝒜) (ha : 0 ≤ a) (hab : a ≤ b) :
    Ring.inverse (1 + a) * a ≤ Ring.inverse (1 + b) * b :=
  by
    have hb : 0 ≤ b := ha.trans hab
    have hsp1 : IsStrictlyPositive (1 : 𝒜) := ⟨zero_le_one, isUnit_one⟩
    have hspa : IsStrictlyPositive (1 + a) := hsp1.add_nonneg ha
    have hspb : IsStrictlyPositive (1 + b) := hsp1.add_nonneg hb
    have key : ∀ x : 𝒜, IsUnit (1 + x) →
        Ring.inverse (1 + x) * x = 1 - Ring.inverse (1 + x) := by
      intro x hx
      have h := Ring.inverse_mul_cancel _ hx
      rw [mul_add, mul_one] at h
      exact eq_sub_of_add_eq' h
    rw [key a hspa.isUnit, key b hspb.isUnit]
    refine sub_le_sub_left ?_ 1
    exact CStarAlgebra.ringInverse_le_ringInverse (add_le_add_right hab 1) hspa

end Sqrt

section VectorStates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The *vector functional* `⟪x, (·) x⟫ : B(H) → ℂ` of a vector `x ∈ H`
(**21III**, cstar.tex:3140), as a linear map. -/
noncomputable def vectorFunctional (x : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ :=
  ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H x)).toLinearMap

@[simp]
theorem vectorFunctional_apply (x : H) (T : H →L[ℂ] H) :
    vectorFunctional x T = ⟪x, T x⟫ :=
  rfl

/-- Auxiliary: every non-zero vector can be rescaled to a unit vector, and the
quantity `⟪x, T x⟫` scales by the positive real factor `‖x‖²`. -/
private theorem inner_self_scale_aux (T : H →L[ℂ] H) (x : H) (hx : x ≠ 0) :
    ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 ∧
      (⟪x, T x⟫ : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) *
        ⟪((‖x‖⁻¹ : ℝ) : ℂ) • x, T (((‖x‖⁻¹ : ℝ) : ℂ) • x)⟫ :=
  by
    have hnx : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hx
    constructor
    · simp [norm_smul, abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ hnx]
    · rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
      push_cast
      field_simp

variable [CompleteSpace H]

/-- Auxiliary: an operator is positive iff `⟪x, T x⟫ ≥ 0` for all unit vectors
`x`; this is the content of both **25III** and **25V**.2 below. -/
private theorem nonneg_clm_iff_inner_unit (T : H →L[ℂ] H) :
    0 ≤ T ↔ ∀ x : H, ‖x‖ = 1 → 0 ≤ ⟪x, T x⟫ :=
  by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    constructor
    · intro hT x _
      exact hT.inner_nonneg_right x
    · intro hx
      have key : ∀ y : H, (0 : ℂ) ≤ ⟪y, T y⟫ := by
        intro y
        rcases eq_or_ne y 0 with rfl | hy
        · simp
        · obtain ⟨hu, he⟩ := inner_self_scale_aux T y hy
          rw [he]
          exact mul_nonneg (by positivity) (hx _ hu)
      rw [ContinuousLinearMap.isPositive_iff]
      constructor
      · rw [LinearMap.isSymmetric_iff_inner_map_self_real]
        intro v
        simp only [ContinuousLinearMap.coe_coe]
        have hk := key v
        rw [Complex.le_def] at hk
        rw [Complex.conj_eq_iff_im, ← inner_conj_symm (T v) v, Complex.conj_im, neg_eq_zero]
        exact hk.2.symm
      · intro x
        rw [← inner_conj_symm (T x) x]
        have h1 := key x
        have h2 : (starRingEnd ℂ) ⟪x, T x⟫ = ⟪x, T x⟫ := by
          refine Complex.conj_eq_iff_im.mpr ?_
          rw [Complex.le_def] at h1
          simpa using h1.2.symm
        rw [h2]
        exact h1

/-- **25III** (`hilb-vector-states-order-separating`, cstar.tex:3798,
Proposition): the vector states `⟪x, (·) x⟫`, `‖x‖ = 1`, of B(H) are order
separating, for every Hilbert space `H`. -/
theorem hilb_vector_states_order_separating :
    OrderSeparating fun x : {x : H // ‖x‖ = 1} => vectorFunctional (x : H) :=
  by
    intro T
    rw [nonneg_clm_iff_inner_unit T]
    exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩

/-- **25V** (`hilb-positive-operators`, cstar.tex:3819, Corollary), part 1:
a bounded operator `T` on a Hilbert space is self-adjoint iff `⟪x, Tx⟫` is
real for every unit vector `x`. -/
theorem hilb_positive_operators_1 (T : H →L[ℂ] H) :
    IsSelfAdjoint T ↔ ∀ x : H, ‖x‖ = 1 → (⟪x, T x⟫ : ℂ).im = 0 :=
  by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
      LinearMap.isSymmetric_iff_inner_map_self_real]
    have e : ∀ v : H,
        ((starRingEnd ℂ) ⟪(T : H →ₗ[ℂ] H) v, v⟫ = ⟪(T : H →ₗ[ℂ] H) v, v⟫) ↔
          (⟪v, T v⟫ : ℂ).im = 0 := by
      intro v
      simp only [ContinuousLinearMap.coe_coe]
      rw [Complex.conj_eq_iff_im, ← inner_conj_symm (T v) v, Complex.conj_im, neg_eq_zero]
    constructor
    · intro h x _
      exact (e x).mp (h x)
    · intro h v
      refine (e v).mpr ?_
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · obtain ⟨hu, he⟩ := inner_self_scale_aux T v hv
        rw [he, Complex.mul_im, h _ hu, mul_zero, zero_add, Complex.ofReal_im, zero_mul]

/-- **25V** (`hilb-positive-operators`, cstar.tex:3819, Corollary), part 2:
`0 ≤ T` iff `0 ≤ ⟪x, Tx⟫` for every unit vector `x`. -/
theorem hilb_positive_operators_2 (T : H →L[ℂ] H) :
    0 ≤ T ↔ ∀ x : H, ‖x‖ = 1 → 0 ≤ ⟪x, T x⟫ :=
  nonneg_clm_iff_inner_unit T

/-- **25V** (`hilb-positive-operators`, cstar.tex:3819, Corollary), part 3:
`‖T‖ = sup_{‖x‖=1} |⟪x, Tx⟫|` for self-adjoint `T`. -/
theorem hilb_positive_operators_3 (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ‖T‖ = ⨆ x : {x : H // ‖x‖ = 1}, ‖⟪(x : H), T x⟫‖ :=
  by
    set M := ⨆ x : {x : H // ‖x‖ = 1}, ‖⟪(x : H), T x⟫‖ with hMdef
    have hcs : ∀ x : {x : H // ‖x‖ = 1}, ‖⟪(x : H), T x⟫‖ ≤ ‖T‖ := by
      intro x
      have h1 : ‖⟪(x : H), T x⟫‖ ≤ ‖(x : H)‖ * ‖T (x : H)‖ := norm_inner_le_norm _ _
      have h2 : ‖T (x : H)‖ ≤ ‖T‖ * ‖(x : H)‖ := T.le_opNorm _
      rw [x.2] at h1 h2
      simp only [one_mul, mul_one] at h1 h2
      exact h1.trans h2
    have hbddA : BddAbove (Set.range fun x : {x : H // ‖x‖ = 1} => ‖⟪(x : H), T x⟫‖) :=
      ⟨‖T‖, by rintro y ⟨x, rfl⟩; exact hcs x⟩
    have hM0 : 0 ≤ M := Real.iSup_nonneg fun _ => norm_nonneg _
    have hle : M ≤ ‖T‖ := Real.iSup_le hcs (norm_nonneg T)
    have hbound : ∀ x : H, ‖⟪x, T x⟫‖ ≤ M * ‖x‖ ^ 2 := by
      intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · obtain ⟨hu, he⟩ := inner_self_scale_aux T x hx
        rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖x‖ ^ 2), mul_comm]
        exact mul_le_mul_of_nonneg_right (le_ciSup hbddA ⟨_, hu⟩) (by positivity)
    have hge : ‖T‖ ≤ M := by
      rw [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric]
      refine ciSup_le fun x => ?_
      rcases eq_or_ne x 0 with rfl | hx
      · simpa using hM0
      · have hx2 : (0:ℝ) < ‖x‖ ^ 2 := by positivity
        have h1 : |T.reApplyInnerSelf x| ≤ ‖⟪x, T x⟫‖ := by
          rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_conj_symm (𝕜 := ℂ) (T x) x]
          rw [RCLike.conj_re]
          exact RCLike.abs_re_le_norm _
        rw [ContinuousLinearMap.rayleighQuotient, abs_div, abs_of_pos hx2, div_le_iff₀ hx2]
        exact h1.trans (hbound x)
    exact le_antisymm hge hle

end VectorStates

/-! ## Parsec 260: commutative C*-algebras are Riesz spaces -/

section Commutative

variable {𝒜 : Type*} [CommCStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3856, Exercise), part 1:
in a commutative C*-algebra, `|a|` is the supremum of `a` and `-a`. -/
theorem commutative_cstar_basic_1 (a : 𝒜) (ha : IsSelfAdjoint a) :
    IsLUB {a, -a} (CFC.abs a) :=
  by
    have h1 : a ≤ CFC.abs a := by
      have h := CFC.abs_sub_self a ha
      have h3 : (0 : 𝒜) ≤ 2 • a⁻ := nsmul_nonneg (CFC.negPart_nonneg a) 2
      rw [← h, sub_nonneg] at h3
      exact h3
    have h2 : -a ≤ CFC.abs a := by
      have h := CFC.abs_add_self a ha
      have h3 : (0 : 𝒜) ≤ 2 • a⁺ := nsmul_nonneg (CFC.posPart_nonneg a) 2
      rw [← h] at h3
      exact neg_le_iff_add_nonneg.mpr h3
    refine ⟨?_, ?_⟩
    · rintro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact h1
      · exact h2
    · intro c hc
      have hac : a ≤ c := hc (Set.mem_insert _ _)
      have hnac : -a ≤ c := hc (Set.mem_insert_of_mem _ rfl)
      have hca : 0 ≤ c - a := sub_nonneg.mpr hac
      have hcb : 0 ≤ c + a := by
        have h0 := sub_nonneg.mpr hnac
        rwa [sub_neg_eq_add] at h0
      have hprod : 0 ≤ (c - a) * (c + a) :=
        mul_nonneg_of_commute hca hcb (mul_comm _ _)
      have hexp : (c - a) * (c + a) = c ^ 2 - a ^ 2 := by ring
      rw [hexp, sub_nonneg] at hprod
      have h4 : (0 : 𝒜) ≤ c + c := by
        have h4' := add_nonneg hca hcb
        have h4'' : (c - a) + (c + a) = c + c := by ring
        rwa [h4''] at h4'
      have h6 : (((1 : ℝ) / 2 : ℝ) : ℂ) • (c + c) = c := by
        rw [← two_smul ℂ c, smul_smul]
        norm_num
      have hc0 : 0 ≤ c := h6 ▸ ofReal_smul_nonneg h4 (by norm_num)
      have habs : CFC.abs a = CFC.sqrt (a ^ 2) := by
        have h7 : CFC.abs a = CFC.sqrt (star a * a) := rfl
        rwa [ha.star_eq, ← sq] at h7
      -- The thesis (asols.tex:2372) invokes the monotonicity of `√` *on
      -- commuting positive elements*, which is **23VII**.0'' (`sqrt_le`), not
      -- the general `sqrt-monotone` of **28III**: `|a|` is self-adjoint,
      -- commutes with `c²`, and `|a|² = a² ≤ c²`, so `|a| ≤ c`.
      have ha2 : (0 : 𝒜) ≤ a ^ 2 := positive_basic_2_4a a ha
      have habs0 : (0 : 𝒜) ≤ CFC.abs a := by rw [habs]; exact CFC.sqrt_nonneg _
      have habssq : CFC.abs a ^ 2 = a ^ 2 := by rw [habs]; exact CFC.sq_sqrt _ ha2
      refine sqrt_le (x := c ^ 2)
        (positive_basic_2_4a c (IsSelfAdjoint.of_nonneg hc0)) hc0 rfl
        (IsSelfAdjoint.of_nonneg habs0) (mul_comm _ _) ?_
      rw [habssq]
      exact hprod

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3856, Exercise), part 2:
if `a` and `b` have a supremum `a ∨ b` then `c + a ∨ b` is the supremum of
`a + c` and `b + c`. -/
theorem commutative_cstar_basic_2 (a b c s : 𝒜) (h : IsLUB {a, b} s) :
    IsLUB {a + c, b + c} (c + s) :=
  by
    obtain ⟨hub, hlub⟩ := h
    constructor
    · rintro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · rw [add_comm c s]
        exact add_le_add_left (hub (Set.mem_insert _ _)) c
      · rw [add_comm c s]
        exact add_le_add_left (hub (Set.mem_insert_of_mem _ rfl)) c
    · intro y hy
      have hs : s ≤ -c + y := by
        refine hlub ?_
        rintro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · have h1 := hy (Set.mem_insert _ _)
          have h2 := add_le_add_left h1 (-c)
          simpa [add_comm, add_left_comm, add_assoc] using h2
        · have h1 := hy (Set.mem_insert_of_mem _ rfl)
          have h2 := add_le_add_left h1 (-c)
          simpa [add_comm, add_left_comm, add_assoc] using h2
      have h3 := add_le_add_left hs c
      simpa [add_comm, add_left_comm, add_assoc] using h3

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3856, Exercise), part 3:
`sa(𝒜)` is a Riesz space: `½(a + b + |a - b|)` is the supremum of the
self-adjoint elements `a` and `b`. -/
theorem commutative_cstar_basic_3 (a b : 𝒜) (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) :
    IsLUB {a, b} ((2 : ℂ)⁻¹ • (a + b + CFC.abs (a - b))) :=
  by
    have hhalf : IsSelfAdjoint ((2 : ℂ)⁻¹) := by simp [isSelfAdjoint_iff]
    have hd : IsSelfAdjoint ((2 : ℂ)⁻¹ • (a - b)) := hhalf.smul (ha.sub hb)
    have hlub1 := commutative_cstar_basic_1 ((2 : ℂ)⁻¹ • (a - b)) hd
    have hlub2 := commutative_cstar_basic_2 ((2 : ℂ)⁻¹ • (a - b))
      (-((2 : ℂ)⁻¹ • (a - b))) ((2 : ℂ)⁻¹ • (a + b))
      (CFC.abs ((2 : ℂ)⁻¹ • (a - b))) hlub1
    have e1 : (2 : ℂ)⁻¹ • (a - b) + (2 : ℂ)⁻¹ • (a + b) = a := by module
    have e2 : -((2 : ℂ)⁻¹ • (a - b)) + (2 : ℂ)⁻¹ • (a + b) = b := by module
    have habs : CFC.abs ((2 : ℂ)⁻¹ • (a - b)) = ((1 / 2 : ℝ)) • CFC.abs (a - b) := by
      rw [CFC.abs_smul]
      norm_num
    have e3 : (2 : ℂ)⁻¹ • (a + b) + CFC.abs ((2 : ℂ)⁻¹ • (a - b))
        = (2 : ℂ)⁻¹ • (a + b + CFC.abs (a - b)) := by
      rw [habs, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_add]
      norm_num
    rw [e1, e2, e3] at hlub2
    exact hlub2

/-- Auxiliary (**26II**.4): an miu-map between C*-algebras preserves the
square root of a positive element — `f(√a)` has the property that
characterises `√(f a)` uniquely (**23VII**.0). -/
private theorem map_sqrt {A B : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : A →⋆ₐ[ℂ] B) (a : A) (ha : 0 ≤ a) : f (CFC.sqrt a) = CFC.sqrt (f a) :=
  by
    refine (CFC.sqrt_unique ?_ ?_).symm
    · rw [← map_mul, CFC.sqrt_mul_sqrt_self a ha]
    · exact norm_mi_map_positive f _ (CFC.sqrt_nonneg a)

/-- Auxiliary (**26II**.4): consequently an miu-map preserves `|·|`. -/
private theorem map_abs {A B : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : A →⋆ₐ[ℂ] B) (x : A) : f (CFC.abs x) = CFC.abs (f x) :=
  by
    show f (CFC.sqrt (star x * x)) = CFC.sqrt (star (f x) * f x)
    rw [map_sqrt f _ (star_mul_self_nonneg x), map_mul, map_star]

/-- Auxiliary (**26II**.3): `a⁺ = ½(|a| + a)` for self-adjoint `a`. -/
private theorem posPart_eq_half {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (x : A) (hx : IsSelfAdjoint x) :
    x⁺ = (2 : ℂ)⁻¹ • (CFC.abs x + x) :=
  by
    rw [CFC.abs_add_self x hx, two_nsmul, ← two_smul ℂ, smul_smul]
    norm_num

/-- Auxiliary (**26II**.4): an miu-map between C*-algebras preserves the
positive part of a self-adjoint element (via `|·|`). -/
private theorem map_posPart {A B : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : A →⋆ₐ[ℂ] B) (x : A) (hx : IsSelfAdjoint x) : f (x⁺) = (f x)⁺ :=
  by
    rw [posPart_eq_half x hx, map_smul, map_add, map_abs,
      posPart_eq_half (f x) (hx.map f)]

/-- Auxiliary (**26II**.3): in a commutative C*-algebra the positive part
`a⁺` of a self-adjoint element `a` is the supremum of `a` and `0`. -/
private theorem isLUB_zero_posPart {A : Type*} [CommCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (x : A) (hx : IsSelfAdjoint x) :
    IsLUB {0, x} (x⁺) :=
  by
    have h := commutative_cstar_basic_3 (0 : A) x (IsSelfAdjoint.zero A) hx
    have h2 : (2 : ℂ)⁻¹ • ((0 : A) + x + CFC.abs (0 - x)) = x⁺ := by
      rw [zero_sub, CFC.abs_neg, zero_add, add_comm x (CFC.abs x),
        CFC.abs_add_self x hx, two_nsmul, ← two_smul ℂ, smul_smul]
      norm_num
    rwa [h2] at h

/-- Auxiliary (**26II**.3): in a commutative C*-algebra `a + (b - a)⁺` is the
supremum of `a` and `b`, whenever `b - a` is self-adjoint. -/
private theorem isLUB_pair {A : Type*} [CommCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (a b : A) (hba : IsSelfAdjoint (b - a)) :
    IsLUB {a, b} (a + (b - a)⁺) :=
  by
    have h := commutative_cstar_basic_2 (0 : A) (b - a) a ((b - a)⁺)
      (isLUB_zero_posPart (b - a) hba)
    simpa using h

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3856, Exercise), part 4:
an miu-map between commutative C*-algebras preserves finite suprema (and,
dually, infima). -/
theorem commutative_cstar_basic_4 {ℬ : Type*} [CommCStarAlgebra ℬ]
    [PartialOrder ℬ] [StarOrderedRing ℬ] (f : 𝒜 →⋆ₐ[ℂ] ℬ) (a b s : 𝒜)
    (h : IsLUB {a, b} s) : IsLUB {f a, f b} (f s) :=
  by
    have hsa : (0 : 𝒜) ≤ s - a := sub_nonneg.mpr (h.1 (Set.mem_insert _ _))
    have hsb : (0 : 𝒜) ≤ s - b := sub_nonneg.mpr (h.1 (Set.mem_insert_of_mem _ rfl))
    have hba : IsSelfAdjoint (b - a) := by
      have he : b - a = (s - a) - (s - b) := by ring
      rw [he]
      exact (IsSelfAdjoint.of_nonneg hsa).sub (IsSelfAdjoint.of_nonneg hsb)
    have hs : s = a + (b - a)⁺ := h.unique (isLUB_pair a b hba)
    have hfba : IsSelfAdjoint (f b - f a) := by
      rw [← map_sub]; exact hba.map f
    have hfs : f s = f a + (f b - f a)⁺ := by
      rw [hs, map_add, map_posPart f (b - a) hba, map_sub]
    rw [hfs]
    exact isLUB_pair (f a) (f b) hfba

/-- **26III** (`riesz-decomposition-lemma`, cstar.tex:3878, Exercise), the
Riesz decomposition lemma: for positive `a, b, c` in a commutative
C*-algebra with `c ≤ a + b` we have `c = a' + b'` with `0 ≤ a' ≤ a` and
`0 ≤ b' ≤ b`. -/
theorem riesz_decomposition_lemma (a b c : 𝒜) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (h : c ≤ a + b) :
    ∃ a' b' : 𝒜, 0 ≤ a' ∧ a' ≤ a ∧ 0 ≤ b' ∧ b' ≤ b ∧ c = a' + b' :=
  by
    have hcb : IsSelfAdjoint (c - b) :=
      (IsSelfAdjoint.of_nonneg hc).sub (IsSelfAdjoint.of_nonneg hb)
    have hlub := isLUB_zero_posPart (c - b) hcb
    have hcba : c - b ≤ a := sub_le_iff_le_add.mpr h
    have hcbc : c - b ≤ c := sub_le_self c hb
    have hub : ∀ y : 𝒜, 0 ≤ y → c - b ≤ y → (c - b)⁺ ≤ y := by
      intro y hy0 hy1
      refine hlub.2 ?_
      rintro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hy0
      · exact hy1
    refine ⟨(c - b)⁺, c - (c - b)⁺, CFC.posPart_nonneg _, hub a ha hcba, ?_, ?_, ?_⟩
    · exact sub_nonneg.mpr (hub c hc hcbc)
    · exact sub_le_comm.mpr (CFC.le_posPart hcb)
    · rw [add_sub_cancel]

end Commutative


end Theses.A.CStar
