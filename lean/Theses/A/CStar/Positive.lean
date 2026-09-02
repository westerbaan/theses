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

**All statements of this file are proved**, parsecs 130–260 included.
Our `cauchy_formula` is a **route divergence**, not the repair of a gap: the
thesis's own proof is complete as printed — the promotion of **14VIII**.4 from
a triangle to a regular `N`-gon is its new part 5, whose hint is the partition
15IV calls "the obvious manner", and that partition is elementary because each
filling triangle carries a *holomorphic* integrand and dies by **14IV**
`goursat`.  Ours restructures the whole proof instead; see the divergence note
above `polygon_winding` below.

Parsecs 120-150 are load-bearing: **16II** `norm_spectrum` is proved the
thesis's way, from **15VII** `rigid_expansion`, which in turn is proved from
**15V** `taylor` and **13VI** `powerseries_uniqueness_coeffients`, hence from
**15I** `cauchy_formula` and **14IV** `goursat`.
See CONVENTIONS.md for the numbering (**16II** = parsec 160, point 20) and
naming conventions.
-/
import Theses.A.CStar.Basic

open scoped ComplexOrder ComplexInnerProductSpace ComplexStarModule NNReal ENNReal
open Filter Topology

namespace Theses.A.CStar

/-! ## Parsec 120: holomorphic 𝒜-valued functions

**12I** (cstar.tex:1718): introduction — nothing to formalize.

**12II** (cstar.tex:1740, Setting): an *𝒜-valued function* is a partial map
`f : ℂ → 𝒜` with open domain; it is *holomorphic* at `x` when the difference
quotients `(f x - f y)/(x - y)` norm-converge as `y → x`, and the limit is its
*derivative* `f' x`.  In Mathlib this is differentiability of `f : ℂ → 𝒜` on
an open set `U` (`DifferentiableOn ℂ f U`, pointwise `HasDerivAt f f' x`),
where `𝒜` is any complex Banach space — in this file always a C*-algebra, as
in the thesis. -/

section Holomorphic

variable {𝒜 : Type*} [CStarAlgebra 𝒜]

/-- **12III** (cstar.tex:1770, Exercise), part 1 (sums): the sum of functions
holomorphic at `z` is holomorphic at `z`, with `(f + g)' = f' + g'`. -/
theorem holomorphic_add (f g : ℂ → 𝒜) (f' g' : 𝒜) (z : ℂ)
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) :
    HasDerivAt (fun w => f w + g w) (f' + g') z :=
  hf.add hg

/-- **12III** (cstar.tex:1770, Exercise), part 1 (products): the product of
functions holomorphic at `z` is holomorphic, with the Leibniz rule for the
derivative. -/
theorem holomorphic_mul (f g : ℂ → 𝒜) (f' g' : 𝒜) (z : ℂ)
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) :
    HasDerivAt (fun w => f w * g w) (f' * g z + f z * g') z :=
  hf.mul hg

/-- **12III** (cstar.tex:1770, Exercise), part 2: the function `z ↦ z`
(as the 𝒜-valued function `z ↦ z·1`) is holomorphic with derivative `1`. -/
theorem holomorphic_id (z : ℂ) :
    HasDerivAt (fun w => algebraMap ℂ 𝒜 w) (1 : 𝒜) z :=
  by
    simpa [Algebra.algebraMap_eq_smul_one] using (hasDerivAt_id z).smul_const (1 : 𝒜)

/-- **12III** (cstar.tex:1770, Exercise), part 3: constant functions are
holomorphic with derivative `0`. -/
theorem holomorphic_const (a : 𝒜) (z : ℂ) :
    HasDerivAt (fun _ : ℂ => a) (0 : 𝒜) z :=
  hasDerivAt_const z a

/-- **12III** (cstar.tex:1770, Exercise), part 4: a polynomial
`z ↦ ∑_{i ≤ n} zⁱ aᵢ` with coefficients in `𝒜` is holomorphic, with
derivative `z ↦ ∑ i zⁱ⁻¹ aᵢ`. -/
theorem holomorphic_polynomial (n : ℕ) (a : ℕ → 𝒜) (z : ℂ) :
    HasDerivAt (fun w => ∑ i ∈ Finset.range (n + 1), w ^ i • a i)
      (∑ i ∈ Finset.range (n + 1), ((i : ℂ) * z ^ (i - 1)) • a i) z :=
  by
    exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_pow i z).smul_const (a i)

/-! ## Parsec 130: power series -/

/-- The *radius of convergence* `R = (limsupₙ ‖aₙ‖^{1/n})⁻¹ ∈ [0,∞]` of a
power series `∑ₙ aₙ zⁿ` over `𝒜` (**13II**, `hadamard`, cstar.tex:1807). -/
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

/-- **13II** (`hadamard`, cstar.tex:1807, Theorem), part 1: the series
`∑ₙ aₙ zⁿ` converges absolutely for `|z| < R`. -/
theorem hadamard_1 (a : ℕ → 𝒜) (z : ℂ)
    (hz : (‖z‖₊ : ℝ≥0∞) < radiusOfConvergence a) :
    Summable fun n : ℕ => ‖a n‖ * ‖z‖ ^ n :=
  by
    -- the thesis's `ε`-and-geometric-tail argument is Mathlib's
    -- `FormalMultilinearSeries.summable_norm_mul_pow`
    rw [radiusOfConvergence_eq] at hz
    simpa [fpsOfCoeffs_coeff] using (fpsOfCoeffs a).summable_norm_mul_pow (r := ‖z‖₊) hz

/-- **13II** (`hadamard`, cstar.tex:1807, Theorem), part 2: if `∑ₙ aₙ zⁿ`
converges then `|z| ≤ R`.

The hypothesis is *convergence of the partial sums* `∑_{n<N} aₙ zⁿ`, as the
Theorem states it — not `Summable`, i.e. unconditional summability, which in
an infinite-dimensional Banach space is strictly stronger and which is not
what the thesis's proof needs.

*Class 1 — faithful*: the terms `aₙ zⁿ = S_{N+1} - S_N` of a convergent
series tend to `0`, hence `‖aₙ‖ |z|ⁿ` is bounded, hence `|z| ≤ R`. -/
theorem hadamard_2 (a : ℕ → 𝒜) (z : ℂ) (L : 𝒜)
    (hz : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ n • a n) atTop (𝓝 L)) :
    (‖z‖₊ : ℝ≥0∞) ≤ radiusOfConvergence a :=
  by
    rw [radiusOfConvergence_eq]
    refine (fpsOfCoeffs a).le_radius_of_tendsto (r := ‖z‖₊) (l := 0) ?_
    -- the terms of a convergent series tend to `0`
    have hshift : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), z ^ n • a n)
        atTop (𝓝 L) := hz.comp (tendsto_add_atTop_nat 1)
    have hterm : Tendsto (fun N : ℕ => z ^ N • a N) atTop (𝓝 0) := by
      have hd := hshift.sub hz
      rw [sub_self] at hd
      refine hd.congr fun N => ?_
      rw [Finset.sum_range_succ]
      abel
    have h0 := hterm.norm
    simpa [fpsOfCoeffs_coeff, norm_smul, mul_comm] using h0

/-- The dominating series of the thesis's proof of **13IV**: if `‖aₙ‖sⁿ` is
summable and `0 < r < s`, then `2 ∑ₙ n ‖aₙ‖ rⁿ⁻¹` converges.  This is the step
cstar.tex:1949 asserts in passing — "the radius of convergence of
`∑ₙ aₙ n zⁿ⁻¹` is `R > r`" — obtained not by recomputing a limsup but from the
bound `‖aₙ‖sⁿ ≤ C` of **13II**.1 at the intermediate radius `s`, which
dominates `2n‖aₙ‖rⁿ⁻¹` by `(2C/r)·n·(r/s)ⁿ`. -/
private theorem summable_deriv_bound (a : ℕ → 𝒜) (r s : ℝ) (hr : 0 < r) (hrs : r < s)
    (hsum : Summable fun n : ℕ => ‖a n‖ * s ^ n) :
    Summable fun n : ℕ => 2 * (n : ℝ) * r ^ (n - 1) * ‖a n‖ := by
  have hs0 : 0 < s := hr.trans hrs
  set C := ∑' n : ℕ, ‖a n‖ * s ^ n with hC
  have hCb : ∀ n : ℕ, ‖a n‖ * s ^ n ≤ C := fun n =>
    hsum.le_tsum n fun m _ => by positivity
  have hC0 : 0 ≤ C := le_trans (by positivity) (hCb 0)
  clear_value C
  have hq0 : 0 ≤ r / s := by positivity
  have hq1 : r / s < 1 := (div_lt_one hs0).2 hrs
  have hgeo : Summable fun n : ℕ => (n : ℝ) * (r / s) ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hgeo.mul_left (2 * C / r))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hkey : ‖a n‖ ≤ C / s ^ n := by
      rw [le_div_iff₀ (by positivity)]
      exact hCb n
    have hrpow : r ^ (n - 1) = r ^ n / r := by
      rw [eq_div_iff hr.ne', ← pow_succ]
      congr 1
      omega
    rw [hrpow]
    calc 2 * (n : ℝ) * (r ^ n / r) * ‖a n‖
        ≤ 2 * (n : ℝ) * (r ^ n / r) * (C / s ^ n) := by
          have h0 : (0:ℝ) ≤ 2 * (n : ℝ) * (r ^ n / r) := by positivity
          exact mul_le_mul_of_nonneg_left hkey h0
      _ = 2 * C / r * ((n : ℝ) * (r / s) ^ n) := by
          rw [div_pow]
          field_simp

/-- **13IV** (cstar.tex:1869, Proposition): the function given by a power
series `∑ₙ aₙ zⁿ` is holomorphic on the disk `|z| < R`, with derivative
`∑ₙ n aₙ zⁿ⁻¹`.

*Class 1 — faithful*: the thesis's own proof (cstar.tex:1912-1955).  Pick
`|z| < r < R`.  The difference quotient minus the candidate derivative is the
tsum of

  `((z+h)ⁿ - zⁿ)/h - n zⁿ⁻¹ = ∑_{i<n} ((z+h)ⁱ - zⁱ) zⁿ⁻¹⁻ⁱ`  (`hkey`),

the thesis's rearranged identity, here in the equivalent index-reversed form
that `geom_sum₂_mul` delivers.  Each term of that sum has norm at most
`2rⁿ⁻¹`, so the whole is at most `2n rⁿ⁻¹` (`hev`), which is the thesis's
`\eqref{power-series-derivative-2}`; each individual term tends to `0` as
`h → 0` (`hab`), which is its `\eqref{power-series-derivative-1}`; and the
dominating series `2 ∑ₙ n‖aₙ‖rⁿ⁻¹` converges (`summable_deriv_bound`).  The
"tails vanish uniformly in `h`" step is Mathlib's
`tendsto_tsum_of_dominated_convergence`, dominated convergence for a tsum
along an arbitrary filter — here `𝓝[≠] z`. -/
theorem powerSeries_hasDerivAt (a : ℕ → 𝒜) (z : ℂ)
    (hz : (‖z‖₊ : ℝ≥0∞) < radiusOfConvergence a) :
    HasDerivAt (fun w : ℂ => ∑' n : ℕ, w ^ n • a n)
      (∑' n : ℕ, ((n : ℂ) * z ^ (n - 1)) • a n) z := by
  -- Pick `‖z‖ < r < s < R`, as the thesis picks `|z| < r < R`.
  obtain ⟨u, hzu, huR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hz
  obtain ⟨v, huv, hvR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp huR
  set r : ℝ := (u : ℝ) with hrdef
  set s : ℝ := (v : ℝ) with hsdef
  have hzr : ‖z‖ < r := by exact_mod_cast ENNReal.coe_lt_coe.mp hzu
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg z) hzr
  have hrs : r < s := by exact_mod_cast ENNReal.coe_lt_coe.mp huv
  have hs0 : 0 < s := hr0.trans hrs
  -- **13II**.1 at the real point `s`
  have hnn : ‖((s : ℝ) : ℂ)‖₊ = v := by
    ext
    simp [hsdef]
  have hsR : (‖((s : ℝ) : ℂ)‖₊ : ℝ≥0∞) < radiusOfConvergence a := by rw [hnn]; exact hvR
  have hsum : Summable fun n : ℕ => ‖a n‖ * s ^ n := by
    have h := hadamard_1 a ((s : ℝ) : ℂ) hsR
    simpa [Complex.norm_real, abs_of_nonneg hs0.le] using h
  -- The dominating series `2 ∑ₙ n ‖aₙ‖ rⁿ⁻¹` of the thesis's proof.
  have hB : Summable fun n : ℕ => 2 * (n : ℝ) * r ^ (n - 1) * ‖a n‖ :=
    summable_deriv_bound a r s hr0 hrs hsum
  have hsummable : ∀ w : ℂ, ‖w‖ ≤ r → Summable fun n : ℕ => w ^ n • a n := by
    intro w hw
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hsum)
    rw [norm_smul, norm_pow, mul_comm]
    gcongr
    exact hw.trans hrs.le
  have hgsum : Summable fun n : ℕ => ((n : ℂ) * z ^ (n - 1)) • a n := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hB)
    rw [norm_smul, norm_mul, Complex.norm_natCast, norm_pow]
    have h1 : (n : ℝ) * ‖z‖ ^ (n - 1) * ‖a n‖ ≤ (n : ℝ) * r ^ (n - 1) * ‖a n‖ := by
      gcongr
    have h2 : (0:ℝ) ≤ (n : ℝ) * r ^ (n - 1) * ‖a n‖ := by positivity
    have h3 : 2 * (n : ℝ) * r ^ (n - 1) * ‖a n‖
        = (n : ℝ) * r ^ (n - 1) * ‖a n‖ + (n : ℝ) * r ^ (n - 1) * ‖a n‖ := by ring
    rw [h3]
    linarith
  have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 z :=
    Metric.isOpen_ball.mem_nhds (by simpa [mem_ball_zero_iff] using hzr)
  -- The thesis's rearranged identity, cstar.tex:1930.
  have hkey : ∀ w : ℂ, w ≠ z → ∀ n : ℕ,
      (w - z)⁻¹ * (w ^ n - z ^ n) - (n : ℂ) * z ^ (n - 1)
        = ∑ i ∈ Finset.range n, (w ^ i - z ^ i) * z ^ (n - 1 - i) := by
    intro w hwne n
    have hwz : w - z ≠ 0 := sub_ne_zero.mpr hwne
    have h1 : (∑ i ∈ Finset.range n, w ^ i * z ^ (n - 1 - i)) * (w - z) = w ^ n - z ^ n :=
      geom_sum₂_mul w z n
    have h2 : (w - z)⁻¹ * (w ^ n - z ^ n) = ∑ i ∈ Finset.range n, w ^ i * z ^ (n - 1 - i) := by
      rw [← h1]
      field_simp
    have h3 : ∀ i ∈ Finset.range n, z ^ i * z ^ (n - 1 - i) = z ^ (n - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    have h4 : (∑ i ∈ Finset.range n, z ^ i * z ^ (n - 1 - i)) = (n : ℂ) * z ^ (n - 1) := by
      rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h2, ← h4, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- The thesis's estimate, cstar.tex:1934: each difference quotient is
  -- dominated by `2 n rⁿ⁻¹ ‖aₙ‖`, uniformly in `w`.
  have hev : ∀ᶠ w : ℂ in 𝓝[≠] z, ∀ n : ℕ,
      ‖((w - z)⁻¹ * (w ^ n - z ^ n) - (n : ℂ) * z ^ (n - 1)) • a n‖
        ≤ 2 * (n : ℝ) * r ^ (n - 1) * ‖a n‖ := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with w hwne hwball n
    have hwne' : w ≠ z := hwne
    have hwr : ‖w‖ ≤ r := le_of_lt (by simpa [mem_ball_zero_iff] using hwball)
    rw [norm_smul, hkey w hwne' n]
    have hterm : ∀ i ∈ Finset.range n,
        ‖(w ^ i - z ^ i) * z ^ (n - 1 - i)‖ ≤ 2 * r ^ (n - 1) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [norm_mul, norm_pow]
      have e1 : ‖w ^ i - z ^ i‖ ≤ 2 * r ^ i := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_pow, norm_pow]
        have f1 : ‖w‖ ^ i ≤ r ^ i := by gcongr
        have f2 : ‖z‖ ^ i ≤ r ^ i := by gcongr
        linarith
      have e2 : ‖z‖ ^ (n - 1 - i) ≤ r ^ (n - 1 - i) := by gcongr
      calc ‖w ^ i - z ^ i‖ * ‖z‖ ^ (n - 1 - i) ≤ (2 * r ^ i) * r ^ (n - 1 - i) := by
            refine mul_le_mul e1 e2 (by positivity) (by positivity)
        _ = 2 * r ^ (n - 1) := by
            rw [mul_assoc, ← pow_add]
            congr 2
            omega
    have hsumle : ‖∑ i ∈ Finset.range n, (w ^ i - z ^ i) * z ^ (n - 1 - i)‖
        ≤ 2 * (n : ℝ) * r ^ (n - 1) := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ i ∈ Finset.range n, ‖(w ^ i - z ^ i) * z ^ (n - 1 - i)‖
          ≤ ∑ _i ∈ Finset.range n, 2 * r ^ (n - 1) := Finset.sum_le_sum hterm
        _ = 2 * (n : ℝ) * r ^ (n - 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    calc ‖∑ i ∈ Finset.range n, (w ^ i - z ^ i) * z ^ (n - 1 - i)‖ * ‖a n‖
        ≤ (2 * (n : ℝ) * r ^ (n - 1)) * ‖a n‖ :=
          mul_le_mul_of_nonneg_right hsumle (norm_nonneg _)
      _ = 2 * (n : ℝ) * r ^ (n - 1) * ‖a n‖ := by ring
  -- Termwise, the difference quotients tend to `0` (cstar.tex:1941).
  have hab : ∀ n : ℕ, Tendsto (fun w : ℂ =>
      ((w - z)⁻¹ * (w ^ n - z ^ n) - (n : ℂ) * z ^ (n - 1)) • a n) (𝓝[≠] z) (𝓝 0) := by
    intro n
    have hslope := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_pow n z)
    have h0 : Tendsto (fun w : ℂ => (w - z)⁻¹ * (w ^ n - z ^ n) - (n : ℂ) * z ^ (n - 1))
        (𝓝[≠] z) (𝓝 0) := by
      have h := hslope.sub_const ((n : ℂ) * z ^ (n - 1))
      rw [sub_self] at h
      refine h.congr fun w => ?_
      simp [slope_def_field, div_eq_inv_mul]
    simpa using h0.smul_const (a n)
  -- Dominated convergence for the tsum along `𝓝[≠] z` (cstar.tex:1947).
  have hdom : Tendsto (fun w : ℂ => ∑' n : ℕ,
      ((w - z)⁻¹ * (w ^ n - z ^ n) - (n : ℂ) * z ^ (n - 1)) • a n) (𝓝[≠] z) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence
      (f := fun (w : ℂ) (n : ℕ) => ((w - z)⁻¹ * (w ^ n - z ^ n) - (n : ℂ) * z ^ (n - 1)) • a n)
      (g := fun _ : ℕ => (0 : 𝒜))
      (bound := fun n : ℕ => 2 * (n : ℝ) * r ^ (n - 1) * ‖a n‖) hB hab hev
    simpa using h
  rw [hasDerivAt_iff_tendsto_slope]
  have hfinal := hdom.add_const (∑' n : ℕ, ((n : ℂ) * z ^ (n - 1)) • a n)
  rw [zero_add] at hfinal
  refine Filter.Tendsto.congr' ?_ hfinal
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with w hwne hwball
  have hwne' : w ≠ z := hwne
  have hwr : ‖w‖ ≤ r := le_of_lt (by simpa [mem_ball_zero_iff] using hwball)
  have hws := (hsummable w hwr).hasSum
  have hzs := (hsummable z hzr.le).hasSum
  have hpsi : HasSum (fun n : ℕ => ((w - z)⁻¹ * (w ^ n - z ^ n) - (n : ℂ) * z ^ (n - 1)) • a n)
      ((w - z)⁻¹ • ((∑' n : ℕ, w ^ n • a n) - ∑' n : ℕ, z ^ n • a n)
        - ∑' n : ℕ, ((n : ℂ) * z ^ (n - 1)) • a n) := by
    refine HasSum.congr_fun (((hws.sub hzs).const_smul (w - z)⁻¹).sub hgsum.hasSum) ?_
    intro n
    simp [smul_sub, smul_smul, sub_smul, mul_sub]
  rw [hpsi.tsum_eq]
  simp [slope, vsub_eq_sub]

/-! ### The solution's route for 13VI

`parsec-130.60` (asols.tex:1594) proves **13VI** by differentiating the series
repeatedly: `f` is `0` on the disk, hence so is `f'`, and `f'(0)` reads off
the first coefficient by **13IV**; iterate.  The three private lemmas below
are what that route needs beyond **13IV** — the radius bound `r ≤ R` of
**13II**.2, and summability of the term-wise derivative series on the same
disk, which **13IV** does not deliver (it gives the derivative only as a
`tsum`).  The derived radius that cstar.tex:1949 asserts in passing is not
recomputed: the disk `|z| < r` is exhausted from inside, and on `|z| ≤ t < s <
r` the bound `‖aₙ‖sⁿ ≤ C` of **13II**.1 dominates `(n+1)‖aₙ₊₁‖tⁿ` by
`(C/s)(n+1)(t/s)ⁿ`.

A slip in the printed solution, reported and not filed: it writes
`0 = f⁽ⁿ⁾(0) = n aₙ` (asols.tex:1614) where the coefficient is `n!·aₙ` —
already wrong at `n = 3`.  The conclusion `aₙ = 0` is unaffected, both being
nonzero multiples of `aₙ`, and the induction below reads each `aₙ` off the
constant term of the `n`-th derived series, so it never meets the slip. -/

/-- Convergence of `∑ₙ aₙ zⁿ` on the disk of radius `r` forces `r ≤ R`; this
is **13II**.2 `hadamard_2` applied at every real point of the disk. -/
private theorem radius_ge_of_hasSum (a : ℕ → 𝒜) (r : ℝ)
    (h : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => z ^ n • a n) 0) :
    ENNReal.ofReal r ≤ radiusOfConvergence a := by
  refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
  have htr : (t : ℝ) < r := by
    have h1 : (t : ℝ≥0∞) < ENNReal.ofReal r := ht
    rw [ENNReal.lt_ofReal_iff_toReal_lt (by simp)] at h1
    simpa using h1
  have hz : ‖((t : ℝ) : ℂ)‖ < r := by
    simpa [Complex.norm_real, abs_of_nonneg t.coe_nonneg] using htr
  have hh := hadamard_2 a ((t : ℝ) : ℂ) 0 ((h _ hz).tendsto_sum_nat)
  simpa [Complex.nnnorm_real, abs_of_nonneg t.coe_nonneg] using hh

/-- A point of the disk of radius `r ≤ R` is strictly inside the disk of
convergence. -/
private theorem enorm_lt_radius (a : ℕ → 𝒜) (r : ℝ) (hr : 0 < r)
    (hR : ENNReal.ofReal r ≤ radiusOfConvergence a) (w : ℂ) (hw : ‖w‖ < r) :
    (‖w‖₊ : ℝ≥0∞) < radiusOfConvergence a := by
  refine lt_of_lt_of_le ?_ hR
  rw [ENNReal.coe_nnreal_eq]
  simpa using (ENNReal.ofReal_lt_ofReal_iff hr).mpr hw

/-- The term-wise derivative series `∑ₙ (n+1) aₙ₊₁ zⁿ` is summable strictly
inside the disk of radius `r ≤ R`.  This is the one step the solution takes
for granted (cstar.tex:1949, "the radius of convergence of `∑ₙ aₙ n zⁿ⁻¹` is
`R > r`"); here it comes from **13II**.1 at an intermediate radius `s` with
`‖z‖ < s < r`, since `‖aₙ‖sⁿ` is then bounded and `∑ₙ (n+1)qⁿ` converges for
`q = ‖z‖/s < 1`. -/
private theorem summable_deriv (a : ℕ → 𝒜) (r : ℝ) (hr : 0 < r)
    (hR : ENNReal.ofReal r ≤ radiusOfConvergence a) (z : ℂ) (hz : ‖z‖ < r) :
    Summable (fun n : ℕ => z ^ n • (((n : ℂ) + 1) • a (n + 1))) := by
  have ht0 : 0 ≤ ‖z‖ := norm_nonneg z
  obtain ⟨s, hts, hsr⟩ : ∃ s : ℝ, ‖z‖ < s ∧ s < r :=
    ⟨(‖z‖ + r) / 2, by linarith, by linarith⟩
  have hs0 : 0 < s := by linarith
  have hsR := enorm_lt_radius a r hr hR ((s : ℝ) : ℂ)
    (by simpa [Complex.norm_real, abs_of_nonneg hs0.le] using hsr)
  have hsum := hadamard_1 a ((s : ℝ) : ℂ) hsR
  have hsum' : Summable (fun n : ℕ => ‖a n‖ * s ^ n) := by
    simpa [Complex.norm_real, abs_of_nonneg hs0.le] using hsum
  set C := ∑' n : ℕ, ‖a n‖ * s ^ n with hCdef
  have hCb : ∀ n : ℕ, ‖a n‖ * s ^ n ≤ C := fun n =>
    hsum'.le_tsum n (fun m _ => by positivity)
  have hC0 : 0 ≤ C := le_trans (by positivity) (hCb 0)
  clear_value C
  have hq0 : 0 ≤ ‖z‖ / s := by positivity
  have hq1 : ‖z‖ / s < 1 := (div_lt_one hs0).2 hts
  have hgeo : Summable (fun n : ℕ => ((n : ℝ) + 1) * (‖z‖ / s) ^ n) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * (‖z‖ / s) ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 1
        (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
    have h2 : Summable (fun n : ℕ => (‖z‖ / s) ^ n) := summable_geometric_of_lt_one hq0 hq1
    refine (h1.add h2).congr fun n => ?_
    ring
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeo.mul_left (C / s))
  have hkey : ‖a (n + 1)‖ ≤ C / s ^ (n + 1) := by
    rw [le_div_iff₀ (by positivity)]
    exact hCb (n + 1)
  have hnc : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    have hcast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_natCast]
    push_cast; ring
  rw [norm_smul, norm_smul, norm_pow, hnc]
  calc ‖z‖ ^ n * (((n : ℝ) + 1) * ‖a (n + 1)‖)
      ≤ ‖z‖ ^ n * (((n : ℝ) + 1) * (C / s ^ (n + 1))) := by gcongr
  _ = C / s * (((n : ℝ) + 1) * (‖z‖ / s) ^ n) := by
        rw [div_pow]
        field_simp
        ring

/-- The solution's inductive step: if `∑ₙ aₙ zⁿ` is `0` on the disk of radius
`r`, so is its term-wise derivative `∑ₙ (n+1) aₙ₊₁ zⁿ`.  `f' = 0` because `f`
vanishes on a neighbourhood of each point of the disk, and `f'` is the
term-wise derivative by **13IV** `powerSeries_hasDerivAt`. -/
private theorem deriv_hasSum_zero (a : ℕ → 𝒜) (r : ℝ) (hr : 0 < r)
    (h : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => z ^ n • a n) 0) :
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => z ^ n • (((n : ℂ) + 1) • a (n + 1))) 0 := by
  intro z hz
  have hR := radius_ge_of_hasSum a r h
  have hsum := summable_deriv a r hr hR z hz
  have hd := powerSeries_hasDerivAt a z (enorm_lt_radius a r hr hR z hz)
  have hd0 : HasDerivAt (fun w : ℂ => ∑' n : ℕ, w ^ n • a n) 0 z := by
    have heq : (fun w : ℂ => ∑' n : ℕ, w ^ n • a n) =ᶠ[𝓝 z] fun _ => (0 : 𝒜) := by
      filter_upwards [Metric.ball_mem_nhds z (by linarith : (0:ℝ) < r - ‖z‖)] with w hw
      refine (h w ?_).tsum_eq
      rw [Metric.mem_ball, dist_eq_norm] at hw
      calc ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by simpa using norm_le_norm_add_norm_sub' w z
        _ < r := by linarith
    exact (hasDerivAt_const z (0 : 𝒜)).congr_of_eventuallyEq heq
  have huniq : (∑' n : ℕ, ((n : ℂ) * z ^ (n - 1)) • a n) = 0 := hd.unique hd0
  set V := ∑' n : ℕ, z ^ n • (((n : ℂ) + 1) • a (n + 1)) with hV
  have hL : HasSum (fun n : ℕ => z ^ n • (((n : ℂ) + 1) • a (n + 1))) V := hsum.hasSum
  have h2 : HasSum (fun b : ℕ => (((b + 1 : ℕ) : ℂ) * z ^ ((b + 1) - 1)) • a (b + 1)) V := by
    refine hL.congr_fun fun b => ?_
    rw [smul_smul]
    congr 1
    push_cast
    ring
  have h3 := (hasSum_nat_add_iff (f := fun n : ℕ => ((n : ℂ) * z ^ (n - 1)) • a n) 1).mp h2
  have h4 : HasSum (fun n : ℕ => ((n : ℂ) * z ^ (n - 1)) • a n) V := by simpa using h3
  have hV0 : V = 0 := by rw [← huniq, h4.tsum_eq]
  rw [← hV0]
  exact hL

/-- **13VI** (`powerseries-uniqueness-coeffients`, cstar.tex:1959, Exercise):
if a power series `∑ₙ aₙ zⁿ` sums to `0` on some disk around `0` of positive
radius, then all its coefficients vanish.

*Class 1 — the solution's own route* (`parsec-130.60`, asols.tex:1594): the
constant term is `f(0) = 0`; the derivative is again a power series summing to
`0` on the same disk (`deriv_hasSum_zero`, which is **13IV**
`powerSeries_hasDerivAt` plus `summable_deriv`); induct. -/
theorem powerseries_uniqueness_coeffients (a : ℕ → 𝒜) (r : ℝ) (hr : 0 < r)
    (h : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => z ^ n • a n) 0) :
    ∀ n, a n = 0 :=
  by
    intro n
    induction n generalizing a with
    | zero =>
      have hs := h 0 (by simpa using hr)
      have hsingle : HasSum (fun n : ℕ => (0 : ℂ) ^ n • a n) ((0 : ℂ) ^ (0 : ℕ) • a 0) := by
        refine hasSum_single 0 fun b hb => ?_
        simp [zero_pow hb]
      have hfin := hsingle.unique hs
      simpa using hfin
    | succ k ih =>
      have hb := deriv_hasSum_zero a r hr h
      have hk := ih (fun n : ℕ => ((n : ℂ) + 1) • a (n + 1)) hb
      have hne : ((k : ℂ) + 1) ≠ 0 := by
        have hpos : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
        simpa using hpos
      rcases smul_eq_zero.mp hk with hzz | hzz
      · exact absurd hzz hne
      · exact hzz

/-! ## Parsec 140: integration and Goursat's theorem

**14II** (cstar.tex:2001, Exercise): the *construction* of the integral
`∫ f ∈ 𝒜` of a continuous `f : [0,1] → 𝒜` — part 1 (the linear
`∫ : S_𝒜 → 𝒜` with `∫ a·1_I = |I|a`), part 2's disjoint-interval normal form
`‖f‖ = supₙ‖aₙ‖`, `∑ₙ|Iₙ| ≤ 1`, and part 3 (density of `S_𝒜` in
`C([0,1],𝒜)`) — is in Mathlib the Bochner integral
`∫ t in (0:ℝ)..1, f t` of the `MeasureTheory` library, and the 𝒜-valued step
functions `S_𝒜` are not built here.  What parts 1–3 are *for*, and what the
rest of the chapter uses, is the bound `‖∫ f‖ ≤ ‖f‖` that part 2 asks one to
deduce; that bound is `integral_norm_le` below, and part 4 is
`integral_scalar_smul`. -/

/-- **14II** (cstar.tex:2001, Exercise), part 4: `∫ a f = a ∫ f` for
continuous `f : [0,1] → ℂ` and `a ∈ 𝒜`. -/
theorem integral_scalar_smul (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc 0 1))
    (a : 𝒜) :
    ∫ t in (0:ℝ)..1, f t • a = (∫ t in (0:ℝ)..1, f t) • a :=
  intervalIntegral.integral_smul_const f a

/-- **14II** (cstar.tex:2001, Exercise), part 2, closing clause: `‖∫ f‖ ≤ ‖f‖`
for the supremum norm on `[0,1]` — the bound the Exercise asks one to deduce
from the disjoint-interval normal form (`‖∫f‖ ≤ ∑ₙ‖aₙ‖|Iₙ| ≤ ‖f‖∑ₙ|Iₙ| ≤ ‖f‖`),
and the clause the rest of the chapter actually uses.  The sup norm of `f` is
taken here as any bound `M` on `‖f t‖` over `[0,1]`, which is what the
Bochner integral's own estimate supplies.

*Class 5 — Mathlib*: the deduction from the normal form is not transcribed,
because `S_𝒜` is not built here; see the section note. -/
theorem integral_norm_le (f : ℝ → 𝒜) (M : ℝ)
    (hM : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖f t‖ ≤ M) :
    ‖∫ t in (0:ℝ)..1, f t‖ ≤ M :=
  by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := 1) (f := f) (C := M) (fun t ht => by
        refine hM t ?_
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
        exact Set.Ioc_subset_Icc_self ht)
    simpa using h

/-- **14III** (cstar.tex:2095, Definition): the integral
`∫_w^{w'} f = (w' - w) ∫₀¹ f(w + t(w' - w)) dt` of an 𝒜-valued function
along the line segment `[w, w']`. -/
noncomputable def segIntegral (f : ℂ → 𝒜) (w w' : ℂ) : 𝒜 :=
  (w' - w) • ∫ t in (0:ℝ)..1, f (w + (t : ℂ) * (w' - w))

/-- **14III** (cstar.tex:2095, Definition): the integral
`∫_T f = ∫_{w₀}^{w₁} f + ∫_{w₁}^{w₂} f + ∫_{w₂}^{w₀} f` of an 𝒜-valued
function along the triangle `T` with vertices `w₀, w₁, w₂`. -/
noncomputable def triIntegral (f : ℂ → 𝒜) (w₀ w₁ w₂ : ℂ) : 𝒜 :=
  segIntegral f w₀ w₁ + segIntegral f w₁ w₂ + segIntegral f w₂ w₀

/-- **14III** (cstar.tex:2095, Definition): `∠(w₀, z, w₁)`, the number of
radians in `(-π, π]` needed to rotate the ray from `z` through `w₀`
counterclockwise around `z` to hit `w₁` — here `arg ((w₁ - z)/(w₀ - z))`. -/
noncomputable def measuredAngle (w₀ z w₁ : ℂ) : ℝ :=
  Complex.arg ((w₁ - z) / (w₀ - z))

/-- **14III** (cstar.tex:2095, Definition): the *winding number* of the
triangle with vertices `w₀, w₁, w₂` around a point `z` not on its boundary:
`2π wn_T(z) = ∠(w₀,z,w₁) + ∠(w₁,z,w₂) + ∠(w₂,z,w₀)`. -/
noncomputable def windingNumber (w₀ w₁ w₂ z : ℂ) : ℝ :=
  (measuredAngle w₀ z w₁ + measuredAngle w₁ z w₂ + measuredAngle w₂ z w₀) /
    (2 * Real.pi)

/-! ### The bisection machinery behind **14IV** `goursat`

The thesis's proof (cstar.tex:2183–2299, after Moore 1900) bisects the triangle
into four, keeps a quarter carrying at least a quarter of the integral, and in the
limit uses differentiability at the point common to all of them, together with
`∫_T (α + βz) dz = 0`, to make the estimate.  **The bisection is transcribed here
in full**; the *endgame* diverges.  Instead of the thesis's final estimate we use
Mathlib's Morera theorem for a disc (`DifferentiableOn.isExactOn_ball`, stated for
any complete complex normed space, so it applies to `𝒜`): the nested triangles
eventually sit inside a disc contained in `dom(f)`, and there `f` has a primitive,
which kills the integral outright.  Both routes are elementary; ours is shorter
and, unlike a rectangle-to-triangle transfer, does not need Mathlib's rectangle
theorem to be moved across a region it does not cover. -/


/-- Reparametrisation: the integral along the sub-segment of `[w,w']` cut out by the
parameters `p` and `q` is the corresponding partial integral. -/
private theorem segIntegral_reparam (f : ℂ → 𝒜) (w w' : ℂ) (p q : ℝ) :
    segIntegral f (w + (p:ℂ) * (w' - w)) (w + (q:ℂ) * (w' - w))
      = (w' - w) • ∫ t in p..q, f (w + (t:ℂ) * (w' - w)) := by
  set g : ℝ → 𝒜 := fun t => f (w + (t:ℂ) * (w' - w)) with hg
  rw [segIntegral]
  have hsub : (w + (q:ℂ) * (w' - w)) - (w + (p:ℂ) * (w' - w))
      = ((q - p : ℝ) : ℂ) * (w' - w) := by push_cast; ring
  rw [hsub]
  have hfun : (fun t : ℝ =>
      f (w + (p:ℂ) * (w' - w) + (t:ℂ) * (((q - p : ℝ) : ℂ) * (w' - w))))
      = fun t : ℝ => g ((q - p) * t + p) := by
    funext t
    simp only [hg]
    congr 1
    push_cast
    ring
  rw [hfun]
  have hs : (((q - p : ℝ) : ℂ) * (w' - w)) • (∫ t in (0:ℝ)..1, g ((q - p) * t + p))
      = (w' - w) • ((q - p) • ∫ t in (0:ℝ)..1, g ((q - p) * t + p)) := by
    rw [← Complex.coe_smul, smul_smul, mul_comm]
  rw [hs, intervalIntegral.smul_integral_comp_mul_add g (q - p) p,
    show (q - p) * 0 + p = p by ring, show (q - p) * 1 + p = q by ring]

private theorem segIntegral_endpoints (f : ℂ → 𝒜) (w w' : ℂ) :
    segIntegral f w w' = (w' - w) • ∫ t in (0:ℝ)..1, f (w + (t:ℂ) * (w' - w)) := rfl

/-- Reversing a segment reverses the sign of the integral. -/
private theorem segIntegral_symm (f : ℂ → 𝒜) (w w' : ℂ) :
    segIntegral f w' w = - segIntegral f w w' := by
  have h1 : w' = w + ((1:ℝ):ℂ) * (w' - w) := by push_cast; ring
  have h0 : w = w + ((0:ℝ):ℂ) * (w' - w) := by push_cast; ring
  calc segIntegral f w' w
      = segIntegral f (w + ((1:ℝ):ℂ) * (w' - w)) (w + ((0:ℝ):ℂ) * (w' - w)) := by
        rw [← h1, ← h0]
    _ = (w' - w) • ∫ t in (1:ℝ)..0, f (w + (t:ℂ) * (w' - w)) := segIntegral_reparam f w w' 1 0
    _ = - segIntegral f w w' := by
        rw [intervalIntegral.integral_symm, smul_neg, segIntegral_endpoints]

/-- The integrand of a segment integral is continuous when `f` is continuous on the segment. -/
private theorem segIntegrand_continuousOn (f : ℂ → 𝒜) (w w' : ℂ)
    (hf : ContinuousOn f (segment ℝ w w')) :
    ContinuousOn (fun t : ℝ => f (w + (t:ℂ) * (w' - w))) (Set.Icc 0 1) := by
  refine hf.comp (Continuous.continuousOn (by fun_prop)) ?_
  intro t ht
  rw [segment_eq_image' ℝ]
  exact ⟨t, ht, by simp [Complex.real_smul]⟩

/-- Splitting a segment at an interior parameter splits the integral. -/
private theorem segIntegral_split (f : ℂ → 𝒜) (w w' : ℂ)
    (hf : ContinuousOn f (segment ℝ w w')) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    segIntegral f w w'
      = segIntegral f w (w + (s:ℂ) * (w' - w))
        + segIntegral f (w + (s:ℂ) * (w' - w)) w' := by
  obtain ⟨hs0, hs1⟩ := hs
  set g : ℝ → 𝒜 := fun t => f (w + (t:ℂ) * (w' - w)) with hg
  have hgc : ContinuousOn g (Set.Icc 0 1) := segIntegrand_continuousOn f w w' hf
  have h0 : w = w + ((0:ℝ):ℂ) * (w' - w) := by push_cast; ring
  have h1 : w' = w + ((1:ℝ):ℂ) * (w' - w) := by push_cast; ring
  have e1 : segIntegral f w (w + (s:ℂ) * (w' - w)) = (w' - w) • ∫ t in (0:ℝ)..s, g t := by
    simpa using segIntegral_reparam f w w' 0 s
  have e2 : segIntegral f (w + (s:ℂ) * (w' - w)) w' = (w' - w) • ∫ t in s..(1:ℝ), g t := by
    simpa using segIntegral_reparam f w w' s 1
  have i1 : IntervalIntegrable g MeasureTheory.volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hs0]
    exact hgc.mono (Set.Icc_subset_Icc le_rfl hs1)
  have i2 : IntervalIntegrable g MeasureTheory.volume s 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hs1]
    exact hgc.mono (Set.Icc_subset_Icc hs0 le_rfl)
  rw [e1, e2, ← smul_add, intervalIntegral.integral_add_adjacent_intervals i1 i2,
    segIntegral_endpoints]

/-- Splitting a segment at its midpoint. -/
private theorem segIntegral_split_mid (f : ℂ → 𝒜) (w w' : ℂ)
    (hf : ContinuousOn f (segment ℝ w w')) :
    segIntegral f w w' = segIntegral f w ((w + w')/2) + segIntegral f ((w + w')/2) w' := by
  have h := segIntegral_split f w w' hf (1/2) (by norm_num)
  rwa [show w + ((1/2:ℝ):ℂ) * (w' - w) = (w + w')/2 by push_cast; ring] at h

/-- The midpoint of two vertices lies in the triangle. -/
private theorem mid_mem_hull {u v : ℂ} {S : Set ℂ} (hu : u ∈ convexHull ℝ S)
    (hv : v ∈ convexHull ℝ S) : (u + v)/2 ∈ convexHull ℝ S := by
  have h := (convex_convexHull ℝ S) hu hv (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  rwa [show ((1:ℝ)/2) • u + ((1:ℝ)/2) • v = (u + v)/2 by
    rw [Complex.real_smul, Complex.real_smul]; push_cast; ring] at h

/-- **Bisection**: the triangle integral is the sum of the four integrals over the
sub-triangles cut out by the midpoints of the sides. -/
private theorem triIntegral_subdivide (f : ℂ → 𝒜) (w₀ w₁ w₂ : ℂ)
    (hf : ContinuousOn f (convexHull ℝ {w₀, w₁, w₂})) :
    triIntegral f w₀ w₁ w₂
      = triIntegral f w₀ ((w₀ + w₁)/2) ((w₀ + w₂)/2)
        + triIntegral f ((w₀ + w₁)/2) w₁ ((w₁ + w₂)/2)
        + triIntegral f ((w₀ + w₂)/2) ((w₁ + w₂)/2) w₂
        + triIntegral f ((w₀ + w₁)/2) ((w₁ + w₂)/2) ((w₀ + w₂)/2) := by
  have hmem : ∀ u : ℂ, u ∈ ({w₀, w₁, w₂} : Set ℂ) → u ∈ convexHull ℝ ({w₀, w₁, w₂} : Set ℂ) :=
    fun u hu => subset_convexHull ℝ _ hu
  have hseg : ∀ u v : ℂ, u ∈ ({w₀, w₁, w₂} : Set ℂ) → v ∈ ({w₀, w₁, w₂} : Set ℂ) →
      ContinuousOn f (segment ℝ u v) := fun u v hu hv =>
    hf.mono ((convex_convexHull ℝ _).segment_subset (hmem u hu) (hmem v hv))
  have s01 := segIntegral_split_mid f w₀ w₁ (hseg _ _ (by simp) (by simp))
  have s12 := segIntegral_split_mid f w₁ w₂ (hseg _ _ (by simp) (by simp))
  have s20 := segIntegral_split_mid f w₂ w₀ (hseg _ _ (by simp) (by simp))
  rw [show (w₂ + w₀)/2 = (w₀ + w₂)/2 by ring] at s20
  simp only [triIntegral]
  rw [s01, s12, s20,
    segIntegral_symm f ((w₀ + w₁)/2) ((w₀ + w₂)/2),
    segIntegral_symm f ((w₁ + w₂)/2) ((w₀ + w₁)/2),
    segIntegral_symm f ((w₀ + w₂)/2) ((w₁ + w₂)/2)]
  abel

/-- If `f` has a primitive on a convex set, the segment integral telescopes. -/
private theorem segIntegral_of_primitive (f F : ℂ → 𝒜) {V : Set ℂ} (hV : Convex ℝ V)
    (hFf : ∀ z ∈ V, HasDerivAt F (f z) z) (hfc : ContinuousOn f V)
    {w w' : ℂ} (hw : w ∈ V) (hw' : w' ∈ V) :
    segIntegral f w w' = F w' - F w := by
  have hmaps : ∀ t ∈ Set.uIcc (0:ℝ) 1, w + (t:ℂ) * (w' - w) ∈ V := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have := hV.segment_subset hw hw'
    refine this ?_
    rw [segment_eq_image' ℝ]
    exact ⟨t, ht, by simp [Complex.real_smul]⟩
  have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w + (s:ℂ) * (w' - w)) (w' - w) t := by
    intro t
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (w' - w)).const_add w
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => F (w + (s:ℂ) * (w' - w)))
        ((w' - w) • f (w + (t:ℂ) * (w' - w))) t := by
    intro t ht
    exact (hFf _ (hmaps t ht)).scomp t (hγ t)
  have hcont : ContinuousOn (fun t : ℝ => (w' - w) • f (w + (t:ℂ) * (w' - w)))
      (Set.uIcc (0:ℝ) 1) := by
    refine ContinuousOn.const_smul ?_ _
    refine hfc.comp (Continuous.continuousOn (by fun_prop)) ?_
    exact fun t ht => hmaps t ht
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [segIntegral_endpoints, ← intervalIntegral.integral_smul, hFTC]
  norm_num

/-- If `f` has a primitive on a convex set containing the triangle, the triangle
integral vanishes. -/
private theorem triIntegral_of_primitive (f F : ℂ → 𝒜) {V : Set ℂ} (hV : Convex ℝ V)
    (hFf : ∀ z ∈ V, HasDerivAt F (f z) z) (hfc : ContinuousOn f V)
    {w₀ w₁ w₂ : ℂ} (h0 : w₀ ∈ V) (h1 : w₁ ∈ V) (h2 : w₂ ∈ V) :
    triIntegral f w₀ w₁ w₂ = 0 := by
  rw [triIntegral, segIntegral_of_primitive f F hV hFf hfc h0 h1,
    segIntegral_of_primitive f F hV hFf hfc h1 h2,
    segIntegral_of_primitive f F hV hFf hfc h2 h0]
  abel

/-- **Goursat inside a disc**: the case of the theorem that Mathlib's Morera theorem
(`DifferentiableOn.isExactOn_ball`) settles outright. -/
private theorem triIntegral_eq_zero_of_ball (f : ℂ → 𝒜) (c : ℂ) (r : ℝ)
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    {w₀ w₁ w₂ : ℂ} (h0 : w₀ ∈ Metric.ball c r) (h1 : w₁ ∈ Metric.ball c r)
    (h2 : w₂ ∈ Metric.ball c r) :
    triIntegral f w₀ w₁ w₂ = 0 := by
  obtain ⟨F, hF⟩ := hf.isExactOn_ball
  exact triIntegral_of_primitive f F (convex_ball c r) hF hf.continuousOn h0 h1 h2

/-- The longest side of a triangle. -/
private noncomputable def triSideMax (u₀ u₁ u₂ : ℂ) : ℝ :=
  max (dist u₀ u₁) (max (dist u₁ u₂) (dist u₂ u₀))

private theorem dist_half_le {a b c d : ℂ} {S : ℝ} (h : a - b = (c - d)/2)
    (hcd : dist c d ≤ S) : dist a b ≤ S/2 := by
  have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [dist_eq_norm] at hcd
  rw [dist_eq_norm, h, norm_div, h2]
  linarith

private theorem sub_triangle_ok {u₀ u₁ u₂ v₀ v₁ v₂ : ℂ}
    (hm0 : v₀ ∈ convexHull ℝ ({u₀, u₁, u₂} : Set ℂ))
    (hm1 : v₁ ∈ convexHull ℝ ({u₀, u₁, u₂} : Set ℂ))
    (hm2 : v₂ ∈ convexHull ℝ ({u₀, u₁, u₂} : Set ℂ))
    (d0 : dist v₀ v₁ ≤ triSideMax u₀ u₁ u₂ / 2)
    (d1 : dist v₁ v₂ ≤ triSideMax u₀ u₁ u₂ / 2)
    (d2 : dist v₂ v₀ ≤ triSideMax u₀ u₁ u₂ / 2) :
    convexHull ℝ ({v₀, v₁, v₂} : Set ℂ) ⊆ convexHull ℝ ({u₀, u₁, u₂} : Set ℂ)
      ∧ triSideMax v₀ v₁ v₂ ≤ triSideMax u₀ u₁ u₂ / 2 := by
  refine ⟨convexHull_min ?_ (convex_convexHull ℝ _), max_le d0 (max_le d1 d2)⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

/-- One bisection step: among the four sub-triangles there is one carrying at least a
quarter of the integral, contained in the parent and with half its longest side. -/
private theorem exists_subtriangle (f : ℂ → 𝒜) (u₀ u₁ u₂ : ℂ)
    (hf : ContinuousOn f (convexHull ℝ ({u₀, u₁, u₂} : Set ℂ))) :
    ∃ v : ℂ × ℂ × ℂ,
      convexHull ℝ ({v.1, v.2.1, v.2.2} : Set ℂ) ⊆ convexHull ℝ ({u₀, u₁, u₂} : Set ℂ) ∧
      triSideMax v.1 v.2.1 v.2.2 ≤ triSideMax u₀ u₁ u₂ / 2 ∧
      ‖triIntegral f u₀ u₁ u₂‖ ≤ 4 * ‖triIntegral f v.1 v.2.1 v.2.2‖ := by
  set S := triSideMax u₀ u₁ u₂ with hS
  have hd01 : dist u₀ u₁ ≤ S := le_max_left _ _
  have hd12 : dist u₁ u₂ ≤ S := le_trans (le_max_left _ _) (le_max_right _ _)
  have hd20 : dist u₂ u₀ ≤ S := le_trans (le_max_right _ _) (le_max_right _ _)
  have hd10 : dist u₁ u₀ ≤ S := by rw [dist_comm]; exact hd01
  have hd21 : dist u₂ u₁ ≤ S := by rw [dist_comm]; exact hd12
  have hd02 : dist u₀ u₂ ≤ S := by rw [dist_comm]; exact hd20
  set p := (u₀ + u₁)/2 with hp
  set q := (u₁ + u₂)/2 with hq
  set r := (u₀ + u₂)/2 with hr
  have e0 : u₀ ∈ convexHull ℝ ({u₀, u₁, u₂} : Set ℂ) := subset_convexHull ℝ _ (by simp)
  have e1 : u₁ ∈ convexHull ℝ ({u₀, u₁, u₂} : Set ℂ) := subset_convexHull ℝ _ (by simp)
  have e2 : u₂ ∈ convexHull ℝ ({u₀, u₁, u₂} : Set ℂ) := subset_convexHull ℝ _ (by simp)
  have ep : p ∈ convexHull ℝ ({u₀, u₁, u₂} : Set ℂ) := mid_mem_hull e0 e1
  have eq' : q ∈ convexHull ℝ ({u₀, u₁, u₂} : Set ℂ) := mid_mem_hull e1 e2
  have er : r ∈ convexHull ℝ ({u₀, u₁, u₂} : Set ℂ) := mid_mem_hull e0 e2
  have hA := sub_triangle_ok e0 ep er
    (dist_half_le (by rw [hp]; ring) hd01) (dist_half_le (by rw [hp, hr]; ring) hd12)
    (dist_half_le (by rw [hr]; ring) hd20)
  have hB := sub_triangle_ok ep e1 eq'
    (dist_half_le (by rw [hp]; ring) hd01) (dist_half_le (by rw [hq]; ring) hd12)
    (dist_half_le (by rw [hp, hq]; ring) hd20)
  have hC := sub_triangle_ok er eq' e2
    (dist_half_le (by rw [hr, hq]; ring) hd01) (dist_half_le (by rw [hq]; ring) hd12)
    (dist_half_le (by rw [hr]; ring) hd20)
  have hD := sub_triangle_ok ep eq' er
    (dist_half_le (by rw [hp, hq]; ring) hd02) (dist_half_le (by rw [hq, hr]; ring) hd10)
    (dist_half_le (by rw [hr, hp]; ring) hd21)
  have hsub := triIntegral_subdivide f u₀ u₁ u₂ hf
  rw [← hp, ← hq, ← hr] at hsub
  have hquarter : ‖triIntegral f u₀ u₁ u₂‖ ≤ 4 * ‖triIntegral f u₀ p r‖ ∨
      ‖triIntegral f u₀ u₁ u₂‖ ≤ 4 * ‖triIntegral f p u₁ q‖ ∨
      ‖triIntegral f u₀ u₁ u₂‖ ≤ 4 * ‖triIntegral f r q u₂‖ ∨
      ‖triIntegral f u₀ u₁ u₂‖ ≤ 4 * ‖triIntegral f p q r‖ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha, hb, hc, hd⟩ := hcon
    have t1 := norm_add_le (triIntegral f u₀ p r + triIntegral f p u₁ q
      + triIntegral f r q u₂) (triIntegral f p q r)
    have t2 := norm_add_le (triIntegral f u₀ p r + triIntegral f p u₁ q)
      (triIntegral f r q u₂)
    have t3 := norm_add_le (triIntegral f u₀ p r) (triIntegral f p u₁ q)
    rw [hsub] at ha hb hc hd
    linarith
  rcases hquarter with h | h | h | h
  · exact ⟨(u₀, p, r), hA.1, hA.2, h⟩
  · exact ⟨(p, u₁, q), hB.1, hB.2, h⟩
  · exact ⟨(r, q, u₂), hC.1, hC.2, h⟩
  · exact ⟨(p, q, r), hD.1, hD.2, h⟩

private theorem hull_subset_closedBall (v₀ v₁ v₂ : ℂ) :
    convexHull ℝ ({v₀, v₁, v₂} : Set ℂ) ⊆ Metric.closedBall v₀ (triSideMax v₀ v₁ v₂) := by
  refine convexHull_min ?_ (convex_closedBall _ _)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · refine Metric.mem_closedBall.mpr ?_
    rw [dist_self]
    exact le_trans dist_nonneg (le_max_left (dist x v₁) _)
  · exact Metric.mem_closedBall.mpr (by rw [dist_comm]; exact le_max_left _ _)
  · exact Metric.mem_closedBall.mpr
      (le_trans (le_max_right _ _) (le_max_right _ _))

/-- **14IV** (`goursat`, cstar.tex:2178, Goursat's Theorem): `∫_T f = 0` for
a holomorphic 𝒜-valued function `f` and a triangle `T` whose closure (convex
hull of its vertices) lies inside `dom(f)`. -/
theorem goursat {U : Set ℂ} (hU : IsOpen U) (f : ℂ → 𝒜)
    (hf : DifferentiableOn ℂ f U) (w₀ w₁ w₂ : ℂ)
    (hT : convexHull ℝ {w₀, w₁, w₂} ⊆ U) :
    triIntegral f w₀ w₁ w₂ = 0 := by
  set K : Set ℂ := convexHull ℝ ({w₀, w₁, w₂} : Set ℂ) with hK
  set S₀ : ℝ := triSideMax w₀ w₁ w₂ with hS₀
  have hS₀0 : 0 ≤ S₀ := le_trans dist_nonneg (le_max_left (dist w₀ w₁) _)
  -- a total bisection step
  have key : ∀ P : ℂ × ℂ × ℂ, ∃ v : ℂ × ℂ × ℂ,
      convexHull ℝ ({P.1, P.2.1, P.2.2} : Set ℂ) ⊆ K →
        (convexHull ℝ ({v.1, v.2.1, v.2.2} : Set ℂ)
            ⊆ convexHull ℝ ({P.1, P.2.1, P.2.2} : Set ℂ) ∧
          triSideMax v.1 v.2.1 v.2.2 ≤ triSideMax P.1 P.2.1 P.2.2 / 2 ∧
          ‖triIntegral f P.1 P.2.1 P.2.2‖ ≤ 4 * ‖triIntegral f v.1 v.2.1 v.2.2‖) := by
    intro P
    by_cases hc : convexHull ℝ ({P.1, P.2.1, P.2.2} : Set ℂ) ⊆ K
    · obtain ⟨v, hv⟩ := exists_subtriangle f P.1 P.2.1 P.2.2
        (hf.continuousOn.mono (hc.trans hT))
      exact ⟨v, fun _ => hv⟩
    · exact ⟨P, fun h => absurd h hc⟩
  choose F hF using key
  set T : ℕ → ℂ × ℂ × ℂ := fun n => F^[n] (w₀, w₁, w₂) with hTdef
  have hT0 : T 0 = (w₀, w₁, w₂) := rfl
  have hTsucc : ∀ n, T (n + 1) = F (T n) := fun n => Function.iterate_succ_apply' F n _
  have hsub : ∀ n, convexHull ℝ ({(T n).1, (T n).2.1, (T n).2.2} : Set ℂ) ⊆ K := by
    intro n
    induction n with
    | zero => exact subset_rfl
    | succ n ih => rw [hTsucc n]; exact ((hF (T n)) ih).1.trans ih
  have hstep : ∀ n, convexHull ℝ ({(T (n+1)).1, (T (n+1)).2.1, (T (n+1)).2.2} : Set ℂ)
      ⊆ convexHull ℝ ({(T n).1, (T n).2.1, (T n).2.2} : Set ℂ) := by
    intro n; rw [hTsucc n]; exact ((hF (T n)) (hsub n)).1
  have hside : ∀ n, triSideMax (T n).1 (T n).2.1 (T n).2.2 ≤ S₀ / 2 ^ n := by
    intro n
    induction n with
    | zero => rw [hT0]; simp [hS₀]
    | succ n ih =>
        have h := ((hF (T n)) (hsub n)).2.1
        rw [hTsucc n]
        rw [pow_succ]
        rw [← div_div]
        calc triSideMax (F (T n)).1 (F (T n)).2.1 (F (T n)).2.2
            ≤ triSideMax (T n).1 (T n).2.1 (T n).2.2 / 2 := h
          _ ≤ (S₀ / 2 ^ n) / 2 := by linarith
  have hnorm : ∀ n, ‖triIntegral f w₀ w₁ w₂‖
      ≤ 4 ^ n * ‖triIntegral f (T n).1 (T n).2.1 (T n).2.2‖ := by
    intro n
    induction n with
    | zero => rw [hT0]; simp
    | succ n ih =>
        have h := ((hF (T n)) (hsub n)).2.2
        rw [hTsucc n, pow_succ]
        have h4 : (0:ℝ) ≤ 4 ^ n := by positivity
        nlinarith [ih, h, h4]
  -- the first vertices form a Cauchy sequence
  set a : ℕ → ℂ := fun n => (T n).1 with ha
  have hmem : ∀ n, a n ∈ convexHull ℝ ({(T n).1, (T n).2.1, (T n).2.2} : Set ℂ) :=
    fun n => subset_convexHull ℝ _ (by simp [ha])
  have hcauchyBound : ∀ n, dist (a n) (a (n + 1)) ≤ (2 * S₀) / 2 / 2 ^ n := by
    intro n
    have h1 : a (n + 1) ∈ convexHull ℝ ({(T n).1, (T n).2.1, (T n).2.2} : Set ℂ) :=
      hstep n (hmem (n + 1))
    have h2 := hull_subset_closedBall (T n).1 (T n).2.1 (T n).2.2 h1
    rw [Metric.mem_closedBall, dist_comm] at h2
    have := hside n
    calc dist (a n) (a (n + 1)) ≤ triSideMax (T n).1 (T n).2.1 (T n).2.2 := h2
      _ ≤ S₀ / 2 ^ n := this
      _ = (2 * S₀) / 2 / 2 ^ n := by ring
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hcauchyBound)
  have hdistz : ∀ n, dist (a n) z ≤ (2 * S₀) / 2 ^ n :=
    fun n => dist_le_of_le_geometric_two_of_tendsto hcauchyBound hz n
  -- the limit lies in the triangle, hence in `U`
  have hzK : z ∈ K :=
    ((Set.toFinite _).isClosed_convexHull ℝ).mem_of_tendsto hz
      (Filter.Eventually.of_forall fun n => hsub n (hmem n))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU z (hT hzK)
  -- for `n` large the `n`-th triangle sits inside that ball
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < δ / (3 * S₀ + 1) by positivity)
    (show (1:ℝ)/2 < 1 by norm_num)
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  have hc0 : (0:ℝ) < 3 * S₀ + 1 := by linarith
  have hn' : (3 * S₀ + 1) / 2 ^ n < δ := by
    rw [div_pow, one_pow, lt_div_iff₀ hc0] at hn
    have h3 := mul_lt_mul_of_pos_right hn hpow
    rw [div_lt_iff₀ hpow]
    calc 3 * S₀ + 1 = 1 / 2 ^ n * (3 * S₀ + 1) * 2 ^ n := by field_simp
      _ < δ * 2 ^ n := h3
  have hin : convexHull ℝ ({(T n).1, (T n).2.1, (T n).2.2} : Set ℂ) ⊆ Metric.ball z δ := by
    intro x hx
    have h2 := hull_subset_closedBall (T n).1 (T n).2.1 (T n).2.2 hx
    rw [Metric.mem_closedBall] at h2
    have h3 := hside n
    have h4 : dist (T n).1 z ≤ (2 * S₀) / 2 ^ n := hdistz n
    have h5 : dist x z ≤ dist x (T n).1 + dist (T n).1 z := dist_triangle _ _ _
    have h6 : S₀ / 2 ^ n + (2 * S₀) / 2 ^ n ≤ (3 * S₀ + 1) / 2 ^ n := by
      have hinv : (0:ℝ) < 1 / 2 ^ n := by positivity
      have e1 : S₀ / 2 ^ n = S₀ * (1 / 2 ^ n) := by ring
      have e2 : (2 * S₀) / 2 ^ n = (2 * S₀) * (1 / 2 ^ n) := by ring
      have e3 : (3 * S₀ + 1) / 2 ^ n = (3 * S₀ + 1) * (1 / 2 ^ n) := by ring
      rw [e1, e2, e3]
      nlinarith [hinv]
    exact Metric.mem_ball.mpr (by linarith)
  have hzero : triIntegral f (T n).1 (T n).2.1 (T n).2.2 = 0 :=
    triIntegral_eq_zero_of_ball f z δ (hf.mono hball) (hin (hmem n))
      (hin (subset_convexHull ℝ _ (by simp))) (hin (subset_convexHull ℝ _ (by simp)))
  have hfin := hnorm n
  rw [hzero, norm_zero, mul_zero] at hfin
  exact norm_le_zero_iff.mp hfin


/-- **14VIII** (`invint`, cstar.tex:2303, Exercise), part 1: for a non-zero
complex number `z`, `z⁻¹ = (Re z - i Im z)/(Re z² + Im z²)`. -/
theorem invint_1 (z : ℂ) (hz : z ≠ 0) :
    z⁻¹ = ((z.re : ℂ) - (z.im : ℂ) * Complex.I) /
      ((z.re : ℂ) ^ 2 + (z.im : ℂ) ^ 2) :=
  by
    -- the solution's computation (asols.tex, `parsec-140.80`(1)): `z̄ z = |z|²`,
    -- so `z · (z̄ |z|⁻²) = 1` and hence `z⁻¹ = z̄ (|z|²)⁻¹`; the identity then
    -- follows from `z̄ = Re z - i Im z` and `|z|² = Re z² + Im z²`.
    have hconj : ((z.re : ℂ) - (z.im : ℂ) * Complex.I) = (starRingEnd ℂ) z := by
      apply Complex.ext <;> simp
    have hsq : ((z.re : ℂ) ^ 2 + (z.im : ℂ) ^ 2) = (starRingEnd ℂ) z * z := by
      apply Complex.ext <;>
        simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring
    have hne : ((z.re : ℂ) ^ 2 + (z.im : ℂ) ^ 2) ≠ 0 := by
      rw [hsq]
      exact mul_ne_zero (by simpa using hz) hz
    rw [eq_div_iff hne, hsq, hconj, mul_comm ((starRingEnd ℂ) z) z, ← mul_assoc,
      inv_mul_cancel₀ hz, one_mul]

/-! **Divergence from the thesis, recorded here for part 3 of 14VIII.**
The thesis's route is 2 → 3 → 4: it computes the two axis-parallel segment
integrals by hand and then reduces the general segment to those *using Goursat's
Theorem* ("using Goursat's Theorem one may reduce the problem to horizontal and
vertical line segments", cstar.tex:2364).  Parts 2 and 2′ below are the thesis's
own computation and part 4 is the thesis's own argument from part 3; what
diverges is the step 2 → 3, where **Goursat is not used at all**: part 3 is
proved directly.  (The thesis's hint is a single sentence and does not say how
to treat a `z₀` inside the axis-parallel triangle spanned by `[w,w']`, which a
reduction to horizontal and vertical segments has to subdivide around.)
The observation that makes the direct proof work is that if `z₀`
misses the segment `[w,w']` then the rescaled segment from `1` to
`ζ := (w'-z₀)/(w-z₀)` misses not merely `0` but the whole branch cut `(-∞,0]`
(`affine_mem_slitPlane` below), so `Complex.log` is a genuine antiderivative of
`z⁻¹` along it and the fundamental theorem of calculus applies in one step.
Both routes are elementary; the thesis's is not wrong, only more expensive. -/

/-- Auxiliary for **14VIII**.3: if the segment from `1` to `ζ` misses `0`, then
it misses the whole branch cut `(-∞,0]` of `Complex.log`.  (Along the segment
the imaginary part is `t·Im ζ`; where that vanishes either `t = 0`, giving the
point `1`, or `ζ` is real — and a real `ζ ≤ 0` would put `0` on the segment.) -/
private theorem affine_mem_slitPlane {ζ : ℂ}
    (hζ : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 → (1:ℂ) + (s : ℂ) * (ζ - 1) ≠ 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (1 : ℂ) + (t : ℂ) * (ζ - 1) ∈ Complex.slitPlane := by
  obtain ⟨ht0, ht1⟩ := ht
  by_contra hc
  rw [Complex.mem_slitPlane_iff, not_or, not_lt, not_not] at hc
  obtain ⟨hre, him⟩ := hc
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    zero_mul, sub_zero, add_zero, zero_add] at hre him
  have him' : t * ζ.im = 0 := him
  have hre' : 1 + t * (ζ.re - 1) ≤ 0 := hre
  have ht0' : t ≠ 0 := by
    rintro rfl; simp at hre'; linarith
  have hzim : ζ.im = 0 := by
    rcases mul_eq_zero.mp him' with h | h
    · exact absurd h ht0'
    · exact h
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ζ = (c : ℂ) :=
    ⟨ζ.re, Complex.ext (by simp) (by simp [hzim])⟩
  have hcre : ζ.re = c := by rw [hc]; simp
  rw [hcre] at hre'
  have hc0 : c ≤ 0 := by nlinarith
  have h1c : (0:ℝ) < 1 - c := by linarith
  have hcne : ((1 - c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h1c)
  have h1c' : (1 : ℂ) - (c : ℂ) ≠ 0 := by push_cast at hcne; exact hcne
  refine hζ (1 / (1 - c)) ⟨by positivity, by rw [div_le_one h1c]; linarith⟩ ?_
  rw [hc]
  push_cast
  field_simp
  ring

/-- The content of **14VIII**.3: `∫_w^{w'} (z-z₀)⁻¹ dz = Log((w'-z₀)/(w-z₀))`.
(Parts 2 and 2′ are its `z₀ = 0` case, but are proved on their own, the thesis's
way; part 4 is the thesis's own argument from part 3.) -/
private theorem segment_inv_integral (w w' z₀ : ℂ) (hz₀ : z₀ ∉ segment ℝ w w') :
    segIntegral (fun z => (z - z₀)⁻¹) w w' =
      (measuredAngle w z₀ w' : ℂ) * Complex.I +
        (Real.log (‖w' - z₀‖ / ‖w - z₀‖) : ℂ) := by
  have hu : w - z₀ ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hz₀ (h ▸ left_mem_segment ℝ w w')
  set ζ : ℂ := (w' - z₀) / (w - z₀) with hζdef
  have hvu : (w' - z₀) = ζ * (w - z₀) := by rw [hζdef]; field_simp
  have hww : w' - w = (w - z₀) * (ζ - 1) := by
    have h : w' - w = (w' - z₀) - (w - z₀) := by ring
    rw [h, hvu]; ring
  -- the affine path `p t = 1 + t (ζ - 1)` misses `0`, since a zero of it would
  -- exhibit `z₀` as a point of `[w,w']`
  have hpne : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 → (1:ℂ) + (s : ℂ) * (ζ - 1) ≠ 0 := by
    intro s hs hzero
    refine hz₀ ?_
    rw [segment_eq_image' ℝ w w']
    refine ⟨s, hs, ?_⟩
    have hexp : w + (s:ℝ) • (w' - w) - z₀ = (w - z₀) * ((1:ℂ) + (s : ℂ) * (ζ - 1)) := by
      rw [Complex.real_smul, hww]; ring
    rw [hzero, mul_zero, sub_eq_zero] at hexp
    exact hexp
  -- so `Log ∘ p` is an antiderivative of the integrand
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => Complex.log ((1:ℂ) + (s : ℂ) * (ζ - 1)))
        ((ζ - 1) / ((1:ℂ) + (t : ℂ) * (ζ - 1))) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1 : HasDerivAt (fun s : ℝ => (1:ℂ) + (s : ℂ) * (ζ - 1)) (ζ - 1) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (ζ - 1)).const_add (1:ℂ)
    exact h1.clog_real (affine_mem_slitPlane hpne ht)
  have hcont : ContinuousOn
      (fun t : ℝ => (ζ - 1) / ((1:ℂ) + (t : ℂ) * (ζ - 1))) (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · fun_prop
    · intro t ht; exact hpne t ht
  have hFTC : (∫ t in (0:ℝ)..1, (ζ - 1) / ((1:ℂ) + (t : ℂ) * (ζ - 1)))
      = Complex.log ζ := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    simp
  have hrw : ∀ t : ℝ, (w' - w) * ((w + (t:ℂ) * (w' - w) - z₀)⁻¹)
      = (ζ - 1) / ((1:ℂ) + (t : ℂ) * (ζ - 1)) := by
    intro t
    have hfac : w + (t:ℂ) * (w' - w) - z₀ = (w - z₀) * ((1:ℂ) + (t : ℂ) * (ζ - 1)) := by
      rw [hww]; ring
    rw [hfac, hww, mul_inv, div_eq_mul_inv]
    field_simp
  have hseg : segIntegral (fun z => (z - z₀)⁻¹) w w' = Complex.log ζ := by
    rw [segIntegral, smul_eq_mul, ← hFTC, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => hrw t
  rw [hseg, Complex.log, measuredAngle, ← hζdef, norm_div]
  ring

/-- **14VIII** (`invint`, cstar.tex:2303, Exercise), part 2 (vertical
segment): `∫_a^{a+ib} z⁻¹ dz = i arctan(b/a) + log|a+ib| - log|ia|` for real
`a ≠ 0` and `b`. -/
theorem invint_2 (a b : ℝ) (ha : a ≠ 0) :
    segIntegral (fun z : ℂ => z⁻¹) (a : ℂ) ((a : ℂ) + (b : ℂ) * Complex.I) =
      (Real.arctan (b / a) : ℂ) * Complex.I +
        (Real.log ‖(a : ℂ) + (b : ℂ) * Complex.I‖ : ℂ) -
        (Real.log ‖(a : ℂ) * Complex.I‖ : ℂ) :=
  by
    -- The thesis's own computation (cstar.tex:2320): parametrise the segment,
    -- read off the integrand from part 1, and integrate the antiderivative
    -- `½log(a² + t²b²) + i arctan(tb/a)`.  (An earlier proof took this as the
    -- `z₀ = 0` case of part 3, reversing the thesis's dependency order — the
    -- thesis derives part 3 *from* part 2 using Goursat.)
    have ha2 : (0 : ℝ) < a ^ 2 := by positivity
    set D : ℝ → ℝ := fun t => a ^ 2 + t ^ 2 * b ^ 2 with hD
    have hDpos : ∀ t : ℝ, 0 < D t := by
      intro t; rw [hD]; nlinarith [sq_nonneg (t * b)]
    have hne : ∀ t : ℝ, ((a : ℂ) + (t : ℂ) * ((b : ℂ) * Complex.I)) ≠ 0 := by
      intro t h
      have hre := congrArg Complex.re h
      simp at hre
      exact ha hre
    set G : ℝ → ℂ := fun t => ((b : ℂ) * Complex.I) *
        ((a : ℂ) + (t : ℂ) * ((b : ℂ) * Complex.I))⁻¹ with hG
    set F : ℝ → ℂ := fun t => ((Real.log (D t) / 2 : ℝ) : ℂ)
        + ((Real.arctan (t * b / a) : ℝ) : ℂ) * Complex.I with hF
    have hderiv : ∀ t : ℝ, HasDerivAt F (G t) t := by
      intro t
      have hd : HasDerivAt D (2 * t * b ^ 2) t := by
        have h := (((hasDerivAt_pow 2 t).mul_const (b ^ 2)).const_add (a ^ 2))
        simpa [hD] using h
      have h1 : HasDerivAt (fun t : ℝ => Real.log (D t) / 2) (t * b ^ 2 / D t) t := by
        have h := (Real.hasDerivAt_log (hDpos t).ne').comp t hd
        have h2 := h.div_const 2
        refine h2.congr_deriv ?_
        field_simp
      have h2 : HasDerivAt (fun t : ℝ => Real.arctan (t * b / a)) (a * b / D t) t := by
        have hin : HasDerivAt (fun t : ℝ => t * b / a) (b / a) t := by
          have h := ((hasDerivAt_id t).mul_const b).div_const a
          simpa using h
        have h := (Real.hasDerivAt_arctan (t * b / a)).comp t hin
        refine h.congr_deriv ?_
        rw [hD]
        field_simp
      have hsum := (h1.ofReal_comp).add ((h2.ofReal_comp).mul_const Complex.I)
      refine hsum.congr_deriv ?_
      rw [hG, eq_comm, mul_inv_eq_iff_eq_mul₀ (hne t)]
      have hDne : D t ≠ 0 := (hDpos t).ne'
      rw [Complex.ext_iff]
      constructor <;>
        · simp only [hD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
            zero_mul, add_zero, zero_add, sub_self]
          field_simp
          ring
    have hGcont : Continuous G := by
      rw [hG]
      exact continuous_const.mul (Continuous.inv₀ (by fun_prop) hne)
    have hint : ∫ t in (0 : ℝ)..1, G t = F 1 - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
        (hGcont.intervalIntegrable 0 1)
    have hseg : segIntegral (fun z : ℂ => z⁻¹) (a : ℂ) ((a : ℂ) + (b : ℂ) * Complex.I)
        = ∫ t in (0 : ℝ)..1, G t := by
      rw [segIntegral, hG]
      have hsub : ((a : ℂ) + (b : ℂ) * Complex.I) - (a : ℂ) = (b : ℂ) * Complex.I := by ring
      rw [hsub, smul_eq_mul, intervalIntegral.integral_const_mul]
    have hlogsq : ∀ z : ℂ, Real.log ‖z‖ = Real.log (‖z‖ ^ 2) / 2 := by
      intro z
      rw [Real.log_pow]
      push_cast
      ring
    have hn1 : ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have hn2 : ‖(a : ℂ) * Complex.I‖ ^ 2 = a ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    rw [hseg, hint, hF, hlogsq ((a : ℂ) + (b : ℂ) * Complex.I), hlogsq ((a : ℂ) * Complex.I),
      hn1, hn2]
    simp only [hD]
    norm_num [Real.arctan_zero]
    ring

/-- **14VIII** (`invint`, cstar.tex:2303, Exercise), part 2 (horizontal
segment): `∫_{a+ib}^{ib} z⁻¹ dz = i arctan(a/b) + log|ib| - log|a+ib|` for
real `a` and `b ≠ 0`. -/
theorem invint_2' (a b : ℝ) (hb : b ≠ 0) :
    segIntegral (fun z : ℂ => z⁻¹) ((a : ℂ) + (b : ℂ) * Complex.I)
        ((b : ℂ) * Complex.I) =
      (Real.arctan (a / b) : ℂ) * Complex.I +
        (Real.log ‖(b : ℂ) * Complex.I‖ : ℂ) -
        (Real.log ‖(a : ℂ) + (b : ℂ) * Complex.I‖ : ℂ) :=
  by
    -- The thesis's own computation again, with antiderivative
    -- `½log(a²(1-t)² + b²) - i arctan(a(1-t)/b)`.
    have hb2 : (0 : ℝ) < b ^ 2 := by positivity
    set D : ℝ → ℝ := fun t => (a - t * a) ^ 2 + b ^ 2 with hD
    have hDpos : ∀ t : ℝ, 0 < D t := by
      intro t; rw [hD]; nlinarith [sq_nonneg (a - t * a)]
    have hne : ∀ t : ℝ, (((a : ℂ) - (t : ℂ) * (a : ℂ)) + (b : ℂ) * Complex.I) ≠ 0 := by
      intro t h
      have him := congrArg Complex.im h
      simp at him
      exact hb him
    set G : ℝ → ℂ := fun t => (-(a : ℂ)) *
        (((a : ℂ) - (t : ℂ) * (a : ℂ)) + (b : ℂ) * Complex.I)⁻¹ with hG
    set F : ℝ → ℂ := fun t => ((Real.log (D t) / 2 : ℝ) : ℂ)
        - ((Real.arctan ((a - t * a) / b) : ℝ) : ℂ) * Complex.I with hF
    have hderiv : ∀ t : ℝ, HasDerivAt F (G t) t := by
      intro t
      have hlin : HasDerivAt (fun t : ℝ => a - t * a) (-a) t := by
        have h := ((hasDerivAt_id t).mul_const a).const_sub a
        simpa using h
      have hd : HasDerivAt D (2 * (a - t * a) * (-a)) t := by
        have h := ((hlin.pow 2).add_const (b ^ 2))
        simpa [hD] using h
      have h1 : HasDerivAt (fun t : ℝ => Real.log (D t) / 2) (-(a * (a - t * a)) / D t) t := by
        have h := (Real.hasDerivAt_log (hDpos t).ne').comp t hd
        have h2 := h.div_const 2
        refine h2.congr_deriv ?_
        field_simp
      have h2 : HasDerivAt (fun t : ℝ => Real.arctan ((a - t * a) / b)) (-(a * b) / D t) t := by
        have hin : HasDerivAt (fun t : ℝ => (a - t * a) / b) (-a / b) t := hlin.div_const b
        have h := (Real.hasDerivAt_arctan ((a - t * a) / b)).comp t hin
        refine h.congr_deriv ?_
        rw [hD]
        field_simp
        ring
      have hsum := (h1.ofReal_comp).sub ((h2.ofReal_comp).mul_const Complex.I)
      refine hsum.congr_deriv ?_
      rw [hG, eq_comm, mul_inv_eq_iff_eq_mul₀ (hne t)]
      have hDne : D t ≠ 0 := (hDpos t).ne'
      rw [Complex.ext_iff]
      constructor <;>
        · simp only [hD, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
            Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
            Complex.I_im, Complex.neg_re, Complex.neg_im, mul_zero, mul_one, zero_mul, add_zero,
            zero_add, sub_self, neg_zero, sub_zero]
          field_simp
          ring
    have hGcont : Continuous G := by
      rw [hG]
      exact continuous_const.mul (Continuous.inv₀ (by fun_prop) hne)
    have hint : ∫ t in (0 : ℝ)..1, G t = F 1 - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
        (hGcont.intervalIntegrable 0 1)
    have hseg : segIntegral (fun z : ℂ => z⁻¹) ((a : ℂ) + (b : ℂ) * Complex.I) ((b : ℂ) * Complex.I)
        = ∫ t in (0 : ℝ)..1, G t := by
      rw [segIntegral, hG]
      have hsub : ((b : ℂ) * Complex.I) - ((a : ℂ) + (b : ℂ) * Complex.I) = -(a : ℂ) := by ring
      rw [hsub, smul_eq_mul]
      have hfun : (fun t : ℝ => ((a : ℂ) + (b : ℂ) * Complex.I + (t : ℂ) * (-(a : ℂ)))⁻¹)
          = fun t : ℝ => (((a : ℂ) - (t : ℂ) * (a : ℂ)) + (b : ℂ) * Complex.I)⁻¹ := by
        funext t; congr 1; ring
      rw [hfun, intervalIntegral.integral_const_mul]
    have hlogsq : ∀ z : ℂ, Real.log ‖z‖ = Real.log (‖z‖ ^ 2) / 2 := by
      intro z
      rw [Real.log_pow]
      push_cast
      ring
    have hn1 : ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have hn2 : ‖(b : ℂ) * Complex.I‖ ^ 2 = b ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    rw [hseg, hint, hF, hlogsq ((a : ℂ) + (b : ℂ) * Complex.I), hlogsq ((b : ℂ) * Complex.I),
      hn1, hn2]
    simp only [hD]
    norm_num [Real.arctan_zero]
    ring

/-- **14VIII** (`invint`, cstar.tex:2303, Exercise), part 3:
`∫_w^{w'} (z - z₀)⁻¹ dz = i ∠(w, z₀, w') + log(|w' - z₀|/|w - z₀|)` when
`z₀ ∉ [w, w']`. -/
theorem invint_3 (w w' z₀ : ℂ) (hz₀ : z₀ ∉ segment ℝ w w') :
    segIntegral (fun z => (z - z₀)⁻¹) w w' =
      (measuredAngle w z₀ w' : ℂ) * Complex.I +
        (Real.log (‖w' - z₀‖ / ‖w - z₀‖) : ℂ) :=
  -- proved without Goursat; see the divergence note above `affine_mem_slitPlane`
  segment_inv_integral w w' z₀ hz₀

/-- **14VIII** (`invint`, cstar.tex:2303, Exercise), part 4:
`(2πi)⁻¹ ∫_T (z - z₀)⁻¹ dz = wn_T(z₀)` for a triangle `T` and a point `z₀`
off its boundary. -/
theorem invint_4 (w₀ w₁ w₂ z₀ : ℂ)
    (h : z₀ ∉ segment ℝ w₀ w₁ ∪ segment ℝ w₁ w₂ ∪ segment ℝ w₂ w₀) :
    triIntegral (fun z => (z - z₀)⁻¹) w₀ w₁ w₂ =
      2 * (Real.pi : ℂ) * Complex.I * (windingNumber w₀ w₁ w₂ z₀ : ℂ) :=
  by
    -- the thesis's own argument: apply part 3 to each of the three sides; the
    -- three logarithms telescope to `log 1 = 0` and the three angles are, by
    -- definition, `2π` times the winding number
    rw [Set.union_assoc] at h
    simp only [Set.mem_union, not_or] at h
    obtain ⟨h01, h12, h20⟩ := h
    have n0 : ‖w₀ - z₀‖ ≠ 0 := by
      simp only [ne_eq, norm_eq_zero, sub_eq_zero]
      rintro rfl; exact h01 (left_mem_segment ℝ w₀ w₁)
    have n1 : ‖w₁ - z₀‖ ≠ 0 := by
      simp only [ne_eq, norm_eq_zero, sub_eq_zero]
      rintro rfl; exact h12 (left_mem_segment ℝ w₁ w₂)
    have n2 : ‖w₂ - z₀‖ ≠ 0 := by
      simp only [ne_eq, norm_eq_zero, sub_eq_zero]
      rintro rfl; exact h20 (left_mem_segment ℝ w₂ w₀)
    rw [triIntegral, invint_3 w₀ w₁ z₀ h01, invint_3 w₁ w₂ z₀ h12, invint_3 w₂ w₀ z₀ h20,
      Real.log_div n1 n0, Real.log_div n2 n1, Real.log_div n0 n2, windingNumber]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
    ring

/-! ## Parsec 150: Cauchy's integral formula and Taylor expansion -/

/-! ### The winding number of a regular `N`-gon about an interior point

⚠ **Route divergence from the thesis — not the repair of a gap.**  The thesis
proves the winding number of the `N`-gon as **14VIII**.5, by partitioning the
region between a triangle `T` with `z₀ ∈ in(T)` and the `N`-gon "in the obvious
manner into triangles `T₁,…,T_M`" and killing each by **14IV** `goursat`, the
integrands there being holomorphic; 15II then cites `invint`(5).  That argument
is elementary and complete as printed (author's ruling, 2026-08-22).  We take
a different route, which proves the polygon case outright and needs only
*continuity* of `f` at `z₀`:

* the `n`-th edge of the `N`-gon spans a supporting line of the polygon, so an
  interior point `z₀` satisfies `Re((z₀ − c)·conj(e^{iπ(2n+1)/N})) < r cos(π/N)`
  strictly (`polygon_halfplane`, `polygon_halfplane_strict`);
* that bound says exactly that `Im(conj(wₙ − z₀)·(wₙ₊₁ − z₀)) > 0`
  (`polygon_im_pos`), so each `ζₙ := (wₙ₊₁ − z₀)/(wₙ − z₀)` lies in the open
  upper half plane, where `Complex.arg` is continuous;
* hence `S(z₀) := ∑ₙ arg ζₙ` is continuous along the segment from the centre `c`
  to `z₀` (which stays inside the same open half planes, by convexity), and
  `exp(i S) = ∏ ζₙ = 1` because the product telescopes and `w_N = w₀`; so
  `S` takes values in `2πℤ` and is therefore constant on that segment;
* at the centre every `ζₙ` is `e^{2πi/N}`, so `S(c) = N·(2π/N) = 2π`.

The divergence is larger than this lemma: `cauchy_formula` below uses
`dslope f z₀`, differentiable on all of `U`, which removes **15III**'s
`δ`/`‖f'(z₀)‖+37` estimate and with it the small triangle `T` around `z₀`
altogether; Goursat is then applied to the **fan** `(w₀, wₙ, wₙ₊₁)`, whose
interior edges cancel immediately, so the region between a triangle and the
`N`-gon never arises.  Two consequences worth recording: the tree uses neither
**14VIII**.4 `invint_4` nor the thesis's **14VIII**.5 here (both have zero
consumers), and `polygon_winding` asks less of `f` than the thesis's route
does. -/

private theorem cos_step (N : ℕ) (hN : 0 < N) (t : ℤ) (h1 : 1 ≤ t) (h2 : t ≤ N) :
    Real.cos (Real.pi * t / N) ≤ Real.cos (Real.pi / N) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have ht1 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast h1
  have ht2 : (t:ℝ) ≤ (N:ℝ) := by exact_mod_cast h2
  refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) ?_ ?_
  · rw [div_le_iff₀ hNR]
    nlinarith [Real.pi_pos]
  · rw [div_le_div_iff_of_pos_right hNR]
    nlinarith [Real.pi_pos]

/-- `cos (π m / N) ≤ cos (π / N)` for every *odd* integer `m` and `N ≥ 1`. -/
private theorem cos_le_cos_of_odd (N : ℕ) (hN : 0 < N) (m : ℤ) (hm : Odd m) :
    Real.cos (Real.pi * m / N) ≤ Real.cos (Real.pi / N) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hN2 : (0:ℤ) < 2 * N := by positivity
  obtain ⟨s, q, hs0, hslt, hm'⟩ : ∃ s q : ℤ, 0 ≤ s ∧ s < 2 * N ∧ m = 2 * N * q + s :=
    ⟨m % (2 * N), m / (2 * N), Int.emod_nonneg m (by omega), Int.emod_lt_of_pos m hN2, by
      have := Int.mul_ediv_add_emod m (2 * (N:ℤ)); omega⟩
  have hsodd : Odd s := by
    rcases hm with ⟨k, hk⟩
    have hfac : 2 * (N:ℤ) * q = 2 * ((N:ℤ) * q) := by ring
    exact ⟨k - N * q, by omega⟩
  have hcos : Real.cos (Real.pi * m / N) = Real.cos (Real.pi * s / N) := by
    have he : Real.pi * m / N = Real.pi * s / N + (q : ℤ) * (2 * Real.pi) := by
      rw [hm']; push_cast; field_simp; ring
    rw [he, Real.cos_add_int_mul_two_pi]
  rw [hcos]
  have hs1 : 1 ≤ s := by rcases hsodd with ⟨k, hk⟩; omega
  rcases le_or_gt s N with hcase | hcase
  · exact cos_step N hN s hs1 hcase
  · have he : Real.pi * s / N = -(Real.pi * ((2 * N - s : ℤ) : ℝ) / N) + (1:ℤ) * (2 * Real.pi) := by
      push_cast; field_simp; ring
    rw [he, Real.cos_add_int_mul_two_pi, Real.cos_neg]
    exact cos_step N hN (2 * N - s) (by omega) (by omega)



private noncomputable def cisR (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

private theorem cisR_re (θ : ℝ) : (cisR θ).re = Real.cos θ := by
  rw [cisR, Complex.exp_ofReal_mul_I_re]

private theorem cisR_im (θ : ℝ) : (cisR θ).im = Real.sin θ := by
  rw [cisR, Complex.exp_ofReal_mul_I_im]

private theorem cisR_add (a b : ℝ) : cisR (a + b) = cisR a * cisR b := by
  rw [cisR, cisR, cisR, ← Complex.exp_add]; push_cast; ring_nf

private theorem cisR_conj (θ : ℝ) : (starRingEnd ℂ) (cisR θ) = cisR (-θ) := by
  rw [cisR, cisR, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I]

private theorem cisR_mul_conj (θ : ℝ) : (starRingEnd ℂ) (cisR θ) * cisR θ = 1 := by
  rw [cisR_conj, cisR, cisR, ← Complex.exp_add]
  push_cast
  rw [show (-(θ:ℂ)) * Complex.I + (θ:ℂ) * Complex.I = 0 by ring, Complex.exp_zero]


/-- The vertices of the regular `N`-gon, written with `cisR`. -/
private theorem polygon_vertex {N : ℕ} (hN : 3 ≤ N) (c : ℂ) (r : ℝ) (w : ℕ → ℂ)
    (hw : ∀ n, w n = c + (r : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (N : ℂ)))
    (n : ℕ) : w n = c + (r : ℂ) * cisR (2 * Real.pi * n / N) := by
  rw [hw n, cisR]
  congr 2
  push_cast
  ring

/-- The closed `N`-gon lies in the closed half plane bounded by the line through
the `n`-th edge; `π(2n+1)/N` is the direction of the outward normal. -/
private theorem polygon_halfplane {N : ℕ} (hN : 3 ≤ N) (c : ℂ) (r : ℝ) (hr : 0 < r) (w : ℕ → ℂ)
    (hw : ∀ n, w n = c + (r : ℂ) * cisR (2 * Real.pi * n / N)) (n : ℕ) :
    convexHull ℝ (Set.range w) ⊆
      {z : ℂ | ((z - c) * (starRingEnd ℂ) (cisR (Real.pi * (2 * n + 1) / N))).re
                 ≤ r * Real.cos (Real.pi / N)} := by
  have hN0 : 0 < N := by omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  set u : ℂ := cisR (Real.pi * (2 * n + 1) / N) with hu
  have hlin : IsLinearMap ℝ (fun z : ℂ => (z * (starRingEnd ℂ) u).re) := by
    constructor
    · intro x y; simp [add_mul, Complex.add_re]
    · intro a x
      simp [Complex.real_smul, Complex.mul_re, Complex.mul_im]
      ring
  have hset : {z : ℂ | ((z - c) * (starRingEnd ℂ) u).re ≤ r * Real.cos (Real.pi / N)}
      = {z : ℂ | (fun z : ℂ => (z * (starRingEnd ℂ) u).re) z
          ≤ r * Real.cos (Real.pi / N) + (c * (starRingEnd ℂ) u).re} := by
    ext z
    simp only [Set.mem_setOf_eq, sub_mul, Complex.sub_re]
    constructor <;> intro h <;> linarith
  rw [hset]
  refine convexHull_min ?_ (convex_halfSpace_le hlin _)
  rintro _ ⟨k, rfl⟩
  simp only [Set.mem_setOf_eq]
  have hwk : w k - c = (r : ℂ) * cisR (2 * Real.pi * k / N) := by rw [hw k]; ring
  have hstep : ((w k - c) * (starRingEnd ℂ) u).re
      = r * Real.cos (2 * Real.pi * k / N - Real.pi * (2 * n + 1) / N) := by
    rw [hwk, hu, cisR_conj, mul_assoc, ← cisR_add]
    rw [show 2 * Real.pi * (k:ℝ) / N + -(Real.pi * (2 * (n:ℝ) + 1) / N)
        = 2 * Real.pi * (k:ℝ) / N - Real.pi * (2 * (n:ℝ) + 1) / N by ring]
    simp [Complex.mul_re, cisR_re, cisR_im]
  have hangle : 2 * Real.pi * (k:ℝ) / N - Real.pi * (2 * (n:ℝ) + 1) / N
      = Real.pi * ((2 * (k:ℤ) - 2 * (n:ℤ) - 1 : ℤ) : ℝ) / N := by
    push_cast
    field_simp
    ring
  have hodd : Odd (2 * (k:ℤ) - 2 * (n:ℤ) - 1) := ⟨(k:ℤ) - (n:ℤ) - 1, by ring⟩
  have := cos_le_cos_of_odd N hN0 (2 * (k:ℤ) - 2 * (n:ℤ) - 1) hodd
  have hsub : ((w k - c) * (starRingEnd ℂ) u).re ≤ r * Real.cos (Real.pi / N) := by
    rw [hstep, hangle]
    exact mul_le_mul_of_nonneg_left this hr.le
  have hexp : ((w k - c) * (starRingEnd ℂ) u).re
      = (w k * (starRingEnd ℂ) u).re - (c * (starRingEnd ℂ) u).re := by
    rw [sub_mul, Complex.sub_re]
  linarith [hsub, hexp.symm.le, hexp.le]

/-- Interior points of the `N`-gon satisfy the half plane bound strictly. -/
private theorem polygon_halfplane_strict {N : ℕ} (hN : 3 ≤ N) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (w : ℕ → ℂ) (hw : ∀ n, w n = c + (r : ℂ) * cisR (2 * Real.pi * n / N)) (n : ℕ)
    (z₀ : ℂ) (hz₀ : z₀ ∈ interior (convexHull ℝ (Set.range w))) :
    ((z₀ - c) * (starRingEnd ℂ) (cisR (Real.pi * (2 * n + 1) / N))).re
      < r * Real.cos (Real.pi / N) := by
  set u : ℂ := cisR (Real.pi * (2 * n + 1) / N) with hu
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z₀ hz₀
  have hz : z₀ + (ε / 2 : ℝ) • u ∈ convexHull ℝ (Set.range w) := by
    refine interior_subset (hball ?_)
    have hnu : ‖u‖ = 1 := by
      rw [hu, cisR, Complex.norm_exp]
      simp
    simp only [Metric.mem_ball, dist_eq_norm]
    rw [show z₀ + (ε / 2 : ℝ) • u - z₀ = (ε / 2 : ℝ) • u by ring]
    rw [norm_smul, hnu, mul_one]
    simp only [Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
    linarith
  have hle := polygon_halfplane hN c r hr w hw n hz
  simp only [Set.mem_setOf_eq] at hle
  have hexp : ((z₀ + (ε / 2 : ℝ) • u - c) * (starRingEnd ℂ) u).re
      = ((z₀ - c) * (starRingEnd ℂ) u).re + ε / 2 := by
    have h1 : (z₀ + (ε / 2 : ℝ) • u - c) = (z₀ - c) + ((ε / 2 : ℝ) : ℂ) * u := by
      rw [Complex.real_smul]; ring
    rw [h1, add_mul, Complex.add_re]
    congr 1
    have huu : u * (starRingEnd ℂ) u = 1 := by rw [hu, mul_comm, cisR_mul_conj]
    rw [mul_assoc, huu, mul_one, Complex.ofReal_re]
  linarith


/-- Strict half plane bound at the `n`-th edge forces the triangle
`(w n, z₀, w (n+1))` to be positively oriented. -/
private theorem polygon_im_pos {N : ℕ} (hN : 3 ≤ N) (c : ℂ) (r : ℝ) (hr : 0 < r) (w : ℕ → ℂ)
    (hw : ∀ n, w n = c + (r : ℂ) * cisR (2 * Real.pi * n / N)) (n : ℕ) (z₀ : ℂ)
    (hlt : ((z₀ - c) * (starRingEnd ℂ) (cisR (Real.pi * (2 * n + 1) / N))).re
      < r * Real.cos (Real.pi / N)) :
    0 < ((starRingEnd ℂ) (w n - z₀) * (w (n + 1) - z₀)).im := by
  have hN0 : 0 < N := by omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  set A : ℂ := cisR (Real.pi / N) with hA
  set U : ℂ := cisR (Real.pi * (2 * n + 1) / N) with hU
  set p : ℂ := z₀ - c with hp
  have hAe : cisR (2 * Real.pi * (n:ℝ) / N) = U * (starRingEnd ℂ) A := by
    rw [hU, hA, cisR_conj, ← cisR_add]
    congr 1
    field_simp
    ring
  have hAe' : cisR (2 * Real.pi * ((n:ℝ) + 1) / N) = U * A := by
    rw [hU, hA, ← cisR_add]
    congr 1
    field_simp
    ring
  have hUU : (starRingEnd ℂ) U * U = 1 := by rw [hU]; exact cisR_mul_conj _
  have hAA : (starRingEnd ℂ) A * A = 1 := by rw [hA]; exact cisR_mul_conj _
  have hw1 : w n - z₀ = (r : ℂ) * (U * (starRingEnd ℂ) A) - p := by
    rw [hw n, hAe, hp]; ring
  have hw2 : w (n + 1) - z₀ = (r : ℂ) * (U * A) - p := by
    have : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hw (n + 1), this, hAe', hp]; ring
  have hconj1 : (starRingEnd ℂ) (w n - z₀)
      = (r : ℂ) * ((starRingEnd ℂ) U * A) - (starRingEnd ℂ) p := by
    rw [hw1]
    simp [map_sub, map_mul, Complex.conj_conj]
  set V : ℝ := ((starRingEnd ℂ) U * p).re with hV
  have hadd : (starRingEnd ℂ) U * p + U * (starRingEnd ℂ) p = ((2 * V : ℝ) : ℂ) := by
    have h := Complex.add_conj ((starRingEnd ℂ) U * p)
    rw [map_mul, Complex.conj_conj] at h
    rw [hV]
    exact h
  have hmc : p * (starRingEnd ℂ) p = ((Complex.normSq p : ℝ) : ℂ) := Complex.mul_conj p
  have key : (starRingEnd ℂ) (w n - z₀) * (w (n + 1) - z₀)
      = (r : ℂ) ^ 2 * A ^ 2 - (r : ℂ) * A * ((2 * V : ℝ) : ℂ) + ((Complex.normSq p : ℝ) : ℂ) := by
    rw [hconj1, hw2]
    linear_combination ((r:ℂ) ^ 2 * A ^ 2) * hUU - (r:ℂ) * A * hadd + hmc
  rw [key]
  have hVlt : V < r * Real.cos (Real.pi / N) := by
    rw [hV, mul_comm]
    exact hlt
  have hsin : 0 < Real.sin (Real.pi / N) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hNR]
      nlinarith [Real.pi_pos,
        mul_le_mul_of_nonneg_left (show (3:ℝ) ≤ N by exact_mod_cast hN) Real.pi_pos.le]
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, pow_two, Complex.sub_re, Complex.add_re, cisR_re, cisR_im, hA,
    zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_sub, neg_zero]
  nlinarith [mul_pos hr (mul_pos hsin (sub_pos.mpr hVlt))]


private theorem cisR_ne_zero (θ : ℝ) : cisR θ ≠ 0 := Complex.exp_ne_zero _

private theorem cisR_sub (a b : ℝ) : cisR (a - b) = cisR a / cisR b := by
  rw [eq_div_iff (cisR_ne_zero b), ← cisR_add]
  congr 1
  ring

private theorem cisR_arg {θ : ℝ} (h : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.arg (cisR θ) = θ := by
  rw [cisR, Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I h

private theorem prod_telescope (a : ℕ → ℂ) (M : ℕ) (ha : ∀ n ≤ M, a n ≠ 0) :
    ∏ n ∈ Finset.range M, (a (n + 1) / a n) = a M / a 0 := by
  induction M with
  | zero => simp [div_self (ha 0 le_rfl)]
  | succ M ih =>
      rw [Finset.prod_range_succ, ih (fun n hn => ha n (by omega))]
      have h1 : a M ≠ 0 := ha M (by omega)
      have h2 : a 0 ≠ 0 := ha 0 (by omega)
      field_simp

private theorem div_im_eq (a b : ℂ) : (a / b).im
    = ((starRingEnd ℂ) b * a).im / Complex.normSq b := by
  rw [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- A continuous function on `[0,1]` all of whose values are integer multiples of
`2π` is constant. -/
private theorem const_of_two_pi_int {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 1))
    (hval : ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ k : ℤ, g t = 2 * Real.pi * k) : g 1 = g 0 := by
  have hpi := Real.pi_pos
  obtain ⟨k0, hk0⟩ := hval 0 (by norm_num)
  obtain ⟨k1, hk1⟩ := hval 1 (by norm_num)
  have habs : ∀ (x : ℝ), x ∈ Set.Icc (g 0) (g 1) ∪ Set.Icc (g 1) (g 0) →
      (∃ t ∈ Set.Icc (0:ℝ) 1, g t = x) → ∃ k : ℤ, x = 2 * Real.pi * k := by
    rintro x _ ⟨t, ht, rfl⟩
    exact hval t ht
  rcases lt_trichotomy (g 1) (g 0) with hlt | heq | hgt
  · exfalso
    have hk : (k1 : ℝ) < k0 := by
      rw [hk0, hk1] at hlt; nlinarith
    have hk' : k1 + 1 ≤ k0 := by exact_mod_cast (by exact_mod_cast hk : k1 < k0)
    have hstep : g 1 ≤ g 0 - 2 * Real.pi := by
      rw [hk0, hk1]
      have : ((k1 : ℝ) + 1) ≤ k0 := by exact_mod_cast hk'
      nlinarith
    have hmem : g 0 - Real.pi ∈ Set.Icc (g 1) (g 0) := ⟨by linarith, by linarith⟩
    obtain ⟨t, ht, hgt'⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hg hmem
    obtain ⟨k, hk2⟩ := hval t ht
    rw [hgt'] at hk2
    rw [hk0] at hk2
    have : (2 : ℝ) * k = 2 * k0 - 1 := by
      field_simp at hk2 ⊢
      nlinarith [hk2]
    have hz : (2 : ℤ) * k = 2 * k0 - 1 := by exact_mod_cast this
    omega
  · exact heq
  · exfalso
    have hk : (k0 : ℝ) < k1 := by
      rw [hk0, hk1] at hgt; nlinarith
    have hk' : k0 + 1 ≤ k1 := by exact_mod_cast (by exact_mod_cast hk : k0 < k1)
    have hstep : g 0 + 2 * Real.pi ≤ g 1 := by
      rw [hk0, hk1]
      have : ((k0 : ℝ) + 1) ≤ k1 := by exact_mod_cast hk'
      nlinarith
    have hmem : g 0 + Real.pi ∈ Set.Icc (g 0) (g 1) := ⟨by linarith, by linarith⟩
    obtain ⟨t, ht, hgt'⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hg hmem
    obtain ⟨k, hk2⟩ := hval t ht
    rw [hgt'] at hk2
    rw [hk0] at hk2
    have : (2 : ℝ) * k = 2 * k0 + 1 := by
      field_simp at hk2 ⊢
      nlinarith [hk2]
    have hz : (2 : ℤ) * k = 2 * k0 + 1 := by exact_mod_cast this
    omega


/-- **The winding number of a regular `N`-gon about an interior point is 1.** -/
private theorem polygon_winding {N : ℕ} (hN : 3 ≤ N) (c : ℂ) (r : ℝ) (hr : 0 < r) (w : ℕ → ℂ)
    (hw : ∀ n, w n = c + (r : ℂ) * cisR (2 * Real.pi * n / N))
    (z₀ : ℂ) (hz₀ : z₀ ∈ interior (convexHull ℝ (Set.range w))) :
    ∑ n ∈ Finset.range N, Complex.arg ((w (n + 1) - z₀) / (w n - z₀)) = 2 * Real.pi := by
  have hN0 : 0 < N := by omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  have hN3 : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  have hposN : 0 < Real.pi / N := by positivity
  have hpos2 : 0 < 2 * Real.pi / N := by positivity
  have hcosp : 0 < Real.cos (Real.pi / N) := by
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith, ?_⟩
    rw [div_lt_div_iff₀ hNR (by norm_num : (0:ℝ) < 2)]
    nlinarith
  set γ : ℝ → ℂ := fun t => c + (t : ℂ) * (z₀ - c) with hγ
  have hγ0 : γ 0 = c := by simp [hγ]
  have hγ1 : γ 1 = z₀ := by simp [hγ]
  have hpath : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ n : ℕ,
      ((γ t - c) * (starRingEnd ℂ) (cisR (Real.pi * (2 * n + 1) / N))).re
        < r * Real.cos (Real.pi / N) := by
    intro t ht n
    obtain ⟨ht0, ht1⟩ := ht
    have hV := polygon_halfplane_strict hN c r hr w hw n z₀ hz₀
    have hre : ((γ t - c) * (starRingEnd ℂ) (cisR (Real.pi * (2 * n + 1) / N))).re
        = t * ((z₀ - c) * (starRingEnd ℂ) (cisR (Real.pi * (2 * n + 1) / N))).re := by
      have hsub : γ t - c = (t : ℂ) * (z₀ - c) := by simp [hγ]
      rw [hsub, mul_assoc]
      simp [Complex.mul_re]
    rw [hre]
    rcases eq_or_lt_of_le ht1 with rfl | hlt
    · simpa using hV
    · nlinarith [mul_le_mul_of_nonneg_left hV.le ht0,
        mul_pos (sub_pos.mpr hlt) (mul_pos hr hcosp)]
  have himpos : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ n : ℕ,
      0 < ((starRingEnd ℂ) (w n - γ t) * (w (n + 1) - γ t)).im :=
    fun t ht n => polygon_im_pos hN c r hr w hw n (γ t) (hpath t ht n)
  have hne : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ n : ℕ, w n - γ t ≠ 0 := by
    intro t ht n h
    have h2 := himpos t ht n
    rw [h] at h2
    simp at h2
  have hzim : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ n : ℕ,
      0 < ((w (n + 1) - γ t) / (w n - γ t)).im := by
    intro t ht n
    rw [div_im_eq]
    exact div_pos (himpos t ht n) (Complex.normSq_pos.mpr (hne t ht n))
  -- continuity of the total angle along the path
  have hcont : ContinuousOn
      (fun t => ∑ n ∈ Finset.range N, Complex.arg ((w (n + 1) - γ t) / (w n - γ t)))
      (Set.Icc 0 1) := by
    refine continuousOn_finsetSum _ (fun n _ t ht => ?_)
    refine ContinuousAt.continuousWithinAt ?_
    have hcγ : ContinuousAt γ t := by
      rw [hγ]
      fun_prop
    have hq : ContinuousAt (fun s => (w (n + 1) - γ s) / (w n - γ s)) t :=
      (continuousAt_const.sub hcγ).div (continuousAt_const.sub hcγ) (hne t ht n)
    have harg : ContinuousAt Complex.arg ((w (n + 1) - γ t) / (w n - γ t)) :=
      Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr (Or.inr (hzim t ht n).ne'))
    exact ContinuousAt.comp (g := Complex.arg)
      (f := fun s => (w (n + 1) - γ s) / (w n - γ s)) (x := t) harg hq
  -- the total angle is an integer multiple of `2π`
  have hwN : w N = w 0 := by
    rw [hw N, hw 0]
    congr 2
    rw [show 2 * Real.pi * ((N:ℕ):ℝ) / N = 2 * Real.pi by field_simp,
      show 2 * Real.pi * ((0:ℕ):ℝ) / N = 0 by simp]
    rw [cisR, cisR]
    push_cast
    rw [show ((0:ℂ)) * Complex.I = 0 by ring, Complex.exp_zero]
    exact Complex.exp_two_pi_mul_I
  have hvals : ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ k : ℤ,
      (∑ n ∈ Finset.range N, Complex.arg ((w (n + 1) - γ t) / (w n - γ t))) = 2 * Real.pi * k := by
    intro t ht
    have hane : ∀ n ≤ N, w n - γ t ≠ 0 := fun n _ => hne t ht n
    have hprod : ∏ n ∈ Finset.range N, ((w (n + 1) - γ t) / (w n - γ t)) = 1 := by
      rw [prod_telescope (fun n => w n - γ t) N hane, hwN, div_self (hane 0 (by omega))]
    have hexp : Complex.exp
        (((∑ n ∈ Finset.range N, Complex.arg ((w (n + 1) - γ t) / (w n - γ t)) : ℝ) : ℂ)
          * Complex.I) = 1 := by
      have h1 : (((∑ n ∈ Finset.range N,
            Complex.arg ((w (n + 1) - γ t) / (w n - γ t)) : ℝ) : ℂ) * Complex.I)
          = ∑ n ∈ Finset.range N,
              ((Complex.arg ((w (n + 1) - γ t) / (w n - γ t)) : ℂ) * Complex.I) := by
        push_cast
        rw [Finset.sum_mul]
      rw [h1, Complex.exp_sum]
      have h2 : ∀ n ∈ Finset.range N,
          Complex.exp ((Complex.arg ((w (n + 1) - γ t) / (w n - γ t)) : ℂ) * Complex.I)
            = ((w (n + 1) - γ t) / (w n - γ t))
                / ((‖(w (n + 1) - γ t) / (w n - γ t)‖ : ℝ) : ℂ) := by
        intro n _
        have hz : (w (n + 1) - γ t) / (w n - γ t) ≠ 0 :=
          div_ne_zero (hne t ht (n + 1)) (hne t ht n)
        have hnz : ((‖(w (n + 1) - γ t) / (w n - γ t)‖ : ℝ) : ℂ) ≠ 0 := by
          simpa using hz
        rw [eq_div_iff hnz, mul_comm]
        exact Complex.norm_mul_exp_arg_mul_I _
      rw [Finset.prod_congr rfl h2, Finset.prod_div_distrib, hprod, ← Complex.ofReal_prod,
        ← norm_prod, hprod]
      simp
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
    refine ⟨k, ?_⟩
    have him := congrArg Complex.im hk
    simp [Complex.mul_im, Complex.mul_re] at him
    linarith [him]
  -- the total angle at the centre is `2π`
  have hg0 : (∑ n ∈ Finset.range N, Complex.arg ((w (n + 1) - γ 0) / (w n - γ 0)))
      = 2 * Real.pi := by
    have hterm : ∀ n ∈ Finset.range N,
        Complex.arg ((w (n + 1) - γ 0) / (w n - γ 0)) = 2 * Real.pi / N := by
      intro n _
      rw [hγ0, hw (n + 1), hw n]
      rw [show c + (r:ℂ) * cisR (2 * Real.pi * ((n+1:ℕ):ℝ) / N) - c
            = (r:ℂ) * cisR (2 * Real.pi * ((n+1:ℕ):ℝ) / N) by ring,
        show c + (r:ℂ) * cisR (2 * Real.pi * ((n:ℕ):ℝ) / N) - c
            = (r:ℂ) * cisR (2 * Real.pi * ((n:ℕ):ℝ) / N) by ring]
      rw [mul_div_mul_left _ _ (by exact_mod_cast hr.ne' : (r:ℂ) ≠ 0), ← cisR_sub,
        show 2 * Real.pi * ((n+1:ℕ):ℝ) / N - 2 * Real.pi * ((n:ℕ):ℝ) / N
            = 2 * Real.pi / N by push_cast; field_simp; ring]
      refine cisR_arg ⟨by linarith, ?_⟩
      rw [div_le_iff₀ hNR]
      nlinarith
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hmain := const_of_two_pi_int hcont hvals
  rw [hg0, hγ1] at hmain
  exact hmain



/-- The regular `N`-gon closes up: `w_N = w₀`. -/
private theorem polygon_closed {N : ℕ} (hN : 3 ≤ N) (c : ℂ) (r : ℝ) (w : ℕ → ℂ)
    (hw : ∀ n, w n = c + (r : ℂ) * cisR (2 * Real.pi * n / N)) : w N = w 0 := by
  have hN0 : 0 < N := by omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  rw [hw N, hw 0]
  congr 2
  rw [show 2 * Real.pi * ((N:ℕ):ℝ) / N = 2 * Real.pi by field_simp,
    show 2 * Real.pi * ((0:ℕ):ℝ) / N = 0 by simp]
  rw [cisR, cisR]
  push_cast
  rw [show ((0:ℂ)) * Complex.I = 0 by ring, Complex.exp_zero]
  exact Complex.exp_two_pi_mul_I

/-- An interior point of the `N`-gon lies on none of its edges. -/
private theorem polygon_notMem_edge {N : ℕ} (hN : 3 ≤ N) (c : ℂ) (r : ℝ) (hr : 0 < r) (w : ℕ → ℂ)
    (hw : ∀ n, w n = c + (r : ℂ) * cisR (2 * Real.pi * n / N)) (z₀ : ℂ)
    (hz₀ : z₀ ∈ interior (convexHull ℝ (Set.range w))) (n : ℕ) :
    z₀ ∉ segment ℝ (w n) (w (n + 1)) := by
  intro hmem
  have hpos := polygon_im_pos hN c r hr w hw n z₀
    (polygon_halfplane_strict hN c r hr w hw n z₀ hz₀)
  obtain ⟨a, b, ha, hb, hab, hz⟩ := hmem
  have hac : (a : ℂ) = 1 - (b : ℂ) := by
    have h : (a : ℝ) = 1 - b := by linarith
    rw [h]; push_cast; ring
  have hbc : (b : ℂ) = 1 - (a : ℂ) := by
    have h : (b : ℝ) = 1 - a := by linarith
    rw [h]; push_cast; ring
  have h1 : w n - z₀ = (b : ℂ) * (w n - w (n + 1)) := by
    rw [← hz]
    simp only [Complex.real_smul]
    rw [hac]; ring
  have h2 : w (n + 1) - z₀ = (a : ℂ) * (w (n + 1) - w n) := by
    rw [← hz]
    simp only [Complex.real_smul]
    rw [hbc]; ring
  have hd : (starRingEnd ℂ) (w n - w (n + 1)) * (w n - w (n + 1))
      = ((Complex.normSq (w n - w (n + 1)) : ℝ) : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj _
  have hcalc : (starRingEnd ℂ) ((b:ℂ) * (w n - w (n + 1))) * ((a:ℂ) * (w (n + 1) - w n))
      = (((-(a * b) : ℝ) * (Complex.normSq (w n - w (n + 1)) : ℝ) : ℝ) : ℂ) := by
    rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul, ← hd]
    push_cast
    ring
  rw [h1, h2, hcalc] at hpos
  simp at hpos

/-- Fan triangulation from a point `v`: the closed polygon integral is the sum of
the integrals over the triangles `(v, wₙ, wₙ₊₁)`. -/
private theorem polygon_fan (g : ℂ → 𝒜) (N : ℕ) (w : ℕ → ℂ) (v : ℂ) (hwN : w N = w 0) :
    ∑ n ∈ Finset.range N, triIntegral g v (w n) (w (n + 1))
      = ∑ n ∈ Finset.range N, segIntegral g (w n) (w (n + 1)) := by
  have hkey : ∀ n : ℕ, triIntegral g v (w n) (w (n + 1))
      = segIntegral g (w n) (w (n + 1))
        + (segIntegral g v (w n) - segIntegral g v (w (n + 1))) := by
    intro n
    rw [triIntegral, segIntegral_symm g v (w (n + 1))]
    abel
  rw [Finset.sum_congr rfl (fun n _ => hkey n), Finset.sum_add_distrib,
    Finset.sum_range_sub' (fun n => segIntegral g v (w n)) N, hwN, sub_self, add_zero]

/-- The integral of a holomorphic function around the closed polygon vanishes:
Goursat on each triangle of the fan from `w₀`. -/
private theorem polygon_integral_eq_zero {U : Set ℂ} (hU : IsOpen U) (g : ℂ → 𝒜)
    (hg : DifferentiableOn ℂ g U) (N : ℕ) (w : ℕ → ℂ)
    (hUw : convexHull ℝ (Set.range w) ⊆ U) (hwN : w N = w 0) :
    ∑ n ∈ Finset.range N, segIntegral g (w n) (w (n + 1)) = 0 := by
  rw [← polygon_fan g N w (w 0) hwN]
  refine Finset.sum_eq_zero (fun n _ => goursat hU g hg _ _ _ (subset_trans ?_ hUw))
  refine convexHull_mono ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨n, rfl⟩, ⟨n + 1, rfl⟩]

/-- **The polygon integral of `(z − z₀)⁻¹` is `2πi`** when `z₀` is interior: the
angles sum to `2π` by `polygon_winding` and the logarithms telescope. -/
private theorem polygon_inv_integral {N : ℕ} (hN : 3 ≤ N) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (w : ℕ → ℂ) (hw : ∀ n, w n = c + (r : ℂ) * cisR (2 * Real.pi * n / N)) (z₀ : ℂ)
    (hz₀ : z₀ ∈ interior (convexHull ℝ (Set.range w))) :
    ∑ n ∈ Finset.range N, segIntegral (fun z => (z - z₀)⁻¹) (w n) (w (n + 1))
      = 2 * (Real.pi : ℂ) * Complex.I := by
  have hnotmem := polygon_notMem_edge hN c r hr w hw z₀ hz₀
  have hne : ∀ n : ℕ, ‖w n - z₀‖ ≠ 0 := by
    intro n h
    rw [norm_eq_zero, sub_eq_zero] at h
    exact hnotmem n (h ▸ left_mem_segment ℝ (w n) (w (n + 1)))
  have hterm : ∀ n : ℕ, segIntegral (fun z => (z - z₀)⁻¹) (w n) (w (n + 1))
      = (Complex.arg ((w (n + 1) - z₀) / (w n - z₀)) : ℂ) * Complex.I
        + (((fun m => Real.log ‖w (m : ℕ) - z₀‖) (n + 1)
              - (fun m => Real.log ‖w (m : ℕ) - z₀‖) n : ℝ) : ℂ) := by
    intro n
    rw [invint_3 (w n) (w (n + 1)) z₀ (hnotmem n), measuredAngle,
      Real.log_div (hne (n + 1)) (hne n)]
  rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_add_distrib]
  rw [← Complex.ofReal_sum, Finset.sum_range_sub (fun m => Real.log ‖w m - z₀‖) N,
    polygon_closed hN c r w hw, sub_self, Complex.ofReal_zero, add_zero,
    ← Finset.sum_mul, ← Complex.ofReal_sum, polygon_winding hN c r hr w hw z₀ hz₀]
  push_cast
  ring


/-- **The geometric expansion of `(u − z)⁻¹` under a single edge integral.**  This
is the analytic heart of **15V**: on an edge whose points are at distance at
least `s` from `v`, and for `‖z − v‖ < s`, the series
`∑ₙ (z−v)ⁿ (u−v)^{-(n+1)}` converges to `(u−z)⁻¹` uniformly, so it may be
integrated term by term. -/
private theorem edge_taylor (f : ℂ → 𝒜) (W W' : ℂ)
    (hfc : ContinuousOn f (segment ℝ W W')) (v z : ℂ) (s : ℝ) (hs : 0 < s)
    (hzv : ‖z - v‖ < s) (hfar : ∀ u ∈ segment ℝ W W', s ≤ ‖u - v‖) :
    HasSum (fun n : ℕ => (z - v) ^ n • segIntegral (fun u => ((u - v) ^ (n + 1))⁻¹ • f u) W W')
      (segIntegral (fun u => (u - z)⁻¹ • f u) W W') := by
  set γ : ℝ → ℂ := fun t => W + (t : ℂ) * (W' - W) with hγ
  have hγc : Continuous γ := by rw [hγ]; fun_prop
  have hmemseg : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ segment ℝ W W' := by
    intro t ht
    rw [segment_eq_image' ℝ]
    exact ⟨t, ht, by simp [hγ, Complex.real_smul]⟩
  have hfarγ : ∀ t ∈ Set.Icc (0:ℝ) 1, s ≤ ‖γ t - v‖ := fun t ht => hfar _ (hmemseg t ht)
  have hnev : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t - v ≠ 0 := by
    intro t ht h
    have hb := hfarγ t ht
    rw [h, norm_zero] at hb
    linarith
  have hfγ : ContinuousOn (fun t : ℝ => f (γ t)) (Set.Icc 0 1) :=
    segIntegrand_continuousOn f W W' hfc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hfγ
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by norm_num))
  have hq1 : ‖z - v‖ / s < 1 := (div_lt_one hs).mpr hzv
  have hq0 : (0:ℝ) ≤ ‖z - v‖ / s := by positivity
  -- the pointwise expansion
  have hlim : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasSum (fun n : ℕ => (z - v) ^ n • ((γ t - v) ^ (n + 1))⁻¹ • f (γ t))
        ((γ t - z)⁻¹ • f (γ t)) := by
    intro t ht
    have hne := hnev t ht
    have hqn : ‖(z - v) / (γ t - v)‖ < 1 := by
      rw [norm_div, div_lt_one (by simpa [norm_pos_iff] using hne)]
      exact lt_of_lt_of_le hzv (hfarγ t ht)
    have hgeom := hasSum_geometric_of_norm_lt_one hqn
    have hz : γ t - z ≠ 0 := by
      intro h
      have heq : γ t = z := by linear_combination h
      have hb := hfarγ t ht
      rw [heq] at hb
      linarith
    have hterm : (fun n : ℕ => (z - v) ^ n • ((γ t - v) ^ (n + 1))⁻¹ • f (γ t))
        = fun n : ℕ => (((z - v) / (γ t - v)) ^ n * (γ t - v)⁻¹) • f (γ t) := by
      funext n
      rw [smul_smul]
      congr 1
      rw [div_pow, pow_succ]
      field_simp
    have h1 : 1 - (z - v) / (γ t - v) = (γ t - z) / (γ t - v) := by
      field_simp
      ring
    have hval : (1 - (z - v) / (γ t - v))⁻¹ * (γ t - v)⁻¹ = (γ t - z)⁻¹ := by
      rw [h1, inv_div]
      field_simp
    rw [hterm, ← hval]
    exact (hgeom.mul_right _).smul_const _
  -- dominated convergence
  have hmain : HasSum
      (fun n : ℕ => ∫ t in (0:ℝ)..1, ((z - v) ^ n • ((γ t - v) ^ (n + 1))⁻¹ • f (γ t)))
      (∫ t in (0:ℝ)..1, (γ t - z)⁻¹ • f (γ t)) := by
    have huIoc : Set.uIoc (0:ℝ) 1 ⊆ Set.Icc 0 1 :=
      (Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)) ▸ Set.Ioc_subset_Icc_self
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => (‖z - v‖ / s) ^ n * (M / s)) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      refine ContinuousOn.mono ?_ huIoc
      refine continuousOn_const.smul (ContinuousOn.smul ?_ hfγ)
      exact ContinuousOn.inv₀ (by fun_prop) (fun t ht => pow_ne_zero _ (hnev t ht))
    · refine Filter.Eventually.of_forall (fun t ht => ?_)
      have htI : t ∈ Set.Icc (0:ℝ) 1 := huIoc ht
      have hnorm : s ≤ ‖γ t - v‖ := hfarγ t htI
      have hsn : s ^ (n + 1) ≤ ‖γ t - v‖ ^ (n + 1) := by
        exact pow_le_pow_left₀ hs.le hnorm _
      calc ‖(z - v) ^ n • ((γ t - v) ^ (n + 1))⁻¹ • f (γ t)‖
          = ‖z - v‖ ^ n * (‖γ t - v‖ ^ (n + 1))⁻¹ * ‖f (γ t)‖ := by
            rw [norm_smul, norm_smul, norm_pow, norm_inv, norm_pow]
            ring
        _ ≤ ‖z - v‖ ^ n * (s ^ (n + 1))⁻¹ * M := by
            have hsp : (0:ℝ) < s ^ (n + 1) := by positivity
            have hinv : (‖γ t - v‖ ^ (n + 1))⁻¹ ≤ (s ^ (n + 1))⁻¹ :=
              inv_anti₀ hsp hsn
            refine mul_le_mul (mul_le_mul_of_nonneg_left hinv (by positivity)) (hM t htI)
              (norm_nonneg _) (by positivity)
        _ = (‖z - v‖ / s) ^ n * (M / s) := by
            rw [div_pow, pow_succ]
            field_simp
    · exact Filter.Eventually.of_forall (fun t _ =>
        (summable_geometric_of_lt_one hq0 hq1).mul_right _)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall (fun t ht => hlim t (huIoc ht))
  have hstep : ∀ n : ℕ, (z - v) ^ n • segIntegral (fun u => ((u - v) ^ (n + 1))⁻¹ • f u) W W'
      = (W' - W) • ∫ t in (0:ℝ)..1, ((z - v) ^ n • ((γ t - v) ^ (n + 1))⁻¹ • f (γ t)) := by
    intro n
    rw [segIntegral_endpoints, smul_comm, ← intervalIntegral.integral_smul]
  have heq : (fun n : ℕ => (z - v) ^ n • segIntegral (fun u => ((u - v) ^ (n + 1))⁻¹ • f u) W W')
      = fun n : ℕ =>
        (W' - W) • ∫ t in (0:ℝ)..1, ((z - v) ^ n • ((γ t - v) ^ (n + 1))⁻¹ • f (γ t)) :=
    funext hstep
  rw [heq, segIntegral_endpoints]
  exact hmain.const_smul (W' - W)

/-- **15I** (`cauchy-formula`, cstar.tex:2411, Theorem (Cauchy's Integral
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
  by
    -- A route divergence from the thesis, not a gap repair: `dslope` removes
    -- the small triangle of 15III, Goursat runs on the fan from `w₀`, and
    -- `polygon_winding` proves the polygon case outright rather than promoting
    -- **14VIII**.4 to it (see the divergence note above).
    have hw' : ∀ n, w n = c + (r : ℂ) * cisR (2 * Real.pi * n / N) :=
      polygon_vertex hN c r w hw
    have hwN : w N = w 0 := polygon_closed hN c r w hw'
    have hnotmem := polygon_notMem_edge hN c r hr w hw' z₀ hz₀
    have hz₀U : z₀ ∈ U := hUw (interior_subset hz₀)
    -- (1) the removable singularity: `dslope f z₀` is holomorphic on all of `U`
    have hds : DifferentiableOn ℂ (dslope f z₀) U :=
      (Complex.differentiableOn_dslope (hU.mem_nhds hz₀U)).mpr hf
    -- (2) its polygon integral vanishes, by Goursat on the fan from `w₀`
    have hzero : ∑ n ∈ Finset.range N, segIntegral (dslope f z₀) (w n) (w (n + 1)) = 0 :=
      polygon_integral_eq_zero hU _ hds N w hUw hwN
    -- (3) split the integrand `dslope f z₀ z = (z-z₀)⁻¹ • f z - (z-z₀)⁻¹ • f z₀`
    have hsplit : ∀ n : ℕ, segIntegral (dslope f z₀) (w n) (w (n + 1))
        = segIntegral (fun z => (z - z₀)⁻¹ • f z) (w n) (w (n + 1))
          - (segIntegral (fun z => (z - z₀)⁻¹) (w n) (w (n + 1))) • f z₀ := by
      intro n
      have hmemhull : ∀ m : ℕ, w m ∈ convexHull ℝ (Set.range w) :=
        fun m => subset_convexHull ℝ _ ⟨m, rfl⟩
      have hseg : segment ℝ (w n) (w (n + 1)) ⊆ U :=
        subset_trans ((convex_convexHull ℝ (Set.range w)).segment_subset
          (hmemhull n) (hmemhull (n + 1))) hUw
      have hsne : ∀ z ∈ segment ℝ (w n) (w (n + 1)), z - z₀ ≠ 0 := by
        intro z hz h
        rw [sub_eq_zero] at h
        exact hnotmem n (h ▸ hz)
      have hinvc : ContinuousOn (fun z : ℂ => (z - z₀)⁻¹) (segment ℝ (w n) (w (n + 1))) :=
        ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop)) hsne
      have hAc : ContinuousOn (fun z : ℂ => (z - z₀)⁻¹ • f z) (segment ℝ (w n) (w (n + 1))) :=
        hinvc.smul (hf.continuousOn.mono hseg)
      have hBc : ContinuousOn (fun z : ℂ => (z - z₀)⁻¹ • f z₀) (segment ℝ (w n) (w (n + 1))) :=
        hinvc.smul continuousOn_const
      have hA : IntervalIntegrable
          (fun t : ℝ => (w n + (t:ℂ) * (w (n + 1) - w n) - z₀)⁻¹
            • f (w n + (t:ℂ) * (w (n + 1) - w n))) MeasureTheory.volume 0 1 := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact segIntegrand_continuousOn _ (w n) (w (n + 1)) hAc
      have hB : IntervalIntegrable
          (fun t : ℝ => (w n + (t:ℂ) * (w (n + 1) - w n) - z₀)⁻¹ • f z₀)
          MeasureTheory.volume 0 1 := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact segIntegrand_continuousOn _ (w n) (w (n + 1)) hBc
      have hid : Set.EqOn (fun t : ℝ => dslope f z₀ (w n + (t:ℂ) * (w (n + 1) - w n)))
          (fun t : ℝ => (w n + (t:ℂ) * (w (n + 1) - w n) - z₀)⁻¹
              • f (w n + (t:ℂ) * (w (n + 1) - w n))
            - (w n + (t:ℂ) * (w (n + 1) - w n) - z₀)⁻¹ • f z₀) (Set.uIcc 0 1) := by
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
        have hmem : w n + (t:ℂ) * (w (n + 1) - w n) ∈ segment ℝ (w n) (w (n + 1)) := by
          rw [segment_eq_image' ℝ]
          exact ⟨t, ht, by simp [Complex.real_smul]⟩
        have hne' : w n + (t:ℂ) * (w (n + 1) - w n) ≠ z₀ := fun h => hnotmem n (h ▸ hmem)
        simp only
        rw [dslope_of_ne _ hne', slope_def_module, smul_sub]
      rw [segIntegral_endpoints (dslope f z₀), intervalIntegral.integral_congr hid,
        intervalIntegral.integral_sub hA hB, smul_sub]
      congr 1
      rw [intervalIntegral.integral_smul_const, smul_smul, segIntegral_endpoints,
        smul_eq_mul]
    rw [Finset.sum_congr rfl (fun n _ => hsplit n), Finset.sum_sub_distrib, ← Finset.sum_smul,
      polygon_inv_integral hN c r hr w hw' z₀ hz₀, sub_eq_zero] at hzero
    rw [hzero, smul_smul, inv_mul_cancel₀ ?hne, one_smul]
    case hne =>
      have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      simp [this, Complex.I_ne_zero]

/-- **15V** (`taylor`, cstar.tex:2480, Proposition): a holomorphic 𝒜-valued
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
  by
    -- The thesis's proof: expand `(u - z)⁻¹` geometrically inside Cauchy's
    -- integral formula and integrate term by term (`edge_taylor`).
    have hw' : ∀ n, w n = c + (r : ℂ) * cisR (2 * Real.pi * n / K) :=
      polygon_vertex hK c r w hw
    have hzint : z ∈ interior (convexHull ℝ (Set.range w)) := hball hz
    have hzv : ‖z - v‖ < s := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact hz
    have hmemhull : ∀ m : ℕ, w m ∈ convexHull ℝ (Set.range w) :=
      fun m => subset_convexHull ℝ _ ⟨m, rfl⟩
    have hedge : ∀ k : ℕ, HasSum
        (fun n : ℕ => (z - v) ^ n • segIntegral (fun u => ((u - v) ^ (n + 1))⁻¹ • f u)
          (w k) (w (k + 1)))
        (segIntegral (fun u => (u - z)⁻¹ • f u) (w k) (w (k + 1))) := by
      intro k
      have hseg : segment ℝ (w k) (w (k + 1)) ⊆ U :=
        subset_trans ((convex_convexHull ℝ (Set.range w)).segment_subset
          (hmemhull k) (hmemhull (k + 1))) hUw
      refine edge_taylor f (w k) (w (k + 1)) (hf.continuousOn.mono hseg) v z s hs hzv ?_
      intro u hu
      by_contra hcon
      push_neg at hcon
      exact polygon_notMem_edge hK c r hr w hw' u
        (hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hcon)) k hu
    have hcauchy : f z = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        ∑ k ∈ Finset.range K,
          segIntegral (fun u => (u - z)⁻¹ • f u) (w k) (w (k + 1)) :=
      cauchy_formula hU f hf K hK c r hr w hw hUw z hzint
    have hsum := (hasSum_sum (fun k (_ : k ∈ Finset.range K) => hedge k)).const_smul
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)
    have hfun : (fun n : ℕ => (z - v) ^ n •
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          ∑ k ∈ Finset.range K,
            segIntegral (fun u => ((u - v) ^ (n + 1))⁻¹ • f u) (w k) (w (k + 1))))
        = fun n : ℕ => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          ∑ k ∈ Finset.range K, (z - v) ^ n •
            segIntegral (fun u => ((u - v) ^ (n + 1))⁻¹ • f u) (w k) (w (k + 1)) := by
      funext n
      rw [smul_comm, Finset.smul_sum]
    rw [hfun, hcauchy]
    exact hsum

/-! ### The inradius of the regular `K`-gon, for **15VII** `rigid_expansion`

The thesis's proof of `rigid-expansion` needs a regular `K`-gon that fits
*between* two concentric disks; the only quantitative fact required is that the
`K`-gon of circumradius `ρ` contains the open disk of radius `ρ cos(π/K)`, so
that `K` can be chosen to make the polygon's inner disk exceed any prescribed
radius `< ρ`.  The polygon lemmas above all run the other way (from a point of
the interior to a property of it); this one runs into the interior. -/

/-- `cisR` is `2π`-periodic. -/
private theorem cisR_add_int_two_pi (θ : ℝ) (m : ℤ) : cisR (θ + 2 * Real.pi * m) = cisR θ := by
  rw [cisR_add]
  have : cisR (2 * Real.pi * m) = 1 := by
    rw [cisR]
    have he : ((2 * Real.pi * m : ℝ) : ℂ) * Complex.I
        = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_int_mul_two_pi_mul_I]
  rw [this, mul_one]

private theorem cisR_congr_mod (K : ℕ) (hK : 0 < K) (a b : ℤ) (h : (K : ℤ) ∣ (a - b)) :
    cisR (2 * Real.pi * (a : ℝ) / K) = cisR (2 * Real.pi * (b : ℝ) / K) := by
  obtain ⟨q, hq⟩ := h
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have ha : (a : ℝ) = (b : ℝ) + (K : ℝ) * (q : ℝ) := by
    have h2 : a = b + (K : ℤ) * q := by linarith
    exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) h2
  rw [ha, show 2 * Real.pi * ((b : ℝ) + (K : ℝ) * (q : ℝ)) / K
      = 2 * Real.pi * (b : ℝ) / K + 2 * Real.pi * (q : ℝ) by field_simp,
    cisR_add_int_two_pi]

/-- The regular `K`-gon inscribed in the circle of radius `rho` about `c` contains
the open disk of radius `rho cos(π/K)` about `c` — its inradius. -/
private theorem ball_subset_polygon {K : ℕ} (hK : 3 ≤ K) (c : ℂ) (rho : ℝ) (hrho : 0 < rho)
    (w : ℕ → ℂ) (hw : ∀ n, w n = c + (rho : ℂ) * cisR (2 * Real.pi * n / K)) :
    Metric.ball c (rho * Real.cos (Real.pi / K)) ⊆ convexHull ℝ (Set.range w) := by
  have hK0 : 0 < K := by omega
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK0
  have hpi : 0 < Real.pi := Real.pi_pos
  -- the vertex set is finite: `w` is periodic with period `K`
  have hwper : ∀ n : ℕ, w (n % K) = w n := by
    intro n
    rw [hw, hw]
    congr 2
    refine cisR_congr_mod K hK0 ((n % K : ℕ) : ℤ) ((n : ℕ) : ℤ) ?_ |>.trans ?_
    · refine ⟨-((n / K : ℕ) : ℤ), ?_⟩
      have hnk : ((n % K : ℕ) : ℤ) + (K : ℤ) * ((n / K : ℕ) : ℤ) = (n : ℤ) := by
        exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) (Nat.mod_add_div n K)
      linarith
    · norm_cast
  have hfin : (Set.range w).Finite := by
    refine Set.Finite.subset (Set.finite_range (fun n : Fin K => w (n : ℕ))) ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨⟨n % K, Nat.mod_lt _ hK0⟩, hwper n⟩
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  by_contra hnot
  obtain ⟨f, u, hfs, hfz⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (Set.range w)) (hfin.isClosed_convexHull (𝕜 := ℝ)) hnot
  have hmem : ∀ n : ℕ, w n ∈ convexHull ℝ (Set.range w) :=
    fun n => subset_convexHull ℝ _ ⟨n, rfl⟩
  -- `f` is `y ↦ Re(conj u₀ · y)` for `u₀ := f(1) + f(i)i`
  set u0 : ℂ := ⟨f 1, f Complex.I⟩ with hu0def
  have hlin : ∀ y : ℂ, f y = u0.re * y.re + u0.im * y.im := by
    intro y
    have hy : y = y.re • (1 : ℂ) + y.im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hy]
    rw [map_add, map_smul, map_smul]
    simp [hu0def]
    ring
  have hlin2 : ∀ y : ℂ, f y = ((starRingEnd ℂ) u0 * y).re := by
    intro y
    rw [hlin y, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rcases eq_or_ne u0 0 with hu00 | hu00
  · have h0 : ∀ y : ℂ, f y = 0 := by
      intro y; rw [hlin y, hu00]; simp
    rw [h0 z] at hfz
    have := hfs (w 0) (hmem 0)
    rw [h0] at this
    linarith
  · have hu0pos : 0 < ‖u0‖ := norm_pos_iff.mpr hu00
    have hK3 : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    -- the value of `f` at a point of the circumscribed circle
    have hval : ∀ φ : ℝ, f (c + (rho : ℂ) * cisR φ)
        = f c + rho * ‖u0‖ * Real.cos (φ - u0.arg) := by
      intro φ
      have hsm : ((rho : ℝ) : ℂ) * cisR φ = (rho : ℝ) • cisR φ := by rw [Complex.real_smul]
      rw [map_add, hsm, map_smul, hlin (cisR φ), cisR_re, cisR_im, smul_eq_mul,
        Real.cos_sub, Complex.cos_arg hu00, Complex.sin_arg]
      field_simp
    -- the vertex nearest in angle to `arg u₀`
    set m : ℤ := round (u0.arg * K / (2 * Real.pi)) with hm
    set psi : ℝ := 2 * Real.pi * (m : ℝ) / K with hpsi
    obtain ⟨n, hn⟩ : ∃ n : ℕ, cisR (2 * Real.pi * (n : ℝ) / K) = cisR psi := by
      refine ⟨(m % (K : ℤ)).toNat, ?_⟩
      have hm0 : 0 ≤ m % (K : ℤ) := Int.emod_nonneg m (by exact_mod_cast hK0.ne')
      have hcast : (((m % (K : ℤ)).toNat : ℕ) : ℤ) = m % (K : ℤ) := Int.toNat_of_nonneg hm0
      have hcg := cisR_congr_mod K hK0 (((m % (K : ℤ)).toNat : ℕ) : ℤ) m
        ⟨-(m / (K : ℤ)), by rw [hcast, Int.emod_def]; ring⟩
      rw [hpsi]
      exact_mod_cast hcg
    have hclose : |psi - u0.arg| ≤ Real.pi / K := by
      have hr := abs_sub_round (u0.arg * K / (2 * Real.pi))
      have he : psi - u0.arg = (2 * Real.pi / K) * ((m : ℝ) - u0.arg * K / (2 * Real.pi)) := by
        rw [hpsi]; field_simp
      rw [he, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi / K), abs_sub_comm, hm]
      calc 2 * Real.pi / K * |u0.arg * K / (2 * Real.pi)
              - ((round (u0.arg * K / (2 * Real.pi)) : ℤ) : ℝ)|
          ≤ 2 * Real.pi / K * (1 / 2) := mul_le_mul_of_nonneg_left hr (by positivity)
        _ = Real.pi / K := by ring
    have hcos : Real.cos (Real.pi / K) ≤ Real.cos (psi - u0.arg) := by
      rw [← Real.cos_abs (psi - u0.arg)]
      refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) ?_ hclose
      rw [div_le_iff₀ hKR]
      nlinarith
    -- `f` is larger at that vertex than at `z`
    have hwn : w n = c + (rho : ℂ) * cisR psi := by rw [hw n, hn]
    have hfw : f (w n) = f c + rho * ‖u0‖ * Real.cos (psi - u0.arg) := by
      rw [hwn]; exact hval psi
    have hfzc : f z ≤ f c + ‖u0‖ * ‖z - c‖ := by
      have hsplit : f z = f c + f (z - c) := by
        rw [← map_add]; congr 1; ring
      have hb : f (z - c) ≤ ‖u0‖ * ‖z - c‖ := by
        rw [hlin2]
        calc ((starRingEnd ℂ) u0 * (z - c)).re ≤ ‖(starRingEnd ℂ) u0 * (z - c)‖ :=
              Complex.re_le_norm _
          _ = ‖u0‖ * ‖z - c‖ := by rw [norm_mul, RCLike.norm_conj]
      linarith
    have h1 : ‖u0‖ * ‖z - c‖ < ‖u0‖ * (rho * Real.cos (Real.pi / K)) :=
      mul_lt_mul_of_pos_left hz hu0pos
    have e1 : ‖u0‖ * (rho * Real.cos (Real.pi / K))
        = rho * ‖u0‖ * Real.cos (Real.pi / K) := by ring
    have h2 : rho * ‖u0‖ * Real.cos (Real.pi / K)
        ≤ rho * ‖u0‖ * Real.cos (psi - u0.arg) :=
      mul_le_mul_of_nonneg_left hcos (by positivity)
    have h3 := hfs (w n) (hmem n)
    linarith


/-- **15VII** (`rigid-expansion`, cstar.tex:2529, Proposition): if a
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
    -- The thesis's own proof (cstar.tex:2528).  The previous proof here took
    -- Mathlib's `DifferentiableOn.hasFPowerSeriesOnBall` and
    -- `eq_formalMultilinearSeries` instead, on the ground that **15V**
    -- `taylor` and **13VI** `powerseries_uniqueness_coeffients` were still
    -- `sorry`; both have been proved since, and the thesis's route is the one
    -- below: fit a regular `K`-gon between the disk of radius `‖z - w‖` and
    -- the disk of radius `R`, expand `f` on it by **15V**, and identify the
    -- two coefficient sequences by **13VI**.
    have hd : ‖z - w‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    set d : ℝ := ‖z - w‖ with hddef
    have hd0 : 0 ≤ d := norm_nonneg _
    set rho : ℝ := (d + R) / 2 with hrhodef
    have hrho0 : 0 < rho := by rw [hrhodef]; linarith [hr.trans hrR]
    have hdrho : d < rho := by rw [hrhodef]; linarith
    have hrhoR : rho < R := by rw [hrhodef]; linarith
    have hquot : d / rho < 1 := (div_lt_one hrho0).mpr hdrho
    -- a regular `K`-gon whose inradius `rho cos(π/K)` still exceeds `d`
    have hlim : Filter.Tendsto (fun K : ℕ => Real.cos (Real.pi / K)) Filter.atTop (nhds 1) := by
      have h1 : Filter.Tendsto (fun K : ℕ => Real.pi / (K : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat Real.pi
      simpa [Function.comp_def] using (Real.continuous_cos.tendsto 0).comp h1
    obtain ⟨K, hKcos, hK3⟩ :=
      ((hlim.eventually (eventually_gt_nhds hquot)).and (Filter.eventually_ge_atTop 3)).exists
    have hK0 : 0 < K := by omega
    have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK0
    set s : ℝ := rho * Real.cos (Real.pi / K) with hsdef
    have hds : d < s := by
      rw [hsdef]
      calc d = rho * (d / rho) := by field_simp
        _ < rho * Real.cos (Real.pi / K) := by exact mul_lt_mul_of_pos_left hKcos hrho0
    have hs0 : 0 < s := lt_of_le_of_lt hd0 hds
    -- the polygon
    set W : ℕ → ℂ := fun n => w + (rho : ℂ) * Complex.exp (2 * Real.pi * Complex.I * n / K) with hWdef
    have hW : ∀ n, W n = w + (rho : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (K : ℂ)) :=
      fun n => rfl
    have hW' : ∀ n, W n = w + (rho : ℂ) * cisR (2 * Real.pi * n / K) := by
      intro n
      rw [hW n, cisR]
      congr 2
      push_cast
      ring
    have hWball : convexHull ℝ (Set.range W) ⊆ Metric.closedBall w rho := by
      refine convexHull_min ?_ (convex_closedBall w rho)
      rintro _ ⟨n, rfl⟩
      rw [hW' n, Metric.mem_closedBall, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hrho0]
      rw [cisR, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hUw : convexHull ℝ (Set.range W) ⊆ U := by
      refine subset_trans hWball (subset_trans ?_ hball)
      intro y hy
      rw [Metric.mem_closedBall] at hy
      exact Metric.mem_ball.mpr (lt_of_le_of_lt hy hrhoR)
    have hballin : Metric.ball w s ⊆ interior (convexHull ℝ (Set.range W)) :=
      interior_maximal (ball_subset_polygon hK3 w rho hrho0 W hW') Metric.isOpen_ball
    -- **15V** `taylor` on that polygon
    set b : ℕ → 𝒜 := fun n => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        ∑ k ∈ Finset.range K, segIntegral (fun u => ((u - w) ^ (n + 1))⁻¹ • f u) (W k) (W (k + 1))
      with hbdef
    have htay : ∀ y ∈ Metric.ball w s, HasSum (fun n : ℕ => (y - w) ^ n • b n) (f y) := by
      intro y hy
      exact taylor hU f hf K hK3 w rho hrho0 W hW hUw w s hs0 hballin y hy
    -- **13VI**: the two expansions agree on the small ball, so the coefficients agree
    have hcoeff : ∀ n, a n - b n = 0 := by
      refine powerseries_uniqueness_coeffients (fun n => a n - b n) (min r s)
        (lt_min hr hs0) ?_
      intro y hy
      have hyr : w + y ∈ Metric.ball w r := by
        rw [Metric.mem_ball, dist_eq_norm]
        simpa using lt_of_lt_of_le hy (min_le_left _ _)
      have hys : w + y ∈ Metric.ball w s := by
        rw [Metric.mem_ball, dist_eq_norm]
        simpa using lt_of_lt_of_le hy (min_le_right _ _)
      have h1 := hsmall _ hyr
      have h2 := htay _ hys
      simp only [add_sub_cancel_left] at h1 h2
      have := h1.sub h2
      rw [sub_self] at this
      refine this.congr_fun fun n => ?_
      rw [smul_sub]
    have hab : ∀ n, a n = b n := fun n => sub_eq_zero.mp (hcoeff n)
    have hzs : z ∈ Metric.ball w s := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt (le_of_eq hddef.symm) hds
    have := htay z hzs
    simpa [hab] using this
/-! ## Parsec 160: the spectral radius -/

/-- **16II** (`norm-spectrum`, cstar.tex:2581, Proposition): for a
self-adjoint element `a` of a C*-algebra,
`‖a‖ = sup { |λ| : λ ∈ spec(a) }`, the *spectral radius* of `a` (Mathlib:
`spectralRadius ℂ a`, valued in `ℝ≥0∞`). -/
theorem norm_spectrum (a : 𝒜) (ha : IsSelfAdjoint a) :
    spectralRadius ℂ a = (‖a‖₊ : ℝ≥0∞) := by
  -- The thesis's own proof (**16III**, cstar.tex:2575), which is what the
  -- whole of parsecs 120-150 was built for.  Mathlib's
  -- `IsSelfAdjoint.spectralRadius_eq_nnnorm` would close this in one line and
  -- leave Goursat, Cauchy and Taylor unused by the statement that motivates
  -- them.  The route below is the thesis's: `f z = z(1-az)⁻¹` is holomorphic
  -- wherever `1 - az` is invertible, its geometric expansion `∑ₙ aⁿz^{n+1}`
  -- (**11II** `geometric`) is valid for `|z| < ‖a‖⁻¹`, **15VII**
  -- `rigid_expansion` carries that expansion out to the whole disk on which
  -- `f` is defined, and **11VII** `geometric_convergence` — the step that
  -- uses self-adjointness — says the expansion cannot reach past `‖a‖⁻¹`.
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun z hz => ?_
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    by_contra hcon
    push_neg at hcon
    exact (spectrum.mem_iff.mp hz) (by simpa using (spectrum_bounded_1 a z hcon).neg)
  · by_contra hcon
    push_neg at hcon
    obtain ⟨t, ht1, ht2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hcon
    have ht2' : (t : ℝ) < ‖a‖ := by exact_mod_cast ht2
    have hanorm : 0 < ‖a‖ := lt_of_le_of_lt t.coe_nonneg ht2'
    set s : ℝ := max (t : ℝ) (‖a‖ / 2) with hsdef
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity) (le_max_right _ _)
    have hsa : s < ‖a‖ := max_lt ht2' (by linarith)
    have hspec : ∀ z ∈ spectrum ℂ a, ‖z‖ < s := by
      intro z hz
      have h1 : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ a :=
        le_iSup₂ (f := fun z (_ : z ∈ spectrum ℂ a) => (‖z‖₊ : ℝ≥0∞)) z hz
      have h2 : (‖z‖₊ : ℝ≥0∞) < (t : ℝ≥0∞) := lt_of_le_of_lt h1 ht1
      have h3 : ‖z‖ < (t : ℝ) := by exact_mod_cast h2
      exact lt_of_lt_of_le h3 (le_max_left _ _)
    -- the thesis's `G`: `1 - za` is invertible for `|z| < s⁻¹`
    have hunit : ∀ z : ℂ, ‖z‖ < s⁻¹ → IsUnit (1 - z • a) := by
      intro z hz
      rcases eq_or_ne z 0 with rfl | hz0
      · simp
      · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
        have hzinv : s < ‖z⁻¹‖ := by
          rw [norm_inv, lt_inv_comm₀ hs0 hzpos]
          exact hz
        have hnotmem : z⁻¹ ∉ spectrum ℂ a := fun hmem =>
          absurd (hspec _ hmem) (not_lt.mpr hzinv.le)
        have hu : IsUnit (algebraMap ℂ 𝒜 z⁻¹ - a) := by
          rw [spectrum.notMem_iff] at hnotmem
          exact hnotmem
        have hzu : IsUnit (algebraMap ℂ 𝒜 z) := (Ne.isUnit hz0).map (algebraMap ℂ 𝒜)
        have hfac : (1 : 𝒜) - z • a = algebraMap ℂ 𝒜 z * (algebraMap ℂ 𝒜 z⁻¹ - a) := by
          rw [mul_sub, ← map_mul, mul_inv_cancel₀ hz0, map_one, ← Algebra.smul_def]
        rw [hfac]
        exact hzu.mul hu
    -- `f z = z (1 - za)⁻¹` is holomorphic on `|z| < s⁻¹`
    set f : ℂ → 𝒜 := fun z => z • Ring.inverse (1 - z • a) with hfdef
    have hdiff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) s⁻¹) := by
      intro z hz
      refine DifferentiableAt.differentiableWithinAt ?_
      have hz' : ‖z‖ < s⁻¹ := by simpa [Metric.mem_ball, dist_zero_right] using hz
      have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 - w • a) z :=
        ((differentiable_id.smul_const a).const_sub 1).differentiableAt
      exact differentiableAt_id.smul (h1.inverse (hunit z hz'))
    -- the power series `∑ₙ aⁿ z^{n+1}` of `f` on `|z| < ‖a‖⁻¹`
    set c : ℕ → 𝒜 := fun n => if n = 0 then 0 else a ^ (n - 1) with hcdef
    have hsmall : ∀ z ∈ Metric.ball (0 : ℂ) ‖a‖⁻¹,
        HasSum (fun n : ℕ => (z - 0) ^ n • c n) (f z) := by
      intro z hz
      have hz' : ‖z‖ < ‖a‖⁻¹ := by simpa [Metric.mem_ball, dist_zero_right] using hz
      have hlt1 : ‖z • a‖ < 1 := by
        rw [norm_smul]
        have h := mul_lt_mul_of_pos_right hz' hanorm
        rwa [inv_mul_cancel₀ hanorm.ne'] at h
      have hgs : HasSum (fun n : ℕ => (z • a) ^ n) (∑' n : ℕ, (z • a) ^ n) :=
        (summable_geometric_of_norm_lt_one hlt1).hasSum
      have hginv : Ring.inverse (1 - z • a) = ∑' n : ℕ, (z • a) ^ n := by
        obtain ⟨-, h1, h2⟩ := geometric_2 (z • a) hlt1
        have hu : (1 : 𝒜) - z • a = ((⟨1 - z • a, ∑' n : ℕ, (z • a) ^ n, h1, h2⟩ : 𝒜ˣ) : 𝒜) := rfl
        rw [hu, Ring.inverse_unit]
        rfl
      have hfz : HasSum (fun n : ℕ => z • (z • a) ^ n) (f z) := by
        rw [hfdef]
        simp only [hginv]
        exact hgs.const_smul z
      have hshift : (fun n : ℕ => (z - 0) ^ (n + 1) • c (n + 1))
          = fun n : ℕ => z • (z • a) ^ n := by
        funext n
        have hcn : c (n + 1) = a ^ n := by simp [hcdef]
        rw [hcn, sub_zero, smul_pow, smul_smul, pow_succ']
      have h0 : f z - ∑ i ∈ Finset.range 1, (z - 0) ^ i • c i = f z := by simp [hcdef]
      rw [← hasSum_nat_add_iff' 1, hshift, h0]
      exact hfz
    -- **15VII** `rigid_expansion`: the expansion is valid on all of `|z| < s⁻¹`
    have hlt : ‖a‖⁻¹ < s⁻¹ := (inv_lt_inv₀ hanorm hs0).mpr hsa
    have hkey := rigid_expansion Metric.isOpen_ball f hdiff c 0 ‖a‖⁻¹ s⁻¹
      (by positivity) hlt hsmall (subset_refl _)
    -- but at a real `z₁` with `‖a‖⁻¹ < z₁ < s⁻¹` the series `∑ₙ (z₁a)ⁿ` diverges
    set z₁ : ℝ := (‖a‖⁻¹ + s⁻¹) / 2 with hz₁def
    have hz₁lo : ‖a‖⁻¹ < z₁ := by rw [hz₁def]; linarith
    have hz₁hi : z₁ < s⁻¹ := by rw [hz₁def]; linarith
    have hz₁pos : 0 < z₁ := lt_trans (by positivity) hz₁lo
    have hmem : (z₁ : ℂ) ∈ Metric.ball (0 : ℂ) s⁻¹ := by
      simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hz₁pos]
      exact hz₁hi
    have hsum := hkey (z₁ : ℂ) hmem
    have hz1ne : ((z₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz₁pos.ne'
    have hsummable : Summable (fun n : ℕ => ((z₁ : ℂ) • a) ^ n) := by
      have h2 : Summable (fun n : ℕ => (((z₁ : ℂ)) - 0) ^ (n + 1) • c (n + 1)) :=
        (summable_nat_add_iff 1).mpr hsum.summable
      have h3 : Summable (fun n : ℕ => (z₁ : ℂ) • ((z₁ : ℂ) • a) ^ n) := by
        refine h2.congr fun n => ?_
        have hcn : c (n + 1) = a ^ n := by simp [hcdef]
        rw [hcn, sub_zero, smul_pow, smul_smul, pow_succ']
      have h4 : (fun n : ℕ => ((z₁ : ℂ))⁻¹ • ((z₁ : ℂ) • ((z₁ : ℂ) • a) ^ n))
          = fun n : ℕ => ((z₁ : ℂ) • a) ^ n := by
        funext n
        rw [smul_smul, inv_mul_cancel₀ hz1ne, one_smul]
      have h5 := h3.const_smul ((z₁ : ℂ)⁻¹)
      rwa [h4] at h5
    have hrsa : IsSelfAdjoint ((z₁ : ℝ) : ℂ) := by
      rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal]
    have hdiv := (geometric_convergence ((z₁ : ℂ) • a) (hrsa.smul ha)).mp hsummable
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz₁pos] at hdiv
    have hone : 1 < z₁ * ‖a‖ := by
      have h := mul_lt_mul_of_pos_right hz₁lo hanorm
      rwa [inv_mul_cancel₀ hanorm.ne'] at h
    linarith

/-! **16IV** (cstar.tex:2640, Remark): for non-self-adjoint `a` the formula
may fail (e.g. `[[0,1],[0,0]]`); the general formula
`sup |spec(a)| = limsup ‖aⁿ‖^{1/n}` is not needed here.  Not converted. -/

/-- **16V** (`spectrum-non-empty`, cstar.tex:2661, Exercise): the spectrum of
a self-adjoint element of a C*-algebra `𝒜 ≠ {0}` is non-empty.  (Mathlib
proves this for arbitrary elements: `spectrum.nonempty`.)

The hypothesis `𝒜 ≠ {0}` — here `[Nontrivial 𝒜]` — is **erratum 160.50**;
without it the statement is false for the trivial C*-algebra, where every
element is invertible and so `spec(a) = ∅`. -/
theorem spectrum_nonempty [Nontrivial 𝒜] (a : 𝒜) (ha : IsSelfAdjoint a) :
    (spectrum ℂ a).Nonempty :=
  spectrum.nonempty a

/-- **16VI** (cstar.tex:2665, Exercise): for self-adjoint `a` and `λ ∈ ℝ`:
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
      -- self-adjoint element `a - λ` — its norm, by **16II** — vanishes.
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

/-- **16VII** (cstar.tex:2673, Theorem (Gelfand–Mazur for C*-algebras)):
if every non-zero element of a C*-algebra `𝒜` is invertible, then `𝒜 = ℂ`
or `𝒜 = {0}` — here: every element of `𝒜` is a scalar.  (**16VIa**,
cstar.tex:2655, Exercise, asks to prove this from **16VI**; it is merged into
this statement.) -/
theorem gelfand_mazur (h : ∀ a : 𝒜, a ≠ 0 → IsUnit a) :
    ∀ a : 𝒜, ∃ z : ℂ, a = algebraMap ℂ 𝒜 z :=
  by
    -- the solution's argument (asols.tex, `parsec-160.61`): if `𝒜 = {0}` we are
    -- done, so assume `𝒜 ≠ {0}`.  For *self-adjoint* `b` the spectrum is
    -- non-empty by **16V** `spectrum_nonempty`, so `b - λ` fails to be invertible
    -- for some `λ`; as `0` is the only non-invertible element of `𝒜`, that gives
    -- `b = λ`.  Every element `a`, being `ℜa + i·ℑa` (**7III**.1), is then a
    -- scalar too.
    intro a
    rcases subsingleton_or_nontrivial 𝒜 with _ | _
    · exact ⟨0, Subsingleton.elim _ _⟩
    · have key : ∀ b : 𝒜, IsSelfAdjoint b → ∃ z : ℂ, b = algebraMap ℂ 𝒜 z := by
        intro b hb
        obtain ⟨z, hz⟩ := spectrum_nonempty b hb
        refine ⟨z, ?_⟩
        rw [spectrum.mem_iff] at hz
        by_contra hne
        exact hz (h _ (sub_ne_zero.mpr (Ne.symm hne)))
      obtain ⟨z₁, h₁⟩ := key (ℜ a : 𝒜) (ℜ a).property
      obtain ⟨z₂, h₂⟩ := key (ℑ a : 𝒜) (ℑ a).property
      refine ⟨z₁ + Complex.I * z₂, ?_⟩
      rw [map_add, map_mul, ← h₁, ← h₂, ← Algebra.smul_def]
      exact cstar_involution_basic_1 a

/-! **16VIII** (`gelfand-mazur-predicament`, cstar.tex:2678, Remark): why the
usual Banach-algebra route to Gelfand's representation theorem is avoided —
nothing to formalize. -/

/-! ## Parsec 170 (`cstar-positive-2`): positive elements, continued -/

/-- **17II** (`real-pos-ineq`, cstar.tex:2724, Exercise): `|λ - t| ≤ t` iff
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

/-- **17III** (`pos-spectrum`, cstar.tex:2729, Proposition): for self-adjoint
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
**25I** (`cstar-positive-final`, cstar.tex:3768), sixteen parsecs further on,
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
  -- The solution's own argument (asols.tex, `parsec-170.60`(2)).  First its
  -- **17V** step, in the form the argument needs: a thesis-positive `b` with
  -- `‖b‖ ≤ t` already satisfies `‖b - t‖ ≤ t`, because
  -- `spec(b) ⊆ [0,‖b‖] ⊆ [0,2t]` and **17III** `pos_spectrum`.
  have step : ∀ (b : 𝒜) (t : ℝ), ThesisPos b → ‖b‖ ≤ t →
      ‖b - algebraMap ℂ 𝒜 (t : ℂ)‖ ≤ t := by
    intro b t hb hbt
    have ht0 : 0 ≤ t := le_trans (norm_nonneg b) hbt
    refine (pos_spectrum b hb.1 t ht0).mpr fun z hz => ?_
    obtain ⟨r, hr0, hrz⟩ := hb.spectrum_subset hz
    refine ⟨r, hr0, ?_, hrz⟩
    have hzn : ‖z‖ ≤ ‖b‖ :=
      (norm_le_iff_spectrum_norm_le b hb.1 ‖b‖ (norm_nonneg b)).mp le_rfl z hz
    rw [hrz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at hzn
    linarith
  refine IsSeqClosed.isClosed fun {f a} hf hlim => ?_
  -- `a` is self-adjoint, because `(·)*` is continuous
  have hsa : IsSelfAdjoint a := by
    have h1 : Filter.Tendsto (fun n => star (f n)) Filter.atTop (nhds (star a)) :=
      hlim.star
    have h2 : Filter.Tendsto f Filter.atTop (nhds (star a)) := by
      simpa only [fun n => (hf n).1.star_eq] using h1
    exact tendsto_nhds_unique h2 hlim
  -- the sequence converges, hence is bounded: `‖fₙ‖ ≤ t` for some `t`
  obtain ⟨t, ht⟩ := (hlim.norm).bddAbove_range
  have htn : ∀ n, ‖f n‖ ≤ t := fun n => ht ⟨n, rfl⟩
  refine ⟨hsa, t, ?_⟩
  -- `‖fₙ - t‖ ≤ t` for every `n`; take the limit over `n`
  have hconv : Filter.Tendsto (fun n => ‖f n - algebraMap ℂ 𝒜 (t : ℂ)‖)
      Filter.atTop (nhds ‖a - algebraMap ℂ 𝒜 (t : ℂ)‖) :=
    (hlim.sub tendsto_const_nhds).norm
  exact le_of_tendsto hconv (.of_forall fun n => step (f n) t (hf n) (htn n))

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

/-- **17VI**.4d for `ThesisPos`, by the thesis's own route: **11XV**.3 again,
read in the direction opposite to `thesisPos_of_pow_odd`.  The solution of
**17VI** defers the whole of point 4 to **11XV** (asols.tex:1980), and the
thesis is emphatic that the product of commuting positive elements is *not*
available before `ineq-square-root` (cstar.tex:3618); so this must not go by
induction through `square-commuting-monotone` of parsec 230, and does not:
an even power is a square (**11XV**.2) and an odd power is handled by the
`.mpr` half of **11XV**.3, both from parsec 110. -/
private theorem thesisPos_pow {a : 𝒜} (ha : ThesisPos a) : ∀ n : ℕ, ThesisPos (a ^ n) := by
  intro n
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, rfl⟩ := hn
    have h : a ^ (m + m) = (a ^ m) ^ 2 := by rw [← pow_mul, Nat.mul_two]
    rw [h]
    exact thesisPos_sq (ha.1.pow m)
  · refine (thesisPos_iff_spectrum (ha.1.pow n)).mpr fun z hz => ?_
    by_contra hcon
    simp only [Set.mem_setOf_eq] at hcon
    push_neg at hcon
    have hbase : ∀ w : ℂ, (∀ r : ℝ, 0 ≤ r → w ≠ r) → IsUnit (a - algebraMap ℂ 𝒜 w) := by
      intro w hw
      have hns : w ∉ spectrum ℂ a := fun hmem => by
        obtain ⟨r, hr0, hrw⟩ := ha.spectrum_subset hmem
        exact hw r hr0 hrw
      rw [spectrum.notMem_iff] at hns
      simpa using hns.neg
    have hu := (spectrum_self_adjoint_real_3 a ha.1 n hn).mpr hbase z hcon
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

/-- The thesis's `square-commuting-monotone` (cstar.tex:3589) for `ThesisPos`:
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

/-! #### **19III** and **24IV** for `ThesisPos` -/

/-- Auxiliary: `x + x = y + y` implies `x = y` (the algebra is a `ℂ`-vector
space).  Used to divide the thesis's identities by two. -/
private theorem eq_of_add_self_eq {x y : 𝒜} (hxy : x + x = y + y) : x = y := by
  have h2 : ((2 : ℂ))⁻¹ • ((2 : ℂ) • x) = ((2 : ℂ))⁻¹ • ((2 : ℂ) • y) := by
    rw [two_smul, two_smul, hxy]
  rwa [smul_smul, smul_smul, show ((2 : ℂ))⁻¹ * 2 = 1 by norm_num, one_smul, one_smul] at h2

/-- **19III** (`astara-non-negative`, cstar.tex:2853, Lemma) for the thesis's
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

/-- **24IV** (`astara-positive`, cstar.tex:3761, Lemma) for the thesis's
notion of positivity, transcribing the thesis's argument: `a*a` is positive.

The thesis takes `b := a ((a*a)_-)^{1/2}`; here the negative part is reached
directly as `u := |h| - h` (with `h := a*a` and `|h|` the square root of `h²`
from **23VII**), and `b := a u` already does the job, `u` being positive
because `u³ = 2|h|u²` is a product of commuting positives (**23VII**.1, here
`thesisPos_mul_of_commute`) and **11XV**.3 reads positivity back off that odd
power (`thesisPos_of_pow_odd`). -/
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

/-- **25I** (`cstar-positive-final`, cstar.tex:3768, Exercise), the part that
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

/-- **17V** (`cstar-positive-1`, cstar.tex:2747, Exercise): for a
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

/-- **17VI** (`positive-basic-2`, cstar.tex:2771, Exercise), part 1:
`0 ≤ a ≤ 0` entails `a = 0`. -/
theorem positive_basic_2_1 (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 0) : a = 0 :=
  by
    -- `le_antisymm` would close this from the `[PartialOrder 𝒜]` instance —
    -- but the antisymmetry of the positive cone *is* **17VI**.1, and taking it
    -- from the instance imports it rather than proves it.  The thesis's own
    -- argument (asols.tex:1917) is `thesisPos_antisymm`: `spec(a) ⊆ [0,∞)` and
    -- `spec(a) = -spec(-a) ⊆ (-∞,0]`, so `spec(a) = {0}` and `‖a‖ = 0`.
    exact thesisPos_antisymm (thesisPos_of_nonneg h0) (thesisPos_of_nonneg (neg_nonneg.mpr h1))

/-- **17VI** (`positive-basic-2`, cstar.tex:2771, Exercise), part 2: the set
`𝒜₊` of positive elements is closed. -/
theorem positive_basic_2_2 : IsClosed {a : 𝒜 | 0 ≤ a} :=
  by
    have hset : {a : 𝒜 | 0 ≤ a} = {a : 𝒜 | ThesisPos a} := by
      ext a; exact (thesisPos_iff_nonneg a).symm
    rw [hset]
    exact isClosed_thesisPos

/-- **17VI** (`positive-basic-2`, cstar.tex:2771, Exercise), part 3a: for
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

/-- **17VI** (`positive-basic-2`, cstar.tex:2771, Exercise), part 3b:
`‖a‖ = inf { λ ≥ 0 : -λ ≤ a ≤ λ }` for self-adjoint `a` (so `sa(𝒜)` is a
complete Archimedean order unit space).

The infimum runs over `λ ≥ 0`, not over all `λ ∈ ℝ`: that is **erratum
170.60**, incorporated in cstar.tex.  With the range restricted, the set is
`[‖a‖, ∞)` in *every* C*-algebra, the trivial one included, so no
`Subsingleton`/`Nontrivial` case split is needed. -/
theorem positive_basic_2_3b (a : 𝒜) (ha : IsSelfAdjoint a) :
    ‖a‖ = sInf {lam : ℝ | 0 ≤ lam ∧
      -(algebraMap ℂ 𝒜 (lam : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (lam : ℂ)} :=
  by
    -- the solution's own argument (asols.tex, `parsec-170.60`(3)): `‖a‖ₒ ≤ ‖a‖`
    -- because "in `parsec-90.100` we already saw that `‖a‖ₒ ≤ ‖a‖`", i.e.
    -- because `‖a‖` is itself one of the bounds (**9X**.2, `cstar_positive_2`);
    -- and `‖a‖ ≤ ‖a‖ₒ` because every bound `λ` for `a` satisfies `‖a‖ ≤ λ` by
    -- the previous paragraph (part 3a), so `‖a‖` is a lower bound of the set
    -- and hence below its infimum.  (The solution takes a decreasing sequence
    -- `λₙ ↓ ‖a‖ₒ`; `le_csInf` is that passage to the infimum.)
    have hmem : ‖a‖ ∈ {lam : ℝ | 0 ≤ lam ∧
        -(algebraMap ℂ 𝒜 (lam : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (lam : ℂ)} :=
      ⟨norm_nonneg a, (cstar_positive_2 a ha).2⟩
    have hbdd : BddBelow {lam : ℝ | 0 ≤ lam ∧
        -(algebraMap ℂ 𝒜 (lam : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (lam : ℂ)} :=
      ⟨0, fun r hr => hr.1⟩
    refine le_antisymm (le_csInf ⟨‖a‖, hmem⟩ ?_) (csInf_le hbdd hmem)
    rintro r ⟨h0, h1, h2⟩
    exact (positive_basic_2_3a a ha r h0).mp ⟨h1, h2⟩


/-- **17VI** (`positive-basic-2`, cstar.tex:2771, Exercise), part 3c:
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

/-- **17VI** (`positive-basic-2`, cstar.tex:2771, Exercise), part 4a: `a²`
is positive for self-adjoint `a`. -/
theorem positive_basic_2_4a (a : 𝒜) (ha : IsSelfAdjoint a) : 0 ≤ a ^ 2 :=
  by
    -- the thesis's route (**11XV**.2): `spec(a²) ⊆ [0,∞)`, not the Lean
    -- triviality `a² = star a * a`
    exact (thesisPos_sq ha).nonneg

/-- **17VI** (`positive-basic-2`, cstar.tex:2771, Exercise), part 4b: `aⁿ`
is positive for self-adjoint `a` and even `n`. -/
theorem positive_basic_2_4b (a : 𝒜) (ha : IsSelfAdjoint a) (n : ℕ)
    (hn : Even n) : 0 ≤ a ^ n :=
  by
    obtain ⟨m, rfl⟩ := hn
    have h : a ^ (m + m) = (a ^ m) ^ 2 := by rw [← pow_mul, Nat.mul_two]
    rw [h]
    exact (thesisPos_sq (ha.pow m)).nonneg

/-- **17VI** (`positive-basic-2`, cstar.tex:2771, Exercise), part 4c: for
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

/-- **17VI** (`positive-basic-2`, cstar.tex:2771, Exercise), part 4d: `aⁿ` is
positive for positive `a` and every `n`. -/
theorem positive_basic_2_4d (a : 𝒜) (ha : 0 ≤ a) (n : ℕ) : 0 ≤ a ^ n :=
  (thesisPos_pow (thesisPos_of_nonneg ha) n).nonneg

/-- **17VI** (`positive-basic-2`, cstar.tex:2771, Exercise), part 5: for
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

/-- **17VI** (`positive-basic-2`, cstar.tex:2771, Exercise), part 6: a
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

**18I** (cstar.tex:2823): moved to `cstar-product-2` (20aI below) — nothing to
formalize.  **19I** (cstar.tex:2827): introduction — nothing to formalize. -/

/-- **19Ia** (`prod-spec`, cstar.tex:2834, Lemma): for elements `a`, `b` of a
C*-algebra, `spec(ab) \ {0} = spec(ba) \ {0}`. -/
theorem prod_spec (a b : 𝒜) :
    spectrum ℂ (a * b) \ {0} = spectrum ℂ (b * a) \ {0} :=
  spectrum.nonzero_mul_comm a b

/-- **19III** (`astara-non-negative`, cstar.tex:2853, Lemma):
`a* a ≤ 0` implies `a = 0`. -/
theorem astara_non_negative [PartialOrder 𝒜] [StarOrderedRing 𝒜] (a : 𝒜)
    (h : star a * a ≤ 0) : a = 0 :=
  by
    -- Under Mathlib's star order `0 ≤ star a * a` holds by definition, so
    -- `le_antisymm h (star_mul_self_nonneg a)` closes this in one line — but
    -- that line is **24IV**, which the thesis proves *from* this Lemma.  The
    -- thesis's parsec-190 argument is `thesisPos_astara_non_negative` above,
    -- and it is what is used here.  (The residual appeal to **24IV** through
    -- `thesisPos_of_nonneg` is the 25I bridge, unavoidable in this encoding:
    -- the hypothesis is stated with Mathlib's `≤`.  Under that encoding the
    -- *statement* carries no content; `thesisPos_astara_non_negative` is the
    -- real transcription of **19III**.)
    exact thesisPos_astara_non_negative (thesisPos_of_nonneg (neg_nonneg.mpr h))

end Holomorphic

/-! ## Parsec 200: positive maps are bounded; bipositive maps -/

section Maps

variable {𝒜 ℬ : Type*} [CStarAlgebra 𝒜] [CStarAlgebra ℬ]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **20II** (`weak-russo-dye`, cstar.tex:2884, Lemma), part 1: a positive
map `f : 𝒜 → ℬ` between C*-algebras satisfies `‖f(a)‖ ≤ ‖f(1)‖ ‖a‖` for
self-adjoint `a`. -/
theorem weak_russo_dye_1 (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) (a : 𝒜)
    (ha : IsSelfAdjoint a) : ‖f a‖ ≤ ‖f 1‖ * ‖a‖ :=
  by
    have hfsa : IsSelfAdjoint (f a) := by
      -- `a = (‖a‖ + a) - ‖a‖` with both terms positive (**17VI**.3a); the
      -- positive/negative parts are only available at parsec 240.  This is
      -- **10V**'s argument inline.  20II.1's use of "`f a` is self-adjoint"
      -- is not a gap: **10V** proves it ten parsecs earlier (author's ruling,
      -- 2026-08-22).  Citing **10IV** `cstar_p_implies_i` instead would be one
      -- line, but it is CFC-reachable through the parsec-90 order bridge, and
      -- 20II.1 is deliberately kept off that bridge; the inline copy of 10V
      -- goes through `ThesisPos` and stays off it.
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
    -- `-‖a‖ ≤ a ≤ ‖a‖` and `f 1 ≤ ‖f 1‖` are **17VI**.3a, `positive_basic_2_3a`
    -- — the thesis's own parsec-170 theorem, which is what erratum
    -- `parsec-200.30` cites here.  (Mathlib's `le_algebraMap_norm_self` and
    -- `A/CStar/Basic`'s `norm_le_iff_neg_algebraMap_le`, used here before, are
    -- the CFC-backed forms of the same statement, at parsec 90.)
    obtain ⟨hlow, hup⟩ := (positive_basic_2_3a a ha ‖a‖ (norm_nonneg a)).mpr le_rfl
    have hfalg : f (algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ)) = ((‖a‖ : ℝ) : ℂ) • f 1 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul]
    have hf1 : f 1 ≤ algebraMap ℂ ℬ ((‖f 1‖ : ℝ) : ℂ) :=
      ((positive_basic_2_3a (f 1) (IsSelfAdjoint.of_nonneg (hf 1 zero_le_one)) ‖f 1‖
        (norm_nonneg _)).mpr le_rfl).2
    have hkey : ((‖a‖ : ℝ) : ℂ) • f 1 ≤ algebraMap ℂ ℬ (((‖f 1‖ * ‖a‖ : ℝ)) : ℂ) := by
      have h3 : (0 : ℬ) ≤ ((‖a‖ : ℝ) : ℂ) • (algebraMap ℂ ℬ ((‖f 1‖ : ℝ) : ℂ) - f 1) :=
        ofReal_smul_nonneg (sub_nonneg.mpr hf1) (norm_nonneg a)
      rw [smul_sub, sub_nonneg] at h3
      refine h3.trans (le_of_eq ?_)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul,
        ← Complex.ofReal_mul, mul_comm]
    refine (positive_basic_2_3a (f a) hfsa (‖f 1‖ * ‖a‖) hM).mp ?_
    constructor
    · have h4 := hmono _ _ hlow
      rw [map_neg, hfalg] at h4
      exact (neg_le_neg hkey).trans h4
    · have h5 := hmono _ _ hup
      rw [hfalg] at h5
      exact h5.trans hkey

/-- **20II** (`weak-russo-dye`, cstar.tex:2884, Lemma), part 2: a positive
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

/-! **20IV** (`russo-dye-remark`, cstar.tex:2907, Remark): the factor 2 can
be dropped — proved for cp-maps at 34XVI (`cp_russo_dye`) and for positive
maps at 34aVIII (`russo_dye_cor`); not converted separately. -/

/-- **20V** (`norm-mi-map`, cstar.tex:2919, Lemma), part 1: every miu-map
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

/-- **20V** (`norm-mi-map`, cstar.tex:2919, Lemma), part 2: every miu-map
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

/-- **20VI** (`cstar-isometry`, cstar.tex:2949, Lemma): for a pu-map
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

/-- **20aI** (`cstar-product-2`, cstar.tex:3030, Exercise), part 1: the
direct sum `⊕ᵢ 𝒜ᵢ` (Mathlib: `lp 𝒜 ∞`, cf. **3V**) is the categorical
product in `CStar_miu`: for every C*-algebra `ℬ` and family of miu-maps
`fᵢ : ℬ → 𝒜ᵢ` there is a unique miu-map `g : ℬ → ⊕ᵢ 𝒜ᵢ` with `πᵢ ∘ g = fᵢ`
(and, by `cstar_product_2_comm` below, the same in `cCStar_miu`).

The `[∀ i, Nontrivial (𝒜 i)]` binder is Mathlib's, not the Exercise's: it is
what Mathlib's only unital ring structure on `lp 𝒜 ∞` demands (the same note
stands on 47IV in `A/VN/Basic`). -/
theorem cstar_product_2_miu {ι : Type*} {𝒜 : ι → Type*}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, Nontrivial (𝒜 i)] {ℬ : Type*}
    [CStarAlgebra ℬ] (f : ∀ i, ℬ →⋆ₐ[ℂ] 𝒜 i) :
    ∃! g : ℬ →⋆ₐ[ℂ] lp 𝒜 ∞, ∀ (i : ι) (b : ℬ),
      (g b : ∀ i, 𝒜 i) i = f i b :=
  by
    -- The solution's construction (asols.tex:2053-2062, read for miu-maps at
    -- asols.tex:2085-2088): `g(b)(i) = f_i(b)` defines an element of
    -- `⊕ᵢ 𝒜ᵢ` because the `f_i` are bounded -- the Exercise's own hint,
    -- "use here that the projections `π_j` are bounded by `norm-mi-map`",
    -- i.e. **20V** `norm_mi_map_contractive` above.  `g` is then clearly miu,
    -- and unique because `g'(b)(i) = π_i(g'(b)) = f_i(b) = g(b)(i)`.
    have hmem : ∀ b : ℬ, Memℓp (fun i => f i b) ∞ := fun b =>
      memℓp_infty ⟨‖b‖, by
        rintro y ⟨i, rfl⟩
        -- `norm_mi_map_contractive` above is this statement under its thesis
        -- name; it cannot be cited here, because its section carries order
        -- instances on the two algebras that `⊕ᵢ 𝒜ᵢ` has no reason to have.
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

/-- Auxiliary for `lpInftyNontrivialEquiv`: extend a family indexed by the
nontrivial summands `J = {i // Nontrivial (𝒜 i)}` by `0` on the trivial ones.
(Classical `dite`: `Nontrivial` is not decidable.) -/
noncomputable def lpInftyExtend {ι : Type*} {𝒜 : ι → Type*} [∀ i, CStarAlgebra (𝒜 i)]
    (y : ∀ j : {i // Nontrivial (𝒜 i)}, 𝒜 j) (i : ι) : 𝒜 i :=
  @dite (𝒜 i) (Nontrivial (𝒜 i)) (Classical.propDecidable _) (fun h => y ⟨i, h⟩) fun _ => 0

@[simp]
theorem lpInftyExtend_coe {ι : Type*} {𝒜 : ι → Type*} [∀ i, CStarAlgebra (𝒜 i)]
    (y : ∀ j : {i // Nontrivial (𝒜 i)}, 𝒜 j) (j : {i // Nontrivial (𝒜 i)}) :
    lpInftyExtend y j = y j :=
  dite_eq_left j.2

theorem lpInftyExtend_of_not_nontrivial {ι : Type*} {𝒜 : ι → Type*} [∀ i, CStarAlgebra (𝒜 i)]
    (y : ∀ j : {i // Nontrivial (𝒜 i)}, 𝒜 j) {i : ι} (h : ¬ Nontrivial (𝒜 i)) :
    lpInftyExtend y i = 0 :=
  dite_eq_right h

/-- Zero summands contribute nothing to an `ℓ^∞`-direct sum: restriction to the
nontrivial indices `J := {i // Nontrivial (𝒜 i)}` is an isomorphism of
non-unital star algebras (isometric: `norm_lpInftyNontrivialEquiv`).  This is
why the `[∀ i, Nontrivial (𝒜 i)]` binder that Mathlib's unital structure on
`lp 𝒜 ∞` demands costs no content: over `J` the binder holds by `fun j => j.2`,
so every gated statement about `⊕ᵢ𝒜ᵢ` in this tree covers the printed one
after this identification.

(Mathlib has no separate *non-unital* star-algebra equivalence: `StarAlgEquiv`,
`≃⋆ₐ[ℂ]`, *is* the non-unital notion — it asks for addition, multiplication,
scalar multiplication and `star`, and never for `1`.  It is therefore the right
target here, where the left-hand side need not be unital.) -/
noncomputable def lpInftyNontrivialEquiv {ι : Type*} (𝒜 : ι → Type*)
    [∀ i, CStarAlgebra (𝒜 i)] :
    lp 𝒜 ∞ ≃⋆ₐ[ℂ] lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞ where
  toFun x :=
    ⟨fun j => (x : ∀ i, 𝒜 i) j, memℓp_infty ⟨‖x‖, by
      rintro _ ⟨j, rfl⟩
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero x j⟩⟩
  invFun y :=
    ⟨lpInftyExtend (⇑y), memℓp_infty ⟨‖y‖, by
      rintro _ ⟨i, rfl⟩
      show ‖lpInftyExtend (⇑y) i‖ ≤ ‖y‖
      by_cases h : Nontrivial (𝒜 i)
      · rw [show lpInftyExtend (⇑y) i = y ⟨i, h⟩ from dite_eq_left h]
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero y ⟨i, h⟩
      · rw [lpInftyExtend_of_not_nontrivial _ h, norm_zero]
        exact norm_nonneg y⟩⟩
  left_inv x := by
    refine lp.ext (funext fun i => ?_)
    by_cases h : Nontrivial (𝒜 i)
    · exact dite_eq_left h
    · have := not_nontrivial_iff_subsingleton.mp h
      exact (dite_eq_right h).trans (Subsingleton.elim _ _)
  right_inv y := lp.ext (funext fun j => lpInftyExtend_coe (⇑y) j)
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

theorem lpInftyNontrivialEquiv_apply {ι : Type*} (𝒜 : ι → Type*) [∀ i, CStarAlgebra (𝒜 i)]
    (x : lp 𝒜 ∞) (j : {i // Nontrivial (𝒜 i)}) :
    (lpInftyNontrivialEquiv 𝒜 x : ∀ j : {i // Nontrivial (𝒜 i)}, 𝒜 j) j = (x : ∀ i, 𝒜 i) j :=
  rfl

/-- `lpInftyNontrivialEquiv` is isometric: both norms are the supremum of the
coordinate norms, and the coordinates it forgets are `0`. -/
theorem norm_lpInftyNontrivialEquiv {ι : Type*} (𝒜 : ι → Type*) [∀ i, CStarAlgebra (𝒜 i)]
    (x : lp 𝒜 ∞) : ‖lpInftyNontrivialEquiv 𝒜 x‖ = ‖x‖ := by
  refine le_antisymm (lp.norm_le_of_forall_le (norm_nonneg x) fun j => ?_)
    (lp.norm_le_of_forall_le (norm_nonneg _) fun i => ?_)
  · rw [lpInftyNontrivialEquiv_apply]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero x j
  · by_cases h : Nontrivial (𝒜 i)
    · have hle := lp.norm_apply_le_norm ENNReal.top_ne_zero
        (lpInftyNontrivialEquiv 𝒜 x) ⟨i, h⟩
      rwa [lpInftyNontrivialEquiv_apply] at hle
    · have := not_nontrivial_iff_subsingleton.mp h
      rw [show (x : ∀ i, 𝒜 i) i = 0 from Subsingleton.elim _ _, norm_zero]
      exact norm_nonneg _

/-- **20aI** (`cstar-product-2`, cstar.tex:3030, Exercise), the Exercise's
hint for the `pu` half: an element of `⊕ᵢ 𝒜ᵢ` is positive iff all of its
components are.  The `pu` universal property it is a hint *for* is
`cstar_product_2_pu` below. -/
theorem cstar_product_2_positive {ι : Type*} {𝒜 : ι → Type*}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, Nontrivial (𝒜 i)]
    [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [PartialOrder (lp 𝒜 ∞)] [StarOrderedRing (lp 𝒜 ∞)] (a : lp 𝒜 ∞) :
    0 ≤ a ↔ ∀ i, 0 ≤ (a : ∀ i, 𝒜 i) i :=
  by
    -- The solution's argument (asols.tex, `parsec-201.10`) runs the thesis's
    -- norm criterion (**17V**, parsec 170) in *both* directions: since
    -- `‖a‖ = supᵢ ‖a(i)‖`, one has `‖a(i)‖ ≤ ‖a‖`, and so `a` is positive iff
    -- `‖a - ‖a‖‖ ≤ ‖a‖` iff `‖a(i) - ‖a‖‖ ≤ ‖a‖` for every `i` iff every `a(i)`
    -- is positive.  A single `t` therefore serves all the components at once,
    -- and no square root — hence no continuous functional calculus, which the
    -- thesis reaches only at parsec 270 — is needed in either direction.
    have hco : ∀ (t : ℝ) (i : ι),
        ((a - algebraMap ℂ (lp 𝒜 ∞) (t : ℂ) : lp 𝒜 ∞) : ∀ i, 𝒜 i) i
          = (a : ∀ i, 𝒜 i) i - algebraMap ℂ (𝒜 i) (t : ℂ) := by
      intro t i
      rw [lp.coeFn_sub]
      rfl
    constructor
    · intro h i
      have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg h
      have hsai : IsSelfAdjoint ((a : ∀ i, 𝒜 i) i) := by
        have := congrFun (congrArg (fun x : lp 𝒜 ∞ => (x : ∀ i, 𝒜 i))
          hsa.star_eq) i
        rwa [lp.coeFn_star] at this
      set t : ℝ := ‖a‖ / 2 with ht
      -- `0 ≤ a` gives `‖a - t‖ ≤ t` for every `t ≥ ‖a‖/2` (**17V**, 4 → 2)
      have hAiff : (0 : lp 𝒜 ∞) ≤ a ↔
          ∀ s : ℝ, ‖a‖ / 2 ≤ s → ‖a - algebraMap ℂ (lp 𝒜 ∞) (s : ℂ)‖ ≤ s :=
        (cstar_positive_tfae a hsa).out 3 1
      have hA : ‖a - algebraMap ℂ (lp 𝒜 ∞) (t : ℂ)‖ ≤ t := hAiff.mp h t le_rfl
      -- the norm on `⊕ᵢ 𝒜ᵢ` is a supremum, so the same `t` works componentwise
      have hAi : ‖(a : ∀ i, 𝒜 i) i - algebraMap ℂ (𝒜 i) (t : ℂ)‖ ≤ t := by
        have hle := lp.norm_apply_le_norm ENNReal.top_ne_zero
          (a - algebraMap ℂ (lp 𝒜 ∞) (t : ℂ)) i
        rw [hco t i] at hle
        linarith
      -- and back to positivity of the component, again by **17V** (1 → 4)
      have hti : ‖(a : ∀ i, 𝒜 i) i‖ / 2 ≤ t := by
        have := lp.norm_apply_le_norm ENNReal.top_ne_zero a i
        rw [ht]; linarith
      have hiff : (∃ s : ℝ, ‖(a : ∀ i, 𝒜 i) i‖ / 2 ≤ s ∧
          ‖(a : ∀ i, 𝒜 i) i - algebraMap ℂ (𝒜 i) (s : ℂ)‖ ≤ s) ↔
            (0 : 𝒜 i) ≤ (a : ∀ i, 𝒜 i) i :=
        (cstar_positive_tfae ((a : ∀ i, 𝒜 i) i) hsai).out 0 3
      exact hiff.mp ⟨t, hti, hAi⟩
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
      rw [hco t i]
      exact hai i

/-- **20aI** (`cstar-product-2`, cstar.tex:3030, Exercise): the direct sum of
*commutative* C*-algebras is again commutative — which is what makes
`cstar_product_2_miu` and `cstar_product_2_pu` below the descriptions of the
product in `cCStar_miu` and `cCStar_pu` as well, as the Exercise asks. -/
theorem cstar_product_2_comm {ι : Type*} {𝒜 : ι → Type*}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, Nontrivial (𝒜 i)]
    (hcomm : ∀ (i : ι) (x y : 𝒜 i), x * y = y * x) (a b : lp 𝒜 ∞) :
    a * b = b * a :=
  by
    refine lp.ext ?_
    funext i
    exact hcomm i _ _

/-- **20aI** (`cstar-product-2`, cstar.tex:3030, Exercise), the `pu` half:
`⊕ᵢ 𝒜ᵢ` is also the categorical product in `CStar_pu` (and, by
`cstar_product_2_comm`, in `cCStar_pu`): for every C*-algebra `ℬ` and family
of pu-maps `fᵢ : ℬ → 𝒜ᵢ` there is a unique pu-map `g : ℬ → ⊕ᵢ 𝒜ᵢ` with
`πᵢ ∘ g = fᵢ`.

*Class 1 — faithful*: the mediating map is the tuple `b ↦ (fᵢ b)ᵢ`; it lands
in `⊕ᵢ 𝒜ᵢ` because the `fᵢ` are bounded — the Exercise's hint, here in the
pu form of **20II**.2, `‖f b‖ ≤ 2‖f 1‖‖b‖ = 2‖b‖` — and it is positive by
the Exercise's *other* hint, `cstar_product_2_positive`.

The `[∀ i, Nontrivial (𝒜 i)]` binder is Mathlib's, not the Exercise's: it is
what Mathlib's only unital ring structure on `lp 𝒜 ∞` demands (cf. the same
note on 47IV in `A/VN/Basic`).  The order binders on `lp 𝒜 ∞` record that
this file assumes the C*-order on the product rather than constructing it,
as it does for every other C*-algebra in the file. -/
theorem cstar_product_2_pu {ι : Type*} {𝒜 : ι → Type*}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, Nontrivial (𝒜 i)]
    [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [PartialOrder (lp 𝒜 ∞)] [StarOrderedRing (lp 𝒜 ∞)]
    {ℬ : Type*} [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    (f : ∀ i, ℬ →ₗ[ℂ] 𝒜 i) (hp : ∀ i, IsPositiveMap (f i))
    (hu : ∀ i, IsUnitalMap (f i)) :
    ∃! g : ℬ →ₗ[ℂ] lp 𝒜 ∞, IsPositiveMap g ∧ IsUnitalMap g ∧
      ∀ (i : ι) (b : ℬ), (g b : ∀ i, 𝒜 i) i = f i b :=
  by
    have hmem : ∀ b : ℬ, Memℓp (fun i => f i b) ∞ := fun b =>
      memℓp_infty ⟨2 * ‖b‖, by
        rintro y ⟨i, rfl⟩
        exact norm_map_le_two_mul (f i) (hp i) (hu i) b⟩
    refine ⟨{ toFun := fun b => ⟨fun i => f i b, hmem b⟩
              map_add' := fun x y => by ext i; exact map_add (f i) x y
              map_smul' := fun r x => by ext i; exact map_smul (f i) r x },
            ⟨?_, ?_, fun _ _ => rfl⟩, ?_⟩
    · intro b hb
      refine (cstar_product_2_positive _).mpr fun i => ?_
      exact hp i b hb
    · have hu' : ∀ j, (f j) 1 = 1 := hu
      show (⟨fun i => f i 1, hmem 1⟩ : lp 𝒜 ∞) = 1
      ext i
      simpa using hu' i
    · rintro g' ⟨-, -, hg'⟩
      ext b i
      exact hg' i b

/-! ### 20aI over the nontrivial summands only

The four statements above carry Mathlib's `[∀ i, Nontrivial (𝒜 i)]`, which the
Exercise does not.  Restated over `J = {i // Nontrivial (𝒜 i)}` the binder is
*discharged* rather than assumed (`fun j => j.2`), and by
`lpInftyNontrivialEquiv` above `⊕_{j : J} 𝒜ⱼ` is the printed `⊕ᵢ𝒜ᵢ` — so the
primed corollaries below are the Exercise's statements as printed.

The discharge has to be a `local instance`, not a `haveI` inside each proof:
the *statements* already mention `lp` structures that Mathlib gates on the
binder (`→⋆ₐ[ℂ]`, `1`, `≤`), so the instance must be available while the type
is elaborated. -/

section NontrivialSummands

private theorem nontrivial_of_nontrivialIndex {ι : Type*} {𝒜 : ι → Type*}
    (j : {i // Nontrivial (𝒜 i)}) : Nontrivial (𝒜 j) := j.2

attribute [local instance] nontrivial_of_nontrivialIndex

/-- **20aI** `cstar_product_2_miu` without the Mathlib binder: over the
nontrivial indices, which is the whole sum up to `lpInftyNontrivialEquiv`. -/
theorem cstar_product_2_miu' {ι : Type*} {𝒜 : ι → Type*}
    [∀ i, CStarAlgebra (𝒜 i)] {ℬ : Type*} [CStarAlgebra ℬ]
    (f : ∀ j : {i // Nontrivial (𝒜 i)}, ℬ →⋆ₐ[ℂ] 𝒜 j) :
    ∃! g : ℬ →⋆ₐ[ℂ] lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞,
      ∀ (j : {i // Nontrivial (𝒜 i)}) (b : ℬ),
        (g b : ∀ j : {i // Nontrivial (𝒜 i)}, 𝒜 j) j = f j b :=
  cstar_product_2_miu f

/-- **20aI** `cstar_product_2_positive` without the Mathlib binder: over the
nontrivial indices, which is the whole sum up to `lpInftyNontrivialEquiv`. -/
theorem cstar_product_2_positive' {ι : Type*} {𝒜 : ι → Type*}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [PartialOrder (lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞)]
    [StarOrderedRing (lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞)]
    (a : lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞) :
    0 ≤ a ↔ ∀ j : {i // Nontrivial (𝒜 i)},
      0 ≤ (a : ∀ j : {i // Nontrivial (𝒜 i)}, 𝒜 j) j :=
  cstar_product_2_positive a

/-- **20aI** `cstar_product_2_comm` without the Mathlib binder: over the
nontrivial indices, which is the whole sum up to `lpInftyNontrivialEquiv`. -/
theorem cstar_product_2_comm' {ι : Type*} {𝒜 : ι → Type*} [∀ i, CStarAlgebra (𝒜 i)]
    (hcomm : ∀ (i : ι) (x y : 𝒜 i), x * y = y * x)
    (a b : lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞) : a * b = b * a :=
  cstar_product_2_comm (𝒜 := fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) (fun j => hcomm j) a b

/-- **20aI** `cstar_product_2_pu` without the Mathlib binder: over the
nontrivial indices, which is the whole sum up to `lpInftyNontrivialEquiv`. -/
theorem cstar_product_2_pu' {ι : Type*} {𝒜 : ι → Type*}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [PartialOrder (lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞)]
    [StarOrderedRing (lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞)]
    {ℬ : Type*} [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    (f : ∀ j : {i // Nontrivial (𝒜 i)}, ℬ →ₗ[ℂ] 𝒜 j) (hp : ∀ j, IsPositiveMap (f j))
    (hu : ∀ j, IsUnitalMap (f j)) :
    ∃! g : ℬ →ₗ[ℂ] lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞,
      IsPositiveMap g ∧ IsUnitalMap g ∧
        ∀ (j : {i // Nontrivial (𝒜 i)}) (b : ℬ),
          (g b : ∀ j : {i // Nontrivial (𝒜 i)}, 𝒜 j) j = f j b :=
  cstar_product_2_pu f hp hu

end NontrivialSummands

/-- **20aII** (`cstar-equaliser-1`, cstar.tex:3059, Exercise): for miu-maps
`f, g : 𝒜 → ℬ` the set `ℰ = {a : f(a) = g(a)}` is a (closed) C*-subalgebra
of `𝒜`.  This is the Exercise's *first* clause only; that the inclusion is a
positive miu-map and *is* the equaliser of `f` and `g` in `CStar_miu` and
`CStar_pu` (and in the commutative variants) is `cstar_equaliser_2_positive`,
`cstar_equaliser_2_miu` and `cstar_equaliser_2_pu` below.

(**20aIII**, `cstar-no-pu-equalisers`, cstar.tex:3073, Remark: pu-maps need
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

section Equaliser

variable {𝒜 ℬ : Type*} [CStarAlgebra 𝒜] [CStarAlgebra ℬ]

/-- **20aII** (`cstar-equaliser-1`, cstar.tex:3059, Exercise): the equaliser
`ℰ = {a ∈ 𝒜 : f(a) = g(a)}` of two miu-maps, as a ∗-subalgebra of `𝒜`.
`cstar_equaliser_1` above says it is a *closed* one, i.e. a C*-subalgebra;
the instance below records that closedness, which is what puts a C*-algebra
structure on `ℰ` as a type and lets the universal property be stated. -/
def cstarEqualiser (f g : 𝒜 →⋆ₐ[ℂ] ℬ) : StarSubalgebra ℂ 𝒜 :=
  StarAlgHom.equalizer f g

@[simp]
theorem mem_cstarEqualiser {f g : 𝒜 →⋆ₐ[ℂ] ℬ} {a : 𝒜} :
    a ∈ cstarEqualiser f g ↔ f a = g a :=
  StarAlgHom.mem_equalizer f g a

/-- `ℰ` is norm-closed: miu-maps are contractive (**20V**), hence
continuous, so `ℰ` is an equaliser of continuous maps. -/
instance isClosed_cstarEqualiser (f g : 𝒜 →⋆ₐ[ℂ] ℬ) :
    IsClosed ((cstarEqualiser f g : StarSubalgebra ℂ 𝒜) : Set 𝒜) :=
  by
    have hc : ∀ φ : 𝒜 →⋆ₐ[ℂ] ℬ, Continuous φ := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ 1
        (fun a => by simpa using NonUnitalStarAlgHom.norm_apply_le φ a)
    have hset : ((cstarEqualiser f g : StarSubalgebra ℂ 𝒜) : Set 𝒜)
        = {a : 𝒜 | f a = g a} := by
      ext a; exact StarAlgHom.mem_equalizer f g a
    rw [hset]
    exact isClosed_eq (hc f) (hc g)

/-- **20aII** (`cstar-equaliser-1`, cstar.tex:3059, Exercise), second
clause: the inclusion `e : ℰ → 𝒜` is a positive miu-map.  It is an miu-map
because it is a unital ∗-homomorphism; positivity is **20V**.1. -/
theorem cstar_equaliser_2_positive [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (f g : 𝒜 →⋆ₐ[ℂ] ℬ) [PartialOrder (cstarEqualiser f g)]
    [StarOrderedRing (cstarEqualiser f g)] :
    IsPositiveMap ((cstarEqualiser f g).subtype.toAlgHom.toLinearMap) :=
  fun a ha => norm_mi_map_positive (cstarEqualiser f g).subtype a ha

/-- Auxiliary (**20aII**): an injective *isometric* unital ∗-homomorphism
reflects positivity.  The argument is the thesis's own norm criterion for
positivity (**17V**): `0 ≤ ι x` gives `‖ι x - t‖ ≤ t` at `t = ‖ι x‖/2`, and
both norms are unchanged by `ι`, so `‖x - t‖ ≤ t` at `t = ‖x‖/2`.  For the
inclusion of a C*-subalgebra the isometry hypothesis holds by definition of
the subspace norm; in general it is **29VIII**, which is downstream. -/
private theorem nonneg_of_map_nonneg {ℰ : Type*} [CStarAlgebra ℰ]
    [PartialOrder ℰ] [StarOrderedRing ℰ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (ι : ℰ →⋆ₐ[ℂ] 𝒜) (hinj : Function.Injective ι)
    (hiso : ∀ x : ℰ, ‖ι x‖ = ‖x‖) (x : ℰ) (h : 0 ≤ ι x) : 0 ≤ x :=
  by
    have hisa : IsSelfAdjoint (ι x) := IsSelfAdjoint.of_nonneg h
    have hsa : IsSelfAdjoint x := hinj (by rw [map_star, hisa.star_eq])
    have ht' : ‖ι x‖ / 2 ≤ ‖x‖ / 2 := by rw [hiso]
    have hfwd : (0 : 𝒜) ≤ ι x ↔
        ∀ t : ℝ, ‖ι x‖ / 2 ≤ t → ‖ι x - algebraMap ℂ 𝒜 (t : ℂ)‖ ≤ t :=
      (cstar_positive_tfae (ι x) hisa).out 3 1
    have h2 : ‖ι x - algebraMap ℂ 𝒜 ((‖x‖ / 2 : ℝ) : ℂ)‖ ≤ ‖x‖ / 2 :=
      hfwd.mp h (‖x‖ / 2) ht'
    have h3 : ι (x - algebraMap ℂ ℰ ((‖x‖ / 2 : ℝ) : ℂ))
        = ι x - algebraMap ℂ 𝒜 ((‖x‖ / 2 : ℝ) : ℂ) := by
      rw [map_sub]
      congr 1
      exact AlgHomClass.commutes ι _
    rw [← h3, hiso] at h2
    have hbwd : (∃ t : ℝ, ‖x‖ / 2 ≤ t ∧ ‖x - algebraMap ℂ ℰ (t : ℂ)‖ ≤ t) ↔ (0 : ℰ) ≤ x :=
      (cstar_positive_tfae x hsa).out 0 3
    exact hbwd.mp ⟨‖x‖ / 2, le_rfl, h2⟩

/-- **20aII** (`cstar-equaliser-1`, cstar.tex:3059, Exercise), third clause,
in `CStar_miu` (and, `𝒜` being commutative, in `cCStar_miu`): the inclusion
`e : ℰ → 𝒜` **is** the equaliser of `f` and `g` — every miu-map
`h : 𝒞 → 𝒜` with `f ∘ h = g ∘ h` factors through `e` by a unique miu-map.

*Class 1 — faithful*: the factorisation is set-theoretic, `h` corestricted
to `ℰ`, which is where its values already lie. -/
theorem cstar_equaliser_2_miu (f g : 𝒜 →⋆ₐ[ℂ] ℬ) {𝒞 : Type*} [CStarAlgebra 𝒞]
    (h : 𝒞 →⋆ₐ[ℂ] 𝒜) (hfg : ∀ c : 𝒞, f (h c) = g (h c)) :
    ∃! m : 𝒞 →⋆ₐ[ℂ] cstarEqualiser f g,
      ∀ c : 𝒞, ((m c : 𝒜)) = h c :=
  by
    have hmem : ∀ c : 𝒞, h c ∈ cstarEqualiser f g := fun c =>
      mem_cstarEqualiser.mpr (hfg c)
    refine ⟨StarAlgHom.codRestrict h _ hmem, fun _ => rfl, ?_⟩
    intro m' hm'
    ext c
    exact hm' c

/-- **20aII** (`cstar-equaliser-1`, cstar.tex:3059, Exercise), third clause,
in `CStar_pu` (and, `𝒜` being commutative, in `cCStar_pu`): the same
inclusion is the equaliser of `f` and `g` for *pu*-maps — every pu-map
`h : 𝒞 → 𝒜` with `f ∘ h = g ∘ h` factors through `e` by a unique pu-map.

*Class 1 — faithful*: the mediating map is again `h` corestricted; it is
unital because `e` is injective and `e(1) = 1`, and positive because `e`
reflects positivity — for the inclusion of a C*-subalgebra the norm is the
restricted one, so `nonneg_of_map_nonneg` applies with `hiso := rfl`. -/
theorem cstar_equaliser_2_pu [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (f g : 𝒜 →⋆ₐ[ℂ] ℬ) [PartialOrder (cstarEqualiser f g)]
    [StarOrderedRing (cstarEqualiser f g)] {𝒞 : Type*} [CStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] (h : 𝒞 →ₗ[ℂ] 𝒜)
    (hp : IsPositiveMap h) (hu : IsUnitalMap h) (hfg : ∀ c : 𝒞, f (h c) = g (h c)) :
    ∃! m : 𝒞 →ₗ[ℂ] cstarEqualiser f g,
      IsPositiveMap m ∧ IsUnitalMap m ∧ ∀ c : 𝒞, ((m c : 𝒜)) = h c :=
  by
    set e := (cstarEqualiser f g).subtype with he
    have heinj : Function.Injective e := Subtype.val_injective
    have heiso : ∀ x : cstarEqualiser f g, ‖e x‖ = ‖x‖ := fun _ => rfl
    have hmem : ∀ c : 𝒞, h c ∈ cstarEqualiser f g := fun c =>
      mem_cstarEqualiser.mpr (hfg c)
    -- the corestriction of `h`, as a linear map
    refine ⟨{ toFun := fun c => ⟨h c, hmem c⟩
              map_add' := fun x y => by ext; simp
              map_smul' := fun r x => by ext; simp }, ⟨?_, ?_, fun _ => rfl⟩, ?_⟩
    · intro c hc
      refine nonneg_of_map_nonneg e heinj heiso _ ?_
      exact hp c hc
    · refine heinj ?_
      show (h 1 : 𝒜) = ((1 : cstarEqualiser f g) : 𝒜)
      rw [hu]
      rfl
    · rintro m' ⟨-, -, hm'⟩
      ext c
      exact hm' c


end Equaliser

end Products

/-! ## Parsec 210: separating collections of maps -/

section Separating

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
variable {ι : Type*} {ℬf : ι → Type*} [∀ i, CStarAlgebra (ℬf i)]
  [∀ i, PartialOrder (ℬf i)] [∀ i, StarOrderedRing (ℬf i)]

/-- **21II** (`separating`, cstar.tex:3113, Definition), part 1: a collection
`Ω` of linear maps on a C*-algebra `𝒜` (formalized as an indexed family with
possibly varying codomains) is *order separating* if `a` is positive iff
`ω(a) ≥ 0` for all `ω ∈ Ω`. -/
def OrderSeparating (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i) : Prop :=
  ∀ a : 𝒜, 0 ≤ a ↔ ∀ i, 0 ≤ ω i a

/-- **21II** (`separating`, cstar.tex:3113, Definition), part 2: `Ω` is
*separating* if `a = 0` iff `ω(a) = 0` for all `ω ∈ Ω`. -/
def Separating (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i) : Prop :=
  ∀ a : 𝒜, a = 0 ↔ ∀ i, ω i a = 0

/-- **21II** (`separating`, cstar.tex:3113, Definition), part 3: `Ω` is
*faithful* if a positive `a` is zero iff `ω(a) = 0` for all `ω ∈ Ω`. -/
def Faithful (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i) : Prop :=
  ∀ a : 𝒜, 0 ≤ a → (a = 0 ↔ ∀ i, ω i a = 0)

/-- **21II** (`separating`, cstar.tex:3113, Definition), part 4: `Ω` is
*centre separating* if a positive `a` is zero iff `ω(b* a b) = 0` for all
`ω ∈ Ω` and `b ∈ 𝒜`. -/
def CentreSeparating (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i) : Prop :=
  ∀ a : 𝒜, 0 ≤ a → (a = 0 ↔ ∀ (i) (b : 𝒜), ω i (star b * a * b) = 0)

/-- **21II** (`separating`, cstar.tex:3113, Definition), noted implication:
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

/-- **21II** (`separating`, cstar.tex:3113, Definition), noted implication:
separating collections are faithful. -/
theorem Separating.faithful (ω : ∀ i, 𝒜 →ₗ[ℂ] ℬf i) (h : Separating ω) :
    Faithful ω :=
  fun a _ => h a

/-- **21II** (`separating`, cstar.tex:3113, Definition), noted implication:
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

/-! **21III**–**21IV** (cstar.tex:3198, Examples): the states, the
multiplicative states (on a commutative C*-algebra), and the vector
functionals (on B(H)) are order separating — stated at 22VIII, 27–, and 25III
respectively; the four levels of separation differ — not converted. -/

/-- **21V** (`separating-self-adjoint`, cstar.tex:3232, Exercise): given a
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

/-- **21VII** (`order-separating-norm`, cstar.tex:3247, Proposition): for a
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
  -- and the norm is the supremum.  The ℓ^∞-product of an arbitrary family is
  -- not available *here*: Mathlib's `lp 𝒜 ∞` carries no `CStarAlgebra` or
  -- order instance on its own, and the ones the tree builds (together with
  -- `vonNeumannAlgebra_lp_infty`) live in `A/VN/Basic`, which imports this
  -- file.  So we run **20VI**'s *argument* on the family directly; the
  -- three steps are the same.  Note no index is needed: for
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

/-! **21IX** (`warning-norm-states`, cstar.tex:3271, Warning): the formula
`‖a‖ = sup_ω ‖ω(a)‖` may fail for non-self-adjoint `a` — not converted. -/

/-- **21X** (`order-separating-dense-subset`, cstar.tex:3290, Exercise): an
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

/-- **22II** (cstar.tex:3315, Definition): an *order ideal* of a C*-algebra
`𝒜` is a linear subspace `I` closed under the involution such that
`[-b, b] ⊆ I` for every positive `b ∈ I`. -/
structure IsOrderIdeal (I : Submodule ℂ 𝒜) : Prop where
  star_mem : ∀ b ∈ I, star b ∈ I
  mem_of_mem_interval : ∀ b ∈ I, 0 ≤ b → ∀ a : 𝒜, -b ≤ a → a ≤ b → a ∈ I

/-- **22II** (cstar.tex:3315, Definition): an order ideal is *proper* when it
does not contain `1`. -/
def IsProperOrderIdeal (I : Submodule ℂ 𝒜) : Prop :=
  IsOrderIdeal I ∧ (1 : 𝒜) ∉ I

/-- **22II** (cstar.tex:3315, Definition): a *maximal* order ideal is a
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


/-- **22III** (`order-ideal-basic`, cstar.tex:3339, Exercise), part 1: the
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

/-- **22III** (`order-ideal-basic`, cstar.tex:3339, Exercise), part 2: every
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


/-- **22III** (`order-ideal-basic`, cstar.tex:3339, Exercise), part 3a: for
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

/-- **22III** (`order-ideal-basic`, cstar.tex:3339, Exercise), part 3b: when
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

/-- **22III** (`order-ideal-basic`, cstar.tex:3339, Exercise), part 3c:
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

/-- **22III** (`order-ideal-basic`, cstar.tex:3339, Exercise), part 4: every
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
(**16V**), compactness, `‖a‖ = sup |spec(a)|` (**16II**) and the reality of
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

/-- **22III** (`order-ideal-basic`, cstar.tex:3339, Exercise), part 5: for
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
from the thesis's proof of **22IV** (cstar.tex:3388). -/
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

/-- **22IV** (`maximal-ideal-state`, cstar.tex:3383, Lemma): for every
maximal order ideal `I` of a C*-algebra `𝒜` there is a state `ω : 𝒜 → ℂ`
with `ker(ω) = I`. -/
theorem maximal_ideal_state (I : Submodule ℂ 𝒜) (hI : IsMaximalOrderIdeal I) :
    ∃ ω : 𝒜 →ₗ[ℂ] ℂ, IsState ω ∧ LinearMap.ker ω = I := by
  obtain ⟨⟨hord, h1I⟩, hmax⟩ := hI
  -- Step A (`pos-hahn-banach-1`, cstar.tex:3426): for self-adjoint `a`
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

/-- **22VIII** (`states-order-separating`, cstar.tex:3480, Exercise), part 1:
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

/-- **22VIII** (`states-order-separating`, cstar.tex:3480, Exercise), part 2:
the states of a C*-algebra are order separating.

This is the exercise's own "conclude": by **21VII** `order_separating_norm`
— the states are pu-maps — order separation is equivalent to clause (3),
`‖a‖ = sup_ω ‖ω(a)‖` for positive `a`, and that is part 1 together with
`‖ω(a)‖ ≤ ‖ω(1)‖‖a‖ = ‖a‖` (**20II**.1).  The trivial algebra, excluded from
part 1 by erratum 220.80, is the case where both sides are `0`. -/
theorem states_order_separating_2 :
    OrderSeparating fun ω : {ω : 𝒜 →ₗ[ℂ] ℂ // IsState ω} =>
      (ω : 𝒜 →ₗ[ℂ] ℂ) := by
  have hbound : ∀ (ω : {ω : 𝒜 →ₗ[ℂ] ℂ // IsState ω}) (a : 𝒜), IsSelfAdjoint a →
      ‖(ω : 𝒜 →ₗ[ℂ] ℂ) a‖ ≤ ‖a‖ := by
    intro ω a ha
    have h := weak_russo_dye_1 (ω : 𝒜 →ₗ[ℂ] ℂ) ω.2.1 a ha
    rwa [ω.2.2, norm_one, one_mul] at h
  refine ((order_separating_norm
      (fun ω : {ω : 𝒜 →ₗ[ℂ] ℂ // IsState ω} => (ω : 𝒜 →ₗ[ℂ] ℂ))
      (fun ω a ha => ω.2.1 a ha) (fun ω => ω.2.2)).out 2 0).mp ?_
  intro a ha
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
  have hbdd : BddAbove (Set.range fun ω : {ω : 𝒜 →ₗ[ℂ] ℂ // IsState ω} =>
      ‖(ω : 𝒜 →ₗ[ℂ] ℂ) a‖) := ⟨‖a‖, by rintro x ⟨ω, rfl⟩; exact hbound ω a hsa⟩
  refine le_antisymm ?_ (Real.iSup_le (fun ω => hbound ω a hsa) (norm_nonneg a))
  rcases subsingleton_or_nontrivial 𝒜 with hsub | hnt
  · have hzero : a = 0 := Subsingleton.elim _ _
    simp [hzero]
  · obtain ⟨ω, hω, hnorm⟩ := states_order_separating_1 (𝒜 := 𝒜) a hsa
    exact hnorm ▸ le_ciSup hbdd (⟨ω, hω⟩ : {ω : 𝒜 →ₗ[ℂ] ℂ // IsState ω})


end OrderIdeals

/-! ## Parsec 230: the square root -/

section Sqrt

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-! ### Auxiliary development for 23II

Everything in this block follows the thesis's own proof of **23II**
(cstar.tex:3495–3634) and uses nothing beyond parsec 170: the continuous
functional calculus is deliberately *not* used, since **23II** is precisely
what the thesis builds in order to avoid it.

One small departure from the letter of the thesis, order-preserving: the
thesis bounds `‖bₙ - b_N‖` by `qₙ(1) - q_N(1)` using that the polynomials
`qₙ` have nonnegative coefficients; we instead bound the successive
differences `‖b_{n+1} - bₙ‖` by `r_{n+1} - rₙ` for the real iteration
`r₀ = 0`, `r_{n+1} = ½(1 + rₙ²)` by a direct induction.  This needs no
polynomial algebra, so the existence of the limit does not wait on the
monotonicity of `b₀ ≤ b₁ ≤ ⋯` (part 2 of **23II**), which is stated below at
`sqrt_lemma_monotone`.  Part 2 is nevertheless proved the thesis's way, from
the nonnegativity of the coefficients of `qₙ₊₁ - qₙ` and *not* from the
positivity of commuting products; see the `SqrtCone` block below. -/

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

/-- The existence half of **23II** (cstar.tex:3509–3570). -/
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

/-- **23II** in the form `square-commuting-monotone` (cstar.tex:3589): the
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

/-- The corollary of `square-commuting-monotone` (cstar.tex:3602). -/
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

/-- **23II**, the inequality of `ineq-square-root` (cstar.tex:3611). -/
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

/-- **23II** (cstar.tex:3501, Lemma), part 1: for `0 ≤ a ≤ 1` there is a
unique `b` with `0 ≤ b ≤ 1`, `ab = ba` and `(1-b)² = 1-a`. -/
theorem sqrt_lemma_existsUnique (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    ∃! b : 𝒜, 0 ≤ b ∧ b ≤ 1 ∧ a * b = b * a ∧ (1 - b) ^ 2 = 1 - a :=
  by
    obtain ⟨b, hlim, hb0, hb1, hbsq, hbc⟩ := sqrt_lemma_exists a h0 h1
    refine ⟨b, ⟨hb0, hb1, hbc a rfl, hbsq⟩, ?_⟩
    rintro b' ⟨hb'0, hb'1, hb'a, hb'sq⟩
    exact (sqrt_lemma_unique a h0 h1 b hlim hb0 hbsq b' hb'0 hb'1 hb'a hb'sq).symm

/-! ### The thesis's cone, for **23II**.2

The thesis proves `b₀ ≤ b₁ ≤ ⋯` (cstar.tex:3520-3546) without the positivity
of commuting products, and says why in as many words at cstar.tex:3543: "we
have carefully avoided using the fact here that the product of positive
commuting elements is positive, which is not available to us until
`ineq-square-root`".  Its argument runs on the polynomials `q₀ = 0`,
`qₙ₊₁ = ½(x + qₙ²)` with `bₙ ≡ qₙ(a)`: every `qₙ`, and every difference
`qₙ₊₁ − qₙ`, has nonnegative coefficients and zero constant term, and
`a, a², a³, …` are positive by **17VI**.4d, so `bₙ` and `bₙ₊₁ − bₙ` are
positive.

`SqrtCone a` is the set of values `p(a)` of exactly those polynomials: the
nonnegative-real span of `a, a², a³, ….`  It is closed under products for the
thesis's reason and no other — `aᵐ⁺¹ · aⁿ⁺¹ = aᵐ⁺ⁿ⁺²`, an identity of
exponents — so nothing below appeals to the positivity of commuting products,
and the induction step is the thesis's own
`qₙ₊₂ − qₙ₊₁ = ½(qₙ₊₁ + qₙ)(qₙ₊₁ − qₙ)` (cstar.tex:3532). -/

/-- The nonnegative-real span of `a, a², a³, …`: the values at `a` of the real
polynomials with nonnegative coefficients and zero constant term, which is
what the thesis's "the coefficients of `qₙ` are positive" (cstar.tex:3520)
says about `qₙ(a)`. -/
private inductive SqrtCone (a : 𝒜) : 𝒜 → Prop
  | smul_pow (r : ℝ) (hr : 0 ≤ r) (n : ℕ) : SqrtCone a ((r : ℂ) • a ^ (n + 1))
  | add {x y : 𝒜} : SqrtCone a x → SqrtCone a y → SqrtCone a (x + y)

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
private theorem SqrtCone.zero (a : 𝒜) : SqrtCone a 0 := by
  simpa using SqrtCone.smul_pow (a := a) 0 le_rfl 0

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
private theorem SqrtCone.self (a : 𝒜) : SqrtCone a a := by
  simpa using SqrtCone.smul_pow (a := a) 1 zero_le_one 0

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
private theorem SqrtCone.smul {a x : 𝒜} (h : SqrtCone a x) {r : ℝ} (hr : 0 ≤ r) :
    SqrtCone a ((r : ℂ) • x) := by
  induction h with
  | smul_pow s hs n =>
    rw [smul_smul, ← Complex.ofReal_mul]
    exact SqrtCone.smul_pow _ (mul_nonneg hr hs) n
  | add _ _ ih₁ ih₂ =>
    rw [smul_add]
    exact ih₁.add ih₂

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
private theorem SqrtCone.half {a x : 𝒜} (h : SqrtCone a x) :
    SqrtCone a ((2 : ℂ)⁻¹ • x) := by
  have he : (2 : ℂ)⁻¹ = (((1 / 2 : ℝ)) : ℂ) := by norm_num
  rw [he]
  exact h.smul (by norm_num)

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- The cone is closed under products, by `aᵐ⁺¹ · aⁿ⁺¹ = aᵐ⁺ⁿ⁺²` alone. -/
private theorem SqrtCone.mul {a x y : 𝒜} (hx : SqrtCone a x) (hy : SqrtCone a y) :
    SqrtCone a (x * y) := by
  induction hx with
  | smul_pow r hr m =>
    induction hy with
    | smul_pow s hs n =>
      have hexp : m + 1 + (n + 1) = m + n + 1 + 1 := by omega
      have he : ((r : ℂ) • a ^ (m + 1)) * ((s : ℂ) • a ^ (n + 1))
          = ((r * s : ℝ) : ℂ) • a ^ (m + n + 1 + 1) := by
        rw [smul_mul_smul_comm, ← pow_add, hexp, Complex.ofReal_mul]
      rw [he]
      exact SqrtCone.smul_pow _ (mul_nonneg hr hs) _
    | add _ _ ih₁ ih₂ =>
      rw [mul_add]
      exact ih₁.add ih₂
  | add _ _ ih₁ ih₂ =>
    rw [add_mul]
    exact ih₁.add ih₂

/-- Every element of the cone is positive: **17VI**.4d for `aⁿ⁺¹`, **9X**.1
for the nonnegative scalars, and `add_nonneg` for the sums. -/
private theorem SqrtCone.nonneg {a x : 𝒜} (h0 : 0 ≤ a) (h : SqrtCone a x) : 0 ≤ x := by
  induction h with
  | smul_pow r hr n => exact ofReal_smul_nonneg (positive_basic_2_4d a h0 (n + 1)) hr
  | add _ _ ih₁ ih₂ => exact add_nonneg ih₁ ih₂

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- `bₙ ≡ qₙ(a)` lies in the cone: `q₀ = 0` and `qₙ₊₁ = ½(x + qₙ²)`. -/
private theorem sqrtApproxSeq_mem_cone (a : 𝒜) (n : ℕ) :
    SqrtCone a (sqrtApproxSeq a n) := by
  induction n with
  | zero =>
    rw [sqrtApproxSeq_zero]
    exact SqrtCone.zero a
  | succ n ih =>
    rw [sqrtApproxSeq_succ]
    refine SqrtCone.half ((SqrtCone.self a).add ?_)
    rw [pow_two]
    exact ih.mul ih

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- The thesis's third display line at cstar.tex:3532, as an identity in two
commuting elements: `½(a + x²) − ½(a + y²) = ½(x + y)(x − y)`. -/
private theorem half_sq_diff {x y : 𝒜} (hxy : x * y = y * x) (a : 𝒜) :
    (2 : ℂ)⁻¹ • (a + x ^ 2) - (2 : ℂ)⁻¹ • (a + y ^ 2)
      = (2 : ℂ)⁻¹ • ((x + y) * (x - y)) := by
  rw [← smul_sub]
  congr 1
  rw [mul_sub, add_mul, add_mul, hxy]
  noncomm_ring

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- `qₙ₊₁ − qₙ` has nonnegative coefficients, by the thesis's induction: the
base case is `q₁ − q₀ = ½x`, and the step is
`qₙ₊₂ − qₙ₊₁ = ½(qₙ₊₁ + qₙ)(qₙ₊₁ − qₙ)`, a product of two elements of the
cone. -/
private theorem sqrtApproxSeq_diff_mem_cone (a : 𝒜) (n : ℕ) :
    SqrtCone a (sqrtApproxSeq a (n + 1) - sqrtApproxSeq a n) := by
  induction n with
  | zero =>
    have he : sqrtApproxSeq a (0 + 1) - sqrtApproxSeq a 0 = (2 : ℂ)⁻¹ • a := by
      rw [sqrtApproxSeq_succ, sqrtApproxSeq_zero]
      simp
    rw [he]
    exact (SqrtCone.self a).half
  | succ n ih =>
    have key := half_sq_diff (sqrtApproxSeq_self_commute a (n + 1) n) a
    rw [← sqrtApproxSeq_succ a (n + 1), ← sqrtApproxSeq_succ a n] at key
    rw [key]
    exact SqrtCone.half (SqrtCone.mul
      ((sqrtApproxSeq_mem_cone a (n + 1)).add (sqrtApproxSeq_mem_cone a n)) ih)

/-- **23II** (cstar.tex:3501, Lemma), part 2: the sequence
`b₀ ≤ b₁ ≤ ⋯` given by `b₀ = 0`, `b_{n+1} = ½(a + bₙ²)` is monotone.

Proved the thesis's way (cstar.tex:3520-3546), through the cone above: the
positivity of commuting products is *not* used, which is the point the thesis
makes at cstar.tex:3543, so this lemma is independent of `sqrt_lemma_exists`
and of everything downstream of it. -/
theorem sqrt_lemma_monotone (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    Monotone (sqrtApproxSeq a) :=
  by
    refine monotone_nat_of_le_succ fun n => ?_
    exact sub_nonneg.mp ((sqrtApproxSeq_diff_mem_cone a n).nonneg h0)

/-- **23II** (cstar.tex:3501, Lemma), part 3: the `b` of
`sqrt_lemma_existsUnique` is the norm limit of the sequence `(bₙ)ₙ`. -/
theorem sqrt_lemma_tendsto (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 1) (b : 𝒜)
    (hb : 0 ≤ b ∧ b ≤ 1 ∧ a * b = b * a ∧ (1 - b) ^ 2 = 1 - a) :
    Tendsto (sqrtApproxSeq a) atTop (𝓝 b) :=
  by
    obtain ⟨b₀, hlim, hb₀0, _, hb₀sq, _⟩ := sqrt_lemma_exists a h0 h1
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    rwa [sqrt_lemma_unique a h0 h1 b₀ hlim hb₀0 hb₀sq b hb1 hb2 hb3 hb4] at hlim

/-- **23II** (cstar.tex:3501, Lemma), part 4: any `c` commuting with `a`
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

/-- **23VII** (`sqrt`, cstar.tex:3653, Exercise), part 0 (existence and
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

/-- **23VII** (`sqrt`, cstar.tex:3653, Exercise), part 0': Mathlib's
`CFC.sqrt a` is such a square root. -/
theorem sqrt_spec (a : 𝒜) (ha : 0 ≤ a) :
    0 ≤ CFC.sqrt a ∧ CFC.sqrt a ^ 2 = a ∧ a * CFC.sqrt a = CFC.sqrt a * a :=
  by
    have h2 := CFC.sq_sqrt a ha
    refine ⟨CFC.sqrt_nonneg a, h2, ?_⟩
    calc a * CFC.sqrt a = CFC.sqrt a ^ 2 * CFC.sqrt a := by rw [h2]
      _ = CFC.sqrt a * CFC.sqrt a ^ 2 := pow_mul_comm' _ 2
      _ = CFC.sqrt a * a := by rw [h2]

/-- **23VII** (`sqrt`, cstar.tex:3653, Exercise), part 0'': if `c` commutes
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

/-- **23VII** (`sqrt`, cstar.tex:3653, Exercise), part 1: the product of
commuting positive elements is positive. -/
theorem sqrt_1 (a b : 𝒜) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = b * a) :
    0 ≤ a * b :=
  mul_nonneg_of_commute ha hb hab

/-- **23VII** (`sqrt`, cstar.tex:3653, Exercise), part 2: for `a ≥ 0` and
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

/-- **23VII** (`sqrt`, cstar.tex:3653, Exercise), part 3: for commuting
self-adjoint `a, b` with `0 ≤ a ≤ b`: `a² ≤ b²`.

The hypothesis `0 ≤ a` is **erratum 230.70**: without it the statement is
false already in `𝒜 = ℂ`, where
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

/-- **23VII** (`sqrt`, cstar.tex:3653, Exercise), part 4: commutativity is
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

**24I** (cstar.tex:3699, Definition): for self-adjoint `a`:
`|a| := √(a²)`, the *positive part* `a₊ := ½(|a| + a)` and the *negative
part* `a₋ := ½(|a| - a)`.  In Mathlib: `CFC.abs a` (`= CFC.sqrt (star a * a)`,
which equals `CFC.sqrt (a ^ 2)` for self-adjoint `a`), `a⁺` (`CFC.posPart`)
and `a⁻` (`CFC.negPart`). -/

/-- **24II** (`cstar-pos-neg-part`, cstar.tex:3715, Exercise), part 1:
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

/-- **24II** (`cstar-pos-neg-part`, cstar.tex:3715, Exercise), part 2:
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

/-- **24II** (`cstar-pos-neg-part`, cstar.tex:3715, Exercise), part 3: the
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

/-- **24II** (`cstar-pos-neg-part`, cstar.tex:3715, Exercise), part 4 (from
addendum `parsec-240.20`): `‖a‖ = ‖a₊‖ ∨ ‖a₋‖` for self-adjoint `a`.

*Class 1 — faithful* (asols.tex `parsec-240.20`(4)).  For `≤`, the chain
`-(‖a₊‖ ∨ ‖a₋‖) ≤ -‖a₋‖ ≤ -a₋ ≤ a ≤ a₊ ≤ ‖a₊‖ ≤ ‖a₊‖ ∨ ‖a₋‖` and **17VI**.3a.
For `≥`, `a₊² + a₋² = (a₊ - a₋)² = a²` because `a₊a₋ = 0`, so `a₊² ≤ a²`,
whence `‖a₊‖² = ‖a₊²‖ ≤ ‖a²‖ = ‖a‖²` by **17VI**.3c and **7III**.13; likewise
for `a₋`. -/
theorem cstar_pos_neg_part_4 (a : 𝒜) (ha : IsSelfAdjoint a) :
    ‖a‖ = max ‖a⁺‖ ‖a⁻‖ :=
  by
    have hp0 : (0 : 𝒜) ≤ a⁺ := CFC.posPart_nonneg a
    have hm0 : (0 : 𝒜) ≤ a⁻ := CFC.negPart_nonneg a
    have hpsa : IsSelfAdjoint a⁺ := IsSelfAdjoint.of_nonneg hp0
    have hmsa : IsSelfAdjoint a⁻ := IsSelfAdjoint.of_nonneg hm0
    have hpm : a⁺ - a⁻ = a := CFC.posPart_sub_negPart a ha
    set M : ℝ := max ‖a⁺‖ ‖a⁻‖ with hM
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (le_max_left _ _)
    -- `≤`: the thesis's chain `-M ≤ -‖a₋‖ ≤ -a₋ ≤ a ≤ a₊ ≤ ‖a₊‖ ≤ M`
    have hle : ‖a‖ ≤ M := by
      refine (positive_basic_2_3a a ha M hM0).mp ⟨?_, ?_⟩
      · -- `-M ≤ a`
        have h1 : -(algebraMap ℂ 𝒜 ((M : ℝ) : ℂ)) ≤ -(algebraMap ℂ 𝒜 ((‖a⁻‖ : ℝ) : ℂ)) :=
          neg_le_neg (algebraMap_ofReal_mono (le_max_right _ _))
        have h2 : -(algebraMap ℂ 𝒜 ((‖a⁻‖ : ℝ) : ℂ)) ≤ -a⁻ :=
          neg_le_neg ((positive_basic_2_3a a⁻ hmsa ‖a⁻‖ (norm_nonneg _)).mpr le_rfl).2
        have h3 : -a⁻ ≤ a := by
          have h := sub_le_sub_right hp0 a⁻
          rwa [zero_sub, hpm] at h
        exact (h1.trans h2).trans h3
      · -- `a ≤ M`
        have h1 : a ≤ a⁺ := by
          have h := sub_le_sub_left hm0 a⁺
          rwa [sub_zero, hpm] at h
        have h2 : a⁺ ≤ algebraMap ℂ 𝒜 ((‖a⁺‖ : ℝ) : ℂ) :=
          ((positive_basic_2_3a a⁺ hpsa ‖a⁺‖ (norm_nonneg _)).mpr le_rfl).2
        exact (h1.trans h2).trans (algebraMap_ofReal_mono (le_max_left _ _))
    -- `≥`: `a₊² + a₋² = a²`, so both parts are dominated by `a²` in norm
    have hsq : a⁺ ^ 2 + a⁻ ^ 2 = a ^ 2 := by
      have hexp : (a⁺ - a⁻) ^ 2 = a⁺ ^ 2 - a⁺ * a⁻ - a⁻ * a⁺ + a⁻ ^ 2 := by
        noncomm_ring
      conv_rhs => rw [← hpm]
      rw [hexp, CFC.posPart_mul_negPart a, CFC.negPart_mul_posPart a]
      simp
    have key : ∀ b : 𝒜, IsSelfAdjoint b → 0 ≤ b → b ^ 2 ≤ a ^ 2 → ‖b‖ ≤ ‖a‖ := by
      intro b hb hb0 hble
      have h1 : ‖b ^ 2‖ ≤ ‖a ^ 2‖ :=
        positive_basic_2_3c _ _ (positive_basic_2_4a b hb) hble
      rw [cstar_involution_basic_13 b hb, cstar_involution_basic_13 a ha] at h1
      nlinarith [norm_nonneg b, norm_nonneg a]
    have hge : M ≤ ‖a‖ := by
      refine max_le (key _ hpsa hp0 ?_) (key _ hmsa hm0 ?_)
      · rw [← hsq]
        simpa using add_le_add_left (positive_basic_2_4a a⁻ hmsa) (a⁺ ^ 2)
      · rw [← hsq, add_comm]
        simpa using add_le_add_left (positive_basic_2_4a a⁺ hpsa) (a⁻ ^ 2)
    exact le_antisymm hle hge

/-- **24IV** (`astara-positive`, cstar.tex:3747, Lemma): `a* a ≥ 0` for every
element `a` of a C*-algebra.  (Mathlib: `star_mul_self_nonneg`.) -/
theorem astara_positive (a : 𝒜) : 0 ≤ star a * a :=
  (thesisPos_star_mul_self a).nonneg

/-! ## Parsec 250: positivity rounded up; vector states -/

/-- **25I** (`cstar-positive-final`, cstar.tex:3768, Exercise): for a
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
    -- the exercise's own 4 ⟹ 1: "that `c*c` is positive for all `c` was
    -- already shown in `parsec-240.40`" (asols.tex:2398), i.e. **24IV**.
    tfae_have 4 → 1 := by
      rintro ⟨c, rfl⟩
      exact astara_positive c
    tfae_have 1 ↔ 5 := nonneg_iff_spectrum_ofReal_nonneg a ha
    tfae_finish

/-- **25II** (`astara-pos-basic-consequences`, cstar.tex:3790, Exercise),
part 1: `b ≤ c` implies `a* b a ≤ a* c a`. -/
theorem astara_pos_basic_1 (a b c : 𝒜) (h : b ≤ c) :
    star a * b * a ≤ star a * c * a :=
  star_left_conjugate_le_conjugate h a

/-- **25II** (`astara-pos-basic-consequences`, cstar.tex:3790, Exercise),
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

/-- **25II** (`astara-pos-basic-consequences`, cstar.tex:3790, Exercise),
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

/-- **25II** (`astara-pos-basic-consequences`, cstar.tex:3790, Exercise),
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
    -- (a) ⟺ (b) is the solution's own argument (asols.tex:2496-2506), which
    -- runs on part 1 of this exercise, `astara_pos_basic_1`, in both
    -- directions: "if `a ≤ b⁻¹` then `√b a √b ≤ √b b⁻¹ √b = 1`, by part 1 of
    -- this exercise, where we used that `√(b⁻¹)` is the inverse of `√b`.  On
    -- the other hand, if `√b a √b ≤ 1`, then
    -- `a ≡ (√b)⁻¹ √b a √b (√b)⁻¹ ≤ b⁻¹`, again using part 1."  The solution's
    -- preceding observation -- that `√b` is invertible with
    -- `(√b)⁻¹ = √(b⁻¹)` -- enters only through `(√b)⁻¹ (√b)⁻¹ = b⁻¹`.
    have key12 : ∀ x y : 𝒜, 0 ≤ x → 0 ≤ y → IsUnit y →
        (x ≤ Ring.inverse y ↔ CFC.sqrt y * x * CFC.sqrt y ≤ 1) := by
      intro x y _hx hy huy
      set s := CFC.sqrt y with hs
      have hssa : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg y)
      have hsq : s * s = y := CFC.sqrt_mul_sqrt_self y hy
      have hus : IsUnit s := (CFC.isUnit_sqrt_iff y hy).mpr huy
      set t := Ring.inverse s with ht
      have hts : t * s = 1 := Ring.inverse_mul_cancel s hus
      have hst : s * t = 1 := Ring.mul_inverse_cancel s hus
      have htsa : IsSelfAdjoint t := by
        rw [IsSelfAdjoint, ht, ← Ring.inverse_star, hssa.star_eq]
      have htt : t * t = Ring.inverse y := by
        rw [← hsq, Ring.mul_inverse_rev' (Commute.refl s)]
      constructor
      · intro hle
        have h := astara_pos_basic_1 s x (Ring.inverse y) hle
        rw [hssa.star_eq] at h
        have hone : s * Ring.inverse y * s = 1 := by
          rw [← htt, ← mul_assoc, mul_assoc s t t, ← mul_assoc, hst, one_mul, hts]
        rwa [hone] at h
      · intro hle
        have h := astara_pos_basic_1 t (s * x * s) 1 hle
        rw [htsa.star_eq] at h
        have h1 : t * (s * x * s) * t = x := by
          rw [← mul_assoc, ← mul_assoc, hts, one_mul, mul_assoc, hst, mul_one]
        have h2 : t * 1 * t = Ring.inverse y := by rw [mul_one, htt]
        rwa [h1, h2] at h
    -- (b) ⟺ (c) "follows from `parsec-170.60`(3)" (asols.tex:2508-2513), i.e.
    -- from **17VI**.3a `positive_basic_2_3a` at `λ = 1`: the solution's
    -- displayed `(-1 ≤) √b a √b ≤ 1 iff ‖√a √b‖² ≡ ‖√b a √b‖ ≤ 1 iff
    -- ‖√a √b‖ ≤ 1`, with the parenthetical `-1 ≤` free because `√b a √b ≥ 0`.
    have key23 : ∀ x y : 𝒜, 0 ≤ x → 0 ≤ y →
        (CFC.sqrt y * x * CFC.sqrt y ≤ 1 ↔ ‖CFC.sqrt x * CFC.sqrt y‖ ≤ 1) := by
      intro x y hx _hy
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
      have hsa : IsSelfAdjoint (CFC.sqrt y * x * CFC.sqrt y) :=
        IsSelfAdjoint.of_nonneg hnn
      have hone : algebraMap ℂ 𝒜 ((1 : ℝ) : ℂ) = 1 := by norm_num
      have h3a := positive_basic_2_3a (CFC.sqrt y * x * CFC.sqrt y) hsa 1 zero_le_one
      rw [hone] at h3a
      have hneg : -(1 : 𝒜) ≤ CFC.sqrt y * x * CFC.sqrt y :=
        le_trans (neg_nonpos.mpr (zero_le_one (α := 𝒜))) hnn
      have hnsq : ‖CFC.sqrt y * x * CFC.sqrt y‖ = ‖CFC.sqrt x * CFC.sqrt y‖ ^ 2 := by
        rw [← heq, CStarRing.norm_star_mul_self, sq]
      constructor
      · intro hle
        have hn := h3a.mp ⟨hneg, hle⟩
        rw [hnsq] at hn
        nlinarith [norm_nonneg (CFC.sqrt x * CFC.sqrt y)]
      · intro hle
        refine (h3a.mpr ?_).2
        rw [hnsq]
        nlinarith [norm_nonneg (CFC.sqrt x * CFC.sqrt y)]
    tfae_have 1 ↔ 2 := key12 a b ha hb hub
    tfae_have 2 ↔ 3 := key23 a b ha hb
    tfae_have 4 ↔ 3 := by rw [key12 b a hb ha hua, key23 b a hb ha, hstar]
    tfae_finish

/-- **25II** (`astara-pos-basic-consequences`, cstar.tex:3790, Exercise),
part 3, closing clause: `a ≤ b` entails `b⁻¹ ≤ a⁻¹` for positive invertible
`a` and `b`.

*Class 1 — faithful*: it is the instance `(a) ⟺ (d)` of part 3 read at
`b⁻¹` in place of `b` — `a ≤ b = (b⁻¹)⁻¹` iff `b⁻¹ ≤ a⁻¹` — the inverse
being positive and invertible by **17VI**.5. -/
theorem astara_pos_basic_3_inv_antitone (a b : 𝒜) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hua : IsUnit a) (hub : IsUnit b) (hab : a ≤ b) :
    Ring.inverse b ≤ Ring.inverse a :=
  by
    have hbi0 : (0 : 𝒜) ≤ Ring.inverse b := (positive_basic_2_5 b hub).mp hb
    have hbiu : IsUnit (Ring.inverse b) := hub.ringInverse
    have hbb : Ring.inverse (Ring.inverse b) = b := by
      obtain ⟨u, rfl⟩ := hub
      rw [Ring.inverse_unit, Ring.inverse_unit, inv_inv]
    -- part 3 at the pair `(a, b⁻¹)`: clause 1 is `a ≤ (b⁻¹)⁻¹ = b`, clause 4
    -- is `b⁻¹ ≤ a⁻¹`
    have h := (astara_pos_basic_3 a (Ring.inverse b) ha hbi0 hua hbiu).out 0 3
    rw [hbb] at h
    exact h.mp hab

/-- **25II** (`astara-pos-basic-consequences`, cstar.tex:3790, Exercise),
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
    -- the exercise's own dependency: this is part 3's closing clause, not
    -- Mathlib's `CStarAlgebra.ringInverse_le_ringInverse`
    exact astara_pos_basic_3_inv_antitone (1 + a) (1 + b) hspa.nonneg hspb.nonneg
      hspa.isUnit hspb.isUnit (add_le_add_right hab 1)

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

variable [CompleteSpace H]

/-- Auxiliary: the vector functionals are positive maps (**21IV**). -/
private theorem vectorFunctional_isPositiveMap (x : {x : H // ‖x‖ = 1}) :
    IsPositiveMap (vectorFunctional (x : H)) := by
  intro T hT
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hT
  simpa using hT.inner_nonneg_right (x : H)

omit [CompleteSpace H] in
/-- Auxiliary: the vector functional of a unit vector is unital, so together
with `vectorFunctional_isPositiveMap` the vector states are pu-maps. -/
private theorem vectorFunctional_unital (x : {x : H // ‖x‖ = 1}) :
    vectorFunctional (x : H) 1 = 1 := by
  simp [inner_self_eq_norm_sq_to_K, x.2]

/-- Auxiliary: the vector functionals are involution preserving. -/
private theorem vectorFunctional_star (x : {x : H // ‖x‖ = 1}) (T : H →L[ℂ] H) :
    vectorFunctional (x : H) (star T) = star (vectorFunctional (x : H) T) := by
  show (⟪(x : H), (ContinuousLinearMap.adjoint T) (x : H)⟫ : ℂ)
      = star (⟪(x : H), T (x : H)⟫ : ℂ)
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm]
  rfl

omit [CompleteSpace H] in
/-- Auxiliary: `‖S‖ = sup { ‖S x‖ : ‖x‖ = 1 }`, the step "`‖T^{1/2}‖ =
sup_{x ∈ (H)₁} ‖T^{1/2} x‖`" of the thesis's proof of **25III**.  It is
**4IV** `operatorNorm_ball` at `r = 1`, which gives the supremum over the
closed unit *ball*, together with the rescaling of a non-zero vector of the
ball to the sphere.  (When `H` is trivial the sphere is empty and both sides
are `0`.) -/
private theorem norm_eq_iSup_unit_sphere (S : H →L[ℂ] H) :
    ‖S‖ = ⨆ x : {x : H // ‖x‖ = 1}, ‖S (x : H)‖ := by
  have hball := operatorNorm_ball S 1 zero_le_one
  rw [one_mul] at hball
  have hbdds : BddAbove (Set.range fun x : {x : H // ‖x‖ = 1} => ‖S (x : H)‖) :=
    ⟨‖S‖, by rintro _ ⟨x, rfl⟩; simpa [x.2] using S.le_opNorm (x : H)⟩
  set M : ℝ := ⨆ x : {x : H // ‖x‖ = 1}, ‖S (x : H)‖ with hM
  have hMnn : (0 : ℝ) ≤ M := Real.iSup_nonneg fun _ => norm_nonneg _
  refine le_antisymm ?_
    (Real.iSup_le (fun x => by simpa [x.2] using S.le_opNorm (x : H)) (norm_nonneg S))
  rw [hball]
  refine Real.iSup_le (fun y => ?_) hMnn
  rcases eq_or_ne (y : H) 0 with hy | hy
  · simp [hy, hMnn]
  · have hn : (0 : ℝ) < ‖(y : H)‖ := norm_pos_iff.mpr hy
    have hu : ‖(‖(y : H)‖⁻¹ : ℝ) • (y : H)‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        inv_mul_cancel₀ (ne_of_gt hn)]
    have hle := le_ciSup hbdds (⟨(‖(y : H)‖⁻¹ : ℝ) • (y : H), hu⟩ : {x : H // ‖x‖ = 1})
    have hcalc : ‖S ((‖(y : H)‖⁻¹ : ℝ) • (y : H))‖ = ‖(y : H)‖⁻¹ * ‖S (y : H)‖ := by
      rw [S.map_smul_of_tower, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hcalc] at hle
    have h2 := mul_le_mul_of_nonneg_left hle (le_of_lt hn)
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn), one_mul] at h2
    calc ‖S (y : H)‖ ≤ ‖(y : H)‖ * M := h2
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right y.2 hMnn
      _ = M := one_mul M

/-- **25III** (`hilb-vector-states-order-separating`, cstar.tex:3816,
Proposition): the vector states `⟪x, (·) x⟫`, `‖x‖ = 1`, of B(H) are order
separating, for every Hilbert space `H`.

This is the thesis's own proof (cstar.tex:3806): by **21VII**
`order_separating_norm` it suffices to prove clause (3), that
`‖T‖ = sup_{‖x‖=1} |⟪x, T x⟫|` for *positive* `T`; and writing `S := √T`
(**23VII**), `|⟪x, T x⟫| = ⟪S x, S x⟫ = ‖S x‖²` while `‖T‖ = ‖S* S‖ = ‖S‖²`,
so both sides are the square of `sup_{‖x‖=1} ‖S x‖`. -/
theorem hilb_vector_states_order_separating :
    OrderSeparating fun x : {x : H // ‖x‖ = 1} => vectorFunctional (x : H) := by
  refine ((order_separating_norm
      (fun x : {x : H // ‖x‖ = 1} => vectorFunctional (x : H))
      (fun x T hT => vectorFunctional_isPositiveMap x T hT)
      (fun x => vectorFunctional_unital x)).out 2 0).mp ?_
  intro T hT
  set S : H →L[ℂ] H := CFC.sqrt T with hS
  have hSsa : IsSelfAdjoint S := (CFC.sqrt_nonneg T).isSelfAdjoint
  have hSS : S * S = T := CFC.sqrt_mul_sqrt_self T hT
  -- `|⟪x, T x⟫| = ‖S x‖²`, because `S` is self-adjoint
  have hkey : ∀ y : H, ‖(vectorFunctional y) T‖ = ‖S y‖ ^ 2 := by
    intro y
    have h1 : (⟪y, T y⟫ : ℂ) = ⟪S y, S y⟫ := by
      have hTy : T y = S (S y) := by rw [← hSS]; rfl
      have hadj : ContinuousLinearMap.adjoint S = S := hSsa
      rw [hTy, ← ContinuousLinearMap.adjoint_inner_left S (S y) y, hadj]
    rw [vectorFunctional_apply, h1, inner_self_eq_norm_sq_to_K]
    simp [Complex.norm_real]
  -- `‖T‖ = ‖S‖²`, by the C*-identity
  have hnormT : ‖T‖ = ‖S‖ ^ 2 := by
    rw [← hSS]
    conv_lhs => rw [show S * S = star S * S from by rw [hSsa.star_eq]]
    rw [CStarRing.norm_star_mul_self, sq]
  rw [hnormT, norm_eq_iSup_unit_sphere S]
  simp only [hkey]
  rcases subsingleton_or_nontrivial H with hsub | hnt
  · have hempty : IsEmpty {x : H // ‖x‖ = 1} :=
      ⟨fun x => by simpa [Subsingleton.elim (x : H) 0] using x.2⟩
    simp
  · have : Nonempty {x : H // ‖x‖ = 1} := by
      obtain ⟨x, hx⟩ := exists_ne (0 : H)
      exact ⟨⟨(‖x‖⁻¹ : ℝ) • x, by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩⟩
    rw [← Real.iSup_pow (fun x : {x : H // ‖x‖ = 1} => norm_nonneg (S (x : H)))]

/-- Auxiliary: an operator is positive iff `⟪x, T x⟫ ≥ 0` for all unit vectors
`x` — **25III** with the subtype packaging removed, in the form **25V**.2
states it. -/
private theorem nonneg_clm_iff_inner_unit (T : H →L[ℂ] H) :
    0 ≤ T ↔ ∀ x : H, ‖x‖ = 1 → 0 ≤ ⟪x, T x⟫ :=
  by
    rw [hilb_vector_states_order_separating (H := H) T]
    exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h (x : H) x.2⟩

/-- **25V** (`hilb-positive-operators`, cstar.tex:3837, Corollary), part 1:
a bounded operator `T` on a Hilbert space is self-adjoint iff `⟪x, Tx⟫` is
real for every unit vector `x`.

The thesis's own derivation (cstar.tex:3838): the vector states are order
separating by **25III**, hence separating, and they are involution
preserving, so this is **21V** `separating_self_adjoint` — `T` is
self-adjoint iff every `⟪x, T x⟫` is, i.e. iff every `⟪x, T x⟫` is real. -/
theorem hilb_positive_operators_1 (T : H →L[ℂ] H) :
    IsSelfAdjoint T ↔ ∀ x : H, ‖x‖ = 1 → (⟪x, T x⟫ : ℂ).im = 0 :=
  by
    have hsep := (hilb_vector_states_order_separating (H := H)).separating _
    rw [separating_self_adjoint (fun x : {x : H // ‖x‖ = 1} => vectorFunctional (x : H))
      hsep vectorFunctional_star T]
    constructor
    · intro hall x hx
      have h := hall ⟨x, hx⟩
      rwa [isSelfAdjoint_iff, Complex.star_def, Complex.conj_eq_iff_im] at h
    · intro hall x
      rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_eq_iff_im]
      exact hall (x : H) x.2

/-- **25V** (`hilb-positive-operators`, cstar.tex:3837, Corollary), part 2:
`0 ≤ T` iff `0 ≤ ⟪x, Tx⟫` for every unit vector `x`.  This is **25III**
itself, as the thesis's proof says. -/
theorem hilb_positive_operators_2 (T : H →L[ℂ] H) :
    0 ≤ T ↔ ∀ x : H, ‖x‖ = 1 → 0 ≤ ⟪x, T x⟫ :=
  nonneg_clm_iff_inner_unit T

/-- **25V** (`hilb-positive-operators`, cstar.tex:3837, Corollary), part 3:
`‖T‖ = sup_{‖x‖=1} |⟪x, Tx⟫|` for self-adjoint `T`.

The thesis's own derivation: this is clause (2) of **21VII**
`order_separating_norm` for the vector states, which are order separating by
**25III**. -/
theorem hilb_positive_operators_3 (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ‖T‖ = ⨆ x : {x : H // ‖x‖ = 1}, ‖⟪(x : H), T x⟫‖ :=
  by
    have h := (order_separating_norm
        (fun x : {x : H // ‖x‖ = 1} => vectorFunctional (x : H))
        (fun x S hS => vectorFunctional_isPositiveMap x S hS)
        (fun x => vectorFunctional_unital x)).out 0 1
    exact h.mp (hilb_vector_states_order_separating (H := H)) T hT

end VectorStates

/-! ## Parsec 260: commutative C*-algebras are Riesz spaces -/

section Commutative

variable {𝒜 : Type*} [CommCStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3874, Exercise), part 1:
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

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3874, Exercise), part 2:
if `a` and `b` have a supremum `a ∨ b` then `c + a ∨ b` is the supremum of
`a + c` and `b + c`. -/
theorem commutative_cstar_basic_2 (a b c s : 𝒜) (h : IsLUB {a, b} s) :
    IsLUB {a + c, b + c} (c + s) :=
  by
    -- the solution's argument (asols.tex, `parsec-260.20`(2)): `c + (·)` is
    -- order preserving and in fact an order *isomorphism* of `sa(𝒜)`, with
    -- inverse `(-c) + (·)`; and order isomorphisms preserve suprema.
    have himg : (OrderIso.addLeft c) '' ({a, b} : Set 𝒜) = {a + c, b + c} := by
      simp [Set.image_insert_eq, Set.image_singleton, add_comm]
    have hkey := (OrderIso.isLUB_image (OrderIso.addLeft c)
      (s := ({a, b} : Set 𝒜)) (x := c + s)).mpr (by simpa using h)
    rwa [himg] at hkey

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3874, Exercise), part 3:
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

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3874, Exercise), part 4,
binary case: an miu-map between commutative C*-algebras preserves binary
suprema.  The Exercise asks for *finite* suprema and infima; those are
`commutative_cstar_basic_4_finite`, `commutative_cstar_basic_4_inf` and
`commutative_cstar_basic_4_finite_inf` below, each obtained from this one. -/
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

/-- Auxiliary: if `s` is the supremum of `S` and `u` the supremum of
`{x, s}`, then `u` is the supremum of `insert x S`. -/
private theorem isLUB_insert_of {A : Type*} [Preorder A] {S : Set A} {s u x : A}
    (h : IsLUB S s) (h2 : IsLUB ({x, s} : Set A) u) : IsLUB (insert x S) u :=
  by
    constructor
    · intro y hy
      rw [Set.mem_insert_iff] at hy
      rcases hy with rfl | hy
      · exact h2.1 (Set.mem_insert _ _)
      · exact le_trans (h.1 hy) (h2.1 (Set.mem_insert_of_mem _ rfl))
    · intro c hc
      refine h2.2 ?_
      rintro z (rfl | rfl)
      · exact hc (Set.mem_insert _ _)
      · exact h.2 fun y hy => hc (Set.mem_insert_of_mem _ hy)

/-- Auxiliary: negation carries an infimum to a supremum. -/
private theorem isLUB_neg_of_isGLB {A : Type*} [InvolutiveNeg A] [Preorder A]
    (hneg : ∀ x y : A, -x ≤ -y ↔ y ≤ x) {S : Set A} {s : A} (h : IsGLB S s) :
    IsLUB ((fun x => -x) '' S) (-s) :=
  by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (hneg x s).mpr (h.1 hx)
    · intro c hc
      have h1 : -c ∈ lowerBounds S := by
        intro x hx
        have h2 : -x ≤ c := hc ⟨x, hx, rfl⟩
        have h3 : -c ≤ -(-x) := (hneg c (-x)).mpr h2
        rwa [neg_neg] at h3
      have h4 : -s ≤ -(-c) := (hneg s (-c)).mpr (h.2 h1)
      rwa [neg_neg] at h4

/-- Auxiliary: and back. -/
private theorem isGLB_of_isLUB_neg {A : Type*} [InvolutiveNeg A] [Preorder A]
    (hneg : ∀ x y : A, -x ≤ -y ↔ y ≤ x) {S : Set A} {s : A}
    (h : IsLUB ((fun x => -x) '' S) (-s)) : IsGLB S s :=
  by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hneg x s).mp (h.1 ⟨x, hx, rfl⟩)
    · intro c hc
      have h1 : -c ∈ upperBounds ((fun x => -x) '' S) := by
        rintro _ ⟨x, hx, rfl⟩
        exact (hneg x c).mpr (hc hx)
      exact (hneg s c).mp (h.2 h1)

/-- Auxiliary (**26II**.3/.4): a nonempty finite set of self-adjoint elements
of a commutative C*-algebra has a supremum, and an miu-map carries it to the
supremum of the image.  Both halves are the binary case of parts 3 and 4,
iterated along the finite set. -/
private theorem finite_lub_aux {ℬ : Type*} [CommCStarAlgebra ℬ] [PartialOrder ℬ]
    [StarOrderedRing ℬ] (f : 𝒜 →⋆ₐ[ℂ] ℬ) {T : Finset 𝒜} (hT : T.Nonempty) :
    (∀ x ∈ T, IsSelfAdjoint x) →
      ∃ s : 𝒜, IsLUB (T : Set 𝒜) s ∧ IsLUB (f '' (T : Set 𝒜)) (f s) :=
  by
    induction hT using Finset.Nonempty.cons_induction with
    | singleton x =>
        intro _
        refine ⟨x, ?_, ?_⟩
        · simpa using isLUB_singleton
        · simp only [Finset.coe_singleton, Set.image_singleton]
          exact isLUB_singleton
    | cons x T hx hT ih =>
        intro hsa
        obtain ⟨s, hs, hfs⟩ := ih fun y hy => hsa y (Finset.mem_cons_of_mem hy)
        have hxsa : IsSelfAdjoint x := hsa x (Finset.mem_cons_self ..)
        obtain ⟨y, hy⟩ := hT
        have hysa : IsSelfAdjoint y := hsa y (Finset.mem_cons_of_mem hy)
        -- `s` is self-adjoint: `s = (s - y) + y` with `s - y ≥ 0`
        have hssa : IsSelfAdjoint s := by
          have h0 : (0 : 𝒜) ≤ s - y := sub_nonneg.mpr (hs.1 (Finset.mem_coe.mpr hy))
          have h1 := (IsSelfAdjoint.of_nonneg h0).add hysa
          simpa using h1
        have hlub2 := commutative_cstar_basic_3 x s hxsa hssa
        refine ⟨(2 : ℂ)⁻¹ • (x + s + CFC.abs (x - s)), ?_, ?_⟩
        · rw [Finset.coe_cons]
          exact isLUB_insert_of hs hlub2
        · rw [Finset.coe_cons, Set.image_insert_eq]
          exact isLUB_insert_of hfs (commutative_cstar_basic_4 f x s _ hlub2)

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3874, Exercise), part 3,
finite form: every nonempty finite set of self-adjoint elements of a
commutative C*-algebra has a supremum — `sa(𝒜)` being a lattice, part 3's
binary supremum iterated.  (This is the form **29V** needs of
`g₁ ∨ ⋯ ∨ g_N`.) -/
theorem commutative_cstar_basic_3_finite {S : Set 𝒜} (hfin : S.Finite)
    (hne : S.Nonempty) (hsa : ∀ x ∈ S, IsSelfAdjoint x) : ∃ s : 𝒜, IsLUB S s :=
  by
    classical
    have hT : hfin.toFinset.Nonempty := by
      rwa [Set.Finite.toFinset_nonempty]
    obtain ⟨s, h, -⟩ := finite_lub_aux (StarAlgHom.id ℂ 𝒜) hT
      (by simpa [hfin.coe_toFinset] using hsa)
    rw [hfin.coe_toFinset] at h
    exact ⟨s, h⟩

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3874, Exercise), part 4,
in the Exercise's own *finite* form: an miu-map between commutative
C*-algebras preserves the supremum of a nonempty finite set of self-adjoint
elements.

*Class 1 — faithful*: the solution's binary case (`commutative_cstar_basic_4`)
iterated along the finite set. -/
theorem commutative_cstar_basic_4_finite {ℬ : Type*} [CommCStarAlgebra ℬ]
    [PartialOrder ℬ] [StarOrderedRing ℬ] (f : 𝒜 →⋆ₐ[ℂ] ℬ) {S : Set 𝒜}
    (hfin : S.Finite) (hne : S.Nonempty) (hsa : ∀ x ∈ S, IsSelfAdjoint x)
    {s : 𝒜} (h : IsLUB S s) : IsLUB (f '' S) (f s) :=
  by
    classical
    have hT : hfin.toFinset.Nonempty := by
      rwa [Set.Finite.toFinset_nonempty]
    obtain ⟨s', h1, h2⟩ := finite_lub_aux f hT (by simpa [hfin.coe_toFinset] using hsa)
    rw [hfin.coe_toFinset] at h1 h2
    rw [h.unique h1]
    exact h2

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3874, Exercise), part 4,
infima (binary): an miu-map between commutative C*-algebras preserves binary
infima.

*Class 1 — faithful*: the solution's own last line, `a ∧ b = -((-a) ∨ (-b))`. -/
theorem commutative_cstar_basic_4_inf {ℬ : Type*} [CommCStarAlgebra ℬ]
    [PartialOrder ℬ] [StarOrderedRing ℬ] (f : 𝒜 →⋆ₐ[ℂ] ℬ) (a b s : 𝒜)
    (h : IsGLB {a, b} s) : IsGLB {f a, f b} (f s) :=
  by
    have hnA : ∀ x y : 𝒜, -x ≤ -y ↔ y ≤ x := fun _ _ => neg_le_neg_iff
    have hnB : ∀ x y : ℬ, -x ≤ -y ↔ y ≤ x := fun _ _ => neg_le_neg_iff
    have h1 := isLUB_neg_of_isGLB hnA h
    simp only [Set.image_insert_eq, Set.image_singleton] at h1
    have h2 := commutative_cstar_basic_4 f (-a) (-b) (-s) h1
    rw [map_neg, map_neg, map_neg] at h2
    refine isGLB_of_isLUB_neg hnB ?_
    simpa only [Set.image_insert_eq, Set.image_singleton] using h2

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3874, Exercise), part 4,
infima (finite): an miu-map between commutative C*-algebras preserves the
infimum of a nonempty finite set of self-adjoint elements. -/
theorem commutative_cstar_basic_4_finite_inf {ℬ : Type*} [CommCStarAlgebra ℬ]
    [PartialOrder ℬ] [StarOrderedRing ℬ] (f : 𝒜 →⋆ₐ[ℂ] ℬ) {S : Set 𝒜}
    (hfin : S.Finite) (hne : S.Nonempty) (hsa : ∀ x ∈ S, IsSelfAdjoint x)
    {s : 𝒜} (h : IsGLB S s) : IsGLB (f '' S) (f s) :=
  by
    have hnA : ∀ x y : 𝒜, -x ≤ -y ↔ y ≤ x := fun _ _ => neg_le_neg_iff
    have hnB : ∀ x y : ℬ, -x ≤ -y ↔ y ≤ x := fun _ _ => neg_le_neg_iff
    have h1 := isLUB_neg_of_isGLB hnA h
    have hfin' : ((fun x : 𝒜 => -x) '' S).Finite := hfin.image _
    have hne' : ((fun x : 𝒜 => -x) '' S).Nonempty := hne.image _
    have hsa' : ∀ x ∈ (fun x : 𝒜 => -x) '' S, IsSelfAdjoint x := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hsa x hx).neg
    have h2 := commutative_cstar_basic_4_finite f hfin' hne' hsa' h1
    rw [map_neg] at h2
    refine isGLB_of_isLUB_neg hnB ?_
    have himg : ⇑f '' ((fun x : 𝒜 => -x) '' S) = (fun y : ℬ => -y) '' (⇑f '' S) := by
      ext y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨f x, ⟨x, hx, rfl⟩, (map_neg f x).symm⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨-x, ⟨x, hx, rfl⟩, map_neg f x⟩
    rwa [himg] at h2

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3874, Exercise), part 3,
finite form, infima: every nonempty finite set of self-adjoint elements of a
commutative C*-algebra has an infimum. -/
theorem commutative_cstar_basic_3_finite_inf {S : Set 𝒜} (hfin : S.Finite)
    (hne : S.Nonempty) (hsa : ∀ x ∈ S, IsSelfAdjoint x) : ∃ s : 𝒜, IsGLB S s :=
  by
    have hnA : ∀ x y : 𝒜, -x ≤ -y ↔ y ≤ x := fun _ _ => neg_le_neg_iff
    obtain ⟨s, hs⟩ := commutative_cstar_basic_3_finite (hfin.image (fun x : 𝒜 => -x))
      (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact (hsa x hx).neg)
    refine ⟨-s, isGLB_of_isLUB_neg hnA ?_⟩
    rwa [neg_neg]

/-- **26II** (`commutative-cstar-basic`, cstar.tex:3874, Exercise), part 6:
the C*-subalgebra generated by two commuting self-adjoint elements of an
arbitrary C*-algebra is commutative — which is what makes the suprema and
infima of part 3 available for such a pair, computed in that subalgebra.
A C*-subalgebra is norm-closed (**3IV**), hence the `topologicalClosure`.

The proof follows the solution's skeleton: the least C*-subalgebra containing
`a` and `b` is the norm closure of the span of the `aⁿbᵐ`, which is
commutative, and "that which commutes with the elements of a sequence commutes
with its limit too" — here `StarAlgebra.adjoin` and
`StarSubalgebra.commRingTopologicalClosure` are those two steps. -/
theorem commutative_cstar_basic_6 {A : Type*} [CStarAlgebra A] {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : Commute a b) :
    IsMulCommutative ((StarAlgebra.adjoin ℂ ({a, b} : Set A)).topologicalClosure) :=
  by
    have hmem : ∀ x ∈ ({a, b} : Set A), x = a ∨ x = b := fun x hx => by simpa using hx
    have hcomm : ∀ x ∈ ({a, b} : Set A), ∀ y ∈ ({a, b} : Set A), x * y = y * x := by
      intro x hx y hy
      rcases hmem x hx with rfl | rfl <;> rcases hmem y hy with rfl | rfl
      · rfl
      · exact hab.eq
      · exact hab.symm.eq
      · rfl
    have h5 : IsMulCommutative (StarAlgebra.adjoin ℂ ({a, b} : Set A)) := by
      refine StarAlgebra.isMulCommutative_adjoin ℂ hcomm ?_
      intro x hx y hy
      have hy' : star y = y := by
        rcases hmem y hy with rfl | rfl
        · exact ha
        · exact hb
      rw [hy']
      exact hcomm x hx y hy
    let _ := StarSubalgebra.commRingTopologicalClosure
      (StarAlgebra.adjoin ℂ ({a, b} : Set A)) (fun x y => h5.is_comm.comm x y)
    exact ⟨⟨fun x y => mul_comm x y⟩⟩

/-- The meet `a ∧ b := ½(a + b - |a - b|)` of two commuting self-adjoint
elements of a C*-algebra.  **26II**.6 says they generate a commutative
C*-subalgebra, and **26II**.3 that this formula is their infimum in it —
which is the sense in which `p ∧ q` is read in **104III** and **104VII**
(proc.tex), *not* the infimum in the order of the ambient algebra, which by
Kadison's anti-lattice theorem usually does not exist. -/
noncomputable def meet {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (a b : A) : A :=
  (2 : ℂ)⁻¹ • (a + b - CFC.abs (a - b))

/-- In a *commutative* C*-algebra `meet` is the infimum outright: **26II**.3
read through `a ⊓ b = -((-a) ⊔ (-b))`. -/
theorem meet_isGLB (a b : 𝒜) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    IsGLB {a, b} (meet a b) :=
  by
    have habs : CFC.abs (-a - -b) = CFC.abs (a - b) := by
      rw [show -a - -b = -(a - b) by ring, CFC.abs_neg]
    have hlub := commutative_cstar_basic_3 (-a) (-b) ha.neg hb.neg
    rw [habs] at hlub
    have hneg : (2 : ℂ)⁻¹ • (-a + -b + CFC.abs (a - b)) = -meet a b := by
      rw [meet]; module
    rw [hneg] at hlub
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rcases hx with rfl | rfl
      · exact neg_le_neg_iff.mp (hlub.1 (Set.mem_insert _ _))
      · exact neg_le_neg_iff.mp (hlub.1 (Set.mem_insert_of_mem _ rfl))
    · refine neg_le_neg_iff.mp (hlub.2 ?_)
      rintro y (rfl | rfl)
      · exact neg_le_neg_iff.mpr (hx (Set.mem_insert _ _))
      · exact neg_le_neg_iff.mpr (hx (Set.mem_insert_of_mem _ rfl))

section MeetLemmas

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `|x| = √(x·x)` for self-adjoint `x`. -/
theorem abs_eq_sqrt_mul_self {x : A} (hx : IsSelfAdjoint x) :
    CFC.abs x = CFC.sqrt (x * x) := by
  show CFC.sqrt (star x * x) = _
  rw [hx.star_eq]

/-- `a ∧ b ≤ a`: the difference is `(a − b)⁺`.  No commutation needed. -/
theorem meet_le_left (a b : A) (hab : IsSelfAdjoint (a - b)) : meet a b ≤ a := by
  have h : a - meet a b = (a - b)⁺ := by
    have h2 := CFC.abs_add_self (a - b) hab
    have h3 : a - (2 : ℂ)⁻¹ • (a + b - CFC.abs (a - b))
        = (2 : ℂ)⁻¹ • (CFC.abs (a - b) + (a - b)) := by module
    rw [meet, h3, h2, two_nsmul, ← two_smul ℂ, smul_smul]
    norm_num
  rw [← sub_nonneg, h]
  exact CFC.posPart_nonneg _

theorem meet_le_right (a b : A) (hab : IsSelfAdjoint (a - b)) : meet a b ≤ b := by
  have h : b - meet a b = (b - a)⁺ := by
    have hba : IsSelfAdjoint (b - a) := by
      rw [← neg_sub a b]; exact hab.neg
    have h2 := CFC.abs_add_self (b - a) hba
    have habs : CFC.abs (a - b) = CFC.abs (b - a) := by
      rw [← neg_sub a b, CFC.abs_neg]
    have h3 : b - (2 : ℂ)⁻¹ • (a + b - CFC.abs (b - a))
        = (2 : ℂ)⁻¹ • (CFC.abs (b - a) + (b - a)) := by module
    rw [meet, habs, h3, h2, two_nsmul, ← two_smul ℂ, smul_smul]
    norm_num
  rw [← sub_nonneg, h]
  exact CFC.posPart_nonneg _

/-- For commuting positives, `|a − b| ≤ a + b`, since `(a−b)² ≤ (a+b)²` and
`√` is operator monotone. -/
theorem abs_sub_le_add {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a * b = b * a) : CFC.abs (a - b) ≤ a + b := by
  have hd : IsSelfAdjoint (a - b) :=
    (IsSelfAdjoint.of_nonneg ha).sub (IsSelfAdjoint.of_nonneg hb)
  have hsum : (0 : A) ≤ a + b := add_nonneg ha hb
  have h4 : (a + b) * (a + b) - (a - b) * (a - b) = a * b + a * b + a * b + a * b := by
    have hba : b * a = a * b := hab.symm
    calc (a + b) * (a + b) - (a - b) * (a - b)
        = a * b + a * b + b * a + b * a := by noncomm_ring
      _ = a * b + a * b + a * b + a * b := by rw [hba]
  have hkey : (a - b) * (a - b) ≤ (a + b) * (a + b) := by
    rw [← sub_nonneg, h4]
    have h := mul_nonneg_of_commute ha hb hab
    exact add_nonneg (add_nonneg (add_nonneg h h) h) h
  rw [abs_eq_sqrt_mul_self hd, ← CFC.sqrt_mul_self (a + b) hsum]
  exact CFC.sqrt_le_sqrt _ _ hkey

/-- For commuting positives the meet is positive. -/
theorem meet_nonneg {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = b * a) :
    0 ≤ meet a b := by
  have h := sub_nonneg.mpr (abs_sub_le_add ha hb hab)
  rw [meet]
  have h2 : (2 : ℂ)⁻¹ • (a + b - CFC.abs (a - b))
      = ((2⁻¹ : ℝ) : ℂ) • (a + b - CFC.abs (a - b)) := by norm_num
  rw [h2]
  exact ofReal_smul_nonneg h (by norm_num)

/-- Anything commuting with `a` and `b` commutes with `a ∧ b`. -/
theorem commute_meet {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hca : c * a = a * c) (hcb : c * b = b * c) : c * meet a b = meet a b * c := by
  have hd : IsSelfAdjoint (a - b) :=
    (IsSelfAdjoint.of_nonneg ha).sub (IsSelfAdjoint.of_nonneg hb)
  have hdd : (0 : A) ≤ (a - b) * (a - b) := by
    have h := star_mul_self_nonneg (a - b)
    rwa [hd.star_eq] at h
  have hca' : Commute c a := hca
  have hcb' : Commute c b := hcb
  have hcd : Commute c (a - b) := hca'.sub_right hcb'
  have habs : c * CFC.abs (a - b) = CFC.abs (a - b) * c := by
    rw [abs_eq_sqrt_mul_self hd]
    exact (sqrt_commute _ hdd c (hcd.mul_right hcd).eq).1
  rw [meet, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_add, add_mul,
    hca, hcb, habs]

/-- The exact identity behind the carrier of a meet: for commuting positives,
`(a ∧ b)(a + b) = ab + (a ∧ b)²`.  (Pointwise: `min·(x+y) = xy + min²`.) -/
theorem meet_mul_add {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = b * a) :
    meet a b * (a + b) = a * b + meet a b * meet a b := by
  set t := a + b with ht
  set u := CFC.abs (a - b) with hu
  have hd : IsSelfAdjoint (a - b) :=
    (IsSelfAdjoint.of_nonneg ha).sub (IsSelfAdjoint.of_nonneg hb)
  have hdd : (0 : A) ≤ (a - b) * (a - b) := by
    have h := star_mul_self_nonneg (a - b)
    rwa [hd.star_eq] at h
  have huu : u * u = (a - b) * (a - b) := by
    rw [hu, abs_eq_sqrt_mul_self hd]
    exact CFC.sqrt_mul_sqrt_self _ hdd
  have hcab : Commute a b := hab
  have hctd : Commute t (a - b) :=
    ((Commute.refl a).sub_right hcab).add_left (hcab.symm.sub_right (Commute.refl b))
  have hcomm_dd : t * ((a - b) * (a - b)) = ((a - b) * (a - b)) * t :=
    (hctd.mul_right hctd).eq
  have hut : u * t = t * u := by
    rw [hu, abs_eq_sqrt_mul_self hd]
    exact ((sqrt_commute _ hdd t hcomm_dd).1).symm
  have hM : meet a b = (2 : ℂ)⁻¹ • (t - u) := by rw [meet, ht, hu]
  have hkey : (t - u) * t + (t - u) * t - (t - u) * (t - u) = (4 : ℂ) • (a * b) := by
    have hba : b * a = a * b := hab.symm
    calc (t - u) * t + (t - u) * t - (t - u) * (t - u)
        = t * t - u * u + (t * u - u * t) := by noncomm_ring
      _ = t * t - u * u := by rw [hut]; abel
      _ = (4 : ℂ) • (a * b) := by
          rw [huu, ht]
          have hexp : (a + b) * (a + b) - (a - b) * (a - b)
              = a * b + a * b + a * b + a * b := by
            calc (a + b) * (a + b) - (a - b) * (a - b)
                = a * b + a * b + b * a + b * a := by noncomm_ring
              _ = a * b + a * b + a * b + a * b := by rw [hba]
          rw [hexp]
          module
  have hMM : (t - u) * (t - u) = (2 : ℂ) • ((t - u) * t) - (4 : ℂ) • (a * b) := by
    rw [← hkey]; module
  have hsq : ((2 : ℂ)⁻¹ • (t - u)) * ((2 : ℂ)⁻¹ • (t - u))
      = ((4 : ℂ)⁻¹) • ((t - u) * (t - u)) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]; norm_num
  rw [hM, hsq, hMM, smul_mul_assoc]
  module

/-- `(a ∧ b)·w = (aw) ∧ (bw)` for `w ≥ 0` commuting with `a` and `b`.
Pointwise this is `min(x,y)·u = min(xu, yu)` for `u ≥ 0`.  With `w` a
projection it says the meet localises to a corner. -/
theorem meet_mul_right {a b w : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w)
    (haw : a * w = w * a) (hbw : b * w = w * b) :
    meet a b * w = meet (a * w) (b * w) := by
  have hd : IsSelfAdjoint (a - b) :=
    (IsSelfAdjoint.of_nonneg ha).sub (IsSelfAdjoint.of_nonneg hb)
  have hdw : (a - b) * w = w * (a - b) := by rw [sub_mul, mul_sub, haw, hbw]
  have hdd : (0 : A) ≤ (a - b) * (a - b) := by
    have h := star_mul_self_nonneg (a - b)
    rwa [hd.star_eq] at h
  have hddw : w * ((a - b) * (a - b)) = (a - b) * (a - b) * w := by
    calc w * ((a - b) * (a - b)) = w * (a - b) * (a - b) := by rw [mul_assoc]
      _ = (a - b) * w * (a - b) := by rw [hdw]
      _ = (a - b) * (w * (a - b)) := by rw [mul_assoc]
      _ = (a - b) * ((a - b) * w) := by rw [hdw]
      _ = (a - b) * (a - b) * w := by rw [mul_assoc]
  have habsw : CFC.abs (a - b) * w = w * CFC.abs (a - b) := by
    rw [abs_eq_sqrt_mul_self hd]
    exact ((sqrt_commute _ hdd w hddw).1).symm
  have habs0 : (0 : A) ≤ CFC.abs (a - b) := CFC.abs_nonneg _
  -- `|(a−b)w| = |a−b|·w`, by uniqueness of positive square roots
  have hkey : CFC.abs ((a - b) * w) = CFC.abs (a - b) * w := by
    have hnn : (0 : A) ≤ CFC.abs (a - b) * w := sqrt_1 _ _ habs0 hw habsw
    have habs2 : CFC.abs (a - b) * CFC.abs (a - b) = (a - b) * (a - b) := by
      rw [abs_eq_sqrt_mul_self hd]
      exact CFC.sqrt_mul_sqrt_self _ hdd
    show CFC.sqrt (star ((a - b) * w) * ((a - b) * w)) = _
    refine CFC.sqrt_unique ?_ hnn
    have hwsa : star w = w := (IsSelfAdjoint.of_nonneg hw).star_eq
    calc CFC.abs (a - b) * w * (CFC.abs (a - b) * w)
        = CFC.abs (a - b) * (w * CFC.abs (a - b)) * w := by noncomm_ring
      _ = CFC.abs (a - b) * (CFC.abs (a - b) * w) * w := by rw [habsw]
      _ = (a - b) * (a - b) * (w * w) := by rw [← mul_assoc, habs2]; noncomm_ring
      _ = w * ((a - b) * (a - b)) * w := by rw [hddw]; noncomm_ring
      _ = star ((a - b) * w) * ((a - b) * w) := by
          rw [star_mul, hd.star_eq, hwsa]; noncomm_ring
  rw [meet, meet, show a * w - b * w = (a - b) * w by rw [sub_mul], hkey,
    smul_mul_assoc, sub_mul, add_mul]

end MeetLemmas

/-- **26III** (`riesz-decomposition-lemma`, cstar.tex:3907, Exercise), the
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
