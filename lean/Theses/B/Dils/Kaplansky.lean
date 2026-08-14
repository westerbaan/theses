/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 4082–4279.

  parsec 1580:  the Kaplansky density theorem for Hilbert C*-modules

**158Ia** is proved; **158II** and the four **158V** estimates are `sorry`
(the latter four are *false*, see below).  Following the conventions of
`HilbertModules.lean`, ultrastrong/ultranorm approximation is expressed
through the seminorms `unSeminorm ω B` (with `B = mulInner ℬ` for the
ultrastrong uniformity on `ℬ` itself); "there is a net `x_α → x` ultranorm
with `‖x_α‖ ≤ ‖x‖`" is rendered as bounded approximability within every
entourage (finitely many seminorms, `ε > 0`), which yields the canonical
approximating net.
-/
import Theses.A.VN.Completeness
import Theses.B.Dils.HilbertModules

open scoped ComplexOrder CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u v w

namespace Theses.B.Dils

/-! **158I** (dils.tex:4084) and **158Ib** (dils.tex:4129): introduction and
discussion — nothing to formalize. -/

section Kaplansky

variable {ℬ : Type u}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- The `mulInner` ultranorm seminorm is the *mirrored* ultrastrong seminorm:
`‖x‖_ω = ω(x x*)^½ = ‖x*‖_ω^{ultrastrong}` (**146VIII**). -/
private theorem unSeminorm_mulInner_eq (ω : NPFunctional ℬ) (x : ℬ) :
    unSeminorm ω (mulInner ℬ) x = omegaNorm ℬ ω (star x) := by
  rw [omegaNorm, unSeminorm, star_star]; rfl

/-- **158Ia** (dils.tex:4121, Kaplansky density theorem), the variant of
thesis A's `kaplansky` (vn.tex 74IV) used here: for an ultrastrongly dense
C*-subalgebra `𝒜` of a von Neumann algebra `ℬ` and every `b ∈ ℬ`, there is
a net in `𝒜`, norm-bounded by `‖b‖`, converging ultrastrongly to `b`.

*Class 1 — faithful*: this **is** 74IV, transported across the mirror.  The
ultranorm uniformity of `mulInner` is the *mirrored* ultrastrong uniformity
(`unSeminorm_mulInner_eq`), whereas `Theses.A.VN.kaplansky` speaks of the
ultrastrong one; since `star` is an isometric involution of `𝒜` that swaps
the two, applying 74IV at `b*` and starring the resulting net is all that is
needed — no appeal to convexity, to `73VIII` `ultraclosed`, or to the
comparison with the ultraweak topology.  The finitary "bounded approximation
in every entourage" phrasing of the ultranorm conventions is recovered from
the net by taking a point on which the finitely many `‖·‖_{ωᵢ}` are already
small, which exists since the index filter is nontrivial. -/
theorem kaplansky_bounded_approx [VonNeumannAlgebra ℬ]
    (A : StarSubalgebra ℂ ℬ) (hA : IsClosed (A : Set ℬ))
    (hdense : UnDense (mulInner ℬ) (A : Set ℬ)) (b : ℬ) :
    ∀ (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (ε : ℝ), 0 < ε →
      ∃ a ∈ A, ‖a‖ ≤ ‖b‖ ∧
        ∀ i, unSeminorm (ωs i) (mulInner ℬ) (a - b) ≤ ε := by
  -- `b*` lies in the *ultrastrong* closure of `𝒜`
  have hbstar : star b ∈ @closure ℬ (ultrastrong ℬ) (A : Set ℬ) := by
    let _ : TopologicalSpace ℬ := ultrastrong ℬ
    rw [mem_closure_iff]
    intro o ho hmem
    obtain ⟨ω, δ, hδ, hsub⟩ := exists_ultrastrong_ball_of_isOpen ho _ hmem
    obtain ⟨d, hd, hdε⟩ := hdense b 1 (fun _ => ω) (δ / 2) (by positivity)
    have h0 := hdε 0
    rw [unSeminorm_mulInner_eq, star_sub] at h0
    have h1 : omegaNorm ℬ ω (star d - star b) < δ := by
      rw [← omegaNorm_neg, neg_sub]; linarith
    exact ⟨star d, hsub h1, star_mem hd⟩
  obtain ⟨ι, l, hl, a, ha, hlim⟩ := Theses.A.VN.kaplansky A hA (star b) hbstar
  haveI := hl
  intro n ωs ε hε
  have hev : ∀ᶠ j in l, ∀ i, omegaNorm ℬ (ωs i) (a j - star b) ≤ ε := by
    refine Filter.eventually_all.mpr fun i => ?_
    have hi := (usTendsto_iff a l (star b)).mp hlim (ωs i)
    filter_upwards [Metric.tendsto_nhds.mp hi ε hε] with j hj
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (omegaNorm_nonneg _ _)] at hj
    exact hj.le
  obtain ⟨j, hj⟩ := hev.exists
  refine ⟨star (a j), star_mem (ha j).1, ?_, fun i => ?_⟩
  · simpa using (ha j).2
  · rw [unSeminorm_mulInner_eq, star_sub, star_star]
    exact hj i

variable {X : Type v}
  [NormedAddCommGroup X] [Module ℂ X] [SMul ℬ X] [CStarModule ℬ X]

/-- **158II** (`kaplansky-hilbmod`, dils.tex:4135, Kaplansky density
theorem for Hilbert C*-modules): let `X` be a Hilbert ℬ-module for a von
Neumann algebra `ℬ` with an ultranorm-dense 𝒜-submodule `D ⊆ X`, where
`𝒜 ⊆ ℬ` is a C*-subalgebra with `⟨y,y⟩ ∈ 𝒜` for all `y ∈ D`.  Then every
`x ∈ X` is the ultranorm limit of a net in `D` norm-bounded by `‖x‖`.

**158III** and **158IV** are the elementary part of the proof (with
`h y = y · 2/(1+⟨y,y⟩)` and `g x = x · 1/(1+√(1-⟨x,x⟩))`: `‖h y‖ ≤ 1` and
`h (g x) = x`) — not converted.  **158V**, the ultranorm continuity of `h`,
is the real work; its four convergence estimates are stated separately
below as `kaplansky_hilbmod_A₁`, `kaplansky_hilbmod_A₁'`,
`kaplansky_hilbmod_A₂` and `kaplansky_hilbmod_A₂'`. -/
theorem kaplansky_hilbmod [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (A : StarSubalgebra ℂ ℬ) (hA : IsClosed (A : Set ℬ))
    (D : Set X)
    (hD0 : (0 : X) ∈ D)
    (hDadd : ∀ d ∈ D, ∀ d' ∈ D, d + d' ∈ D)
    (hDsmul : ∀ a ∈ A, ∀ d ∈ D, a • d ∈ D)
    (hDinner : ∀ d ∈ D, inner ℬ d d ∈ A)
    (hdense : UnDense (inner ℬ) D) (x : X) :
    ∀ (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (ε : ℝ), 0 < ε →
      ∃ d ∈ D, ‖d‖ ≤ ‖x‖ ∧
        ∀ i, unSeminorm (ωs i) (inner ℬ) (x - d) ≤ ε :=
  sorry

/-! ### 158V (dils.tex:4189): ultranorm continuity of `h`

For `h y = y · 2/(1+⟨y,y⟩)` and a net `y_α → y` ultranorm, the splitting
`kaplansky-splitting` (dils.tex:4205) reads

  `⟨h y - h y_α, h y - h y_α⟩ = A₁ + A₁' + A₂ + A₂'`,

and each of the four terms is shown to converge ultraweakly to `0`; that
gives `h y_α → h y` ultranorm.  The four estimates are the four theorems
below.  (`A₁`, `A₁'` are dual to each other under swapping `y` and `y_α`,
as are `A₂`, `A₂'`, but the thesis states — and uses — all four.)

⚠️ **158V is false as stated, and so are all four estimates.**  Take
`ℬ = B(ℓ²)`, `X = ℬ` over itself (`inner a b = b a*`), `pₙ = |eₙ⟩⟨eₙ|`,

  `y₀ = |e₁⟩⟨e₂|`,  `yₙ = |e₁ + eₙ⟩⟨e₂|`  (`n ≥ 2`).

Then `⟨yₙ - y₀, yₙ - y₀⟩ = pₙ`, and `ω(pₙ) → 0` for *every* np-functional
`ω` (normality: `ω = Tr(ρ·)` with `ρ` trace class), so `yₙ → y₀`
ultranorm — indeed inside the norm ball of radius `√2`, so this is not the
usual "the net is only bounded above" gap.  Yet, writing `w = e₁ + eₙ`,
`P = p₁`, `Q = |w⟩⟨w|`, `(1+P)⁻¹ = 1 - ½p₁`, `(1+Q)⁻¹ = 1 - ⅓|w⟩⟨w|`, the
vector functional `ω₀ = ⟨e₁, · e₁⟩` gives, *independently of `n`*,

  `ω₀(A₁) = -1/12`,  `ω₀(A₁') = -1/18`,  `ω₀(A₂') = 1/6`,
  `ω₀(⟨h y₀ - h yₙ, h y₀ - h yₙ⟩) = 1/9`

(and `ω₀(A₂) = 0`, which only means this one functional does not see `A₂`),
so none of them tends to `0`.  The step that fails is the right-hand half
of `kaplanskytodo2` (dils.tex:4251), the one whose "different, but simpler"
proof the thesis omits: here
`⟨y₀, yₙ - y₀⟩(1+⟨yₙ,yₙ⟩)⁻¹ = |e₁⟩⟨eₙ| - ⅓|e₁⟩⟨w|` has `ω₀`-value `-1/3`.
(The left-hand half *is* fine: `⟨y_α-y, y_α(1+⟨y_α,y_α⟩)⁻¹⟩` is Cauchy–Schwarz
against a vector of norm `≤ 1`, and the resolvent bounds below are exactly
what that argument needs.)  The four `sorry`s are therefore *not* closable;
see `PROVING-LOG.md` and `ERRATA.md`.

Two further defects fell out of the same computation.  (i) `kaplansky-splitting`
is off by a factor `4`: with `h y = y·2/(1+⟨y,y⟩)` the left-hand side carries the
square of that `2`, and indeed `⟨h y - h yₙ, h y - h yₙ⟩ = 4(A₁+A₁'+A₂+A₂')`
(`1/9 = 4·(-1/12 - 1/18 + 0 + 1/6)`).  (ii) *Ours*: the statements of
`kaplansky_hilbmod_A₂` and `kaplansky_hilbmod_A₂'` below were transcribed
without the mirroring swap — `inner ℬ (y i - y₀) (y i)` is `⟨y_α, y_α - y⟩`,
where the thesis's `A₂` has `⟨y_α - y, y_α⟩ = inner ℬ (y i) (y i - y₀)`, and
likewise for `A₂'`.  `A₁` and `A₁'` mention only `⟨y,y⟩` and `⟨y_α,y_α⟩` and are
so unaffected.  Both `A₂` statements are false anyway, so this was left alone. -/

/-- `inv1p b = (1 + b)⁻¹`, the resolvent occurring throughout **158V**; for
`b ≥ 0` in a C*-algebra `1 + b` is invertible, so `Ring.inverse` is the
genuine inverse there, and `0 ≤ inv1p b ≤ 1` as well as `0 ≤ b * inv1p b ≤ 1`
(dils.tex:4213). -/
private noncomputable def inv1p (b : ℬ) : ℬ := Ring.inverse (1 + b)

private theorem isUnit_one_add {b : ℬ} (hb : 0 ≤ b) : IsUnit (1 + b) :=
  (IsStrictlyPositive.add_nonneg (⟨zero_le_one, isUnit_one⟩ :
    IsStrictlyPositive (1 : ℬ)) hb).isUnit

private theorem inv1p_mul {b : ℬ} (hb : 0 ≤ b) : inv1p b * (1 + b) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_one_add hb)

private theorem mul_inv1p {b : ℬ} (hb : 0 ≤ b) : (1 + b) * inv1p b = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_one_add hb)

private theorem inv1p_star {b : ℬ} (hb : 0 ≤ b) : star (inv1p b) = inv1p b := by
  rw [inv1p, ← Ring.inverse_star, star_add, star_one, hb.isSelfAdjoint.star_eq]

/-- `t ↦ (1+t)⁻¹`, cut off below `0` so as to be globally continuous. -/
private noncomputable def rf : ℝ → ℝ := fun t => (1 + max t 0)⁻¹

private theorem rf_continuous : Continuous rf := by
  refine Continuous.inv₀ (continuous_const.add (continuous_id.max continuous_const))
    fun t => ?_
  have h : (0 : ℝ) ≤ max t 0 := le_max_right _ _
  exact ne_of_gt (by linarith)

private theorem rf_nonneg (t : ℝ) : 0 ≤ rf t := by
  have h : (0 : ℝ) ≤ max t 0 := le_max_right _ _
  exact inv_nonneg.mpr (by linarith)

private theorem rf_le_one (t : ℝ) : rf t ≤ 1 := by
  have h : (0 : ℝ) ≤ max t 0 := le_max_right _ _
  rw [rf, inv_le_one_iff₀]
  right; linarith

private theorem one_add_mul_rf {t : ℝ} (ht : 0 ≤ t) : (1 + t) * rf t = 1 := by
  rw [rf, max_eq_left ht]
  field_simp

private theorem inv1p_eq_cfc {b : ℬ} (hb : 0 ≤ b) : inv1p b = cfc rf b := by
  have h1 : cfc (fun t : ℝ => 1 + t) b = 1 + b := by
    have h := cfc_add (a := b) (fun _ : ℝ => (1 : ℝ)) (fun t : ℝ => t)
      (by fun_prop) (by fun_prop)
    rwa [cfc_const_one ℝ b, cfc_id' ℝ b] at h
  have h2 : cfc (fun t : ℝ => (1 + t) * rf t) b = cfc (fun _ : ℝ => (1 : ℝ)) b :=
    cfc_congr fun t ht => one_add_mul_rf (spectrum_nonneg_of_nonneg hb ht)
  have h3 : (1 + b) * cfc rf b = 1 := by
    rw [← h1, ← cfc_mul _ _ b (by fun_prop) rf_continuous.continuousOn, h2,
      cfc_const_one ℝ b]
  calc inv1p b = inv1p b * ((1 + b) * cfc rf b) := by rw [h3, mul_one]
    _ = cfc rf b := by rw [← mul_assoc, inv1p_mul hb, one_mul]

private theorem inv1p_nonneg {b : ℬ} (hb : 0 ≤ b) : 0 ≤ inv1p b := by
  rw [inv1p_eq_cfc hb]; exact cfc_nonneg fun t _ => rf_nonneg t

private theorem inv1p_le_one {b : ℬ} (hb : 0 ≤ b) : inv1p b ≤ 1 := by
  rw [inv1p_eq_cfc hb, ← cfc_const_one ℝ b]
  exact (cfc_le_iff _ _ b rf_continuous.continuousOn (by fun_prop)
    hb.isSelfAdjoint).mpr fun t _ => rf_le_one t

/-- `b(1+b)⁻¹ = (1+b)⁻¹b`: both equal `1 − (1+b)⁻¹`. -/
private theorem inv1p_comm {b : ℬ} (hb : 0 ≤ b) : b * inv1p b = inv1p b * b := by
  have h1 : b * inv1p b = 1 - inv1p b := by
    have := mul_inv1p hb
    rw [add_mul, one_mul] at this
    linear_combination (norm := noncomm_ring) this
  have h2 : inv1p b * b = 1 - inv1p b := by
    have := inv1p_mul hb
    rw [mul_add, mul_one] at this
    linear_combination (norm := noncomm_ring) this
  rw [h1, h2]

/-- `(1+b)⁻¹b(1+b)⁻¹ = (1+b)⁻¹ − ((1+b)⁻¹)²`, hence `≤ 1`. -/
private theorem inv1p_conj_le_one {b : ℬ} (hb : 0 ≤ b) :
    inv1p b * b * inv1p b ≤ 1 := by
  have h : inv1p b * b * inv1p b = inv1p b - inv1p b * inv1p b := by
    have := inv1p_mul hb
    rw [mul_add, mul_one] at this
    have h2 : inv1p b * b = 1 - inv1p b := by
      linear_combination (norm := noncomm_ring) this
    rw [h2]; noncomm_ring
  have hsq : 0 ≤ inv1p b * inv1p b := by
    have := star_mul_self_nonneg (inv1p b)
    rwa [inv1p_star hb] at this
  rw [h]
  exact (sub_le_self _ hsq).trans (inv1p_le_one hb)

variable {ι : Type w} {l : Filter ι}

/-- **158V**.1 (dils.tex:4193, the term `A₁` of `kaplansky-splitting`): if
`y_α → y` ultranorm, then

  `A₁ = ⟨y,y⟩ (1+⟨y,y⟩)⁻² - (1+⟨y_α,y_α⟩)⁻¹ ⟨y,y⟩ (1+⟨y,y⟩)⁻¹ → 0`

ultraweakly.  Proof (dils.tex:4211): rewrite `A₁` as
`(1+⟨y,y⟩)⁻¹ (⟨y_α-y,y_α⟩ + ⟨y,y_α-y⟩) (1+⟨y_α,y_α⟩)⁻¹ ⟨y,y⟩ (1+⟨y,y⟩)⁻¹`
using the resolvent identity, then use ultraweak continuity of
multiplication by constants (`mult-uws-cont`) together with
`⟨y_α-y, y_α (1+⟨y_α,y_α⟩)⁻¹⟩ → 0` and `⟨y, y_α-y⟩ (1+⟨y_α,y_α⟩)⁻¹ → 0`,
both by Cauchy–Schwarz for the `f`-seminorms. -/
private theorem kaplansky_hilbmod_A₁ [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (y : ι → X) (y₀ : X) (hy : UnTendsto (inner ℬ) y l y₀) :
    UWTendsto (fun i =>
        inner ℬ y₀ y₀ * inv1p (inner ℬ y₀ y₀) * inv1p (inner ℬ y₀ y₀)
          - inv1p (inner ℬ (y i) (y i))
              * (inner ℬ y₀ y₀ * inv1p (inner ℬ y₀ y₀))) l 0 :=
  sorry

/-- **158V**.2 (dils.tex:4196, the term `A₁'` of `kaplansky-splitting`): if
`y_α → y` ultranorm, then

  `A₁' = ⟨y_α,y_α⟩ (1+⟨y_α,y_α⟩)⁻² - (1+⟨y,y⟩)⁻¹ ⟨y_α,y_α⟩ (1+⟨y_α,y_α⟩)⁻¹ → 0`

ultraweakly.  This is `A₁` with the roles of `y` and `y_α` interchanged;
"in a similar way one sees `A₁' → 0` ultraweakly" (dils.tex:4272). -/
private theorem kaplansky_hilbmod_A₁' [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (y : ι → X) (y₀ : X) (hy : UnTendsto (inner ℬ) y l y₀) :
    UWTendsto (fun i =>
        inner ℬ (y i) (y i) * inv1p (inner ℬ (y i) (y i))
              * inv1p (inner ℬ (y i) (y i))
          - inv1p (inner ℬ y₀ y₀)
              * (inner ℬ (y i) (y i) * inv1p (inner ℬ (y i) (y i)))) l 0 :=
  sorry

/-- **158V**.3 (dils.tex:4200, the term `A₂` of `kaplansky-splitting`): if
`y_α → y` ultranorm, then

  `A₂ = (1+⟨y,y⟩)⁻¹ ⟨y_α - y, y_α⟩ (1+⟨y_α,y_α⟩)⁻¹ → 0`

ultraweakly; "the proofs for `A₂, A₂' → 0` are very similar"
(dils.tex:4273) — the middle factor is exactly the quantity bounded by
Cauchy–Schwarz in the proof of `A₁`, and the outer resolvents are bounded
by `1`. -/
private theorem kaplansky_hilbmod_A₂ [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (y : ι → X) (y₀ : X) (hy : UnTendsto (inner ℬ) y l y₀) :
    UWTendsto (fun i =>
        inv1p (inner ℬ y₀ y₀) * inner ℬ (y i - y₀) (y i)
          * inv1p (inner ℬ (y i) (y i))) l 0 :=
  sorry

/-- **158V**.4 (dils.tex:4202, the term `A₂'` of `kaplansky-splitting`): if
`y_α → y` ultranorm, then

  `A₂' = (1+⟨y_α,y_α⟩)⁻¹ ⟨y - y_α, y⟩ (1+⟨y,y⟩)⁻¹ → 0`

ultraweakly; as for `A₂` (dils.tex:4273). -/
private theorem kaplansky_hilbmod_A₂' [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (y : ι → X) (y₀ : X) (hy : UnTendsto (inner ℬ) y l y₀) :
    UWTendsto (fun i =>
        inv1p (inner ℬ (y i) (y i)) * inner ℬ (y₀ - y i) y₀
          * inv1p (inner ℬ y₀ y₀)) l 0 :=
  sorry

end Kaplansky

end Theses.B.Dils
