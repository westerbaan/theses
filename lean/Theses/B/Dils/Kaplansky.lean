/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 4082–4279.

  parsec 1580:  the Kaplansky density theorem for Hilbert C*-modules

**158Ia** is proved; **158II** and the four **158V** estimates are `sorry`
(the latter four are *false*, see below).  The **commutative case of 158II**
is proved outright (`kaplansky_hilbmod_of_commutative`, end of this file) —
there the mirror obstruction vanishes and a one-shot renormalization closes
the weak statement.  For the general 158II the sound part of a
replacement proof is banked as `kaplansky_hilbmod_of_weak` (axiom-clean):
158II reduces, by an elementary Mazur-style variational argument, to *weak*
bounded approximation — making `ω ⟪w, x−d⟫` small with `d` in the
`‖x‖`-ball of `D`; see the section "Reduction of 158II to weak bounded
approximation" and `PROVING-LOG.md`.  Following the conventions of
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
theorem unSeminorm_mulInner_eq (ω : NPFunctional ℬ) (x : ℬ) :
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
`kaplansky_hilbmod_A₂` and `kaplansky_hilbmod_A₂'`.

⚠️ The thesis's proof route is **dead**: 158V is false (see the section
comment below), so this `sorry` cannot be closed by the printed argument.
The statement itself is believed true but currently *open*: by
`kaplansky_hilbmod_of_weak` (end of this file, proved) it reduces to the
weak bounded-approximation statement recorded there; the obstruction to
proving *that* — and the reason no counterexample is known either — is
analyzed in `PROVING-LOG.md`.  The **commutative case** is proved:
`kaplansky_hilbmod_of_commutative` (end of this file). -/
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

/-! ### Reduction of 158II to weak bounded approximation

Since the thesis's route through 158V is closed (see above), we record here
the part of a replacement proof that is certain: a Mazur-style variational
argument reducing the *strong* (seminorm) approximation of **158II** to
*weak* approximation — approximating the finitely many complex numbers
`ω [w, x]` by `ω [w, d]` with `d` in the `‖x‖`-ball of `D`.  The set
`C = D ∩ ball(‖x‖)` is convex, and for the semidefinite inner product
`(u,v) ↦ ω[u,v]` weak approximability of `x` by a convex set forces seminorm
approximability; the proof is the elementary approximate-nearest-point
computation, needing no completion, quotient, or Riesz representation.

First, finite sums of np-functionals (`ω = Σ ωᵢ` dominates each `ωᵢ`, which
turns the `n` seminorm bounds of the conclusion into one). -/

section WeakToStrong

omit [StarOrderedRing ℬ] in
theorem np_mono (ω : NPFunctional ℬ) {a b : ℬ} (h : a ≤ b) :
    ω a ≤ ω b := ω.toPositiveLinearMap.monotone h

omit [StarOrderedRing ℬ] in
theorem preservesDirSups_npAdd (ω₁ ω₂ : NPFunctional ℬ) :
    PreservesDirSups (fun a : ℬ => ω₁ a + ω₂ a) := by
  intro D s hne hdir hlub
  have hFl := ω₁.preservesDirSups' D s hne hdir hlub
  have hGl := ω₂.preservesDirSups' D s hne hdir hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact add_le_add (hFl.1 ⟨d, hd, rfl⟩) (hGl.1 ⟨d, hd, rfl⟩)
  · intro z hz
    have key : ∀ d' ∈ D, (ω₁ ((s : selfAdjoint ℬ) : ℬ))
        ≤ z - ω₂ ((d' : selfAdjoint ℬ) : ℬ) := by
      intro d' hd'
      refine hFl.2 ?_
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨e, he, hde, hd'e⟩ := hdir d hd d' hd'
      have h1 : ω₁ ((d : selfAdjoint ℬ) : ℬ) ≤ ω₁ ((e : selfAdjoint ℬ) : ℬ) :=
        np_mono ω₁ (Subtype.coe_le_coe.mpr hde)
      have h2 : ω₂ ((d' : selfAdjoint ℬ) : ℬ) ≤ ω₂ ((e : selfAdjoint ℬ) : ℬ) :=
        np_mono ω₂ (Subtype.coe_le_coe.mpr hd'e)
      have h3 : ω₁ ((e : selfAdjoint ℬ) : ℬ) + ω₂ ((e : selfAdjoint ℬ) : ℬ) ≤ z :=
        hz ⟨e, he, rfl⟩
      rw [le_sub_iff_add_le]
      calc ω₁ ((d : selfAdjoint ℬ) : ℬ) + ω₂ ((d' : selfAdjoint ℬ) : ℬ)
          ≤ ω₁ ((e : selfAdjoint ℬ) : ℬ) + ω₂ ((e : selfAdjoint ℬ) : ℬ) :=
            add_le_add h1 h2
        _ ≤ z := h3
    have h4 : ω₂ ((s : selfAdjoint ℬ) : ℬ)
        ≤ z - ω₁ ((s : selfAdjoint ℬ) : ℬ) := by
      refine hGl.2 ?_
      rintro _ ⟨d', hd', rfl⟩
      rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
      exact key d' hd'
    rw [le_sub_iff_add_le, add_comm] at h4
    exact h4

/-- The sum of two np-functionals. -/
noncomputable def npAdd (ω₁ ω₂ : NPFunctional ℬ) : NPFunctional ℬ where
  toPositiveLinearMap := ω₁.toPositiveLinearMap + ω₂.toPositiveLinearMap
  preservesDirSups' := by
    have h : ⇑(ω₁.toPositiveLinearMap + ω₂.toPositiveLinearMap)
        = fun a : ℬ => ω₁ a + ω₂ a :=
      funext fun a => by rw [PositiveLinearMap.add_apply]; rfl
    rw [h]
    exact preservesDirSups_npAdd ω₁ ω₂

/-- The zero np-functional. -/
noncomputable def npZero : NPFunctional ℬ where
  toPositiveLinearMap := 0
  preservesDirSups' := by
    intro D s hne hdir hlub
    have h : ⇑(0 : ℬ →ₚ[ℂ] ℂ) = fun _ : ℬ => (0 : ℂ) :=
      funext fun a => PositiveLinearMap.zero_apply a
    rw [h]
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact le_refl 0
    · intro z hz
      exact hz ⟨hne.choose, hne.choose_spec, rfl⟩

/-- The sum `Σᵢ ωᵢ` of a finite family of np-functionals. -/
noncomputable def npSum : ∀ (n : ℕ), (Fin n → NPFunctional ℬ) → NPFunctional ℬ
  | 0, _ => npZero
  | (n + 1), ωs => npAdd (ωs 0) (npSum n fun i => ωs i.succ)

theorem npAdd_apply (ω₁ ω₂ : NPFunctional ℬ) (a : ℬ) :
    npAdd ω₁ ω₂ a = ω₁ a + ω₂ a := by
  change (ω₁.toPositiveLinearMap + ω₂.toPositiveLinearMap) a = _
  rw [PositiveLinearMap.add_apply]; rfl

theorem npSum_apply (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (a : ℬ) :
    npSum n ωs a = ∑ i, ωs i a := by
  induction n with
  | zero => simp [npSum]; rfl
  | succ n ih =>
      rw [npSum, npAdd_apply, ih, Fin.sum_univ_succ]

omit [StarOrderedRing ℬ] in
theorem np_re_nonneg' (ω : NPFunctional ℬ) {a : ℬ} (ha : 0 ≤ a) :
    0 ≤ (ω a).re := by
  have h : ω 0 ≤ ω a := np_mono ω ha
  have h0 : ω (0 : ℬ) = 0 := map_zero ω.toPositiveLinearMap
  rw [h0] at h
  simpa using (Complex.le_def.mp h).1

/-- Each `‖·‖_{ωᵢ}` is dominated by `‖·‖_{Σⱼωⱼ}`, in the `omegaNorm` form.
(The `unSeminorm` form is `unSeminorm_le_npSum` below.) -/
theorem omegaNorm_le_npSum (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (i : Fin n)
    (a : ℬ) : omegaNorm ℬ (ωs i) a ≤ omegaNorm ℬ (npSum n ωs) a := by
  refine Real.sqrt_le_sqrt ?_
  rw [npSum_apply, Complex.re_sum]
  exact Finset.single_le_sum
    (f := fun j => (ωs j (star a * a)).re)
    (fun j _ => np_re_nonneg' (ωs j) (star_mul_self_nonneg a))
    (Finset.mem_univ i)

omit [StarOrderedRing ℬ] in
theorem np_re_mono' (ω : NPFunctional ℬ) {a b : ℬ} (h : a ≤ b) :
    (ω a).re ≤ (ω b).re :=
  (Complex.le_def.mp (np_mono ω h)).1

private theorem np_star' (ω : NPFunctional ℬ) (a : ℬ) :
    ω (star a) = starRingEnd ℂ (ω a) :=
  map_star ω.toPositiveLinearMap a

omit [CStarModule ℬ X] in
/-- Each summand seminorm is dominated by the `npSum` seminorm. -/
private theorem unSeminorm_le_npSum (n : ℕ) (ωs : Fin n → NPFunctional ℬ)
    (i : Fin n) (B : BInner ℬ X) (u : X) :
    unSeminorm (ωs i) B.inner u ≤ unSeminorm (npSum n ωs) B.inner u := by
  refine Real.sqrt_le_sqrt ?_
  rw [npSum_apply]
  have hsum : (∑ j, ωs j (B.inner u u)).re = ∑ j, (ωs j (B.inner u u)).re :=
    Complex.re_sum _ _
  rw [hsum]
  exact Finset.single_le_sum
    (f := fun j => (ωs j (B.inner u u)).re)
    (fun j _ => np_re_nonneg' (ωs j) (B.inner_self_nonneg u))
    (Finset.mem_univ i)

omit [CStarModule ℬ X] in
/-- `‖·‖_ω` of a negation. -/
private theorem unSeminorm_neg' (ω : NPFunctional ℬ) (B : BInner ℬ X) (u : X) :
    unSeminorm ω B.inner (-u) = unSeminorm ω B.inner u := by
  have h : B.inner (-u) (-u) = B.inner u u := by
    rw [show (-u) = ((-1 : ℂ)) • u by simp, B.inner_smul_right_complex,
      B.inner_smul_left_complex]
    simp
  rw [unSeminorm, unSeminorm, h]

/-- Triangle inequality for differences. -/
private theorem unSeminorm_sub_le' (ω : NPFunctional ℬ) (B : BInner ℬ X)
    (u v : X) :
    unSeminorm ω B.inner (u - v)
      ≤ unSeminorm ω B.inner u + unSeminorm ω B.inner v := by
  have h := unSeminorm_add_le ω B u (-v)
  rw [← sub_eq_add_neg, unSeminorm_neg'] at h
  exact h

omit [CStarModule ℬ X] in
/-- The quadratic expansion `‖u - t·v‖_ω² = ‖u‖_ω² - 2t·Re ω[u,v] + t²‖v‖_ω²`
for real `t`. -/
private theorem unSeminorm_sub_smul_sq (ω : NPFunctional ℬ) (B : BInner ℬ X)
    (u v : X) (t : ℝ) :
    unSeminorm ω B.inner (u - ((t : ℝ) : ℂ) • v) ^ 2
      = unSeminorm ω B.inner u ^ 2 - 2 * t * (ω (B.inner u v)).re
        + t ^ 2 * unSeminorm ω B.inner v ^ 2 := by
  have hexp : B.inner (u - ((t : ℝ) : ℂ) • v) (u - ((t : ℝ) : ℂ) • v)
      = B.inner u u - ((t : ℝ) : ℂ) • B.inner u v
        - ((t : ℝ) : ℂ) • B.inner v u
        + (((t : ℝ) : ℂ) * ((t : ℝ) : ℂ)) • B.inner v v := by
    rw [B.inner_sub_right, B.inner_sub_left, B.inner_sub_left,
      B.inner_smul_right_complex, B.inner_smul_left_complex,
      B.inner_smul_left_complex, B.inner_smul_right_complex, smul_smul]
    rw [Complex.conj_ofReal]
    abel
  have hvu : ω (B.inner v u) = starRingEnd ℂ (ω (B.inner u v)) := by
    rw [← B.star_inner u v, np_star']
  have happ : ω (B.inner (u - ((t : ℝ) : ℂ) • v) (u - ((t : ℝ) : ℂ) • v))
      = ω (B.inner u u) - ((t : ℝ) : ℂ) * ω (B.inner u v)
        - ((t : ℝ) : ℂ) * starRingEnd ℂ (ω (B.inner u v))
        + (((t : ℝ) : ℂ) * ((t : ℝ) : ℂ)) * ω (B.inner v v) := by
    have hadd : ∀ a b : ℬ, ω (a + b) = ω a + ω b := fun a b =>
      map_add ω.toPositiveLinearMap a b
    have hsub : ∀ a b : ℬ, ω (a - b) = ω a - ω b := fun a b =>
      map_sub ω.toPositiveLinearMap a b
    have hsmul : ∀ (c : ℂ) (a : ℬ), ω (c • a) = c * ω a := fun c a =>
      map_smul ω.toPositiveLinearMap c a
    rw [hexp, hadd, hsub, hsub, hsmul, hsmul, hsmul, hvu]
  rw [unSeminorm_sq, unSeminorm_sq, unSeminorm_sq, happ]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
    pow_two, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The variational (Mazur-style) step: for the semidefinite inner product
`(u,v) ↦ ω [u,v]` of a single np-functional, a point that is *weakly*
approximable by a convex set `C` of uniformly bounded `‖·‖_ω`-distance is
`‖·‖_ω`-approximable by `C`.  Entirely elementary: no completion, quotient,
or Riesz representation — only the parallelogram-type expansion
`unSeminorm_sub_smul_sq` and the approximate-nearest-point computation. -/
private theorem weak_to_strong (ω : NPFunctional ℬ) (B : BInner ℬ X) (x : X)
    (C : Set X) (M : ℝ)
    (hbdd : ∀ d ∈ C, unSeminorm ω B.inner (x - d) ≤ M)
    (hconv : ∀ d ∈ C, ∀ d' ∈ C, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      d + ((t : ℝ) : ℂ) • (d' - d) ∈ C)
    (hweak : ∀ (w : X) (η : ℝ), 0 < η →
      ∃ d ∈ C, ‖ω (B.inner w (x - d))‖ ≤ η)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d ∈ C, unSeminorm ω B.inner (x - d) ≤ ε := by
  have hsubω : ∀ a b : ℬ, ω (a - b) = ω a - ω b := fun a b =>
    map_sub ω.toPositiveLinearMap a b
  set p : X → ℝ := fun z => unSeminorm ω B.inner (x - z) with hp
  obtain ⟨d₀, hd₀C, -⟩ := hweak x 1 one_pos
  have hM0 : 0 ≤ M :=
    le_trans (unSeminorm_nonneg ω B.inner (x - d₀)) (hbdd d₀ hd₀C)
  set S : Set ℝ := p '' C with hS
  have hSne : S.Nonempty := ⟨p d₀, d₀, hd₀C, rfl⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro - ⟨d, hd, rfl⟩
    exact unSeminorm_nonneg ω B.inner _
  set γ := sInf S with hγ
  have hγ0 : 0 ≤ γ := by
    refine le_csInf hSne ?_
    rintro - ⟨d, hd, rfl⟩
    exact unSeminorm_nonneg ω B.inner _
  have hγle : ∀ d ∈ C, γ ≤ p d := fun d hd => csInf_le hSbdd ⟨d, hd, rfl⟩
  have hγM : γ ≤ M := le_trans (hγle d₀ hd₀C) (hbdd d₀ hd₀C)
  -- main estimate: `γ² ≤ η(2M+2)` for every `0 < η ≤ 1`
  have hmain : ∀ η : ℝ, 0 < η → η ≤ 1 → γ ^ 2 ≤ η * (2 * M + 2) := by
    intro η hη hη1
    have h2M1 : (0 : ℝ) < 2 * M + 1 := by linarith
    -- an approximate nearest point `d*`
    obtain ⟨s, hsS, hslt⟩ := exists_lt_of_csInf_lt hSne
      (show sInf S < γ + η ^ 2 / (2 * M + 1) by
        have hpos : 0 < η ^ 2 / (2 * M + 1) := div_pos (by positivity) h2M1
        rw [← hγ]; linarith)
    obtain ⟨dstar, hdstarC, rfl⟩ := hsS
    have hpn : 0 ≤ p dstar := unSeminorm_nonneg ω B.inner _
    have hPM : p dstar ≤ M := hbdd _ hdstarC
    have hP2 : p dstar ^ 2 ≤ γ ^ 2 + η ^ 2 := by
      have hd1 : η ^ 2 / (2 * M + 1) ≤ η ^ 2 := by
        rw [div_le_iff₀ h2M1]; nlinarith [sq_nonneg η]
      have hd2 : η ^ 2 / (2 * M + 1) * (2 * γ + η ^ 2 / (2 * M + 1))
          ≤ η ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ h2M1]
        have hd3 : η ^ 2 / (2 * M + 1) ≤ 1 := by
          rw [div_le_one h2M1]; nlinarith
        nlinarith [sq_nonneg η]
      nlinarith [hslt, hγ0]
    -- a weak approximant against `w = x - d*`
    obtain ⟨d, hdC, hdw⟩ := hweak (x - dstar) (η ^ 2) (by positivity)
    set u := x - dstar with hu
    set v := d - dstar with hv
    have hvsplit : v = u - (x - d) := by rw [hv, hu]; abel
    -- `‖v‖_ω ≤ 2M`
    have hq : unSeminorm ω B.inner v ≤ 2 * M := by
      have h := unSeminorm_sub_le' ω B u (x - d)
      rw [← hvsplit] at h
      exact le_trans h (by
        have h1 : unSeminorm ω B.inner u ≤ M := hbdd _ hdstarC
        have h2 : unSeminorm ω B.inner (x - d) ≤ M := hbdd _ hdC
        linarith)
    -- `Re ω[u,v] ≥ γ² - η²`
    have hR : γ ^ 2 - η ^ 2 ≤ (ω (B.inner u v)).re := by
      have hsplit2 : B.inner u v = B.inner u u - B.inner u (x - d) := by
        rw [hvsplit, B.inner_sub_right]
      have hre1 : (ω (B.inner u (x - d))).re ≤ η ^ 2 :=
        le_trans (Complex.re_le_norm _) hdw
      have huu : γ ^ 2 ≤ (ω (B.inner u u)).re := by
        have h1 : γ ≤ p dstar := hγle _ hdstarC
        have h2 : γ ^ 2 ≤ p dstar ^ 2 := by nlinarith
        rw [hp] at h2
        rw [← unSeminorm_sq ω B u]
        exact h2
      rw [hsplit2, hsubω, Complex.sub_re]
      linarith
    -- the quadratic in `t`
    have hkey : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        0 ≤ η ^ 2 - 2 * t * (γ ^ 2 - η ^ 2) + t ^ 2 * (2 * M) ^ 2 := by
      intro t ht0 ht1
      have hdt : dstar + ((t : ℝ) : ℂ) • v ∈ C := hconv dstar hdstarC d hdC t ht0 ht1
      have hxd : x - (dstar + ((t : ℝ) : ℂ) • v) = u - ((t : ℝ) : ℂ) • v := by
        rw [hu]; abel
      have hγt : γ ≤ p (dstar + ((t : ℝ) : ℂ) • v) := hγle _ hdt
      rw [hp] at hγt
      simp only [hxd] at hγt
      have hsq : γ ^ 2 ≤ unSeminorm ω B.inner (u - ((t : ℝ) : ℂ) • v) ^ 2 := by
        nlinarith [unSeminorm_nonneg ω B.inner (u - ((t : ℝ) : ℂ) • v)]
      rw [unSeminorm_sub_smul_sq] at hsq
      have e1 : 2 * t * (γ ^ 2 - η ^ 2) ≤ 2 * t * (ω (B.inner u v)).re :=
        mul_le_mul_of_nonneg_left hR (by linarith)
      have e2 : t ^ 2 * unSeminorm ω B.inner v ^ 2 ≤ t ^ 2 * (2 * M) ^ 2 := by
        have := unSeminorm_nonneg ω B.inner v
        have h5 : unSeminorm ω B.inner v ^ 2 ≤ (2 * M) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left h5 (sq_nonneg t)
      have h6 : unSeminorm ω B.inner u ^ 2 = p dstar ^ 2 := by rw [hp, hu]
      nlinarith [hsq, hP2]
    -- optimize `t`
    by_cases hcase : γ ^ 2 ≤ η ^ 2
    · nlinarith
    · push_neg at hcase
      set K := 4 * M ^ 2 + 1 with hK
      have hKpos : (0 : ℝ) < K := by positivity
      set t0 := (γ ^ 2 - η ^ 2) / K with ht0def
      have hApos : 0 < γ ^ 2 - η ^ 2 := by linarith
      have ht00 : 0 ≤ t0 := le_of_lt (div_pos hApos hKpos)
      have ht01 : t0 ≤ 1 := by
        rw [ht0def, div_le_one hKpos, hK]
        nlinarith [sq_nonneg η]
      have hkey0 := hkey t0 ht00 ht01
      have hsubst : t0 * K = γ ^ 2 - η ^ 2 := div_mul_cancel₀ _ hKpos.ne'
      -- `0 ≤ η² − t₀²(4M²+2)` hence `(γ²−η²)² ≤ η²(4M²+1)`
      have hAsq : (γ ^ 2 - η ^ 2) ^ 2 ≤ η ^ 2 * K := by
        nlinarith [hkey0, hsubst, hKpos, sq_nonneg t0]
      have hB0 : 0 < η * (2 * M + 1) := mul_pos hη (by linarith)
      have h9 : η ^ 2 * K ≤ (η * (2 * M + 1)) ^ 2 := by
        rw [hK]; nlinarith [sq_nonneg η, hM0]
      have hfin : γ ^ 2 - η ^ 2 ≤ η * (2 * M + 1) := by
        nlinarith [hAsq, h9, hApos, hB0]
      nlinarith
  -- from the main estimate, `γ ≤ ε/2`
  have hγε : γ ≤ ε / 2 := by
    set η := min 1 ((ε / 2) ^ 2 / (2 * M + 2)) with hηdef
    have hη0 : 0 < η := lt_min one_pos (by positivity)
    have h1 := hmain η hη0 (min_le_left _ _)
    have h6 : η * (2 * M + 2) ≤ (ε / 2) ^ 2 := by
      have h7 : η ≤ (ε / 2) ^ 2 / (2 * M + 2) := min_le_right _ _
      calc η * (2 * M + 2) ≤ (ε / 2) ^ 2 / (2 * M + 2) * (2 * M + 2) :=
            mul_le_mul_of_nonneg_right h7 (by linarith)
        _ = (ε / 2) ^ 2 := div_mul_cancel₀ _ (by positivity)
    have h8 : γ ^ 2 ≤ (ε / 2) ^ 2 := le_trans h1 h6
    nlinarith
  obtain ⟨s, hsS, hslt⟩ := exists_lt_of_csInf_lt hSne
    (show sInf S < ε from lt_of_le_of_lt hγε (by linarith))
  obtain ⟨d, hdC, rfl⟩ := hsS
  exact ⟨d, hdC, le_of_lt hslt⟩

omit [StarOrderedRing ℬ] in
/-- Scalar action through the algebra: `(c·1) • d = c • d` in a
`CStarModule` (by definiteness of the inner product). -/
private theorem smul_one_smul' (c : ℂ) (d : X) :
    (c • (1 : ℬ)) • d = c • d := by
  have hz : inner ℬ ((c • (1 : ℬ)) • d - c • d) ((c • (1 : ℬ)) • d - c • d)
      = (0 : ℬ) := by
    simp only [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
      CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
      CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex,
      star_smul, star_one, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      smul_smul]
    module
  exact sub_eq_zero.mp (CStarModule.inner_self.mp hz)

omit [StarOrderedRing ℬ] in
private theorem np_re_one_smul (ω : NPFunctional ℬ) (r : ℝ) :
    (ω (r • (1 : ℬ))).re = r * (ω 1).re := by
  have h : (r • (1 : ℬ)) = ((r : ℝ) : ℂ) • (1 : ℬ) :=
    RCLike.real_smul_eq_coe_smul (K := ℂ) r 1
  have h2 : ω (((r : ℝ) : ℂ) • (1 : ℬ)) = ((r : ℝ) : ℂ) * ω 1 :=
    map_smul ω.toPositiveLinearMap _ _
  rw [h, h2]
  simp [Complex.mul_re]

/-- `‖z‖_ω ≤ √(ω 1) ‖z‖`: the ultranorm seminorms are dominated by the
norm. -/
private theorem unSeminorm_le_norm' (ω : NPFunctional ℬ) (z : X) :
    unSeminorm ω (cstarBInner ℬ X).inner z ≤ Real.sqrt (ω 1).re * ‖z‖ := by
  have h1 : inner ℬ z z ≤ algebraMap ℝ ℬ ‖inner ℬ z z‖ :=
    (CStarModule.isSelfAdjoint_inner_self (A := ℬ) (x := z)).le_algebraMap_norm_self
  have h2 : (ω (inner ℬ z z)).re ≤ ‖inner ℬ z z‖ * (ω 1).re := by
    have h3 := np_re_mono' ω h1
    rwa [Algebra.algebraMap_eq_smul_one, np_re_one_smul] at h3
  have h4 : ‖inner ℬ z z‖ = ‖z‖ ^ 2 := (CStarModule.norm_sq_eq (A := ℬ)).symm
  calc unSeminorm ω (cstarBInner ℬ X).inner z
      = Real.sqrt (ω (inner ℬ z z)).re := rfl
    _ ≤ Real.sqrt (‖z‖ ^ 2 * (ω 1).re) := Real.sqrt_le_sqrt (by rw [← h4]; exact h2)
    _ = ‖z‖ * Real.sqrt (ω 1).re := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg z)]
    _ = Real.sqrt (ω 1).re * ‖z‖ := mul_comm _ _

omit [StarOrderedRing ℬ] in
include ℬ in
/-- `‖c • d‖ = ‖c‖ ‖d‖` for complex scalars, from the `CStarModule` norm
(the section does not assume `NormedSpace ℂ X`). -/
private theorem norm_smul_complex (c : ℂ) (d : X) : ‖c • d‖ = ‖c‖ * ‖d‖ := by
  have h1 : inner ℬ (c • d) (c • d) = (star c * c) • inner ℬ d d := by
    rw [CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex,
      smul_smul]
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ), h1, norm_smul, norm_mul,
    norm_star, CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ) (x := d)]
  have h2 : ‖c‖ * ‖c‖ * ‖inner ℬ d d‖ = ‖c‖ ^ 2 * ‖inner ℬ d d‖ := by ring
  rw [h2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]

/-- **Reduction of 158II to weak bounded approximation.**  If, for every
np-functional `ω`, every `w ∈ X` and every `η > 0`, some `d ∈ D` with
`‖d‖ ≤ ‖x‖` makes the single complex number `ω ⟪w, x - d⟫` small, then the
full conclusion of `kaplansky_hilbmod` holds for `x`: `d ∈ D` with
`‖d‖ ≤ ‖x‖` and `x - d` small in finitely many ultranorm seminorms at once.

This is the sound part of a replacement proof for **158II** (whose route
through 158V is closed — see the section comment above): `C = D ∩ ball(‖x‖)`
is convex, so by the variational argument `weak_to_strong` its weak
approximations of `x` upgrade to `‖·‖_ω`-approximations, and a finite family
`ω₁, …, ωₙ` is dominated by the single np-functional `Σᵢ ωᵢ` (`npSum`).
Note no von Neumann algebra, completeness, closedness of `A`, ultranorm
density of `D`, or `⟪d,d⟫ ∈ A` hypothesis is needed for this step. -/
theorem kaplansky_hilbmod_of_weak
    (A : StarSubalgebra ℂ ℬ) (D : Set X)
    (hDadd : ∀ d ∈ D, ∀ d' ∈ D, d + d' ∈ D)
    (hDsmul : ∀ a ∈ A, ∀ d ∈ D, a • d ∈ D)
    (x : X)
    (hweak : ∀ (ω : NPFunctional ℬ) (w : X) (η : ℝ), 0 < η →
      ∃ d ∈ D, ‖d‖ ≤ ‖x‖ ∧ ‖ω (inner ℬ w (x - d))‖ ≤ η) :
    ∀ (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (ε : ℝ), 0 < ε →
      ∃ d ∈ D, ‖d‖ ≤ ‖x‖ ∧
        ∀ i, unSeminorm (ωs i) (inner ℬ) (x - d) ≤ ε := by
  intro n ωs ε hε
  set ω := npSum n ωs with hω
  set C : Set X := {d | d ∈ D ∧ ‖d‖ ≤ ‖x‖} with hC
  -- `D` is closed under complex scalars, through `A ∋ c·1`
  have hDsmulℂ : ∀ (c : ℂ), ∀ d ∈ D, c • d ∈ D := by
    intro c d hd
    have h1 : (c • (1 : ℬ)) ∈ A := by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact A.algebraMap_mem c
    have h2 := hDsmul _ h1 d hd
    rwa [smul_one_smul' c d] at h2
  -- `C` is convex
  have hconv : ∀ d ∈ C, ∀ d' ∈ C, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      d + ((t : ℝ) : ℂ) • (d' - d) ∈ C := by
    intro d hd d' hd' t ht0 ht1
    have heq : d + ((t : ℝ) : ℂ) • (d' - d)
        = ((1 - t : ℝ) : ℂ) • d + ((t : ℝ) : ℂ) • d' := by
      push_cast
      module
    rw [heq]
    refine ⟨hDadd _ (hDsmulℂ _ _ hd.1) _ (hDsmulℂ _ _ hd'.1), ?_⟩
    calc ‖((1 - t : ℝ) : ℂ) • d + ((t : ℝ) : ℂ) • d'‖
        ≤ ‖((1 - t : ℝ) : ℂ) • d‖ + ‖((t : ℝ) : ℂ) • d'‖ := norm_add_le _ _
      _ = (1 - t) * ‖d‖ + t * ‖d'‖ := by
          rw [norm_smul_complex (ℬ := ℬ), norm_smul_complex (ℬ := ℬ),
            Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t), abs_of_nonneg ht0]
      _ ≤ (1 - t) * ‖x‖ + t * ‖x‖ := by nlinarith [hd.2, hd'.2]
      _ = ‖x‖ := by ring
  -- the distances `‖x - d‖_ω` are bounded over `C`
  have hbddM : ∀ d ∈ C, unSeminorm ω (cstarBInner ℬ X).inner (x - d)
      ≤ Real.sqrt (ω 1).re * (2 * ‖x‖) := by
    intro d hd
    refine le_trans (unSeminorm_le_norm' ω (x - d)) ?_
    have h1 : ‖x - d‖ ≤ 2 * ‖x‖ := by
      have := norm_sub_le x d
      have := hd.2
      linarith
    have h2 : 0 ≤ Real.sqrt (ω 1).re := Real.sqrt_nonneg _
    nlinarith
  -- weak approximation within `C`
  have hweakC : ∀ (w : X) (η : ℝ), 0 < η →
      ∃ d ∈ C, ‖ω ((cstarBInner ℬ X).inner w (x - d))‖ ≤ η := by
    intro w η hη
    obtain ⟨d, hd, hnorm, hval⟩ := hweak ω w η hη
    exact ⟨d, ⟨hd, hnorm⟩, hval⟩
  obtain ⟨d, hdC, hdε⟩ := weak_to_strong ω (cstarBInner ℬ X) x C _ hbddM hconv
    hweakC ε hε
  refine ⟨d, hdC.1, hdC.2, fun i => ?_⟩
  exact le_trans (unSeminorm_le_npSum n ωs i (cstarBInner ℬ X) (x - d)) hdε

end WeakToStrong

/-! ### 158II, the commutative case

⚠️ *Class 2 — different proof.*  For **commutative** `ℬ` the statement of
**158II** is provable outright, by a one-shot renormalization that is *not*
the thesis's route (158V, which is false in general, is not used; nor is it
true that this specializes the thesis's argument — the printed proof is dead
even here).  The obstruction analyzed in `PROVING-LOG.md` — the *mirrored
compression* `ω(c* · c)` with `c` not known in advance — vanishes when `ℬ`
is commutative: `ω(r z r) = ω(r² z) ≤ ω(z)` for contractions `r`, because
positive commuting elements have positive products.  Concretely: given `x`
with `N := ‖x‖ > 0` and a `δ`-approximant `d₀ ∈ D`, set `b₀ := ⟪d₀, d₀⟫ ∈ A`
and renormalize with `f_N(t) := N/√(max t N²)`:

  `d := f_N(b₀) • d₀`.

Then `⟪d,d⟫ = cfc (t ↦ f_N(t)²t) b₀` has norm `≤ N²`, so `‖d‖ ≤ ‖x‖`, and
`d ∈ D` since `cfc f_N b₀` lies in the closed C*-subalgebra `A ∋ b₀`
(`cfc_mem`).  The weak defect splits as

  `ω⟪w, x−d⟫ = ω⟪w, x−d₀⟫ + ω(q ⟪w, d₀⟫)`,   `q := 1 − f_N(b₀) ≥ 0`,

whose first term is `≤ ‖w‖_ω δ` by Cauchy–Schwarz, and whose second is
`≤ ‖w‖_ω ‖q•d₀‖_ω` with `‖q•d₀‖_ω² = ω(q b₀ q)`.  The one identity doing the
real work is the *single-variable* factorization (avoiding the two-variable
functional calculus `(√s−√t)² ≤ |s−t|` of the original sketch):

  `(1−f_N(t))² t = m_N(t)·(t − N²)`,   `m_N(t) := (√(max t N²) − N)/(√(max t N²) + N) ∈ [0,1]`,

so `q b₀ q = r(b₀ − N²)` with `r := m_N(b₀)`; since `⟪x,x⟫ ≤ N²·1` and `r ≥ 0`
commute, `ω(q b₀ q) ≤ ω(r(b₀ − ⟪x,x⟫))`, and `b₀ − ⟪x,x⟫ =
⟪d₀−x, d₀⟫ + ⟪x, d₀−x⟫` is weak-small by Cauchy–Schwarz — both times on the
*good* slot, which is what commutativity buys: `r` moves to the other side of
the inner product at no cost.  Hence `ω(q b₀ q) ≤ δ² + 2‖x‖_ω δ`, and `δ`
chosen from `η`, `‖w‖_ω`, `‖x‖_ω` alone closes the weak statement; the full
(finitely-many-seminorms) statement follows by `kaplansky_hilbmod_of_weak`.

This isolates exactly what the open general case is missing: a substitute
for the commutation `ω(q z q) = ω(q² z)` on a one-sided module. -/

section Commutative

/-- `√(max t N²)`, the cut-off square root used by the renormalizer. -/
private noncomputable def rsq (N t : ℝ) : ℝ := Real.sqrt (max t (N ^ 2))

/-- The one-shot renormalizer `f_N(t) = N/√(max t N²)`. -/
private noncomputable def renf (N t : ℝ) : ℝ := N / rsq N t

/-- The extraction factor `m_N(t) = (√(max t N²) − N)/(√(max t N²) + N)`. -/
private noncomputable def extf (N t : ℝ) : ℝ := (rsq N t - N) / (rsq N t + N)

variable {N : ℝ}

private theorem rsq_pos (hN : 0 < N) (t : ℝ) : 0 < rsq N t :=
  Real.sqrt_pos.mpr (lt_of_lt_of_le (pow_pos hN 2) (le_max_right t (N ^ 2)))

private theorem le_rsq (hN : 0 < N) (t : ℝ) : N ≤ rsq N t := by
  rw [rsq]
  calc N = Real.sqrt (N ^ 2) := (Real.sqrt_sq hN.le).symm
    _ ≤ Real.sqrt (max t (N ^ 2)) := Real.sqrt_le_sqrt (le_max_right t (N ^ 2))

private theorem rsq_sq (t : ℝ) : rsq N t ^ 2 = max t (N ^ 2) :=
  Real.sq_sqrt (le_trans (sq_nonneg N) (le_max_right t (N ^ 2)))

private theorem continuous_rsq (N : ℝ) : Continuous (rsq N) :=
  Real.continuous_sqrt.comp (continuous_id.max continuous_const)

private theorem continuous_renf (hN : 0 < N) : Continuous (renf N) :=
  continuous_const.div (continuous_rsq N) fun t => (rsq_pos hN t).ne'

private theorem continuous_extf (hN : 0 < N) : Continuous (extf N) :=
  ((continuous_rsq N).sub continuous_const).div
    ((continuous_rsq N).add continuous_const)
    fun t => ne_of_gt (by have := rsq_pos hN t; linarith)

private theorem renf_nonneg (hN : 0 < N) (t : ℝ) : 0 ≤ renf N t :=
  div_nonneg hN.le (rsq_pos hN t).le

private theorem renf_le_one (hN : 0 < N) (t : ℝ) : renf N t ≤ 1 :=
  div_le_one_of_le₀ (le_rsq hN t) (rsq_pos hN t).le

private theorem extf_nonneg (hN : 0 < N) (t : ℝ) : 0 ≤ extf N t :=
  div_nonneg (sub_nonneg.mpr (le_rsq hN t))
    (by have := rsq_pos hN t; linarith)

private theorem extf_le_one (hN : 0 < N) (t : ℝ) : extf N t ≤ 1 := by
  have h := rsq_pos hN t
  exact div_le_one_of_le₀ (by linarith) (by linarith)

/-- The renormalized square stays under the cap: `f_N(t)·t·f_N(t) ≤ N²`. -/
private theorem renf_conj_le (hN : 0 < N) (t : ℝ) :
    renf N t * t * renf N t ≤ N ^ 2 := by
  rw [renf]
  set s := rsq N t with hsdef
  have hs : 0 < s := rsq_pos hN t
  have hts : t ≤ s ^ 2 := by rw [hsdef, rsq_sq]; exact le_max_left _ _
  have key : N / s * t * (N / s) = N ^ 2 * t / s ^ 2 := by
    field_simp [hs.ne']
  rw [key, div_le_iff₀ (pow_pos hs 2)]
  exact mul_le_mul_of_nonneg_left hts (sq_nonneg N)

/-- The key single-variable factorization: `(1−f_N(t))² t = m_N(t)(t − N²)`. -/
private theorem renf_extf_key (hN : 0 < N) (t : ℝ) :
    (1 - renf N t) * t * (1 - renf N t) = extf N t * (t - N ^ 2) := by
  rcases le_total t (N ^ 2) with h | h
  · have hst : rsq N t = N := by rw [rsq, max_eq_right h, Real.sqrt_sq hN.le]
    rw [renf, extf, hst, div_self hN.ne']
    simp
  · rw [renf, extf]
    set s := rsq N t with hsdef
    have hs : 0 < s := rsq_pos hN t
    have hst : s ^ 2 = t := by rw [hsdef, rsq_sq]; exact max_eq_left h
    have hsN : 0 < s + N := by linarith
    rw [← hst]
    field_simp [hs.ne', hsN.ne']
    ring

/-- `cfc (f·id·g) b = cfc f b * b * cfc g b` for `b ≥ 0`. -/
private theorem cfc_mul_id_mul {f g : ℝ → ℝ} {b : ℬ} (hb : 0 ≤ b)
    (hf : Continuous f) (hg : Continuous g) :
    cfc (fun t => f t * t * g t) b = cfc f b * b * cfc g b := by
  have h1 : cfc (fun t : ℝ => f t * t) b = cfc f b * b := by
    have h := cfc_mul (a := b) f (fun t : ℝ => t)
      hf.continuousOn continuous_id.continuousOn
    rwa [cfc_id' ℝ b hb.isSelfAdjoint] at h
  have h2 := cfc_mul (a := b) (fun t : ℝ => f t * t) g
    (hf.mul continuous_id).continuousOn hg.continuousOn
  rw [h2, h1]

/-- The mirror vanishes in a commutative algebra: `ω(r z r) ≤ ω(z)` for a
selfadjoint contraction `r` (in the form `r² ≤ 1`) against positive `z`,
since `r z r = r² z ≤ z` — the inequality that is *not* available in the
noncommutative case (see the section comment). -/
private theorem np_re_conj_le (hcomm : ∀ a b : ℬ, a * b = b * a)
    (ω : NPFunctional ℬ) {r z : ℬ} (hz : 0 ≤ z) (hr1 : 0 ≤ 1 - r * r) :
    (ω (r * z * r)).re ≤ (ω z).re := by
  have h1 : r * z * r = r * r * z := by rw [mul_assoc, hcomm z r, ← mul_assoc]
  have h2 : (1 - r * r) * z = z - r * r * z := by rw [sub_mul, one_mul]
  have h3 : 0 ≤ z - r * r * z := h2 ▸ Commute.mul_nonneg hr1 hz (hcomm _ _)
  rw [h1]
  exact np_re_mono' ω (sub_nonneg.mp h3)

/-- Contractions do not increase the ultranorm seminorms of a Hilbert module
over a commutative C*-algebra. -/
private theorem unSeminorm_smul_le (hcomm : ∀ a b : ℬ, a * b = b * a)
    (ω : NPFunctional ℬ) {r : ℬ} (hrsa : IsSelfAdjoint r)
    (hr1 : 0 ≤ 1 - r * r) (z : X) :
    unSeminorm ω (inner ℬ) (r • z) ≤ unSeminorm ω (inner ℬ) z := by
  have h1 : inner ℬ (r • z) (r • z) = r * inner ℬ z z * r := by
    rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
      hrsa.star_eq]
  rw [unSeminorm, unSeminorm, h1]
  exact Real.sqrt_le_sqrt
    (np_re_conj_le hcomm ω CStarModule.inner_self_nonneg hr1)

/-- **158II, commutative case — the weak statement**: for commutative `ℬ`
the weak bounded approximation required by `kaplansky_hilbmod_of_weak` holds,
by the one-shot renormalization described in the section comment. -/
private theorem kaplansky_weak_of_commutative
    (hcomm : ∀ a b : ℬ, a * b = b * a)
    (A : StarSubalgebra ℂ ℬ) (hA : IsClosed (A : Set ℬ))
    (D : Set X) (hD0 : (0 : X) ∈ D)
    (hDsmul : ∀ a ∈ A, ∀ d ∈ D, a • d ∈ D)
    (hDinner : ∀ d ∈ D, inner ℬ d d ∈ A)
    (hdense : UnDense (inner ℬ) D) (x : X)
    (ω : NPFunctional ℬ) (w : X) (η : ℝ) (hη : 0 < η) :
    ∃ d ∈ D, ‖d‖ ≤ ‖x‖ ∧ ‖ω (inner ℬ w (x - d))‖ ≤ η := by
  by_cases hx0 : x = 0
  · refine ⟨0, hD0, by simp, ?_⟩
    rw [hx0, sub_zero, CStarModule.inner_zero_right,
      show ω (0 : ℬ) = 0 from map_zero ω.toPositiveLinearMap]
    simpa using hη.le
  have hN : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set N := ‖x‖ with hNdef
  set P := unSeminorm ω (inner ℬ) w
  set Q := unSeminorm ω (inner ℬ) x with hQ
  have hP0 : 0 ≤ P := unSeminorm_nonneg ω _ w
  have hQ0 : 0 ≤ Q := unSeminorm_nonneg ω _ x
  have hP1 : (0 : ℝ) < 2 * (P + 1) := by linarith
  have hQ1 : (0 : ℝ) < 1 + 2 * Q := by linarith
  have hP2 : (0 : ℝ) < 4 * (P + 1) ^ 2 * (1 + 2 * Q) :=
    mul_pos (mul_pos (by norm_num) (pow_pos (by linarith) 2)) hQ1
  set δ := min 1 (min (η / (2 * (P + 1)))
    (η ^ 2 / (4 * (P + 1) ^ 2 * (1 + 2 * Q))))
  have hδ : 0 < δ :=
    lt_min one_pos (lt_min (div_pos hη hP1) (div_pos (pow_pos hη 2) hP2))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδA : δ ≤ η / (2 * (P + 1)) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδB : δ ≤ η ^ 2 / (4 * (P + 1) ^ 2 * (1 + 2 * Q)) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  -- the raw approximant `d₀` and its renormalization `d = f_N(b₀) • d₀`
  obtain ⟨d₀, hd₀D, hd₀⟩ := hdense x 1 (fun _ => ω) δ hδ
  have hxd₀ : unSeminorm ω (inner ℬ) (x - d₀) ≤ δ := hd₀ 0
  have hd₀x : unSeminorm ω (inner ℬ) (d₀ - x) ≤ δ := by
    rw [← neg_sub x d₀]
    exact le_trans (le_of_eq (unSeminorm_neg' ω (cstarBInner ℬ X) (x - d₀))) hxd₀
  set b₀ := inner ℬ d₀ d₀ with hb₀def
  have hb₀A : b₀ ∈ A := hDinner d₀ hd₀D
  have hb₀ : 0 ≤ b₀ := CStarModule.inner_self_nonneg
  have hspec : ∀ t ∈ spectrum ℝ b₀, 0 ≤ t := fun t ht =>
    spectrum_nonneg_of_nonneg hb₀ ht
  set c := cfc (renf N) b₀ with hcdef
  have hc0 : 0 ≤ c := cfc_nonneg fun t _ => renf_nonneg hN t
  have hcsa : IsSelfAdjoint c := hc0.isSelfAdjoint
  have hcA : c ∈ A := by
    rw [hcdef]
    exact cfc_mem (𝕜' := ℂ) (s := A) (hs := hA) (f := renf N) (has := hb₀A)
  refine ⟨c • d₀, hDsmul c hcA d₀ hd₀D, ?_, ?_⟩
  · -- ‖c • d₀‖ ≤ ‖x‖ = N: the renormalizer caps the norm
    have hdd : inner ℬ (c • d₀) (c • d₀)
        = cfc (fun t => renf N t * t * renf N t) b₀ := by
      rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
        hcsa.star_eq, ← hb₀def, hcdef,
        ← cfc_mul_id_mul hb₀ (continuous_renf hN) (continuous_renf hN)]
    have h2 : ‖inner ℬ (c • d₀) (c • d₀)‖ ≤ N ^ 2 := by
      rw [hdd]
      refine norm_cfc_le (by positivity) fun t ht => ?_
      have ht0 : 0 ≤ t := hspec t ht
      have hf0 := renf_nonneg hN t
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hf0 ht0) hf0)]
      exact renf_conj_le hN t
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ)]
    calc Real.sqrt ‖inner ℬ (c • d₀) (c • d₀)‖
        ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt h2
      _ = N := Real.sqrt_sq hN.le
  · -- the weak defect
    have haddω : ∀ a b : ℬ, ω (a + b) = ω a + ω b := fun a b =>
      map_add ω.toPositiveLinearMap a b
    have hsubω : ∀ a b : ℬ, ω (a - b) = ω a - ω b := fun a b =>
      map_sub ω.toPositiveLinearMap a b
    -- the trimming factor `q = 1 − c` and the extraction factor `r`
    set q := cfc (fun t => 1 - renf N t) b₀ with hqdef
    have hq0 : 0 ≤ q := cfc_nonneg fun t _ => sub_nonneg.mpr (renf_le_one hN t)
    have hqsa : IsSelfAdjoint q := hq0.isSelfAdjoint
    have hq_eq : q = 1 - c := by
      rw [hqdef, hcdef, cfc_sub _ _ b₀ continuous_const.continuousOn
        (continuous_renf hN).continuousOn, cfc_const_one ℝ b₀ hb₀.isSelfAdjoint]
    set r := cfc (extf N) b₀ with hrdef
    have hr0 : 0 ≤ r := cfc_nonneg fun t _ => extf_nonneg hN t
    have hrsa : IsSelfAdjoint r := hr0.isSelfAdjoint
    have hr1 : 0 ≤ 1 - r * r := by
      rw [hrdef, ← cfc_mul _ _ b₀ (continuous_extf hN).continuousOn
          (continuous_extf hN).continuousOn,
        ← cfc_const_one ℝ b₀ hb₀.isSelfAdjoint,
        ← cfc_sub (fun _ : ℝ => (1 : ℝ)) (fun t : ℝ => extf N t * extf N t) b₀
          continuous_const.continuousOn
          (show Continuous fun t : ℝ => extf N t * extf N t from
            (continuous_extf hN).mul (continuous_extf hN)).continuousOn]
      exact cfc_nonneg fun t _ => by
        nlinarith [extf_nonneg hN t, extf_le_one hN t]
    -- the splitting `ω⟪w, x−d⟫ = ω⟪w, x−d₀⟫ + ω(q ⟪w, d₀⟫)`
    have hsplit : inner ℬ w (x - c • d₀)
        = inner ℬ w (x - d₀) + q * inner ℬ w d₀ := by
      rw [CStarModule.inner_sub_right, CStarModule.inner_sub_right,
        CStarModule.inner_op_smul_right, hq_eq]
      noncomm_ring
    have hT0 : ‖ω (inner ℬ w (x - d₀))‖ ≤ P * δ :=
      le_trans (unSeminorm_inner_le ω (cstarBInner ℬ X) w (x - d₀))
        (mul_le_mul_of_nonneg_left hxd₀ hP0)
    have hT1 : ‖ω (q * inner ℬ w d₀)‖
        ≤ P * unSeminorm ω (inner ℬ) (q • d₀) := by
      rw [show q * inner ℬ w d₀ = inner ℬ w (q • d₀) from
        (CStarModule.inner_op_smul_right).symm]
      exact unSeminorm_inner_le ω (cstarBInner ℬ X) w (q • d₀)
    -- the central estimate: `‖q•d₀‖_ω² = ω(q b₀ q) ≤ δ² + 2Qδ`
    have hqbq : q * b₀ * star q = r * (b₀ - algebraMap ℝ ℬ (N ^ 2)) := by
      rw [hqsa.star_eq, hqdef,
        ← cfc_mul_id_mul hb₀
          (show Continuous fun t : ℝ => 1 - renf N t from
            continuous_const.sub (continuous_renf hN))
          (show Continuous fun t : ℝ => 1 - renf N t from
            continuous_const.sub (continuous_renf hN)),
        cfc_congr fun t _ => renf_extf_key hN t,
        cfc_mul (extf N) (fun t : ℝ => t - N ^ 2) b₀
          (continuous_extf hN).continuousOn
          (continuous_id.sub continuous_const).continuousOn,
        cfc_sub (fun t : ℝ => t) (fun _ : ℝ => N ^ 2) b₀
          continuous_id.continuousOn continuous_const.continuousOn,
        cfc_id' ℝ b₀ hb₀.isSelfAdjoint, cfc_const (N ^ 2) b₀ hb₀.isSelfAdjoint,
        ← hrdef]
    have ha0 : (0 : ℬ) ≤ inner ℬ x x := CStarModule.inner_self_nonneg
    have hnorm_a : ‖inner ℬ x x‖ = N ^ 2 := by
      rw [← Real.sq_sqrt (norm_nonneg (inner ℬ x x)),
        ← CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ), hNdef]
    have haN : inner ℬ x x ≤ algebraMap ℝ ℬ (N ^ 2) := by
      have h := IsSelfAdjoint.le_algebraMap_norm_self ha0.isSelfAdjoint
      rwa [hnorm_a] at h
    have hpos2 : 0 ≤ r * (algebraMap ℝ ℬ (N ^ 2) - inner ℬ x x) :=
      Commute.mul_nonneg hr0 (sub_nonneg.mpr haN) (hcomm _ _)
    have hqd₀ : inner ℬ (q • d₀) (q • d₀) = q * b₀ * star q := by
      rw [CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
        ← hb₀def]
    have hrba : r * (b₀ - inner ℬ x x)
        = inner ℬ (d₀ - x) (r • d₀) + inner ℬ x (r • (d₀ - x)) := by
      rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_right,
        CStarModule.inner_sub_left, CStarModule.inner_sub_right, ← hb₀def]
      noncomm_ring
    have hrd₀ : unSeminorm ω (inner ℬ) (r • d₀) ≤ Q + δ := by
      refine le_trans (unSeminorm_smul_le hcomm ω hrsa hr1 d₀) ?_
      have h3 := unSeminorm_add_le ω (cstarBInner ℬ X) (d₀ - x) x
      rw [sub_add_cancel] at h3
      exact le_trans h3 (le_trans (add_le_add hd₀x hQ.symm.le)
        (le_of_eq (add_comm δ Q)))
    have hcs1 : ‖ω (inner ℬ (d₀ - x) (r • d₀))‖ ≤ δ * (Q + δ) :=
      le_trans (unSeminorm_inner_le ω (cstarBInner ℬ X) (d₀ - x) (r • d₀))
        (mul_le_mul hd₀x hrd₀ (unSeminorm_nonneg _ _ _) hδ.le)
    have hcs2 : ‖ω (inner ℬ x (r • (d₀ - x)))‖ ≤ Q * δ :=
      le_trans (unSeminorm_inner_le ω (cstarBInner ℬ X) x (r • (d₀ - x)))
        (mul_le_mul hQ.symm.le
          (le_trans (unSeminorm_smul_le hcomm ω hrsa hr1 (d₀ - x)) hd₀x)
          (unSeminorm_nonneg _ _ _) hQ0)
    have hmass : (ω (inner ℬ (q • d₀) (q • d₀))).re ≤ δ ^ 2 + 2 * Q * δ := by
      rw [hqd₀, hqbq, show r * (b₀ - algebraMap ℝ ℬ (N ^ 2))
          = r * (b₀ - inner ℬ x x)
            - r * (algebraMap ℝ ℬ (N ^ 2) - inner ℬ x x) by noncomm_ring,
        hsubω, Complex.sub_re]
      have h5 : 0 ≤ (ω (r * (algebraMap ℝ ℬ (N ^ 2) - inner ℬ x x))).re :=
        np_re_nonneg' ω hpos2
      have h6 : (ω (r * (b₀ - inner ℬ x x))).re ≤ δ * (Q + δ) + Q * δ := by
        rw [hrba, haddω, Complex.add_re]
        have h9 : (ω (inner ℬ (d₀ - x) (r • d₀))).re ≤ δ * (Q + δ) :=
          le_trans (Complex.re_le_norm _) hcs1
        have h10 : (ω (inner ℬ x (r • (d₀ - x)))).re ≤ Q * δ :=
          le_trans (Complex.re_le_norm _) hcs2
        linarith
      nlinarith [h5, h6]
    have hpq : unSeminorm ω (inner ℬ) (q • d₀)
        ≤ Real.sqrt (δ ^ 2 + 2 * Q * δ) := by
      rw [unSeminorm]
      exact Real.sqrt_le_sqrt hmass
    -- final arithmetic: `P(δ + √(δ² + 2Qδ)) ≤ η` by the choice of `δ`
    have hδ2 : δ * (2 * (P + 1)) ≤ η := (le_div_iff₀ hP1).mp hδA
    have hPδ : P * δ ≤ η / 2 := by nlinarith [hδ.le]
    have hsqrt : Real.sqrt (δ ^ 2 + 2 * Q * δ) ≤ η / (2 * (P + 1)) := by
      have h7 : δ ^ 2 + 2 * Q * δ ≤ δ * (1 + 2 * Q) := by nlinarith
      have h9 : δ ≤ η ^ 2 / (4 * (P + 1) ^ 2) / (1 + 2 * Q) := by
        rw [div_div]; exact hδB
      have h10 : δ * (1 + 2 * Q) ≤ η ^ 2 / (4 * (P + 1) ^ 2) :=
        (le_div_iff₀ hQ1).mp h9
      have h8 : η ^ 2 / (4 * (P + 1) ^ 2) = (η / (2 * (P + 1))) ^ 2 := by
        rw [div_pow]; congr 1; ring
      calc Real.sqrt (δ ^ 2 + 2 * Q * δ)
          ≤ Real.sqrt ((η / (2 * (P + 1))) ^ 2) :=
            Real.sqrt_le_sqrt (le_trans h7 (h8 ▸ h10))
        _ = η / (2 * (P + 1)) := Real.sqrt_sq (div_nonneg hη.le hP1.le)
    have hPsq : P * Real.sqrt (δ ^ 2 + 2 * Q * δ) ≤ η / 2 := by
      have h11 : P * Real.sqrt (δ ^ 2 + 2 * Q * δ) ≤ P * (η / (2 * (P + 1))) :=
        mul_le_mul_of_nonneg_left hsqrt hP0
      have hTmul : η / (2 * (P + 1)) * (2 * (P + 1)) = η :=
        div_mul_cancel₀ η hP1.ne'
      have hT0' : 0 ≤ η / (2 * (P + 1)) := div_nonneg hη.le hP1.le
      nlinarith [h11, hTmul, hT0']
    calc ‖ω (inner ℬ w (x - c • d₀))‖
        = ‖ω (inner ℬ w (x - d₀)) + ω (q * inner ℬ w d₀)‖ := by
          rw [hsplit, haddω]
      _ ≤ ‖ω (inner ℬ w (x - d₀))‖ + ‖ω (q * inner ℬ w d₀)‖ := norm_add_le _ _
      _ ≤ P * δ + P * Real.sqrt (δ ^ 2 + 2 * Q * δ) :=
          add_le_add hT0 (le_trans hT1 (mul_le_mul_of_nonneg_left hpq hP0))
      _ ≤ η / 2 + η / 2 := add_le_add hPδ hPsq
      _ = η := by ring

/-- **158II, the commutative case** (`kaplansky-hilbmod`, dils.tex:4135,
restricted): the Kaplansky density theorem for Hilbert C*-modules over a
*commutative* von Neumann algebra `ℬ` — the hypotheses of
`kaplansky_hilbmod` plus commutativity, with the same conclusion.

*Class 2 — different proof*: the thesis's route (158V) is false even in
general and unnecessary here; instead the weak bounded approximation is
established one-shot by `kaplansky_weak_of_commutative` (where the mirror
obstruction of `PROVING-LOG.md` vanishes) and upgraded by
`kaplansky_hilbmod_of_weak`.  The statement keeps 158II's exact hypotheses
(`[VonNeumannAlgebra ℬ]` and `[CompleteSpace X]` are in fact not needed by
this proof).  The general (noncommutative) case remains open — see
`kaplansky_hilbmod`. -/
theorem kaplansky_hilbmod_of_commutative [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (hcomm : ∀ a b : ℬ, a * b = b * a)
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
  kaplansky_hilbmod_of_weak A D hDadd hDsmul x fun ω w η hη =>
    kaplansky_weak_of_commutative hcomm A hA D hD0 hDsmul hDinner hdense x ω w η hη

end Commutative

end Kaplansky

end Theses.B.Dils
