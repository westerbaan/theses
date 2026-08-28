/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 4082–4279.

  parsec 1580:  the Kaplansky density theorem for Hilbert C*-modules

**158Ia** and **158II** are proved (158II through the linking algebra, at the
end of the file; it uses **150II** `dils_completion`, which is now itself
proved, so 158II is unconditional); the four **158V** estimates are `sorry`
(they are *false*, see below).  The thesis's route to 158II is therefore
dead; the proof here runs the **linking algebra** `ℬᵃ(X ⊕ ℬ)` and thesis A's
**74IV** `kaplansky` instead — see the section comment before
`kaplansky_hilbmod_of_selfDual`, which is the self-dual case and is
axiom-clean.  Two earlier partial results are kept, both still of interest:
`kaplansky_hilbmod_of_weak` (158II reduces, by a Mazur-style variational
argument, to *weak* bounded approximation) and
`kaplansky_hilbmod_of_commutative` (the commutative case, proved through the
weak form and needing neither the linking algebra nor 150II).  Following the conventions of
`HilbertModules.lean`, ultrastrong/ultranorm approximation is expressed
through the seminorms `unSeminorm ω B` (with `B = mulInner ℬ` for the
ultrastrong uniformity on `ℬ` itself); "there is a net `x_α → x` ultranorm
with `‖x_α‖ ≤ ‖x‖`" is rendered as bounded approximability within every
entourage (finitely many seminorms, `ε > 0`), which yields the canonical
approximating net.
-/
import Theses.A.VN.Completeness
import Theses.B.Dils.HilbertModules
import Theses.B.Dils.SelfDualCompletion

open scoped ComplexOrder CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u v w

namespace Theses.B.Dils

/-! **158I** (dils.tex:4092) and **158Ib** (dils.tex:4137): introduction and
discussion — nothing to formalize. -/

section Kaplansky

variable {ℬ : Type u}
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- The `mulInner` ultranorm seminorm is the *mirrored* ultrastrong seminorm:
`‖x‖_ω = ω(x x*)^½ = ‖x*‖_ω^{ultrastrong}` (**146VIII**). -/
theorem unSeminorm_mulInner_eq (ω : NPFunctional ℬ) (x : ℬ) :
    unSeminorm ω (mulInner ℬ) x = omegaNorm ℬ ω (star x) := by
  rw [omegaNorm, unSeminorm, star_star]; rfl

/-- **158Ia** (dils.tex:4129, Kaplansky density theorem), the variant of
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

/-! **158II** (`kaplansky-hilbmod`, dils.tex:4143, Kaplansky density theorem
for Hilbert C*-modules) is stated and **proved** at the end of this file, as
`kaplansky_hilbmod`, because its proof (through the linking algebra) needs
the whole of the file: the np-functional helpers of the `WeakToStrong`
section and the linking-algebra development after it.  Its self-dual case is
`kaplansky_hilbmod_of_selfDual`. -/

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
`⟨y₀, yₙ - y₀⟩(1+⟨yₙ,yₙ⟩)⁻¹ = |e₁⟩⟨eₙ| - ⅓|e₁⟩⟨w|` has `ω₀`-value `-1/3`
— written in the *thesis's* argument order, which under this file's mirrored
`⟨a,b⟩ = b a*` is `inner (yₙ - y₀) y₀`.  Read literally in the mirrored order
the same display has `ω₀`-value `0`.
(The left-hand half *is* fine: `⟨y_α-y, y_α(1+⟨y_α,y_α⟩)⁻¹⟩` is Cauchy–Schwarz
against a vector of norm `≤ 1`, and the resolvent bounds below are exactly
what that argument needs.)  The four `sorry`s are therefore *not* closable;
see `PROVING-LOG.md` and `ERRATA.md`.

**The whole computation was re-checked in exact rational arithmetic on
2026-08-28** and all nine recorded values reproduce: `scripts/kaplansky_witness.py`,
which is a 3×3 matrix calculation over `ℚ` because everything above lives in the
span of `e₁, e₂, eₙ`.  It is *not* a Lean proof — `docs/DECISIONS.md` §1.3 still
records the falsity as disproved-on-paper — but it is reproducible, and it
caught the two convention slips flagged in this block: read on the side the
prose writes them, two of the six values come out `0`.

Two further defects fell out of the same computation.  (i) `kaplansky-splitting`
is off by a factor `4`: with `h y = 2(1+⟨y,y⟩)⁻¹·y` — the scalar on the **left**,
which is the side this file's mirrored `⟨a,b⟩ = b a*` forces; on the right the
value is `0`, not `1/9` — the left-hand side carries the square of that `2`, and
indeed `⟨h y - h yₙ, h y - h yₙ⟩ = 4(A₁+A₁'+A₂+A₂')`
(`1/9 = 4·(-1/12 - 1/18 + 0 + 1/6)`).  (ii) *Ours*, repaired in session 94:
`kaplansky_hilbmod_A₂` and `kaplansky_hilbmod_A₂'` below had been transcribed
with the arguments of their inner products in the thesis's order rather than
the mirrored one, which made them neither the thesis's terms nor the stars of
those terms.

All four terms are transcribed here as `star ∘ mirror`: the *full* mirror of a
thesis product `ABC` of inner-product expressions is the reversed product
`C'B'A'` of the mirrored factors, and its star is `A' star(B') C'` — the
thesis's factor order back again, with each inner product's two arguments
swapped relative to a bare mirror.  That is what `A₁` and `A₁'` do (there
every inner product is a self-adjoint `⟨y,y⟩` or `⟨y_α,y_α⟩`, so only the
factor order is visible), and `A₂`, `A₂'` now do it too: the thesis's
`⟨y_α − y, y_α⟩` is `inner ℬ (y i) (y i - y₀)` and its `⟨y − y_α, y⟩` is
`inner ℬ y₀ (y₀ - y i)`.  Since `star` is ultraweakly continuous and the
claim is convergence to `0`, `star ∘ mirror` transcribes the thesis's claim
faithfully.  All four remain false, and remain `sorry`. -/

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

/-- **158V**.1 (dils.tex:4201, the term `A₁` of `kaplansky-splitting`): if
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
        inv1p (inner ℬ y₀ y₀) * inner ℬ (y i) (y i - y₀)
          * inv1p (inner ℬ (y i) (y i))) l 0 :=
  sorry

/-- **158V**.4 (dils.tex:4202, the term `A₂'` of `kaplansky-splitting`): if
`y_α → y` ultranorm, then

  `A₂' = (1+⟨y_α,y_α⟩)⁻¹ ⟨y - y_α, y⟩ (1+⟨y,y⟩)⁻¹ → 0`

ultraweakly; as for `A₂` (dils.tex:4273). -/
private theorem kaplansky_hilbmod_A₂' [VonNeumannAlgebra ℬ] [CompleteSpace X]
    (y : ι → X) (y₀ : X) (hy : UnTendsto (inner ℬ) y l y₀) :
    UWTendsto (fun i =>
        inv1p (inner ℬ (y i) (y i)) * inner ℬ y₀ (y₀ - y i)
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

/-- **158II, the commutative case** (`kaplansky-hilbmod`, dils.tex:4143,
restricted): the Kaplansky density theorem for Hilbert C*-modules over a
*commutative* von Neumann algebra `ℬ` — the hypotheses of
`kaplansky_hilbmod` plus commutativity, with the same conclusion.

*Class 2 — different proof*: the thesis's route (158V) is false even in
general and unnecessary here; instead the weak bounded approximation is
established one-shot by `kaplansky_weak_of_commutative` (where the mirror
obstruction of `PROVING-LOG.md` vanishes) and upgraded by
`kaplansky_hilbmod_of_weak`.  The statement keeps 158II's exact hypotheses
(`[VonNeumannAlgebra ℬ]` and `[CompleteSpace X]` are in fact not needed by
this proof).

The commutativity hypothesis is *not* 158II's: 158II is unconditional, and it
is proved unconditionally below as `kaplansky_hilbmod` (session 56, and
unconditional since session 61) by the linking-algebra route.  This
declaration is kept as an independent second route to the commutative case,
not because the general case is open. -/
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

/-! ### 158II through the linking algebra

The route that works.  Form the **linking module** `Lk = X ⊕ ℬ` (Mathlib's
`C⋆ᵐᵒᵈ(ℬ, X × ℬ)`) and the von Neumann algebra `ℬᵃ(Lk)` of its adjointable
operators (**152X** `ba_vonNeumannAlgebra`, which needs `Lk` self dual — hence
the `SelfDual ℬ X` hypothesis below, the one place the self-dual completion
**150II** would be needed for the general case).  Inside it,

  `cor z = |z ⊕ 0⟩⟨0 ⊕ 1|`   ("`[[0,z],[0,0]]`")

is a linear isometry of `X` into the corner with

  `(cor z)* (cor z) = ι⟨z,z⟩`,  `ι b = |0 ⊕ b⟩⟨0 ⊕ 1|`   ("`[[0,0],[0,b]]`"),

so the ultrastrong seminorms of `cor z` are *exactly* the ultranorm seminorms
of `z` — no mirrored (`ω(bb*)`) quantity appears, which is what kills every
route through 158V.  (The *self-adjoint* `[[0,z],[z*,0]]` of the classical
proof would reintroduce the mirror, through the `|z⟩⟨z|` corner; it is not
needed, because thesis A's **74IV** `kaplansky` already handles a
non-self-adjoint element.)  `D` sits inside the closed ∗-subalgebra
`lkSub` of operators preserving `N = cl(D) ⊕ 𝒜` — this is exactly what the
hypotheses `⟨D,D⟩ ⊆ 𝒜` (through polarization) and `𝒜·D ⊆ D` say — and 74IV
compresses back into `cl(D)`, from where `kaplansky_hilbmod_of_closure`
rescales into `D` itself.  Note that `𝒜` is *not* assumed ultrastrongly dense
in `ℬ` anywhere. -/

section Linking



/-- The linking module `X ⊕ ℬ`. -/
private abbrev Lk (ℬ : Type u) (X : Type v) [CStarAlgebra ℬ] [PartialOrder ℬ]
    [StarOrderedRing ℬ] [NormedAddCommGroup X] [Module ℂ X] [SMul ℬ X]
    [CStarModule ℬ X] : Type (max u v) := C⋆ᵐᵒᵈ(ℬ, X × ℬ)

/-- `x ∈ X` as a vector of the linking module. -/
private def lkX (z : X) : Lk ℬ X := (z, 0)
/-- `b ∈ ℬ` as a vector of the linking module. -/
private def lkB (b : ℬ) : Lk ℬ X := (0, b)

@[simp] private theorem lkX_fst (z : X) : (lkX (ℬ := ℬ) z).1 = z := rfl
@[simp] private theorem lkX_snd (z : X) : (lkX (ℬ := ℬ) z).2 = 0 := rfl
@[simp] private theorem lkB_fst (b : ℬ) : (lkB (X := X) b).1 = 0 := rfl
@[simp] private theorem lkB_snd (b : ℬ) : (lkB (X := X) b).2 = b := rfl

private theorem lk_inner (v w : Lk ℬ X) :
    (inner ℬ v w : ℬ) = inner ℬ v.1 w.1 + inner ℬ v.2 w.2 := rfl

private theorem inner_lkX (z z' : X) : (inner ℬ (lkX (ℬ := ℬ) z) (lkX (ℬ := ℬ) z') : ℬ)
    = inner ℬ z z' := by
  rw [lk_inner]; simp

private theorem inner_lkB (b b' : ℬ) : (inner ℬ (lkB (X := X) b) (lkB (X := X) b') : ℬ)
    = b' * star b := by
  rw [lk_inner]; simp; rfl

private theorem norm_lkX (z : X) : ‖lkX (ℬ := ℬ) z‖ = ‖z‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ), inner_lkX,
    ← CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ)]

private theorem norm_lkB (b : ℬ) : ‖lkB (X := X) b‖ = ‖b‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ), inner_lkB,
    CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ) (x := b)]
  rfl

private theorem norm_lkB_one_le : ‖lkB (X := X) (1 : ℬ)‖ ≤ 1 := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ), inner_lkB, star_one, mul_one]
  rw [show (1:ℝ) = Real.sqrt 1 by simp]
  refine Real.sqrt_le_sqrt ?_
  rcases subsingleton_or_nontrivial ℬ with _ | _
  · rw [Subsingleton.elim (1:ℬ) 0, norm_zero]; exact zero_le_one
  · exact le_of_eq CStarRing.norm_one

/-- `|v⟩⟨w| : u ↦ ⟨w,u⟩ • v` on the linking module (a private copy of 159II
`mketbra`, which lives downstream in `SelfDual.lean`). -/
private noncomputable def mkb (v w : Lk ℬ X) : Lk ℬ X →L[ℂ] Lk ℬ X :=
  LinearMap.mkContinuous
    { toFun := fun u => inner ℬ w u • v
      map_add' := fun z z' => by rw [CStarModule.inner_add_right, op_add_smul]
      map_smul' := fun c z => by
        rw [CStarModule.inner_smul_right_complex, op_smul_complex_smul,
          RingHom.id_apply] }
    (‖w‖ * ‖v‖) fun u => by
      calc ‖(inner ℬ w u : ℬ) • v‖ ≤ ‖(inner ℬ w u : ℬ)‖ * ‖v‖ := norm_op_smul_le _ _
        _ ≤ ‖w‖ * ‖u‖ * ‖v‖ :=
            mul_le_mul_of_nonneg_right (CStarModule.norm_inner_le (Lk ℬ X)) (norm_nonneg _)
        _ = ‖w‖ * ‖v‖ * ‖u‖ := by ring

@[simp] private theorem mkb_apply (v w u : Lk ℬ X) : mkb v w u = inner ℬ w u • v := rfl

private theorem mkb_adjointTo (v w : Lk ℬ X) :
    ModuleAdjointTo ℬ (⇑(mkb v w) : Lk ℬ X → Lk ℬ X) ⇑(mkb w v) := by
  intro z u
  rw [mkb_apply, mkb_apply, CStarModule.inner_op_smul_left,
    CStarModule.inner_op_smul_right, CStarModule.star_inner]

private theorem mkb_adjointable (v w : Lk ℬ X) :
    ModuleAdjointable ℬ (⇑(mkb v w) : Lk ℬ X → Lk ℬ X) := ⟨_, mkb_adjointTo v w⟩

private theorem mkb_comp (v w v' w' : Lk ℬ X) :
    (mkb v w).comp (mkb v' w') = mkb ((inner ℬ w v' : ℬ) • v) w' := by
  ext u
  change (inner ℬ w ((inner ℬ w' u : ℬ) • v') : ℬ) • v
    = (inner ℬ w' u : ℬ) • ((inner ℬ w v' : ℬ) • v)
  rw [CStarModule.inner_op_smul_right, op_mul_smul]

private theorem op_smul_sub (a : ℬ) (v v' : Lk ℬ X) : a • (v - v') = a • v - a • v' :=
  eq_sub_of_add_eq (by rw [← op_smul_add, sub_add_cancel])

private theorem mkb_add_left (v v' w : Lk ℬ X) : mkb (v + v') w = mkb v w + mkb v' w := by
  ext u
  show (inner ℬ w u : ℬ) • (v + v') = mkb v w u + mkb v' w u
  rw [op_smul_add]; rfl

private theorem mkb_smul_left (c : ℂ) (v w : Lk ℬ X) : mkb (c • v) w = c • mkb v w := by
  ext u
  exact op_smul_comm_complex c (inner ℬ w u) v

private theorem mkb_sub_left (v v' w : Lk ℬ X) : mkb (v - v') w = mkb v w - mkb v' w := by
  ext u
  show (inner ℬ w u : ℬ) • (v - v') = mkb v w u - mkb v' w u
  rw [op_smul_sub]; rfl

private theorem smul_lkX (b : ℬ) (z : X) : b • lkX (ℬ := ℬ) z = lkX (b • z) :=
  Prod.ext rfl (by show b • (0:ℬ) = 0; rw [smul_eq_mul, mul_zero])

private theorem smul_lkB (b c : ℬ) : b • lkB (X := X) c = lkB (b * c) :=
  Prod.ext (by show b • (0:X) = 0; rw [op_smul_zero]) rfl

variable [CompleteSpace X]

omit [CompleteSpace X] in
theorem norm_mkb_le (v w : Lk ℬ X) : ‖mkb v w‖ ≤ ‖w‖ * ‖v‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The corner embedding `x ↦ [[0,x],[0,0]]` of `X` into the linking algebra. -/
private noncomputable def cor (z : X) : Ba ℬ (Lk ℬ X) :=
  ⟨mkb (lkX z) (lkB (1:ℬ)), mkb_adjointable _ _⟩

/-- The diagonal embedding of `ℬ` into the linking algebra. -/
private noncomputable def iota (b : ℬ) : Ba ℬ (Lk ℬ X) :=
  ⟨mkb (lkB b) (lkB (1:ℬ)), mkb_adjointable _ _⟩

omit [CompleteSpace X] in
private theorem cor_apply (z : X) (u : Lk ℬ X) : (cor z).1 u = lkX (u.2 • z) := by
  show (inner ℬ (lkB (X := X) (1:ℬ)) u : ℬ) • lkX z = _
  rw [lk_inner]
  simp only [lkB_fst, lkB_snd, CStarModule.inner_zero_left, zero_add]
  show (u.2 * star (1:ℬ)) • lkX (ℬ := ℬ) z = _
  rw [star_one, mul_one, smul_lkX]

omit [CompleteSpace X] in
private theorem iota_apply (b : ℬ) (u : Lk ℬ X) : (iota (X := X) b).1 u = lkB (u.2 * b) := by
  show (inner ℬ (lkB (X := X) (1:ℬ)) u : ℬ) • lkB b = _
  rw [lk_inner]
  simp only [lkB_fst, lkB_snd, CStarModule.inner_zero_left, zero_add]
  show (u.2 * star (1:ℬ)) • lkB (X := X) b = _
  rw [star_one, mul_one, smul_lkB]

private theorem star_cor_coe (z : X) :
    (star (cor (ℬ := ℬ) z)).1 = mkb (lkB (X := X) (1:ℬ)) (lkX z) :=
  DFunLike.coe_injective
    (moduleAdjointTo_unique _ _ _ (baSubalgebra_star_spec (cor z)) (mkb_adjointTo _ _))

omit [CompleteSpace X] in
private theorem lkX_sub (z z' : X) : lkX (ℬ := ℬ) (z - z') = lkX z - lkX z' :=
  Prod.ext rfl (sub_zero (0:ℬ)).symm

private theorem cor_sub (z z' : X) : cor (ℬ := ℬ) (z - z') = cor z - cor z' :=
  Subtype.ext (by
    show mkb (lkX (z - z')) (lkB (X := X) (1:ℬ)) = _
    rw [lkX_sub, mkb_sub_left]; rfl)

private theorem star_cor_mul_cor (z : X) :
    star (cor (ℬ := ℬ) z) * cor z = iota (inner ℬ z z) := by
  refine Subtype.ext ?_
  show (star (cor (ℬ := ℬ) z)).1.comp
      (mkb (lkX z) (lkB (X := X) (1:ℬ))) = mkb (lkB (inner ℬ z z)) (lkB (X := X) (1:ℬ))
  rw [star_cor_coe, mkb_comp, inner_lkX, smul_lkB, mul_one]

private theorem norm_cor_le (z : X) : ‖cor (ℬ := ℬ) z‖ ≤ ‖z‖ := by
  have h : ‖cor (ℬ := ℬ) z‖ = ‖mkb (lkX (ℬ := ℬ) z) (lkB (X := X) (1:ℬ))‖ := rfl
  rw [h]
  calc ‖mkb (lkX (ℬ := ℬ) z) (lkB (X := X) (1:ℬ))‖ ≤ ‖lkB (X := X) (1:ℬ)‖ * ‖lkX (ℬ := ℬ) z‖ :=
        norm_mkb_le _ _
    _ ≤ 1 * ‖z‖ := by
        rw [norm_lkX]
        exact mul_le_mul_of_nonneg_right norm_lkB_one_le (norm_nonneg _)
    _ = ‖z‖ := one_mul _

-- PART 2 (appended to Link.lean before `end Linking`)

/-- `X` sits in the linking module ℂ-linearly. -/
private noncomputable def lkXLM : X →ₗ[ℂ] Lk ℬ X where
  toFun := lkX
  map_add' z z' := Prod.ext rfl (add_zero (0:ℬ)).symm
  map_smul' c z := Prod.ext rfl (smul_zero c).symm

/-- `ℬ` sits in the linking module ℂ-linearly. -/
private noncomputable def lkBLM : ℬ →ₗ[ℂ] Lk ℬ X where
  toFun := lkB
  map_add' b b' := Prod.ext (add_zero (0:X)).symm rfl
  map_smul' c b := Prod.ext (smul_zero c).symm rfl

omit [CompleteSpace X] in
private theorem lk_decomp (v : Lk ℬ X) : v = lkX v.1 + lkB v.2 :=
  Prod.ext (add_zero v.1).symm (zero_add v.2).symm

/-- **141III** (direct sums): the linking module `X ⊕ ℬ` is self dual when
`X` is. -/
private theorem selfDual_lk (hX : SelfDual ℬ X) : SelfDual ℬ (Lk ℬ X) := by
  intro τ hmod hbdd
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨t₁, ht₁⟩ := hX (τ.comp lkXLM)
    (fun b z => by
      show τ (lkX (b • z)) = b * τ (lkX z)
      rw [← smul_lkX]; exact hmod b (lkX z))
    ⟨C, fun z => by
      show ‖τ (lkX z)‖ ≤ C * ‖z‖
      rw [← norm_lkX (ℬ := ℬ) z]; exact hC _⟩
  obtain ⟨t₂, ht₂⟩ := selfDual_self ℬ (τ.comp lkBLM)
    (fun b c => by
      show τ (lkB (X := X) (b • c)) = b * τ (lkB c)
      rw [smul_eq_mul, ← smul_lkB]; exact hmod b (lkB c))
    ⟨C, fun c => by
      show ‖τ (lkB (X := X) c)‖ ≤ C * ‖c‖
      rw [← norm_lkB (X := X) c]; exact hC _⟩
  refine ⟨lkX t₁ + lkB t₂, fun v => ?_⟩
  have h1 : (inner ℬ (lkX (ℬ := ℬ) t₁ + lkB t₂) v : ℬ)
      = inner ℬ t₁ v.1 + inner ℬ t₂ v.2 := by
    rw [lk_inner]
    show (inner ℬ (t₁ + 0) v.1 : ℬ) + inner ℬ (0 + t₂) v.2 = _
    rw [add_zero, zero_add]
  rw [h1, ← ht₁ v.1, ← ht₂ v.2]
  show τ v = τ (lkX v.1) + τ (lkB v.2)
  rw [← map_add, ← lk_decomp]

-- PART 3: iota is normal

private theorem inner_iota (b : ℬ) (u : Lk ℬ X) :
    (inner ℬ u ((iota (X := X) b).1 u) : ℬ) = u.2 * b * star u.2 := by
  rw [iota_apply, lk_inner]
  simp only [lkB_fst, lkB_snd, CStarModule.inner_zero_right, zero_add]
  rfl

private theorem iota_sub (b b' : ℬ) : iota (X := X) (b - b') = iota b - iota b' :=
  Subtype.ext (by
    show mkb (lkB (X := X) (b - b')) (lkB (X := X) (1:ℬ)) = _
    rw [show lkB (X := X) (b - b') = lkB b - lkB b' from Prod.ext (sub_zero (0:X)).symm rfl,
      mkb_sub_left]
    rfl)

omit [CompleteSpace X] in
private theorem lkB_add (b b' : ℬ) : lkB (X := X) (b + b') = lkB b + lkB b' :=
  Prod.ext (add_zero (0:X)).symm rfl

omit [CompleteSpace X] in
private theorem lkB_smul (c : ℂ) (b : ℬ) : lkB (X := X) (c • b) = c • lkB b :=
  Prod.ext (smul_zero c).symm rfl

private theorem iota_add (b b' : ℬ) : iota (X := X) (b + b') = iota b + iota b' :=
  Subtype.ext (by
    show mkb (lkB (X := X) (b + b')) (lkB (X := X) (1:ℬ)) = _
    rw [lkB_add, mkb_add_left]; rfl)

private theorem iota_smul (c : ℂ) (b : ℬ) : iota (X := X) (c • b) = c • iota b :=
  Subtype.ext (by
    show mkb (lkB (X := X) (c • b)) (lkB (X := X) (1:ℬ)) = _
    rw [lkB_smul, mkb_smul_left]; rfl)

private theorem iota_mono {b b' : ℬ} (h : b ≤ b') : iota (X := X) b ≤ iota b' := by
  rw [← sub_nonneg, ← iota_sub]
  refine (ba_nonneg_iff _).mpr fun u => ?_
  rw [inner_iota]
  have := star_left_conjugate_nonneg (sub_nonneg.mpr h) (star u.2)
  rwa [star_star] at this

private theorem star_iota (b : ℬ) : star (iota (X := X) b) = iota (star b) := by
  refine Subtype.ext ?_
  have h : (star (iota (X := X) b)).1 = mkb (lkB (X := X) (1:ℬ)) (lkB b) :=
    DFunLike.coe_injective
      (moduleAdjointTo_unique _ _ _ (baSubalgebra_star_spec (iota (X := X) b))
        (mkb_adjointTo _ _))
  rw [h]
  ext u
  show (inner ℬ (lkB (X := X) b) u : ℬ) • lkB (X := X) (1:ℬ)
    = (inner ℬ (lkB (X := X) (1:ℬ)) u : ℬ) • lkB (X := X) (star b)
  rw [lk_inner, lk_inner]
  simp only [lkB_fst, lkB_snd, CStarModule.inner_zero_left, zero_add]
  show (u.2 * star b) • lkB (X := X) (1:ℬ) = (u.2 * star (1:ℬ)) • lkB (X := X) (star b)
  rw [star_one, mul_one, smul_lkB, smul_lkB, mul_one]

private theorem isSelfAdjoint_iota {b : ℬ} (hb : IsSelfAdjoint b) :
    IsSelfAdjoint (iota (X := X) b) := by
  change star (iota (X := X) b) = _
  rw [star_iota, hb.star_eq]

/-- `ι` on self-adjoint elements. -/
private noncomputable def iotaSA (d : selfAdjoint ℬ) : selfAdjoint (Ba ℬ (Lk ℬ X)) :=
  ⟨iota (X := X) d, isSelfAdjoint_iota (X := X) d.2⟩

private theorem iotaSA_mono : Monotone (iotaSA (ℬ := ℬ) (X := X)) := fun _ _ h =>
  Subtype.coe_le_coe.mp (iota_mono (Subtype.coe_le_coe.mpr h))

variable [VonNeumannAlgebra ℬ]

private theorem iotaSA_isLUB {D : Set (selfAdjoint ℬ)} {s : selfAdjoint ℬ}
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) :
    IsLUB (iotaSA (ℬ := ℬ) (X := X) '' D) (iotaSA s) := by
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact iotaSA_mono (hlub.1 hd)
  · intro T hT
    rw [← Subtype.coe_le_coe, ← sub_nonneg]
    refine (ba_nonneg_iff _).mpr fun u => ?_
    have hsub : ((T : Ba ℬ (Lk ℬ X)) - (iotaSA (ℬ := ℬ) (X := X) s : Ba ℬ (Lk ℬ X))).1 u
        = (T : Ba ℬ (Lk ℬ X)).1 u - (iota (X := X) (s : ℬ)).1 u := rfl
    rw [hsub, CStarModule.inner_sub_right, sub_nonneg, inner_iota]
    refine np_orderSeparating _ _ ?_ ?_ fun ω => ?_
    · exact s.2.conjugate u.2
    · exact ba_inner_isSelfAdjoint u (T : Ba ℬ (Lk ℬ X)) T.2
    · have hkey := (conjNP (star u.2) ω).preservesDirSups' D s hne hdir hlub
      have hub : ∀ y ∈ (fun d : selfAdjoint ℬ =>
          (conjNP (star (u.2 : ℬ)) ω) (d : ℬ)) '' D,
          y ≤ ω (inner ℬ u ((T : Ba ℬ (Lk ℬ X)).1 u)) := by
        rintro _ ⟨d, hd, rfl⟩
        have h1 : (iotaSA (ℬ := ℬ) (X := X) d : Ba ℬ (Lk ℬ X)) ≤ (T : Ba ℬ (Lk ℬ X)) :=
          Subtype.coe_le_coe.mpr (hT ⟨d, hd, rfl⟩)
        have h2 := ba_inner_mono u h1
        rw [show ((iotaSA (ℬ := ℬ) (X := X) d : Ba ℬ (Lk ℬ X)) : Ba ℬ (Lk ℬ X))
            = iota (X := X) (d : ℬ) from rfl, inner_iota] at h2
        have h3 := np_mono ω h2
        show ω (star (star (u.2 : ℬ)) * (d : ℬ) * star (u.2 : ℬ)) ≤ _
        rw [star_star]
        exact h3
      have h := hkey.2 hub
      have h' : ω (star (star (u.2 : ℬ)) * (s : ℬ) * star (u.2 : ℬ))
          ≤ ω (inner ℬ u ((T : Ba ℬ (Lk ℬ X)).1 u)) := h
      rwa [star_star] at h'

/-- The linking algebra's np-functionals restrict to np-functionals of `ℬ`
along the diagonal embedding `ι`.  This is the step that needs `ι` to be
*normal*, i.e. the normality of `b ↦ c b c*`. -/
private noncomputable def iotaNP [CompleteSpace X] (hY : SelfDual ℬ (Lk ℬ X))
    (φ : NPFunctional (Ba ℬ (Lk ℬ X))) : NPFunctional ℬ where
  toPositiveLinearMap :=
    { toFun := fun b => φ (iota (X := X) b)
      map_add' := fun b b' => by
        rw [iota_add]
        exact map_add φ.toPositiveLinearMap _ _
      map_smul' := fun c b => by
        rw [iota_smul]
        exact map_smul φ.toPositiveLinearMap _ _
      monotone' := fun b b' h => φ.toPositiveLinearMap.monotone (iota_mono h) }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hdir' : DirectedOn (· ≤ ·) (iotaSA (ℬ := ℬ) (X := X) '' D) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
      obtain ⟨w, hw, hxw, hzw⟩ := hdir x hx z hz
      exact ⟨iotaSA w, ⟨w, hw, rfl⟩, iotaSA_mono hxw, iotaSA_mono hzw⟩
    have hkey := φ.preservesDirSups' (iotaSA (ℬ := ℬ) (X := X) '' D) (iotaSA s)
      (hne.image _) hdir' (iotaSA_isLUB hne hdir hlub)
    rw [← Set.image_comp] at hkey
    exact hkey

-- PART 4: the linking subalgebra

omit [VonNeumannAlgebra ℬ] in
private theorem op_smul_sub' {W : Type*} [NormedAddCommGroup W] [Module ℂ W] [SMul ℬ W]
    [CStarModule ℬ W] (a : ℬ) (v v' : W) : a • (v - v') = a • v - a • v' :=
  eq_sub_of_add_eq (by rw [← op_smul_add, sub_add_cancel])

section Sub

omit [CompleteSpace X] [VonNeumannAlgebra ℬ] in
private theorem lipschitz_lk_fst : LipschitzWith 1 (fun v : Lk ℬ X => v.1) :=
  LipschitzWith.of_dist_le_mul fun v w => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact (le_max_left _ _).trans (WithCStarModule.max_le_prod_norm (v - w))

omit [CompleteSpace X] [VonNeumannAlgebra ℬ] in
private theorem lipschitz_lk_snd : LipschitzWith 1 (fun v : Lk ℬ X => v.2) :=
  LipschitzWith.of_dist_le_mul fun v w => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact (le_max_right _ _).trans (WithCStarModule.max_le_prod_norm (v - w))

omit [VonNeumannAlgebra ℬ] in
private theorem continuous_ba_apply (v : Lk ℬ X) :
    Continuous (fun T : Ba ℬ (Lk ℬ X) => T.1 v) :=
  (ContinuousLinearMap.apply ℂ (Lk ℬ X) v).continuous.comp continuous_subtype_val

/-- The `∗`-subalgebra of the linking algebra of the operators that preserve
a ℂ-subspace `N ⊆ X ⊕ ℬ` together with their adjoints. -/
private noncomputable def lkSub (N : Set (Lk ℬ X)) (hadd : ∀ v ∈ N, ∀ w ∈ N, v + w ∈ N)
    (hsmul : ∀ (c : ℂ), ∀ v ∈ N, c • v ∈ N) :
    StarSubalgebra ℂ (Ba ℬ (Lk ℬ X)) where
  carrier := {T | ∀ v ∈ N, T.1 v ∈ N ∧ (star T).1 v ∈ N}
  mul_mem' := by
    intro S T hS hT v hv
    refine ⟨(hS _ (hT v hv).1).1, ?_⟩
    rw [star_mul]
    exact (hT _ (hS v hv).2).2
  add_mem' := by
    intro S T hS hT v hv
    refine ⟨hadd _ (hS v hv).1 _ (hT v hv).1, ?_⟩
    rw [star_add]
    exact hadd _ (hS v hv).2 _ (hT v hv).2
  algebraMap_mem' := by
    intro c v hv
    refine ⟨hsmul c v hv, ?_⟩
    rw [← algebraMap_star_comm]
    exact hsmul _ v hv
  star_mem' := by
    intro T hT v hv
    exact ⟨(hT v hv).2, by rw [star_star]; exact (hT v hv).1⟩

omit [VonNeumannAlgebra ℬ] in
private theorem mem_lkSub {N : Set (Lk ℬ X)} {hadd hsmul} {T : Ba ℬ (Lk ℬ X)} :
    T ∈ lkSub N hadd hsmul ↔ ∀ v ∈ N, T.1 v ∈ N ∧ (star T).1 v ∈ N := Iff.rfl

private theorem isClosed_lkSub {N : Set (Lk ℬ X)} (hadd hsmul) (hN : IsClosed N) :
    IsClosed ((lkSub N hadd hsmul : StarSubalgebra ℂ (Ba ℬ (Lk ℬ X))) :
      Set (Ba ℬ (Lk ℬ X))) := by
  have hset : ((lkSub N hadd hsmul : StarSubalgebra ℂ (Ba ℬ (Lk ℬ X))) :
        Set (Ba ℬ (Lk ℬ X)))
      = ⋂ v ∈ N, ((fun T : Ba ℬ (Lk ℬ X) => T.1 v) ⁻¹' N)
          ∩ ((fun T : Ba ℬ (Lk ℬ X) => (star T).1 v) ⁻¹' N) := by
    ext T
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
    exact Iff.rfl
  rw [hset]
  refine isClosed_iInter fun v => isClosed_iInter fun _ => ?_
  exact (hN.preimage (continuous_ba_apply v)).inter
    (hN.preimage ((continuous_ba_apply v).comp continuous_star))

end Sub

-- PART 5: 158II for self-dual modules

section Main

omit [CompleteSpace X] [VonNeumannAlgebra ℬ] in
/-- From approximation inside the *norm closure* of `D` to approximation
inside `D` itself: norm-approximate, then rescale into the ball. -/
theorem kaplansky_hilbmod_of_closure
    (A : StarSubalgebra ℂ ℬ) (D : Set X)
    (hDsmul : ∀ a ∈ A, ∀ d ∈ D, a • d ∈ D) (x : X)
    (h : ∀ (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (ε : ℝ), 0 < ε →
      ∃ z ∈ closure D, ‖z‖ ≤ ‖x‖ ∧
        ∀ i, unSeminorm (ωs i) (inner ℬ) (x - z) ≤ ε) :
    ∀ (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (ε : ℝ), 0 < ε →
      ∃ d ∈ D, ‖d‖ ≤ ‖x‖ ∧
        ∀ i, unSeminorm (ωs i) (inner ℬ) (x - d) ≤ ε := by
  intro n ωs ε hε
  have hDc : ∀ (c : ℂ), ∀ d ∈ D, c • d ∈ D := by
    intro c d hd
    have h1 : (c • (1 : ℬ)) ∈ A := by
      rw [← Algebra.algebraMap_eq_smul_one]; exact A.algebraMap_mem c
    have h2 := hDsmul _ h1 d hd
    rwa [smul_one_smul' c d] at h2
  set ω := npSum n ωs with hω
  set M : ℝ := Real.sqrt (ω 1).re with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  set δ : ℝ := (ε / 2) / (2 * (M + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hMδ : 2 * M * δ ≤ ε / 2 := by
    have h1 : (0:ℝ) < 2 * (M + 1) := by positivity
    have h2 : 2 * M / (2 * (M + 1)) ≤ 1 := by rw [div_le_one h1]; linarith
    have h3 : 2 * M * δ = (2 * M / (2 * (M + 1))) * (ε / 2) := by rw [hδ]; field_simp
    rw [h3]
    nlinarith [hε.le, h2, hM0]
  obtain ⟨z, hz, hzn, hzε⟩ := h 1 (fun _ => ω) (ε / 2) (by positivity)
  have hzω : unSeminorm ω (inner ℬ) (x - z) ≤ ε / 2 := hzε 0
  obtain ⟨d', hd', hd'δ⟩ := Metric.mem_closure_iff.mp hz δ hδ0
  set γ : ℝ := ‖x‖ with hγ
  have hγ0 : 0 ≤ γ := norm_nonneg _
  have hpos : 0 < γ + δ := by linarith
  set t : ℝ := γ / (γ + δ) with ht
  have ht0 : 0 ≤ t := by positivity
  have htγ : t * (γ + δ) = γ := by rw [ht]; field_simp
  have hzd' : ‖z - d'‖ ≤ δ := by
    rw [← dist_eq_norm]; exact hd'δ.le
  have hd'n : ‖d'‖ ≤ γ + δ := by
    have h1 : ‖d'‖ ≤ ‖z‖ + ‖d' - z‖ := by
      simpa using norm_add_le z (d' - z)
    have h2 : ‖d' - z‖ = ‖z - d'‖ := norm_sub_rev _ _
    linarith
  refine ⟨((t : ℝ) : ℂ) • d', hDc _ _ hd', ?_, fun i => ?_⟩
  · rw [norm_smul_complex (ℬ := ℬ), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0]
    nlinarith [hd'n, ht0]
  · refine le_trans (unSeminorm_le_npSum n ωs i (cstarBInner ℬ X) _) ?_
    have hsplit : x - ((t : ℝ) : ℂ) • d'
        = (x - z) + ((z - d') + (d' - ((t : ℝ) : ℂ) • d')) := by abel
    have htri : unSeminorm ω (cstarBInner ℬ X).inner (x - ((t : ℝ) : ℂ) • d')
        ≤ unSeminorm ω (cstarBInner ℬ X).inner (x - z)
          + (unSeminorm ω (cstarBInner ℬ X).inner (z - d')
            + unSeminorm ω (cstarBInner ℬ X).inner
                (d' - ((t : ℝ) : ℂ) • d')) := by
      rw [hsplit]
      have ha := unSeminorm_add_le ω (cstarBInner ℬ X) (x - z)
        ((z - d') + (d' - ((t : ℝ) : ℂ) • d'))
      have hb := unSeminorm_add_le ω (cstarBInner ℬ X) (z - d')
        (d' - ((t : ℝ) : ℂ) • d')
      linarith
    have h2 : unSeminorm ω (cstarBInner ℬ X).inner (z - d') ≤ M * δ :=
      le_trans (unSeminorm_le_norm' ω (z - d'))
        (mul_le_mul_of_nonneg_left hzd' hM0)
    have hrest : ‖d' - ((t : ℝ) : ℂ) • d'‖ ≤ δ := by
      have he : d' - ((t : ℝ) : ℂ) • d' = ((1 - t : ℝ) : ℂ) • d' := by
        push_cast; module
      rw [he, norm_smul_complex (ℬ := ℬ), Complex.norm_real, Real.norm_eq_abs]
      have ht1 : t ≤ 1 := by rw [ht, div_le_one hpos]; linarith
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
      nlinarith [hd'n, norm_nonneg d']
    have h3 : unSeminorm ω (cstarBInner ℬ X).inner (d' - ((t : ℝ) : ℂ) • d')
        ≤ M * δ :=
      le_trans (unSeminorm_le_norm' ω _) (mul_le_mul_of_nonneg_left hrest hM0)
    have h1 : unSeminorm ω (cstarBInner ℬ X).inner (x - z) ≤ ε / 2 := hzω
    have : M * δ + M * δ = 2 * M * δ := by ring
    linarith

/-- **158II** (`kaplansky-hilbmod`, dils.tex:4143) for a **self-dual**
Hilbert module, proved through the linking algebra.  Self-duality is *not* a
hypothesis of 158II: this is the intermediate step of the replacement proof
(the linking algebra `ℬᵃ(X ⊕ ℬ)` needs `X ⊕ ℬ` self dual, **152X**), and the
point itself, without it, is `kaplansky_hilbmod` below, which reduces to this
one along the self-dual completion. -/
theorem kaplansky_hilbmod_of_selfDual (hX : SelfDual ℬ X)
    (A : StarSubalgebra ℂ ℬ) (hA : IsClosed (A : Set ℬ)) (D : Set X)
    (hD0 : (0 : X) ∈ D)
    (hDadd : ∀ d ∈ D, ∀ d' ∈ D, d + d' ∈ D)
    (hDsmul : ∀ a ∈ A, ∀ d ∈ D, a • d ∈ D)
    (hDinner : ∀ d ∈ D, inner ℬ d d ∈ A)
    (hdense : UnDense (inner ℬ) D) (x : X) :
    ∀ (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (ε : ℝ), 0 < ε →
      ∃ d ∈ D, ‖d‖ ≤ ‖x‖ ∧
        ∀ i, unSeminorm (ωs i) (inner ℬ) (x - d) ≤ ε := by
  refine kaplansky_hilbmod_of_closure A D hDsmul x ?_
  intro n ωs ε hε
  -- `D` is a ℂ-subspace, through `A ∋ c·1`
  have hDc : ∀ (c : ℂ), ∀ d ∈ D, c • d ∈ D := by
    intro c d hd
    have h1 : (c • (1 : ℬ)) ∈ A := by
      rw [← Algebra.algebraMap_eq_smul_one]; exact A.algebraMap_mem c
    have h2 := hDsmul _ h1 d hd
    rwa [smul_one_smul' c d] at h2
  -- polarization: `⟪D,D⟫ ⊆ A`
  have hsum : ∀ e ∈ D, ∀ e' ∈ D,
      (inner ℬ e e' : ℬ) + inner ℬ e' e ∈ A := by
    intro e he e' he'
    have hid : (inner ℬ e e' : ℬ) + inner ℬ e' e
        = inner ℬ (e + e') (e + e') - inner ℬ e e - inner ℬ e' e' := by
      rw [CStarModule.inner_add_left, CStarModule.inner_add_right,
        CStarModule.inner_add_right]
      abel
    rw [hid]
    exact sub_mem (sub_mem (hDinner _ (hDadd _ he _ he')) (hDinner _ he))
      (hDinner _ he')
  have hpol : ∀ e ∈ D, ∀ e' ∈ D, (inner ℬ e e' : ℬ) ∈ A := by
    intro e he e' he'
    have h1 := hsum e he e' he'
    have h2 := hsum e he (Complex.I • e') (hDc Complex.I e' he')
    have hI : (inner ℬ e (Complex.I • e') : ℬ) + inner ℬ (Complex.I • e') e
        = Complex.I • ((inner ℬ e e' : ℬ) - inner ℬ e' e) := by
      rw [CStarModule.inner_smul_right_complex, CStarModule.inner_smul_left_complex,
        show (star Complex.I : ℂ) = -Complex.I by simp, neg_smul, smul_sub,
        ← sub_eq_add_neg]
    rw [hI] at h2
    have h3 : (inner ℬ e e' : ℬ) - inner ℬ e' e ∈ A := by
      have h4 := A.smul_mem h2 (-Complex.I)
      rwa [smul_smul, show (-Complex.I) * Complex.I = 1 by
        simp [Complex.I_mul_I], one_smul] at h4
    have h5 := A.smul_mem (add_mem h1 h3) (1/2 : ℂ)
    rwa [show (1/2 : ℂ) • (((inner ℬ e e' : ℬ) + inner ℬ e' e)
        + ((inner ℬ e e' : ℬ) - inner ℬ e' e)) = inner ℬ e e' by module] at h5
  -- closure facts
  have hclA : ∀ u ∈ closure D, ∀ w ∈ closure D, u + w ∈ closure D := by
    intro u hu w hw
    have hmaps : Set.MapsTo (fun p : X × X => p.1 + p.2) (D ×ˢ D) D :=
      fun p hp => hDadd _ hp.1 _ hp.2
    have h2 := hmaps.closure (continuous_fst.add continuous_snd)
    rw [closure_prod_eq] at h2
    exact h2 (Set.mk_mem_prod hu hw)
  have hclC : ∀ (c : ℂ), ∀ u ∈ closure D, c • u ∈ closure D := by
    intro c u hu
    have hcont : Continuous (fun z : X => c • z) := by
      refine LipschitzWith.continuous (K := ‖c‖₊)
        (LipschitzWith.of_dist_le_mul fun z z' => ?_)
      rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul_complex (ℬ := ℬ)]
      simp
    exact (Set.MapsTo.closure (fun z hz => hDc c z hz) hcont) hu
  have hclB : ∀ a ∈ A, ∀ u ∈ closure D, a • u ∈ closure D := by
    intro a ha u hu
    have hcont : Continuous (fun z : X => a • z) := by
      refine LipschitzWith.continuous (K := ‖a‖₊)
        (LipschitzWith.of_dist_le_mul fun z z' => ?_)
      rw [dist_eq_norm, dist_eq_norm, ← op_smul_sub']
      simpa using norm_op_smul_le a (z - z')
    exact (Set.MapsTo.closure (fun z hz => hDsmul a ha z hz) hcont) hu
  have hclI : ∀ d ∈ D, ∀ u ∈ closure D, (inner ℬ d u : ℬ) ∈ A := by
    intro d hd u hu
    have hcont : Continuous (fun z : X => (inner ℬ d z : ℬ)) := by
      refine LipschitzWith.continuous (K := ‖d‖₊)
        (LipschitzWith.of_dist_le_mul fun z z' => ?_)
      rw [dist_eq_norm, dist_eq_norm, ← CStarModule.inner_sub_right, coe_nnnorm]
      exact CStarModule.norm_inner_le X
    have hmaps : Set.MapsTo (fun z : X => (inner ℬ d z : ℬ)) D (A : Set ℬ) :=
      fun z hz => hpol d hd z hz
    have := hmaps.closure hcont hu
    rwa [hA.closure_eq] at this
  -- the ℂ-subspace `N = cl(D) ⊕ A` of the linking module
  set N : Set (Lk ℬ X) := {v | v.1 ∈ closure D ∧ v.2 ∈ A} with hN
  have hNadd : ∀ v ∈ N, ∀ w ∈ N, v + w ∈ N := fun v hv w hw =>
    ⟨hclA _ hv.1 _ hw.1, add_mem hv.2 hw.2⟩
  have hNsmul : ∀ (c : ℂ), ∀ v ∈ N, c • v ∈ N := fun c v hv =>
    ⟨hclC c _ hv.1, A.smul_mem hv.2 c⟩
  have hNclosed : IsClosed N :=
    (isClosed_closure.preimage lipschitz_lk_fst.continuous).inter
      (hA.preimage lipschitz_lk_snd.continuous)
  have hone : lkB (X := X) (1 : ℬ) ∈ N :=
    ⟨subset_closure hD0, A.one_mem⟩
  -- the linking subalgebra
  set S := lkSub N hNadd hNsmul with hS
  have hScl : IsClosed ((S : StarSubalgebra ℂ (Ba ℬ (Lk ℬ X))) :
      Set (Ba ℬ (Lk ℬ X))) := isClosed_lkSub _ _ hNclosed
  have hcor : ∀ d ∈ D, cor (ℬ := ℬ) d ∈ S := by
    intro d hd v hv
    constructor
    · rw [cor_apply]
      exact ⟨hclB _ hv.2 _ (subset_closure hd), A.zero_mem⟩
    · rw [star_cor_coe]
      show (inner ℬ (lkX (ℬ := ℬ) d) v : ℬ) • lkB (X := X) (1 : ℬ) ∈ N
      rw [lk_inner]
      simp only [lkX_fst, lkX_snd, CStarModule.inner_zero_left, add_zero]
      rw [smul_lkB, mul_one]
      exact ⟨subset_closure hD0, hclI d hd _ hv.1⟩
  -- the linking algebra is a von Neumann algebra
  have hY : SelfDual ℬ (Lk ℬ X) := selfDual_lk hX
  haveI : VonNeumannAlgebra (Ba ℬ (Lk ℬ X)) := ba_vonNeumannAlgebra hY
  -- `cor x` lies in the ultrastrong closure of `S`
  have hmem : cor (ℬ := ℬ) x ∈
      @closure _ (ultrastrong _) ((S : StarSubalgebra ℂ (Ba ℬ (Lk ℬ X))) :
        Set (Ba ℬ (Lk ℬ X))) := by
    let _ : TopologicalSpace (Ba ℬ (Lk ℬ X)) := ultrastrong _
    rw [mem_closure_iff]
    intro o ho hmemo
    obtain ⟨φ, δ, hδ, hsub⟩ := exists_ultrastrong_ball_of_isOpen ho _ hmemo
    obtain ⟨d, hd, hdd⟩ :=
      hdense x 1 (fun _ => iotaNP hY φ) (δ / 2) (by positivity)
    refine ⟨cor d, hsub ?_, hcor d hd⟩
    have h1 : cor (ℬ := ℬ) d - cor x = cor (d - x) := (cor_sub d x).symm
    have h2 : omegaNorm (Ba ℬ (Lk ℬ X)) φ (cor (ℬ := ℬ) (d - x))
        = unSeminorm (iotaNP hY φ) (inner ℬ) (d - x) := by
      rw [omegaNorm, star_cor_mul_cor]
      rfl
    have h3 := hdd 0
    rw [show x - d = -(d - x) by abel] at h3
    rw [show unSeminorm (iotaNP hY φ) (inner ℬ) (-(d - x))
        = unSeminorm (iotaNP hY φ) (cstarBInner ℬ X).inner (-(d - x)) from rfl,
      unSeminorm_neg'] at h3
    show omegaNorm (Ba ℬ (Lk ℬ X)) φ (cor (ℬ := ℬ) d - cor x) < δ
    rw [h1, h2]
    calc unSeminorm (iotaNP hY φ) (inner ℬ) (d - x) ≤ δ / 2 := h3
      _ < δ := by linarith
  -- classical Kaplansky in the linking algebra
  obtain ⟨ι, l, hl, a, ha, hlim⟩ :=
    Theses.A.VN.kaplansky (S : StarSubalgebra ℂ (Ba ℬ (Lk ℬ X))) hScl
      (cor (ℬ := ℬ) x) hmem
  haveI := hl
  have hev : ∀ᶠ j in l, ∀ i,
      omegaNorm (Ba ℬ (Lk ℬ X)) (baVecNP hY (lkB (X := X) (1 : ℬ)) (ωs i))
        (a j - cor (ℬ := ℬ) x) ≤ ε := by
    refine Filter.eventually_all.mpr fun i => ?_
    have hi := (usTendsto_iff a l (cor (ℬ := ℬ) x)).mp hlim
      (baVecNP hY (lkB (X := X) (1 : ℬ)) (ωs i))
    filter_upwards [Metric.tendsto_nhds.mp hi ε hε] with j hj
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (omegaNorm_nonneg _ _)] at hj
    exact hj.le
  obtain ⟨j, hj⟩ := hev.exists
  -- compress to the corner
  set w : Lk ℬ X := (a j).1 (lkB (X := X) (1 : ℬ)) with hw
  have hwN : w ∈ N := ((ha j).1 _ hone).1
  refine ⟨w.1, hwN.1, ?_, fun i => ?_⟩
  · calc ‖w.1‖ ≤ ‖w‖ := (le_max_left _ _).trans (WithCStarModule.max_le_prod_norm w)
      _ ≤ ‖a j‖ * ‖lkB (X := X) (1 : ℬ)‖ := by
          exact (a j).1.le_opNorm _
      _ ≤ ‖cor (ℬ := ℬ) x‖ * 1 := by
          refine mul_le_mul (ha j).2 norm_lkB_one_le (norm_nonneg _) (norm_nonneg _)
      _ ≤ ‖x‖ := by rw [mul_one]; exact norm_cor_le x
  · -- the corner seminorm is dominated by the ultrastrong seminorm
    have hTv : ((a j) - cor (ℬ := ℬ) x).1 (lkB (X := X) (1 : ℬ)) = w - lkX x := by
      show (a j).1 (lkB (X := X) (1:ℬ)) - (cor (ℬ := ℬ) x).1 (lkB (X := X) (1:ℬ)) = _
      rw [cor_apply]
      show w - lkX ((1:ℬ) • x) = w - lkX x
      rw [op_one_smul]
    have hkey : omegaNorm (Ba ℬ (Lk ℬ X))
        (baVecNP hY (lkB (X := X) (1 : ℬ)) (ωs i)) (a j - cor (ℬ := ℬ) x)
        = Real.sqrt ((ωs i) (inner ℬ (w - lkX x) (w - lkX x))).re := by
      rw [omegaNorm]
      congr 2
      show (baVecNP hY (lkB (X := X) (1:ℬ)) (ωs i))
        (star (a j - cor (ℬ := ℬ) x) * (a j - cor (ℬ := ℬ) x)) = _
      rw [baVecNP_apply]
      congr 1
      exact (baSubalgebra_inner_star_mul_self (𝒷 := ℬ) (X := Lk ℬ X)
        (a j - cor (ℬ := ℬ) x) (lkB (X := X) (1:ℬ))).trans (by rw [hTv])
    have hji := hj i
    rw [hkey] at hji
    refine le_trans ?_ hji
    have hin : (inner ℬ (w - lkX (ℬ := ℬ) x) (w - lkX (ℬ := ℬ) x) : ℬ)
        = inner ℬ (w.1 - x) (w.1 - x) + inner ℬ w.2 w.2 := by
      rw [lk_inner]
      congr 1
      show (inner ℬ (w.2 - (0:ℬ)) (w.2 - (0:ℬ)) : ℬ) = _
      rw [sub_zero]
    show unSeminorm (ωs i) (cstarBInner ℬ X).inner (x - w.1) ≤ _
    rw [show x - w.1 = -(w.1 - x) by abel, unSeminorm_neg', unSeminorm]
    refine Real.sqrt_le_sqrt ?_
    rw [hin]
    have hle : (inner ℬ (w.1 - x) (w.1 - x) : ℬ)
        ≤ inner ℬ (w.1 - x) (w.1 - x) + inner ℬ w.2 w.2 :=
      le_add_of_nonneg_right CStarModule.inner_self_nonneg
    exact np_re_mono' (ωs i) hle

end Main



omit [CompleteSpace X] [VonNeumannAlgebra ℬ] in
/-- Ultranorm density is transitive: if `D` is ultranorm dense in `X` and (the
image of) `X` is ultranorm dense in `Y`, then `D` is ultranorm dense in `Y`. -/
private theorem unDense_trans {Y : Type*} [NormedAddCommGroup Y] [Module ℂ Y]
    [SMul ℬ Y] [CStarModule ℬ Y] (D : Set X) (η : X → Y)
    (hη_add : ∀ z z' : X, η (z + z') = η z + η z')
    (hη_inner : ∀ z z' : X, (inner ℬ (η z) (η z') : ℬ) = inner ℬ z z')
    (hD : UnDense (inner ℬ) D) (hηd : UnDense (inner ℬ) (Set.range η)) :
    UnDense (inner ℬ) (η '' D) := by
  intro y n ωs ε hε
  obtain ⟨p, ⟨z, rfl⟩, hp⟩ := hηd y n ωs (ε / 2) (by positivity)
  obtain ⟨d, hd, hdz⟩ := hD z n ωs (ε / 2) (by positivity)
  refine ⟨η d, ⟨d, hd, rfl⟩, fun i => ?_⟩
  have hsub : ∀ z z' : X, η z - η z' = η (z - z') := by
    intro z z'
    have h := hη_add (z - z') z'
    rw [sub_add_cancel] at h
    rw [h]; abel
  have hkey : unSeminorm (ωs i) (inner ℬ) (η z - η d)
      = unSeminorm (ωs i) (inner ℬ) (z - d) := by
    rw [hsub, unSeminorm, unSeminorm, hη_inner]
  have hsplit : y - η d = (y - η z) + (η z - η d) := by abel
  have htri := unSeminorm_add_le (ωs i) (cstarBInner ℬ Y) (y - η z) (η z - η d)
  rw [← hsplit, show ((cstarBInner ℬ Y).inner : Y → Y → ℬ) = inner ℬ from rfl] at htri
  have h1 := hp i
  have h2 : unSeminorm (ωs i) (inner ℬ) (η z - η d) ≤ ε / 2 := by
    rw [hkey]; exact hdz i
  show unSeminorm (ωs i) (inner ℬ) (y - η d) ≤ ε
  linarith [htri, h1, h2]

/-- **158II** (`kaplansky-hilbmod`, dils.tex:4143, Kaplansky density
theorem for Hilbert C*-modules): let `X` be a Hilbert ℬ-module for a von
Neumann algebra `ℬ` with an ultranorm-dense 𝒜-submodule `D ⊆ X`, where
`𝒜 ⊆ ℬ` is a C*-subalgebra with `⟨y,y⟩ ∈ 𝒜` for all `y ∈ D`.  Then every
`x ∈ X` is the ultranorm limit of a net in `D` norm-bounded by `‖x‖`.

*Class 2 — a different proof.*  The thesis's route is through **158V**,
which is **false** (see the section comment above and ERRATA.md); this proof
instead runs the **linking algebra** `ℬᵃ(X ⊕ ℬ)` and thesis A's **74IV**
`kaplansky`, as described before `kaplansky_hilbmod_of_selfDual`.  The
general case is reduced to the self-dual one by the self-dual completion
**150II** `dils_completion` (proved since session 61, so this theorem is
now unconditional — `#print axioms` is clean): `D` is
ultranorm dense in `X`, `X` is ultranorm dense in its completion `X̄`, so `D`
is ultranorm dense in `X̄` (`unDense_trans`), and both the norm bound and the
ultranorm seminorms are computed from the inner product, which `η` preserves.
Note the thesis proves 150II at parsec 1500, before 1580, so the dependency
respects the thesis's own order.

**158III** and **158IV** (`h y = y · 2/(1+⟨y,y⟩)`, `g x = x · 1/(1+√(1-⟨x,x⟩))`)
are the elementary part of the *printed* proof and are not needed here. -/
theorem kaplansky_hilbmod
    (A : StarSubalgebra ℂ ℬ) (hA : IsClosed (A : Set ℬ))
    (D : Set X)
    (hD0 : (0 : X) ∈ D)
    (hDadd : ∀ d ∈ D, ∀ d' ∈ D, d + d' ∈ D)
    (hDsmul : ∀ a ∈ A, ∀ d ∈ D, a • d ∈ D)
    (hDinner : ∀ d ∈ D, inner ℬ d d ∈ A)
    (hdense : UnDense (inner ℬ) D) (x : X) :
    ∀ (n : ℕ) (ωs : Fin n → NPFunctional ℬ) (ε : ℝ), 0 < ε →
      ∃ d ∈ D, ‖d‖ ≤ ‖x‖ ∧
        ∀ i, unSeminorm (ωs i) (inner ℬ) (x - d) ≤ ε := by
  intro n ωs ε hε
  obtain ⟨E⟩ := dils_completion (cstarBInner ℬ X)
  have hηsub : ∀ z z' : X, E.η z - E.η z' = E.η (z - z') := by
    intro z z'
    have h := E.η_add (z - z') z'
    rw [sub_add_cancel] at h
    rw [h]; abel
  have hηnorm : ∀ z : X, ‖E.η z‖ = ‖z‖ := by
    intro z
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ), E.η_inner,
      CStarModule.norm_eq_sqrt_norm_inner_self (A := ℬ) (x := z)]
    rfl
  have hηsem : ∀ (ω : NPFunctional ℬ) (z : X),
      unSeminorm ω (inner ℬ) (E.η z) = unSeminorm ω (inner ℬ) z := by
    intro ω z
    rw [unSeminorm, unSeminorm, E.η_inner]
    rfl
  have hη0 : E.η (0 : X) = 0 := by
    have h := E.η_smul_complex 0 0
    rwa [zero_smul, zero_smul] at h
  obtain ⟨d', ⟨d, hd, rfl⟩, hdn, hds⟩ :=
    kaplansky_hilbmod_of_selfDual E.selfDual A hA (E.η '' D)
      (by rw [← hη0]; exact ⟨0, hD0, rfl⟩)
      (by
        rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
        exact ⟨e + e', hDadd e he e' he', E.η_add e e'⟩)
      (by
        rintro a ha _ ⟨e, he, rfl⟩
        exact ⟨a • e, hDsmul a ha e he, E.η_smul a e⟩)
      (by
        rintro _ ⟨e, he, rfl⟩
        rw [E.η_inner]
        exact hDinner e he)
      (unDense_trans D E.η E.η_add (fun z z' => E.η_inner z z') hdense E.dense)
      (E.η x) n ωs ε hε
  refine ⟨d, hd, ?_, fun i => ?_⟩
  · rw [hηnorm, hηnorm] at hdn; exact hdn
  · have h := hds i
    rw [hηsub, hηsem] at h
    exact h


end Linking

end Kaplansky

end Theses.B.Dils
