/-
FDS 2.2, the print's primary definition of a W*-category ("every homset has a
Banach space predual") against the form `WStarCategory` uses (the print's
"equivalently [GLR, Prop. 2.15]": every `End A` a von Neumann algebra and every
hom-set self dual).  See `Papers/FDS/PLAN.md`, "W*-categories from preduals".

What is proved here, without `sorry`:

* **Krein–Šmulian** in separation form (`Sakai.ks_separate`), by the
  Banach–Dieudonné construction and the `c₀`–`ℓ¹` duality: a convex subset of
  the dual of a Banach space that is weak-* closed on every closed ball is
  separated from each outside point by an element of the predual.
* **Sakai ⇒ Kadison** (`Sakai.vonNeumannAlgebra_of_predual`): a C*-algebra
  that is, as a Banach space, the dual of a normed space is a von Neumann
  algebra in the theses' (Kadison) sense, `Theses.VonNeumannAlgebra`.  No
  compatibility between the predual and the multiplication is assumed (Sakai's
  theorem shows none is needed).  Suprema: a bounded directed set has a weak-*
  cluster point, which is its supremum because the positive part of each ball
  is weak-* closed (a norm characterisation of self-adjointness after Vidav).
  Normal functionals: Krein–Šmulian separates `-a` from the positive cone by
  some `e` in the predual; `b ↦ re b(e)`, made complex-linear, is positive,
  normal and nonzero at `a`.
* the bridge from Mathlib's Sakai-style `WStarAlgebra` to the theses'
  `VonNeumannAlgebra` (one direction of DECISIONS §3.7,
  `Sakai.vonNeumannAlgebra_of_wStarAlgebra`);
* **FDS 2.2**: in a C*-category with preduals every `End A` is a von Neumann
  algebra (`vonNeumann_of_homsHavePreduals`), and a C*-category with preduals
  in which any two objects embed isometrically in a common object is a
  W*-category (`WStarCategory.of_homsHavePreduals_of_linking`).

Not proved (the gap, recorded in `PLAN.md` and the FDS 2.2 audit row): the
self-duality of `C(A,B)` for a general C*-category with preduals, which GLR
obtain through the linking algebra of `A` and `B` — a C*-algebra outside the
category, whose predual must itself be constructed.
-/
import Papers.FDS.DirectSums

open Filter Topology Set Metric
open scoped ComplexOrder ENNReal
open Theses

noncomputable section

namespace Papers.FDS

namespace Sakai

section KreinSmulian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

open WeakDual

attribute [local instance] Classical.propDecidable

/-- The finite step of the Banach–Dieudonné construction: if no point of the
weak-* compact set `Q` lies in the polar of `T`, then already the polar of a
finite subset of `T` misses `Q`. -/
theorem ks_finite_step {Q : Set (WeakDual ℂ E)} (hQ : IsCompact Q) (T : Set E)
    (hT : ∀ w ∈ Q, ¬ ∀ e ∈ T, ‖w e‖ ≤ 1) :
    ∃ F : Finset E, (↑F ⊆ T) ∧ ∀ w ∈ Q, ∃ e ∈ F, 1 < ‖w e‖ := by
  obtain ⟨u, hu⟩ := hQ.elim_finite_subfamily_closed
    (fun e : T => {w : WeakDual ℂ E | ‖w e‖ ≤ 1})
    (fun e => isClosed_le (WeakDual.eval_continuous (e : E)).norm continuous_const)
    (by
      ext w
      simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hw h
      exact hT w hw fun e he => h ⟨e, he⟩)
  classical
  refine ⟨u.image Subtype.val, ?_, ?_⟩
  · intro e he
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at he
    obtain ⟨e', -, rfl⟩ := he
    exact e'.2
  · intro w hw
    by_contra h
    push Not at h
    have : w ∈ Q ∩ ⋂ i ∈ u, {w : WeakDual ℂ E | ‖w (i : E)‖ ≤ 1} := by
      refine ⟨hw, ?_⟩
      simp only [mem_iInter, mem_ofPred_eq]
      intro i hi
      exact h i (Finset.mem_image_of_mem _ hi)
    rw [hu] at this
    exact this

/-- The polar condition of the Banach–Dieudonné construction at stage `N`:
every point of `K` of norm at most `N` is pushed out of the unit disc by some
`e ∈ G`. -/
def KSGood (K : Set (WeakDual ℂ E)) (N : ℕ) (G : Finset E) : Prop :=
  ∀ w ∈ K, ‖toStrongDual w‖ ≤ N → ∃ e ∈ G, 1 < ‖w e‖

theorem weakDual_eq_zero_of_forall_norm_le_one {w : WeakDual ℂ E} (h : ∀ e : E, ‖w e‖ ≤ 1) :
    w = 0 := by
  refine DFunLike.ext _ _ fun e => ?_
  by_contra hne
  have hpos : 0 < ‖w e‖ := norm_pos_iff.mpr hne
  have h1 := h (((2 / ‖w e‖ : ℝ) : ℂ) • e)
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    div_mul_cancel₀ _ hpos.ne'] at h1
  norm_num at h1

theorem ks_step {K : Set (WeakDual ℂ E)}
    (hK : ∀ r, IsClosed (K ∩ toStrongDual ⁻¹' closedBall 0 r))
    (h0 : (0 : WeakDual ℂ E) ∉ K) (N : ℕ) (G : Finset E) (hG : KSGood K N G) :
    ∃ F : Finset E, (1 ≤ N → ∀ e ∈ F, ‖e‖ ≤ 1 / N) ∧ KSGood K (N + 1) (G ∪ F) := by
  set Q := (K ∩ toStrongDual ⁻¹' closedBall 0 ((N : ℝ) + 1)) ∩
    ⋂ e ∈ G, {w : WeakDual ℂ E | ‖w e‖ ≤ 1} with hQdef
  have hQ : IsCompact Q := by
    refine (WeakDual.isCompact_closedBall (𝕜 := ℂ) (0 : StrongDual ℂ E) ((N : ℝ) + 1)
      ).of_isClosed_subset ?_ ?_
    · exact (hK _).inter (isClosed_biInter fun e _ =>
        isClosed_le (WeakDual.eval_continuous e).norm continuous_const)
    · exact fun w hw => hw.1.2
  have hT : ∀ w ∈ Q, ¬ ∀ e ∈ (if N = 0 then univ else closedBall 0 (1 / (N : ℝ)) : Set E), ‖w e‖ ≤ 1 := by
    intro w hw hall
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [↓reduceIte] at hall
      apply h0
      have : w = 0 := weakDual_eq_zero_of_forall_norm_le_one fun e => hall e trivial
      exact this ▸ hw.1.1
    · simp only [show N ≠ 0 by omega, ↓reduceIte] at hall
      have hnorm : ‖toStrongDual w‖ ≤ N := by
        refine (toStrongDual w).opNorm_le_bound (Nat.cast_nonneg N) fun x => ?_
        rcases eq_or_ne x 0 with rfl | hx
        · simp
        have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        set c : ℝ := 1 / ((N : ℝ) * ‖x‖) with hc
        have hcpos : 0 < c := by positivity
        have h1 := hall ((c : ℂ) • x) (by
          rw [mem_closedBall_zero_iff, norm_smul, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
          apply le_of_eq
          rw [hc]
          field_simp)
        rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hcpos.le, hc, one_div,
          inv_mul_le_iff₀ (by positivity), mul_one] at h1
        exact h1
      obtain ⟨e, he, h⟩ := hG w hw.1.1 hnorm
      have := hw.2
      simp only [mem_iInter, mem_ofPred_eq] at this
      exact absurd (this e he) (not_le.mpr h)
  obtain ⟨F, hFT, hF⟩ := ks_finite_step hQ (if N = 0 then univ else closedBall 0 (1 / (N : ℝ))) hT
  refine ⟨F, fun hN e he => ?_, fun w hwK hwN => ?_⟩
  · have := hFT he
    simp only [show N ≠ 0 by omega, ↓reduceIte] at this
    simpa using this
  · by_cases hGe : ∃ e ∈ G, 1 < ‖w e‖
    · obtain ⟨e, he, h⟩ := hGe
      exact ⟨e, Finset.mem_union_left _ he, h⟩
    · push Not at hGe
      obtain ⟨e, he, h⟩ := hF w ⟨⟨hwK, by simpa using hwN⟩, by simpa using hGe⟩
      exact ⟨e, Finset.mem_union_right _ he, h⟩

/-- **Banach–Dieudonné**: if `K` meets every closed ball in a weak-* closed
set and `0 ∉ K`, there is a set `U ⊆ E` tending to zero (only finitely many
elements of norm `≥ ε`, for each `ε > 0`) such that every point of `K` takes a
value of modulus `> 1` somewhere on `U`. -/
theorem ks_exists_null_set {K : Set (WeakDual ℂ E)}
    (hK : ∀ r, IsClosed (K ∩ toStrongDual ⁻¹' closedBall 0 r)) (h0 : (0 : WeakDual ℂ E) ∉ K) :
    ∃ U : Set E, (∀ ε > 0, {e ∈ U | ε ≤ ‖e‖}.Finite) ∧ ∀ w ∈ K, ∃ e ∈ U, 1 < ‖w e‖ := by
  classical
  choose F hF1 hF2 using ks_step hK h0
  have base : KSGood K 0 ∅ := by
    intro w hw hn
    exfalso
    have : toStrongDual w = 0 := norm_le_zero_iff.mp (by simpa using hn)
    have hw0 : w = 0 := by simpa using this
    exact h0 (hw0 ▸ hw)
  let G : ∀ N : ℕ, {G : Finset E // KSGood K N G} := fun N =>
    Nat.rec (motive := fun N => {G : Finset E // KSGood K N G}) ⟨∅, base⟩
      (fun N G => ⟨G.1 ∪ F N G.1 G.2, hF2 N G.1 G.2⟩) N
  have hGsucc : ∀ N, (G (N + 1)).1 = (G N).1 ∪ F N (G N).1 (G N).2 := fun N => rfl
  have hmono : Monotone fun N => (G N).1 := by
    refine monotone_nat_of_le_succ fun N => ?_
    rw [hGsucc]
    exact Finset.subset_union_left
  refine ⟨⋃ N, ((G N).1 : Set E), fun ε hε => ?_, fun w hw => ?_⟩
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    set M := n + 1 with hM
    have hsub : ∀ k, ∀ e ∈ (G (M + k)).1, ε ≤ ‖e‖ → e ∈ (G M).1 := by
      intro k
      induction k with
      | zero => intro e he _; simpa using he
      | succ k ih =>
        intro e he hε'
        rw [← add_assoc, hGsucc, Finset.mem_union] at he
        rcases he with he | he
        · exact ih e he hε'
        · exfalso
          have h1 := hF1 (M + k) _ _ (by omega) e he
          have h2 : (1 : ℝ) / ((M + k : ℕ) : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
            apply one_div_le_one_div_of_le (by positivity)
            push_cast [hM]
            linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
          linarith
    refine (G M).1.finite_toSet.subset ?_
    rintro e ⟨he, hε'⟩
    obtain ⟨N, hN⟩ := mem_iUnion.mp he
    rcases le_total N M with hNM | hNM
    · exact hmono hNM hN
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
      exact hsub k e hN hε'
  · obtain ⟨e, he, h⟩ := (G ⌈‖toStrongDual w‖⌉₊).2 w hw (Nat.le_ceil _)
    exact ⟨e, mem_iUnion.mpr ⟨_, he⟩, h⟩

/-- A continuous functional on `ℓ^∞(ι)` is summable against every sequence
tending to zero: with `λᵢ = f(δᵢ)`, `∑ ‖λᵢ‖ ≤ ‖f‖` and `f y = ∑ λᵢ yᵢ`.  (The
`c₀`–`ℓ¹` half of the duality, stated on `ℓ^∞`.) -/
theorem linf_summable_norm_single {ι : Type*} [DecidableEq ι] (f : StrongDual ℂ (lp (fun _ : ι => ℂ) ∞)) :
    Summable fun i => ‖f (lp.single ∞ i 1)‖ := by
  set l : ι → ℂ := fun i => f (lp.single ∞ i 1)
  refine summable_of_sum_le (c := ‖f‖) (fun i => norm_nonneg _) fun S => ?_
  set c : ι → ℂ := fun i => if l i = 0 then 0 else star (l i) / (‖l i‖ : ℂ)
  have hc : ∀ i, ‖c i‖ ≤ 1 := by
    intro i
    by_cases h : l i = 0
    · simp [c, h]
    · have : 0 < ‖l i‖ := norm_pos_iff.mpr h
      simp only [c, h, ↓reduceIte, norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg
        this.le]
      rw [div_self this.ne']
  have hcl : ∀ i, c i * l i = (‖l i‖ : ℂ) := by
    intro i
    by_cases h : l i = 0
    · simp [c, h]
    · have : (‖l i‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr h).ne'
      simp only [c, h, ↓reduceIte]
      rw [div_mul_eq_mul_div, div_eq_iff this, Complex.star_def, Complex.conj_mul']
      ring
  set v : lp (fun _ : ι => ℂ) ∞ := ∑ i ∈ S, c i • lp.single ∞ i 1
  have hv : ‖v‖ ≤ 1 := by
    refine lp.norm_le_of_forall_le zero_le_one fun j => ?_
    simp only [v, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_single,
      smul_eq_mul]
    by_cases hj : j ∈ S
    · rw [Finset.sum_eq_single j]
      · simpa using hc j
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hj'
        exact absurd hj hj'
    · rw [Finset.sum_eq_zero]
      · simp
      · intro b hb
        have : j ≠ b := fun h => hj (h ▸ hb)
        simp [this]
  have hfv : f v = ∑ i ∈ S, (‖l i‖ : ℂ) := by
    simp only [v, map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => hcl i
  have : (∑ i ∈ S, ‖l i‖ : ℝ) = (f v).re := by
    rw [hfv]; simp
  rw [this]
  calc (f v).re ≤ ‖f v‖ := Complex.re_le_norm _
    _ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v
    _ ≤ ‖f‖ * 1 := by gcongr
    _ = ‖f‖ := mul_one _

theorem linf_hasSum_of_tendsto_zero {ι : Type*} [DecidableEq ι] (f : StrongDual ℂ (lp (fun _ : ι => ℂ) ∞))
    (y : lp (fun _ : ι => ℂ) ∞) (hy : Tendsto (fun i => y i) cofinite (𝓝 0)) :
    HasSum (fun i => f (lp.single ∞ i 1) * y i) (f y) := by
  set yS : Finset ι → lp (fun _ : ι => ℂ) ∞ := fun S => ∑ i ∈ S, y i • lp.single ∞ i 1
  have hfy : ∀ S, ∑ i ∈ S, f (lp.single ∞ i 1) * y i = f (yS S) := by
    intro S
    simp only [yS, map_sum, map_smul, smul_eq_mul, mul_comm]
  have hcoord : ∀ S j, (yS S) j = if j ∈ S then y j else 0 := by
    intro S j
    simp only [yS, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_single,
      smul_eq_mul]
    by_cases hj : j ∈ S
    · rw [Finset.sum_eq_single j]
      · simp [hj]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hj'
        exact absurd hj hj'
    · rw [Finset.sum_eq_zero]
      · simp [hj]
      · intro b hb
        have : j ≠ b := fun h => hj (h ▸ hb)
        simp [this]
  have hconv : Tendsto yS atTop (𝓝 y) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hfin : {i | ¬ ‖y i‖ < ε / 2}.Finite := by
      have := (Metric.tendsto_nhds.mp hy) (ε / 2) (by positivity)
      simpa [Filter.eventually_cofinite, dist_zero_right] using this
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (lp.norm_le_of_forall_le (by positivity) fun j => ?_) (half_lt_self hε)
    rw [lp.coeFn_sub, Pi.sub_apply, hcoord]
    by_cases hj : j ∈ S
    · simp [hj]; positivity
    · have : j ∉ hfin.toFinset := fun h => hj (hS h)
      simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, not_not] at this
      simp [hj, this.le]
  unfold HasSum
  simp only [hfy]
  exact (f.continuous.tendsto y).comp hconv

/-- **Krein–Šmulian**, in the separation form we need: in the dual of a
Banach space, a convex set `K` whose intersections with the closed balls are
weak-* closed, and which does not contain `0`, is separated from `0` by an
element of the predual: `1 ≤ re (w e)` for all `w ∈ K`.  Proof by the
Banach–Dieudonné construction and the `c₀`–`ℓ¹` duality. -/
theorem ks_separate_zero [CompleteSpace E] {K : Set (WeakDual ℂ E)}
    (hconv : ∀ w₁ ∈ K, ∀ w₂ ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (t : ℂ) • w₁ + ((1 - t : ℝ) : ℂ) • w₂ ∈ K)
    (hK : ∀ r, IsClosed (K ∩ toStrongDual ⁻¹' closedBall 0 r)) (h0 : (0 : WeakDual ℂ E) ∉ K) :
    ∃ e : E, ∀ w ∈ K, 1 ≤ (w e).re := by
  obtain ⟨U, hfin, hU⟩ := ks_exists_null_set hK h0
  -- a bound on `U`
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ e ∈ U, ‖e‖ ≤ M := by
    obtain ⟨M', hM'⟩ := ((hfin 1 one_pos).image norm).bddAbove
    refine ⟨max 1 M', le_max_left _ _, fun e he => ?_⟩
    by_cases h : 1 ≤ ‖e‖
    · exact (hM' ⟨e, ⟨he, h⟩, rfl⟩).trans (le_max_right _ _)
    · exact (le_of_not_ge h).trans (le_max_left _ _)
  set ι := ↥U
  set L := lp (fun _ : ι => ℂ) ∞
  have hmem : ∀ w : WeakDual ℂ E, Memℓp (fun i : ι => w (i : E)) ∞ := by
    intro w
    refine memℓp_infty ⟨‖toStrongDual w‖ * M, ?_⟩
    rintro _ ⟨i, rfl⟩
    calc ‖w (i : E)‖ = ‖toStrongDual w (i : E)‖ := rfl
      _ ≤ ‖toStrongDual w‖ * ‖(i : E)‖ := (toStrongDual w).le_opNorm _
      _ ≤ ‖toStrongDual w‖ * M := by gcongr; exact hM _ i.2
  let T : WeakDual ℂ E → L := fun w => ⟨fun i => w (i : E), hmem w⟩
  have hT : ∀ w i, T w i = w (i : E) := fun _ _ => rfl
  -- separate the open unit ball from `T '' K`
  have hconvT : Convex ℝ (T '' K) := by
    rintro _ ⟨w₁, hw₁, rfl⟩ _ ⟨w₂, hw₂, rfl⟩ a b ha hb hab
    refine ⟨(a : ℂ) • w₁ + ((1 - a : ℝ) : ℂ) • w₂, hconv w₁ hw₁ w₂ hw₂ a ha (by linarith), ?_⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    ext i
    change toStrongDual ((a : ℂ) • w₁ + ((1 - a : ℝ) : ℂ) • w₂) (i : E) = _
    rw [map_add, map_smul, map_smul]
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  have hdisj : Disjoint (ball (0 : L) 1) (T '' K) := by
    rw [Set.disjoint_left]
    rintro _ hy ⟨w, hw, rfl⟩
    obtain ⟨e, he, h⟩ := hU w hw
    have h1 : ‖T w ⟨e, he⟩‖ ≤ ‖T w‖ := lp.norm_apply_le_norm (by simp) _ _
    rw [mem_ball_zero_iff] at hy
    rw [hT] at h1
    linarith
  obtain ⟨f, u, hfs, hft⟩ :=
    RCLike.geometric_hahn_banach_open (𝕜 := ℂ) (convex_ball 0 1) isOpen_ball hconvT hdisj
  have hu : 0 < u := by simpa using hfs 0 (mem_ball_self one_pos)
  set l : ι → ℂ := fun i => f (lp.single ∞ i 1)
  have hl : Summable fun i => ‖l i‖ := by
    show Summable fun i => ‖f (lp.single ∞ i 1)‖
    exact linf_summable_norm_single f
  have hsum : Summable fun i : ι => l i • (i : E) :=
    Summable.of_norm_bounded (hl.mul_right M) fun i => by
      rw [norm_smul]; gcongr; exact hM _ i.2
  refine ⟨((1 / u : ℝ) : ℂ) • ∑' i : ι, l i • (i : E), fun w hw => ?_⟩
  -- `T w` tends to zero
  have hTw : Tendsto (fun i => T w i) cofinite (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set δ := ε / (‖toStrongDual w‖ + 1)
    have hδ : 0 < δ := by positivity
    have hfinδ : {i : ι | δ ≤ ‖(i : E)‖}.Finite :=
      (hfin δ hδ).preimage (Subtype.val_injective.injOn) |>.subset fun i hi => ⟨i.2, hi⟩
    rw [Filter.eventually_cofinite]
    refine hfinδ.subset fun i hi => ?_
    simp only [mem_ofPred_eq, dist_zero_right, not_lt] at hi ⊢
    by_contra hlt
    push Not at hlt
    have : ‖T w i‖ ≤ ‖toStrongDual w‖ * ‖(i : E)‖ := (toStrongDual w).le_opNorm _
    have h2 : ‖toStrongDual w‖ * ‖(i : E)‖ ≤ ‖toStrongDual w‖ * δ := by gcongr
    have h3 : ‖toStrongDual w‖ * δ < ε := by
      simp only [δ]
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg (toStrongDual w)]
    linarith
  have hrep := linf_hasSum_of_tendsto_zero f (T w) hTw
  have hw_tsum : w (∑' i : ι, l i • (i : E)) = f (T w) := by
    change toStrongDual w (∑' i : ι, l i • (i : E)) = _
    rw [(toStrongDual w).map_tsum hsum]
    simp only [map_smul, smul_eq_mul]
    exact Eq.trans rfl hrep.tsum_eq
  have hfT : u ≤ (f (T w)).re := hft _ ⟨w, hw, rfl⟩
  change 1 ≤ (toStrongDual w (((1 / u : ℝ) : ℂ) • ∑' i : ι, l i • (i : E))).re
  rw [map_smul]
  change 1 ≤ (((1 / u : ℝ) : ℂ) • w (∑' i : ι, l i • (i : E))).re
  rw [hw_tsum, smul_eq_mul, Complex.re_ofReal_mul, one_div, ← div_eq_inv_mul, le_div_iff₀ hu,
    one_mul]
  exact hfT

/-- **Krein–Šmulian**, separation form, for an arbitrary point `x₀ ∉ K`. -/
theorem ks_separate [CompleteSpace E] {K : Set (WeakDual ℂ E)}
    (hconv : ∀ w₁ ∈ K, ∀ w₂ ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (t : ℂ) • w₁ + ((1 - t : ℝ) : ℂ) • w₂ ∈ K)
    (hK : ∀ r, IsClosed (K ∩ toStrongDual ⁻¹' closedBall 0 r)) {x₀ : WeakDual ℂ E}
    (hx₀ : x₀ ∉ K) : ∃ e : E, ∀ w ∈ K, (x₀ e).re + 1 ≤ (w e).re := by
  set K' := {w : WeakDual ℂ E | w + x₀ ∈ K}
  have hconv' : ∀ w₁ ∈ K', ∀ w₂ ∈ K', ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (t : ℂ) • w₁ + ((1 - t : ℝ) : ℂ) • w₂ ∈ K' := by
    intro w₁ h₁ w₂ h₂ t ht0 ht1
    have := hconv _ h₁ _ h₂ t ht0 ht1
    show _ ∈ K
    convert this using 1
    rw [smul_add, smul_add]
    have : x₀ = (t : ℂ) • x₀ + ((1 - t : ℝ) : ℂ) • x₀ := by
      rw [← add_smul]; push_cast; simp
    conv_lhs => rw [this]
    abel
  have hK' : ∀ r, IsClosed (K' ∩ toStrongDual ⁻¹' closedBall 0 r) := by
    intro r
    have : K' ∩ toStrongDual ⁻¹' closedBall 0 r =
        (fun w => w + x₀) ⁻¹' (K ∩ toStrongDual ⁻¹' closedBall 0 (r + ‖toStrongDual x₀‖)) ∩
          toStrongDual ⁻¹' closedBall 0 r := by
      ext w
      simp only [K', mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_closedBall_zero_iff, map_add]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, (norm_add_le _ _).trans (by linarith)⟩, h2⟩
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
    rw [this]
    exact ((hK _).preimage (continuous_add_const x₀)).inter (WeakDual.isClosed_closedBall 0 r)
  have h0' : (0 : WeakDual ℂ E) ∉ K' := by simpa [K'] using hx₀
  obtain ⟨e, he⟩ := ks_separate_zero hconv' hK' h0'
  refine ⟨e, fun w hw => ?_⟩
  have := he (w - x₀) (by simpa [K'] using hw)
  change 1 ≤ (toStrongDual (w - x₀) e).re at this
  rw [map_sub, sub_apply, Complex.sub_re] at this
  change 1 ≤ (w e).re - (x₀ e).re at this
  linarith

end KreinSmulian

/-! ### Sakai's theorem, Kadison form -/

section CStar

open Theses

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem cstar_norm_one_le : ‖(1 : A)‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial A with h | h
  · simp [Subsingleton.elim (1 : A) 0]
  · simp

theorem algebraMap_mono_real {a b : ℝ} (h : a ≤ b) : algebraMap ℝ A a ≤ algebraMap ℝ A b := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← sub_nonneg, ← sub_smul]
  exact smul_nonneg (sub_nonneg.mpr h) (by simp)

/-- If `m ≤ s C` for every `s > 0`, then `m ≤ 0` (the positive cone is closed). -/
theorem cstar_nonpos_of_forall_pos {m : A} (C : ℝ)
    (h : ∀ s : ℝ, 0 < s → m ≤ algebraMap ℝ A (s * C)) : m ≤ 0 := by
  have hcont : Tendsto (fun s : ℝ => algebraMap ℝ A (s * C) - m) (𝓝[>] 0)
      (𝓝 (algebraMap ℝ A (0 * C) - m)) :=
    (((continuous_algebraMap ℝ A).comp (continuous_id.mul continuous_const)).sub
      continuous_const).tendsto 0 |>.mono_left nhdsWithin_le_nhds
  have := CStarAlgebra.isClosed_nonneg.mem_of_tendsto hcont
    (eventually_nhdsWithin_of_forall fun s hs => sub_nonneg.mpr (h s hs))
  simpa using this

omit [PartialOrder A] [StarOrderedRing A] in
theorem star_mul_self_one_add (x : A) (t : ℝ) :
    star ((1 : A) + ((t : ℂ) * Complex.I) • x) * ((1 : A) + ((t : ℂ) * Complex.I) • x) =
      1 + t • (Complex.I • (x - star x)) + (t * t) • (star x * x) := by
  have hs : star ((1 : A) + ((t : ℂ) * Complex.I) • x) =
      1 - (t : ℂ) • (Complex.I • star x) := by
    rw [star_add, star_one, star_smul, Complex.star_def, map_mul, Complex.conj_ofReal,
      Complex.conj_I, mul_neg, neg_smul, mul_smul, sub_eq_add_neg]
  rw [hs, mul_smul]
  simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, Complex.I_mul_I,
    neg_smul, smul_neg, ← Complex.coe_smul]
  simp only [one_smul, Complex.ofReal_mul]
  module

/-- A norm characterisation of self-adjointness (after Vidav): for `‖x‖ ≤ r`,
`x` is self-adjoint iff `‖1 + i t x‖² ≤ 1 + t² r²` for all real `t`.  Each
condition is a norm bound, hence weak-* closed. -/
theorem isSelfAdjoint_iff_norm_le {x : A} {r : ℝ} (hx : ‖x‖ ≤ r) :
    IsSelfAdjoint x ↔ ∀ t : ℝ,
      ‖(1 : A) + ((t : ℂ) * Complex.I) • x‖ ≤ Real.sqrt (1 + t ^ 2 * r ^ 2) := by
  have hr : 0 ≤ r := (norm_nonneg x).trans hx
  have key : ∀ t : ℝ, ‖(1 : A) + ((t : ℂ) * Complex.I) • x‖ ^ 2 =
      ‖(1 : A) + t • (Complex.I • (x - star x)) + (t * t) • (star x * x)‖ := by
    intro t
    rw [← star_mul_self_one_add, CStarRing.norm_star_mul_self, sq]
  constructor
  · intro hsa t
    rw [Real.le_sqrt (norm_nonneg _) (by positivity), key t, hsa.star_eq, sub_self, smul_zero,
      smul_zero, add_zero]
    calc ‖(1 : A) + (t * t) • (x * x)‖ ≤ ‖(1 : A)‖ + ‖(t * t) • (x * x)‖ := norm_add_le _ _
      _ ≤ 1 + t ^ 2 * r ^ 2 := by
        gcongr
        · exact cstar_norm_one_le
        · rw [norm_smul, Real.norm_of_nonneg (mul_self_nonneg t), ← sq]
          gcongr
          calc ‖x * x‖ ≤ ‖x‖ * ‖x‖ := norm_mul_le _ _
            _ ≤ r * r := by gcongr
            _ = r ^ 2 := (sq r).symm
  · intro h
    set m : A := Complex.I • (x - star x) with hm
    have hmsa : IsSelfAdjoint m := by
      rw [IsSelfAdjoint, hm, star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I,
        neg_smul, ← smul_neg, neg_sub]
    have hbound : ∀ t : ℝ, t • m ≤ algebraMap ℝ A (t ^ 2 * r ^ 2) := by
      intro t
      set Y : A := (1 : A) + t • m + (t * t) • (star x * x) with hY
      have hYsa : IsSelfAdjoint Y := by
        refine ((IsSelfAdjoint.one A).add ((IsSelfAdjoint.all t).smul hmsa)).add ?_
        exact (IsSelfAdjoint.all _).smul (IsSelfAdjoint.star_mul_self x)
      have hYn : ‖Y‖ ≤ 1 + t ^ 2 * r ^ 2 := by
        rw [hY, hm, ← key t]
        exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mp (h t)
      have h1 : Y ≤ algebraMap ℝ A (1 + t ^ 2 * r ^ 2) :=
        hYsa.le_algebraMap_norm_self.trans (algebraMap_mono_real hYn)
      have h2 : 0 ≤ (t * t) • (star x * x) := smul_nonneg (mul_self_nonneg t) (star_mul_self_nonneg x)
      rw [map_add, map_one] at h1
      calc t • m ≤ t • m + (t * t) • (star x * x) := le_add_of_nonneg_right h2
        _ ≤ algebraMap ℝ A (t ^ 2 * r ^ 2) := by
          have := h1
          rw [hY, add_assoc] at this
          exact le_of_add_le_add_left this
    have hle : m ≤ 0 := by
      refine cstar_nonpos_of_forall_pos (r ^ 2) fun s hs => ?_
      have := smul_le_smul_of_nonneg_left (hbound s) (inv_nonneg.mpr hs.le)
      rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul, Algebra.algebraMap_eq_smul_one,
        smul_smul] at this
      rw [Algebra.algebraMap_eq_smul_one]
      convert this using 2
      field_simp
    have hge : -m ≤ 0 := by
      refine cstar_nonpos_of_forall_pos (r ^ 2) fun s hs => ?_
      have := smul_le_smul_of_nonneg_left (hbound (-s)) (inv_nonneg.mpr hs.le)
      have hneg : s⁻¹ * -s = -1 := by field_simp
      rw [smul_smul, hneg, neg_one_smul, Algebra.algebraMap_eq_smul_one, smul_smul] at this
      rw [Algebra.algebraMap_eq_smul_one]
      convert this using 2
      field_simp
    have hm0 : m = 0 := le_antisymm hle (neg_nonpos.mp hge)
    rw [hm, smul_eq_zero] at hm0
    rcases hm0 with hI | hsub
    · exact absurd hI Complex.I_ne_zero
    · exact (sub_eq_zero.mp hsub).symm

/-- For self-adjoint `x` with `‖x‖ ≤ r`: `0 ≤ x` iff `‖r - x‖ ≤ r`. -/
theorem nonneg_iff_norm_algebraMap_sub_le {x : A} (hx : IsSelfAdjoint x) {r : ℝ} (hxr : ‖x‖ ≤ r) :
    0 ≤ x ↔ ‖algebraMap ℝ A r - x‖ ≤ r := by
  have hr : 0 ≤ r := (norm_nonneg x).trans hxr
  constructor
  · intro h0
    have h1 : x ≤ algebraMap ℝ A r :=
      hx.le_algebraMap_norm_self.trans (algebraMap_mono_real hxr)
    have h2 : 0 ≤ algebraMap ℝ A r - x := sub_nonneg.mpr h1
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hr h2).mpr (sub_le_self _ h0)
  · intro h
    have hz : IsSelfAdjoint (algebraMap ℝ A r - x) :=
      (IsSelfAdjoint.algebraMap A (IsSelfAdjoint.all r)).sub hx
    have := hz.le_algebraMap_norm_self.trans (algebraMap_mono_real h)
    exact (sub_le_self_iff _).mp this

section Predual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Φ : StrongDual ℂ E ≃ₗᵢ[ℂ] A)

/-- The weak-* dual of the predual, identified with `A` (a linear bijection,
isometric for the dual norm). -/
def wequiv : WeakDual ℂ E ≃ₗ[ℂ] A := WeakDual.toStrongDual.trans Φ.toLinearEquiv

omit [PartialOrder A] [StarOrderedRing A] in
theorem wequiv_apply (w : WeakDual ℂ E) : wequiv Φ w = Φ (WeakDual.toStrongDual w) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem norm_wequiv (w : WeakDual ℂ E) : ‖wequiv Φ w‖ = ‖WeakDual.toStrongDual w‖ :=
  Φ.norm_map _

omit [PartialOrder A] [StarOrderedRing A] in
/-- Norm bounds on affine images are weak-* closed. -/
theorem isClosed_norm_add_smul_le (v : A) (c : ℂ) (ρ : ℝ) :
    IsClosed {w : WeakDual ℂ E | ‖v + c • wequiv Φ w‖ ≤ ρ} := by
  have : {w : WeakDual ℂ E | ‖v + c • wequiv Φ w‖ ≤ ρ} =
      (fun w => (wequiv Φ).symm v + c • w) ⁻¹' (WeakDual.toStrongDual ⁻¹' closedBall 0 ρ) := by
    ext w
    simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff]
    rw [← norm_wequiv Φ, map_add, map_smul, LinearEquiv.apply_symm_apply]
  rw [this]
  exact (WeakDual.isClosed_closedBall 0 ρ).preimage
    (continuous_const.add (continuous_const_smul c))

/-- The self-adjoint part of the `R`-ball, in the weak-* dual. -/
def saBall (R : ℝ) : Set (WeakDual ℂ E) :=
  {w | IsSelfAdjoint (wequiv Φ w) ∧ ‖wequiv Φ w‖ ≤ R}

/-- The positive part of the `R`-ball, in the weak-* dual. -/
def posBall (R : ℝ) : Set (WeakDual ℂ E) := {w | 0 ≤ wequiv Φ w ∧ ‖wequiv Φ w‖ ≤ R}

theorem isClosed_saBall (R : ℝ) : IsClosed (saBall Φ R) := by
  have : saBall Φ R = {w | ‖(0 : A) + (1 : ℂ) • wequiv Φ w‖ ≤ R} ∩
      ⋂ t : ℝ, {w | ‖(1 : A) + ((t : ℂ) * Complex.I) • wequiv Φ w‖ ≤
        Real.sqrt (1 + t ^ 2 * R ^ 2)} := by
    ext w
    simp only [saBall, mem_ofPred_eq, mem_inter_iff, mem_iInter, zero_add, one_smul]
    constructor
    · rintro ⟨hsa, hn⟩
      exact ⟨hn, (isSelfAdjoint_iff_norm_le hn).mp hsa⟩
    · rintro ⟨hn, ht⟩
      exact ⟨(isSelfAdjoint_iff_norm_le hn).mpr ht, hn⟩
  rw [this]
  exact (isClosed_norm_add_smul_le Φ _ _ _).inter
    (isClosed_iInter fun t => isClosed_norm_add_smul_le Φ _ _ _)

theorem isClosed_posBall (R : ℝ) : IsClosed (posBall Φ R) := by
  have : posBall Φ R = saBall Φ R ∩
      {w | ‖algebraMap ℝ A R + (-1 : ℂ) • wequiv Φ w‖ ≤ R} := by
    ext w
    simp only [posBall, saBall, mem_ofPred_eq, mem_inter_iff, neg_one_smul, ← sub_eq_add_neg]
    constructor
    · rintro ⟨h0, hn⟩
      exact ⟨⟨IsSelfAdjoint.of_nonneg h0, hn⟩,
        (nonneg_iff_norm_algebraMap_sub_le (IsSelfAdjoint.of_nonneg h0) hn).mp h0⟩
    · rintro ⟨⟨hsa, hn⟩, h⟩
      exact ⟨(nonneg_iff_norm_algebraMap_sub_le hsa hn).mpr h, hn⟩
  rw [this]
  exact (isClosed_saBall Φ R).inter (isClosed_norm_add_smul_le Φ _ _ _)

theorem isCompact_saBall (R : ℝ) : IsCompact (saBall Φ R) :=
  (WeakDual.isCompact_closedBall (𝕜 := ℂ) (0 : StrongDual ℂ E) R).of_isClosed_subset
    (isClosed_saBall Φ R) fun w hw => by
      simpa [mem_closedBall_zero_iff, ← norm_wequiv Φ] using hw.2

/-- **Monotone completeness from a predual**: a bounded directed set of
self-adjoint elements has a supremum, and the supremum lies in the weak-*
closure of the set (it is the weak-* limit of the net). -/
theorem exists_isLUB_mem_closure (D : Set (selfAdjoint A)) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hbdd : BddAbove D) :
    ∃ s : selfAdjoint A, IsLUB D s ∧
      (wequiv Φ).symm (s : A) ∈
        closure ((fun d : selfAdjoint A => (wequiv Φ).symm (d : A)) '' D) := by
  obtain ⟨d₀, hd₀⟩ := hne
  obtain ⟨u, hu⟩ := hbdd
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  have : IsDirectedOrder D := hdir.isDirectedOrder
  set ι : D → WeakDual ℂ E := fun d => (wequiv Φ).symm (((d : selfAdjoint A)) : A) with hι
  set F : Filter (WeakDual ℂ E) := map ι atTop with hF
  set R : ℝ := ‖(d₀ : A)‖ + ‖(u : A) - d₀‖ with hR
  have htail : ∀ᶠ d : D in atTop, (d₀ : A) ≤ ((d : selfAdjoint A) : A) := by
    filter_upwards [eventually_ge_atTop (⟨d₀, hd₀⟩ : D)] with d hd
    exact hd
  have hbound : ∀ d ∈ D, (d₀ : A) ≤ (d : A) → ‖(d : A)‖ ≤ R := by
    intro d hd h
    have h1 : 0 ≤ (d : A) - d₀ := sub_nonneg.mpr h
    have h2 : (d : A) - d₀ ≤ (u : A) - d₀ := sub_le_sub_right (hu hd) _
    have h3 := CStarAlgebra.norm_le_norm_of_nonneg_of_le h1 h2
    calc ‖(d : A)‖ = ‖(d₀ : A) + ((d : A) - d₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖(d₀ : A)‖ + ‖(d : A) - d₀‖ := norm_add_le _ _
      _ ≤ R := by rw [hR]; gcongr
  have hFR : ∀ᶠ w in F, w ∈ saBall Φ R := by
    rw [hF, eventually_map]
    filter_upwards [htail] with d hd
    refine ⟨?_, ?_⟩
    · simp [hι]
    · simpa [hι] using hbound d d.2 hd
  have : F.NeBot := by rw [hF]; infer_instance
  obtain ⟨c', hc'R, hc'⟩ := (isCompact_saBall Φ R).exists_clusterPt (le_principal_iff.mpr hFR)
  have hmem : ∀ Z : Set (WeakDual ℂ E), IsClosed Z → (∀ᶠ w in F, w ∈ Z) → c' ∈ Z :=
    fun Z hZ hFZ => hZ.closure_subset
      (mem_closure_iff_clusterPt.mpr (hc'.mono (le_principal_iff.mpr hFZ)))
  set c : A := wequiv Φ c' with hc
  have hc_sa : IsSelfAdjoint c := hc'R.1
  have hc'eq : (wequiv Φ).symm c = c' := by rw [hc, LinearEquiv.symm_apply_apply]
  refine ⟨⟨c, hc_sa⟩, ⟨?_, ?_⟩, ?_⟩
  · intro d hd
    have hZ : IsClosed ((fun w => w - (wequiv Φ).symm (d : A)) ⁻¹' posBall Φ (R + ‖(d : A)‖)) :=
      (isClosed_posBall Φ _).preimage (continuous_sub_right _)
    have := hmem _ hZ (by
      rw [hF, eventually_map]
      filter_upwards [htail, eventually_ge_atTop (⟨d, hd⟩ : D)] with d' hd' hdd'
      simp only [hι, posBall, mem_preimage, mem_ofPred_eq, map_sub, LinearEquiv.apply_symm_apply]
      refine ⟨sub_nonneg.mpr hdd', (norm_sub_le _ _).trans ?_⟩
      gcongr
      exact hbound _ d'.2 hd')
    simp only [posBall, mem_preimage, mem_ofPred_eq, map_sub, LinearEquiv.apply_symm_apply] at this
    exact sub_nonneg.mp this.1
  · intro v hv
    have hZ : IsClosed ((fun w => (wequiv Φ).symm (v : A) - w) ⁻¹' posBall Φ (‖(v : A)‖ + R)) :=
      (isClosed_posBall Φ _).preimage (continuous_const.sub continuous_id)
    have := hmem _ hZ (by
      rw [hF, eventually_map]
      filter_upwards [htail] with d' hd'
      simp only [hι, posBall, mem_preimage, mem_ofPred_eq, map_sub, LinearEquiv.apply_symm_apply]
      refine ⟨sub_nonneg.mpr (hv d'.2), (norm_sub_le _ _).trans ?_⟩
      gcongr
      exact hbound _ d'.2 hd')
    simp only [posBall, mem_preimage, mem_ofPred_eq, map_sub, LinearEquiv.apply_symm_apply] at this
    exact sub_nonneg.mp this.1
  · show (wequiv Φ).symm c ∈ _
    rw [hc'eq]
    refine mem_closure_iff_clusterPt.mpr (hc'.mono (le_principal_iff.mpr ?_))
    rw [hF, mem_map]
    exact univ_mem' fun d => ⟨d.1, d.2, rfl⟩

include Φ in
/-- **Sakai ⇒ Kadison** (complete predual): a C*-algebra that is, as a Banach
space, the dual of a Banach space `E` is a von Neumann algebra in the theses'
(Kadison) sense: bounded directed sets of self-adjoint elements have suprema
(`exists_isLUB_mem_closure`), and the functionals `b ↦ re φ_e(b)` from the
predual, made positive and complex-linear, are normal and faithful (via the
Krein–Šmulian separation `ks_separate`). -/
theorem vonNeumannAlgebra_of_complete_predual [CompleteSpace E] : VonNeumannAlgebra A where
  isLUB_of_bddAbove_directed D hne hdir hbdd :=
    (exists_isLUB_mem_closure Φ D hne hdir hbdd).imp fun _ hs => hs.1
  np_faithful a ha hω := by
    by_contra ha0
    set K : Set (WeakDual ℂ E) := {w | 0 ≤ wequiv Φ w} with hKdef
    have hconv : ∀ w₁ ∈ K, ∀ w₂ ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (t : ℂ) • w₁ + ((1 - t : ℝ) : ℂ) • w₂ ∈ K := by
      intro w₁ h₁ w₂ h₂ t ht0 ht1
      simp only [hKdef, mem_ofPred_eq] at h₁ h₂ ⊢
      rw [map_add, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]
      exact add_nonneg (smul_nonneg ht0 h₁) (smul_nonneg (by linarith) h₂)
    have hK : ∀ r, IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall 0 r) := by
      intro r
      have : K ∩ WeakDual.toStrongDual ⁻¹' closedBall 0 r = posBall Φ r := by
        ext w
        simp [hKdef, posBall, norm_wequiv]
      rw [this]
      exact isClosed_posBall Φ r
    set x₀ : WeakDual ℂ E := (wequiv Φ).symm (-a) with hx₀
    have hx₀K : x₀ ∉ K := by
      intro h
      simp only [hKdef, hx₀, mem_ofPred_eq, LinearEquiv.apply_symm_apply] at h
      exact ha0 (le_antisymm (neg_nonneg.mp h) ha)
    obtain ⟨e, he⟩ := ks_separate hconv hK hx₀K
    set ψ : A → ℂ := fun b => (wequiv Φ).symm b e with hψ
    have hψadd : ∀ b c, ψ (b + c) = ψ b + ψ c := fun b c => by
      simp only [hψ, map_add]; rfl
    have hψsmul : ∀ (z : ℂ) b, ψ (z • b) = z * ψ b := fun z b => by
      simp only [hψ, map_smul]; rfl
    have hψK : ∀ b, 0 ≤ b → (x₀ e).re + 1 ≤ (ψ b).re := fun b hb =>
      he _ (by simpa [hKdef] using hb)
    have hψpos : ∀ b, 0 ≤ b → 0 ≤ (ψ b).re := by
      intro b hb
      by_contra hneg
      push Not at hneg
      set t : ℝ := (|(x₀ e).re| + 1) / (-(ψ b).re) with ht
      have htpos : 0 < t := by rw [ht]; apply div_pos (by positivity) (by linarith)
      have h1 := hψK ((t : ℂ) • b) (by rw [Complex.coe_smul]; exact smul_nonneg htpos.le hb)
      rw [hψsmul, Complex.re_ofReal_mul] at h1
      have h2 : t * (ψ b).re = -(|(x₀ e).re| + 1) := by
        rw [ht, div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
      rw [h2] at h1
      linarith [neg_abs_le (x₀ e).re]
    have hψa : 1 ≤ (ψ a).re := by
      have h1 := hψK 0 le_rfl
      have h2 : ψ 0 = 0 := by simpa using hψsmul 0 0
      have h3 : x₀ e = -ψ a := by
        have := hψsmul (-1) a
        simp only [neg_one_smul, neg_one_mul] at this
        rw [← this]
      rw [h2, h3] at h1
      simp at h1
      linarith
    -- the positive complex-linear functional
    let ω₀ : A →ₗ[ℂ] ℂ :=
      { toFun := fun b => (ψ b + star (ψ (star b))) / 2
        map_add' := fun b c => by rw [star_add, hψadd, hψadd, star_add]; ring
        map_smul' := fun z b => by
          simp only [star_smul, hψsmul, star_mul', star_star, RingHom.id_apply, smul_eq_mul]
          ring }
    have hω_sa : ∀ b, IsSelfAdjoint b → ω₀ b = ((ψ b).re : ℂ) := by
      intro b hb
      change (ψ b + star (ψ (star b))) / 2 = _
      rw [hb.star_eq, Complex.star_def, Complex.add_conj]
      push_cast
      ring
    let ω : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ ω₀ fun b hb => by
      rw [hω_sa b (IsSelfAdjoint.of_nonneg hb)]
      exact Complex.zero_le_real.mpr (hψpos b hb)
    have hωapp : ∀ b, ω b = ω₀ b := fun _ => rfl
    have hnormal : PreservesDirSups ⇑ω := by
      intro D s hne hdir hlub
      obtain ⟨s', hs'lub, hs'cl⟩ := exists_isLUB_mem_closure Φ D hne hdir ⟨s, hlub.1⟩
      have hss' : s = s' := hlub.unique hs'lub
      subst hss'
      refine ⟨?_, ?_⟩
      · rintro _ ⟨d, hd, rfl⟩
        exact OrderHomClass.mono ω (hlub.1 hd)
      · intro z hz
        obtain ⟨d₀, hd₀⟩ := hne
        have hz0 : ω (d₀ : A) ≤ z := hz ⟨d₀, hd₀, rfl⟩
        rw [hωapp, hω_sa _ d₀.2, Complex.le_def] at hz0
        simp only [Complex.ofReal_re, Complex.ofReal_im] at hz0
        rw [hωapp, hω_sa _ s.2, Complex.le_def]
        simp only [Complex.ofReal_re, Complex.ofReal_im]
        refine ⟨?_, hz0.2⟩
        have hZ : IsClosed {w : WeakDual ℂ E | (w e).re ≤ z.re} :=
          isClosed_le (Complex.continuous_re.comp (WeakDual.eval_continuous e)) continuous_const
        have hsub : (fun d : selfAdjoint A => (wequiv Φ).symm (d : A)) '' D ⊆
            {w : WeakDual ℂ E | (w e).re ≤ z.re} := by
          rintro _ ⟨d, hd, rfl⟩
          have : ω (d : A) ≤ z := hz ⟨d, hd, rfl⟩
          rw [hωapp, hω_sa _ d.2, Complex.le_def] at this
          simpa using this.1
        exact hZ.closure_subset (closure_mono hsub hs'cl)
    have := hω ⟨ω, hnormal⟩
    have h1 : ω a = ((ψ a).re : ℂ) := by rw [hωapp, hω_sa _ (IsSelfAdjoint.of_nonneg ha)]
    have h2 : ω a = 0 := this
    rw [h1] at h2
    have : (ψ a).re = 0 := by exact_mod_cast h2
    linarith

end Predual

end CStar


/-! ### Normed preduals: passing to the completion -/

section Completion

open UniformSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The dual of a normed space is (isometrically) the dual of its completion. -/
def dualCompletionEquiv : StrongDual ℂ (Completion E) ≃ₗᵢ[ℂ] StrongDual ℂ E where
  toFun g := g.comp Completion.toComplL
  invFun f := f.extend Completion.toComplL
  map_add' g h := ContinuousLinearMap.add_comp _ _ _
  map_smul' c g := ContinuousLinearMap.smul_comp _ _ _
  left_inv g := ContinuousLinearMap.extend_unique _ (by simpa using Completion.denseRange_coe)
    (by simpa using Completion.isUniformInducing_coe E) g rfl
  right_inv f := ContinuousLinearMap.ext fun x => by
    have := ContinuousLinearMap.extend_eq f (e := (Completion.toComplL : E →L[ℂ] Completion E))
      (by simpa using Completion.denseRange_coe) (by simpa using Completion.isUniformInducing_coe E) x
    simpa using this
  norm_map' g := by
    refine le_antisymm ?_ ?_
    · calc ‖g.comp Completion.toComplL‖ ≤ ‖g‖ * ‖(Completion.toComplL : E →L[ℂ] Completion E)‖ :=
            g.opNorm_comp_le _
        _ ≤ ‖g‖ * 1 := by
            gcongr
            exact LinearIsometry.norm_toContinuousLinearMap_le _
        _ = ‖g‖ := mul_one _
    · refine g.opNorm_le_bound (norm_nonneg _) fun y => ?_
      refine Completion.induction_on y
        (isClosed_le (continuous_norm.comp g.continuous) (continuous_const.mul continuous_norm))
        fun x => ?_
      have := (g.comp (Completion.toComplL : E →L[ℂ] Completion E)).le_opNorm x
      simpa [Completion.norm_coe] using this

end Completion

section PredualGeneral

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Sakai ⇒ Kadison**: a C*-algebra that is, as a Banach space, the dual of
a normed space `E` (a linear isometric isomorphism `E* ≅ A`) is a von Neumann
algebra in the theses' (Kadison) sense.  `E` need not be complete: its
completion has the same dual. -/
theorem vonNeumannAlgebra_of_predual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Φ : StrongDual ℂ E ≃ₗᵢ[ℂ] A) : VonNeumannAlgebra A :=
  vonNeumannAlgebra_of_complete_predual (dualCompletionEquiv.trans Φ)

/-- A conjugate-linear isometric isomorphism `E* ≅ M` (the form of Mathlib's
`WStarAlgebra`) composed with the involution of `M`: a linear one. -/
def linearPredualOfConj {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (Ψ : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) : StrongDual ℂ X ≃ₗᵢ[ℂ] A where
  toFun x := star (Ψ x)
  invFun m := Ψ.symm (star m)
  map_add' x y := by simp [star_add]
  map_smul' c x := by
    rw [map_smulₛₗ, star_smul]
    simp
  left_inv x := by simp
  right_inv m := by simp
  norm_map' x := by simp

/-- **Mathlib's `WStarAlgebra` ⇒ the theses' `VonNeumannAlgebra`** (one
direction of the bridge DECISIONS §3.7 asks about): a C*-algebra with a
Banach predual in Mathlib's Sakai-style sense is a von Neumann algebra in the
Kadison sense of thesis A (vn.tex 42I). -/
theorem vonNeumannAlgebra_of_wStarAlgebra [WStarAlgebra A] : VonNeumannAlgebra A := by
  obtain ⟨X, _, _, _, ⟨Ψ⟩⟩ := WStarAlgebra.exists_predual (M := A)
  exact vonNeumannAlgebra_of_predual (linearPredualOfConj Ψ)

end PredualGeneral

end Sakai

/-! ### FDS 2.2: W*-categories from preduals -/

section Category

open CategoryTheory Theses StarCategory

variable {C : Type*} [Category C] [Preadditive C] [Linear ℂ C] [StarCategory C]
  [NormedStarCategory C] [CStarCategory C]

/-- **FDS 2.2** (direct_sums.tex:255, Definition), part 3, the `C(A,A)` half
of "equivalently [GLR, Prop. 2.15]": if the endomorphism space `C(A,A)` of a
C*-category has a Banach predual, then `End A` is a von Neumann algebra
(Sakai's theorem, `Sakai.vonNeumannAlgebra_of_predual`).  Only the predual of
`C(A,A)` is used, and no compatibility with composition. -/
theorem vonNeumann_of_predual {A : C} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Φ : StrongDual ℂ E ≃ₗᵢ[ℂ] (A ⟶ A)) : VonNeumannAlgebra (End A) :=
  Sakai.vonNeumannAlgebra_of_predual (A := End A) Φ

/-- **FDS 2.2** (direct_sums.tex:255, Definition), part 3: in a C*-category
in which every hom-set has a Banach predual (the print's definition of a
W*-category, `HomsHavePreduals`), every `End A` is a von Neumann algebra. -/
theorem vonNeumann_of_homsHavePreduals (h : HomsHavePreduals C) (A : C) :
    VonNeumannAlgebra (End A) := by
  obtain ⟨E, _, _, ⟨Φ⟩⟩ := h A A
  exact vonNeumann_of_predual Φ

/-- **FDS 2.2** (direct_sums.tex:255, Definition), part 3, the print's
definition implies `WStarCategory` for C*-categories in which any two objects
embed isometrically into a common object (e.g. those with orthogonal binary
direct sums, such as Hilb, Rep and NRep): `End S` is a von Neumann algebra by
Sakai's theorem, and the linking argument `WStarCategory.of_linking` gives the
von Neumann algebras `End A` and the self-duality of `A ⟶ B`.  Only the
preduals of the endomorphism spaces are used. -/
theorem WStarCategory.of_homsHavePreduals_of_linking (hP : HomsHavePreduals C)
    (h : ∀ A B : C, ∃ (S : C) (ιA : A ⟶ S) (ιB : B ⟶ S), IsIsometry ιA ∧ IsIsometry ιB) :
    WStarCategory C :=
  WStarCategory.of_linking fun A B => by
    obtain ⟨S, ιA, ιB, hA, hB⟩ := h A B
    exact ⟨S, ιA, ιB, hA, hB, vonNeumann_of_homsHavePreduals hP S⟩

end Category

end Papers.FDS
