/-
FDS 2.2, "equivalently [GLR, Prop. 2.15]", forward direction: the off-diagonal
automatic weak-* continuity left open by Predual.lean (`AdjCompWeakStar`).

PLAN / ASSESSMENT (written before the proof).

Wanted: for any Banach preduals `E₁` of `X = A ⟶ B` and `E₂` of `N = End B`,
`T_w : y ↦ w† ≫ y` is `σ(X,E₁) → σ(N,E₂)` continuous on balls.
(b) Direct sums / a common object `S ⊇ A, B`: then `WStarCategory` is
    already proved without any predual of `A ⟶ B`
    (`WStarCategory.of_homsHavePreduals_of_linking`, WStar.lean), and
    `AdjCompWeakStar` follows from `adjCompWeakStar_of_wStarCategory`.  Proving
    it for the *given* `E₁` is the uniqueness of the predual of the corner
    `ι_A†·End S·ι_B`, a general W*-TRO — no easier than the general case.
(a) Sakai's proof transfers only through norm geometry *with a unit*: the
    closed positive ball of `End B` is an intersection of norm balls around
    multiples of `1`.  `X` has no unit.  The Peirce-2 space of a partial
    isometry `u` plays that role, but P₁(u)-directions are flat to second
    order at `u` (`‖u + t y₁‖² = 1 + t²‖y₁‖²`), so no intersection of norm balls
    of `X` separates P₂(u)⁺ from P₁(u); one needs weak-* continuity of the
    Peirce projections, which the literature (Barton–Timoney 1986, Horn
    1987; Zettl 1983, Effros–Ozawa–Ruan 2001 Thm 2.6 for TROs, Schweizer 2002
    for Hilbert modules) gets from JB*-triple structure theory (Dineen's
    bidual theorem, Friedman–Russo contractive projections).  Polarisation
    and Cauchy–Schwarz only move the problem between `T_w` and the
    `End A`-valued products `y ↦ y ≫ z†`, both unknown.  Not attempted.
What IS proved here (faithful partials, arbitrary given preduals):
 1. the good `w` (those with `T_w` weak-* continuous on balls) form a
    norm-closed subspace stable under `w ↦ w ≫ b`, `b ∈ End B`
    (Sakai 1.7.8 on `End B`; uniform limits on balls);
 2. a unitary `u : A ⟶ B` is good: `y ↦ u† ≫ y` is an isometric iso
    `X ≅ End B`, so `E₁` becomes a second predual of `End B` and Sakai's
    uniqueness (`continuousOn_weakStar_id`) applies; by 1 every `w` is good;
 3. finite-dimensional `A ⟶ B`: the ball is norm compact, `σ(X,E₁)` is
    Hausdorff, so all these topologies agree on it;
 4. hence `AdjCompWeakStar` (and `WStarCategory`) for `HomsHavePreduals`
    categories in which every pair of objects is unitarily isomorphic or has
    a finite-dimensional hom-set.
Missing lemma, precisely: for A, B with no unitary between them and
infinite-dimensional `A ⟶ B`, some `w ≠ 0` good for the given `E₁`
(equivalently, by 1, a set of good `w` whose `End B`-span is dense).
-/
import Papers.FDS.Predual

open Filter Topology Set Metric CategoryTheory
open scoped ComplexOrder
open Theses Theses.A.VN Theses.B.Dils

noncomputable section

universe u w

namespace Papers.FDS

namespace Predual2

open StarCategory Predual

variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear ℂ C] [StarCategory C]
  [NormedStarCategory C] [CStarCategory C]

section Good

variable {A B : C} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  (Φ₁ : StrongDual ℂ E₁ ≃ₗᵢ[ℂ] (A ⟶ B)) (Φ₂ : StrongDual ℂ E₂ ≃ₗᵢ[ℂ] (B ⟶ B))

/-- `w` is **good** for the preduals `E₁` of `A ⟶ B` and `E₂` of `B ⟶ B`
when `y ↦ w† ≫ y` is weak-* continuous on every ball. -/
def AdjGood (w : A ⟶ B) : Prop :=
  ∀ R : ℝ, @ContinuousOn (A ⟶ B) (B ⟶ B) (weakStar Φ₁) (weakStar Φ₂) (fun y => w† ≫ y)
    (closedBall 0 R)

omit [CStarCategory C] in
/-- Goodness through the scalar evaluations. -/
theorem adjGood_iff (w : A ⟶ B) : AdjGood Φ₁ Φ₂ w ↔ ∀ (e : E₂) (R : ℝ),
    @ContinuousOn (A ⟶ B) ℂ (weakStar Φ₁) _ (fun y => Φ₂.symm (w† ≫ y) e) (closedBall 0 R) := by
  constructor
  · intro h e R
    exact continuousOn_comp' (weakStar Φ₁) (weakStar Φ₂)
      (continuousOn_of_continuous _ _ (continuous_weakStar_eval Φ₂ e)) (h R) (mapsTo_univ _ _)
  · intro h R
    let _ : TopologicalSpace (A ⟶ B) := weakStar Φ₁
    exact continuousOn_weakStar_of_eval Φ₂ fun e => h e R

omit [CStarCategory C] in
theorem adjGood_zero : AdjGood Φ₁ Φ₂ 0 := by
  rw [adjGood_iff]
  intro e R
  let _ : TopologicalSpace (A ⟶ B) := weakStar Φ₁
  refine (continuousOn_const (c := (0 : ℂ))).congr fun y _ => ?_
  show Φ₂.symm ((0 : A ⟶ B)† ≫ y) e = 0
  rw [adj_zero', Limits.zero_comp, map_zero]
  rfl

omit [CStarCategory C] in
theorem AdjGood.add {w w' : A ⟶ B} (h : AdjGood Φ₁ Φ₂ w) (h' : AdjGood Φ₁ Φ₂ w') :
    AdjGood Φ₁ Φ₂ (w + w') := by
  rw [adjGood_iff] at h h' ⊢
  intro e R
  let _ : TopologicalSpace (A ⟶ B) := weakStar Φ₁
  refine ((h e R).add (h' e R)).congr fun y _ => ?_
  show Φ₂.symm ((w + w')† ≫ y) e = Φ₂.symm (w† ≫ y) e + Φ₂.symm (w'† ≫ y) e
  rw [adj_add', Preadditive.add_comp, map_add]
  rfl

omit [CStarCategory C] in
theorem AdjGood.smul {w : A ⟶ B} (h : AdjGood Φ₁ Φ₂ w) (c : ℂ) : AdjGood Φ₁ Φ₂ (c • w) := by
  rw [adjGood_iff] at h ⊢
  intro e R
  let _ : TopologicalSpace (A ⟶ B) := weakStar Φ₁
  refine ((continuousOn_const (c := starRingEnd ℂ c)).mul (h e R)).congr fun y _ => ?_
  show Φ₂.symm ((c • w)† ≫ y) e = starRingEnd ℂ c * Φ₂.symm (w† ≫ y) e
  rw [adj_smul', Linear.smul_comp, map_smul]
  rfl

/-- **Stability under `End B`**: `(w ≫ b)† ≫ y = (w† ≫ y) * b†` in `End B`,
and right multiplication is weak-* continuous on balls (Sakai 1.7.8). -/
theorem AdjGood.comp_end {w : A ⟶ B} (h : AdjGood Φ₁ Φ₂ w) (b : B ⟶ B) :
    AdjGood Φ₁ Φ₂ (w ≫ b) := by
  have := vonNeumann_of_predual Φ₂
  rw [adjGood_iff]
  intro e R
  have hm := continuousOn_mul_right (M := End B) Φ₂ (toEnd b†) (‖w‖ * R)
  have hm' := continuousOn_comp' (Z := ℂ) (weakStar Φ₂) (weakStar Φ₂)
    (continuousOn_of_continuous _ _ (continuous_weakStar_eval Φ₂ e)) hm (mapsTo_univ _ _)
  have hc := continuousOn_comp' (Z := ℂ) (weakStar Φ₁) (weakStar Φ₂) hm' (h R) (fun y hy => by
    rw [mem_closedBall_zero_iff] at hy ⊢
    calc ‖w† ≫ y‖ ≤ ‖w†‖ * ‖y‖ := NormedStarCategory.norm_comp_le _ _
      _ ≤ ‖w‖ * R := by rw [norm_adj]; gcongr)
  let _ : TopologicalSpace (A ⟶ B) := weakStar Φ₁
  refine hc.congr fun y _ => ?_
  show Φ₂.symm ((w ≫ b)† ≫ y) e = Φ₂.symm (b† ≫ w† ≫ y) e
  rw [adj_comp', Category.assoc]

/-- **The good morphisms are norm closed**: `y ↦ ω(w† ≫ y)` depends
uniformly on `w` over each ball, and uniform limits of continuous maps are
continuous. -/
theorem isClosed_setOf_adjGood : IsClosed {w : A ⟶ B | AdjGood Φ₁ Φ₂ w} := by
  rw [← closure_subset_iff_isClosed]
  intro w hw
  rw [mem_ofPred_eq, adjGood_iff]
  intro e R
  obtain ⟨p, hp⟩ : ∃ p : Filter (A ⟶ B), p = 𝓝[{w : A ⟶ B | AdjGood Φ₁ Φ₂ w}] w := ⟨_, rfl⟩
  have hne : p.NeBot := hp ▸ mem_closure_iff_nhdsWithin_neBot.mp hw
  have hball : ∀ δ > 0, Metric.ball w δ ∈ p := fun δ hδ =>
    hp ▸ mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds w hδ)
  have hself : {w : A ⟶ B | AdjGood Φ₁ Φ₂ w} ∈ p := hp ▸ self_mem_nhdsWithin
  let _ : TopologicalSpace (A ⟶ B) := weakStar Φ₁
  refine TendstoUniformlyOn.continuousOn (F := fun (w' : A ⟶ B) y => Φ₂.symm (w'† ≫ y) e)
    (p := p) ?_ ?_
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set K : ℝ := (‖e‖ + 1) * (|R| + 1) with hK
    have hKpos : 0 < K := by positivity
    filter_upwards [hball (ε / K) (div_pos hε hKpos)] with w' hw' y hy
    rw [mem_ball, dist_eq_norm] at hw'
    rw [mem_closedBall_zero_iff] at hy
    rw [dist_eq_norm, ← ContinuousLinearMap.sub_apply, ← map_sub,
      ← Preadditive.sub_comp, ← adj_sub']
    calc ‖Φ₂.symm ((w - w')† ≫ y) e‖ ≤ ‖Φ₂.symm ((w - w')† ≫ y)‖ * ‖e‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖(w - w')† ≫ y‖ * ‖e‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ ‖(w - w')†‖ * ‖y‖ * ‖e‖ := by gcongr; exact NormedStarCategory.norm_comp_le _ _
      _ ≤ ‖w' - w‖ * (|R| + 1) * (‖e‖ + 1) := by
          rw [norm_adj, norm_sub_rev]
          gcongr
          · exact hy.trans ((le_abs_self R).trans (le_add_of_nonneg_right zero_le_one))
          · linarith
      _ = ‖w' - w‖ * K := by rw [hK]; ring
      _ < ε / K * K := by gcongr
      _ = ε := div_mul_cancel₀ ε hKpos.ne'
  · refine (Filter.eventually_of_mem hself fun w' hw' => ?_).frequently
    exact (adjGood_iff Φ₁ Φ₂ w').mp hw' e R

/-- The good morphisms as a closed `ℂ`-subspace of `A ⟶ B`, stable under
`End B` (`AdjGood.comp_end`, `isClosed_setOf_adjGood`). -/
def goodSubmodule : Submodule ℂ (A ⟶ B) where
  carrier := {w | AdjGood Φ₁ Φ₂ w}
  add_mem' := AdjGood.add Φ₁ Φ₂
  zero_mem' := adjGood_zero Φ₁ Φ₂
  smul_mem' c _ h := AdjGood.smul Φ₁ Φ₂ h c

/-- **Unitaries are good.**  `y ↦ u† ≫ y` is an isometric isomorphism
`A ⟶ B ≅ End B`, so `E₁` is a second predual of `End B`; by Sakai's
uniqueness of the predual (`continuousOn_weakStar_id`) its weak-* topology
agrees with that of `E₂` on balls. -/
theorem adjGood_of_isUnitary {u : A ⟶ B} (hu : IsUnitary u) : AdjGood Φ₁ Φ₂ u := by
  have := vonNeumann_of_predual Φ₂
  let L : (A ⟶ B) ≃ₗ[ℂ] (B ⟶ B) :=
    { toFun := fun y => u† ≫ y
      invFun := fun b => u ≫ b
      left_inv := fun y => by
        show u ≫ u† ≫ y = y
        rw [← Category.assoc, hu.1, Category.id_comp]
      right_inv := fun b => by
        show u† ≫ u ≫ b = b
        rw [← Category.assoc, hu.2, Category.id_comp]
      map_add' := fun y y' => Preadditive.comp_add _ _ _ _ _ _
      map_smul' := fun c y => Linear.comp_smul _ _ _ _ _ _ }
  have hnorm : ∀ y, ‖L y‖ = ‖y‖ := fun y => by
    have h1 : ‖u† ≫ y‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [← norm_adj_comp, ← norm_adj_comp y, adj_comp', adj_adj', Category.assoc,
        ← Category.assoc u, hu.1, Category.id_comp]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  let T : (A ⟶ B) ≃ₗᵢ[ℂ] (B ⟶ B) := { toLinearEquiv := L, norm_map' := hnorm }
  let Ψ : StrongDual ℂ E₁ ≃ₗᵢ[ℂ] (B ⟶ B) := Φ₁.trans T
  intro R
  have h1 : @ContinuousOn (A ⟶ B) (B ⟶ B) (weakStar Φ₁) (weakStar Ψ) T (closedBall 0 R) := by
    let _ : TopologicalSpace (A ⟶ B) := weakStar Φ₁
    refine continuousOn_weakStar_of_eval Ψ fun e => ?_
    refine (continuous_weakStar_eval Φ₁ e).continuousOn.congr fun y _ => ?_
    show Φ₁.symm (T.symm (T y)) e = Φ₁.symm y e
    rw [LinearIsometryEquiv.symm_apply_apply]
  have h2 := continuousOn_weakStar_id (M := End B) Ψ Φ₂ R
  exact @continuousOn_comp' (A ⟶ B) (B ⟶ B) (B ⟶ B) (weakStar Φ₁) (weakStar Ψ) (weakStar Φ₂)
    _ _ _ _ h2 h1 (fun y hy => by
    rw [mem_closedBall_zero_iff] at hy ⊢
    show ‖L y‖ ≤ R
    rw [hnorm]; exact hy)

/-- **Unitarily isomorphic objects**: if some `u : A ⟶ B` is unitary, every
`w : A ⟶ B` is good, for arbitrary preduals (`w = u ≫ (u† ≫ w)`). -/
theorem adjGood_of_exists_isUnitary {u : A ⟶ B} (hu : IsUnitary u) (w : A ⟶ B) :
    AdjGood Φ₁ Φ₂ w := by
  have h := (adjGood_of_isUnitary Φ₁ Φ₂ hu).comp_end Φ₁ Φ₂ (u† ≫ w)
  have e : u ≫ u† ≫ w = w := by rw [← Category.assoc, hu.1, Category.id_comp]
  rwa [e] at h

omit [CStarCategory C] in
/-- **Finite-dimensional hom-sets**: every `w` is good, for arbitrary
preduals — the norm-compact ball carries the Hausdorff `σ(A ⟶ B, E₁)`,
so the two topologies agree on it. -/
theorem adjGood_of_finiteDimensional [FiniteDimensional ℂ (A ⟶ B)] (w : A ⟶ B) :
    AdjGood Φ₁ Φ₂ w := by
  have := FiniteDimensional.proper ℂ (A ⟶ B)
  intro R
  have hid : @ContinuousOn (A ⟶ B) (A ⟶ B) _ (weakStar Φ₁) id (closedBall 0 R) :=
    continuousOn_weakStar_of_eval Φ₁ fun e =>
      (((ContinuousLinearMap.apply ℂ ℂ e).continuous).comp Φ₁.symm.continuous).continuousOn
  have hT : Continuous (fun y : A ⟶ B => w† ≫ y) :=
    AddMonoidHomClass.continuous_of_bound (Preadditive.leftComp B w†) ‖w†‖
      (fun y => NormedStarCategory.norm_comp_le _ _)
  have hf : @ContinuousOn (A ⟶ B) (B ⟶ B) _ (weakStar Φ₂) (fun y => w† ≫ y)
      (closedBall 0 R) :=
    continuousOn_weakStar_of_eval Φ₂ fun e =>
      ((((ContinuousLinearMap.apply ℂ ℂ e).continuous).comp Φ₂.symm.continuous).comp
        hT).continuousOn
  exact @continuousOn_of_isCompact (A ⟶ B) (B ⟶ B) _ (weakStar Φ₁) (weakStar Φ₂) _
    (isCompact_closedBall 0 R) (t2_weakStar Φ₁) hid _ hf

end Good

/-- **FDS 2.2**, "equivalently [GLR, Prop. 2.15]", forward direction, for
C*-categories in which any two objects are unitarily isomorphic or have a
finite-dimensional hom-set: the print's `HomsHavePreduals` gives
`AdjCompWeakStar` (for the given preduals), hence `WStarCategory`. -/
theorem adjCompWeakStar_of_unitary_or_finiteDimensional (hP : HomsHavePreduals C)
    (h : ∀ A B : C, (∃ u : A ⟶ B, IsUnitary u) ∨ FiniteDimensional ℂ (A ⟶ B)) :
    AdjCompWeakStar C := by
  intro A B
  obtain ⟨E₁, i₁, i₂, ⟨Φ₁⟩⟩ := hP A B
  obtain ⟨E₂, j₁, j₂, ⟨Φ₂⟩⟩ := hP B B
  refine ⟨E₁, i₁, i₂, Φ₁, E₂, j₁, j₂, Φ₂, fun w => ?_⟩
  rcases h A B with ⟨u, hu⟩ | hfin
  · exact adjGood_of_exists_isUnitary Φ₁ Φ₂ hu w
  · exact adjGood_of_finiteDimensional Φ₁ Φ₂ w

theorem WStarCategory.of_homsHavePreduals_of_unitary_or_finiteDimensional
    (hP : HomsHavePreduals C)
    (h : ∀ A B : C, (∃ u : A ⟶ B, IsUnitary u) ∨ FiniteDimensional ℂ (A ⟶ B)) :
    WStarCategory C :=
  WStarCategory.of_adjCompWeakStar (adjCompWeakStar_of_unitary_or_finiteDimensional hP h)

end Predual2

end Papers.FDS
