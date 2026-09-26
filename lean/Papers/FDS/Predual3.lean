/-
FDS 2.2, forward direction, the off-diagonal case left open by Predual2.lean:
is an isometry `v : A ⟶ B` (`v ≫ v† = 𝟙`) good, i.e. is `y ↦ v† ≫ y`
`σ(A ⟶ B, E₁) → σ(End B, E₂)` continuous on balls for the GIVEN `E₁`?

PLAN / ASSESSMENT (written before the proof).
Operator picture: `N = End B`, `e = v† ≫ v` (the projection `vv*`); then
`y ↦ v† ≫ y` is an isometric iso of `A ⟶ B` onto the one-sided corner
`Ne = {b | b = e ≫ b}`, and `a ↦ a ≫ v` embeds `End A ≅ eNe` as `e(A ⟶ B)`.
So goodness of `v` is exactly: the transported `E₁` is the canonical predual
of the W*-TRO `Ne`.  Tools available for the *given* `E₁`: only
`σ(E₁)`-closedness of norm-defined sets (closed balls, their intersections,
Krein–Šmulian).  Idea (1) (Sakai on `End A` through `e(A ⟶ B)`) needs the
ball of `e(A ⟶ B)` to be `σ(E₁)`-closed; w.r.t. the tripotent `v`,
`e(A ⟶ B) = P₂(v)`, `(1-e)(A ⟶ B) = P₁(v)`, `P₀(v) = 0`.  Every norm
condition tested: `‖tv - y‖ ≤ t` (the "positive cone"), `‖v ± i t y‖ = 1+o(t)`
("hermitian"), and the order-interval conditions `‖q_F - c‖ ≤ 1`,
`‖e - q + c‖ ≤ 1` for a cluster point `c` of increasing projections `q_F ↑ q`
in `eNe` — is satisfied by non-`P₂` points (`M₂`, `e = e₁₁`: `(½, ½)ᵀ` lies
in `{‖y‖ ≤ 1, ‖v - y‖ ≤ 1}`; `(1-ε)q + y₁` with small `y₁ ∈ P₁` passes all
the order-interval tests), because `‖(a + y₁)‖² = ‖a*a + y₁*y₁‖` hides `y₁`
to second order.  Idea (2) (Peirce projections via module actions) needs the
`End B`-action on `A ⟶ B` to be `σ(E₁)`-continuous — the same unknown.
Separating `P₂` from `P₁` needs facial / M-orthogonality structure of the
ball (Edwards–Rüttimann; Barton–Timoney 1986, Horn 1987 via Dineen's bidual
theorem and Friedman–Russo).  NOT attempted.

What IS proved here (faithful partial, arbitrary given preduals):
 1. **reflexive predual uniqueness**: if a normed space `M` is reflexive
    (`inclusionInDoubleDual` surjective), then for ANY predual `E` every
    bounded functional on `M` is `σ(M, E)`-continuous on balls — Hahn–Banach
    in `M*` shows the evaluations at `E` span a dense subspace (a vanishing
    element of `M** = M` is killed by all of `E`, hence 0), then uniform
    approximation on balls;
 2. hence every `w : A ⟶ B` is good whenever `A ⟶ B` is reflexive (this
    subsumes Predual2's finite-dimensional case; a W*-TRO `Ne` is reflexive
    e.g. when `eNe` is finite-dimensional, as for `Hom(ℂⁿ, H)`);
 3. `AdjCompWeakStar`, hence `WStarCategory`, for `HomsHavePreduals`
    categories where each pair of objects is unitarily isomorphic or has a
    reflexive hom-set — e.g. any category of Hilbert spaces in which
    infinite-dimensional objects of the same dimension are unitarily isomorphic.
-/
import Papers.FDS.Predual2

open Filter Topology Set Metric CategoryTheory
open scoped ComplexOrder
open Theses Theses.A.VN Theses.B.Dils

noncomputable section

universe u w

namespace Papers.FDS

namespace Predual3

open StarCategory Predual Predual2

section Reflexive

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Φ : StrongDual ℂ E ≃ₗᵢ[ℂ] M)

/-- The functional `m ↦ ⟨Φ⁻¹ m, e⟩` on `M` given by `e ∈ E`. -/
def evalFun (e : E) : StrongDual ℂ M :=
  (ContinuousLinearMap.apply ℂ ℂ e).comp Φ.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem evalFun_apply (e : E) (m : M) : evalFun Φ e m = Φ.symm m e := rfl

/-- The bounded functionals on `M` that are (everywhere) `σ(M, E)`-continuous. -/
def weakStarCts : Submodule ℂ (StrongDual ℂ M) where
  carrier := {f | @Continuous M ℂ (weakStar Φ) _ f}
  add_mem' {f g} hf hg := by
    let _ : TopologicalSpace M := weakStar Φ
    exact (hf.add hg : Continuous fun m => f m + g m)
  zero_mem' := by
    let _ : TopologicalSpace M := weakStar Φ
    exact (continuous_const : Continuous fun _ : M => (0 : ℂ))
  smul_mem' c f hf := by
    let _ : TopologicalSpace M := weakStar Φ
    exact (continuous_const.mul hf : Continuous fun m => c * f m)

theorem span_evalFun_le :
    Submodule.span ℂ (range (evalFun Φ)) ≤ weakStarCts Φ := by
  rw [Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  exact continuous_weakStar_eval Φ e

/-- **Hahn–Banach for a reflexive `M`**: the evaluations at the predual span a
dense subspace of `M*`. -/
theorem mem_closure_span_evalFun
    (hr : Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ M)) (f : StrongDual ℂ M) :
    f ∈ (Submodule.span ℂ (range (evalFun Φ))).topologicalClosure := by
  set K := (Submodule.span ℂ (range (evalFun Φ))).topologicalClosure
  by_contra hf
  obtain ⟨φ, c, hK, hc⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    (x := f) (s := (K : Set (StrongDual ℂ M))) (K.restrictScalars ℝ).convex
    (Submodule.span ℂ (range (evalFun Φ))).isClosed_topologicalClosure hf
  obtain ⟨h, rfl⟩ := hr φ
  have h0 : ∀ e : E, Φ.symm h e = 0 := by
    intro e
    set z := Φ.symm h e
    have hmem : ∀ t : ℂ, t • evalFun Φ e ∈ K := fun t =>
      K.smul_mem t (Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨e, rfl⟩))
    have hc0 : 0 < c := by
      have := hK 0 K.zero_mem
      simpa using this
    have key : ∀ n : ℕ, (n : ℝ) * ‖z‖ ^ 2 < c := by
      intro n
      have := hK _ (hmem ((n : ℂ) * (starRingEnd ℂ z)))
      have hz : NormedSpace.inclusionInDoubleDual ℂ M h
          (((n : ℂ) * (starRingEnd ℂ z)) • evalFun Φ e) = (n : ℂ) * ((starRingEnd ℂ z) * z) := by
        rw [NormedSpace.dual_def, smul_apply, evalFun_apply, smul_eq_mul,
          mul_assoc]
      rw [hz, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_natCast,
        ← Complex.ofReal_mul] at this
      have h' : (n : ℝ) * Complex.normSq z < c := by simpa using this
      rwa [Complex.normSq_eq_norm_sq] at h'
    by_contra hz
    have hpos : 0 < ‖z‖ ^ 2 := by positivity
    obtain ⟨n, hn⟩ := exists_nat_gt (c / ‖z‖ ^ 2)
    have := key n
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have hh : h = 0 := by
    have : Φ.symm h = 0 := ContinuousLinearMap.ext h0
    simpa using congrArg Φ this
  subst hh
  have := hK 0 K.zero_mem
  simp only [map_zero, zero_apply] at this hc
  linarith

/-- **Predual uniqueness for reflexive spaces**: if `M` is reflexive, then for
ANY predual `E`, every bounded functional on `M` is `σ(M, E)`-continuous on
balls (uniform approximation by the `σ(M, E)`-continuous span of `E`). -/
theorem continuousOn_weakStar_of_reflexive
    (hr : Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ M)) (f : StrongDual ℂ M)
    (R : ℝ) : @ContinuousOn M ℂ (weakStar Φ) _ f (closedBall 0 R) := by
  let _ : TopologicalSpace M := weakStar Φ
  refine continuousOn_of_uniform_approx_of_continuousOn fun U hU => ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
  have hK : 0 < |R| + 1 := by positivity
  have hf : f ∈ closure (SetLike.coe (Submodule.span ℂ (range (evalFun Φ)))) := by
    rw [← Submodule.topologicalClosure_coe]; exact mem_closure_span_evalFun Φ hr f
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf (ε / (|R| + 1)) (div_pos hε hK)
  refine ⟨g, (span_evalFun_le Φ hg : Continuous g).continuousOn, fun y hy => hεU ?_⟩
  rw [mem_closedBall_zero_iff] at hy
  rw [dist_eq_norm, ← sub_apply]
  calc ‖(f - g) y‖ ≤ ‖f - g‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖f - g‖ * (|R| + 1) := by
        gcongr; exact hy.trans ((le_abs_self R).trans (le_add_of_nonneg_right zero_le_one))
    _ < ε / (|R| + 1) * (|R| + 1) := by
        rw [← dist_eq_norm]; exact mul_lt_mul_of_pos_right hfg hK
    _ = ε := div_mul_cancel₀ ε hK.ne'

end Reflexive

section Good

variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear ℂ C] [StarCategory C]
  [NormedStarCategory C] [CStarCategory C]

omit [CStarCategory C] in
/-- **Reflexive hom-sets**: if `A ⟶ B` is reflexive, every `w : A ⟶ B` is
good for arbitrary preduals `E₁` of `A ⟶ B` and `E₂` of `End B`: each
`y ↦ ⟨Φ₂⁻¹(w† ≫ y), e⟩` is a bounded functional on `A ⟶ B`
(`continuousOn_weakStar_of_reflexive`). -/
theorem adjGood_of_reflexive {A B : C} {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    (Φ₁ : StrongDual ℂ E₁ ≃ₗᵢ[ℂ] (A ⟶ B)) (Φ₂ : StrongDual ℂ E₂ ≃ₗᵢ[ℂ] (B ⟶ B))
    (hr : Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ (A ⟶ B))) (w : A ⟶ B) :
    AdjGood Φ₁ Φ₂ w := by
  rw [adjGood_iff]
  intro e R
  let L : (A ⟶ B) →L[ℂ] (B ⟶ B) :=
    (Linear.leftComp ℂ B w†).mkContinuous ‖w†‖ fun y => NormedStarCategory.norm_comp_le _ _
  exact continuousOn_weakStar_of_reflexive Φ₁ hr ((evalFun Φ₂ e).comp L) R

/-- **FDS 2.2**, "equivalently [GLR, Prop. 2.15]", forward direction, for
C*-categories in which any two objects are unitarily isomorphic or have a
reflexive hom-set: `HomsHavePreduals` gives `AdjCompWeakStar` for the given
preduals. -/
theorem adjCompWeakStar_of_unitary_or_reflexive (hP : HomsHavePreduals C)
    (h : ∀ A B : C, (∃ u : A ⟶ B, IsUnitary u) ∨
      Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ (A ⟶ B))) :
    AdjCompWeakStar C := by
  intro A B
  obtain ⟨E₁, i₁, i₂, ⟨Φ₁⟩⟩ := hP A B
  obtain ⟨E₂, j₁, j₂, ⟨Φ₂⟩⟩ := hP B B
  refine ⟨E₁, i₁, i₂, Φ₁, E₂, j₁, j₂, Φ₂, fun w => ?_⟩
  rcases h A B with ⟨u, hu⟩ | hr
  · exact adjGood_of_exists_isUnitary Φ₁ Φ₂ hu w
  · exact adjGood_of_reflexive Φ₁ Φ₂ hr w

theorem WStarCategory.of_homsHavePreduals_of_unitary_or_reflexive (hP : HomsHavePreduals C)
    (h : ∀ A B : C, (∃ u : A ⟶ B, IsUnitary u) ∨
      Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ (A ⟶ B))) :
    WStarCategory C :=
  WStarCategory.of_adjCompWeakStar (adjCompWeakStar_of_unitary_or_reflexive hP h)

end Good

end Predual3

end Papers.FDS
