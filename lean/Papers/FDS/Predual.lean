/-
FDS 2.2, "equivalently [GLR, Prop. 2.15]", the forward direction: a
C*-category whose hom-sets have Banach preduals (`HomsHavePreduals`) is a
`WStarCategory` (every `End A` von Neumann, every `A ⟶ B` self dual).

PLAN (written before the proof).

`WStarCategory` asks (i) `End A` von Neumann — done (`vonNeumann_of_predual`,
Sakai via Krein–Šmulian, WStar.lean) — and (ii) `A ⟶ B` self dual over
`End B`.  For (ii) the linking algebra is avoided: by **149V**
(`dils_selfdual`, 3 ⇒ 1) it suffices that bounded ultranorm-Cauchy filters
converge.  Take a weak-* cluster point `x₀` (Banach–Alaoglu for the predual
of `A ⟶ B`); `‖x - x₀‖_ω ≤ ε` follows by lower semicontinuity once
`y ↦ ω(w† ≫ y)` is weak-* continuous on bounded sets of `A ⟶ B` for every
normal `ω` on `End B`.  That splits into
 (a) `y ↦ w† ≫ y`, `A ⟶ B → End B`, weak-* continuous on bounded sets for
     the preduals of the two hom-sets, and
 (b) every normal `ω` is weak-* continuous on bounded sets of `End B` for
     *its given* predual `E` (Sakai's uniqueness of the predual).
(b) is proved here in general: let `P` be the normal positive functionals
that are `σ(M,E)`-continuous on balls.  `P` separates points (Krein–Šmulian
separates `-a` from the positive cone; the functional is made hermitian,
which needs the involution to be `σ(M,E)`-continuous on balls — true because
the self-adjoint part of each ball is weak-* closed); so the initial topology
`τ_P` of `P` is Hausdorff.  On a ball, the ultraweak topology and `σ(M,E)`
are both compact and both finer than `τ_P`, hence all three agree.  So every
ultraweakly continuous map is `σ(M,E)`-continuous on balls, every element of
`E` is a normal functional, and multiplication is separately weak-*
continuous on bounded sets (Sakai 1.7.8, 1.13.2).  Incomplete `E`: pass to
the completion, same argument (compact-to-Hausdorff).
(a) for `A = B` is then (b) (right multiplication by `w†`).  For `A ≠ B` it
is the automatic weak-* continuity of the off-diagonal hom-sets (for TROs:
Zettl 1983, Effros–Ozawa–Ruan 2001 Thm 2.6; for JBW*-triples
Barton–Timoney 1986), whose known proofs need the linking algebra's
predual or triple-product structure theory.  Not attempted: (a) becomes the
hypothesis `AdjCompWeakStar` (an actual property of the preduals, not a cited
theorem), which is also *necessary*: `WStarCategory ↔ AdjCompWeakStar`.
-/
import Papers.FDS.Linking

open Filter Topology Set Metric CategoryTheory
open scoped ComplexOrder
open Theses Theses.A.VN Theses.B.Dils

noncomputable section

universe u w

namespace Papers.FDS

namespace Predual

/-! ### Compact-to-Hausdorff comparison of topologies on a set -/

/-- If `S` is compact for `t₁`, `t₂` is Hausdorff and the identity is
continuous on `S` from `t₁` to `t₂`, then every map continuous on `S` for
`t₁` is continuous on `S` for `t₂` (the two topologies agree on `S`). -/
theorem continuousOn_of_isCompact {X Y : Type*} (t₁ t₂ : TopologicalSpace X)
    [TopologicalSpace Y] {S : Set X} (hS : @IsCompact X t₁ S) (h2 : @T2Space X t₂)
    (hid : @ContinuousOn X X t₁ t₂ id S) {f : X → Y} (hf : @ContinuousOn X Y t₁ _ f S) :
    @ContinuousOn X Y t₂ _ f S := by
  rw [@continuousOn_iff_isClosed X Y t₂]
  intro Z hZ
  obtain ⟨u, hu, hfu⟩ := (@continuousOn_iff_isClosed X Y t₁ _ f S).mp hf Z hZ
  have hK : @IsCompact X t₁ (u ∩ S) := @IsCompact.inter_left X t₁ _ _ hS hu
  have hK2 : @IsCompact X t₂ (u ∩ S) := by
    have := @IsCompact.image_of_continuousOn X X t₁ t₂ _ _ hK
      (@ContinuousOn.mono X X t₁ t₂ id S (u ∩ S) hid inter_subset_right)
    simpa using this
  refine ⟨u ∩ S, @IsCompact.isClosed X t₂ h2 _ hK2, ?_⟩
  rw [hfu, inter_assoc, inter_self]

/-- Composition with the identity from a finer topology on a set. -/
theorem continuousOn_of_id {X Y : Type*} (t₁ t₂ : TopologicalSpace X) [TopologicalSpace Y]
    {S : Set X} {f : X → Y} (hf : @ContinuousOn X Y t₂ _ f S)
    (hid : @ContinuousOn X X t₁ t₂ id S) : @ContinuousOn X Y t₁ _ f S := by
  rw [@continuousOn_iff_isClosed X Y t₁]
  intro Z hZ
  obtain ⟨u, hu, hfu⟩ := (@continuousOn_iff_isClosed X Y t₂ _ f S).mp hf Z hZ
  obtain ⟨u', hu', hu'e⟩ := (@continuousOn_iff_isClosed X X t₁ t₂ id S).mp hid u hu
  exact ⟨u', hu', by rw [hfu, ← hu'e]; rfl⟩

/-- A continuous map is continuous on every set (explicit topologies). -/
theorem continuousOn_of_continuous {X Y : Type*} (t₁ : TopologicalSpace X)
    (t₂ : TopologicalSpace Y) {S : Set X} {f : X → Y} (hf : @Continuous X Y t₁ t₂ f) :
    @ContinuousOn X Y t₁ t₂ f S := by
  rw [@continuousOn_iff_isClosed X Y t₁ t₂]
  intro Z hZ
  exact ⟨f ⁻¹' Z, @IsClosed.preimage X Y t₁ t₂ f hf Z hZ, rfl⟩

/-- Composition across three types with explicit topologies on the first two. -/
theorem continuousOn_comp' {X Y Z : Type*} (tX : TopologicalSpace X) (tY : TopologicalSpace Y)
    [TopologicalSpace Z] {f : X → Y} {g : Y → Z} {S : Set X} {T : Set Y}
    (hg : @ContinuousOn Y Z tY _ g T) (hf : @ContinuousOn X Y tX tY f S) (hST : MapsTo f S T) :
    @ContinuousOn X Z tX _ (g ∘ f) S := by
  let _ := tX; let _ := tY; exact hg.comp hf hST

/-! ### The weak-* topology of a predual, on the dual itself -/

section Weak

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Φ : StrongDual ℂ E ≃ₗᵢ[ℂ] M)

/-- The weak-* topology `σ(M, E)` of a predual `E` of `M` (`Φ : E* ≅ M`),
as a topology on `M`. -/
@[instance_reducible] def weakStar : TopologicalSpace M :=
  TopologicalSpace.induced (fun m => StrongDual.toWeakDual (Φ.symm m)) inferInstance

theorem isInducing_weakStar :
    @Topology.IsInducing M (WeakDual ℂ E) (weakStar Φ) _
      (fun m => StrongDual.toWeakDual (Φ.symm m)) :=
  @Topology.IsInducing.induced M (WeakDual ℂ E) _ _

theorem continuous_weakStar_eval (e : E) :
    @Continuous M ℂ (weakStar Φ) _ (fun m => Φ.symm m e) := by
  let _ : TopologicalSpace M := weakStar Φ
  exact (WeakDual.eval_continuous e).comp continuous_induced_dom

theorem t2_weakStar : @T2Space M (weakStar Φ) := by
  let _ : TopologicalSpace M := weakStar Φ
  refine T2Space.of_injective_continuous (f := fun m => StrongDual.toWeakDual (Φ.symm m))
    (fun a b h => ?_) continuous_induced_dom
  have : Φ.symm a = Φ.symm b := StrongDual.toWeakDual.injective h
  simpa using congrArg Φ this

/-- Continuity into `σ(M, E)` on a set is continuity of every evaluation. -/
theorem continuousOn_weakStar_of_eval {X : Type*} [TopologicalSpace X] {h : X → M} {s : Set X}
    (H : ∀ e : E, ContinuousOn (fun x => Φ.symm (h x) e) s) :
    @ContinuousOn X M _ (weakStar Φ) h s := by
  let _ : TopologicalSpace M := weakStar Φ
  rw [(isInducing_weakStar Φ).continuousOn_iff, continuousOn_iff_continuous_domRestrict]
  refine WeakDual.continuous_of_continuous_eval fun e => ?_
  exact continuousOn_iff_continuous_domRestrict.mp (H e)

theorem image_closedBall (R : ℝ) :
    (fun w : WeakDual ℂ E => Φ (WeakDual.toStrongDual w)) ''
      (WeakDual.toStrongDual ⁻¹' closedBall 0 R) = closedBall (0 : M) R := by
  ext m
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [mem_closedBall_zero_iff] using hw
  · intro hm
    refine ⟨StrongDual.toWeakDual (Φ.symm m), ?_, by simp⟩
    simpa [mem_closedBall_zero_iff] using hm

/-- **Banach–Alaoglu** on `M`: balls are `σ(M, E)`-compact. -/
theorem isCompact_weakStar_closedBall (R : ℝ) :
    @IsCompact M (weakStar Φ) (closedBall (0 : M) R) := by
  let _ : TopologicalSpace M := weakStar Φ
  rw [← image_closedBall Φ R]
  refine (WeakDual.isCompact_closedBall (𝕜 := ℂ) (0 : StrongDual ℂ E) R).image ?_
  refine (continuous_induced_rng (f := fun m : M => StrongDual.toWeakDual (Φ.symm m))
    (t₂ := inferInstance)).mpr ?_
  refine WeakDual.continuous_of_continuous_eval fun e => ?_
  simpa [Function.comp_def] using WeakDual.eval_continuous (𝕜 := ℂ) e

/-- The weak-* topologies of `E` and of its completion agree on `M` up to
continuity: `σ(M, Ê) → σ(M, E)` is continuous. -/
theorem continuous_weakStar_completion :
    @Continuous M M (weakStar (Sakai.dualCompletionEquiv.trans Φ)) (weakStar Φ) id := by
  let _ : TopologicalSpace M := weakStar (Sakai.dualCompletionEquiv.trans Φ)
  refine (continuous_induced_rng (f := fun m : M => StrongDual.toWeakDual (Φ.symm m))
    (t₂ := inferInstance)).mpr ?_
  refine WeakDual.continuous_of_continuous_eval fun e => ?_
  have h := continuous_weakStar_eval (Sakai.dualCompletionEquiv.trans Φ) (e : UniformSpace.Completion E)
  refine h.congr fun m => ?_
  have hm : Sakai.dualCompletionEquiv ((Sakai.dualCompletionEquiv.trans Φ).symm m) = Φ.symm m := by
    exact Sakai.dualCompletionEquiv.apply_symm_apply (Φ.symm m)
  simp only [Function.comp_apply, id]
  rw [← hm]
  rfl

end Weak

/-! ### Sakai: the given predual is the predual of normal functionals -/

section CStar

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Φ : StrongDual ℂ E ≃ₗᵢ[ℂ] M)

omit [PartialOrder M] [StarOrderedRing M] in
theorem wequiv_symm (m : M) :
    (Sakai.wequiv Φ).symm m = StrongDual.toWeakDual (Φ.symm m) := by
  rw [LinearEquiv.symm_apply_eq, Sakai.wequiv_apply]
  simp

omit [PartialOrder M] [StarOrderedRing M] in
theorem isSelfAdjoint_I_smul_sub_star (m : M) :
    IsSelfAdjoint (Complex.I • (m - star m)) := by
  rw [IsSelfAdjoint, star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I,
    neg_smul, ← smul_neg, neg_sub]

omit [PartialOrder M] [StarOrderedRing M] in
theorem eq_star_of_isSelfAdjoint {x c : M} (h1 : IsSelfAdjoint (x + c))
    (h2 : IsSelfAdjoint (Complex.I • (x - c))) : c = star x := by
  have e1 : star x + star c = x + c := by simpa [star_add] using h1.star_eq
  have e2 : star x - star c = c - x := by
    have h := h2.star_eq
    rw [star_smul, star_sub, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg] at h
    have h' := smul_right_injective M Complex.I_ne_zero h
    rw [neg_eq_iff_eq_neg, neg_sub] at h'
    exact h'
  have e3 : star c + star c = x + x := by
    have h := congrArg₂ (· - ·) e1 e2
    calc star c + star c = star x + star c - (star x - star c) := by abel
      _ = x + c - (c - x) := h
      _ = x + x := by abel
  have e4 : star c = x := by
    have h : (2 : ℂ) • star c = (2 : ℂ) • x := by rw [two_smul, two_smul]; exact e3
    exact smul_right_injective M (two_ne_zero) h
  rw [← e4, star_star]

/-- **The involution is `σ(M, E)`-continuous on balls**: a cluster point `c`
of `star mᵢ` (`mᵢ → x`) has `x + c` and `i(x - c)` self-adjoint, because the
self-adjoint part of each ball is weak-* closed (`Sakai.isClosed_saBall`);
so `c = x*`. -/
theorem continuousOn_star (R : ℝ) :
    @ContinuousOn M M (weakStar Φ) (weakStar Φ) star (closedBall 0 R) := by
  let _ : TopologicalSpace M := weakStar Φ
  set g : M → WeakDual ℂ E := fun m => StrongDual.toWeakDual (Φ.symm m) with hg
  have hgc : Continuous g := continuous_induced_dom
  have hgadd : ∀ a b, g (a + b) = g a + g b := fun a b => by simp [hg]
  have hgsub : ∀ a b, g (a - b) = g a - g b := fun a b => by simp [hg]
  have hgsmul : ∀ (c : ℂ) a, g (c • a) = c • g a := fun c a => by simp [hg]
  have hwg : ∀ m, Sakai.wequiv Φ (g m) = m := fun m => by simp [hg, Sakai.wequiv_apply]
  have hsa : ∀ r, IsClosed (Sakai.saBall Φ r) := Sakai.isClosed_saBall Φ
  intro x _
  rw [ContinuousWithinAt, tendsto_iff_ultrafilter]
  intro U hU
  have hUx : (U : Filter M) ≤ 𝓝 x := hU.trans inf_le_left
  have hUB : (U : Filter M) ≤ 𝓟 (closedBall 0 R) := hU.trans inf_le_right
  have hball : ∀ᶠ m in (U : Filter M), ‖m‖ ≤ R := by
    filter_upwards [le_principal_iff.mp hUB] with m hm
    simpa using hm
  obtain ⟨c, -, hc⟩ := (isCompact_weakStar_closedBall Φ R).ultrafilter_le_nhds (U.map star) (by
    rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
    filter_upwards [hball] with m hm
    simpa [mem_closedBall_zero_iff, norm_star] using hm)
  have hc' : Tendsto star (U : Filter M) (𝓝 c) := by
    rw [Tendsto, ← Ultrafilter.coe_map]; exact hc
  have h1 : Tendsto (fun m => g m) U (𝓝 (g x)) := (hgc.tendsto x).comp hUx
  have h2 : Tendsto (fun m => g (star m)) U (𝓝 (g c)) := (hgc.tendsto c).comp hc'
  have hs1 : IsSelfAdjoint (x + c) := by
    have hmem := (hsa (2 * R)).mem_of_tendsto (h1.add h2) (by
      filter_upwards [hball] with m hm
      show IsSelfAdjoint (Sakai.wequiv Φ (g m + g (star m))) ∧
        ‖Sakai.wequiv Φ (g m + g (star m))‖ ≤ 2 * R
      rw [← hgadd, hwg]
      refine ⟨IsSelfAdjoint.add_star_self m, ?_⟩
      calc ‖m + star m‖ ≤ ‖m‖ + ‖star m‖ := norm_add_le _ _
        _ ≤ 2 * R := by rw [norm_star]; linarith)
    have := hmem.1
    rwa [← hgadd, hwg] at this
  have hs2 : IsSelfAdjoint (Complex.I • (x - c)) := by
    have hmem := (hsa (2 * R)).mem_of_tendsto ((h1.sub h2).const_smul Complex.I) (by
      filter_upwards [hball] with m hm
      show IsSelfAdjoint (Sakai.wequiv Φ (Complex.I • (g m - g (star m)))) ∧
        ‖Sakai.wequiv Φ (Complex.I • (g m - g (star m)))‖ ≤ 2 * R
      rw [← hgsub, ← hgsmul, hwg]
      refine ⟨isSelfAdjoint_I_smul_sub_star m, ?_⟩
      rw [norm_smul, Complex.norm_I, one_mul]
      calc ‖m - star m‖ ≤ ‖m‖ + ‖star m‖ := norm_sub_le _ _
        _ ≤ 2 * R := by rw [norm_star]; linarith)
    have := hmem.1
    rwa [← hgsub, ← hgsmul, hwg] at this
  rw [← eq_star_of_isSelfAdjoint hs1 hs2]
  exact hc'

/-- The ultraweak topology makes every ball compact (**77III** and scaling). -/
theorem uw_isCompact_closedBall [VonNeumannAlgebra M] (R : ℝ) :
    @IsCompact M (ultraweak M) (closedBall (0 : M) R) := by
  let _ : TopologicalSpace M := ultraweak M
  rcases lt_or_ge R 0 with hR | hR
  · rw [closedBall_eq_empty.mpr hR]; exact isCompact_empty
  have him : closedBall (0 : M) R = (fun a : M => (R : ℂ) • a) '' closedBall 0 1 := by
    ext m
    constructor
    · intro hm
      rw [mem_closedBall_zero_iff] at hm
      rcases eq_or_lt_of_le hR with h0 | hpos
      · refine ⟨0, by simp, ?_⟩
        have : ‖m‖ ≤ 0 := by rw [h0]; exact hm
        simp [norm_le_zero_iff.mp this]
      · refine ⟨((R⁻¹ : ℝ) : ℂ) • m, ?_, ?_⟩
        · rw [mem_closedBall_zero_iff, norm_smul, Complex.norm_real, Real.norm_of_nonneg
            (inv_nonneg.mpr hR)]
          calc R⁻¹ * ‖m‖ ≤ R⁻¹ * R := by gcongr
            _ = 1 := inv_mul_cancel₀ hpos.ne'
        · simp only
          rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one,
            one_smul]
    · rintro ⟨a, ha, rfl⟩
      rw [mem_closedBall_zero_iff] at ha ⊢
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hR]
      calc R * ‖a‖ ≤ R * 1 := by gcongr
        _ = R := mul_one R
  rw [him]
  exact vn_ball_compact.image (continuous_ultraweak_smul _)

section Complete

variable [CompleteSpace E]

/-- The normal positive functionals that are `σ(M, E)`-continuous on balls. -/
def PSet : Set (NPFunctional M) :=
  {ω | ∀ R : ℝ, @ContinuousOn M ℂ (weakStar Φ) _ (fun m => (ω m : ℂ)) (closedBall 0 R)}

/-- **Enough functionals in `PSet`**: if `a` is self-adjoint and `-a` is not
positive, Krein–Šmulian separates `-a` from the (weak-* closed on balls)
positive cone by some `e ∈ E`; the hermitian part of `b ↦ b(e)` is positive,
normal (bounded monotone nets converge weak-*) and — by `continuousOn_star` —
`σ(M, E)`-continuous on balls, and it does not vanish at `a`.  (The argument
of `Sakai.vonNeumannAlgebra_of_complete_predual`, plus continuity.) -/
theorem exists_mem_PSet (a : M) (ha : IsSelfAdjoint a) (hna : ¬ (0 : M) ≤ -a) :
    ∃ ω ∈ PSet Φ, ω a ≠ 0 := by
  set K : Set (WeakDual ℂ E) := {w | 0 ≤ Sakai.wequiv Φ w} with hKdef
  have hconv : ∀ w₁ ∈ K, ∀ w₂ ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (t : ℂ) • w₁ + ((1 - t : ℝ) : ℂ) • w₂ ∈ K := by
    intro w₁ h₁ w₂ h₂ t ht0 ht1
    simp only [hKdef, mem_ofPred_eq] at h₁ h₂ ⊢
    rw [map_add, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]
    exact add_nonneg (smul_nonneg ht0 h₁) (smul_nonneg (by linarith) h₂)
  have hK : ∀ r, IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall 0 r) := by
    intro r
    have : K ∩ WeakDual.toStrongDual ⁻¹' closedBall 0 r = Sakai.posBall Φ r := by
      ext w
      simp [hKdef, Sakai.posBall, Sakai.norm_wequiv]
    rw [this]
    exact Sakai.isClosed_posBall Φ r
  set x₀ : WeakDual ℂ E := (Sakai.wequiv Φ).symm (-a) with hx₀
  have hx₀K : x₀ ∉ K := by
    intro h
    simp only [hKdef, hx₀, mem_ofPred_eq, LinearEquiv.apply_symm_apply] at h
    exact hna h
  obtain ⟨e, he⟩ := Sakai.ks_separate hconv hK hx₀K
  set ψ : M → ℂ := fun b => (Sakai.wequiv Φ).symm b e with hψ
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
  let ω₀ : M →ₗ[ℂ] ℂ :=
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
  let ω : M →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ ω₀ fun b hb => by
    rw [hω_sa b (IsSelfAdjoint.of_nonneg hb)]
    exact Complex.zero_le_real.mpr (hψpos b hb)
  have hωapp : ∀ b, ω b = ω₀ b := fun _ => rfl
  have hnormal : PreservesDirSups ⇑ω := by
    intro D s hne hdir hlub
    obtain ⟨s', hs'lub, hs'cl⟩ := Sakai.exists_isLUB_mem_closure Φ D hne hdir ⟨s, hlub.1⟩
    have hss' : s = s' := hlub.unique hs'lub
    subst hss'
    refine ⟨?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact OrderHomClass.mono ω (hlub.1 hd)
    · intro z hz
      obtain ⟨d₀, hd₀⟩ := hne
      have hz0 : ω (d₀ : M) ≤ z := hz ⟨d₀, hd₀, rfl⟩
      rw [hωapp, hω_sa _ d₀.2, Complex.le_def] at hz0
      simp only [Complex.ofReal_re, Complex.ofReal_im] at hz0
      rw [hωapp, hω_sa _ s.2, Complex.le_def]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      refine ⟨?_, hz0.2⟩
      have hZ : IsClosed {w : WeakDual ℂ E | (w e).re ≤ z.re} :=
        isClosed_le (Complex.continuous_re.comp (WeakDual.eval_continuous e)) continuous_const
      have hsub : (fun d : selfAdjoint M => (Sakai.wequiv Φ).symm (d : M)) '' D ⊆
          {w : WeakDual ℂ E | (w e).re ≤ z.re} := by
        rintro _ ⟨d, hd, rfl⟩
        have : ω (d : M) ≤ z := hz ⟨d, hd, rfl⟩
        rw [hωapp, hω_sa _ d.2, Complex.le_def] at this
        simpa using this.1
      exact hZ.closure_subset (closure_mono hsub hs'cl)
  refine ⟨⟨ω, hnormal⟩, fun R => ?_, ?_⟩
  · let _ : TopologicalSpace M := weakStar Φ
    have hψc : Continuous ψ := by
      have h := continuous_weakStar_eval Φ e
      refine h.congr fun m => ?_
      simp only [hψ, wequiv_symm]
      rfl
    have hc : ContinuousOn (fun b => (ψ b + star (ψ (star b))) / 2) (closedBall 0 R) :=
      (hψc.continuousOn.add (continuous_star.comp_continuousOn
        (hψc.comp_continuousOn (continuousOn_star Φ R)))).div_const 2
    exact hc
  · show ω a ≠ 0
    rw [hωapp, hω_sa a ha]
    intro h0
    have : (ψ a).re = 0 := by exact_mod_cast h0
    linarith

/-- **`PSet` separates the points of `M`.** -/
theorem eq_zero_of_PSet {m : M} (h : ∀ ω ∈ PSet Φ, ω m = 0) : m = 0 := by
  have hreal : ∀ ω : NPFunctional M, ∀ g : M, IsSelfAdjoint g → (ω g).im = 0 := by
    intro ω g hg
    have h1 : ω.toPositiveLinearMap (star g) = starRingEnd ℂ (ω.toPositiveLinearMap g) :=
      map_star ω.toPositiveLinearMap g
    rw [hg.star_eq] at h1
    exact Complex.conj_eq_iff_im.mp h1.symm
  have hsa : ∀ g : M, IsSelfAdjoint g → (∀ ω ∈ PSet Φ, ω g = 0) → g = 0 := by
    intro g hg hz
    by_contra hg0
    by_cases hn : (0 : M) ≤ -g
    · have hn' : ¬ (0 : M) ≤ -(-g) := by
        rw [neg_neg]
        intro h0
        exact hg0 (le_antisymm (neg_nonneg.mp hn) h0)
      obtain ⟨ω, hω, hne⟩ := exists_mem_PSet Φ (-g) hg.neg hn'
      apply hne
      show ω.toPositiveLinearMap (-g) = 0
      rw [map_neg]
      exact neg_eq_zero.mpr (hz ω hω)
    · obtain ⟨ω, hω, hne⟩ := exists_mem_PSet Φ g hg hn
      exact hne (hz ω hω)
  set hh : M := (realPart m : M) with hhdef
  set kk : M := (imaginaryPart m : M) with hkdef
  have hm : m = hh + Complex.I • kk := (realPart_add_I_smul_imaginaryPart m).symm
  have hhk : ∀ ω ∈ PSet Φ, ω hh = 0 ∧ ω kk = 0 := by
    intro ω hω
    have e : ω.toPositiveLinearMap m = 0 := h ω hω
    rw [hm, map_add, map_smul, smul_eq_mul] at e
    have r1 := hreal ω hh (realPart m).2
    have r2 := hreal ω kk (imaginaryPart m).2
    have ere := congrArg Complex.re e
    have eim := congrArg Complex.im e
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.zero_re,
      Complex.add_im, Complex.mul_im, Complex.zero_im] at ere eim
    change (ω hh).re + (0 * (ω kk).re - 1 * (ω kk).im) = 0 at ere
    change (ω hh).im + (0 * (ω kk).im + 1 * (ω kk).re) = 0 at eim
    rw [r2] at ere
    rw [r1] at eim
    exact ⟨Complex.ext (by rw [Complex.zero_re]; linarith) (by rw [Complex.zero_im]; exact r1),
      Complex.ext (by rw [Complex.zero_re]; linarith) (by rw [Complex.zero_im]; exact r2)⟩
  have h1 : hh = 0 := hsa hh (realPart m).2 fun ω hω => (hhk ω hω).1
  have h2 : kk = 0 := hsa kk (imaginaryPart m).2 fun ω hω => (hhk ω hω).2
  rw [hm, h1, h2, smul_zero, add_zero]

/-- The initial topology `τ_P` of the functionals in `PSet`. -/
@[instance_reducible] def tP : TopologicalSpace M :=
  TopologicalSpace.induced (fun m (ω : PSet Φ) => ((ω : NPFunctional M) m : ℂ)) inferInstance

theorem t2_tP : @T2Space M (tP Φ) := by
  let _ : TopologicalSpace M := tP Φ
  refine T2Space.of_injective_continuous
    (f := fun m (ω : PSet Φ) => ((ω : NPFunctional M) m : ℂ)) (fun a b hab => ?_)
    continuous_induced_dom
  have : a - b = 0 := eq_zero_of_PSet Φ fun ω hω => by
    have := congrFun hab ⟨ω, hω⟩
    show ω.toPositiveLinearMap (a - b) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr this
  exact sub_eq_zero.mp this

omit [CompleteSpace E] in
theorem continuous_uw_tP [VonNeumannAlgebra M] : @Continuous M M (ultraweak M) (tP Φ) id := by
  let _ : TopologicalSpace M := ultraweak M
  refine (continuous_induced_rng
    (f := fun m (ω : PSet Φ) => ((ω : NPFunctional M) m : ℂ)) (t₂ := inferInstance)).mpr ?_
  exact continuous_pi fun ω => continuous_ultraweak_npFunctional (ω : NPFunctional M)

omit [StarOrderedRing M] [CompleteSpace E] in
theorem continuousOn_weakStar_tP (R : ℝ) :
    @ContinuousOn M M (weakStar Φ) (tP Φ) id (closedBall 0 R) := by
  let _ : TopologicalSpace M := weakStar Φ
  refine (@Topology.IsInducing.continuousOn_iff M M (PSet Φ → ℂ) (weakStar Φ) (tP Φ) _ id
    (fun m (ω : PSet Φ) => ((ω : NPFunctional M) m : ℂ))
    (@Topology.IsInducing.induced M (PSet Φ → ℂ) _ _) (closedBall 0 R)).mpr ?_
  exact continuousOn_pi.mpr fun ω => ω.2 R

/-- **Sakai, complete predual**: every map that is ultraweakly continuous on
a ball is `σ(M, E)`-continuous there.  (On the ball, the ultraweak topology
and `σ(M, E)` are compact and finer than the Hausdorff `τ_P`.) -/
theorem continuousOn_weakStar_of_uw_complete [VonNeumannAlgebra M] {Y : Type*}
    [TopologicalSpace Y] {f : M → Y} (R : ℝ)
    (hf : @ContinuousOn M Y (ultraweak M) _ f (closedBall 0 R)) :
    @ContinuousOn M Y (weakStar Φ) _ f (closedBall 0 R) :=
  continuousOn_of_id (weakStar Φ) (tP Φ)
    (continuousOn_of_isCompact (ultraweak M) (tP Φ) (uw_isCompact_closedBall R) (t2_tP Φ)
      (continuousOn_of_continuous _ _ (continuous_uw_tP Φ)) hf)
    (continuousOn_weakStar_tP Φ R)

end Complete

/-- **Sakai's uniqueness of the predual, first half** (any normed predual):
every map that is ultraweakly continuous on a ball of `M` is continuous there
for the weak-* topology of the *given* predual `E`.  In particular every
normal functional is `σ(M, E)`-continuous on bounded sets. -/
theorem continuousOn_weakStar_of_uw [VonNeumannAlgebra M] {Y : Type*} [TopologicalSpace Y]
    {f : M → Y} (R : ℝ) (hf : @ContinuousOn M Y (ultraweak M) _ f (closedBall 0 R)) :
    @ContinuousOn M Y (weakStar Φ) _ f (closedBall 0 R) :=
  continuousOn_of_isCompact (weakStar (Sakai.dualCompletionEquiv.trans Φ)) (weakStar Φ)
    (isCompact_weakStar_closedBall _ R) (t2_weakStar Φ)
    (continuousOn_of_continuous _ _ (continuous_weakStar_completion Φ))
    (continuousOn_weakStar_of_uw_complete (Sakai.dualCompletionEquiv.trans Φ) R hf)

/-- **Sakai's uniqueness of the predual, second half**: every element of the
given predual `E` is a normal (ultraweakly continuous) functional on `M`. -/
theorem continuous_uw_eval [VonNeumannAlgebra M] (e : E) :
    @Continuous M ℂ (ultraweak M) _ (fun m => Φ.symm m e) := by
  set Φ' := Sakai.dualCompletionEquiv.trans Φ
  have h0 : @ContinuousOn M ℂ (weakStar Φ') _ (fun m => Φ.symm m e) (closedBall 0 1) :=
    continuousOn_of_continuous _ _ (@Continuous.comp M M ℂ (weakStar Φ') (weakStar Φ) _ _ _
      (continuous_weakStar_eval Φ e) (continuous_weakStar_completion Φ))
  have h1 : @ContinuousOn M ℂ (tP Φ') _ (fun m => Φ.symm m e) (closedBall 0 1) :=
    continuousOn_of_isCompact (weakStar Φ') (tP Φ') (isCompact_weakStar_closedBall Φ' 1)
      (t2_tP Φ') (continuousOn_weakStar_tP Φ' 1) h0
  have h2 : @ContinuousOn M ℂ (ultraweak M) _ (fun m => Φ.symm m e) (closedBall 0 1) :=
    continuousOn_of_id (ultraweak M) (tP Φ') h1
      (continuousOn_of_continuous _ _ (continuous_uw_tP Φ'))
  let L : M →ₗ[ℂ] ℂ :=
    { toFun := fun m => Φ.symm m e
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  exact uwcont_on_ball L h2

/-- **Sakai: the weak-* topology on bounded sets does not depend on the
predual.**  For any two preduals `E, E'` of a von Neumann algebra, `σ(M, E)`
and `σ(M, E')` agree on balls. -/
theorem continuousOn_weakStar_id [VonNeumannAlgebra M] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℂ E'] (Φ' : StrongDual ℂ E' ≃ₗᵢ[ℂ] M) (R : ℝ) :
    @ContinuousOn M M (weakStar Φ) (weakStar Φ') id (closedBall 0 R) := by
  let _ : TopologicalSpace M := weakStar Φ
  refine continuousOn_weakStar_of_eval Φ' fun e => ?_
  exact continuousOn_weakStar_of_uw Φ R (continuousOn_of_continuous _ _ (continuous_uw_eval Φ' e))

/-- **Sakai 1.7.8, on bounded sets** (any predual): left multiplication is
`σ(M, E)`-continuous on balls. -/
theorem continuousOn_mul_left [VonNeumannAlgebra M] (a : M) (R : ℝ) :
    @ContinuousOn M M (weakStar Φ) (weakStar Φ) (fun m => a * m) (closedBall 0 R) := by
  let _ : TopologicalSpace M := weakStar Φ
  refine continuousOn_weakStar_of_eval Φ fun e => ?_
  refine continuousOn_weakStar_of_uw Φ R (continuousOn_of_continuous _ _ ?_)
  exact @Continuous.comp M M ℂ (ultraweak M) (ultraweak M) _ _ _ (continuous_uw_eval Φ e)
    (mult_uws_cont a).1

/-- **Sakai 1.7.8, on bounded sets** (any predual): right multiplication is
`σ(M, E)`-continuous on balls. -/
theorem continuousOn_mul_right [VonNeumannAlgebra M] (a : M) (R : ℝ) :
    @ContinuousOn M M (weakStar Φ) (weakStar Φ) (fun m => m * a) (closedBall 0 R) := by
  let _ : TopologicalSpace M := weakStar Φ
  refine continuousOn_weakStar_of_eval Φ fun e => ?_
  refine continuousOn_weakStar_of_uw Φ R (continuousOn_of_continuous _ _ ?_)
  exact @Continuous.comp M M ℂ (ultraweak M) (ultraweak M) _ _ _ (continuous_uw_eval Φ e)
    (mult_uws_cont a).2.1

end CStar

end Predual

/-! ### FDS 2.2: self-duality from preduals compatible with `y ↦ w† ≫ y` -/

section Category

open StarCategory Predual

variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear ℂ C] [StarCategory C]
  [NormedStarCategory C] [CStarCategory C]

/-- **Self-duality from a predual.**  If `A ⟶ B` has a predual `E₁`, `End B`
(a von Neumann algebra) has a predual `E₂`, and every `y ↦ w† ≫ y` is
weak-* continuous on bounded sets for these preduals, then `A ⟶ B` is a
self-dual Hilbert `End B`-module.  Route **149V** 3 ⇒ 1: a bounded
ultranorm-Cauchy filter has a weak-* cluster point `x₀` (Banach–Alaoglu), and
`‖x - x₀‖_ω ≤ ε` because `y ↦ ω⟪x - x₀, x - y⟫` is weak-* continuous on the
ball (hypothesis, and Sakai's `continuousOn_weakStar_of_uw` for the normal
`ω`) and bounded by `‖x - x₀‖_ω ε` near `x₀` (Cauchy–Schwarz). -/
theorem selfDual_of_weakStar {A B : C} [VonNeumannAlgebra (End B)]
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
    [NormedSpace ℂ E₂] (Φ₁ : StrongDual ℂ E₁ ≃ₗᵢ[ℂ] (A ⟶ B))
    (Φ₂ : StrongDual ℂ E₂ ≃ₗᵢ[ℂ] (B ⟶ B))
    (h : ∀ (w : A ⟶ B) (R : ℝ), @ContinuousOn (A ⟶ B) (B ⟶ B) (weakStar Φ₁) (weakStar Φ₂)
      (fun y => w† ≫ y) (closedBall 0 R)) :
    SelfDual (End B) (A ⟶ B) := by
  have hS : BddUnComplete (End B) (A ⟶ B) := by
    rintro F hF hcau ⟨K, s₀, hs₀F, hs₀⟩
    let _ : TopologicalSpace (A ⟶ B) := weakStar Φ₁
    have : T2Space (A ⟶ B) := t2_weakStar Φ₁
    have hSc : IsCompact (closedBall (0 : A ⟶ B) K) := isCompact_weakStar_closedBall Φ₁ K
    have hFS : F ≤ 𝓟 (closedBall 0 K) := le_principal_iff.mpr
      (mem_of_superset hs₀F fun x hx => mem_closedBall_zero_iff.mpr (hs₀ x hx))
    obtain ⟨x₀, -, hx₀⟩ := hSc.exists_clusterPt hFS
    refine ⟨x₀, fun ω => ?_⟩
    have hω : ∀ R, @ContinuousOn (End B) ℂ (weakStar (M := End B) Φ₂) _ (fun m => ω m)
        (closedBall 0 R) := fun R =>
      continuousOn_weakStar_of_uw (M := End B) Φ₂ R
        (continuousOn_of_continuous _ _ (continuous_ultraweak_npFunctional ω))
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨s, hsF, hs⟩ := hcau ω (ε / 2) (by linarith)
    filter_upwards [hsF, hs₀F] with x hx hx0
    set v : A ⟶ B := x - x₀ with hv
    set u : ℝ := unSeminorm ω (inner (End B)) v with hu
    have hu0 : 0 ≤ u := unSeminorm_nonneg _ _ _
    -- `y ↦ ω⟪v, y⟫` is weak-* continuous on the ball
    have hcomp : ContinuousOn (fun y => ω (toEnd (v† ≫ y))) (closedBall 0 K) :=
      continuousOn_comp' (weakStar Φ₁) (weakStar (M := End B) Φ₂) (hω (‖v‖ * K)) (h v K)
        (fun y hy => by
          rw [mem_closedBall_zero_iff] at hy ⊢
          calc ‖v† ≫ y‖ ≤ ‖v†‖ * ‖y‖ := NormedStarCategory.norm_comp_le _ _
            _ ≤ ‖v‖ * K := by rw [norm_adj]; gcongr)
    have hg : ContinuousOn (fun y => ω (inner (End B) v (x - y))) (closedBall 0 K) := by
      refine ContinuousOn.congr (f := fun y => ω (toEnd (v† ≫ x)) - ω (toEnd (v† ≫ y)))
        (continuousOn_const.sub hcomp) fun y _ => ?_
      show ω (toEnd (v† ≫ (x - y))) = ω (toEnd (v† ≫ x)) - ω (toEnd (v† ≫ y))
      rw [show toEnd (v† ≫ (x - y)) = toEnd (v† ≫ x) - toEnd (v† ≫ y) from
        Preadditive.comp_sub _ _ _]
      exact map_sub ω.toPositiveLinearMap _ _
    have hZ : IsClosed (closedBall (0 : A ⟶ B) K ∩
        (fun y => ω (inner (End B) v (x - y))) ⁻¹' closedBall 0 (u * (ε / 2))) :=
      hg.preimage_isClosed_of_isClosed hSc.isClosed isClosed_closedBall
    have hZF : closedBall (0 : A ⟶ B) K ∩
        (fun y => ω (inner (End B) v (x - y))) ⁻¹' closedBall 0 (u * (ε / 2)) ∈ F := by
      filter_upwards [hsF, hs₀F] with y hy hy0
      refine ⟨mem_closedBall_zero_iff.mpr (hs₀ y hy0), ?_⟩
      rw [mem_preimage, mem_closedBall_zero_iff]
      have hcs := unSeminorm_inner_le ω (cstarBInner (End B) (A ⟶ B)) v (x - y)
      calc ‖ω (inner (End B) v (x - y))‖ ≤ u * unSeminorm ω (inner (End B)) (x - y) := hcs
        _ ≤ u * (ε / 2) := by gcongr; exact hs x hx y hy
    have hx₀Z := hZ.closure_subset (mem_closure_iff_clusterPt.mpr (hx₀.mono (le_principal_iff.mpr hZF)))
    have hle : ‖ω (inner (End B) v v)‖ ≤ u * (ε / 2) := by
      have := hx₀Z.2
      rwa [mem_preimage, mem_closedBall_zero_iff] at this
    have hsq : u ^ 2 = (ω (inner (End B) v v)).re :=
      unSeminorm_sq ω (cstarBInner (End B) (A ⟶ B)) v
    have hre : (ω (inner (End B) v v)).re ≤ ‖ω (inner (End B) v v)‖ := Complex.re_le_norm _
    have hue : u ≤ ε / 2 := by nlinarith
    show dist (unSeminorm ω (inner (End B)) (x - x₀)) 0 < ε
    rw [Real.dist_eq, sub_zero, ← hv, ← hu, abs_of_nonneg hu0]
    linarith
  exact ((dils_selfdual (𝒷 := End B) (X := A ⟶ B)).out 2 0).mp hS

variable (C) in
/-- **Preduals compatible with `y ↦ w† ≫ y`**: for all objects `A, B` there
are Banach preduals `E₁` of `A ⟶ B` and `E₂` of `B ⟶ B` such that for every
`w : A ⟶ B` the map `y ↦ w† ≫ y` (the inner product `⟪w, y⟫` of the Hilbert
`End B`-module `A ⟶ B`) is weak-* continuous on bounded sets.  The choice of
`E₂` is immaterial (`Predual.continuousOn_weakStar_id`).  For `A = B` this
holds for *every* predual (`adjComp_weakStar_diag`, Sakai); for `A ≠ B`
it is the automatic weak-* continuity of the off-diagonal hom-sets, which the
print (and GLR's "equivalently") takes for granted. -/
def AdjCompWeakStar : Prop :=
  ∀ A B : C, ∃ (E₁ : Type u) (_ : NormedAddCommGroup E₁) (_ : NormedSpace ℂ E₁)
    (Φ₁ : StrongDual ℂ E₁ ≃ₗᵢ[ℂ] (A ⟶ B)) (E₂ : Type u) (_ : NormedAddCommGroup E₂)
    (_ : NormedSpace ℂ E₂) (Φ₂ : StrongDual ℂ E₂ ≃ₗᵢ[ℂ] (B ⟶ B)),
    ∀ (w : A ⟶ B) (R : ℝ), @ContinuousOn (A ⟶ B) (B ⟶ B) (weakStar Φ₁) (weakStar Φ₂)
      (fun y => w† ≫ y) (closedBall 0 R)

/-- **Sakai 1.7.8 for `End A`**: for *any* Banach predual of `A ⟶ A`, every
`y ↦ w† ≫ y` (right multiplication by `w†` in `End A`) is weak-* continuous on
bounded sets — the diagonal case of `AdjCompWeakStar` holds automatically. -/
theorem adjComp_weakStar_diag {A : C} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Φ : StrongDual ℂ E ≃ₗᵢ[ℂ] (A ⟶ A)) (w : A ⟶ A) (R : ℝ) :
    @ContinuousOn (A ⟶ A) (A ⟶ A) (weakStar Φ) (weakStar Φ) (fun y => w† ≫ y)
      (closedBall 0 R) := by
  have := vonNeumann_of_predual Φ
  exact continuousOn_mul_right (M := End A) Φ (toEnd w†) R

/-- **FDS 2.2** (direct_sums.tex:255, Definition), part 3, the forward half of
"equivalently [GLR, Prop. 2.15]" under compatible preduals: a C*-category
whose hom-sets have preduals for which `y ↦ w† ≫ y` is weak-* continuous on
bounded sets is a W*-category (`End A` von Neumann by Sakai,
`vonNeumann_of_predual`; `A ⟶ B` self dual by `selfDual_of_weakStar`). -/
theorem WStarCategory.of_adjCompWeakStar (h : AdjCompWeakStar C) : WStarCategory C where
  vonNeumann A := by
    obtain ⟨E₁, _, _, Φ₁, -⟩ := h A A
    exact vonNeumann_of_predual Φ₁
  selfDual A B := by
    obtain ⟨E₁, _, _, Φ₁, E₂, _, _, Φ₂, hc⟩ := h A B
    have := vonNeumann_of_predual Φ₂
    exact selfDual_of_weakStar Φ₁ Φ₂ hc

/-- The compatibility is necessary: in a `WStarCategory` the canonical
preduals (`Linking.selfDualPredualEquiv` for `A ⟶ B`, the normal functionals
`Linking.predualEquiv` for `End B`) satisfy it, since `ω(w† ≫ y)` is the
evaluation of `y` at the generator `ω ∘ ⟪w, ·⟫` of the predual of `A ⟶ B`. -/
theorem adjCompWeakStar_of_wStarCategory [WStarCategory C] : AdjCompWeakStar C := by
  intro A B
  refine ⟨_, _, _, Linking.selfDualPredualEquiv (M := End B) (X := A ⟶ B)
    (WStarCategory.selfDual A B), _, _, _, Linking.predualEquiv (M := End B), fun w R => ?_⟩
  refine continuousOn_of_continuous _ _ ?_
  let _ : TopologicalSpace (A ⟶ B) :=
    weakStar (Linking.selfDualPredualEquiv (M := End B) (X := A ⟶ B) (WStarCategory.selfDual A B))
  refine (continuous_induced_rng (t₂ := inferInstance)).mpr ?_
  refine WeakDual.continuous_of_continuous_eval fun ω => ?_
  exact (continuous_weakStar_eval _ ⟨Linking.efun ω w, Linking.efun_mem ω w⟩).congr fun y => rfl

/-- **FDS 2.2**, "equivalently [GLR, Prop. 2.15]", with the compatibility made
explicit: a C*-category is a `WStarCategory` iff its hom-sets have preduals
for which `y ↦ w† ≫ y` is weak-* continuous on bounded sets. -/
theorem wStarCategory_iff_adjCompWeakStar : WStarCategory C ↔ AdjCompWeakStar C :=
  ⟨fun _ => adjCompWeakStar_of_wStarCategory, WStarCategory.of_adjCompWeakStar⟩

end Category

end Papers.FDS
