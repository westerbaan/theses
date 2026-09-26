import Papers.REC.Monoidal

/-!
# Alfsen–Shultz (1.82) and the exponential formula: `AlfsenShultzResolventCriterion`, proved

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707, `short.tex` §5.4, REC 120 (`prop:assert-is-derivation`).

The named hypothesis `AlfsenShultzResolventCriterion` (`Reconstruction.lean`), which
REC 120 and through it REC 121, 102, 103 and 136 took, is *proved* here: on a Banach
order unit space, a bounded `δ` such that `1 ∓ λδ` carries non-positive elements to
non-positive elements for all small `λ > 0` is an order derivation (REC 117).

The argument (Alfsen–Shultz, *State spaces of operator algebras*, (1.82) and the
exponential formula), on the Banach algebra `B(W)` of bounded operators for the
order-unit norm (`ousNormedAddCommGroup`, `completeSpace_of_banach`):

1. for `λ‖δ‖ < 1` the operator `1 - λB` is invertible (Neumann series,
   `Units.oneSub`), and its inverse is positive: for `x ≥ 0` put `y = (1 - λB)⁻¹ x`;
   if `y` were not positive, neither would `x = (1 - λB) y` be;
2. `((1 - A/n)⁻¹)ⁿ → e^{A}` in norm (`tendsto_resolvent_pow`, proved like the
   Lie–Trotter formula of `JordanSymmetry.lean`: `s ↦ (1 - sA)⁻¹ - e^{sA}` has
   derivative `0` at `0`, and `‖aⁿ - bⁿ‖ ≤ n‖a - b‖Mⁿ`);
3. the positive operators form a closed submonoid (`isClosed_posOps`), so `e^{tδ}`
   (`t ≥ 0`, with `B = δ`) and `e^{-tδ}` (with `B = -δ`) are positive, and
   `isOrderDerivation_of_expIn` concludes.

The corollaries `rec120_unconditional`, `rec121_unconditional`, `rec102_unconditional`,
`rec103_unconditional`, `rec136_unconditional` are REC 120/121/102/103/136 with this
hypothesis discharged.
-/

set_option linter.unusedSectionVars false

open CategoryTheory
open Theses.B.Eff
open NormedSpace Filter Topology
open scoped unitInterval

namespace Papers.REC

universe u v w

/-! ## The resolvent form of the exponential in a real Banach algebra -/

section BanachResolvent

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem norm_inverse_one_sub_le (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖Ring.inverse (1 - x)‖ ≤ (1 - ‖x‖)⁻¹ := by
  rw [← geom_series_eq_inverse x hx]
  have := tsum_geometric_le_of_norm_lt_one x hx
  linarith

theorem hasDerivAt_inverse_one_sub_smul (A : 𝔸) :
    HasDerivAt (fun s : ℝ => Ring.inverse (1 - s • A)) A 0 := by
  have hl := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : 𝔸ˣ)
  have hf : HasDerivAt (fun s : ℝ => 1 - s • A) (0 - (1 : ℝ) • A) 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : 𝔸)).sub ((hasDerivAt_id (0 : ℝ)).smul_const A)
  have e : (1 - (0 : ℝ) • A) = ((1 : 𝔸ˣ) : 𝔸) := by simp
  rw [← e] at hl
  have := hl.comp_hasDerivAt (0 : ℝ) hf
  refine this.congr_deriv ?_
  simp

variable [NormedAlgebra ℚ 𝔸]

/-- The exponential formula `((1 - A/n)⁻¹)ⁿ → e^{A}`. -/
theorem tendsto_resolvent_pow (h1 : ‖(1 : 𝔸)‖ ≤ 1) (A : 𝔸) :
    Tendsto (fun n : ℕ => Ring.inverse (1 - (n : ℝ)⁻¹ • A) ^ n) atTop (𝓝 (exp A)) := by
  set g : ℝ → 𝔸 := fun s => Ring.inverse (1 - s • A) - exp (s • A) with hg
  have hd : HasDerivAt g 0 0 := by
    have := (hasDerivAt_inverse_one_sub_smul A).sub (hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0)
    refine this.congr_deriv ?_
    simp
  have hseq : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ), ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero, Nat.cast_eq_zero]
    omega
  have hlim := hd.tendsto_slope_zero.comp hseq
  have hg0 : g 0 = 0 := by simp [hg]
  set K := Real.exp (2 * ‖A‖)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (by simpa using hlim.norm.mul_const K)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * ‖A‖ ≤ N := exists_nat_ge _
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set s : ℝ := (n : ℝ)⁻¹ with hs
  have hs0 : 0 ≤ s := by positivity
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hsA : s * ‖A‖ ≤ 1 / 2 := by
    have : s * (2 * ‖A‖) ≤ s * n := mul_le_mul_of_nonneg_left (hN.trans hnN) hs0
    rw [hs, inv_mul_cancel₀ hn0.ne'] at this
    rw [hs]; linarith
  set M := Real.exp (s * (2 * ‖A‖))
  have hM : 1 ≤ M := Real.one_le_exp (by positivity)
  have hnorm : ‖s • A‖ = s * ‖A‖ := by rw [norm_smul, Real.norm_of_nonneg hs0]
  have hx0 : 0 ≤ s * ‖A‖ := by positivity
  have ha : ‖Ring.inverse (1 - s • A)‖ ≤ M := by
    refine (norm_inverse_one_sub_le h1 _ (by rw [hnorm]; linarith)).trans ?_
    rw [hnorm]
    have hpos : 0 < 1 - s * ‖A‖ := by linarith
    calc (1 - s * ‖A‖)⁻¹ ≤ 1 + 2 * (s * ‖A‖) := by
          rw [← one_div, div_le_iff₀ hpos]; nlinarith
      _ ≤ M := by
          have := Real.add_one_le_exp (s * (2 * ‖A‖))
          linarith
  have hb : ‖exp (s • A)‖ ≤ M := by
    refine (norm_exp_le_real_exp h1 _).trans (Real.exp_le_exp.2 ?_)
    rw [hnorm]; nlinarith
  have hbn : exp (s • A) ^ n = exp A := by
    rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, _root_.smul_smul, hs, mul_inv_cancel₀ hn0.ne',
      one_smul]
  have hMn : M ^ n = K := by
    rw [← Real.exp_nat_mul]; congr 1; rw [hs]; field_simp
  have key := norm_pow_sub_pow_le h1 hM ha hb n
  rw [hbn, hMn] at key
  refine key.trans (le_of_eq ?_)
  simp only [hg0, sub_zero, norm_smul, Real.norm_natCast]
  rfl

/-- If the resolvents `(1 - sB)⁻¹` lie in a closed submonoid `S` for all small `s > 0`,
so does `e^{tB}` for every `t ≥ 0`. -/
theorem exp_mem_of_resolvent (h1 : ‖(1 : 𝔸)‖ ≤ 1) {S : Submonoid 𝔸}
    (hS : IsClosed (S : Set 𝔸)) (B : 𝔸) {c : ℝ} (hc : 0 < c)
    (h : ∀ s : ℝ, 0 < s → s < c → Ring.inverse (1 - s • B) ∈ S) {t : ℝ} (ht : 0 ≤ t) :
    exp (t • B) ∈ S := by
  refine hS.mem_of_tendsto (tendsto_resolvent_pow h1 (t • B)) ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (t / c)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  refine pow_mem ?_ n
  rw [_root_.smul_smul]
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  have hn0 : (0 : ℝ) < n := by
    have := le_of_max_le_right hn; exact_mod_cast this
  rcases ht.eq_or_lt with rfl | ht'
  · simp only [mul_zero, zero_smul, sub_zero, Ring.inverse_one]
    exact one_mem S
  · refine h _ (by positivity) ?_
    rw [div_lt_iff₀ hc] at hN
    rw [inv_mul_lt_iff₀ hn0]
    nlinarith

end BanachResolvent

/-! ## `AlfsenShultzResolventCriterion` -/

section Criterion

variable {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]
  [IsOUS W]

attribute [local instance] ousNormedAddCommGroup ousNormedSpace

/-- **Alfsen–Shultz (1.82)**: if `1 - λB` carries non-positive elements to
non-positive ones and `‖λB‖ < 1`, the inverse `(1 - λB)⁻¹` is positive. -/
theorem inverse_one_sub_mem_posOps [CompleteSpace W] (T : W →L[ℝ] W) (hT : ‖T‖ < 1)
    (h : ∀ y : W, ¬ 0 ≤ y → ¬ 0 ≤ (1 - T) y) :
    Ring.inverse (1 - T) ∈ posOps (W := W) := by
  rw [NormedRing.inverse_one_sub T hT]
  intro x hx
  by_contra hy
  apply h _ hy
  have := congrArg (fun S : W →L[ℝ] W => S x) (Units.oneSub T hT).mul_inv
  simp only [Units.val_oneSub, mul_apply_eq_comp] at this
  rw [this]
  exact hx

theorem exp_mem_posOps_of_resolvent [CompleteSpace W] (B : W →L[ℝ] W) {c : ℝ} (hc : 0 < c)
    (h : ∀ l : ℝ, 0 < l → l < c → ∀ y : W, ¬ 0 ≤ y → ¬ 0 ≤ (1 - l • B) y) {t : ℝ}
    (ht : 0 ≤ t) : exp (t • B) ∈ posOps (W := W) := by
  let _ : NormedAlgebra ℚ (W →L[ℝ] W) := NormedAlgebra.restrictScalars ℚ ℝ _
  have h1 : ‖(1 : W →L[ℝ] W)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  set c' := min c (‖B‖ + 1)⁻¹
  have hc' : 0 < c' := lt_min hc (by positivity)
  refine exp_mem_of_resolvent h1 isClosed_posOps B hc' (fun s hs0 hs => ?_) ht
  have hsc : s < c := hs.trans_le (min_le_left _ _)
  have hsB : s < (‖B‖ + 1)⁻¹ := hs.trans_le (min_le_right _ _)
  have hn : ‖s • B‖ < 1 := by
    rw [norm_smul, Real.norm_of_nonneg hs0.le]
    have hB1 : (0 : ℝ) < ‖B‖ + 1 := by positivity
    have := mul_lt_mul_of_pos_right hsB hB1
    rw [inv_mul_cancel₀ hB1.ne'] at this
    nlinarith [norm_nonneg B]
  exact inverse_one_sub_mem_posOps _ hn (h s hs0 hsc)

end Criterion

/-- **Alfsen–Shultz, *State spaces*, (1.82) with the exponential formula**, proved:
the named hypothesis `AlfsenShultzResolventCriterion` of REC 120 holds.  On the Banach
algebra of bounded operators of the Banach order unit space `W`, the resolvents
`(1 ∓ λδ)⁻¹` are positive for small `λ > 0` (Neumann series and the hypothesis), and
`e^{±tδ} = lim ((1 ∓ (t/n)δ)⁻¹)ⁿ` is a norm limit of positive operators, hence
positive, the positive operators being closed. -/
theorem alfsenShultzResolventCriterion_holds : AlfsenShultzResolventCriterion.{u} := by
  intro W _ _ _ _ hOUS hB δ ⟨c0, hc0⟩ ⟨c1, hc1, h1⟩ ⟨c2, hc2, h2⟩
  have := completeSpace_of_banach hB
  let _ : NormedAddCommGroup W := ousNormedAddCommGroup
  let _ : NormedSpace ℝ W := ousNormedSpace
  let δL : W →L[ℝ] W := δ.mkContinuous c0 hc0
  have hδL : ∀ v, δL v = δ v := fun _ => rfl
  refine isOrderDerivation_of_expIn hδL fun t => ?_
  rcases le_or_gt 0 t with ht | ht
  · refine exp_mem_posOps_of_resolvent δL hc1 (fun l hl0 hl y hy => ?_) ht
    have := h1 l hl0 hl y hy
    simpa [hδL] using this
  · have e : t • δL = (-t) • (-δL) := by rw [neg_smul_neg]
    rw [e]
    refine exp_mem_posOps_of_resolvent (-δL) hc2 (fun l hl0 hl y hy => ?_) (by linarith)
    have := h2 l hl0 hl y hy
    simpa [hδL, sub_eq_add_neg] using this

/-! ## REC 120, 121, 102, 103, 136 with the hypothesis discharged -/

section Unconditional

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

/-- **REC 120** (`prop:assert-is-derivation`, short.tex:2175, Proposition): `rec120`
with `AlfsenShultzResolventCriterion` discharged; only REC 119 remains assumed. -/
theorem rec120_unconditional (σs : ScalarSplit C) (h119 : WeteringStateOrderLemma C)
    {A : C} (p : CPt σs A) (hp : IsSharp p.1) : IsOrderDerivation (VA σs A) (Dop σs p) :=
  rec120 σs alfsenShultzResolventCriterion_holds h119 p hp

/-- **REC 121** (`prop:is-JB-algebra`, short.tex:2226, Proposition): `rec121` with
`AlfsenShultzResolventCriterion` discharged; only REC 119 remains assumed. -/
theorem rec121_unconditional (σs : ScalarSplit C) (h119 : WeteringStateOrderLemma C) (A : C) :
    ∃ _ : Mul (VA σs A), JBAlgebra (VA σs A) ∧
      ∀ q : CPt σs A, IsSharp q.1 → ∀ w, GP.gmap q * w = (2⁻¹ : ℝ) • (w + Dop σs q w) :=
  rec121 σs alfsenShultzResolventCriterion_holds h119 A

/-- **REC 102** (`thm:JB-embedding`, short.tex:1869, Theorem): `rec102` with
`AlfsenShultzResolventCriterion` discharged; only REC 119 remains assumed. -/
theorem rec102_unconditional (h119 : WeteringStateOrderLemma C) :
    ∃ σs : ScalarSplit C,
      Nonempty (C ≌ (dcSplitting σs separatedByStates).ε.Part ×
        (dcSplitting σs separatedByStates).ε'.Part) ∧
      (∀ P : (dcSplitting σs separatedByStates).ε.Part, Nonempty (CBAOn (Pred P))) ∧
      (∀ P : (dcSplitting σs separatedByStates).ε'.Part,
        ∃ _ : Mul (VA σs P.obj.X), JBAlgebra (VA σs P.obj.X) ∧
          IsDirectedCompleteOUS (VA σs P.obj.X) ∧
          ∃ e : Pred P ≃ Set.Icc (0 : VA σs P.obj.X) (ouUnit (VA σs P.obj.X)),
            (∀ a b : Pred P, a ≼ b ↔ (e a : VA σs P.obj.X) ≤ e b) ∧
            (∀ (a b : Pred P) (h : Perp a b), (e (ovee a b h) : VA σs P.obj.X) = e a + e b) ∧
            (e (truth P) : VA σs P.obj.X) = ouUnit (VA σs P.obj.X)) ∧
      ((rec102_cbaFunctor σs).Faithful ∧
          (rec102_jbFunctor σs alfsenShultzResolventCriterion_holds h119).Faithful ↔
        SeparatingPredicates C) :=
  rec102 alfsenShultzResolventCriterion_holds h119

/-- **REC 103** (`thm:JBW-CBA`, short.tex:1874, Theorem): `rec103` with
`AlfsenShultzResolventCriterion` discharged; only REC 119 remains assumed. -/
theorem rec103_unconditional (h119 : WeteringStateOrderLemma C) (hirr : IsIrreducible (Scal C)) :
    (∃ hB : ∀ A : C, CBAOn (Pred A), (cbaPredFunctor hB).Faithful ↔ SeparatingPredicates C) ∨
    (∃ (σs : ScalarSplit C) (hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _
        (jbMul σs alfsenShultzResolventCriterion_holds h119 A)),
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : VA σs A) (ouUnit (VA σs A)),
        (∀ a b : Pred A, a ≼ b ↔ (e a : VA σs A) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b), (e (ovee a b h) : VA σs A) = e a + e b) ∧
        (e (truth A) : VA σs A) = ouUnit (VA σs A)) ∧
      ((rec103_jbwFunctor alfsenShultzResolventCriterion_holds h119 σs hJBW).Faithful ↔
        SeparatingPredicates C)) :=
  rec103 alfsenShultzResolventCriterion_holds h119 hirr

open MonoidalCategory in
/-- **REC 136** (`thm:JW-algebra`, short.tex:2409, Theorem): `rec136` with
`AlfsenShultzResolventCriterion` discharged.  Remaining named hypotheses: REC 119
(`h119`), REC 52 (`hHOS`), REC 55 (`hSh`), REC 132 (`hAS4`). -/
theorem rec136_unconditional [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C] (h119 : WeteringStateOrderLemma C)
    (hHOS : HancheOlsenStormerDecomposition.{v}) (hSh : ShultzExceptionalStructure.{v})
    (hAS4 : AlfsenShultzFourExchangeable.{v}) (hirr : IsIrreducible (Scal C))
    (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136 alfsenShultzResolventCriterion_holds h119 hHOS hSh hAS4 hirr h01

end Unconditional

end Papers.REC

#print axioms Papers.REC.alfsenShultzResolventCriterion_holds
#print axioms Papers.REC.rec136_unconditional
