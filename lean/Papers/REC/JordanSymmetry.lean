import Papers.REC.Reconstruction

/-!
# REC 121: the Jordan symmetry `[D_p, D_q] 1 = 0`, proved

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707, `short.tex` §5.4, `prop:is-JB-algebra` (line 2226).

The named hypothesis `AlfsenShultzJordanFromDerivations` (REC's transplant of
Alfsen–Shultz, *Geometry*, 9.43/9.48) carries, among other things, the symmetry
`T_p q = T_q p` (`T_r := ½(1 + D_r)`) of the family of compressions: the print
obtains it by citing 9.48 outside its hypotheses.  Here it is *proved* from the
Prop's own hypotheses (research note `docs/research/as948-lemmaM.md`, with its
Review), and the named hypothesis shrinks to `AlfsenShultzJordanTransplant`: the same
statement with the symmetry as an extra hypothesis on the family (what remains of 9.43:
the product on the span, continuity, the Jordan identity, `0 ≤ a² ≤ 1`).  That
remainder is now proved too (`jb_of_chainDense`, `JordanFromChains.lean`, from the
chain density of `V_A`), so REC 121 (`Reconstruction2.lean`) takes neither Prop.

## Contents

1. `IsOrderDerivation.lie`: on a Banach order unit space the commutator of two order
   derivations is an order derivation (the fact the print cites at short.tex:2233;
   Alfsen–Shultz, *State spaces*, commutator of order derivations).  *Proved*, not
   named: on `B(W)` (the order-unit norm makes `W` a Banach space) the set of `A` with
   `e^{tA}` positive for all `t` is closed (the cone is closed), closed under
   scalars, under conjugation by `e^{sX}`, and under sums (Lie–Trotter product
   formula, `tendsto_trotter`); `[X,Y]` is the norm limit of
   `s⁻¹(e^{sX} Y e^{-sX} − Y)`.
2. `lemmaP`: for an order derivation `δ`, a positive map `Φ` and `a ≥ 0` with
   `Φ a = 0`, `Φ (δ a) = 0`.
3. `jordan_symmetry`: for the family of the Prop, with `D_i := U_i − U_{c i}` and
   `y := (e_j + D_i e_j) − (e_i + D_j e_i)`, the corner lemmas give `D_i y = D_j y = 0`;
   so `δ := [D_i, D_j]` has `δ 1 = 2y`, `δ y = 0`, `e^{tδ} 1 = 1 + 2t y ≥ 0` for all
   `t`, and `y = 0` (Archimedean).
4. `AlfsenShultzJordanTransplant`, `alfsenShultzJordanFromDerivations_of_transplant`:
   the smaller named hypothesis, now unused (kept as a documented open `Prop`).
   `rec102'`, `rec103'`, `rec136'` moved to `Monoidal.lean`; they are now REC 102/103/136
   themselves, with no A–S 9.4x hypothesis.
-/

set_option linter.unusedSectionVars false

open CategoryTheory
open Theses.B.Eff
open NormedSpace Filter Topology
open scoped unitInterval

namespace Papers.REC

universe u v w

/-! ## Order derivations in a real Banach algebra -/

section BanachLie

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem norm_exp_le_real_exp (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have hs := exp_series_hasSum_exp' (𝕂 := ℝ) x
  have hr := exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  rw [← Real.exp_eq_exp_ℝ] at hr
  refine hs.norm_le_of_bounded hr fun n => ?_
  rw [norm_smul, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using h1
  · exact norm_pow_le' x hn

theorem norm_pow_le_of_le (h1 : ‖(1 : 𝔸)‖ ≤ 1) {a : 𝔸} {M : ℝ} (hM : 1 ≤ M) (ha : ‖a‖ ≤ M)
    (n : ℕ) : ‖a ^ n‖ ≤ M ^ n := by
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih ha (norm_nonneg _) (by positivity))

theorem norm_pow_sub_pow_le (h1 : ‖(1 : 𝔸)‖ ≤ 1) {a b : 𝔸} {M : ℝ} (hM : 1 ≤ M)
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ n * ‖a - b‖ * M ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by
      rw [pow_succ', pow_succ', mul_sub, sub_mul]; abel
    have hMn : 0 ≤ M ^ n := by positivity
    have hd : 0 ≤ ‖a - b‖ := norm_nonneg _
    have hbn := norm_pow_le_of_le h1 hM hb n
    calc ‖a ^ (n + 1) - b ^ (n + 1)‖
        ≤ ‖a‖ * ‖a ^ n - b ^ n‖ + ‖a - b‖ * ‖b ^ n‖ := by
          rw [e]; exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ M * (n * ‖a - b‖ * M ^ n) + ‖a - b‖ * M ^ n :=
          add_le_add (mul_le_mul ha ih (norm_nonneg _) (by linarith))
            (mul_le_mul_of_nonneg_left hbn hd)
      _ ≤ ((n + 1 : ℕ) : ℝ) * ‖a - b‖ * M ^ (n + 1) := by
          have := mul_nonneg (mul_nonneg hd hMn) (sub_nonneg.2 hM)
          push_cast; rw [pow_succ]; nlinarith

/-- `A` generates a one-parameter group inside the submonoid `S`. -/
def ExpIn (S : Submonoid 𝔸) (A : 𝔸) : Prop := ∀ t : ℝ, exp (t • A) ∈ S

theorem ExpIn.smul {S : Submonoid 𝔸} {A : 𝔸} (h : ExpIn S A) (r : ℝ) : ExpIn S (r • A) :=
  fun t => by rw [_root_.smul_smul]; exact h _

variable [NormedAlgebra ℚ 𝔸]

theorem exp_mul_exp_neg (x : 𝔸) : exp x * exp (-x) = 1 := by
  rw [← exp_add_of_commute (Commute.refl x).neg_right, add_neg_cancel, exp_zero]

theorem exp_neg_mul_exp (x : 𝔸) : exp (-x) * exp x = 1 := by
  rw [← exp_add_of_commute (Commute.refl x).neg_left, neg_add_cancel, exp_zero]

/-- The Lie–Trotter product formula `(e^{A/n} e^{B/n})ⁿ → e^{A+B}`. -/
theorem tendsto_trotter (h1 : ‖(1 : 𝔸)‖ ≤ 1) (A B : 𝔸) :
    Tendsto (fun n : ℕ => (exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n) atTop
      (𝓝 (exp (A + B))) := by
  set g : ℝ → 𝔸 := fun s => exp (s • A) * exp (s • B) - exp (s • (A + B)) with hg
  have hd : HasDerivAt g 0 0 := by
    have := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) B 0)).sub (hasDerivAt_exp_smul_const (𝕂 := ℝ) (A + B) 0)
    refine this.congr_deriv ?_
    simp
  have hseq : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ), ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero, Nat.cast_eq_zero]
    omega
  have hlim := hd.tendsto_slope_zero.comp hseq
  have hg0 : g 0 = 0 := by simp [hg]
  set K := Real.exp (‖A‖ + ‖B‖)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (by simpa using hlim.norm.mul_const K)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set s : ℝ := (n : ℝ)⁻¹ with hs
  have hs0 : 0 ≤ s := by positivity
  set M := Real.exp (s * (‖A‖ + ‖B‖))
  have hM : 1 ≤ M := Real.one_le_exp (by positivity)
  have hnorm : ∀ C : 𝔸, ‖s • C‖ = s * ‖C‖ := fun C => by
    rw [norm_smul, Real.norm_of_nonneg hs0]
  have ha : ‖exp (s • A) * exp (s • B)‖ ≤ M := by
    refine (norm_mul_le _ _).trans ?_
    refine (mul_le_mul (norm_exp_le_real_exp h1 _) (norm_exp_le_real_exp h1 _) (norm_nonneg _)
      (Real.exp_pos _).le).trans ?_
    rw [← Real.exp_add, hnorm, hnorm]
    exact Real.exp_le_exp.2 (le_of_eq (mul_add _ _ _).symm)
  have hb : ‖exp (s • (A + B))‖ ≤ M := by
    refine (norm_exp_le_real_exp h1 _).trans (Real.exp_le_exp.2 ?_)
    rw [hnorm]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hs0
  have hbn : exp (s • (A + B)) ^ n = exp (A + B) := by
    rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, _root_.smul_smul, hs, mul_inv_cancel₀ hn0.ne',
      one_smul]
  have hMn : M ^ n = K := by
    rw [← Real.exp_nat_mul]; congr 1; rw [hs]; field_simp
  have key := norm_pow_sub_pow_le h1 hM ha hb n
  rw [hbn, hMn] at key
  refine key.trans (le_of_eq ?_)
  simp only [hg0, sub_zero, norm_smul, Real.norm_natCast]
  rfl

variable {S : Submonoid 𝔸}

theorem ExpIn.add (h1 : ‖(1 : 𝔸)‖ ≤ 1) (hS : IsClosed (S : Set 𝔸)) {A B : 𝔸}
    (hA : ExpIn S A) (hB : ExpIn S B) : ExpIn S (A + B) := fun t => by
  rw [smul_add]
  refine hS.mem_of_tendsto (tendsto_trotter h1 (t • A) (t • B)) (Eventually.of_forall fun n => ?_)
  rw [_root_.smul_smul, _root_.smul_smul]
  exact pow_mem (mul_mem (hA _) (hB _)) n

theorem ExpIn.conj {X Y : 𝔸} (hX : ExpIn S X) (hY : ExpIn S Y) (s : ℝ) :
    ExpIn S (exp (s • X) * Y * exp (-(s • X))) := fun t => by
  let u : 𝔸ˣ := ⟨exp (s • X), exp (-(s • X)), exp_mul_exp_neg _, exp_neg_mul_exp _⟩
  have hu : (u : 𝔸) = exp (s • X) := rfl
  have hu' : ((u⁻¹ : 𝔸ˣ) : 𝔸) = exp (-(s • X)) := rfl
  have e : t • (exp (s • X) * Y * exp (-(s • X))) = (u : 𝔸) * (t • Y) * ((u⁻¹ : 𝔸ˣ) : 𝔸) := by
    rw [hu, hu', mul_smul_comm, smul_mul_assoc]
  rw [e, exp_units_conj, hu, hu']
  refine mul_mem (mul_mem (hX s) (hY t)) ?_
  have := hX (-s); rwa [neg_smul] at this

theorem isClosed_expIn (hS : IsClosed (S : Set 𝔸)) : IsClosed {A : 𝔸 | ExpIn S A} := by
  have : {A : 𝔸 | ExpIn S A} = ⋂ t : ℝ, (fun A : 𝔸 => exp (t • A)) ⁻¹' (S : Set 𝔸) := by
    ext A; simp [ExpIn]
  rw [this]
  exact isClosed_iInter fun t => hS.preimage (exp_continuous.comp (continuous_const_smul t))

/-- The commutator of two generators of one-parameter groups in a closed submonoid is
again one: `[X, Y]` is the limit of `s⁻¹ (e^{sX} Y e^{-sX} − Y)`. -/
theorem ExpIn.lie (h1 : ‖(1 : 𝔸)‖ ≤ 1) (hS : IsClosed (S : Set 𝔸)) {X Y : 𝔸}
    (hX : ExpIn S X) (hY : ExpIn S Y) : ExpIn S (X * Y - Y * X) := by
  set h : ℝ → 𝔸 := fun s => exp (s • X) * Y * exp (s • -X) with hh
  have hd : HasDerivAt h (X * Y - Y * X) 0 := by
    have := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).mul_const Y).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0)
    refine this.congr_deriv ?_
    simp [sub_eq_add_neg]
  have h0 : h 0 = Y := by simp [hh]
  refine (isClosed_expIn hS).mem_of_tendsto hd.tendsto_slope_zero
    (eventually_nhdsWithin_of_forall fun s _ => ?_)
  show ExpIn S _
  rw [h0, zero_add, smul_sub, sub_eq_add_neg, ← neg_smul]
  have hc : ExpIn S (h s) := by
    have := ExpIn.conj hX hY s
    simpa [hh, smul_neg] using this
  exact ExpIn.add h1 hS (hc.smul _) (hY.smul _)

end BanachLie

/-! ## The order-unit norm as a Banach space structure -/

section OUSNormed

variable {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]

theorem ousNorm_smul_eq (r : ℝ) (x : W) : ousNorm W (r • x) = |r| * ousNorm W x := by
  refine le_antisymm (ousNorm_smul_le r x) ?_
  rcases eq_or_ne r 0 with rfl | hr
  · simp [ousNorm_nonneg_rc]
  · have := ousNorm_smul_le r⁻¹ (r • x)
    rw [_root_.smul_smul, inv_mul_cancel₀ hr, one_smul, abs_inv] at this
    have hr' : 0 < |r| := abs_pos.2 hr
    calc |r| * ousNorm W x ≤ |r| * (|r|⁻¹ * ousNorm W (r • x)) :=
          mul_le_mul_of_nonneg_left this hr'.le
      _ = ousNorm W (r • x) := by field_simp

/-- The order-unit norm of REC 41, as a `Norm` (for local use). -/
@[reducible] noncomputable def ousNormInst : Norm W := ⟨ousNorm W⟩

variable [IsOUS W]

/-- On an order unit space in the sense of REC 41 the order-unit norm is a norm. -/
@[reducible] noncomputable def ousNormedAddCommGroup : NormedAddCommGroup W :=
  letI := (ousNormInst : Norm W)
  NormedAddCommGroup.ofCore (𝕜 := ℝ)
    { norm_nonneg := fun x => ousNorm_nonneg_rc x
      norm_smul := fun r x => by
        show ousNorm W (r • x) = ‖r‖ * ousNorm W x
        rw [ousNorm_smul_eq, Real.norm_eq_abs]
      norm_triangle := fun x y => ousNorm_add_le x y
      norm_eq_zero_iff := fun x => ⟨IsOUS.norm_eq_zero x, fun h => by
        subst h; exact ousNorm_zero'⟩ }

attribute [local instance] ousNormedAddCommGroup

@[reducible] noncomputable def ousNormedSpace : NormedSpace ℝ W where
  norm_smul_le r x := (ousNorm_smul_eq r x).le

attribute [local instance] ousNormedSpace

theorem norm_eq_ousNorm (x : W) : ‖x‖ = ousNorm W x := rfl

theorem completeSpace_of_banach (hB : IsBanachOUS W) : CompleteSpace W := by
  refine Metric.complete_of_cauchySeq_tendsto fun s hs => ?_
  obtain ⟨v, hv⟩ := hB s fun ε hε => by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hs ε hε
    exact ⟨N, fun m hm n hn => by have := hN m hm n hn; rwa [dist_eq_norm] at this⟩
  exact ⟨v, Metric.tendsto_atTop.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hv ε hε
    exact ⟨N, fun n hn => by rw [dist_eq_norm]; exact hN n hn⟩⟩

theorem ousTendsto_iff (s : ℕ → W) (w : W) : OUSTendsto W s w ↔ Tendsto s atTop (𝓝 w) := by
  rw [Metric.tendsto_atTop]
  simp only [dist_eq_norm]
  exact Iff.rfl

theorem isClosed_nonneg : IsClosed {w : W | 0 ≤ w} := by
  refine isClosed_of_closure_subset fun w hw => ?_
  refine IsOUS.cone_closed w fun ε hε => ?_
  obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.1 hw ε hε
  exact ⟨b, hb, by rw [dist_eq_norm] at hd; exact hd⟩

/-- The positive operators, a submonoid of `B(W)`. -/
noncomputable def posOps : Submonoid (W →L[ℝ] W) where
  carrier := {T | ∀ v, 0 ≤ v → 0 ≤ T v}
  one_mem' := fun _ hv => hv
  mul_mem' := fun hS hT v hv => hS _ (hT v hv)

theorem isClosed_posOps : IsClosed (posOps (W := W) : Set (W →L[ℝ] W)) := by
  have : (posOps (W := W) : Set (W →L[ℝ] W)) =
      ⋂ v : W, ⋂ (_ : 0 ≤ v), (fun T : W →L[ℝ] W => T v) ⁻¹' {w | 0 ≤ w} := by
    ext T
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    isClosed_nonneg.preimage (ContinuousLinearMap.apply ℝ W v).continuous

theorem pow_apply_of_eq {δ : W →ₗ[ℝ] W} {δL : W →L[ℝ] W} (hδL : ∀ v, δL v = δ v) (k : ℕ)
    (v : W) : (δL ^ k) v = (δ ^ k) v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, mul_apply_eq_comp, Module.End.mul_apply, hδL, ih]

theorem tendsto_expPartialSum [CompleteSpace W] {δ : W →ₗ[ℝ] W} {δL : W →L[ℝ] W}
    (hδL : ∀ v, δL v = δ v) (t : ℝ) (v : W) :
    Tendsto (expPartialSum W δ t v) atTop (𝓝 (exp (t • δL) v)) := by
  have hs := exp_series_hasSum_exp' (𝕂 := ℝ) (t • δL)
  have hv := ((ContinuousLinearMap.apply ℝ W v).hasSum hs).tendsto_sum_nat
  refine Tendsto.congr (fun n => ?_) hv
  symm
  unfold expPartialSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.apply_apply, _root_.smul_apply, smul_pow,
    _root_.smul_apply, pow_apply_of_eq hδL, _root_.smul_smul, div_eq_inv_mul]

theorem IsOrderDerivation.expIn [CompleteSpace W] {δ : W →ₗ[ℝ] W}
    (hδ : IsOrderDerivation W δ) {δL : W →L[ℝ] W} (hδL : ∀ v, δL v = δ v) :
    ExpIn posOps δL := by
  intro t
  obtain ⟨e, hconv, hiso⟩ := hδ.2 t
  have heq : ∀ v, e v = exp (t • δL) v := fun v =>
    tendsto_nhds_unique ((ousTendsto_iff _ _).1 (hconv v)) (tendsto_expPartialSum hδL t v)
  intro v hv
  rw [← heq]
  have := (hiso 0 v).1 hv
  rwa [map_zero] at this

theorem isOrderDerivation_of_expIn [CompleteSpace W] {δ : W →ₗ[ℝ] W} {δL : W →L[ℝ] W}
    (hδL : ∀ v, δL v = δ v) (h : ExpIn posOps δL) : IsOrderDerivation W δ := by
  let _ : NormedAlgebra ℚ (W →L[ℝ] W) := NormedAlgebra.restrictScalars ℚ ℝ _
  refine ⟨⟨‖δL‖, fun v => ?_⟩, fun t => ?_⟩
  · rw [← hδL]; exact δL.le_opNorm v
  · have h1 : exp (t • δL) * exp ((-t) • δL) = 1 := by rw [neg_smul]; exact exp_mul_exp_neg _
    have h2 : exp ((-t) • δL) * exp (t • δL) = 1 := by rw [neg_smul]; exact exp_neg_mul_exp _
    have h1' : ∀ w, exp (t • δL) (exp ((-t) • δL) w) = w := fun w =>
      congrArg (fun T : W →L[ℝ] W => T w) h1
    have h2' : ∀ w, exp ((-t) • δL) (exp (t • δL) w) = w := fun w =>
      congrArg (fun T : W →L[ℝ] W => T w) h2
    let e : W ≃ₗ[ℝ] W := LinearEquiv.ofLinearMap (exp (t • δL)).toLinearMap
      (exp ((-t) • δL)).toLinearMap (LinearMap.ext h1') (LinearMap.ext h2')
    have he : ∀ w, e w = exp (t • δL) w := fun _ => rfl
    refine ⟨e, fun v => ?_, fun v w => ⟨fun hvw => ?_, fun hvw => ?_⟩⟩
    · rw [he, ousTendsto_iff]; exact tendsto_expPartialSum hδL t v
    · have := h t (w - v) (sub_nonneg.2 hvw)
      rw [map_sub] at this
      rw [he, he]; exact sub_nonneg.1 this
    · have := h (-t) (e w - e v) (sub_nonneg.2 hvw)
      rw [map_sub, he, he, h2', h2'] at this
      exact sub_nonneg.1 this

/-- **The commutator of two order derivations is an order derivation** (the fact the
print cites at short.tex:2233, Alfsen–Shultz *State spaces*; numbering unverified), on
a Banach order unit space in the sense of REC 41.  Proved: `ExpIn.lie` in `B(W)`. -/
theorem IsOrderDerivation.lie (hB : IsBanachOUS W) {X Y : W →ₗ[ℝ] W}
    (hX : IsOrderDerivation W X) (hY : IsOrderDerivation W Y) :
    IsOrderDerivation W (X * Y - Y * X) := by
  have := completeSpace_of_banach hB
  let _ : NormedAlgebra ℚ (W →L[ℝ] W) := NormedAlgebra.restrictScalars ℚ ℝ _
  obtain ⟨cX, hcX⟩ := hX.1
  obtain ⟨cY, hcY⟩ := hY.1
  let XL := X.mkContinuous cX hcX
  let YL := Y.mkContinuous cY hcY
  have h1 : ‖(1 : W →L[ℝ] W)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  refine isOrderDerivation_of_expIn (δL := XL * YL - YL * XL) (fun v => rfl)
    (ExpIn.lie h1 isClosed_posOps (hX.expIn fun _ => rfl) (hY.expIn fun _ => rfl))

/-- A positive map is bounded by `‖Φ 1‖`. -/
theorem positive_bound (Φ : W →ₗ[ℝ] W) (hΦ : ∀ v, 0 ≤ v → 0 ≤ Φ v) (v : W) :
    ousNorm W (Φ v) ≤ ousNorm W (Φ (ouUnit W)) * ousNorm W v := by
  set k := ousNorm W (Φ (ouUnit W))
  have hk0 : 0 ≤ k := ousNorm_nonneg_rc _
  have hΦ1 := ousNorm_bounds_le (Φ (ouUnit W))
  have hv0 := ousNorm_nonneg_rc v
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set l := ousNorm W v + ε / (k + 1) with hl
  have hεk : 0 < ε / (k + 1) := by positivity
  have hl0 : 0 ≤ l := by positivity
  obtain ⟨b1, b2⟩ := ousNorm_bounds (v := v) (ε := l) (by linarith)
  have hlk : l • Φ (ouUnit W) ≤ (l * k) • ouUnit W := by
    rw [← _root_.smul_smul]; exact smul_le_smul_of_nonneg_left hΦ1.2 hl0
  have u1 : Φ v ≤ (l * k) • ouUnit W := by
    have := hΦ _ (sub_nonneg.2 b2)
    rw [map_sub, map_smul] at this
    exact (sub_nonneg.1 this).trans hlk
  have u2 : -((l * k) • ouUnit W) ≤ Φ v := by
    have h0 : 0 ≤ v + l • ouUnit W := by
      have := sub_nonneg.2 b1; rwa [sub_neg_eq_add] at this
    have := hΦ _ h0
    rw [map_add, map_smul] at this
    have h3 : -(l • Φ (ouUnit W)) ≤ Φ v := by
      rw [← sub_nonneg, sub_neg_eq_add]; exact this
    exact (neg_le_neg hlk).trans h3
  have := ousNorm_le_rc (mul_nonneg hl0 hk0) u2 u1
  have e : l * k = k * ousNorm W v + k * (ε / (k + 1)) := by rw [hl]; ring
  have hkε : k * (ε / (k + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- **Lemma P** (research note as948-lemmaM §1): for an order derivation `δ`, a
positive map `Φ` and `a ≥ 0` with `Φ a = 0`, also `Φ (δ a) = 0`.  From the slope of
`t ↦ Φ (e^{tδ} a) ≥ 0` at `0` from both sides; no states are used. -/
theorem lemmaP (hB : IsBanachOUS W) {δ : W →ₗ[ℝ] W} (hδ : IsOrderDerivation W δ)
    (Φ : W →ₗ[ℝ] W) (hΦ : ∀ v, 0 ≤ v → 0 ≤ Φ v) {a : W} (ha : 0 ≤ a) (hΦa : Φ a = 0) :
    Φ (δ a) = 0 := by
  have := completeSpace_of_banach hB
  obtain ⟨c, hc⟩ := hδ.1
  let δL := δ.mkContinuous c hc
  let ΦL := Φ.mkContinuous _ (positive_bound Φ hΦ)
  have hpos := hδ.expIn (δL := δL) fun _ => rfl
  set φ : ℝ → W := fun t => ΦL (exp (t • δL) a) with hφ
  have hd : HasDerivAt φ (Φ (δ a)) 0 := by
    have h1 := (hasDerivAt_const (0 : ℝ) ΦL).clm_apply
      ((hasDerivAt_exp_smul_const (𝕂 := ℝ) δL 0).clm_apply (hasDerivAt_const (0 : ℝ) a))
    refine h1.congr_deriv ?_
    simp [ΦL, δL]
  have hφ0 : φ 0 = 0 := by simp [hφ, ΦL, hΦa]
  have hφpos : ∀ t, 0 ≤ φ t := fun t => hΦ _ (hpos t a ha)
  apply le_antisymm
  · have hcl : IsClosed {w : W | w ≤ 0} := by
      have := (isClosed_nonneg (W := W)).preimage continuous_neg
      simpa [Set.preimage, neg_nonneg] using this
    refine hcl.mem_of_tendsto hd.tendsto_slope_zero_left
      (eventually_nhdsWithin_of_forall fun t (ht : t < 0) => ?_)
    show t⁻¹ • (φ (0 + t) - φ 0) ≤ 0
    rw [hφ0, sub_zero, zero_add]
    have : 0 ≤ (-t⁻¹) • φ t := ou_smul_nonneg (by simp [ht.le]) (hφpos t)
    rw [neg_smul] at this
    exact neg_nonneg.1 this
  · refine isClosed_nonneg.mem_of_tendsto hd.tendsto_slope_zero_right
      (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_)
    show 0 ≤ t⁻¹ • (φ (0 + t) - φ 0)
    rw [hφ0, sub_zero, zero_add]
    exact ou_smul_nonneg (inv_nonneg.2 ht.le) (hφpos t)

end OUSNormed

/-! ## The symmetry of REC 121 -/

section Symmetry

variable {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]
  [IsOUS W]

/-- **REC 121, the symmetry step** (short.tex:2233–2235; research note as948-lemmaM with
its Review).  For the family of compressions of `AlfsenShultzJordanFromDerivations`,
`T_i e_j = T_j e_i` with `T_r = ½(1 + D_r)`, i.e. `e_j + D_i e_j = e_i + D_j e_i`.
The print derives this from Alfsen–Shultz 9.48, outside its hypotheses; here it follows
from the commutator of order derivations (`IsOrderDerivation.lie`) and Lemma P: with
`y := (e_j + D_i e_j) − (e_i + D_j e_i)` the corner lemmas give `D_i y = D_j y = 0`, so
`δ := [D_i, D_j]` has `δ 1 = 2y`, `δ y = 0`, hence `e^{tδ} 1 = 1 + 2t y ≥ 0` for all
`t`, and `y = 0`.  Neither density, directed completeness nor the kernel condition is
used. -/
theorem jordan_symmetry (hB : IsBanachOUS W) {ι : Type*} (e : ι → W)
    (U : ι → W →ₗ[ℝ] W) (c : ι → ι) (hinj : Function.Injective e)
    (hc : ∀ i, e (c i) = ouUnit W - e i)
    (hU : ∀ i, (∀ w, 0 ≤ w → 0 ≤ U i w) ∧ U i (ouUnit W) = e i ∧ U i ∘ₗ U i = U i ∧
      U i ∘ₗ U (c i) = 0)
    (hD : ∀ i, IsOrderDerivation W (U i - U (c i))) (i j : ι) :
    e j + (U i - U (c i)) (e j) = e i + (U j - U (c j)) (e i) := by
  set one := ouUnit W with hone
  have hcc : ∀ i, c (c i) = i := fun i => hinj (by rw [hc, hc]; abel)
  have hpos : ∀ i w, 0 ≤ w → 0 ≤ U i w := fun i => (hU i).1
  have hU1 : ∀ i, U i one = e i := fun i => (hU i).2.1
  have hUU : ∀ i w, U i (U i w) = U i w := fun i w => LinearMap.congr_fun (hU i).2.2.1 w
  have hUc : ∀ i w, U i (U (c i) w) = 0 := fun i w => LinearMap.congr_fun (hU i).2.2.2 w
  have hcU : ∀ i w, U (c i) (U i w) = 0 := fun i w => by
    have := hUc (c i) w; rwa [hcc] at this
  have he0 : ∀ i, 0 ≤ e i := fun i => hU1 i ▸ hpos i _ ou_unit_nonneg
  have hUe : ∀ i, U i (e i) = e i := fun i => by rw [← hU1, hUU]
  have hcUe : ∀ i, U (c i) (e i) = 0 := fun i => by rw [← hU1, hcU]
  have hUce : ∀ i, U i (e (c i)) = 0 := fun i => by rw [← hU1 (c i), hUc]
  have hD1 : ∀ i, (U i - U (c i)) one = e i - e (c i) := fun i => by
    rw [LinearMap.sub_apply, hU1, hU1]
  let y : ι → ι → W := fun i j =>
    e j + (U i - U (c i)) (e j) - (e i + (U j - U (c j)) (e i))
  have hyanti : ∀ i j, y j i = -y i j := fun i j => by simp only [y]; abel
  -- the corner lemmas
  have corner : ∀ i j, U i (y i j) = 0 ∧ U (c i) (y i j) = 0 := by
    intro i j
    have hA : U (c i) ((U j - U (c j)) (e i)) = 0 :=
      lemmaP hB (hD j) (U (c i)) (hpos _) (he0 i) (hcUe i)
    have hB' : U i ((U j - U (c j)) (e (c i))) = 0 :=
      lemmaP hB (hD j) (U i) (hpos _) (he0 (c i)) (hUce i)
    have hsplit : e i = one - e (c i) := by rw [hc]; abel
    have h1 : U i ((U j - U (c j)) (e i)) = U i (e j) + U i (e j) - e i := by
      calc U i ((U j - U (c j)) (e i))
          = U i ((U j - U (c j)) one) - U i ((U j - U (c j)) (e (c i))) := by
            conv_lhs => rw [hsplit]
            rw [map_sub, map_sub]
        _ = U i (e j - (one - e j)) := by rw [hB', sub_zero, hD1, hc]
        _ = U i (e j) + U i (e j) - e i := by rw [map_sub, map_sub, hU1]; abel
    constructor
    · show U i (e j + (U i - U (c i)) (e j) - (e i + (U j - U (c j)) (e i))) = 0
      rw [map_sub, map_add, map_add, h1, LinearMap.sub_apply, map_sub, hUU, hUc, hUe]
      abel
    · show U (c i) (e j + (U i - U (c i)) (e j) - (e i + (U j - U (c j)) (e i))) = 0
      rw [map_sub, map_add, map_add, hA, LinearMap.sub_apply, map_sub, hcU, hcUe, hUU]
      abel
  have hDy : ∀ i j, (U i - U (c i)) (y i j) = 0 := fun i j => by
    rw [LinearMap.sub_apply, (corner i j).1, (corner i j).2, sub_zero]
  have hDy' : (U j - U (c j)) (y i j) = 0 := by
    rw [← neg_neg (y i j), ← hyanti, map_neg, hDy, neg_zero]
  -- the commutator
  set δ : W →ₗ[ℝ] W := (U i - U (c i)) * (U j - U (c j)) - (U j - U (c j)) * (U i - U (c i))
    with hδdef
  have hδ : IsOrderDerivation W δ := (hD i).lie hB (hD j)
  have hδy : δ (y i j) = 0 := by
    rw [hδdef, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hDy', hDy,
      map_zero, map_zero, sub_zero]
  have hδ1 : δ one = y i j + y i j := by
    have e1 : (U i - U (c i)) ((U j - U (c j)) one) =
        (U i - U (c i)) (e j) + (U i - U (c i)) (e j) - e i + e (c i) := by
      rw [hD1 j, hc j, map_sub, map_sub, hD1 i]; abel
    have e2 : (U j - U (c j)) ((U i - U (c i)) one) =
        (U j - U (c j)) (e i) + (U j - U (c j)) (e i) - e j + e (c j) := by
      rw [hD1 i, hc i, map_sub, map_sub, hD1 j]; abel
    rw [hδdef, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, e1, e2, hc i,
      hc j]
    simp only [y]; abel
  -- `e^{tδ} 1 = 1 + t δ 1`
  have hpow : ∀ k, (δ ^ (k + 2)) one = 0 := fun k => by
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hδ1, map_add, hδy,
      add_zero, map_zero]
  have hsum : ∀ t m, expPartialSum W δ t one (m + 2) = one + t • δ one := by
    intro t m
    induction m with
    | zero => simp [expPartialSum, Finset.sum_range_succ]
    | succ m ih =>
      unfold expPartialSum at ih ⊢
      rw [show m + 1 + 2 = (m + 2) + 1 by ring, Finset.sum_range_succ, ih, hpow, smul_zero,
        add_zero]
  have hnonneg : ∀ t : ℝ, 0 ≤ one + t • δ one := by
    intro t
    obtain ⟨E, hconv, hiso⟩ := hδ.2 t
    have hE : E one = one + t • δ one := by
      have hn : ousNorm W (one + t • δ one - E one) = 0 := by
        refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (ousNorm_nonneg_rc _)
        obtain ⟨N, hN⟩ := hconv one ε hε
        have := hN (N + 2) (by omega)
        rw [hsum] at this
        linarith
      exact (sub_eq_zero.1 (IsOUS.norm_eq_zero _ hn)).symm
    have := (hiso 0 one).1 ou_unit_nonneg
    rwa [map_zero, hE] at this
  -- Archimedean conclusion
  have key : ∀ s : ℝ, 0 ≤ one + s • y i j := fun s => by
    have := hnonneg (s / 2)
    rwa [hδ1, ← two_smul ℝ (y i j), _root_.smul_smul, div_mul_cancel₀ s two_ne_zero] at this
  have harch := archimedean_of_isOUS_rc (V := W)
  have hle : y i j ≤ 0 := harch _ fun ε hε => by
    have := ou_smul_nonneg hε.le (key (-ε⁻¹))
    rw [smul_add, _root_.smul_smul, mul_neg, mul_inv_cancel₀ hε.ne', neg_one_smul,
      ← sub_eq_add_neg] at this
    exact sub_nonneg.1 this
  have hge : -y i j ≤ 0 := harch _ fun ε hε => by
    have := ou_smul_nonneg hε.le (key ε⁻¹)
    rw [smul_add, _root_.smul_smul, mul_inv_cancel₀ hε.ne', one_smul] at this
    rwa [← sub_neg_eq_add, sub_nonneg] at this
  exact sub_eq_zero.1 (le_antisymm hle (neg_nonpos.1 hge))

end Symmetry

/-! ## The smaller named hypothesis -/

/-- **REC's transplant of Alfsen–Shultz, *Geometry*, 9.43**, as a named hypothesis:
`AlfsenShultzJordanFromDerivations` with the symmetry `T_i e_j = T_j e_i`
(`e_j + D_i e_j = e_i + D_j e_i`, `D_i := U_i − U_{c i}`) added as a hypothesis on the
family.  The symmetry is the step the print takes from 9.48 outside its hypotheses; it is
proved in `jordan_symmetry`, so this Prop implies the old one
(`alfsenShultzJordanFromDerivations_of_transplant`).  What it still asks is the rest of
9.43: that `e_i * w := ½(w + D_i w)` extends to a Jordan product making `W` a
JB-algebra (well-definedness on the span, continuity, the Jordan identity,
`0 ≤ a² ≤ 1`).  Its truth in this generality is open.

**No longer needed**: REC 121 is proved from `jb_of_chainDense` (`JordanFromChains.lean`)
and `va_chainDense` (`SpectralChains.lean`), with chain density in place of density of
the span.  Kept as a documented open `Prop`; nothing uses it. -/
def AlfsenShultzJordanTransplant : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W],
    IsOUS W → IsBanachOUS W → IsDirectedCompleteOUS W →
    ∀ (ι : Type u) (e : ι → W) (U : ι → W →ₗ[ℝ] W) (c : ι → ι),
      Function.Injective e →
      (∀ i, 0 ≤ e i ∧ e i ≤ ouUnit W) → (∀ i, e (c i) = ouUnit W - e i) →
      (∀ i, (∀ w, 0 ≤ w → 0 ≤ U i w) ∧ U i (ouUnit W) = e i ∧ U i ∘ₗ U i = U i ∧
        U i ∘ₗ U (c i) = 0) →
      (∀ i w, 0 ≤ w → (U i w = 0 ↔ U (c i) w = w)) →
      (∀ i, IsOrderDerivation W (U i - U (c i))) →
      (∀ i j, e j + (U i - U (c i)) (e j) = e i + (U j - U (c j)) (e i)) →
      (∀ (w : W) (ε : ℝ), 0 < ε → ∃ l : List (ℝ × ι),
        ousNorm W (w - (l.map fun p => p.1 • e p.2).sum) < ε) →
      ∃ _ : Mul W, JBAlgebra W ∧
        ∀ i w, e i * w = (2⁻¹ : ℝ) • (w + (U i w - U (c i) w))

/-- The transplant with the symmetry as a hypothesis implies the transplant without it:
the symmetry is `jordan_symmetry`. -/
theorem alfsenShultzJordanFromDerivations_of_transplant
    (hT : AlfsenShultzJordanTransplant.{u}) : AlfsenShultzJordanFromDerivations.{u} := by
  intro W _ _ _ _ hOUS hB hdc ι e U c hinj h01 hc hU hker hD hdense
  have := hOUS
  exact hT W hOUS hB hdc ι e U c hinj h01 hc hU hker hD
    (jordan_symmetry hB e U c hinj hc hU hD) hdense

end Papers.REC
