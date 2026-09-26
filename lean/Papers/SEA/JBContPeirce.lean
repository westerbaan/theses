/-
Papers/SEA/JBContPeirce.lean

**`ContPeirce A` for every JB-algebra**, hence SEA 16's JB half unconditionally
(`ex:canonical-sea`, second.tex:475; van de Wetering, arXiv 2004.12749): every JB-algebra's
`[0,1]` is a convex SEA with `a ∘ b = U_{√a} b`.

Plan (2026-09-26).  Hypothesis (G): `U_{k(h)} U_x f(h) = 0` for separated `k`, `f ≥ 0`.
Goal: `D := [L_x, L_h] = 0`.  No spectral projections, no bidual, no Shirshov–Cohn.
1. **Off-diagonal parts vanish** (`u2_sep`): `U_{p(h),r(h)} x = 0` for separated `p`, `r`.
   Shift `x' = x + ‖x‖ ≥ 0` (G survives: `U_p L_q = 0` when `pq = 0`).  The t²-coefficient of
   the fundamental formula at `p + t r` gives `4 z² + 2 c∘e = U_pU_{x'}r² + U_rU_{x'}p² +
   4 U_{p,r}U_{x'}(p∘r) = 0` (`z = U_{p,r}x'`, `c = U_p x'`, `e = U_r x' ≥ 0`); `U_c e =
   U_pU_{x'}U_{pr}x' = 0` and `e ≥ 0` give `c∘e = 0` (`U_{1+tc} e = e + 2t c∘e ≥ 0` for all
   `t`); so `z² = 0`, `z = 0`.
2. **Second-order vanishing** (`der_h_zero`): `D h = h²∘x − h∘(h∘x) = 0`.  With the
   multiplicativity `U_{a,b}U_{c,d} = ½(U_{ac,bd} + U_{ad,bc})` on `C(h)` and `g = h − m`,
   `D h = ½(U_{1,g²} − U_g)x`, so `D h (L_ℓ x) = ¼(U_{ℓ,g²ψ} + U_{g²ℓ,ψ})x − ½U_{gℓ,gψ}x`
   when `ψ = 1` near `supp ℓ` (1.).  A ramp partition of unity of mesh `ε` has `O(1/ε)`
   pieces, each `O(ε²)` (the symbol `(s−t)²` vanishes to second order on the diagonal), so
   `‖D h‖ = O(ε)` by the triangle inequality alone — no orthogonal-sum estimate needed.
3. **Kleinecke–Shirokov** (`ks_norm`): `D` is a derivation, so `[D, L_h] = L_{Dh} = 0`;
   in any normed algebra `C = TS − ST` with `[S, C] = 0` has `n!‖Cⁿ‖ ≤ (2‖S‖‖T‖)ⁿ`
   (`δ = [·,S]`, `δⁿ(Tⁿ) = n! Cⁿ`).
4. **Gelfand–Hille, the version needed** (`eq_zero_of_bounded_group`): a bounded `D` on a
   real Banach space with `n!‖Dⁿ‖ ≤ Kⁿ` and `‖e^{tD}‖ ≤ 1` for all real `t` is `0`.  For a
   functional `ℓ` and vector `v`, `F(w) = Σ ℓ(Dⁿv) wⁿ/n!` is entire with
   `|F(w)| ≤ C e^{2√(K|w|)}`; `G(z) = F(z²)` is bounded on both axes (`e^{tD}` contracts),
   of order 1, so bounded (Phragmén–Lindelöf in the four quadrants), so constant
   (Liouville); thus `ℓ(e^{tD}v)` is constant and `ℓ(Dv) = 0`.
5. `e^{tD}` is a unital Jordan automorphism, hence contractive (`exp_der_norm`); so
   `D = 0`, i.e. `x | h`: `contPeirce`, then `jbCommutation_all`, `sea16_jb_unconditional_all`.
Status: 1–5 done, no sorry, axiom-clean (propext, Classical.choice, Quot.sound).
-/
import Papers.SEA.JBCommJB

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.SEA.JBContPeirce

open NormedSpace Filter Topology
open scoped Nat

noncomputable section

/-! ## 1. Kleinecke–Shirokov in a normed algebra -/

section KS

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- The inner derivation `X ↦ XS − SX`. -/
def adR (S X : R) : R := X * S - S * X

theorem adR_mul (S X Y : R) : adR S (X * Y) = adR S X * Y + X * adR S Y := by
  simp only [adR]; noncomm_ring

theorem adR_add (S X Y : R) : adR S (X + Y) = adR S X + adR S Y := by
  simp only [adR]; noncomm_ring

theorem adR_nsmul (S X : R) (m : ℕ) : adR S (m • X) = m • adR S X := by
  simp only [adR, smul_mul_assoc, mul_smul_comm, smul_sub]

theorem adR_zero (S : R) : adR S 0 = 0 := by simp [adR]

theorem adR_one (S : R) : adR S 1 = 0 := by simp [adR]

theorem adR_iter_zero (S : R) (m : ℕ) : (adR S)^[m] 0 = 0 :=
  Function.iterate_fixed (adR_zero S) m

theorem norm_adR_le (S X : R) : ‖adR S X‖ ≤ 2 * ‖S‖ * ‖X‖ := by
  calc ‖adR S X‖ ≤ ‖X * S‖ + ‖S * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖S‖ + ‖S‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖S‖ * ‖X‖ := by ring

theorem norm_adR_iter_le (S X : R) (m : ℕ) : ‖(adR S)^[m] X‖ ≤ (2 * ‖S‖) ^ m * ‖X‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    have h2 : 0 ≤ 2 * ‖S‖ := by positivity
    calc ‖adR S ((adR S)^[m] X)‖ ≤ 2 * ‖S‖ * ‖(adR S)^[m] X‖ := norm_adR_le _ _
      _ ≤ 2 * ‖S‖ * ((2 * ‖S‖) ^ m * ‖X‖) := mul_le_mul_of_nonneg_left ih h2
      _ = _ := by ring

variable {T S : R} (hC : adR S (adR S T) = 0)
include hC

theorem adR_iter_T_mul (m : ℕ) (Y : R) :
    (adR S)^[m + 1] (T * Y) =
      T * (adR S)^[m + 1] Y + (m + 1 : ℕ) • (adR S T * (adR S)^[m] Y) := by
  induction m with
  | zero =>
    simp only [zero_add, Function.iterate_one, Function.iterate_zero, id_eq, one_smul, adR_mul]
    abel
  | succ m ih =>
    have e1 : (adR S)^[m + 1 + 1] (T * Y) = adR S ((adR S)^[m + 1] (T * Y)) :=
      Function.iterate_succ_apply' _ _ _
    have e2 : (adR S)^[m + 1 + 1] Y = adR S ((adR S)^[m + 1] Y) :=
      Function.iterate_succ_apply' _ _ _
    have e3 : adR S ((adR S)^[m] Y) = (adR S)^[m + 1] Y :=
      (Function.iterate_succ_apply' _ _ _).symm
    rw [e1, e2, ih, adR_add, adR_mul, adR_nsmul, adR_mul, hC, zero_mul, zero_add, e3,
      succ_nsmul _ (m + 1)]
    abel

theorem adR_iter_pow (n : ℕ) :
    (adR S)^[n] (T ^ n) = n ! • (adR S T) ^ n ∧ ∀ k, (adR S)^[n + 1 + k] (T ^ n) = 0 := by
  induction n with
  | zero =>
    refine ⟨by simp, fun k => ?_⟩
    rw [show 0 + 1 + k = k + 1 by omega, Function.iterate_succ_apply, pow_zero, adR_one,
      adR_iter_zero]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have z0 : (adR S)^[n + 1] (T ^ n) = 0 := by simpa using ih2 0
    refine ⟨?_, fun k => ?_⟩
    · rw [_root_.pow_succ', adR_iter_T_mul hC, z0, mul_zero, zero_add, ih1, mul_smul_comm, smul_smul,
        _root_.pow_succ' (adR S T) n, Nat.factorial_succ]
    · rw [_root_.pow_succ', show n + 1 + 1 + k = (n + 1 + k) + 1 by omega, adR_iter_T_mul hC,
        show n + 1 + k + 1 = n + 1 + (k + 1) by omega, ih2 (k + 1), ih2 k, mul_zero, mul_zero,
        smul_zero, add_zero]

/-- **Kleinecke–Shirokov**, quantitative: `n! ‖Cⁿ‖ ≤ (2‖S‖)ⁿ ‖Tⁿ‖` for `C = TS − ST`
commuting with `S`. -/
theorem ks_norm (n : ℕ) : (n ! : ℝ) * ‖(adR S T) ^ n‖ ≤ (2 * ‖S‖) ^ n * ‖T ^ n‖ := by
  have h := norm_adR_iter_le S (T ^ n) n
  rw [(adR_iter_pow hC n).1, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast] at h
  exact h

end KS

/-! ## 2. A Gelfand–Hille theorem: a contractive group with fast-decaying powers is trivial -/

section GH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem sum_sq_bound {s : ℝ} (hs : 0 ≤ s) :
    HasSum (fun n : ℕ => (s ^ n / n !) ^ 2) (∑' n : ℕ, (s ^ n / n !) ^ 2) ∧
      ∑' n : ℕ, (s ^ n / n !) ^ 2 ≤ Real.exp (2 * s) := by
  have h1 : ∀ n : ℕ, (s ^ n / n !) ^ 2 ≤ Real.exp s * (s ^ n / n !) := fun n => by
    have a := Real.pow_div_factorial_le_exp s hs n
    have b : 0 ≤ s ^ n / n ! := by positivity
    rw [sq]; exact mul_le_mul_of_nonneg_right a b
  have hsum : HasSum (fun n : ℕ => s ^ n / n !) (Real.exp s) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp s
  have hs2 : Summable (fun n : ℕ => (s ^ n / n !) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) h1 (hsum.summable.mul_left _)
  refine ⟨hs2.hasSum, ?_⟩
  calc ∑' n, (s ^ n / n !) ^ 2 ≤ Real.exp s * Real.exp s :=
        hasSum_le h1 hs2.hasSum (hsum.mul_left _)
    _ = Real.exp (2 * s) := by rw [← Real.exp_add]; ring_nf

/-- **Gelfand–Hille, the form needed here**: a bounded operator `D` on a real Banach space
with `n!‖Dⁿv‖ ≤ Kⁿ‖v‖` (so `D` is quasinilpotent, of order `½`) and `‖e^{tD}v‖ ≤ ‖v‖` for
every real `t` is zero. -/
theorem eq_zero_of_bounded_group {D : E →L[ℝ] E} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (n : ℕ) (v : E), (n ! : ℝ) * ‖(D ^ n) v‖ ≤ K ^ n * ‖v‖)
    (hb : ∀ (t : ℝ) (v : E), ‖exp (t • D) v‖ ≤ ‖v‖) : D = 0 := by
  ext v
  rw [ContinuousLinearMap.zero_apply]
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ => ?_
  set B := ‖ℓ‖ * ‖v‖ with hB
  have hB0 : 0 ≤ B := by positivity
  set c : ℕ → ℝ := fun n => ℓ ((D ^ n) v) with hc
  -- coefficient bound
  have hcb : ∀ (n : ℕ) {r : ℝ}, 0 ≤ r →
      |c n| / n ! * r ^ n ≤ B * (Real.sqrt (K * r) ^ n / n !) ^ 2 := by
    intro n r hr
    have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    have h1 : |c n| ≤ ‖ℓ‖ * ‖(D ^ n) v‖ := by
      have := ℓ.le_opNorm ((D ^ n) v); rwa [Real.norm_eq_abs] at this
    have h2 := hK n v
    have key : (n ! : ℝ) * |c n| ≤ B * K ^ n := by
      calc (n ! : ℝ) * |c n| ≤ n ! * (‖ℓ‖ * ‖(D ^ n) v‖) :=
            mul_le_mul_of_nonneg_left h1 hf.le
        _ = ‖ℓ‖ * (n ! * ‖(D ^ n) v‖) := by ring
        _ ≤ ‖ℓ‖ * (K ^ n * ‖v‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = B * K ^ n := by rw [hB]; ring
    have hsq : (Real.sqrt (K * r) ^ n / n !) ^ 2 = (K * r) ^ n / (n ! : ℝ) ^ 2 := by
      rw [div_pow, ← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (mul_nonneg hK0 hr)]
    rw [hsq]
    have hrn : 0 ≤ r ^ n := pow_nonneg hr n
    calc |c n| / n ! * r ^ n = ((n ! : ℝ) * |c n|) * r ^ n / (n ! : ℝ) ^ 2 := by
          field_simp
      _ ≤ (B * K ^ n) * r ^ n / (n ! : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right key hrn) (by positivity)
      _ = B * ((K * r) ^ n / (n ! : ℝ) ^ 2) := by rw [mul_pow]; ring
  -- the entire function
  set f : ℕ → ℂ → ℂ := fun n w => ((c n / n ! : ℝ) : ℂ) * w ^ n with hf
  have hfn : ∀ n w, ‖f n w‖ = |c n| / n ! * ‖w‖ ^ n := fun n w => by
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, abs_div,
      Nat.abs_cast]
  set u : ℝ → ℕ → ℝ := fun r n => B * (Real.sqrt (K * r) ^ n / n !) ^ 2 with hu
  have hus : ∀ r, 0 ≤ r → HasSum (u r) (B * ∑' n : ℕ, (Real.sqrt (K * r) ^ n / n !) ^ 2) :=
    fun r _ => (sum_sq_bound (Real.sqrt_nonneg _)).1.mul_left B
  have hfle : ∀ n w {r : ℝ}, ‖w‖ ≤ r → ‖f n w‖ ≤ u r n := fun n w r hr => by
    rw [hfn]
    have hr0 : 0 ≤ r := (norm_nonneg w).trans hr
    calc |c n| / n ! * ‖w‖ ^ n ≤ |c n| / n ! * r ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hr n) (by positivity)
      _ ≤ u r n := hcb n hr0
  set F : ℂ → ℂ := fun w => ∑' n, f n w with hF
  have hFsum : ∀ w, Summable fun n => ‖f n w‖ := fun w =>
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hfle n w le_rfl)
      (hus _ (norm_nonneg w)).summable
  have hFb : ∀ w, ‖F w‖ ≤ B * Real.exp (2 * Real.sqrt (K * ‖w‖)) := fun w => by
    calc ‖F w‖ ≤ ∑' n, ‖f n w‖ := norm_tsum_le_tsum_norm (hFsum w)
      _ ≤ B * ∑' n : ℕ, (Real.sqrt (K * ‖w‖) ^ n / n !) ^ 2 :=
          hasSum_le (fun n => hfle n w le_rfl) (hFsum w).hasSum (hus _ (norm_nonneg w))
      _ ≤ B * Real.exp (2 * Real.sqrt (K * ‖w‖)) :=
          mul_le_mul_of_nonneg_left (sum_sq_bound (Real.sqrt_nonneg _)).2 hB0
  have hFd : Differentiable ℂ F := by
    intro w0
    have hon : DifferentiableOn ℂ F (Metric.ball 0 (‖w0‖ + 1)) := by
      refine Complex.differentiableOn_tsum_of_summable_norm (u := u (‖w0‖ + 1))
        (hus _ (by positivity)).summable (fun n => ?_) Metric.isOpen_ball
        (fun n w hw => hfle n w ?_)
      · exact ((differentiable_const _).mul (differentiable_pow n)).differentiableOn
      · rw [Metric.mem_ball, dist_zero_right] at hw; exact hw.le
    exact hon.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))
  -- values on the real line
  have hFr : ∀ s : ℝ, F s = ((ℓ (exp (s • D) v) : ℝ) : ℂ) := fun s => by
    have h := exp_series_hasSum_exp' (𝕂 := ℝ) (s • D)
    have h2 := (ℓ.comp (ContinuousLinearMap.apply ℝ E v)).hasSum h
    have h3 := Complex.hasSum_ofReal.2 h2
    refine HasSum.tsum_eq ?_
    have h4 : (fun n => f n s) = fun n : ℕ => (((ℓ.comp (ContinuousLinearMap.apply ℝ E v))
        ((n ! : ℝ)⁻¹ • (s • D) ^ n) : ℝ) : ℂ) := by
      funext n
      simp only [hf, hc, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        smul_pow, map_smul, smul_eq_mul]
      push_cast
      ring
    rw [h4]; exact h3
  have hFrb : ∀ s : ℝ, ‖F s‖ ≤ B := fun s => by
    rw [hFr, Complex.norm_real, Real.norm_eq_abs]
    calc |ℓ (exp (s • D) v)| ≤ ‖ℓ‖ * ‖exp (s • D) v‖ := by
          have := ℓ.le_opNorm (exp (s • D) v); rwa [Real.norm_eq_abs] at this
      _ ≤ B := mul_le_mul_of_nonneg_left (hb s v) (norm_nonneg _)
  -- `G(z) = F(z²)`
  set G : ℂ → ℂ := fun z => F (z ^ 2) with hG
  have hGd : Differentiable ℂ G := hFd.comp (differentiable_pow 2)
  have hGb : ∀ z, ‖G z‖ ≤ B * Real.exp (2 * Real.sqrt K * ‖z‖) := fun z => by
    have := hFb (z ^ 2)
    rwa [norm_pow, Real.sqrt_mul hK0, Real.sqrt_sq (norm_nonneg z), ← mul_assoc] at this
  have hGre : ∀ x : ℝ, ‖G x‖ ≤ B := fun x => by
    have : G x = F ((x ^ 2 : ℝ) : ℂ) := by simp only [hG]; push_cast; rfl
    rw [this]; exact hFrb _
  have hGim : ∀ x : ℝ, ‖G (x * Complex.I)‖ ≤ B := fun x => by
    have : G (x * Complex.I) = F ((-x ^ 2 : ℝ) : ℂ) := by
      simp only [hG]; congr 1; push_cast; rw [mul_pow, Complex.I_sq]; ring
    rw [this]; exact hFrb _
  have hGO : ∀ S : Set ℂ, ∃ c < (2 : ℝ), ∃ B',
      G =O[Bornology.cobounded ℂ ⊓ 𝓟 S] fun z => Real.exp (B' * ‖z‖ ^ c) := fun S => by
    refine ⟨1, by norm_num, 2 * Real.sqrt K, Asymptotics.IsBigO.of_bound B
      (Eventually.of_forall fun z => ?_)⟩
    rw [Real.rpow_one, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hGb z
  have hall : ∀ z, ‖G z‖ ≤ B := fun z => by
    rcases le_total 0 z.re with h1 | h1 <;> rcases le_total 0 z.im with h2 | h2
    · exact PhragmenLindelof.quadrant_I hGd.diffContOnCl (hGO _) (fun x _ => hGre x)
        (fun x _ => hGim x) h1 h2
    · exact PhragmenLindelof.quadrant_IV hGd.diffContOnCl (hGO _) (fun x _ => hGre x)
        (fun x _ => hGim x) h1 h2
    · exact PhragmenLindelof.quadrant_II hGd.diffContOnCl (hGO _) (fun x _ => hGre x)
        (fun x _ => hGim x) h1 h2
    · exact PhragmenLindelof.quadrant_III hGd.diffContOnCl (hGO _) (fun x _ => hGre x)
        (fun x _ => hGim x) h1 h2
  have hLiou : ∀ z, G z = G 0 := fun z =>
    hGd.apply_eq_apply_of_bounded
      (isBounded_iff_forall_norm_le.2 ⟨B, by rintro _ ⟨w, rfl⟩; exact hall w⟩) z 0
  have hF0 : F 0 = ((ℓ v : ℝ) : ℂ) := by
    have := hFr 0
    rw [zero_smul, exp_zero, ContinuousLinearMap.one_apply] at this
    simpa using this
  have hconst : ∀ s : ℝ, ℓ (exp (s • D) v) = ℓ v := fun s => by
    have key : F s = F 0 := by
      have hG0 : G 0 = F 0 := by simp [hG]
      rcases le_total 0 s with hs | hs
      · have : F s = G (Real.sqrt s) := by
          simp only [hG]; congr 1
          rw [← Complex.ofReal_pow, Real.sq_sqrt hs]
        rw [this, hLiou, hG0]
      · have : F s = G (Real.sqrt (-s) * Complex.I) := by
          simp only [hG]; congr 1
          rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
          push_cast; ring
        rw [this, hLiou, hG0]
    rw [hFr, hF0] at key
    exact_mod_cast key
  have hd : HasDerivAt (fun s : ℝ => ℓ (exp (s • D) v)) (ℓ (D v)) 0 := by
    have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) D (0 : ℝ)).clm_apply
      (hasDerivAt_const (0 : ℝ) v)
    have h2 := ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    simp only [zero_smul, exp_zero, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.coe_mul, Function.comp_apply, map_zero, add_zero] at h2
    convert h2 using 1 <;> first | rfl | simp
  have hd' : HasDerivAt (fun s : ℝ => ℓ (exp (s • D) v)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (ℓ v)).congr_of_eventuallyEq (Eventually.of_forall hconst)
  exact hd.unique hd'

end GH

/-! ## 3. Jordan identities on `C(h)` -/

section Jordan

open Theses.B.Eff Papers.REC Papers.REC.JBCalc Papers.REC.JBMac Papers.SEA.JBAll
  Papers.SEA.JBComm Papers.SEA.JBWFull Papers.REC.JBWProj Papers.SEA.JBCommJB

universe u

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hJ : JBAlgebra A]

include hJ

attribute [local instance] ousNormedAddCommGroup ousNormedSpace jbComplete opRat

theorem Uo_eq_U2o (a : A) : Uo a = U2o a a := by
  rw [Uo, U2o, two_smul]

theorem U2o_comm (a c : A) : U2o a c = U2o c a := by
  rw [U2o, U2o, JBAlgebra.mul_comm a c, add_comm (mulC a * mulC c)]

theorem U2o_one_left (c : A) : U2o (ouUnit A) c = mulC c := by
  rw [U2o, mulC_one, JBAlgebra.one_mul, one_mul, mul_one]; abel

theorem U2o_add_left (a b c : A) : U2o (a + b) c = U2o a c + U2o b c := by
  simp only [U2o, map_add, add_mul, mul_add, JBAlgebra.add_mul]; abel

theorem U2o_add_right (a b c : A) : U2o a (b + c) = U2o a b + U2o a c := by
  rw [U2o_comm, U2o_add_left, U2o_comm b, U2o_comm c]

theorem U2o_zero_left (c : A) : U2o 0 c = 0 := by
  simp [U2o, jb_zero_mul]

theorem U2o_zero_right (c : A) : U2o c 0 = 0 := by
  rw [U2o_comm, U2o_zero_left]

theorem U2o_neg_right (a b : A) : U2o a (-b) = -U2o a b := by
  simp only [U2o, map_neg, jb_mul_neg, neg_mul, mul_neg]; abel

theorem Uo_neg (b : A) : Uo (-b) = Uo b := by
  rw [Uo, Uo, map_neg, neg_mul_neg, jb_neg_mul, jb_mul_neg, neg_neg]

theorem Uo_add (a b : A) : Uo (a + b) = Uo a + Uo b + (2 : ℝ) • U2o a b := by
  rw [Uo_eq_U2o, Uo_eq_U2o, Uo_eq_U2o, U2o_add_left, U2o_add_right, U2o_add_right,
    U2o_comm b a]
  module

theorem norm_U2o_le (a b w : A) : ‖U2o a b w‖ ≤ 3 * ‖a‖ * ‖b‖ * ‖w‖ := by
  have nm : ∀ u v : A, ‖u * v‖ ≤ ‖u‖ * ‖v‖ := jb_norm_mul_le
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hw := norm_nonneg w
  have e1 : ‖a * (b * w)‖ ≤ ‖a‖ * ‖b‖ * ‖w‖ :=
    (nm _ _).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (nm _ _) ha)
  have e2 : ‖b * (a * w)‖ ≤ ‖a‖ * ‖b‖ * ‖w‖ :=
    (nm _ _).trans (by
      calc ‖b‖ * ‖a * w‖ ≤ ‖b‖ * (‖a‖ * ‖w‖) := mul_le_mul_of_nonneg_left (nm _ _) hb
        _ = _ := by ring)
  have e3 : ‖a * b * w‖ ≤ ‖a‖ * ‖b‖ * ‖w‖ :=
    (nm _ _).trans (mul_le_mul_of_nonneg_right (nm _ _) hw)
  rw [U2o_apply]
  calc ‖a * (b * w) + b * (a * w) - a * b * w‖
      ≤ ‖a * (b * w) + b * (a * w)‖ + ‖a * b * w‖ := norm_sub_le _ _
    _ ≤ ‖a * (b * w)‖ + ‖b * (a * w)‖ + ‖a * b * w‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith

/-- The fundamental formula applied to `1`: `(U_a x)² = U_a U_x a²`. -/
theorem ff1 (a x : A) : Uo a x * Uo a x = Uo a (Uo x (a * a)) := by
  have := congrArg (fun T : A →L[ℝ] A => T (ouUnit A)) (Uo_Uo a x)
  simp only [mul_apply_eq_comp, Uo_apply_one] at this
  exact this

/-- The `t²`-coefficient of the fundamental formula at `a + t b`, for `a∘b = 0`:
`4 (U_{a,b}x)² + 2 (U_a x)∘(U_b x) = U_a U_x b² + U_b U_x a²`. -/
theorem ff_cross (a b x : A) (hab : a * b = 0) :
    (4 : ℝ) • (U2o a b x * U2o a b x) + (2 : ℝ) • (Uo a x * Uo b x) =
      Uo a (Uo x (b * b)) + Uo b (Uo x (a * a)) := by
  have f1 := ff1 (a + b) x
  have f2 := ff1 (a + -b) x
  have f3 := ff1 a x
  have f4 := ff1 b x
  have hba : b * a = 0 := by rw [JBAlgebra.mul_comm]; exact hab
  have s1 : (a + b) * (a + b) = a * a + b * b := by
    rw [JBAlgebra.add_mul, jb_mul_add, jb_mul_add, hab, hba]; abel
  have s2 : (a + -b) * (a + -b) = a * a + b * b := by
    rw [JBAlgebra.add_mul, jb_mul_add, jb_mul_add, jb_mul_neg, jb_neg_mul, jb_neg_mul,
      jb_mul_neg, hab, hba, neg_neg]; abel
  rw [s1, Uo_add] at f1
  rw [s2, Uo_add, Uo_neg, U2o_neg_right] at f2
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, map_add, JBAlgebra.add_mul, jb_mul_add, jb_neg_mul,
    jb_mul_neg, JBAlgebra.smul_mul, jb_mul_smul, smul_neg, smul_add] at f1 f2
  have hc : ∀ u v : A, u * v = v * u := JBAlgebra.mul_comm
  simp only [hc] at f1 f2 f3 f4 ⊢
  linear_combination (norm := module) (2⁻¹ : ℝ) • f1 + (2⁻¹ : ℝ) • f2 - f3 - f4

/-- **Orthogonality**: `e ≥ 0` and `U_c e = 0` give `c∘e = 0` (`U_{1+tc} e = e + 2t c∘e ≥ 0`
for every real `t`). -/
theorem mul_eq_zero_of_Uo {c e : A} (he : 0 ≤ e) (hce : Uo c e = 0) : c * e = 0 := by
  have key : ∀ t : ℝ, 0 ≤ e + (2 * t) • (c * e) := fun t => by
    have h0 := jQ_nonneg (ouUnit A + t • c) he
    have : jQ (ouUnit A + t • c) e = e + (2 * t) • (c * e) + (t * t) • jQ c e := by
      simp only [jQ, JBAlgebra.add_mul, jb_mul_add, JBAlgebra.smul_mul, jb_mul_smul,
        JBAlgebra.one_mul, JBAlgebra.mul_one, smul_add]
      module
    rwa [this, ← Uo_apply, hce, smul_zero, add_zero] at h0
  set w := c * e
  have hE := (ousNorm_bounds_le e).2
  have hb : ∀ s : ℝ, 0 < s → ousNorm A w ≤ (2 * s)⁻¹ * ousNorm A e := by
    intro s hs
    have hi : 0 ≤ (2 * s)⁻¹ := by positivity
    have up : w ≤ (2 * s)⁻¹ • e := by
      have k := smul_nonneg hi (key (-s))
      have : (2 * s)⁻¹ • (e + (2 * -s) • w) = (2 * s)⁻¹ • e - w := by
        rw [smul_add, smul_smul, show (2 * s)⁻¹ * (2 * -s) = -1 by field_simp, neg_one_smul,
          sub_eq_add_neg]
      rw [this] at k; exact sub_nonneg.1 k
    have lo : -((2 * s)⁻¹ • e) ≤ w := by
      have k := smul_nonneg hi (key s)
      have : (2 * s)⁻¹ • (e + (2 * s) • w) = (2 * s)⁻¹ • e + w := by
        rw [smul_add, smul_smul, show (2 * s)⁻¹ * (2 * s) = 1 by field_simp, one_smul]
      rw [this] at k; exact neg_le_iff_add_nonneg.2 (by rw [add_comm]; exact k)
    have hE' : (2 * s)⁻¹ • e ≤ ((2 * s)⁻¹ * ousNorm A e) • ouUnit A := by
      rw [← smul_smul]; exact smul_le_smul_of_nonneg_left hE hi
    refine ousNorm_le_rc (mul_nonneg hi (ousNorm_nonneg_rc e)) ?_ (up.trans hE')
    exact (neg_le_neg hE').trans lo
  have hw0 : ousNorm A w ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have he0 := ousNorm_nonneg_rc e
    have hs : 0 < (ousNorm A e + 1) / ousNorm A w := div_pos (by linarith) hpos
    have h1 := hb _ hs
    have h2 : (2 * ((ousNorm A e + 1) / ousNorm A w))⁻¹ * ousNorm A e =
        ousNorm A w * ousNorm A e / (2 * (ousNorm A e + 1)) := by
      field_simp
    rw [h2, le_div_iff₀ (by positivity)] at h1
    nlinarith
  exact IsOUS.norm_eq_zero _ (le_antisymm hw0 (ousNorm_nonneg_rc _))

/-! ### Multiplicativity of `U` on `C(h)` -/

theorem jbCfc_zero' (h : A) : jbCfc h 0 = 0 := by
  have := jbCfc_smul h 0 0
  rwa [zero_smul, zero_smul] at this

/-- `√s` for `s ≥ 0` on `sp h`. -/
def sqrtF {h : A} (s : C(jbSpec h, ℝ)) : C(jbSpec h, ℝ) :=
  ⟨fun t => Real.sqrt (s t), Real.continuous_sqrt.comp s.continuous⟩

theorem sqrtF_mul_self {h : A} {s : C(jbSpec h, ℝ)} (hs : ∀ t, 0 ≤ s t) :
    sqrtF s * sqrtF s = s := by
  ext t; simp [sqrtF, Real.mul_self_sqrt (hs t)]

theorem M0 (h : A) {s : C(jbSpec h, ℝ)} (hs : ∀ t, 0 ≤ s t) (m : C(jbSpec h, ℝ)) :
    Uo (jbCfc h (s * m)) = Uo (jbCfc h m) * Uo (jbCfc h s) := by
  have := Uo_cfc_mul h (sqrtF s) m
  rwa [sqrtF_mul_self hs] at this

theorem Ma (h : A) {s : C(jbSpec h, ℝ)} (hs : ∀ t, 0 ≤ s t) (m1 m2 : C(jbSpec h, ℝ)) :
    U2o (jbCfc h (s * m1)) (jbCfc h (s * m2)) =
      U2o (jbCfc h m1) (jbCfc h m2) * Uo (jbCfc h s) := by
  have e := M0 h hs (m1 + m2)
  rw [mul_add, jbCfc_add, jbCfc_add, Uo_add, Uo_add, M0 h hs m1, M0 h hs m2, add_mul, add_mul,
    smul_mul_assoc] at e
  exact smul_right_injective _ two_ne_zero (add_left_cancel e)

/-- **Multiplicativity, polarised**: for `s₁, s₂ ≥ 0` on `sp h` and any `m₁, m₂`,
`U_{s₁m₁,s₂m₂} + U_{s₂m₁,s₁m₂} = 2 U_{m₁,m₂} U_{s₁,s₂}`. -/
theorem Mb (h : A) {s1 s2 : C(jbSpec h, ℝ)} (hs1 : ∀ t, 0 ≤ s1 t) (hs2 : ∀ t, 0 ≤ s2 t)
    (m1 m2 : C(jbSpec h, ℝ)) :
    U2o (jbCfc h (s1 * m1)) (jbCfc h (s2 * m2)) + U2o (jbCfc h (s2 * m1)) (jbCfc h (s1 * m2)) =
      (2 : ℝ) • (U2o (jbCfc h m1) (jbCfc h m2) * U2o (jbCfc h s1) (jbCfc h s2)) := by
  have hs : ∀ t, 0 ≤ (s1 + s2) t := fun t => add_nonneg (hs1 t) (hs2 t)
  have e := Ma h hs m1 m2
  simp only [add_mul, jbCfc_add, U2o_add_left, U2o_add_right, Uo_add, mul_add,
    mul_smul_comm] at e
  rw [Ma h hs1, Ma h hs2] at e
  rw [← sub_eq_zero] at e ⊢
  rw [← e]
  abel

theorem UU_zero (h : A) {p r : C(jbSpec h, ℝ)} (hr : ∀ t, 0 ≤ r t) (hpr : p * r = 0) :
    Uo (jbCfc h p) * Uo (jbCfc h r) = 0 := by
  have e := Mb h hr hr p p
  rw [mul_comm r p, hpr, jbCfc_zero', U2o_zero_left, add_zero, ← Uo_eq_U2o, ← Uo_eq_U2o]
    at e
  exact (smul_eq_zero.1 e.symm).resolve_left two_ne_zero

theorem UL_zero (h : A) {p q : C(jbSpec h, ℝ)} (hq : ∀ t, 0 ≤ q t) (hpq : p * q = 0) :
    Uo (jbCfc h p) * mulC (jbCfc h q) = 0 := by
  have e := Mb h (s1 := 1) (fun _ => zero_le_one) hq p p
  rw [mul_comm q p, hpq, jbCfc_zero', U2o_zero_left, U2o_zero_right, add_zero,
    ← Uo_eq_U2o, jbCfc_one, U2o_one_left] at e
  exact (smul_eq_zero.1 e.symm).resolve_left two_ne_zero

/-! ### Off-diagonal parts vanish -/

theorem sep_mul_zero {h : A} {p r : C(jbSpec h, ℝ)} (hs : SepSupp p r) : p * r = 0 := by
  obtain ⟨α, β, hαβ, ⟨hk, hf⟩ | ⟨hk, hf⟩⟩ := hs
  · ext t
    simp only [ContinuousMap.mul_apply, ContinuousMap.zero_apply]
    by_cases ht : t.1 < β
    · rw [hk t ht, zero_mul]
    · rw [hf t (by linarith [not_lt.1 ht]), mul_zero]
  · ext t
    simp only [ContinuousMap.mul_apply, ContinuousMap.zero_apply]
    by_cases ht : α < t.1
    · rw [hk t ht, zero_mul]
    · rw [hf t (by linarith [not_lt.1 ht]), mul_zero]

theorem sep_sq_right {h : A} {p r : C(jbSpec h, ℝ)} (hs : SepSupp p r) : SepSupp p (r * r) := by
  obtain ⟨α, β, hαβ, ⟨hk, hf⟩ | ⟨hk, hf⟩⟩ := hs
  · exact ⟨α, β, hαβ, Or.inl ⟨hk, fun t ht => by simp [hf t ht]⟩⟩
  · exact ⟨α, β, hαβ, Or.inr ⟨hk, fun t ht => by simp [hf t ht]⟩⟩

theorem sep_swap_sq {h : A} {p r : C(jbSpec h, ℝ)} (hs : SepSupp p r) : SepSupp r (p * p) := by
  obtain ⟨α, β, hαβ, ⟨hk, hf⟩ | ⟨hk, hf⟩⟩ := hs
  · exact ⟨α, β, hαβ, Or.inr ⟨hf, fun t ht => by simp [hk t ht]⟩⟩
  · exact ⟨α, β, hαβ, Or.inl ⟨hf, fun t ht => by simp [hk t ht]⟩⟩

/-- **Step 1**: under the gap hypotheses, `U_{p(h), r(h)} x = 0` for separated `p, r ≥ 0`. -/
theorem u2_sep {x h : A}
    (hG : ∀ k f : C(jbSpec h, ℝ), (∀ t, 0 ≤ f t) → SepSupp k f →
      jQ (jbCfc h k) (jQ x (jbCfc h f)) = 0)
    {p r : C(jbSpec h, ℝ)} (hp : ∀ t, 0 ≤ p t) (hr : ∀ t, 0 ≤ r t) (hs : SepSupp p r) :
    U2o (jbCfc h p) (jbCfc h r) x = 0 := by
  set P := jbCfc h p with hPdef
  set R := jbCfc h r with hRdef
  have hpr := sep_mul_zero hs
  have hrp : r * p = 0 := by rw [mul_comm]; exact hpr
  have hPR : P * R = 0 := by rw [hPdef, hRdef, ← jbCfc_mul, hpr, jbCfc_zero']
  have hRP : R * P = 0 := by rw [JBAlgebra.mul_comm]; exact hPR
  have hG1 : jQ P (jQ x (R * R)) = 0 := by
    have := hG p (r * r) (fun t => by simp [mul_self_nonneg]) (sep_sq_right hs)
    rwa [jbCfc_mul] at this
  have hG2 : jQ R (jQ x (P * P)) = 0 := by
    have := hG r (p * p) (fun t => by simp [mul_self_nonneg]) (sep_swap_sq hs)
    rwa [jbCfc_mul] at this
  set l := ousNorm A x with hl
  set x' := x + l • ouUnit A with hx'def
  have hx' : 0 ≤ x' := by
    exact neg_le_iff_add_nonneg.1 (ousNorm_bounds_le x).1
  have hshift : ∀ y, jQ x' y = jQ x y + (2 * l) • (x * y) + (l * l) • y := by
    intro y
    simp only [hx'def, jQ, JBAlgebra.add_mul, jb_mul_add, JBAlgebra.smul_mul, jb_mul_smul,
      JBAlgebra.one_mul, JBAlgebra.mul_one, smul_add]
    module
  have hUPR : Uo P * Uo R = 0 := UU_zero h hr hpr
  have hURP : Uo R * Uo P = 0 := UU_zero h hp hrp
  have shifted : ∀ {P' R' : A} {p' r' : C(jbSpec h, ℝ)}, P' = jbCfc h p' → R' = jbCfc h r' →
      (∀ t, 0 ≤ r' t) → p' * r' = 0 → Uo P' * Uo R' = 0 → jQ P' (jQ x (R' * R')) = 0 →
      jQ P' (jQ x' (R' * R')) = 0 := by
    intro P' R' p' r' hP' hR' hr' hpr' hUU hG'
    rw [hshift, jQ_add, jQ_add, jQ_smul, jQ_smul, hG']
    have a1 : jQ P' (x * (R' * R')) = 0 := by
      have e := congrArg (fun T : A →L[ℝ] A => T x) (UL_zero h (p := p') (q := r' * r')
        (fun t => by simp [mul_self_nonneg]) (by rw [← mul_assoc, hpr', zero_mul]))
      simp only [mul_apply_eq_comp, mulC_apply, ContinuousLinearMap.zero_apply,
        Uo_apply, jbCfc_mul, ← hP', ← hR'] at e
      rwa [JBAlgebra.mul_comm x]
    have a2 : jQ P' (R' * R') = 0 := by
      rw [← Uo_apply, ← Uo_apply_one R', ← mul_apply_eq_comp, hUU,
        ContinuousLinearMap.zero_apply]
    rw [a1, a2, smul_zero, smul_zero, add_zero, add_zero]
  have hG1' := shifted hPdef hRdef hr hpr hUPR hG1
  have hG2' := shifted hRdef hPdef hp hrp hURP hG2
  have hz : U2o P R x' = U2o P R x := by
    rw [hx'def, map_add, map_smul, U2o_apply P R (ouUnit A)]
    simp only [JBAlgebra.mul_one, hPR, hRP, add_zero, sub_zero, smul_zero]
  have he : 0 ≤ Uo R x' := by rw [Uo_apply]; exact jQ_nonneg _ hx'
  have hce : Uo (Uo P x') (Uo R x') = 0 := by
    rw [Uo_Uo, mul_apply_eq_comp, mul_apply_eq_comp, ← mul_apply_eq_comp (Uo P) (Uo R), hUPR,
      ContinuousLinearMap.zero_apply, map_zero, map_zero]
  have horth := mul_eq_zero_of_Uo he hce
  have hff := ff_cross P R x' hPR
  rw [horth, smul_zero, add_zero] at hff
  simp only [Uo_apply] at hff
  rw [hG1', hG2', add_zero] at hff
  have hzz : U2o P R x' * U2o P R x' = 0 :=
    (smul_eq_zero.1 hff).resolve_left (by norm_num)
  have n1 := jb_norm_mul_self (U2o P R x')
  rw [hzz, ousNorm_zero'] at n1
  rw [← hz]
  exact IsOUS.norm_eq_zero _ (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 n1.symm)


/-! ## 4. Second-order vanishing: `h²∘x = h∘(h∘x)` -/

/-- `L_{h²} − L_h²`, whose value at `x` is `[L_x, L_h] h`. -/
def DelOp (h : A) : A →L[ℝ] A := mulC (h * h) - mulC h * mulC h

/-- The ramp `t ↦ min 1 (max 0 ((t − c)/ε))` on `sp h`. -/
def rmp (h : A) (ε c : ℝ) : C(jbSpec h, ℝ) :=
  ⟨fun t => min 1 (max 0 ((t.1 - c) / ε)), continuous_const.min (continuous_const.max
    ((continuous_subtype_val.sub continuous_const).div_const ε))⟩

theorem rmp_apply (h : A) (ε c : ℝ) (t : jbSpec h) :
    rmp h ε c t = min 1 (max 0 ((t.1 - c) / ε)) := rfl

theorem rmp_nonneg (h : A) (ε c : ℝ) (t : jbSpec h) : 0 ≤ rmp h ε c t :=
  le_min zero_le_one (le_max_left _ _)

theorem rmp_le_one (h : A) (ε c : ℝ) (t : jbSpec h) : rmp h ε c t ≤ 1 := min_le_left _ _

theorem rmp_of_le (h : A) {ε c : ℝ} (hε : 0 < ε) {t : jbSpec h} (ht : t.1 ≤ c) :
    rmp h ε c t = 0 := by
  rw [rmp_apply, max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le),
    min_eq_right zero_le_one]

theorem rmp_of_ge (h : A) {ε c : ℝ} (hε : 0 < ε) {t : jbSpec h} (ht : c + ε ≤ t.1) :
    rmp h ε c t = 1 := by
  have h1 : 1 ≤ (t.1 - c) / ε := by rw [le_div_iff₀ hε]; linarith
  rw [rmp_apply, max_eq_right (by linarith), min_eq_left h1]

theorem rmp_anti (h : A) {ε c c' : ℝ} (hε : 0 < ε) (hc : c ≤ c') (t : jbSpec h) :
    rmp h ε c' t ≤ rmp h ε c t := by
  rw [rmp_apply, rmp_apply]
  exact min_le_min_left _ (max_le_max_left _
    (div_le_div_of_nonneg_right (by linarith) hε.le))

/-- Localisation estimate: a bump `u ∈ [0,1]` vanishing off `|t − m| ≤ δ` has
`‖u·(t−m)‖ ≤ δ`, `‖u·(t−m)²‖ ≤ δ²`. -/
theorem loc_bound (h : A) {m δ : ℝ} (hδ : 0 ≤ δ) {u : C(jbSpec h, ℝ)} (hu0 : ∀ t, 0 ≤ u t)
    (hu1 : ∀ t, u t ≤ 1) (hz : ∀ t : jbSpec h, δ < |t.1 - m| → u t = 0) :
    ‖u‖ ≤ 1 ∧ ‖u * (specId h - m • 1)‖ ≤ δ ∧
      ‖u * ((specId h - m • 1) * (specId h - m • 1))‖ ≤ δ ^ 2 := by
  have ev : ∀ t : jbSpec h, (specId h - m • (1 : C(jbSpec h, ℝ))) t = t.1 - m := fun t => by
    simp [specId]
  refine ⟨(ContinuousMap.norm_le _ zero_le_one).2 fun t => ?_,
    (ContinuousMap.norm_le _ hδ).2 fun t => ?_, (ContinuousMap.norm_le _ (by positivity)).2
      fun t => ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hu0 t)]; exact hu1 t
  · rw [ContinuousMap.mul_apply, ev, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hu0 t)]
    by_cases hd : |t.1 - m| ≤ δ
    · calc u t * |t.1 - m| ≤ 1 * δ := mul_le_mul (hu1 t) hd (abs_nonneg _) zero_le_one
        _ = δ := one_mul _
    · rw [hz t (not_le.1 hd), zero_mul]; exact hδ
  · rw [ContinuousMap.mul_apply, ContinuousMap.mul_apply, ev, Real.norm_eq_abs, abs_mul,
      abs_mul, abs_of_nonneg (hu0 t)]
    by_cases hd : |t.1 - m| ≤ δ
    · calc u t * (|t.1 - m| * |t.1 - m|) ≤ 1 * (δ * δ) :=
            mul_le_mul (hu1 t) (mul_le_mul hd hd (abs_nonneg _) hδ)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
        _ = δ ^ 2 := by ring
    · rw [hz t (not_le.1 hd), zero_mul]; positivity

/-- **One piece**: `‖(L_{h²} − L_h²)(ϕ(h)∘x)‖ ≤ 12 ε² ‖x‖` for the bump
`ϕ = ramp_c − ramp_{c+ε}`. -/
theorem piece_bound {x h : A}
    (hG : ∀ k f : C(jbSpec h, ℝ), (∀ t, 0 ≤ f t) → SepSupp k f →
      jQ (jbCfc h k) (jQ x (jbCfc h f)) = 0) {ε c : ℝ} (hε : 0 < ε) :
    ‖DelOp h (jbCfc h (rmp h ε c - rmp h ε (c + ε)) * x)‖ ≤ 12 * ε ^ 2 * ‖x‖ := by
  set ϕ := rmp h ε c - rmp h ε (c + ε) with hϕdef
  set ψ := rmp h ε (c - 2 * ε) - rmp h ε (c + 3 * ε) with hψdef
  set lo := 1 - rmp h ε (c - 2 * ε) with hlodef
  set hi := rmp h ε (c + 3 * ε) with hhidef
  set m := c + ε with hm
  set g : C(jbSpec h, ℝ) := specId h - m • 1 with hgdef
  have hϕ0 : ∀ t, 0 ≤ ϕ t := fun t => by
    simp only [hϕdef, ContinuousMap.sub_apply]
    exact sub_nonneg.2 (rmp_anti h hε (by linarith) t)
  have hϕ1 : ∀ t, ϕ t ≤ 1 := fun t => by
    simp only [hϕdef, ContinuousMap.sub_apply]
    linarith [rmp_le_one h ε c t, rmp_nonneg h ε (c + ε) t]
  have hψ0 : ∀ t, 0 ≤ ψ t := fun t => by
    simp only [hψdef, ContinuousMap.sub_apply]
    exact sub_nonneg.2 (rmp_anti h hε (by linarith) t)
  have hψ1 : ∀ t, ψ t ≤ 1 := fun t => by
    simp only [hψdef, ContinuousMap.sub_apply]
    linarith [rmp_le_one h ε (c - 2 * ε) t, rmp_nonneg h ε (c + 3 * ε) t]
  have hlo0 : ∀ t, 0 ≤ lo t := fun t => by
    simp only [hlodef, ContinuousMap.sub_apply, ContinuousMap.one_apply]
    linarith [rmp_le_one h ε (c - 2 * ε) t]
  have hhi0 : ∀ t, 0 ≤ hi t := fun t => rmp_nonneg h ε _ t
  have hϕlow : ∀ t : jbSpec h, t.1 < c → ϕ t = 0 := fun t ht => by
    simp only [hϕdef, ContinuousMap.sub_apply]
    rw [rmp_of_le h hε (by linarith), rmp_of_le h hε (by linarith), sub_zero]
  have hϕhigh : ∀ t : jbSpec h, c + 2 * ε < t.1 → ϕ t = 0 := fun t ht => by
    simp only [hϕdef, ContinuousMap.sub_apply]
    rw [rmp_of_ge h hε (by linarith), rmp_of_ge h hε (by linarith), sub_self]
  have hϕz : ∀ t : jbSpec h, ε < |t.1 - m| → ϕ t = 0 := fun t ht => by
    rcases lt_abs.1 ht with h1 | h1
    · exact hϕhigh t (by linarith)
    · exact hϕlow t (by linarith)
  have hψz : ∀ t : jbSpec h, 3 * ε < |t.1 - m| → ψ t = 0 := fun t ht => by
    simp only [hψdef, ContinuousMap.sub_apply]
    rcases lt_abs.1 ht with h1 | h1
    · rw [rmp_of_ge h hε (by linarith), rmp_of_ge h hε (by linarith), sub_self]
    · rw [rmp_of_le h hε (by linarith), rmp_of_le h hε (by linarith), sub_zero]
  have sep1 : SepSupp ϕ lo := ⟨c - ε, c, by linarith, Or.inl ⟨hϕlow, fun t ht => by
    simp only [hlodef, ContinuousMap.sub_apply, ContinuousMap.one_apply]
    rw [rmp_of_ge h hε (by linarith), sub_self]⟩⟩
  have sep2 : SepSupp ϕ hi := ⟨c + 2 * ε, c + 3 * ε, by linarith, Or.inr ⟨hϕhigh,
    fun t ht => rmp_of_le h hε ht.le⟩⟩
  have hsum : ψ + lo + hi = 1 := by rw [hψdef, hlodef, hhidef]; ring
  set Φ := jbCfc h ϕ with hΦ
  set Ψ := jbCfc h ψ with hΨ
  have hΦx : Φ * x = U2o Φ Ψ x := by
    have e1 : Φ * x = U2o Φ (ouUnit A) x := by rw [U2o_comm, U2o_one_left, mulC_apply]
    rw [e1, ← jbCfc_one, ← hsum, jbCfc_add, jbCfc_add, U2o_add_right, U2o_add_right,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      u2_sep hG hϕ0 hlo0 sep1, u2_sep hG hϕ0 hhi0 sep2, add_zero, add_zero]
  have hGel : jbCfc h g = h - m • ouUnit A := by
    rw [hgdef, jbCfc_sub, jbCfc_id, jbCfc_smul, jbCfc_one]
  have hDel : DelOp h = (2⁻¹ : ℝ) •
      (U2o (ouUnit A) (jbCfc h (g * g)) - U2o (jbCfc h g) (jbCfc h g)) := by
    ext w
    have hc : ∀ u v : A, u * v = v * u := JBAlgebra.mul_comm
    simp only [DelOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, U2o_apply,
      mul_apply_eq_comp, mulC_apply, jbCfc_mul, hGel, jb_sub_mul, jb_mul_sub,
      JBAlgebra.smul_mul, jb_mul_smul, JBAlgebra.one_mul, JBAlgebra.mul_one]
    simp only [hc]
    module
  have e1 := Mb h hϕ0 hψ0 1 (g * g)
  have e2 := Mb h hϕ0 hψ0 g g
  simp only [mul_one, jbCfc_one] at e1
  have e1x := congrArg (fun T : A →L[ℝ] A => T x) e1
  have e2x := congrArg (fun T : A →L[ℝ] A => T x) e2
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    mul_apply_eq_comp] at e1x e2x
  have key : DelOp h (Φ * x) =
      (4⁻¹ : ℝ) • (U2o Φ (jbCfc h (ψ * (g * g))) x + U2o Ψ (jbCfc h (ϕ * (g * g))) x) -
      (4⁻¹ : ℝ) • (U2o (jbCfc h (ϕ * g)) (jbCfc h (ψ * g)) x +
        U2o (jbCfc h (ψ * g)) (jbCfc h (ϕ * g)) x) := by
    rw [hΦx, hDel]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
    linear_combination (norm := module) (-4⁻¹ : ℝ) • e1x + (4⁻¹ : ℝ) • e2x
  have nf : ∀ f : C(jbSpec h, ℝ), ‖jbCfc h f‖ = ‖f‖ := ousNorm_jbCfc h
  obtain ⟨fb1, fb5, fb4⟩ := loc_bound h hε.le hϕ0 hϕ1 hϕz
  obtain ⟨fb2, fb6, fb3⟩ := loc_bound h (by positivity : (0 : ℝ) ≤ 3 * ε) hψ0 hψ1 hψz
  have a1 : ‖U2o Φ (jbCfc h (ψ * (g * g))) x‖ ≤ 3 * 1 * (3 * ε) ^ 2 * ‖x‖ := by
    refine (norm_U2o_le _ _ _).trans ?_
    rw [hΦ, nf, nf]; gcongr
  have a2 : ‖U2o Ψ (jbCfc h (ϕ * (g * g))) x‖ ≤ 3 * 1 * ε ^ 2 * ‖x‖ := by
    refine (norm_U2o_le _ _ _).trans ?_
    rw [hΨ, nf, nf]; gcongr
  have a3 : ‖U2o (jbCfc h (ϕ * g)) (jbCfc h (ψ * g)) x‖ ≤ 3 * ε * (3 * ε) * ‖x‖ := by
    refine (norm_U2o_le _ _ _).trans ?_
    rw [nf, nf]; gcongr
  have a4 : ‖U2o (jbCfc h (ψ * g)) (jbCfc h (ϕ * g)) x‖ ≤ 3 * (3 * ε) * ε * ‖x‖ := by
    refine (norm_U2o_le _ _ _).trans ?_
    rw [nf, nf]; gcongr
  have q : ‖(4⁻¹ : ℝ)‖ = 4⁻¹ := by norm_num
  rw [key]
  calc _ ≤ ‖(4⁻¹ : ℝ) • (U2o Φ (jbCfc h (ψ * (g * g))) x + U2o Ψ (jbCfc h (ϕ * (g * g))) x)‖ +
        ‖(4⁻¹ : ℝ) • (U2o (jbCfc h (ϕ * g)) (jbCfc h (ψ * g)) x +
          U2o (jbCfc h (ψ * g)) (jbCfc h (ϕ * g)) x)‖ := norm_sub_le _ _
    _ ≤ 4⁻¹ * (‖U2o Φ (jbCfc h (ψ * (g * g))) x‖ + ‖U2o Ψ (jbCfc h (ϕ * (g * g))) x‖) +
        4⁻¹ * (‖U2o (jbCfc h (ϕ * g)) (jbCfc h (ψ * g)) x‖ +
          ‖U2o (jbCfc h (ψ * g)) (jbCfc h (ϕ * g)) x‖) := by
        rw [norm_smul, norm_smul, q]
        gcongr <;> exact norm_add_le _ _
    _ ≤ 4⁻¹ * (3 * 1 * (3 * ε) ^ 2 * ‖x‖ + 3 * 1 * ε ^ 2 * ‖x‖) +
        4⁻¹ * (3 * ε * (3 * ε) * ‖x‖ + 3 * (3 * ε) * ε * ‖x‖) := by gcongr
    _ = 12 * ε ^ 2 * ‖x‖ := by ring

/-- **Step 2**: under the gap hypotheses, `h²∘x = h∘(h∘x)`. -/
theorem delOp_eq_zero {x h : A}
    (hG : ∀ k f : C(jbSpec h, ℝ), (∀ t, 0 ≤ f t) → SepSupp k f →
      jQ (jbCfc h k) (jQ x (jbCfc h f)) = 0) : DelOp h x = 0 := by
  set R0 := ousNorm A h with hR0
  set M : ℕ := ⌈2 * R0 + 2⌉₊ with hMdef
  have hM : 2 * R0 + 2 ≤ (M : ℝ) := Nat.le_ceil _
  have hbound : ∀ n : ℕ, 0 < n → ‖DelOp h x‖ ≤ 12 * M * ‖x‖ / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set ε : ℝ := 1 / n with hεdef
    have hε : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by
      rw [hεdef, div_le_one hn']; exact_mod_cast hn
    set a : ℝ := -R0 - 1 with ha
    set f : ℕ → C(jbSpec h, ℝ) := fun i => rmp h ε (a + i * ε) with hf
    set N := M * n with hN
    have hNε : (N : ℝ) * ε = M := by
      rw [hN, hεdef]; push_cast; field_simp
    have htel : ∑ i ∈ Finset.range N, (f i - f (i + 1)) = 1 := by
      rw [Finset.sum_range_sub']
      ext t
      have ht := jbSpec_subset h t.2
      simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, hf]
      rw [rmp_of_ge h hε (by push_cast; linarith [ht.1]),
        rmp_of_le h hε (by rw [hNε]; linarith [ht.2]), sub_zero]
    have hpiece : ∀ i, f i - f (i + 1) = rmp h ε (a + i * ε) - rmp h ε ((a + i * ε) + ε) := by
      intro i; simp only [hf]; congr 2; push_cast; ring
    have hx : x = ∑ i ∈ Finset.range N, jbCfc h (f i - f (i + 1)) * x := by
      have e0 : x = jbCfc h (∑ i ∈ Finset.range N, (f i - f (i + 1))) * x := by
        rw [htel, jbCfc_one, JBAlgebra.one_mul]
      have e1 : jbCfc h (∑ i ∈ Finset.range N, (f i - f (i + 1))) =
          ∑ i ∈ Finset.range N, jbCfc h (f i - f (i + 1)) := by
        have := map_sum (jbCfcL h) (fun i => f i - f (i + 1)) (Finset.range N)
        simpa only [jbCfcL_apply] using this
      conv_lhs => rw [e0]
      rw [e1, JBAlgebra.mul_comm, ← mulC_apply, map_sum]
      simp only [mulC_apply, JBAlgebra.mul_comm x]
    calc ‖DelOp h x‖
        = ‖∑ i ∈ Finset.range N, DelOp h (jbCfc h (f i - f (i + 1)) * x)‖ := by
          conv_lhs => rw [hx]
          rw [map_sum]
      _ ≤ ∑ i ∈ Finset.range N, ‖DelOp h (jbCfc h (f i - f (i + 1)) * x)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range N, 12 * ε ^ 2 * ‖x‖ :=
          Finset.sum_le_sum fun i _ => by rw [hpiece]; exact piece_bound hG hε
      _ = N * ε * (12 * ε * ‖x‖) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ = 12 * M * ‖x‖ / n := by rw [hNε, hεdef]; field_simp
  have h0 : ‖DelOp h x‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖DelOp h x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨n, hn⟩ := exists_nat_gt (12 * M * ‖x‖ / ‖DelOp h x‖)
    have hq : 0 ≤ 12 * M * ‖x‖ / ‖DelOp h x‖ := by positivity
    have hn0 : 0 < n := by exact_mod_cast hq.trans_lt hn
    have h1 := hbound n hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [le_div_iff₀ hn'] at h1
    rw [div_lt_iff₀ hpos] at hn
    linarith
  exact norm_eq_zero.1 h0


/-! ## 5. `ContPeirce`, `JBCommutation` and SEA 16 for every JB-algebra -/

/-- **The continuous Peirce criterion holds in every JB-algebra**: the gap hypotheses force
`D = [L_x, L_h]` to vanish (`Dh = 0` by Steps 1–2, then Kleinecke–Shirokov and
Gelfand–Hille for the contractive group `e^{tD}`). -/
theorem contPeirce : ContPeirce A := by
  intro x h hG
  set D : A →L[ℝ] A := Dop x h with hDdef
  have hder : ∀ u v : A, D (u * v) = D u * v + u * D v := Dop_der x h
  have hDh : D h = 0 := by
    have e := delOp_eq_zero hG
    rw [hDdef, Dop_apply]
    simp only [DelOp, ContinuousLinearMap.sub_apply, mul_apply_eq_comp, mulC_apply] at e
    rw [JBAlgebra.mul_comm x (h * h), JBAlgebra.mul_comm x h]; exact e
  have hcomm : D * mulC h = mulC h * D := by
    ext w
    simp only [mul_apply_eq_comp, mulC_apply]
    rw [hder, hDh, jb_zero_mul, zero_add]
  set T := mulC x with hT
  set S := mulC h with hS
  have hDT : adR S T = D := rfl
  have hC : adR S (adR S T) = 0 := by rw [hDT, adR, hcomm, sub_self]
  set K := 2 * ‖S‖ * ‖T‖ with hK
  have hKn : ∀ (n : ℕ) (v : A), (n ! : ℝ) * ‖(D ^ n) v‖ ≤ K ^ n * ‖v‖ := by
    intro n v
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 := (D ^ n).le_opNorm v
      have h2 := ks_norm hC n
      rw [hDT] at h2
      have h3 : ‖T ^ n‖ ≤ ‖T‖ ^ n := norm_pow_le' T hn
      calc (n ! : ℝ) * ‖(D ^ n) v‖ ≤ n ! * (‖D ^ n‖ * ‖v‖) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (n ! * ‖D ^ n‖) * ‖v‖ := by ring
        _ ≤ ((2 * ‖S‖) ^ n * ‖T ^ n‖) * ‖v‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ ≤ ((2 * ‖S‖) ^ n * ‖T‖ ^ n) * ‖v‖ := by gcongr
        _ = K ^ n * ‖v‖ := by rw [hK, mul_pow, mul_pow, mul_pow]
  have hb : ∀ (t : ℝ) (v : A), ‖exp (t • D) v‖ ≤ ‖v‖ := fun t v => exp_der_norm hder t v
  have hD0 : D = 0 := eq_zero_of_bounded_group (by positivity) hKn hb
  intro w
  have := congrArg (fun T : A →L[ℝ] A => T w) hD0
  simp only [hDdef, Dop_apply, ContinuousLinearMap.zero_apply] at this
  exact sub_eq_zero.1 this

/-- **`JBCommutation` for every JB-algebra** (van de Wetering's commutation theorem). -/
theorem jbCommutation_all : JBCommutation A := jbCommutation_of_contPeirce contPeirce

/-- **SEA 16, JB half, unconditionally**: for every JB-algebra `A`, `[0,1]_A` is a convex
SEA with `a ∘ b = U_{√a} b`. -/
theorem sea16_jb_unconditional_all :
    @IsConvex _ (jbEA A) ∧
    ∀ a b : Set.Icc (0 : A) (ouUnit A),
      ∃! r : A, 0 ≤ r ∧ r * r = a.1 ∧
        (@SequentialEffectAlgebra.seq _ (jbEA A)
          (jbSEA (jbCommutation_all (A := A))).toSequentialEffectAlgebra a b).1 =
          (2 : ℝ) • (r * (r * b.1)) - (r * r) * b.1 :=
  sea16_jb_of_contPeirce contPeirce

end Jordan

end

end Papers.SEA.JBContPeirce
