/-
Papers/REC/JBMacdonald.lean

**Positivity of the quadratic map in a JB-algebra** (Hanche-Olsen–Størmer 3.3.6): for
`a, b` in a JB-algebra `A` (REC 44) with `b ≥ 0`, `U_a b = 2a(ab) − a²b ≥ 0`; and the
**fundamental formula** `U_{U_a b} = U_a U_b U_a` in every JB-algebra.

Plan (2026-09-26; budget ~4 h).  Macdonald's and Shirshov–Cohn's theorems are avoided; the
only algebra is one degree-4 identity, the rest is analysis on `B(A)` (the Banach algebra
of bounded operators for the order-unit norm).
1. `L_a`, `U_a`, `U_{a,c}` as bounded operators; the degree-4 identity
   `2 U_{w, kw} = L_k U_w + U_w L_k` (`two_U2_mul`, two instances of the linearised Jordan
   identity `jb_lin`).
2. **Conjugation formula** `U_{e^{L_h} b} = e^{L_h} U_b e^{L_h}`: `t ↦ e^{−tL_h} U_{e^{tL_h}b}
   e^{−tL_h}` has derivative `e^{−tL_h}(2U_{w,hw} − L_hU_w − U_wL_h)e^{−tL_h} = 0` (1.).
   With `b = 1`: `U_{e(h)} = e^{2L_h}` for `e(h) := e^{L_h} 1`, and the fundamental formula
   holds at every `a = e(h)`.
3. Every `c ≥ δ1` (`δ > 0`) is `e(h)`: `h = log c` by the functional calculus (`JBCalculus`),
   `e^{L_h}1 = Σ hⁿ/n!` (Jordan powers) `= (exp ∘ log)(c) = c`.
4. **Fundamental formula for all `a`**: `λ ↦ U_{U_{a+λ}b} − U_{a+λ}U_bU_{a+λ}` is analytic
   (polynomial) and vanishes for `λ > ‖a‖` (3.), so vanishes identically.
5. **`e^{tL_h} ≥ 0`** (the resolvent criterion `exp_mem_posOps_of_resolvent`): if
   `(1 − lL_h)y ≥ 0` and `y ≱ 0`, a state `φ` with `φ(y) = min sp y =: m < 0` has
   `φ(h(y − m)) = 0` by Cauchy–Schwarz, so `φ((1 − lL_h)y) = m(1 − lφ(h)) < 0`.
   Hence `U_c = e^{2L_{log c}} ≥ 0` for `c ≥ δ1`, and by continuity for all `c ≥ 0`.
6. **General `a`** (the swap trick, `TT*` vs `T*T` for `T = ac`): for `c ≥ 0` put
   `x = U_a(c²)`, `y = U_c(a²) ≥ 0` (5.).  The fundamental formula gives
   `x^{n+1} = U_aU_c(yⁿ)`, hence `x·p(x) = U_aU_c(p(y))` for polynomials, hence for
   continuous `f` (Weierstrass); `f(t) = max(−t, 0)` has `f(y) = 0`, so `t·f(t) = 0` on
   `sp x`, i.e. `x ≥ 0`.  With `c = √b`: `U_a b ≥ 0`.
Status: 1–6 done, no sorry, axiom-clean (`hos336`, `jQ_nonneg`, `Uo_Uo`, `jQ_jQ`).
-/
import Papers.REC.JBCalculus
import Papers.REC.JBPeirce
import Papers.REC.Resolvent

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.REC.JBMac

open Theses.B.Eff Papers.REC Papers.REC.JBCalc NormedSpace Filter Topology

universe u

noncomputable section

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hJ : JBAlgebra A]

include hJ

attribute [local instance] ousNormedAddCommGroup ousNormedSpace

/-! ## 1. Operators and the degree-4 identity -/

/-- The Jordan product as a bounded bilinear map (`‖ab‖ ≤ ‖a‖‖b‖`). -/
def mulC : A →L[ℝ] A →L[ℝ] A :=
  (LinearMap.mk₂ ℝ (· * ·) JBAlgebra.add_mul JBAlgebra.smul_mul jb_mul_add
    jb_mul_smul).mkContinuous₂ 1 fun x y => by rw [one_mul]; exact jb_norm_mul_le x y

@[simp] theorem mulC_apply (a b : A) : mulC a b = a * b := rfl

/-- `U_a = 2L_a² − L_{a²}` as a bounded operator. -/
def Uo (a : A) : A →L[ℝ] A := (2 : ℝ) • (mulC a * mulC a) - mulC (a * a)

/-- `U_{a,c} = L_aL_c + L_cL_a − L_{ac}`. -/
def U2o (a c : A) : A →L[ℝ] A := mulC a * mulC c + mulC c * mulC a - mulC (a * c)

theorem Uo_apply (a b : A) : Uo a b = jQ a b := by
  simp [Uo, jQ]

theorem U2o_apply (a c b : A) : U2o a c b = a * (c * b) + c * (a * b) - (a * c) * b := by
  simp [U2o]

/-- **The degree-4 identity** `2 U_{w,kw} = L_k U_w + U_w L_k`, on elements. -/
theorem two_U2_mul_apply (w k z : A) :
    (2 : ℝ) • (w * ((k * w) * z) + (k * w) * (w * z) - (w * (k * w)) * z) =
      k * ((2 : ℝ) • (w * (w * z)) - (w * w) * z) +
        ((2 : ℝ) • (w * (w * (k * z))) - (w * w) * (k * z)) := by
  have h1 := jb_lin w k z w
  have h2 := jb_lin w k w z
  rw [jb_mul_sub, jb_mul_smul]
  have hc : ∀ a b : A, a * b = b * a := JBAlgebra.mul_comm
  simp only [hc] at h1 h2 ⊢
  rw [← sub_eq_zero]
  linear_combination (norm := module) h2 - (2 : ℝ) • h1

/-- **The degree-4 identity** as an operator identity: `2 U_{w,kw} = L_k U_w + U_w L_k`. -/
theorem two_U2_mul (w k : A) : (2 : ℝ) • U2o w (k * w) = mulC k * Uo w + Uo w * mulC k := by
  ext z
  have := two_U2_mul_apply w k z
  simp only [U2o, Uo, smul_apply, add_apply,
    sub_apply, mul_apply_eq_comp, mulC_apply] at this ⊢
  exact this

theorem jbComplete : CompleteSpace A := completeSpace_of_banach (W := A) hJ.banach

attribute [local instance] jbComplete

/-- `B(A)` as a normed `ℚ`-algebra (only used by `exp` lemmas stated over `ℚ`). -/
def opRat : NormedAlgebra ℚ (A →L[ℝ] A) := NormedAlgebra.restrictScalars ℚ ℝ _

attribute [local instance] opRat

/-! ## 2. The conjugation formula `U_{e^{L_h} b} = e^{L_h} U_b e^{L_h}` -/

theorem hasDerivAt_mulC {w : ℝ → A} {w' : A} {t : ℝ} (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => mulC (w s)) (mulC w') t :=
  (mulC (A := A)).hasFDerivAt.comp_hasDerivAt t hw

theorem hasDerivAt_Uo {w : ℝ → A} {w' : A} {t : ℝ} (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => Uo (w s)) ((2 : ℝ) • U2o (w t) w') t := by
  have h1 := hasDerivAt_mulC hw
  have h2 := (h1.mul h1).const_smul (2 : ℝ)
  have h3 : HasDerivAt (fun s => w s * w s) (w t * w' + w' * w t) t := by
    have := mulC.hasDerivAt_of_bilinear (u := w) (v := w) (fun _ => hw) (fun _ => hw)
    simpa only [mulC_apply] using this
  have h4 := hasDerivAt_mulC h3
  refine HasDerivAt.congr_deriv (f := fun s => Uo (w s)) (h2.sub h4) ?_
  rw [JBAlgebra.mul_comm w' (w t), map_add, U2o]
  module

/-- **The conjugation formula** `U_{e^{L_h} b} = e^{L_h} U_b e^{L_h}`: the function
`t ↦ e^{−tL_h} U_{e^{tL_h} b} e^{−tL_h}` has derivative zero (`two_U2_mul`). -/
theorem Uo_exp_apply (h b : A) :
    Uo (exp (mulC h) b) = exp (mulC h) * Uo b * exp (mulC h) := by
  set X : A →L[ℝ] A := mulC h with hX
  let e : ℝ → (A →L[ℝ] A) := fun t => exp ((-t) • X)
  let w : ℝ → A := fun t => exp (t • X) b
  let F : ℝ → (A →L[ℝ] A) := fun t => e t * Uo (w t) * e t
  have hcomm : ∀ t : ℝ, X * e t = e t * X := fun t =>
    (((Commute.refl X).smul_right (-t)).exp_right).eq
  have he : ∀ t, HasDerivAt e (-(e t * X)) t := fun t => by
    have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (-t)).scomp t (hasDerivAt_neg t)
    simpa [e, Function.comp_def] using this
  have hw : ∀ t, HasDerivAt w (h * w t) t := fun t => by
    have := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X t).clm_apply (hasDerivAt_const t b)
    simpa [w, hX] using this
  have hF : ∀ t, HasDerivAt F 0 t := fun t => by
    have h1 := ((he t).mul (hasDerivAt_Uo (hw t))).mul (he t)
    refine HasDerivAt.congr_deriv (f := F) h1 ?_
    symm
    have hU := two_U2_mul (w t) h
    rw [← hX] at hU
    rw [hU]
    have hl : (e * fun s => Uo (w s)) t = e t * Uo (w t) := rfl
    rw [hl]
    calc (0 : A →L[ℝ] A) = e t * Uo (w t) * (X * e t - e t * X) := by
          rw [hcomm t, sub_self, mul_zero]
      _ = _ := by noncomm_ring
  have hc := is_const_of_deriv_eq_zero (fun t => (hF t).differentiableAt)
    (fun t => (hF t).deriv) 1 0
  have h0 : F 0 = Uo b := by simp [F, e, w]
  have h1 : F 1 = exp (-X) * Uo (exp X b) * exp (-X) := by simp [F, e, w]
  rw [h1, h0] at hc
  have key : Uo (exp X b) = exp X * (exp (-X) * Uo (exp X b) * exp (-X)) * exp X := by
    rw [← mul_assoc, ← mul_assoc, exp_mul_exp_neg, one_mul, mul_assoc, exp_neg_mul_exp,
      mul_one]
  rw [key, hc]

theorem mulC_one : mulC (ouUnit A) = 1 := by
  ext z; exact JBAlgebra.one_mul z

theorem Uo_one : Uo (ouUnit A) = 1 := by
  rw [Uo, mulC_one, JBAlgebra.mul_one, mulC_one, mul_one, two_smul, add_sub_cancel_right]

/-- The exponential `e(h) := e^{L_h} 1 = Σ hⁿ/n!`. -/
def eE (h : A) : A := exp (mulC h) (ouUnit A)

/-- `U_{e(h)} = e^{L_h} e^{L_h}`. -/
theorem Uo_eE (h : A) : Uo (eE h) = exp (mulC h) * exp (mulC h) := by
  rw [eE, Uo_exp_apply, Uo_one, mul_one]

/-- **The fundamental formula at `a = e(h)`**. -/
theorem ff_eE (h b : A) : Uo (Uo (eE h) b) = Uo (eE h) * Uo b * Uo (eE h) := by
  rw [Uo_eE, mul_apply_eq_comp, Uo_exp_apply, Uo_exp_apply]
  noncomm_ring

/-! ## 3. Logarithms: every `c ≥ δ1` (`δ > 0`) is some `e(h)` -/

/-- The functional calculus of `c` as a bounded operator (it is isometric). -/
def jbCfcL (c : A) : C(jbSpec c, ℝ) →L[ℝ] A :=
  LinearMap.mkContinuous
    { toFun := jbCfc c
      map_add' := jbCfc_add c
      map_smul' := jbCfc_smul c } 1 fun f => by
    rw [one_mul]; exact (ousNorm_jbCfc c f).le

@[simp] theorem jbCfcL_apply (c : A) (f : C(jbSpec c, ℝ)) : jbCfcL c f = jbCfc c f := rfl

theorem mulC_pow_one (h : A) (n : ℕ) : (mulC h ^ n) (ouUnit A) = jbPow h n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, mulC_apply, jbPow_succ]

theorem hasSum_eE (h : A) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • jbPow h n) (eE h) := by
  have hs := exp_series_hasSum_exp' (𝕂 := ℝ) (mulC h)
  have := (ContinuousLinearMap.apply ℝ A (ouUnit A)).hasSum hs
  simp only [ContinuousLinearMap.apply_apply, smul_apply,
    mulC_pow_one] at this
  exact this

theorem jbPow_jbCfc (c : A) (g : C(jbSpec c, ℝ)) (n : ℕ) :
    jbPow (jbCfc c g) n = jbCfc c (g ^ n) := by
  induction n with
  | zero => rw [pow_zero, jbCfc_one]; rfl
  | succ n ih => rw [jbPow_succ, ih, pow_succ', jbCfc_mul]

theorem spec_ge {c : A} {δ : ℝ} (hc : δ • ouUnit A ≤ c) {t : ℝ} (ht : t ∈ jbSpec c) :
    δ ≤ t := by
  have e : jbCfc c (specId c - δ • 1) = c - δ • ouUnit A := by
    rw [← jbCfcL_apply, map_sub, map_smul, jbCfcL_apply, jbCfcL_apply, jbCfc_id, jbCfc_one]
  have h0 : 0 ≤ jbCfc c (specId c - δ • 1) := by rw [e]; exact sub_nonneg.2 hc
  have := (jbCfc_nonneg_iff c _).1 h0 ⟨t, ht⟩
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
    smul_eq_mul, mul_one] at this
  have : specId c ⟨t, ht⟩ = t := rfl
  linarith

/-- **Logarithms**: every `c ≥ δ1` with `δ > 0` is `e(h)` for `h = log c`. -/
theorem exists_eE_eq {c : A} {δ : ℝ} (hδ : 0 < δ) (hc : δ • ouUnit A ≤ c) :
    ∃ h : A, eE h = c := by
  have hpos : ∀ t : jbSpec c, 0 < t.1 := fun t => hδ.trans_le (spec_ge hc t.2)
  let g : C(jbSpec c, ℝ) := ⟨fun t => Real.log t.1,
    Real.continuousOn_log.comp_continuous continuous_subtype_val fun t => (hpos t).ne'⟩
  refine ⟨jbCfc c g, ?_⟩
  have h1 := hasSum_eE (jbCfc c g)
  simp only [jbPow_jbCfc] at h1
  have h2 := (jbCfcL c).hasSum (exp_series_hasSum_exp' (𝕂 := ℝ) g)
  simp only [map_smul, jbCfcL_apply] at h2
  rw [h1.unique h2]
  have hexp : exp g = specId c := by
    ext t
    have h3 := (ContinuousMap.evalCLM ℝ t).hasSum (exp_series_hasSum_exp' (𝕂 := ℝ) g)
    have h4 := exp_series_hasSum_exp' (𝕂 := ℝ) (g t)
    simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply,
      ContinuousMap.pow_apply] at h3
    rw [h3.unique h4, ← Real.exp_eq_exp_ℝ]
    exact Real.exp_log (hpos t)
  rw [hexp, jbCfc_id]

/-! ## 4. The fundamental formula in every JB-algebra -/

theorem analyticAt_Uo {x : ℝ → A} {t : ℝ} (hx : AnalyticAt ℝ x t) :
    AnalyticAt ℝ (fun s => Uo (x s)) t := by
  have h1 : AnalyticAt ℝ (fun s => mulC (x s)) t := ((mulC (A := A)).analyticAt _).comp hx
  have h2 : AnalyticAt ℝ (fun s => x s * x s) t :=
    AnalyticAt.comp (g := fun p : A × A => mulC p.1 p.2) (f := fun s => (x s, x s)) (x := t)
      ((mulC (A := A)).analyticAt_bilinear (x t, x t)) (hx.prod hx)
  have h3 : AnalyticAt ℝ (fun s => mulC (x s * x s)) t := ((mulC (A := A)).analyticAt _).comp h2
  exact ((analyticAt_const (v := (2 : ℝ))).smul (h1.mul h1)).sub h3

/-- **The fundamental formula** `U_{U_a b} = U_a U_b U_a` (Hanche-Olsen–Størmer 2.4.13), in
every JB-algebra: both sides are polynomial in `λ` along `a + λ1` and agree for
`λ > ‖a‖`, where `a + λ1 = e(log(a + λ1))` (`ff_eE`). -/
theorem Uo_Uo (a b : A) : Uo (Uo a b) = Uo a * Uo b * Uo a := by
  let x : ℝ → A := fun l => a + l • ouUnit A
  let D : ℝ → (A →L[ℝ] A) := fun l => Uo (Uo (x l) b) - Uo (x l) * Uo b * Uo (x l)
  have hx : ∀ t, AnalyticAt ℝ x t := fun t =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hD : AnalyticOnNhd ℝ D Set.univ := fun t _ => by
    have hU := analyticAt_Uo (hx t)
    have hUb : AnalyticAt ℝ (fun l => Uo (x l) b) t :=
      ((ContinuousLinearMap.apply ℝ A b).analyticAt _).comp hU
    exact (analyticAt_Uo hUb).sub ((hU.mul analyticAt_const).mul hU)
  have hz : D =ᶠ[𝓝 (ousNorm A a + 1)] 0 := by
    filter_upwards [Ioi_mem_nhds (show ousNorm A a < ousNorm A a + 1 by linarith)] with l hl
    have hle : (l - ousNorm A a) • ouUnit A ≤ x l := by
      have := (ousNorm_bounds_le a).1
      rw [sub_smul, sub_eq_neg_add]
      exact add_le_add this le_rfl
    obtain ⟨h, hh⟩ := exists_eE_eq (sub_pos.2 (Set.mem_Ioi.1 hl)) hle
    simp only [D, Pi.zero_apply]
    rw [← hh, ff_eE, sub_self]
  have := hD.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ _) hz (Set.mem_univ 0)
  simp only [D, x, zero_smul, add_zero, Pi.zero_apply] at this
  exact sub_eq_zero.1 this

/-- **The fundamental formula**, elementwise: `U_{U_a b} z = U_a U_b U_a z`. -/
theorem jQ_jQ (a b z : A) : jQ (jQ a b) z = jQ a (jQ b (jQ a z)) := by
  have := congrArg (fun T : A →L[ℝ] A => T z) (Uo_Uo a b)
  simp only [mul_apply_eq_comp, Uo_apply] at this
  exact this

/-- The power law `U_{a²} = U_a²` (the fundamental formula at `b = 1`). -/
theorem Uo_mul_self (a : A) : Uo (a * a) = Uo a * Uo a := by
  have h1 : Uo a (ouUnit A) = a * a := by
    rw [Uo_apply, jQ, JBAlgebra.mul_one, JBAlgebra.mul_one, two_smul, add_sub_cancel_right]
  have := Uo_Uo a (ouUnit A)
  rwa [h1, Uo_one, mul_one] at this

/-! ## 5. `e^{tL_h} ≥ 0`, and `U_c ≥ 0` for `c ≥ 0` -/

/-- For `z ≥ 0`: `z² ≤ ‖z‖ z` (functional calculus). -/
theorem mul_self_le_norm_smul {z : A} (hz : 0 ≤ z) : z * z ≤ ousNorm A z • z := by
  have e : jbCfc z (ousNorm A z • specId z - specId z * specId z) = ousNorm A z • z - z * z := by
    rw [← jbCfcL_apply, map_sub, map_smul, jbCfcL_apply, jbCfcL_apply, jbCfc_mul, jbCfc_id]
  have h0 : 0 ≤ jbCfc z (ousNorm A z • specId z - specId z * specId z) := by
    rw [jbCfc_nonneg_iff]
    intro t
    have h1 := jbSpec_nonneg hz t.2
    have h2 := (jbSpec_subset z t.2).2
    have : specId z t = t.1 := rfl
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      smul_eq_mul, this]
    nlinarith
  rw [e] at h0
  exact sub_nonneg.1 h0

/-- **The resolvent of `L_h` is positive** (Alfsen–Shultz's criterion for order derivations,
checked for `L_h` by Cauchy–Schwarz): if `l‖h‖ < 1` and `y − l·hy ≥ 0` then `y ≥ 0`. -/
theorem nonneg_of_resolvent {h y : A} {l : ℝ} (hl : 0 < l) (hlh : l * ousNorm A h < 1)
    (hx : 0 ≤ y - l • (h * y)) : 0 ≤ y := by
  by_contra hy
  set N := ousNorm A y
  set w := N • ouUnit A - y with hw
  have hw0 : 0 ≤ w := sub_nonneg.2 (ousNorm_bounds_le y).2
  have hwne : w ≠ 0 := by
    intro h0
    apply hy
    have : y = N • ouUnit A := by rw [hw, sub_eq_zero] at h0; exact h0.symm
    rw [this]; exact smul_nonneg (ousNorm_nonneg_rc y) ou_unit_nonneg
  obtain ⟨f, hf, hfw⟩ := exists_state_abs_eq_norm hwne
  set φ := stL hf
  have hφ : ∀ v, φ v = f v := fun _ => rfl
  have hpos : ∀ v : A, 0 ≤ v → 0 ≤ φ v := hf.2.2.1
  have h1 : φ (ouUnit A) = 1 := hf.2.2.2
  set M := ousNorm A w
  have hfw' : φ w = M := by
    rw [hφ, ← hfw, abs_of_nonneg (hf.2.2.1 w hw0)]
  set z := M • ouUnit A - w with hzdef
  have hz0 : 0 ≤ z := sub_nonneg.2 (ousNorm_bounds_le w).2
  have hfz : φ z = 0 := by rw [hzdef, map_sub, map_smul, h1, hfw', smul_eq_mul, mul_one, sub_self]
  set m := N - M
  have hyz : y = z + m • ouUnit A := by rw [hzdef, hw]; simp only [m, sub_smul]; abel
  have hm : m < 0 := by
    by_contra hm
    apply hy
    rw [hyz]
    exact add_nonneg hz0 (smul_nonneg (not_lt.1 hm) ou_unit_nonneg)
  -- `φ(z²) = 0`
  have hzz : φ (z * z) = 0 := by
    have a1 := hpos _ (jb_sq_nonneg z)
    have a2 := hpos _ (sub_nonneg.2 (mul_self_le_norm_smul hz0))
    rw [map_sub, map_smul, hfz, smul_zero, zero_sub] at a2
    linarith
  -- `φ(hz) = 0` (Cauchy–Schwarz)
  have hhz : φ (h * z) = 0 := by
    set B := φ (h * z)
    set C := φ (h * h)
    have hC : 0 ≤ C := hpos _ (jb_sq_nonneg h)
    have key : ∀ s : ℝ, 0 ≤ 2 * s * B + s * s * C := by
      intro s
      have e : (z + s • h) * (z + s • h) = z * z + (2 * s) • (h * z) + (s * s) • (h * h) := by
        simp only [JBAlgebra.add_mul, jb_mul_add, JBAlgebra.smul_mul, jb_mul_smul,
          JBAlgebra.mul_comm z h]
        module
      have := hpos _ (jb_sq_nonneg (z + s • h))
      rw [e, map_add, map_add, map_smul, map_smul, hzz, smul_eq_mul, smul_eq_mul] at this
      linarith
    have k := key (-B / (C + 1))
    have hC1 : 0 < C + 1 := by linarith
    have : 0 ≤ -(B ^ 2) * (C + 2) := by
      have e : 2 * (-B / (C + 1)) * B + -B / (C + 1) * (-B / (C + 1)) * C =
          -(B ^ 2) * (C + 2) / (C + 1) ^ 2 := by field_simp; ring
      rw [e] at k
      exact (div_nonneg_iff.1 k).elim (fun h => h.1) fun h => by
        nlinarith [h.2, sq_nonneg (C + 1), pow_pos hC1 2]
    nlinarith [sq_nonneg B]
  -- `φ((1 − lL_h)y) = m(1 − lφ(h)) < 0`
  have hval : φ (y - l • (h * y)) = m * (1 - l * φ h) := by
    rw [hyz, jb_mul_add, jb_mul_smul, JBAlgebra.mul_one, map_sub, map_smul, map_add, map_add,
      map_smul, map_smul, hfz, hhz, h1, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  have hφh : l * φ h < 1 := by
    have := state_abs_le hf h
    have : l * φ h ≤ l * ousNorm A h :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans this) hl.le
    linarith
  have := hpos _ hx
  rw [hval] at this
  nlinarith

/-- **`e^{tL_h}` is a positive operator** for every `t` (the resolvent criterion). -/
theorem exp_mulC_pos (h : A) (t : ℝ) : exp (t • mulC h) ∈ posOps (W := A) := by
  have key : ∀ (k : A) (t : ℝ), 0 ≤ t → exp (t • mulC k) ∈ posOps (W := A) := by
    intro k t ht
    refine exp_mem_posOps_of_resolvent (mulC k) (c := (ousNorm A k + 1)⁻¹) (by
      have := ousNorm_nonneg_rc k; positivity) (fun l hl hlc y hy hx => hy ?_) ht
    refine nonneg_of_resolvent (h := k) hl ?_ ?_
    · have hk := ousNorm_nonneg_rc k
      have : l * (ousNorm A k + 1) < 1 := by
        have h1 : 0 < ousNorm A k + 1 := by positivity
        have := mul_lt_mul_of_pos_right hlc h1
        rwa [inv_mul_cancel₀ h1.ne'] at this
      nlinarith
    · simpa [sub_apply, smul_apply] using hx
  rcases le_total 0 t with ht | ht
  · exact key h t ht
  · have e : t • mulC h = (-t) • mulC (-h) := by rw [map_neg, smul_neg, neg_smul, neg_neg]
    rw [e]; exact key (-h) (-t) (by linarith)

/-- `U_{e(h)} ≥ 0`. -/
theorem Uo_eE_pos (h : A) : Uo (eE h) ∈ posOps (W := A) := by
  rw [Uo_eE]
  have := exp_mulC_pos h 1
  rw [one_smul] at this
  exact mul_mem this this

/-- **`U_c` is positive for `c ≥ 0`**: `c + ε1 = e(log(c + ε1))` and `ε → 0`. -/
theorem jQ_nonneg_of_nonneg {c y : A} (hc : 0 ≤ c) (hy : 0 ≤ y) : 0 ≤ jQ c y := by
  let F : ℝ → A := fun ε => jQ c y + ε • ((2 : ℝ) • (c * y)) + (ε * ε) • y
  have hF : ∀ ε, F ε = Uo (c + ε • ouUnit A) y := fun ε => by
    simp only [F, Uo_apply, jQ, JBAlgebra.add_mul, jb_mul_add, JBAlgebra.smul_mul, jb_mul_smul,
      JBAlgebra.one_mul, JBAlgebra.mul_one, JBAlgebra.mul_comm (ouUnit A) y,
      _root_.smul_smul]
    module
  have hcont : Continuous F := by fun_prop
  have hcl : IsClosed {ε : ℝ | 0 ≤ F ε} := isClosed_nonneg.preimage hcont
  have hsub : Set.Ioi (0 : ℝ) ⊆ {ε : ℝ | 0 ≤ F ε} := by
    intro ε hε
    have hle : ε • ouUnit A ≤ c + ε • ouUnit A := le_add_of_nonneg_left hc
    obtain ⟨h, hh⟩ := exists_eE_eq (Set.mem_Ioi.1 hε) hle
    show 0 ≤ F ε
    rw [hF, ← hh]
    exact Uo_eE_pos h y hy
  have := hcl.closure_subset_iff.2 hsub (by rw [closure_Ioi]; exact Set.mem_Ici.2 le_rfl)
  simpa [F] using this

/-! ## 6. The swap trick: `U_a b ≥ 0` for every `a` -/

theorem Uo_Uo_apply (a b v : A) : Uo (Uo a b) v = Uo a (Uo b (Uo a v)) := by
  rw [Uo_Uo]; rfl

theorem Uo_mul_self_apply (a v : A) : Uo (a * a) v = Uo a (Uo a v) := by
  rw [Uo_mul_self]; rfl

theorem Uo_apply_one (a : A) : Uo a (ouUnit A) = a * a := by
  rw [Uo_apply, jQ, JBAlgebra.mul_one, JBAlgebra.mul_one, two_smul, add_sub_cancel_right]

theorem Uo_jbPow (x : A) (n : ℕ) : Uo x (jbPow x n) = jbPow x (n + 2) := by
  have h2 : x * x = jbPow x 2 := by
    rw [jbPow_succ, jbPow_one]
  rw [Uo_apply, jQ, ← jbPow_succ, ← jbPow_succ, h2, jbPow_mul_jbPow, two_smul,
    show 2 + n = n + 1 + 1 by omega, add_sub_cancel_right]

/-- **The swap identity** (`(TT*)ⁿ⁺¹ = T(T*T)ⁿT*` for `T = ac`): with `x = U_a(c²)` and
`y = U_c(a²)`, `x^{n+1} = U_a U_c (yⁿ)`; from the fundamental formula. -/
theorem swap_pow (a c : A) (n : ℕ) :
    jbPow (Uo a (c * c)) (n + 1) = Uo a (Uo c (jbPow (Uo c (a * a)) n)) := by
  set x := Uo a (c * c)
  set y := Uo c (a * a)
  have step : ∀ m, jbPow x (m + 1) = Uo a (Uo c (jbPow y m)) →
      jbPow x (m + 3) = Uo a (Uo c (jbPow y (m + 2))) := by
    intro m hm
    calc jbPow x (m + 3) = Uo x (jbPow x (m + 1)) := (Uo_jbPow x (m + 1)).symm
      _ = Uo a (Uo c (Uo c (Uo a (Uo a (Uo c (jbPow y m)))))) := by
          rw [hm, Uo_Uo_apply, Uo_mul_self_apply]
      _ = Uo a (Uo c (Uo y (jbPow y m))) := by
          rw [← Uo_mul_self_apply a, ← Uo_Uo_apply]
      _ = Uo a (Uo c (jbPow y (m + 2))) := by rw [Uo_jbPow]
  have base : ∀ m, jbPow x (m + 1) = Uo a (Uo c (jbPow y m)) ∧
      jbPow x (m + 2) = Uo a (Uo c (jbPow y (m + 1))) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [jbPow_one, jbPow_zero, Uo_apply_one]
      · rw [← Uo_jbPow x 0, jbPow_zero, Uo_Uo_apply, Uo_mul_self_apply, Uo_apply_one, zero_add,
          jbPow_one]
    | succ m ih => exact ⟨ih.2, step m ih.1⟩
  exact (base n).1

/-- The swap identity for polynomials: `x·p(x) = U_aU_c(p(y))`. -/
theorem swap_poly (a c : A) (p : Polynomial ℝ) :
    Uo a (c * c) * jbEv (Uo a (c * c)) p = Uo a (Uo c (jbEv (Uo c (a * a)) p)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, jb_mul_add, hp, hq, map_add, map_add, map_add]
  | monomial n r =>
    rw [jbEv_monomial, jbEv_monomial, jb_mul_smul, ← jbPow_succ, swap_pow, map_smul, map_smul]

/-- **Positivity of the quadratic map** (Hanche-Olsen–Størmer 3.3.6): in a JB-algebra
(REC 44), `U_a b = 2a(ab) − a²b ≥ 0` whenever `b ≥ 0`, for every `a`.  With `c = √b`,
`x = U_a(c²)` and `y = U_c(a²) ≥ 0` (`jQ_nonneg_of_nonneg`), the swap identity gives
`x f(x) = U_aU_c(f(y))` for continuous `f`; for `f(t) = max(−t, 0)` the right side is `0`,
so `sp x ⊆ [0, ∞)`. -/
theorem jQ_nonneg (a : A) {b : A} (hb : 0 ≤ b) : 0 ≤ jQ a b := by
  set c := jbSqrt b
  have hc : 0 ≤ c := jbSqrt_nonneg b
  have hcc : c * c = b := jbSqrt_mul_self hb
  set x := Uo a (c * c) with hxdef
  set y := Uo c (a * a) with hydef
  have hxb : jQ a b = x := by rw [hxdef, hcc, Uo_apply]
  have hy : 0 ≤ y := by rw [hydef, Uo_apply]; exact jQ_nonneg_of_nonneg hc (jb_sq_nonneg a)
  rw [hxb]
  let f : ℝ → ℝ := fun t => max (-t) 0
  have hf : Continuous f := by fun_prop
  let g : C(jbSpec x, ℝ) := ⟨fun t => f t.1, hf.comp continuous_subtype_val⟩
  set R := ousNorm A x + ousNorm A y
  set K := ‖Uo a * Uo c‖
  -- `x · g(x) = 0`
  have hzero : x * jbCfc x g = 0 := by
    have hbound : ∀ ε : ℝ, 0 < ε → ousNorm A (x * jbCfc x g) ≤ (K + ousNorm A x) * ε := by
      intro ε hε
      obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-R) R f hf.continuousOn ε hε
      have hy1 : ousNorm A (jbEv y p) ≤ ε := by
        rw [← jbCfc_specPoly, ousNorm_jbCfc]
        refine (ContinuousMap.norm_le _ hε.le).2 fun t => ?_
        have ht0 := jbSpec_nonneg hy t.2
        have htR := (jbSpec_subset y t.2).2
        have := hp t.1 ⟨by linarith [ousNorm_nonneg_rc x], by linarith [ousNorm_nonneg_rc x]⟩
        have hft : f t.1 = 0 := by simp only [f]; exact max_eq_right (by linarith)
        rw [hft, sub_zero] at this
        exact this.le
      have hx1 : ousNorm A (jbEv x p - jbCfc x g) ≤ ε := by
        rw [← jbCfc_specPoly, ← jbCfcL_apply, ← jbCfcL_apply, ← map_sub, jbCfcL_apply,
          ousNorm_jbCfc]
        refine (ContinuousMap.norm_le _ hε.le).2 fun t => ?_
        have htR := jbSpec_subset x t.2
        have := hp t.1 ⟨by linarith [ousNorm_nonneg_rc y, htR.1],
          by linarith [ousNorm_nonneg_rc y, htR.2]⟩
        exact this.le
      have e : x * jbCfc x g = Uo a (Uo c (jbEv y p)) - x * (jbEv x p - jbCfc x g) := by
        rw [← swap_poly, jb_mul_sub]; abel
      rw [e, sub_eq_add_neg]
      refine (ousNorm_add_le (V := A) _ _).trans ?_
      rw [ousNorm_neg]
      have h1 : ousNorm A (Uo a (Uo c (jbEv y p))) ≤ K * ε := by
        have := (Uo a * Uo c).le_opNorm (jbEv y p)
        rw [mul_apply_eq_comp] at this
        exact this.trans (mul_le_mul_of_nonneg_left hy1 (norm_nonneg _))
      have h2 := (jb_norm_mul_le x (jbEv x p - jbCfc x g)).trans
        (mul_le_mul_of_nonneg_left hx1 (ousNorm_nonneg_rc x))
      nlinarith
    have hK : 0 ≤ K + ousNorm A x := add_nonneg (norm_nonneg _) (ousNorm_nonneg_rc x)
    have hle : ousNorm A (x * jbCfc x g) ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := hbound (ε / (K + ousNorm A x + 1)) (by positivity)
      have e : (K + ousNorm A x) * (ε / (K + ousNorm A x + 1)) ≤ ε := by
        rw [mul_div_assoc']
        exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
      linarith
    exact IsOUS.norm_eq_zero _ (le_antisymm hle (ousNorm_nonneg_rc _))
  -- hence `t · max(−t, 0) = 0` on `sp x`, i.e. `sp x ⊆ [0, ∞)`
  have hprod : jbCfc x (specId x * g) = jbCfc x 0 := by
    rw [jbCfc_mul, jbCfc_id, hzero, ← jbCfcL_apply, map_zero]
  have hfun := jbCfc_injective x hprod
  rw [← jbCfc_id x, jbCfc_nonneg_iff]
  intro t
  have := congrArg (fun F : C(jbSpec x, ℝ) => F t) hfun
  simp only [ContinuousMap.mul_apply, ContinuousMap.zero_apply] at this
  change t.1 * max (-t.1) 0 = 0 at this
  show 0 ≤ t.1
  by_contra hneg
  replace hneg := not_le.1 hneg
  rw [max_eq_left (by linarith)] at this
  nlinarith

/-- **H-O–S 3.3.6 with the fundamental formula (H-O–S 2.4.13)**, for a JB-algebra in the
sense of REC 44: `U_a` is a positive map for every `a`, and
`U_{U_a b} = U_a U_b U_a`. -/
theorem hos336 :
    (∀ a b : A, 0 ≤ b → 0 ≤ jQ a b) ∧ ∀ a b z : A, jQ (jQ a b) z = jQ a (jQ b (jQ a z)) :=
  ⟨fun a _ hb => jQ_nonneg a hb, jQ_jQ⟩

end

end Papers.REC.JBMac
