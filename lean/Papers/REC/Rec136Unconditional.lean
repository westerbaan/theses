import Papers.REC.JBCoord
import Papers.REC.JBWSummandA
import Papers.SEA.JBAllSEA
import Theses.A.VN.Basic

/-!
# REC 136 with no named hypotheses

After `docs/research/special-kernel.md` (reviewed 2026-09-26, verdict STANDS).

Plan.  `JBCoord.rec136_summand_hypfree` needs `JBWExceptionalSummand` only to produce a
purely exceptional `V_W ≠ 0`, which is then refuted by `corner_absurd` (Jordan hom into
`B(Hs)`) and `pe_exists_exch_pair` (Gelfand, associative case).  Both refutations produce
**normal** Jordan homs into von Neumann algebras, so *normal* pure exceptionality
(`IsNormallyPurelyExceptional`) suffices; and that is exactly what the normal kernel
`J_n = cV` (`JBWSummandA.normalKernel_eq_corner`, proved) gives on its summand.
0. `IsNormallyPurelyExceptional`: every normal Jordan hom into a vN algebra vanishes.
1. Normal maps into `ℝ`: normal ⇒ monotone, `ε`-characterisation, sums, non-negative
   multiples, composition (`isNormal_comp`), domination (`isNormal_of_le`).
2. N1 (`isNormal_jQ`): `ω ∘ U_r` normal for `ω` positive normal and any `r`.  First
   `U_r` is order-normal for `0 ≤ r ≤ 1` (`jQ_isLUB` after passing to `{a ≥ a₀}`,
   translating by `a₀`, scaling by `‖s − a₀‖`), then for `r ≥ 0` (`U_{tr} = t²U_r`); general
   `r` by `U_r c ≤ 2U_a c + 2‖r‖²c` (`a = r + ‖r‖1`, polarisation) and domination.
   `exists_normal_state_pos`: `0 ≤ Q ≠ 0` ⇒ a normal state with `ω Q > 0`.
3. N3 (`clm_normal`): a map into `B(Hs β)` with self-adjoint values whose vector
   functionals `re⟪Φ(·)u,u⟫` (`u ∈ Cx β`, dense) are normal is normal (Loewner order;
   positivity tested on the dense `Cx β` and extended by closedness).
   `family_absurd`: the common end of both refutations — a `β`-bounded, `β`-symmetric
   Jordan family `T` with normal `a ↦ β(T_a x, x)` gives a normal Jordan hom `U → B(Hs)`,
   non-zero at `1`.
4. `corner_absurd_normal` (vector functionals `φ ∘ U_Q ∘ U_x ∘ ψ`, `jQ_jQ_eq`);
   `assoc_absurd_normal` (GNS for an associative JBW-algebra: `β(x,y) = φ(xy)`,
   `T_a = L_a`, `U_x c = x²c`); `npe_exists_exch_pair`.
5. REC glue: `corner_purelyExceptional_normal`, `corner_of_summand_normal` (the corner map
   `Pred(π_c)` is normal, `stateLin_normal`); `summand_absurd_normal` (`ψ = U_P ∘ (· ⊗ 1)`,
   REC 127 part 4); `rec135_nohyp` (`c = 0`: the product hom is injective; `c ≠ 0`: the
   summand is normally purely exceptional); `rec136_nohyp` (statement of
   `rec136_hypfree`, hypotheses only `hirr`, `h01`).
-/

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.REC.Rec136U

open Theses Theses.B.Eff Papers.REC Papers.REC.JBCoord Papers.REC.JBPeirce Papers.REC.JBWProj

universe u v w

noncomputable section

/-! ## 0. Normal pure exceptionality -/

section Def

variable (A : Type u) [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]

/-- **Normally purely exceptional**: every *normal* Jordan homomorphism of `A` into a von
Neumann algebra (Kadison's definition, universe `w`) is zero. -/
def IsNormallyPurelyExceptional : Prop :=
  ∀ (𝔄 : Type w) [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]
    [Theses.VonNeumannAlgebra 𝔄] (φ : A →ₗ[ℝ] 𝔄), IsJordanHomInto A 𝔄 φ → IsNormalMap φ → φ = 0

variable {A}

theorem isNormallyPurelyExceptional_of_pe (h : IsPurelyExceptional.{u, w} A) :
    IsNormallyPurelyExceptional.{u, w} A :=
  fun 𝔄 _ _ _ _ φ hφ _ => h 𝔄 φ hφ

end Def

/-! ## 1. Normal maps into `ℝ` -/

section Real

variable {P : Type*} [PartialOrder P]

theorem normal_monotone {Q : Type*} [PartialOrder Q] {f : P → Q} (hf : IsNormalMap f) :
    Monotone f := by
  intro a b hab
  have h : IsLUB ({a, b} : Set P) b :=
    ⟨by rintro x (rfl | rfl); exacts [hab, le_rfl], fun c hc => hc (by simp)⟩
  exact (hf {a, b} b (Set.insert_nonempty _ _)
    (by rintro x hx y hy; exact ⟨b, by simp, h.1 hx, h.1 hy⟩) h).1 ⟨a, by simp, rfl⟩

theorem normal_approx {f : P → ℝ} (hf : IsNormalMap f) {S : Set P} {s : P} (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) (hs : IsLUB S s) {ε : ℝ} (hε : 0 < ε) :
    ∃ d ∈ S, f s < f d + ε := by
  obtain ⟨_, ⟨d, hd, rfl⟩, h1, -⟩ := (hf S s hne hdir hs).exists_between (sub_lt_self (f s) hε)
  exact ⟨d, hd, by linarith⟩

theorem normal_of_approx {f : P → ℝ} (hm : Monotone f)
    (h : ∀ (S : Set P) (s : P), S.Nonempty → DirectedOn (· ≤ ·) S → IsLUB S s →
      ∀ ε : ℝ, 0 < ε → ∃ d ∈ S, f s < f d + ε) : IsNormalMap f := by
  intro S s hne hdir hs
  refine ⟨by rintro _ ⟨x, hx, rfl⟩; exact hm (hs.1 hx),
    fun b hb => le_of_forall_pos_lt_add fun ε hε => ?_⟩
  obtain ⟨d, hd, h⟩ := h S s hne hdir hs ε hε
  have := hb ⟨d, hd, rfl⟩
  linarith

theorem isNormal_add {f g : P → ℝ} (hf : IsNormalMap f) (hg : IsNormalMap g) :
    IsNormalMap (fun a => f a + g a) := by
  refine normal_of_approx (fun a b h => add_le_add (normal_monotone hf h) (normal_monotone hg h))
    fun S s hne hdir hs ε hε => ?_
  obtain ⟨d1, hd1, h1⟩ := normal_approx hf hne hdir hs (half_pos hε)
  obtain ⟨d2, hd2, h2⟩ := normal_approx hg hne hdir hs (half_pos hε)
  obtain ⟨d, hd, e1, e2⟩ := hdir d1 hd1 d2 hd2
  have m1 := normal_monotone hf e1
  have m2 := normal_monotone hg e2
  exact ⟨d, hd, by linarith⟩

theorem isNormal_mul {f : P → ℝ} (hf : IsNormalMap f) {c : ℝ} (hc : 0 ≤ c) :
    IsNormalMap (fun a => c * f a) := by
  refine normal_of_approx (fun a b h => mul_le_mul_of_nonneg_left (normal_monotone hf h) hc)
    fun S s hne hdir hs ε hε => ?_
  have hc1 : 0 < c + 1 := by linarith
  obtain ⟨d, hd, h⟩ := normal_approx hf hne hdir hs (div_pos hε hc1)
  refine ⟨d, hd, ?_⟩
  have k1 : c * f s ≤ c * f d + c * (ε / (c + 1)) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left h.le hc
  have k2 : c * (ε / (c + 1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hc1]; nlinarith
  linarith

/-- Normal after monotone-normal (the inner map is monotone because it is normal). -/
theorem isNormal_comp {Q R : Type*} [PartialOrder Q] [PartialOrder R] {g : Q → R} {f : P → Q}
    (hg : IsNormalMap g) (hf : IsNormalMap f) : IsNormalMap (g ∘ f) := by
  intro S s hne hdir hs
  have h := hf S s hne hdir hs
  rw [Set.image_comp]
  exact hg _ _ (hne.image f) (hdir.mono_comp (normal_monotone hf)) h

/-- Least upper bounds are transported by a monotone bijection with monotone inverse. -/
theorem isLUB_image_of_inv {S : Set P} {x : P} {g h : P → P} (hg : Monotone g) (hh : Monotone h)
    (hhg : ∀ x, h (g x) = x) (hgh : ∀ y, g (h y) = y) (hx : IsLUB S x) : IsLUB (g '' S) (g x) := by
  refine ⟨by rintro _ ⟨a, ha, rfl⟩; exact hg (hx.1 ha), fun u hu => ?_⟩
  have : x ≤ h u := hx.2 fun a ha => by rw [← hhg a]; exact hh (hu ⟨a, ha, rfl⟩)
  calc g x ≤ g (h u) := hg this
    _ = u := hgh u

end Real

section Lin

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]

/-- **Domination**: a positive functional below a normal one on the positive cone is
normal (`ψ(s) − ψ(d) ≤ ω(s − d)`; the argument of `JBWProj.isNormal_of_dom`). -/
theorem isNormal_of_le {ψ ω : V →ₗ[ℝ] ℝ} (hψ : ∀ v, 0 ≤ v → 0 ≤ ψ v) (hω : IsNormalMap ω)
    (hle : ∀ v, 0 ≤ v → ψ v ≤ ω v) : IsNormalMap ψ := by
  have hm : Monotone ψ := fun a b h => by
    have := hψ _ (sub_nonneg.2 h); rwa [map_sub, sub_nonneg] at this
  refine normal_of_approx hm fun S s hne hdir hs ε hε => ?_
  obtain ⟨d, hd, h⟩ := normal_approx hω hne hdir hs hε
  refine ⟨d, hd, ?_⟩
  have := hle _ (sub_nonneg.2 (hs.1 hd))
  rw [map_sub, map_sub] at this
  linarith

end Lin

/-! ## 2. N1: `ω ∘ U_r` is normal -/

section N1

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

/-- `U_r` as a linear map. -/
def jQL (r : V) : V →ₗ[ℝ] V where
  toFun := jQ r
  map_add' := Papers.SEA.JBAll.jQ_add r
  map_smul' c b := Papers.SEA.JBAll.jQ_smul r c b

@[simp] theorem jQL_apply (r x : V) : jQL r x = jQ r x := rfl

theorem jQ_smul_left (t : ℝ) (r y : V) : jQ (t • r) y = (t * t) • jQ r y := by
  simp only [jQ, jsmul_mul, jmul_smul, _root_.smul_smul, smul_sub]
  module

theorem jQ_polar (x y z : V) :
    jQ (x - y) z + jQ (x + y) z = (2 : ℝ) • jQ x z + (2 : ℝ) • jQ y z := by
  simp only [jQ, jsub_mul, jadd_mul, jmul_sub, jmul_add, smul_sub, smul_add]
  module

theorem jQ_monotone (r : V) : Monotone (jQ r) := fun _ _ h => Papers.SEA.JBAll.jQ_mono r h

/-- `U_r` preserves directed suprema for `0 ≤ r ≤ 1`. -/
theorem jQ_normal01 {r : V} (hr0 : 0 ≤ r) (hr1 : r ≤ ouUnit V) : IsNormalMap (jQ r) := by
  intro S s hne hdir hs
  obtain ⟨a₀, ha₀⟩ := hne
  set S' := {a | a ∈ S ∧ a₀ ≤ a} with hS'
  have hS's : IsLUB S' s := by
    refine ⟨fun a ha => hs.1 ha.1, fun u hu => hs.2 fun a ha => ?_⟩
    obtain ⟨d, hd, h1, h2⟩ := hdir a₀ ha₀ a ha
    exact h2.trans (hu ⟨hd, h1⟩)
  have hmono := jQ_monotone r
  suffices h : IsLUB (jQ r '' S') (jQ r s) by
    refine ⟨by rintro _ ⟨a, ha, rfl⟩; exact hmono (hs.1 ha), fun u hu => h.2 ?_⟩
    rintro _ ⟨a, ha, rfl⟩; exact hu ⟨a, ha.1, rfl⟩
  have hsa : a₀ ≤ s := hs.1 ha₀
  set k := ousNorm V (s - a₀) with hk
  by_cases hk0 : k = 0
  · have e : s = a₀ := (sub_eq_zero.1 (IsOUS.norm_eq_zero _ hk0))
    exact ⟨by rintro _ ⟨a, ha, rfl⟩; exact hmono (hS's.1 ha),
      fun u hu => hu ⟨a₀, ⟨ha₀, le_rfl⟩, by rw [e]⟩⟩
  have hkpos : 0 < k := lt_of_le_of_ne (ousNorm_nonneg_rc _) (Ne.symm hk0)
  have hkinv : 0 ≤ k⁻¹ := inv_nonneg.2 hkpos.le
  let g : V → V := fun y => k⁻¹ • (y - a₀)
  let h : V → V := fun y => k • y + a₀
  have hg : Monotone g := fun a b hab => ou_smul_le_smul hkinv (sub_le_sub_right hab _)
  have hh : Monotone h := fun a b hab => add_le_add (ou_smul_le_smul hkpos.le hab) le_rfl
  have hhg : ∀ y, h (g y) = y := fun y => by
    simp only [h, g, _root_.smul_smul, mul_inv_cancel₀ hk0, one_smul, sub_add_cancel]
  have hgh : ∀ y, g (h y) = y := fun y => by
    simp only [h, g, add_sub_cancel_right, _root_.smul_smul, inv_mul_cancel₀ hk0, one_smul]
  have hS'' := isLUB_image_of_inv hg hh hhg hgh hS's
  have hle1 : ∀ a, a₀ ≤ a → a ≤ s → g a ∈ Set.Icc (0 : V) (ouUnit V) := by
    intro a h1 h2
    refine ⟨ou_smul_nonneg hkinv (sub_nonneg.2 h1), ?_⟩
    have e1 : a - a₀ ≤ k • ouUnit V := (sub_le_sub_right h2 _).trans (ousNorm_bounds_le _).2
    have := ou_smul_le_smul hkinv e1
    rwa [_root_.smul_smul, inv_mul_cancel₀ hk0, one_smul] at this
  have hsub : g '' S' ⊆ Set.Icc 0 (ouUnit V) := by
    rintro _ ⟨a, ha, rfl⟩; exact hle1 a ha.2 (hS's.1 ha)
  have h1 := Papers.SEA.JBAll.jQ_isLUB hr0 hr1 hsub (hle1 s hsa le_rfl) hS''
  let G : V → V := fun z => k • z + jQ r a₀
  let H : V → V := fun z => k⁻¹ • (z - jQ r a₀)
  have hG : Monotone G := fun a b hab => add_le_add (ou_smul_le_smul hkpos.le hab) le_rfl
  have hH : Monotone H := fun a b hab => ou_smul_le_smul hkinv (sub_le_sub_right hab _)
  have hHG : ∀ y, H (G y) = y := fun y => by
    simp only [H, G, add_sub_cancel_right, _root_.smul_smul, inv_mul_cancel₀ hk0, one_smul]
  have hGH : ∀ y, G (H y) = y := fun y => by
    simp only [H, G, _root_.smul_smul, mul_inv_cancel₀ hk0, one_smul, sub_add_cancel]
  have h2 := isLUB_image_of_inv hG hH hHG hGH h1
  have e : ∀ y, G (jQ r (g y)) = jQ r y := fun y => by
    simp only [G, g, Papers.SEA.JBAll.jQ_smul, Papers.SEA.JBAll.jQ_sub, _root_.smul_smul,
      mul_inv_cancel₀ hk0, one_smul, sub_add_cancel]
  simp only [Set.image_image, e] at h2
  exact h2

/-- `U_r` preserves directed suprema for `r ≥ 0`. -/
theorem jQ_normal_nonneg {r : V} (hr0 : 0 ≤ r) : IsNormalMap (jQ r) := by
  set t := ousNorm V r + 1 with ht
  have htpos : 0 < t := by have := ousNorm_nonneg_rc (V := V) r; rw [ht]; linarith
  have ht0 : t ≠ 0 := htpos.ne'
  set r' := t⁻¹ • r with hr'
  have hr'0 : 0 ≤ r' := ou_smul_nonneg (inv_nonneg.2 htpos.le) hr0
  have hr'1 : r' ≤ ouUnit V := by
    have e1 : r ≤ t • ouUnit V := (ousNorm_bounds_le r).2.trans
      (by rw [ht, add_smul, one_smul]; exact le_add_of_nonneg_right ou_unit_nonneg)
    have := ou_smul_le_smul (inv_nonneg.2 htpos.le) e1
    rwa [_root_.smul_smul, inv_mul_cancel₀ ht0, one_smul] at this
  have hrr : r = t • r' := by rw [hr', _root_.smul_smul, mul_inv_cancel₀ ht0, one_smul]
  have htt : 0 < t * t := mul_pos htpos htpos
  intro S s hne hdir hs
  have h1 := jQ_normal01 hr'0 hr'1 S s hne hdir hs
  have h2 := isLUB_image_of_inv (g := fun z : V => (t * t) • z) (h := fun z => (t * t)⁻¹ • z)
    (fun a b hab => ou_smul_le_smul htt.le hab)
    (fun a b hab => ou_smul_le_smul (inv_nonneg.2 htt.le) hab)
    (fun y => by simp only [_root_.smul_smul, inv_mul_cancel₀ htt.ne', one_smul])
    (fun y => by simp only [_root_.smul_smul, mul_inv_cancel₀ htt.ne', one_smul]) h1
  have e : ∀ y, (t * t) • jQ r' y = jQ r y := fun y =>
    ((congrArg (fun z => jQ z y) hrr).trans (jQ_smul_left t r' y)).symm
  simp only [Set.image_image, e] at h2
  exact h2

/-- **N1**: `ω ∘ U_r` is normal, for `ω` a positive normal functional and any `r`. -/
theorem isNormal_jQ {ω : V →ₗ[ℝ] ℝ} (hω0 : ∀ v, 0 ≤ v → 0 ≤ ω v) (hω : IsNormalMap ω) (r : V) :
    IsNormalMap (ω ∘ₗ jQL r) := by
  set t := ousNorm V r with ht
  set a := r + t • ouUnit V with ha
  have ha0 : 0 ≤ a := by
    have := (ousNorm_bounds_le r).1
    rw [ha, ← sub_neg_eq_add]; exact sub_nonneg.2 this
  set ω' : V →ₗ[ℝ] ℝ := (2 : ℝ) • (ω ∘ₗ jQL a) + (2 * t * t) • ω with hω'
  have hN : IsNormalMap ω' := by
    have e : (ω' : V → ℝ) = fun v => 2 * (ω ∘ jQ a) v + (2 * t * t) * ω v := by
      funext v; simp [hω']
    rw [e]
    exact isNormal_add (isNormal_mul (isNormal_comp hω (jQ_normal_nonneg ha0)) (by norm_num))
      (isNormal_mul hω (by have := ousNorm_nonneg_rc (V := V) r; rw [← ht] at this; positivity))
  refine isNormal_of_le (fun v hv => hω0 _ (JBMac.jQ_nonneg r hv)) hN fun v hv => ?_
  have pol := jQ_polar a (t • ouUnit V) v
  have hb : jQ (t • ouUnit V) v = (t * t) • v := by
    rw [jQ_smul_left, Papers.SEA.JBAll.jQ_one_left]
  rw [show a - t • ouUnit V = r by rw [ha, add_sub_cancel_right], hb] at pol
  have hpos := JBMac.jQ_nonneg (a + t • ouUnit V) hv
  have hle : jQ r v ≤ (2 : ℝ) • jQ a v + (2 : ℝ) • ((t * t) • v) := by
    rw [← pol]; exact le_add_of_nonneg_right hpos
  have := hω0 _ (sub_nonneg.2 hle)
  simp only [map_sub, map_add, map_smul, smul_eq_mul, sub_nonneg] at this
  simp only [hω', LinearMap.comp_apply, jQL_apply, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  linarith

end N1

section States

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- A non-zero positive element is seen by some normal state. -/
theorem exists_normal_state_pos {Q : V} (hQ : 0 ≤ Q) (hQ0 : Q ≠ 0) :
    ∃ ω : OUSState V, IsNormalMap ω.toLin ∧ 0 < ω.toLin Q := by
  obtain ⟨ω, hωn, hne⟩ := hW.separating Q 0 hQ0
  refine ⟨ω, hωn, lt_of_le_of_ne (ω.nonneg Q hQ) ?_⟩
  rw [map_zero] at hne; exact Ne.symm hne

end States

/-! ## 3. N3: normality into `B(Hs β)` -/

section Hilb

variable {W : Type v} [AddCommGroup W] [Module ℝ W] {β : PsdForm W}

theorem re_inner_mono {A B : Hs β →L[ℂ] Hs β} (h : A ≤ B) (x : Hs β) :
    (inner ℂ (A x) x).re ≤ (inner ℂ (B x) x).re := by
  have := ((ContinuousLinearMap.le_def A B).1 h).re_inner_nonneg_left x
  rw [_root_.sub_apply, inner_sub_left, map_sub, RCLike.re_to_complex,
    RCLike.re_to_complex] at this
  linarith

/-- Loewner order tested on the dense subspace `Cx β`. -/
theorem le_of_dense {S T : Hs β →L[ℂ] Hs β} (hsa : IsSelfAdjoint (T - S))
    (h : ∀ u : Cx β, (inner ℂ (S (u : Hs β)) (u : Hs β)).re ≤
      (inner ℂ (T (u : Hs β)) (u : Hs β)).re) : S ≤ T := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  refine ⟨hsa, fun x => ?_⟩
  refine UniformSpace.Completion.induction_on x
    (p := fun x => 0 ≤ (T - S).reApplyInnerSelf x)
    (isClosed_le continuous_const (T - S).reApplyInnerSelf_continuous) fun u => ?_
  have := h u
  show 0 ≤ (T - S).reApplyInnerSelf (u : Hs β)
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, _root_.sub_apply, inner_sub_left,
    map_sub, RCLike.re_to_complex, RCLike.re_to_complex]
  linarith

/-- **N3**: a map into `B(Hs β)` with self-adjoint values and normal vector functionals
`a ↦ re⟪Φ(a)u, u⟫` (`u ∈ Cx β`) is normal. -/
theorem clm_normal {P : Type*} [PartialOrder P] (Φ : P → (Hs β →L[ℂ] Hs β))
    (hsa : ∀ a, IsSelfAdjoint (Φ a))
    (hρ : ∀ u : Cx β, IsNormalMap (fun a => (inner ℂ (Φ a (u : Hs β)) (u : Hs β)).re)) :
    IsNormalMap Φ := by
  intro S s hne hdir hs
  refine ⟨?_, fun B hB => ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact le_of_dense ((hsa s).sub (hsa a)) fun u => ((hρ u) S s hne hdir hs).1 ⟨a, ha, rfl⟩
  · obtain ⟨a₀, ha₀⟩ := hne
    have hB0 : Φ a₀ ≤ B := hB ⟨a₀, ha₀, rfl⟩
    have hBsa : IsSelfAdjoint B := by
      have := (((ContinuousLinearMap.le_def _ _).1 hB0).isSelfAdjoint).add (hsa a₀)
      rwa [sub_add_cancel] at this
    refine le_of_dense (hBsa.sub (hsa s)) fun u => ?_
    refine ((hρ u) S s ⟨a₀, ha₀⟩ hdir hs).2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact re_inner_mono (hB ⟨a, ha, rfl⟩) _

/-- **The common end of both refutations**: a `β`-bounded, `β`-symmetric Jordan family
`a ↦ T_a` (`T_1 = id`, `β ≢ 0`) whose functionals `a ↦ β(T_a x, x)` are normal gives the
normal, non-zero Jordan homomorphism `a ↦ opC β T_a` into the von Neumann algebra
`B(Hs β)`. -/
theorem family_absurd {U : Type v} [AddCommGroup U] [Module ℝ U] [PartialOrder U]
    [OrderUnitSpace U] [Mul U] (hpe : IsNormallyPurelyExceptional.{v, v} U) (β : PsdForm W)
    (T : U → W →ₗ[ℝ] W) (hTb : ∀ a, IsBdd β (T a))
    (hTs : ∀ a x y, β.B (T a x) y = β.B x (T a y))
    (hTadd : ∀ a b, T (a + b) = T a + T b) (hTsmul : ∀ (r : ℝ) a, T (r • a) = r • T a)
    (hTmul : ∀ a b, T (a * b) = (2⁻¹ : ℝ) • (T a ∘ₗ T b + T b ∘ₗ T a))
    (hT1 : T (ouUnit U) = LinearMap.id) {x₀ : W} (hx₀ : 0 < β.B x₀ x₀)
    (hρ : ∀ x : W, IsNormalMap (fun a => β.B (T a x) x)) : False := by
  have hsm : ∀ (r : ℝ) (A : Hs β →L[ℂ] Hs β), (r : ℂ) • A = r • A := fun r A =>
    (RCLike.real_smul_eq_coe_smul (K := ℂ) r A).symm
  let Φ : U →ₗ[ℝ] (Hs β →L[ℂ] Hs β) :=
    { toFun := fun a => opC β (T a)
      map_add' := fun a b => by rw [hTadd, opC_add (hTb a) (hTb b)]
      map_smul' := fun r a => by
        rw [hTsmul, opC_smul r (hTb a), RingHom.id_apply, hsm] }
  have hΦJ : IsJordanHomInto U (Hs β →L[ℂ] Hs β) Φ := by
    refine ⟨fun a => opC_selfAdjoint (hTb a) (hTs a), fun a b => ?_⟩
    show opC β (T (a * b)) = _
    have hab := isBdd_comp (hTb a) (hTb b)
    have hba := isBdd_comp (hTb b) (hTb a)
    rw [hTmul, opC_smul _ (isBdd_add hab hba), opC_add hab hba, opC_comp (hTb a) (hTb b),
      opC_comp (hTb b) (hTb a), hsm]
    rfl
  have hΦN : IsNormalMap Φ := by
    refine clm_normal (β := β) Φ hΦJ.1 fun u => ?_
    have e : (fun a => (inner ℂ (Φ a (u : Hs β)) (u : Hs β)).re) =
        fun a => β.B (T a u.re) u.re + β.B (T a u.im) u.im := by
      funext a
      show (inner ℂ (opC β (T a) (u : Hs β)) (u : Hs β)).re = _
      rw [opC_coe (hTb a), UniformSpace.Completion.inner_coe, Cx.inner_eq]
      simp only [Cx.inn, Tc_re, Tc_im]
    rw [e]
    exact isNormal_add (hρ u.re) (hρ u.im)
  have h0 := hpe (Hs β →L[ℂ] Hs β) Φ hΦJ hΦN
  have h1 : Φ (ouUnit U) = 1 := by
    show opC β (T (ouUnit U)) = 1
    rw [hT1, opC_id]
  exact one_ne_zero_of_pos (β := β) hx₀ (by rw [← h1, h0]; rfl)

end Hilb

/-! ## 4. The two refutations, for normally purely exceptional algebras -/

section CoreN

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- **`corner_absurd` for normal pure exceptionality**: `V` JBW, `P ⊥ Q` connected by `w`,
`Q ≠ 0`, `ψ : U → V` a unital-onto-`P` Jordan hom that pulls positive normal functionals
back to normal ones.  With a *normal* state `φ`, `φ Q > 0`, the vector functionals of
`a ↦ opC β (2ψ(a)·)` are `φ ∘ U_Q ∘ U_x ∘ ψ` (`jQ_jQ_eq`), normal by N1. -/
theorem corner_absurd_normal {P Q : V} (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0)
    {U : Type v} [AddCommGroup U] [Module ℝ U] [PartialOrder U]
    [OrderUnitSpace U] [Mul U] (hpe : IsNormallyPurelyExceptional.{v, v} U)
    (hu : ∀ a : U, ouUnit U * a = a) (ψ : U →ₗ[ℝ] V) (hψ : ∀ a b, ψ (a * b) = ψ a * ψ b)
    (hψ1 : ψ (ouUnit U) = P)
    (hψN : ∀ ω : V →ₗ[ℝ] ℝ, (∀ v, 0 ≤ v → 0 ≤ ω v) → IsNormalMap ω → IsNormalMap (ω ∘ₗ ψ))
    {w : V} (hwP : w ∈ peirce P (1 / 2))
    (hwQ : w ∈ peirce Q (1 / 2)) (hw : w * w = P + Q) (hQ0 : Q ≠ 0) : False := by
  have hQn : 0 ≤ Q := by rw [← hQ]; exact jb_sq_nonneg Q
  obtain ⟨ω, hωN, hωQ⟩ := exists_normal_state_pos hQn hQ0
  set φ := ω.toLin with hφdef
  have hφ : ∀ z, 0 ≤ z → 0 ≤ φ z := ω.nonneg
  set β := formW (P := P) hQ φ hφ with hβ
  have hmem : ∀ a, ψ a ∈ peirce P 1 := fun a => by
    rw [mem_peirce, one_smul, ← hψ1, ← hψ, hu]
  let T : U → Wsp P Q →ₗ[ℝ] Wsp P Q := fun a => Lc hP hQ hPQ (ψ a) (hmem a)
  have hTadd : ∀ a b, T (a + b) = T a + T b := fun a b =>
    LinearMap.ext fun x => Subtype.ext (by
      simp only [T, Lc_val, LinearMap.add_apply, Submodule.coe_add, map_add, jadd_mul, smul_add])
  have hTsmul : ∀ (r : ℝ) a, T (r • a) = r • T a := fun r a =>
    LinearMap.ext fun x => Subtype.ext (by
      simp only [T, Lc_val, LinearMap.smul_apply, Submodule.coe_smul, map_smul, jsmul_mul]
      rw [smul_comm])
  have hTmul : ∀ a b, T (a * b) = (2⁻¹ : ℝ) • (T a ∘ₗ T b + T b ∘ₗ T a) := fun a b => by
    have h := Lc_mul hP hQ hPQ (hmem a) (hmem b)
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hx := congrArg (fun L : Wsp P Q →ₗ[ℝ] Wsp P Q => (L x).1) h
    rw [← hx]
    simp only [T, Lc_val, hψ]
  have hT1 : T (ouUnit U) = LinearMap.id := LinearMap.ext fun x => Subtype.ext (by
    simp only [T, Lc_val, hψ1, LinearMap.id_apply]
    rw [x.2.1, _root_.smul_smul]; norm_num)
  refine family_absurd hpe β T (fun a => Lc_bdd hP hQ hPQ φ hφ (hmem a))
    (fun a => Lc_symm hP hQ hPQ φ hφ (hmem a)) hTadd hTsmul hTmul hT1
    (x₀ := ⟨w, hwP, hwQ⟩) ?_ fun x => ?_
  · rw [hβ, formW_apply]
    show 0 < φ (Q * (w * w))
    rw [hw, jmul_add, jmul_comm Q P, hPQ, zero_add, hQ]
    exact hωQ
  · have hφQ : ∀ v, 0 ≤ v → 0 ≤ (φ ∘ₗ jQL Q) v := fun v hv => hφ _ (JBMac.jQ_nonneg Q hv)
    have hφQx : ∀ v, 0 ≤ v → 0 ≤ ((φ ∘ₗ jQL Q) ∘ₗ jQL x.1) v := fun v hv =>
      hφQ _ (JBMac.jQ_nonneg x.1 hv)
    have e : (fun a => β.B (T a x) x) = ⇑(((φ ∘ₗ jQL Q) ∘ₗ jQL x.1) ∘ₗ ψ) := by
      funext a
      simp only [LinearMap.comp_apply, jQL_apply]
      rw [jQ_jQ_eq hQ (Q_mul_of_one hP hPQ (hmem a)) x.2.2, map_smul, smul_eq_mul, hβ,
        formW_apply]
      show φ (Q * (((2 : ℝ) • (ψ a * x.1)) * x.1)) = _
      rw [jsmul_mul, jmul_smul, map_smul, smul_eq_mul]
    rw [e]
    exact hψN _ hφQx (isNormal_jQ hφQ (isNormal_jQ hφ hωN Q) x.1)

/-- **The associative case by GNS**: an associative JBW-algebra `V ≠ 0` is not normally
purely exceptional.  `β(x, y) = φ(xy)` for a normal state `φ`, `T_a = L_a`
(`L_{ab} = L_a L_b`, `β`-symmetric), bounded since `(ax)² = U_x(a²) ≤ ‖a‖²x²`; the vector
functionals `a ↦ φ((ax)x) = φ(U_x a)` are normal by N1. -/
theorem assoc_absurd_normal (hpe : IsNormallyPurelyExceptional.{v, v} V) (h1 : ouUnit V ≠ 0)
    (hB : ∀ a b c : V, a * b * c = a * (b * c)) : False := by
  obtain ⟨ω, hωN, hω1⟩ := exists_normal_state_pos (Q := ouUnit V) ou_unit_nonneg h1
  set φ := ω.toLin with hφdef
  have hφ : ∀ z, 0 ≤ z → 0 ≤ φ z := ω.nonneg
  have hcomm : ∀ a b : V, a * b = b * a := JBAlgebra.mul_comm
  have hUx : ∀ x c : V, jQ x c = (x * x) * c := fun x c => by
    rw [jQ, ← hB x x c]; module
  let β : PsdForm V :=
    { B := LinearMap.mk₂ ℝ (fun x y => φ (x * y))
        (fun x x' y => by simp only [jadd_mul, map_add])
        (fun r x y => by simp only [jsmul_mul, map_smul, smul_eq_mul])
        (fun x y y' => by simp only [jmul_add, map_add])
        (fun r x y => by simp only [jmul_smul, map_smul, smul_eq_mul])
      symm := fun x y => by simp only [LinearMap.mk₂_apply]; rw [hcomm x y]
      nonneg := fun x => by simp only [LinearMap.mk₂_apply]; exact hφ _ (jb_sq_nonneg x) }
  have hβ : ∀ x y, β.B x y = φ (x * y) := fun x y => rfl
  refine family_absurd hpe β jbT (fun a => ?_) (fun a x y => ?_) (fun a b => ?_) (fun r a => ?_)
    (fun a b => ?_) ?_ (x₀ := ouUnit V) ?_ fun x => ?_
  · set r := ousNorm V a + 1
    have hr : 0 < r := by have := ousNorm_nonneg_rc (V := V) a; simp only [r]; linarith
    obtain ⟨-, h2⟩ := jb_sq_bounds (a := a) hr (by simp only [r]; linarith)
    refine ⟨r * r, by positivity, fun x => ?_⟩
    rw [hβ, hβ, jbT_apply]
    have e : a * x * (a * x) = jQ x (a * a) := by
      rw [hUx, hB a x (a * x), hcomm a x, ← hB x x a, hcomm (x * x) a, ← hB a a (x * x)]
      exact hcomm _ _
    rw [e]
    have hd := JBMac.jQ_nonneg x (sub_nonneg.2 h2)
    rw [Papers.SEA.JBAll.jQ_sub, Papers.SEA.JBAll.jQ_smul, Papers.SEA.JBAll.jQ_one] at hd
    have := hφ _ hd
    rw [map_sub, map_smul, smul_eq_mul, sub_nonneg] at this
    exact this
  · rw [hβ, hβ, jbT_apply, jbT_apply, hcomm a x, hB x a y]
  · exact LinearMap.ext fun x => by simp only [jbT_apply, LinearMap.add_apply, jadd_mul]
  · exact LinearMap.ext fun x => by simp only [jbT_apply, LinearMap.smul_apply, jsmul_mul]
  · refine LinearMap.ext fun x => ?_
    simp only [jbT_apply, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply]
    rw [← hB a b x, ← hB b a x, hcomm b a]
    module
  · exact LinearMap.ext fun x => by rw [jbT_apply, LinearMap.id_apply, JBAlgebra.one_mul]
  · rw [hβ, JBAlgebra.mul_one]; exact hω1
  · have e : (fun a => β.B (jbT a x) x) = ⇑(φ ∘ₗ jQL x) := by
      funext a
      rw [hβ, jbT_apply, LinearMap.comp_apply, jQL_apply, hUx, hB a x x, hcomm a (x * x)]
    rw [e]
    exact isNormal_jQ hφ hωN x

/-- **A non-zero normally purely exceptional JBW-algebra has an exchangeable pair**
(`pe_exists_exch_pair` with `assoc_absurd_normal` in place of Gelfand). -/
theorem npe_exists_exch_pair (hpe : IsNormallyPurelyExceptional.{v, v} V) (h1 : ouUnit V ≠ 0) :
    ∃ p q : V, p * q = 0 ∧ p ≠ 0 ∧ q ≠ 0 ∧ ExchangeableBySymmetry p q :=
  exists_exch_pair fun hassoc => assoc_absurd_normal hpe h1 hassoc

end CoreN

/-! ## 5. REC glue -/

section CornerN

open CategoryTheory SequentialEffectus
open scoped Papers.SEA

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (σs : ScalarSplit C)
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C) (h0 : σs.s = 0)

include h0 in
/-- `Monoidal.corner_purelyExceptional` for normal homs: if every *normal* Jordan hom of
`V_A` into a von Neumann algebra vanishes on `{x ; c x = x}`, then `V_{A_c}` is normally
purely exceptional (the corner map `J = Pred(π_c)` is normal, `stateLin_normal`). -/
theorem corner_purelyExceptional_normal {A : C} {c : Pred A} (hcs : IsSharp c)
    {c₀ : CPt σs A} (hc₀ : c₀.1 = c) (hc : Papers.SEA.IsIdempotent c₀)
    (hcomm : ∀ w : Pred A, SEA.seq w c = SEA.seq c w)
    (hvan : ∀ (𝔅 : Type v) [CStarAlgebra 𝔅] [PartialOrder 𝔅] [StarOrderedRing 𝔅]
      [Theses.VonNeumannAlgebra 𝔅] (ψ : VA σs A →ₗ[ℝ] 𝔅),
      (letI := jbMul σs hRC h119 A; IsJordanHomInto (VA σs A) 𝔅 ψ) → IsNormalMap ψ →
        ∀ x, jm σs hRC h119 A (GP.gmap c₀) x = x → ψ x = 0) :
    letI := jbMul σs hRC h119 (comprObj c)
    IsNormallyPurelyExceptional.{v, v} (VA σs (comprObj c)) := by
  intro 𝔅 _ _ _ _ φ hφ hφN
  set J := stateLin σs (comprMap c)
  have hψ : (letI := jbMul σs hRC h119 A; IsJordanHomInto (VA σs A) 𝔅 (φ ∘ₗ J)) := by
    refine ⟨fun a => hφ.1 (J a), fun a b => ?_⟩
    show φ (J (jm σs hRC h119 A a b)) = _
    rw [corner_jordan hcs σs hRC h119 h0 hcomm]
    exact hφ.2 (J a) (J b)
  ext y
  rw [LinearMap.zero_apply]
  set z := stateLin σs (dag (comprMap c)) y
  have hy : y = J (Uop σs c₀ z) := by
    rw [Uop_eq_stateLin, hc₀, corner_asrt σs h0 hcs, corner_section σs h0 hcs]
  rw [hy]
  have hN : IsNormalMap (⇑φ ∘ ⇑J) := isNormal_comp hφN (stateLin_normal σs _)
  exact hvan 𝔅 (φ ∘ₗ J) hψ hN _ (jm_idem_Uop σs hRC h119 hc z)

include h0 in
/-- `Rec136Hyps.corner_of_summand` for normal homs: a non-zero central idempotent of `V_X`
whose summand is killed by every normal Jordan hom into a von Neumann algebra gives an
object `W` with a state and `V_W` normally purely exceptional. -/
theorem corner_of_summand_normal (X : C) {c : VA σs X} (hc0 : c ≠ 0)
    (hcc : jm σs hRC h119 X c c = c)
    (hcen : ∀ x y : VA σs X, jm σs hRC h119 X c (jm σs hRC h119 X x y) =
      jm σs hRC h119 X x (jm σs hRC h119 X c y))
    (hvan : ∀ (𝔅 : Type v) [CStarAlgebra 𝔅] [PartialOrder 𝔅] [StarOrderedRing 𝔅]
      [Theses.VonNeumannAlgebra 𝔅] (ψ : VA σs X →ₗ[ℝ] 𝔅),
      (letI := jbMul σs hRC h119 X; IsJordanHomInto (VA σs X) 𝔅 ψ) → IsNormalMap ψ →
        ∀ x, jm σs hRC h119 X c x = x → ψ x = 0) :
    ∃ W : C, Nonempty (Stat W) ∧
      (letI := jbMul σs hRC h119 W; IsNormallyPurelyExceptional.{v, v} (VA σs W)) := by
  obtain ⟨c₀, hc₀, rfl⟩ := jm_idem_gmap σs hRC h119 X hcc
  have hcs : IsSharp c₀.1 := isSharp_of_isIdempotent ((cpt_idem_iff σs c₀).1 hc₀)
  have hcomm : ∀ w : Pred X, SEA.seq w c₀.1 = SEA.seq c₀.1 w := by
    intro w
    have := central_of_jordan σs hRC h119 hc₀ hcen (cptMk σs w (cpt_all σs h0 w))
    have e : SEA.seq c₀.1 w = SEA.seq w c₀.1 := congrArg Subtype.val this
    exact e.symm
  have hc0' : c₀.1 ≠ 0 := fun h => hc0 (by
    rw [show c₀ = 0 from Subtype.ext h, GP.gmap_zero])
  exact ⟨comprObj c₀.1, exists_state_compr hcs hc0',
    corner_purelyExceptional_normal σs hRC h119 h0 hcs rfl hc₀ hcomm hvan⟩

end CornerN

section Rec135N

open CategoryTheory MonoidalCategory SequentialEffectus
open scoped unitInterval

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)
  (φ₀ : EffectMonoidHom (Scal C) I) (ψ₀ : EffectMonoidHom I (Scal C))
  (h1 : ∀ k, ψ₀.toFun (φ₀.toFun k) = k) (h2 : ∀ r, φ₀.toFun (ψ₀.toFun r) = r)

include h1 h2 in
/-- `JBCoord.summand_absurd` for normal pure exceptionality: a normally purely exceptional
`V_W ≠ 0` is impossible.  `npe_exists_exch_pair`, then `corner_absurd_normal` with
`ψ = P·(· ⊗ 1) = U_P ∘ (· ⊗ 1)`, which pulls normal functionals back to normal ones
(N1 for `U_P`, REC 127 part 4 for `· ⊗ 1`). -/
theorem summand_absurd_normal [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C] {W : C} (hW : Nonempty (Stat W))
    (hpe : letI := jbMul (realSplit ψ₀) hRC h119 W;
      IsNormallyPurelyExceptional.{v, v} (VA (realSplit ψ₀) W)) : False := by
  set σs := realSplit ψ₀ with hσs
  have h0 : σs.s = 0 := rfl
  have hWne : ouUnit (VA σs W) ≠ 0 := unit_ne_zero_real φ₀ ψ₀ hW
  let iW := jbMul σs hRC h119 W
  have jW : JBWAlgebra (VA σs W) := jbw_real hRC h119 φ₀ ψ₀ h1 h2 W
  obtain ⟨p, q, hpq, -, hq0, hp, hq, s, hs, hspq⟩ := npe_exists_exch_pair hpe hWne
  let iX := jbMul σs hRC h119 (W ⊗ W)
  have jX : JBWAlgebra (VA σs (W ⊗ W)) := jbw_real hRC h119 φ₀ ψ₀ h1 h2 (W ⊗ W)
  have hκ : ∀ b b' : VA σs W, tensV σs (ouUnit (VA σs W)) b * tensV σs (ouUnit (VA σs W)) b'
      = tensV σs (ouUnit (VA σs W)) (b * b') := (rec127_right σs hRC h119 h0 W W).1
  have hι : ∀ a a' : VA σs W, tensV σs a (ouUnit (VA σs W)) * tensV σs a' (ouUnit (VA σs W))
      = tensV σs (a * a') (ouUnit (VA σs W)) := (rec127 σs hRC h119 h0 W W).1
  set P := tensV σs (ouUnit (VA σs W)) p with hPdef
  set Q := tensV σs (ouUnit (VA σs W)) q with hQdef
  set S := tensV σs (ouUnit (VA σs W)) s with hSdef
  have hP : P * P = P := by rw [hκ, hp]
  have hQ : Q * Q = Q := by rw [hκ, hq]
  have hPQ : P * Q = 0 := by rw [hκ, hpq, tensV_zero_right]
  have hS : S * S = ouUnit (VA σs (W ⊗ W)) := by
    rw [hκ]; rw [show s * s = ouUnit (VA σs W) from hs]; exact tensV_unit σs
  have hSP : jQ S P = Q := by
    rw [hQdef, hSdef, hPdef, ← hspq]
    simp only [jQ, hκ, ← tensV_smul_right, ← tensV_sub_right]
  obtain ⟨w, hwP, hwQ, hww⟩ :=
    JBPeirce.exch_connect (u' := ouUnit (VA σs (W ⊗ W))) JBAlgebra.one_mul hP hPQ hS hSP
  have hQ0 : Q ≠ 0 := tens_ne_zero φ₀ ψ₀ h1 h2 hWne hq0
  obtain ⟨y, hy, hpy⟩ := jm_idem_gmap σs hRC h119 W hp
  have h1y : Papers.SEA.IsIdempotent (1 : CPt σs W) := Papers.SEA.one_seq _
  have hPg : P = GP.gmap (cptTens σs 1 y) := by
    rw [hPdef, hpy, ← tensV_gmap]; rfl
  have hPt : ∀ a t : VA σs W, P * tensV σs a t = tensV σs a (p * t) := by
    intro a t
    have e1 : GP.gmap (cptTens σs 1 y) * tensV σs a t = _ :=
      jm_form σs hRC h119 (W ⊗ W) (cptTens σs 1 y) (cptTens_idem σs h0 h1y hy) (tensV σs a t)
    have e2 : GP.gmap y * t = _ := jm_form σs hRC h119 W y hy t
    rw [hPg, hpy, e1, e2]
    change (2⁻¹ : ℝ) • (tensV σs a t + (Uop σs (cptTens σs 1 y) (tensV σs a t) -
      Uop σs (orth (cptTens σs 1 y)) (tensV σs a t))) =
      tensV σs a ((2⁻¹ : ℝ) • (t + (Uop σs y t - Uop σs (orth y) t)))
    rw [orth_cptTens_one' σs h0, Uop_cptTens_apply σs h0, Uop_cptTens_apply σs h0, Uop_one σs h0,
      tensV_smul_right, tensV_add_right, tensV_sub_right]
  let ι : VA σs W →ₗ[ℝ] VA σs (W ⊗ W) := vtens σs (A := W) (B := W) (ouUnit (VA σs W))
  have hιa : ∀ a, ι a = tensV σs a (ouUnit (VA σs W)) := fun a => rfl
  let ψ : VA σs W →ₗ[ℝ] VA σs (W ⊗ W) := jbT P ∘ₗ ι
  have hψa : ∀ a, ψ a = P * tensV σs a (ouUnit (VA σs W)) := fun a => rfl
  have hPP : ∀ a, P * (P * tensV σs a (ouUnit (VA σs W))) = P * tensV σs a (ouUnit (VA σs W)) := by
    intro a
    rw [hPt, hPt, JBAlgebra.mul_one, hp]
  have hψ : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    rw [hψa, hψa, hψa, ← hι]
    exact compress_mul hP (hPP a) (hPP b)
  have hψ1 : ψ (ouUnit (VA σs W)) = P := by
    rw [hψa, tensV_unit σs, JBAlgebra.mul_one]
  have hψN : ∀ ω : VA σs (W ⊗ W) →ₗ[ℝ] ℝ, (∀ v, 0 ≤ v → 0 ≤ ω v) → IsNormalMap ω →
      IsNormalMap (ω ∘ₗ ψ) := by
    intro ω hω0 hωN
    have e : ⇑(ω ∘ₗ ψ) =
        ⇑(ω ∘ₗ jQL P) ∘ (fun a : VA σs W => tensV σs a (ouUnit (VA σs W))) := by
      funext a
      simp only [LinearMap.comp_apply, Function.comp_apply, jQL_apply]
      congr 1
      rw [hψa, jQ, hPP a, hP]
      module
    rw [e]
    exact isNormal_comp (isNormal_jQ hω0 hωN P) (rec127 σs hRC h119 h0 W W).2.2.2.1
  exact corner_absurd_normal hP hQ hPQ hpe JBAlgebra.one_mul ψ hψ hψ1 hψN hwP hwQ hww hQ0

include h1 h2 in
/-- **REC 135** (short.tex:2395, Proposition) with no named hypothesis on JBW-algebras:
with scalars `[0,1]`, every `V_A` is a JW-algebra.  `J_n = cV` (`normalKernel_eq_corner`);
`c = 0`: the product of all normal Jordan homs into von Neumann algebras is injective;
`c ≠ 0`: `V_{A_c}` is normally purely exceptional, refuted by `summand_absurd_normal`. -/
theorem rec135_nohyp [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C] (A : C) :
    letI := jbMul (realSplit ψ₀) hRC h119 A; IsJWAlgebra (VA (realSplit ψ₀) A) := by
  set σs := realSplit ψ₀ with hσs
  have h0 : σs.s = 0 := rfl
  let iA := jbMul σs hRC h119 A
  have jA : JBWAlgebra (VA σs A) := jbw_real hRC h119 φ₀ ψ₀ h1 h2 A
  obtain ⟨c, hcc, hcen, -, hker⟩ := JBWSummandA.normalKernel_eq_corner (V := VA σs A)
  by_cases hc0 : c = 0
  · obtain ⟨𝔅, i1, i2, i3, i4, Φ, hΦJ, hΦN, hΦker⟩ :=
      JBWSummandA.exists_normal_hom_ker (V := VA σs A)
    refine ⟨𝔅, i1, i2, i3, i4, Φ, hΦJ, fun x y hxy => ?_, hΦN⟩
    have h1' : x - y ∈ JBWSummandA.normalKernel (VA σs A) :=
      (hΦker _).1 (by rw [map_sub, hxy, sub_self])
    rw [hker, hc0, jb_zero_mul] at h1'
    exact sub_eq_zero.1 h1'.symm
  · exfalso
    obtain ⟨W, hW, hpe⟩ := corner_of_summand_normal σs hRC h119 h0 A hc0 hcc hcen
      (fun 𝔅 _ _ _ _ ψ hψ hψN x hx => (hker x).2 hx 𝔅 ψ hψ hψN)
    exact summand_absurd_normal hRC h119 φ₀ ψ₀ h1 h2 hW hpe

end Rec135N

section Rec136N

open CategoryTheory MonoidalCategory SequentialEffectus
open scoped unitInterval

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

/-- REC 136 from REC 135 (`rec135_nohyp`), with the criteria `hRC`, `h119` as parameters;
proof as `JBCoord.rec136_summand`. -/
theorem rec136_nohyp_of [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C]
    (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)
    (hirr : IsIrreducible (Scal C)) (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) := by
  rcases seq_scal_cases hirr with h | h | ⟨φ₀, ψ₀, h1, h2⟩
  · set σs := trivSplit h
    have hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) := fun A =>
      haveI := va_subsingleton h A
      @JBWAlgebra.mk (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) (jbMul_spec σs hRC h119 A)
        (VA_dc σs A) (fun a b hab => (hab (Subsingleton.elim a b)).elim)
    have hJW : ∀ A : C, letI := jbMul σs hRC h119 A; IsJWAlgebra (VA σs A) := fun A =>
      haveI := va_subsingleton h A
      @isJW_of_subsingleton (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) _
    exact jwFunctor_spec hRC h119 σs rfl hJBW hJW
  · exact (h01 h).elim
  · exact jwFunctor_spec hRC h119 (realSplit ψ₀) rfl
      (jbw_real hRC h119 φ₀ ψ₀ h1 h2) (rec135_nohyp hRC h119 φ₀ ψ₀ h1 h2)

/-- **REC 136** (`thm:JW-algebra`, short.tex:2409, Theorem), statement exactly as
`rec136_hypfree`, with **no named hypotheses**: REC 52 (H-O–S), REC 55 (Shultz) and
REC 132 (Alfsen–Shultz four exchangeable) are not needed — normal pure exceptionality of
the normal kernel's summand (`JBWSummandA`, proved) suffices for the Peirce-specialisation
refutation (`corner_absurd_normal`, `assoc_absurd_normal`). -/
theorem rec136_nohyp [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C] (hirr : IsIrreducible (Scal C)) (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136_nohyp_of alfsenShultzResolventCriterion_holds weteringStateOrderLemma_holds hirr h01

end Rec136N

end

end Papers.REC.Rec136U

#print axioms Papers.REC.Rec136U.corner_absurd_normal
#print axioms Papers.REC.Rec136U.assoc_absurd_normal
#print axioms Papers.REC.Rec136U.rec135_nohyp
#print axioms Papers.REC.Rec136U.rec136_nohyp
