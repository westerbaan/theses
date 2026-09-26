/-
Papers/SEA/JBCommJB.lean

**SEA 16, JB half** (`ex:canonical-sea`, second.tex:475; van de Wetering, arXiv 2004.12749):
"any JB-algebra is a convex SEA", i.e. `JBCommutation A` for every JB-algebra `A`, by redoing
`JBWCommFull` with continuous functions only.

Plan (2026-09-26).  Notation of `JBWCommFull`: `flowJ x h τ = U_{e^{τh}} U_x e^{−2τh}`.
1. **Gap lemma on JB, both directions** (`gap_zero_s`, one proof for every sign `s`): if
   `‖flowJ x h (sτ)‖ ≤ C` for `τ > 0`, then `U_{k(h)} U_x f(h) = 0` for continuous `k`, `f ≥ 0`
   with `k` vanishing on `{st < β}`, `f` on `{st > α}`, `α < β`.  No spectral projections.
2. **The one analytic input, isolated** (`ContPeirce A`): if `U_{k(h)} U_x f(h) = 0` for every
   pair of continuous `k`, `f ≥ 0` on `sp h` with separated supports (either order), then `x`
   operator-commutes with `h`.  This is the continuous-function form of "`P½(χ_{>s}(h)) x = 0`
   for every spectral projection ⇒ `x | h`".  It holds in every JBW-algebra
   (`contPeirce_of_jbw`, the committed Step B + `opComm_of_sprojs`).
3. By 1+2, a bounded two-sided flow gives `x | h` (`opComm_of_flow_bdd`).
4. **(SQ)** `u | v ⇒ v | u²`: `[L_u,L_v] = 0` makes the flow of `(u, u∘v)` constant (`flow`),
   so `u | u∘v` (3.), so `v | u²` (Step C, `opComm_sq_of_opComm_mul`).  This is van de
   Wetering's Remark 2.15 ("`a | b ⇒ a | b²`"), here from 2.
5. **Powers without spectral projections** (`opComm_pow`): `y | a ⇒ y | aⁿ` by strong
   induction, `a^{2k} = (a^k)²` and `2a^{2k+1} = (a^k + a^{k+1})² − a^{2k} − a^{2k+2}` (SQ).
6. `mem_comm`: hypothesis ⇒ `D(A) = 0` ⇒ bounded flow ⇒ `x | A` ⇒ `y | a` ⇒ (5) `y ∈ comm a`
   ⇒ (SQ with each `w ∈ C(a)`) `b = y² ∈ comm a`.
   `mul_mem`: `w | y, w | z ⇒ w | (y+z)², y², z²` (SQ) ⇒ `w | yz`.  (Neither needs `c ≥ 0`.)
7. `jbCommutation_of_contPeirce`, `sea16_jb_of_contPeirce`.
Status: 1–7 done, no sorry.  NOT done: `ContPeirce A` for a general JB-algebra.  Why route 1
stops there: every conclusion of 3–6 is a *global* statement (`L_x L_h = L_h L_x` on all of
`A`), while the gap only constrains `x`.  In a JBW-algebra the bridge is Peirce theory for
the idempotents `χ_{>s}(h)`; `C(h)` has no idempotents when `sp h` is connected.  The
continuous substitutes tried (partition-of-unity sums of localised commutators; operator
level `[L_h, U_x] = 0`, which the SQ case already gives, does not by itself yield
`[L_h, L_x] = 0`; Kleinecke–Shirokov in `B(A)`) all need either an orthogonal-sum estimate
for `L`-commutators (only `U`-sums have one, by positivity) or a Phragmén–Lindelöf / Gelfand–
Hille step for a complexified `A`.  So the exact missing lemma is `ContPeirce A`
(equivalently: a faithful unital Jordan embedding of `A` into a JBW-algebra, e.g. `A**`).
-/
import Papers.SEA.JBWCommFull

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.SEA.JBCommJB

open Theses.B.Eff Papers.REC Papers.REC.JBCalc Papers.REC.JBMac Papers.SEA.JBAll
  Papers.SEA.JBComm Papers.SEA.JBWFull Papers.REC.JBWProj NormedSpace Filter Topology

universe u

noncomputable section

section JB

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hJ : JBAlgebra A]

include hJ

attribute [local instance] ousNormedAddCommGroup ousNormedSpace jbComplete opRat

/-! ## 1. The gap lemma on a JB-algebra, for either sign -/

/-- The flow `τ ↦ U_{e^{τh}} U_x e^{−2τh}` (JB version of `JBWFull.flowW`). -/
def flowJ (x h : A) (τ : ℝ) : A := Uo (eE (τ • h)) (Uo x (eE ((-2 * τ) • h)))

/-- **Gap lemma** (continuous cut-offs, any JB-algebra, sign `s`). -/
theorem gap_zero_s {x h : A} {C s : ℝ}
    (hWb : ∀ τ : ℝ, 0 < τ → ousNorm A (flowJ x h (s * τ)) ≤ C)
    {α β : ℝ} (hαβ : α < β) {k f : C(jbSpec h, ℝ)} (hf0 : ∀ t, 0 ≤ f t)
    (hk : ∀ t : jbSpec h, s * t.1 < β → k t = 0) (hf : ∀ t : jbSpec h, α < s * t.1 → f t = 0) :
    jQ (jbCfc h k) (jQ x (jbCfc h f)) = 0 := by
  set Z := jQ (jbCfc h k) (jQ x (jbCfc h f)) with hZ
  have hZ0 : 0 ≤ Z := jQ_nonneg _ (jQ_nonneg _ ((jbCfc_nonneg_iff h f).2 hf0))
  set K := ‖k‖
  set Fn := ‖f‖
  have hK := norm_nonneg k
  have hFn := norm_nonneg f
  have bound : ∀ τ : ℝ, 0 < τ → ousNorm A Z ≤
      (Fn * 3 * K ^ 2 * C) * Real.exp (-(2 * (β - α)) * τ) := by
    intro τ hτ
    have e1 : jbCfc h f ≤ (Fn * Real.exp (2 * τ * α)) • eE ((-2 * (s * τ)) • h) := by
      rw [eE_smul_eq, ← jbCfc_smul, jbCfc_le_iff]
      intro t
      simp only [ContinuousMap.smul_apply, expF_apply, smul_eq_mul]
      by_cases ht : α < s * t.1
      · rw [hf t ht]; positivity
      · replace ht := not_lt.1 ht
        have h1 : f t ≤ Fn := ContinuousMap.apply_le_norm f t
        have hp := mul_le_mul_of_nonneg_left ht hτ.le
        have h2 : 1 ≤ Real.exp (2 * τ * α) * Real.exp (-2 * (s * τ) * t.1) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        calc f t ≤ Fn := h1
          _ ≤ Fn * (Real.exp (2 * τ * α) * Real.exp (-2 * (s * τ) * t.1)) :=
            le_mul_of_one_le_right hFn h2
          _ = _ := by ring
    set g : C(jbSpec h, ℝ) := expF h (s * τ / 2) with hg
    set m : C(jbSpec h, ℝ) := k * expF h (-(s * τ)) with hm
    have hk_eq : k = g * g * m := by
      ext t
      simp only [hg, hm, ContinuousMap.mul_apply, expF_apply]
      have : Real.exp (s * τ / 2 * t.1) * Real.exp (s * τ / 2 * t.1) *
          Real.exp (-(s * τ) * t.1) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]; congr 1; ring
      linear_combination (-(k t)) * this
    have hgg : jbCfc h (g * g) = eE ((s * τ) • h) := by
      rw [eE_smul_eq]; congr 1; ext t
      simp only [hg, ContinuousMap.mul_apply, expF_apply, ← Real.exp_add]; congr 1; ring
    have hUk : Uo (jbCfc h k) = Uo (jbCfc h m) * Uo (eE ((s * τ) • h)) := by
      conv_lhs => rw [hk_eq]
      rw [Uo_cfc_mul, hgg]
    have e2 : Z ≤ (Fn * Real.exp (2 * τ * α)) •
        jQ (jbCfc h k) (jQ x (eE ((-2 * (s * τ)) • h))) := by
      rw [← jQ_smul, ← jQ_smul]; exact jQ_mono _ (jQ_mono _ e1)
    have e3 : jQ (jbCfc h k) (jQ x (eE ((-2 * (s * τ)) • h))) =
        jQ (jbCfc h m) (flowJ x h (s * τ)) := by
      rw [← Uo_apply, ← Uo_apply, hUk, mul_apply_eq_comp, Uo_apply, flowJ]
    have hmn : ousNorm A (jbCfc h m) ≤ K * Real.exp (-τ * β) := by
      rw [ousNorm_jbCfc]
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
      simp only [hm, ContinuousMap.mul_apply, expF_apply, norm_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      by_cases ht : s * t.1 < β
      · rw [hk t ht, abs_zero, zero_mul]; positivity
      · replace ht := not_lt.1 ht
        have hp := mul_le_mul_of_nonneg_left ht hτ.le
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm k t)
          (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le hK
    have hWt := hWb τ hτ
    have hC : 0 ≤ C := (ousNorm_nonneg_rc _).trans hWt
    have hm0 := ousNorm_nonneg_rc (jbCfc h m)
    have hexp : Real.exp (2 * τ * α) * (Real.exp (-τ * β)) ^ 2 =
        Real.exp (-(2 * (β - α)) * τ) := by
      rw [_root_.sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc ousNorm A Z ≤ ousNorm A ((Fn * Real.exp (2 * τ * α)) •
          jQ (jbCfc h k) (jQ x (eE ((-2 * (s * τ)) • h)))) := ousNorm_mono hZ0 e2
      _ = Fn * Real.exp (2 * τ * α) * ousNorm A (jQ (jbCfc h m) (flowJ x h (s * τ))) := by
          rw [e3, ousNorm_smul_eq, abs_of_nonneg (by positivity)]
      _ ≤ Fn * Real.exp (2 * τ * α) * (3 * ousNorm A (jbCfc h m) ^ 2 * C) := by
          refine mul_le_mul_of_nonneg_left ((ousNorm_jQ_le _ _).trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left hWt (by positivity)
      _ ≤ Fn * Real.exp (2 * τ * α) * (3 * (K * Real.exp (-τ * β)) ^ 2 * C) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hC
          exact pow_le_pow_left₀ hm0 hmn 2
      _ = (Fn * 3 * K ^ 2 * C) * (Real.exp (2 * τ * α) * (Real.exp (-τ * β)) ^ 2) := by ring
      _ = _ := by rw [hexp]
  have hlim : Tendsto (fun τ : ℝ => (Fn * 3 * K ^ 2 * C) * Real.exp (-(2 * (β - α)) * τ))
      atTop (𝓝 0) := by
    have := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show -(2 * (β - α)) < 0 by linarith))
    simpa using this.const_mul (Fn * 3 * K ^ 2 * C)
  have hle : ousNorm A Z ≤ 0 :=
    ge_of_tendsto hlim ((eventually_gt_atTop 0).mono bound)
  exact IsOUS.norm_eq_zero _ (le_antisymm hle (ousNorm_nonneg_rc _))

/-! ## 2. The isolated input: a continuous Peirce criterion -/

/-- `k` and `f` (functions on `sp h`) have separated supports, in either order. -/
def SepSupp {h : A} (k f : C(jbSpec h, ℝ)) : Prop :=
  ∃ α β : ℝ, α < β ∧
    (((∀ t : jbSpec h, t.1 < β → k t = 0) ∧ (∀ t : jbSpec h, α < t.1 → f t = 0)) ∨
     ((∀ t : jbSpec h, α < t.1 → k t = 0) ∧ (∀ t : jbSpec h, t.1 < β → f t = 0)))

variable (A) in
/-- **The continuous Peirce criterion** (the one input not proved for JB-algebras): if
`U_{k(h)} U_x f(h) = 0` for all continuous `k`, `f ≥ 0` on `sp h` with separated supports,
then `x` operator-commutes with `h`.  (In a JBW-algebra: `contPeirce_of_jbw`.) -/
def ContPeirce : Prop :=
  ∀ x h : A, (∀ k f : C(jbSpec h, ℝ), (∀ t, 0 ≤ f t) → SepSupp k f →
    jQ (jbCfc h k) (jQ x (jbCfc h f)) = 0) → OpComm x h

/-- A bounded two-sided flow gives the gap hypotheses of `ContPeirce`. -/
theorem gaps_of_flow_bdd {x h : A} {C : ℝ} (hb : ∀ τ : ℝ, ousNorm A (flowJ x h τ) ≤ C)
    (k f : C(jbSpec h, ℝ)) (hf0 : ∀ t, 0 ≤ f t) (hs : SepSupp k f) :
    jQ (jbCfc h k) (jQ x (jbCfc h f)) = 0 := by
  obtain ⟨α, β, hαβ, ⟨hk, hf⟩ | ⟨hk, hf⟩⟩ := hs
  · exact gap_zero_s (s := 1) (fun τ _ => hb _) hαβ hf0 (fun t ht => hk t (by simpa using ht))
      (fun t ht => hf t (by simpa using ht))
  · refine gap_zero_s (s := -1) (fun τ _ => hb _) (α := -β) (β := -α) (by linarith) hf0
      (fun t ht => hk t (by linarith)) (fun t ht => hf t (by linarith))

/-- **Bounded two-sided flow ⇒ operator commutation**, given `ContPeirce`. -/
theorem opComm_of_flow_bdd (H : ContPeirce A) {x h : A} {C : ℝ}
    (hb : ∀ τ : ℝ, ousNorm A (flowJ x h τ) ≤ C) : OpComm x h :=
  H x h (gaps_of_flow_bdd hb)

/-! ## 3. (SQ): `u | v ⇒ v | u²` -/

theorem opComm_mul_of_opComm (H : ContPeirce A) {u v : A} (huv : OpComm u v) :
    OpComm u (u * v) := by
  have hDA : u * (v * (u * v)) - v * (u * (u * v)) = 0 := by rw [huv (u * v), sub_self]
  exact opComm_of_flow_bdd H (C := ousNorm A (u * u)) fun τ => flow_bound u v hDA τ

/-- **(SQ)** van de Wetering's Remark 2.15: `u | v ⇒ v | u²`. -/
theorem opComm_sq (H : ContPeirce A) {u v : A} (huv : OpComm u v) : OpComm v (u * u) :=
  opComm_sq_of_opComm_mul (opComm_mul_of_opComm H huv)

theorem opComm_sub_right {x y y' : A} (h : OpComm x y) (h' : OpComm x y') :
    OpComm x (y - y') := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ y']
  exact opComm_add_right h (opComm_smul_right _ h')

/-- `y | a ⇒ y | aⁿ`, by strong induction from (SQ). -/
theorem opComm_pow (H : ContPeirce A) {a y : A} (h : OpComm a y) (n : ℕ) :
    OpComm (jbPow a n) y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have sqk : ∀ k, k < n → OpComm (jbPow a (k + k)) y := fun k hk => by
      rw [← jbPow_mul_jbPow]; exact (opComm_sq H (ih k hk)).symm
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact opComm_one_left y
      · rw [two_mul]; exact sqk k (by omega)
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa using h
      · have h1 := ih k (by omega)
        have h2 := ih (k + 1) (by omega)
        have hsq := (opComm_sq H (opComm_add_left h1 h2)).symm
        have e : (jbPow a k + jbPow a (k + 1)) * (jbPow a k + jbPow a (k + 1)) =
            jbPow a (k + k) + (2 : ℝ) • jbPow a (2 * k + 1) + jbPow a (k + 1 + (k + 1)) := by
          rw [JBAlgebra.add_mul, jb_mul_add, jb_mul_add, jbPow_mul_jbPow, jbPow_mul_jbPow,
            jbPow_mul_jbPow, jbPow_mul_jbPow, two_smul,
            show k + (k + 1) = 2 * k + 1 by omega, show k + 1 + k = 2 * k + 1 by omega]
          abel
        rw [e] at hsq
        have h3 : OpComm y ((2 : ℝ) • jbPow a (2 * k + 1)) := by
          have := opComm_sub_right (opComm_sub_right hsq.symm (sqk k (by omega)).symm)
            (sqk (k + 1) (by omega)).symm
          have e2 : jbPow a (k + k) + (2 : ℝ) • jbPow a (2 * k + 1) + jbPow a (k + 1 + (k + 1)) -
              jbPow a (k + k) - jbPow a (k + 1 + (k + 1)) = (2 : ℝ) • jbPow a (2 * k + 1) := by
            abel
          rwa [e2] at this
        have := opComm_smul_right (2⁻¹ : ℝ) h3
        rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul] at this
        exact this.symm

theorem continuous_jbPow' (n : ℕ) : Continuous fun w : A => jbPow w n := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    show Continuous fun w : A => w * jbPow w n
    exact jb_continuous_mul.comp (continuous_id.prodMk ih)

theorem mem_comm_of_pows' {h z : A} (hz : ∀ n : ℕ, OpComm (jbPow h n) z) : z ∈ comm h := by
  intro w hw
  have hsub : Set.range (jbEv h) ⊆ {x | OpComm x z} := by
    rintro _ ⟨q, rfl⟩
    induction q using Polynomial.induction_on' with
    | add q q' hq hq' => rw [map_add]; exact opComm_add_left hq hq'
    | monomial n r => rw [jbEv_monomial]; exact opComm_smul_left r (hz n)
  exact (isClosed_opComm_left z).closure_subset_iff.2 hsub (mem_Ca.1 hw)

/-! ## 4. `JBCommutation` from `ContPeirce` -/

/-- `JBCommutation.mem_comm` for every JB-algebra satisfying `ContPeirce`. -/
theorem jb_mem_comm (H : ContPeirce A) {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : JBAll.sq a b = JBAll.sq b a) : b ∈ comm a := by
  set x := jbSqrt a
  set y := jbSqrt b
  have hxx : x * x = a := jbSqrt_mul_self ha
  have hyy : y * y = b := jbSqrt_mul_self hb
  have hDA : x * (y * (x * y)) - y * (x * (x * y)) = 0 := by
    rw [der_xy, hxx, hyy]
    rw [JBAll.sq, JBAll.sq] at h
    rw [h, sub_self, smul_zero]
  have hxA : OpComm x (x * y) :=
    opComm_of_flow_bdd H (C := ousNorm A (x * x)) fun τ => flow_bound x y hDA τ
  have hya : OpComm y a := by have := opComm_sq_of_opComm_mul hxA; rwa [hxx] at this
  have hy : y ∈ comm a := mem_comm_of_pows' (opComm_pow H hya.symm)
  intro w hw
  have := opComm_sq H (hy w hw).symm
  rwa [hyy] at this

/-- `JBCommutation.mul_mem` for every JB-algebra satisfying `ContPeirce` (via (SQ)). -/
theorem jb_mul_mem (H : ContPeirce A) {c y z : A} (hy : y ∈ comm c) (hz : z ∈ comm c) :
    y * z ∈ comm c := by
  intro w hw
  have h1 := opComm_sq H (hy w hw).symm
  have h2 := opComm_sq H (hz w hw).symm
  have h3 := opComm_sq H (opComm_add_right (hy w hw) (hz w hw)).symm
  have e : (y + z) * (y + z) - y * y - z * z = (2 : ℝ) • (y * z) := by
    rw [JBAlgebra.add_mul, jb_mul_add, jb_mul_add, JBAlgebra.mul_comm z y, two_smul]; abel
  have h4 := opComm_sub_right (opComm_sub_right h3 h1) h2
  rw [e] at h4
  have := opComm_smul_right (2⁻¹ : ℝ) h4
  rwa [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul] at this

/-- **`JBCommutation` for every JB-algebra satisfying the continuous Peirce criterion.** -/
theorem jbCommutation_of_contPeirce (H : ContPeirce A) : JBCommutation A :=
  ⟨fun _ _ ha hb h => jb_mem_comm H ha hb h, fun _ _ _ _ hy hz => jb_mul_mem H hy hz⟩

/-- **SEA 16, JB half, from `ContPeirce`**: `[0,1]_A` is a convex SEA with
`a ∘ b = U_{√a} b`. -/
theorem sea16_jb_of_contPeirce (H : ContPeirce A) :
    @IsConvex _ (jbEA A) ∧
    ∀ a b : Set.Icc (0 : A) (ouUnit A),
      ∃! r : A, 0 ≤ r ∧ r * r = a.1 ∧
        (@SequentialEffectAlgebra.seq _ (jbEA A)
          (jbSEA (jbCommutation_of_contPeirce H)).toSequentialEffectAlgebra a b).1 =
          (2 : ℝ) • (r * (r * b.1)) - (r * r) * b.1 :=
  sea16_jb (jbCommutation_of_contPeirce H)

end JB

/-! ## 5. Sanity: `ContPeirce` holds in every JBW-algebra -/

section JBW

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hW : JBWAlgebra A]

include hW

attribute [local instance] ousNormedAddCommGroup ousNormedSpace jbComplete opRat

/-- Step B of `JBWCommFull` from the gap hypotheses alone. -/
theorem ph_sproj_of_gaps {x h : A}
    (hgap : ∀ k f : C(jbSpec h, ℝ), (∀ t, 0 ≤ f t) → SepSupp k f →
      jQ (jbCfc h k) (jQ x (jbCfc h f)) = 0) (δ : ℝ) (j : ℕ) :
    JBPeirce.Ph (sproj (rampF h δ j)) x = 0 := by
  set ρ := rampF h δ j with hρdef
  have hρ0 : ∀ t, 0 ≤ ρ t := rampF_nonneg h j
  set p := sproj ρ with hpdef
  have hp : p * p = p := sproj_idem hρ0
  set s : ℝ := (j : ℝ) * δ - ousNorm A h with hs
  have hρ : ∀ t : jbSpec h, ρ t = max (t.1 - s) 0 := fun t => by
    simp only [hρdef, rampF, ContinuousMap.coe_mk, hs]; congr 1; ring
  refine JBSeq.ph_of_jQ_one_sub hp ?_
  set u := jQ x (ouUnit A - p) with hu
  have hu0 : 0 ≤ u := jQ_nonneg _ (sub_nonneg.2 (sproj_le_one hρ0))
  set r := jbSqrt u with hr
  have c1 : ∀ m : ℕ, jQ r (jbCfc h (cutF ρ (2 / ((m : ℝ) + 1)))) = 0 := by
    intro m
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    set k := cutF ρ (2 / ((m : ℝ) + 1)) with hk
    have hk0 : ∀ t, 0 ≤ k t := fun t => le_max_right _ _
    set sk : C(jbSpec h, ℝ) := ⟨fun t => Real.sqrt (k t), Real.continuous_sqrt.comp k.continuous⟩
      with hsk
    have hk0' : 0 ≤ jbCfc h k := (jbCfc_nonneg_iff h k).2 hk0
    have hskq : jbSqrt (jbCfc h k) = jbCfc h sk := by
      refine (jbSqrt_unique hk0' ((jbCfc_nonneg_iff h sk).2 fun t => Real.sqrt_nonneg _) ?_).symm
      rw [← jbCfc_mul]; congr 1; ext t
      simp only [hsk, ContinuousMap.mul_apply, ContinuousMap.coe_mk]
      exact Real.mul_self_sqrt (hk0 t)
    set fF : C(jbSpec h, ℝ) := 1 - sfun ρ m with hfF
    have hle : ouUnit A - p ≤ jbCfc h fF := by
      rw [hfF, jbCfc_sub, jbCfc_one]
      exact sub_le_sub_left ((sproj_isLUB hρ0).1 ⟨m, rfl⟩) _
    have hz : jQ (jbCfc h sk) (jQ x (jbCfc h fF)) = 0 := by
      refine hgap sk fF ?_ ⟨s + 1 / ((m : ℝ) + 1), s + 2 / ((m : ℝ) + 1), ?_, Or.inl ⟨?_, ?_⟩⟩
      · intro t
        simp only [hfF, ContinuousMap.sub_apply, ContinuousMap.one_apply, sfun_apply]
        linarith [min_le_right (((m : ℝ) + 1) * ρ t) 1]
      · have : 1 / ((m : ℝ) + 1) < 2 / ((m : ℝ) + 1) := div_lt_div_of_pos_right (by norm_num) hm1
        linarith
      · intro t ht
        simp only [hsk, ContinuousMap.coe_mk, hk, cutF_apply]
        rw [hρ t]
        have h2 : 0 < 2 / ((m : ℝ) + 1) := div_pos two_pos hm1
        have : max (t.1 - s) 0 - 2 / ((m : ℝ) + 1) ≤ 0 := by
          rcases le_total (t.1 - s) 0 with h1 | h1
          · rw [max_eq_right h1]; linarith
          · rw [max_eq_left h1]; linarith
        rw [max_eq_right this, Real.sqrt_zero]
      · intro t ht
        simp only [hfF, ContinuousMap.sub_apply, ContinuousMap.one_apply, sfun_apply]
        have h1 : 1 / ((m : ℝ) + 1) < t.1 - s := by linarith
        have h0 : 0 < 1 / ((m : ℝ) + 1) := div_pos one_pos hm1
        rw [hρ t, max_eq_left (by linarith : 0 ≤ t.1 - s)]
        have : 1 ≤ ((m : ℝ) + 1) * (t.1 - s) := by
          rw [div_lt_iff₀ hm1] at h1; linarith
        rw [min_eq_right this, sub_self]
    have h1 : JBAll.sq (jbCfc h k) u = 0 := by
      rw [JBAll.sq, hskq]
      refine le_antisymm ?_ (jQ_nonneg _ hu0)
      calc jQ (jbCfc h sk) u ≤ jQ (jbCfc h sk) (jQ x (jbCfc h fF)) := jQ_mono _ (jQ_mono _ hle)
        _ = 0 := hz
    exact sq_eq_zero_comm hk0' hu0 h1
  have hconv : Tendsto (fun m : ℕ => cutF ρ (2 / ((m : ℝ) + 1))) atTop (𝓝 ρ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h2 : Tendsto (fun m : ℕ => 2 * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) h2
    have hc : 0 ≤ 2 / ((m : ℝ) + 1) := by positivity
    rw [show 2 * (1 / ((m : ℝ) + 1)) = 2 / ((m : ℝ) + 1) by ring]
    refine (ContinuousMap.norm_le _ hc).2 fun t => ?_
    simp only [ContinuousMap.sub_apply, cutF_apply, Real.norm_eq_abs]
    have := hρ0 t
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith [le_max_left (ρ t - 2 / ((m : ℝ) + 1)) 0]
    · have : max (ρ t - 2 / ((m : ℝ) + 1)) 0 ≤ ρ t := max_le (by linarith) this
      linarith
  have c2 : jQ r (jbCfc h ρ) = 0 := by
    have hT : Tendsto (fun m : ℕ => Uo r (jbCfcL h (cutF ρ (2 / ((m : ℝ) + 1))))) atTop
        (𝓝 (Uo r (jbCfcL h ρ))) :=
      (((Uo r).continuous.comp (jbCfcL h).continuous).tendsto ρ).comp hconv
    have h0 : (fun m : ℕ => Uo r (jbCfcL h (cutF ρ (2 / ((m : ℝ) + 1))))) = fun _ => 0 := by
      funext m; rw [jbCfcL_apply, Uo_apply]; exact c1 m
    rw [h0] at hT
    rw [← Uo_apply, ← jbCfcL_apply]
    exact tendsto_nhds_unique hT tendsto_const_nhds
  have c3 : ∀ n, Uo r (sseq ρ n) = 0 := by
    intro n
    have hle : sseq ρ n ≤ ((n : ℝ) + 1) • jbCfc h ρ := by
      rw [sseq, ← jbCfc_smul, jbCfc_le_iff]; intro t
      simp only [sfun_apply, ContinuousMap.smul_apply, smul_eq_mul]; exact min_le_left _ _
    rw [Uo_apply]
    refine le_antisymm ?_ (jQ_nonneg _ (sseq_nonneg hρ0 n))
    calc jQ r (sseq ρ n) ≤ jQ r (((n : ℝ) + 1) • jbCfc h ρ) := jQ_mono _ hle
      _ = 0 := by rw [jQ_smul, c2, smul_zero]
  have c4 : jQ r p = 0 := by
    have hD : Set.range (sseq ρ) ⊆ Set.Icc 0 ((1 : ℝ) • ouUnit A) := by
      rintro _ ⟨n, rfl⟩; rw [one_smul]; exact ⟨sseq_nonneg hρ0 n, sseq_le_one n⟩
    have hg := (good_Uo (jbSqrt_nonneg u)).2 _ 1 hD ⟨_, ⟨0, rfl⟩⟩
      (directedOn_range.2 (sseq_mono hρ0).directed_le) p (sproj_isLUB hρ0)
    rw [← Uo_apply]
    refine le_antisymm (hg.2 ?_) (hg.1 ⟨sseq ρ 0, ⟨0, rfl⟩, c3 0⟩)
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact (c3 n).le
  have hsp : jbSqrt p = p := (jbSqrt_unique (sproj_nonneg hρ0) (sproj_nonneg hρ0) hp).symm
  have h5 := sq_eq_zero_comm hu0 (sproj_nonneg hρ0) c4
  rw [JBAll.sq, hsp] at h5
  exact h5

/-- **`ContPeirce` holds in every JBW-algebra** (so the isolated input is true there, and
`jbCommutation_of_contPeirce` recovers the JBW theorem). -/
theorem contPeirce_of_jbw : ContPeirce A := fun _ h hgap =>
  (opComm_of_sprojs fun δ _ j =>
    opComm_of_ph (sproj_idem (rampF_nonneg h j)) (ph_sproj_of_gaps hgap δ j)).symm

end JBW

end

end Papers.SEA.JBCommJB
