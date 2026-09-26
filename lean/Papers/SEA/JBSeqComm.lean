/-
Papers/SEA/JBSeqComm.lean

**SEA 16** (`ex:canonical-sea`, second.tex:475): the hard half of van de Wetering's
commutation theorem (`JBSeqComm.mem_comm` of `Papers.SEA.JBComm`) beyond two levels.

Plan (2026-09-26).
1. Finite spectrum, every JB-algebra, no trace.  `a = Σ λ_i p_i`, `(p_i)` orthogonal
   idempotents with `Σ p_i = 1`, `λ_i ≥ 0` distinct; `b ≥ 0`, `y = √b`, `r = Σ √λ_i p_i = √a`.
   Put `T_ik = U_{p_i} U_y p_k ≥ 0`.  `U_{p_i}` commutes with `U_r` and `U_r = λ_i` on
   `V₁(p_i)`, so `U_{p_i} U_r b = λ_i U_{p_i} b = λ_i Σ_k T_ik` (`U_y 1 = b`), while
   `U_{p_i} U_y a = Σ_k λ_k T_ik`.  Hence **`Σ_k (λ_i − λ_k) T_ik = 0`** for every `i`.
2. Top-down induction on `#{j ; λ_j > λ_i}`: if `P½(p_j) y = 0` for all `λ_j > λ_i`, then
   `T_ij = 0` for those `j` (`U_y p_j ∈ V₁(p_j)`, killed by `U_{p_i}`, `p_i ⊥ p_j`); the
   remaining terms of 1 are `≥ 0` with positive coefficients, so all `T_ik = 0` (`k ≠ i`);
   `U_{p_i} U_y (1 − p_i) = P₁(p_i)(y½²) = 0` gives `y½ = 0` (`half_eq_zero`), i.e.
   `P½(p_i) y = 0` for every `i`.
3. `P½(p_i) b = 0` (`Ph_mul`), so `b` operator-commutes with every `p_i`, hence with every
   power `a^n = Σ λ_i^n p_i`, every polynomial in `a`, and by closedness with `C(a)`.
4. In a JBW-algebra the relation is symmetric and the operator commutant of `C(b)` is a
   closed subalgebra (`jbw_mul_mem`), so it suffices that *either* `a` or `b` has finite
   spectrum.
Status: 1–4 done (`mem_comm_frame`, `jbw_mem_comm_of_finSpec`), no sorry, axiom-clean.
The general JBW case is NOT reached: for `a` with continuous spectrum the `U_p`-compressed
hypothesis (`p = χ_{>s}(a)`) has non-scalar diagonal terms `U_{r₁}(y₁²) − U_{y₁}(r₁²)`
(a "commutator" `CC* − C*C`, `C = r₁y₁`) that only a trace or Fuglede–Putnam removes, and
norm approximation of `a` by step functions does not preserve the exact hypothesis (the
quantitative form of 1–2 degrades with the level gap at each of ~1/δ induction steps).
Missing input: a Jordan Fuglede–Putnam (or Shirshov–Cohn + Gudder–Nagy).  Note, in special
algebras `[L_x, L_y](x ∘ y) = ¼ (U_x y² − U_y x²)`, so the hypothesis says exactly that the
derivation `[L_{√a}, L_{√b}]` kills `√a ∘ √b`; the goal is that it vanishes.
-/
import Papers.SEA.JBCommThm

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.SEA.JBSeq

open Theses.B.Eff Papers.REC Papers.REC.JBCalc Papers.REC.JBMac Papers.SEA.JBAll
  Papers.SEA.JBComm Papers.REC.JBWProj Filter Topology

universe u

noncomputable section

section Frame

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hJ : JBAlgebra A]

include hJ

attribute [local instance] ousNormedAddCommGroup ousNormedSpace

/-! ## 1. Sums -/

theorem mul_sum' (v : A) {ι : Type*} (s : Finset ι) (f : ι → A) :
    v * ∑ i ∈ s, f i = ∑ i ∈ s, v * f i := by
  have := map_sum (mulC v) f s
  simpa only [mulC_apply] using this

theorem sum_mul' (v : A) {ι : Type*} (s : Finset ι) (f : ι → A) :
    (∑ i ∈ s, f i) * v = ∑ i ∈ s, f i * v := by
  rw [JBAlgebra.mul_comm, mul_sum']
  exact Finset.sum_congr rfl fun i _ => JBAlgebra.mul_comm _ _

theorem jQ_sum (y : A) {ι : Type*} (s : Finset ι) (f : ι → A) :
    jQ y (∑ i ∈ s, f i) = ∑ i ∈ s, jQ y (f i) := by
  simp only [jQ_eq_Uo]; exact map_sum (Uo y) f s

theorem sum_nonneg' {ι : Type*} (s : Finset ι) {f : ι → A} (hf : ∀ i ∈ s, 0 ≤ f i) :
    0 ≤ ∑ i ∈ s, f i :=
  Finset.sum_induction _ (fun v => 0 ≤ v) (fun _ _ => add_nonneg) le_rfl hf

theorem eq_zero_of_sum_eq_zero {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → A}
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∑ i ∈ s, f i = 0) : ∀ i ∈ s, f i = 0 := by
  intro i hi
  have e := Finset.add_sum_erase s f hi
  have hr : 0 ≤ ∑ j ∈ s.erase i, f j :=
    sum_nonneg' _ fun j hj => hf j (Finset.mem_of_mem_erase hj)
  have : f i ≤ 0 := by
    rw [h] at e
    have := le_add_of_nonneg_right (a := f i) hr
    rwa [e] at this
  exact le_antisymm this (hf i hi)

theorem opComm_of_ph' {p y : A} (hp : p * p = p) (h : JBPeirce.Ph p y = 0) : OpComm p y :=
  fun w => comm_of_Ph hp h w

/-! ## 2. Frames -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → A}

theorem frame_mul (hp : ∀ i, p i * p i = p i) (ho : ∀ i j, i ≠ j → p i * p j = 0) (i : ι)
    (c : ι → ℝ) : p i * ∑ j, c j • p j = c i • p i := by
  rw [mul_sum', Finset.sum_eq_single i]
  · rw [jb_mul_smul, hp]
  · intro j _ hji; rw [jb_mul_smul, ho i j (Ne.symm hji), smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem frame_mul_frame (hp : ∀ i, p i * p i = p i) (ho : ∀ i j, i ≠ j → p i * p j = 0)
    (c d : ι → ℝ) : (∑ j, c j • p j) * (∑ j, d j • p j) = ∑ j, (c j * d j) • p j := by
  rw [sum_mul']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [JBAlgebra.smul_mul, frame_mul hp ho, _root_.smul_smul]

theorem frame_mul_mem1 (hp : ∀ i, p i * p i = p i) (ho : ∀ i j, i ≠ j → p i * p j = 0)
    {i : ι} {z : A} (hz : z ∈ JBPeirce.peirce (p i) 1) (c : ι → ℝ) :
    (∑ j, c j • p j) * z = c i • z := by
  rw [sum_mul', Finset.sum_eq_single i]
  · rw [JBAlgebra.smul_mul]
    rw [JBPeirce.mem_peirce, one_smul] at hz
    rw [hz]
  · intro j _ hji
    have hj0 : p j ∈ JBPeirce.peirce (p i) 0 :=
      JBPeirce.mem_peirce_zero_of_orth (ho i j (Ne.symm hji))
    rw [JBAlgebra.smul_mul, JBAlgebra.mul_comm, JBPeirce.peirce_one_mul_zero (hp i) hz hj0,
      smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem frame_opComm (hp : ∀ i, p i * p i = p i) (ho : ∀ i j, i ≠ j → p i * p j = 0)
    (i j : ι) : OpComm (p i) (p j) := by
  refine opComm_of_ph' (hp i) ?_
  by_cases h : j = i
  · subst h
    exact JBPeirce.Ph_of_mem1 (by rw [JBPeirce.mem_peirce, one_smul, hp])
  · exact JBPeirce.Ph_of_mem0 (JBPeirce.mem_peirce_zero_of_orth (ho i j (Ne.symm h)))

theorem opComm_frame_sum {z : A} (h : ∀ j, OpComm z (p j)) (c : ι → ℝ) :
    OpComm z (∑ j, c j • p j) :=
  Finset.sum_induction _ (fun v => OpComm z v) (fun _ _ => opComm_add_right)
    (opComm_zero_left z).symm fun j _ => opComm_smul_right _ (h j)

theorem frame_sum_nonneg (hp : ∀ i, p i * p i = p i) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    0 ≤ ∑ j, c j • p j :=
  sum_nonneg' _ fun j _ => ou_smul_nonneg (hc j) (idem_nonneg (hp j))

/-! ## 3. Two Peirce lemmas -/

/-- `U_p U_y (1 − p) = 0` forces `P½(p) y = 0`. -/
theorem ph_of_jQ_one_sub {q y : A} (hq : q * q = q)
    (h : jQ q (jQ y (ouUnit A - q)) = 0) : JBPeirce.Ph q y = 0 := by
  have hq' : (ouUnit A - q) * (ouUnit A - q) = ouUnit A - q := idem_one_sub hq
  have e : jQ q (jQ y (ouUnit A - q)) =
      JBPeirce.P1 q (JBPeirce.Ph q y * JBPeirce.Ph q y) := by
    rw [jQ_sub, jQ_one, jQ_sub, jQ_idem_jQ_idem hq, ← JBPeirce.P1_eq_jQ hq, P1_mul_self hq]
    abel
  rw [e] at h
  have mh := JBPeirce.Ph_mem hq y
  have mhq : JBPeirce.Ph q y ∈ JBPeirce.peirce (ouUnit A - q) (1 / 2) := by
    rw [JBPeirce.mem_peirce] at mh ⊢
    rw [jb_sub_mul, JBAlgebra.one_mul, mh]
    module
  exact half_eq_zero hq' mhq (by rw [P0_eq_P1_one_sub, sub_sub_cancel]; exact h)

/-- If `y` operator-commutes with `q` and `p ⊥ q`, then `U_p U_y q = 0`. -/
theorem jQ_jQ_orth {p q y : A} (hp : p * p = p) (hq : q * q = q) (hqp : q * p = 0)
    (hy : JBPeirce.Ph q y = 0) : jQ p (jQ y q) = 0 := by
  have c1 : OpComm q y := opComm_of_ph' hq hy
  have c2 : OpComm q (y * y) := opComm_of_ph' hq (Ph_mul hq hy hy)
  have hw : q * jQ y q = jQ y q := by
    rw [jQ, jb_mul_sub, jb_mul_smul, c1 (y * q), c1 q, hq, c2 q, hq]
  have hw1 : jQ y q ∈ JBPeirce.peirce q 1 := by rw [JBPeirce.mem_peirce, one_smul]; exact hw
  have hp0 : p ∈ JBPeirce.peirce q 0 := JBPeirce.mem_peirce_zero_of_orth hqp
  have h0 : p * jQ y q = 0 := by
    rw [JBAlgebra.mul_comm]; exact JBPeirce.peirce_one_mul_zero hq hw1 hp0
  rw [jQ, hp, h0, jb_mul_zero, smul_zero, sub_zero]

/-! ## 4. The key identity `Σ_k (λ_i − λ_k) U_{p_i} U_y p_k = 0` -/

theorem frame_key (hp : ∀ i, p i * p i = p i) (ho : ∀ i j, i ≠ j → p i * p j = 0)
    (hs : ∑ i, p i = ouUnit A) {l : ι → ℝ} (hl0 : ∀ i, 0 ≤ l i) {b : A} (hb : 0 ≤ b)
    (h : sq (∑ j, l j • p j) b = sq b (∑ j, l j • p j)) (i : ι) :
    ∑ k, (l i - l k) • jQ (p i) (jQ (jbSqrt b) (p k)) = 0 := by
  set a := ∑ j, l j • p j with ha
  set r := ∑ j, Real.sqrt (l j) • p j with hr
  have hrr : r * r = a := by
    rw [hr, frame_mul_frame hp ho, ha]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.mul_self_sqrt (hl0 j)]
  have ha0 : 0 ≤ a := frame_sum_nonneg hp hl0
  have hr0 : 0 ≤ r := frame_sum_nonneg hp fun j => Real.sqrt_nonneg _
  have hsr : jbSqrt a = r := (jbSqrt_unique ha0 hr0 hrr).symm
  have c1 : OpComm (p i) r := opComm_frame_sum (frame_opComm hp ho i) _
  have c2 : OpComm (p i) (r * r) := by rw [hrr]; exact opComm_frame_sum (frame_opComm hp ho i) _
  have hcomm : Commute (Uo (p i)) (Uo r) :=
    commute_Uo c1 c2 (by rw [hp]; exact c1) (by rw [hp]; exact c2)
  have hz : jQ (p i) b ∈ JBPeirce.peirce (p i) 1 := by
    rw [← JBPeirce.P1_eq_jQ (hp i) b]; exact JBPeirce.P1_mem (hp i) b
  have hrz : r * jQ (p i) b = Real.sqrt (l i) • jQ (p i) b := frame_mul_mem1 hp ho hz _
  have haz : a * jQ (p i) b = l i • jQ (p i) b := frame_mul_mem1 hp ho hz _
  have hjz : jQ r (jQ (p i) b) = l i • jQ (p i) b := by
    rw [jQ, hrz, jb_mul_smul, hrz, hrr, haz, _root_.smul_smul, _root_.smul_smul, mul_assoc,
      Real.mul_self_sqrt (hl0 i)]
    module
  have hL : jQ (p i) (sq a b) = l i • jQ (p i) b := by
    have e : Uo (p i) (Uo r b) = Uo r (Uo (p i) b) := by
      rw [← mul_apply_eq_comp, hcomm.eq, mul_apply_eq_comp]
    rw [JBAll.sq, hsr]
    simp only [← Uo_apply]
    rw [e]
    simp only [Uo_apply]
    exact hjz
  set y := jbSqrt b with hydef
  have hyy : y * y = b := jbSqrt_mul_self hb
  have hbT : jQ (p i) b = ∑ k, jQ (p i) (jQ y (p k)) := by
    rw [← jQ_sum, ← jQ_sum, hs, jQ_one, hyy]
  have hR : jQ (p i) (sq b a) = ∑ k, l k • jQ (p i) (jQ y (p k)) := by
    rw [JBAll.sq, ← hydef, ha, jQ_sum, jQ_sum]
    simp only [jQ_smul]
  have := congrArg (jQ (p i)) h
  rw [hL, hR, hbT] at this
  have e2 : ∑ k, (l i - l k) • jQ (p i) (jQ y (p k)) =
      l i • ∑ k, jQ (p i) (jQ y (p k)) - ∑ k, l k • jQ (p i) (jQ y (p k)) := by
    simp only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum]
  rw [e2, this, sub_self]

/-! ## 5. Top-down induction -/

theorem ph_frame (hp : ∀ i, p i * p i = p i) (ho : ∀ i j, i ≠ j → p i * p j = 0)
    (hs : ∑ i, p i = ouUnit A) {l : ι → ℝ} (hl0 : ∀ i, 0 ≤ l i) (hinj : Function.Injective l)
    {b : A} (hb : 0 ≤ b) (h : sq (∑ j, l j • p j) b = sq b (∑ j, l j • p j)) :
    ∀ i, JBPeirce.Ph (p i) (jbSqrt b) = 0 := by
  have key := frame_key hp ho hs hl0 hb h
  set y := jbSqrt b
  have hT0 : ∀ i k, 0 ≤ jQ (p i) (jQ y (p k)) := fun i k =>
    jQ_nonneg _ (jQ_nonneg _ (idem_nonneg (hp k)))
  have step : ∀ i, (∀ j, l i < l j → JBPeirce.Ph (p j) y = 0) → JBPeirce.Ph (p i) y = 0 := by
    intro i hi
    have hgt : ∀ k, l i < l k → jQ (p i) (jQ y (p k)) = 0 := fun k hk =>
      jQ_jQ_orth (hp i) (hp k) (ho k i fun e => by subst e; exact lt_irrefl _ hk) (hi k hk)
    have hnn : ∀ k ∈ Finset.univ, 0 ≤ (l i - l k) • jQ (p i) (jQ y (p k)) := by
      intro k _
      rcases le_or_gt (l k) (l i) with hk | hk
      · exact ou_smul_nonneg (sub_nonneg.2 hk) (hT0 i k)
      · rw [hgt k hk, smul_zero]
    have hz := eq_zero_of_sum_eq_zero _ hnn (key i)
    have hall : ∀ k ∈ Finset.univ.erase i, jQ (p i) (jQ y (p k)) = 0 := by
      intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      rcases lt_or_gt_of_ne (fun e : l k = l i => hki (hinj e)) with hk' | hk'
      · have := hz k (Finset.mem_univ k)
        rw [smul_eq_zero] at this
        exact this.resolve_left (sub_ne_zero.2 (ne_of_gt hk'))
      · exact hgt k hk'
    refine ph_of_jQ_one_sub (hp i) ?_
    have e : ouUnit A - p i = ∑ k ∈ Finset.univ.erase i, p k := by
      rw [← hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
    rw [e, jQ_sum, jQ_sum]
    exact Finset.sum_eq_zero hall
  have ind : ∀ m, ∀ i, (Finset.univ.filter fun j => l i < l j).card = m →
      JBPeirce.Ph (p i) y = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hm
      refine step i fun j hj => ih _ ?_ j rfl
      rw [← hm]
      have hsub : (Finset.univ.filter fun k => l j < l k) ⊆
          (Finset.univ.filter fun k => l i < l k) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact hj.trans hk
      refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨j, ?_, ?_⟩)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hj
      · simp
  exact fun i => ind _ i rfl

/-! ## 6. The finite-spectrum hard half -/

/-- **Van de Wetering's hard half for `a` with finite spectrum**, in every JB-algebra:
`a = Σ λ_i p_i` over a frame of orthogonal idempotents summing to `1`, `λ_i ≥ 0` distinct,
`b ≥ 0`, `U_{√a} b = U_{√b} a` ⇒ `b` lies in the operator commutant of `C(a)`. -/
theorem mem_comm_frame (hp : ∀ i, p i * p i = p i) (ho : ∀ i j, i ≠ j → p i * p j = 0)
    (hs : ∑ i, p i = ouUnit A) {l : ι → ℝ} (hl0 : ∀ i, 0 ≤ l i) (hinj : Function.Injective l)
    {a b : A} (ha : a = ∑ j, l j • p j) (hb : 0 ≤ b) (h : sq a b = sq b a) : b ∈ comm a := by
  subst ha
  have hph := ph_frame hp ho hs hl0 hinj hb h
  have hpb : ∀ j, OpComm (p j) b := fun j => by
    have := Ph_mul (hp j) (hph j) (hph j)
    rw [jbSqrt_mul_self hb] at this
    exact opComm_of_ph' (hp j) this
  have hsumb : ∀ c : ι → ℝ, OpComm (∑ j, c j • p j) b := fun c =>
    Finset.sum_induction _ (fun v => OpComm v b) (fun _ _ => opComm_add_left)
      (opComm_zero_left b) fun j _ => opComm_smul_left _ (hpb j)
  have hpow : ∀ n : ℕ, jbPow (∑ j, l j • p j) (n + 1) = ∑ j, (l j ^ (n + 1)) • p j := by
    intro n
    induction n with
    | zero => rw [jbPow_succ, jbPow_zero, JBAlgebra.mul_one]; simp only [zero_add, pow_one]
    | succ n ih =>
      rw [jbPow_succ, ih, frame_mul_frame hp ho]
      exact Finset.sum_congr rfl fun j _ => by rw [pow_succ' (l j) (n + 1)]
  have hopow : ∀ n : ℕ, OpComm (jbPow (∑ j, l j • p j) n) b := by
    intro n
    rcases n with _ | n
    · rw [jbPow_zero]; exact opComm_one_left b
    · rw [hpow]; exact hsumb _
  intro x hx
  have hsub : Set.range (jbEv (∑ j, l j • p j)) ⊆ {x | OpComm x b} := by
    rintro _ ⟨q, rfl⟩
    induction q using Polynomial.induction_on' with
    | add q q' hq hq' => rw [map_add]; exact opComm_add_left hq hq'
    | monomial n r => rw [jbEv_monomial]; exact opComm_smul_left r (hopow n)
  exact (isClosed_opComm_left b).closure_subset_iff.2 hsub (mem_Ca.1 hx)

end Frame

/-! ## 7. JBW: finite spectrum on either side -/

section JBW

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hW : JBWAlgebra A]

include hW

attribute [local instance] ousNormedAddCommGroup ousNormedSpace

/-- In a JBW-algebra the operator commutant of `C(c)` is a closed unital subalgebra. -/
def commSubW (c : A) : ClosedJBSub A where
  carrier := commSubmodule c
  one_mem := fun _ _ => (opComm_one_left _).symm
  mul_mem := fun hy hz => jbw_mul_mem hy hz
  closed := comm_closed c

/-- In a JBW-algebra, `a ∈ comm b ⇒ b ∈ comm a`. -/
theorem mem_comm_symm {a b : A} (h : a ∈ comm b) : b ∈ comm a := fun x hx =>
  ((Ca_le (commSubW b) h hx : x ∈ comm b) b (self_mem_Ca b)).symm

variable (A) in
/-- `a` has **finite spectrum**: `a = Σ_{i<n} λ_i p_i` over a frame of orthogonal idempotents
summing to `1`, with distinct `λ_i ≥ 0`. -/
def FinSpec (a : A) : Prop :=
  ∃ (n : ℕ) (p : Fin n → A) (l : Fin n → ℝ), (∀ i, p i * p i = p i) ∧
    (∀ i j, i ≠ j → p i * p j = 0) ∧ ∑ i, p i = ouUnit A ∧ (∀ i, 0 ≤ l i) ∧
    Function.Injective l ∧ a = ∑ i, l i • p i

/-- **Van de Wetering's hard half in a JBW-algebra when `a` or `b` has finite spectrum**:
for `a, b ≥ 0` with `U_{√a} b = U_{√b} a`, `b` operator-commutes with every element of `C(a)`. -/
theorem jbw_mem_comm_of_finSpec {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfin : FinSpec A a ∨ FinSpec A b) (h : sq a b = sq b a) : b ∈ comm a := by
  rcases hfin with ⟨n, p, l, hp, ho, hs, hl0, hinj, he⟩ | ⟨n, p, l, hp, ho, hs, hl0, hinj, he⟩
  · exact mem_comm_frame hp ho hs hl0 hinj he hb h
  · exact mem_comm_symm (mem_comm_frame hp ho hs hl0 hinj he ha h.symm)

end JBW

end

end Papers.SEA.JBSeq
