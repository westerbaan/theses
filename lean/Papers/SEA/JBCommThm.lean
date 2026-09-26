/-
Papers/SEA/JBCommThm.lean

**SEA 16** (`ex:canonical-sea`, second.tex:475): closing the commutation inputs of
`Papers.SEA.JBAllSEA` as far as possible.

Plan (2026-09-26; budget ~4 h).  Cheapest correct route, JBW first.
1. Normality of operator commutation, in every JB-algebra (no normal states needed):
   call a bounded operator *good* if it is positive and preserves least upper bounds of
   non-empty directed bounded subsets of `A₊`.  `U_r` (`r ≥ 0`) is good (`jQ_isLUB` of
   `JBAllSEA` + scaling); good operators are closed under `+`, `·`, `c ≥ 0` (the sum rule
   `sup (f + g) = sup f + sup g` on a directed set is pure order theory).  Every `L_v` is a
   difference of good operators: `N L_v = U_{(N+v)/2} - U_{(N-v)/2}`.  Hence so is
   `L_x L_w - L_{xw}`, and a difference `P - N` of good maps vanishing on a directed `D`
   vanishes on `sup D` (`P '' D = N '' D`, least upper bounds are unique).  So
   `{y ; OpComm x y}` is closed under directed suprema in `[0,1]`:
   **`JBWCommSup` holds in every JBW-algebra** (`jbwCommSup`).
2. `mul_mem` for JBW: for `x ∈ C(c)` the spectral projections `sproj (rampF x δ j)` of
   `JBWProj` are suprema of increasing sequences in `C(x) ⊆ C(c)`, so by 1 they operator
   commute with every `y ∈ comm c`; for an idempotent `q`, `OpComm q y ⟺ P½(q) y = 0`, and
   `ker P½(q)` is a subalgebra (`Ph_mul`); the spectral theorem (`spectral_approx`,
   restated with its projections explicit) and closedness give `OpComm x (yz)`.
   **`JBCommutation.mul_mem` holds in every JBW-algebra** (`jbw_mul_mem`).
3. `mem_comm` for `a` with at most two spectral values, in every JB-algebra
   (`mem_comm_two_level`; the sharp case `mem_comm_idem` separately): for
   `a = l p + m (1 - p)`, `l > m ≥ 0`, apply `U_p` to `U_{√a} b = U_{√b} a`; with `y = √b`,
   `U_p U_{√a} b = l U_p b = l (y₁² + U_p(y½²))` and (fundamental formula
   `U_p U_y U_p = U_{U_p y}`) `U_p U_y a = l y₁² + m U_p(y½²)`, so `U_p(y½²) = 0`, `y½ = 0`
   (`half_eq_zero`) and `P½(p) b = 0`.
4. Consequences: `sea16_jbw_of_seqComm`: every JBW-algebra satisfying only the
   sequential-commutation hypothesis `mem_comm` (`JBSeqComm`) is a convex normal SEA.
Status: 1–4 done, no sorry, axiom-clean.  Open: `mem_comm` for general `a` (van de
Wetering's hard half), and `mul_mem` for JB-algebras that are not JBW (bidual).  The
argument of 3 needs the top level of `a` on `p` to be a scalar: for `a = a₁ + a₀`
(`a₁ ≥ λp` not scalar) the diagonal terms `U_{√a₁}(y₁²)` and `U_{y₁} a₁` no longer cancel
without a trace — this is where Fuglede–Putnam (or Shirshov–Cohn + Gudder–Nagy) enters in
the literature.  Finite spectrum should follow from 3 by top-down induction over a frame.
-/
import Papers.SEA.JBAllSEA
import Papers.REC.JBWProj

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.SEA.JBComm

open Theses.B.Eff Papers.REC Papers.REC.JBCalc Papers.REC.JBMac Papers.SEA.JBAll Filter
  Topology

universe u

noncomputable section

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hJ : JBAlgebra A]

include hJ

attribute [local instance] ousNormedAddCommGroup ousNormedSpace

/-! ## 1. Order lemmas -/

/-- Least upper bounds scale by `c ≥ 0` (non-empty sets). -/
theorem isLUB_smul {S : Set A} {s : A} (hs : IsLUB S s) (hne : S.Nonempty) {c : ℝ}
    (hc : 0 ≤ c) : IsLUB ((fun v => c • v) '' S) (c • s) := by
  rcases hc.eq_or_lt with h0 | hpos
  · subst h0
    have : ((fun v : A => (0 : ℝ) • v) '' S) = {0} := by
      ext v; simp only [zero_smul, Set.mem_image, Set.mem_singleton_iff]
      exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨hne.some, hne.some_mem, h.symm⟩⟩
    rw [this, zero_smul]; exact isLUB_singleton
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩; exact ou_smul_le_smul hc (hs.1 hv)
  · have h1 : s ≤ c⁻¹ • u := hs.2 fun v hv => by
      have := ou_smul_le_smul (inv_nonneg.2 hc) (hu ⟨v, hv, rfl⟩)
      rwa [_root_.smul_smul, inv_mul_cancel₀ hpos.ne', one_smul] at this
    have := ou_smul_le_smul hc h1
    rwa [_root_.smul_smul, mul_inv_cancel₀ hpos.ne', one_smul] at this

/-- On a directed set, the supremum of a sum of monotone maps is the sum of suprema. -/
theorem isLUB_add_of_directed {D : Set A} (hdir : DirectedOn (· ≤ ·) D) {f g : A → A}
    (hf : MonotoneOn f D) (hg : MonotoneOn g D) {F G : A} (hF : IsLUB (f '' D) F)
    (hG : IsLUB (g '' D) G) : IsLUB ((fun d => f d + g d) '' D) (F + G) := by
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩; exact add_le_add (hF.1 ⟨d, hd, rfl⟩) (hG.1 ⟨d, hd, rfl⟩)
  · have key : ∀ d' ∈ D, g d' ≤ u - F := fun d' hd' => by
      have : F ≤ u - g d' := hF.2 (by
        rintro _ ⟨d, hd, rfl⟩
        obtain ⟨e, he, hde, hd'e⟩ := hdir d hd d' hd'
        have := hu ⟨e, he, rfl⟩
        have h2 : f d + g d' ≤ f e + g e := add_le_add (hf hd he hde) (hg hd' he hd'e)
        exact le_sub_iff_add_le.2 (h2.trans this))
      exact le_sub_comm.1 this
    have : G ≤ u - F := hG.2 (by rintro _ ⟨d, hd, rfl⟩; exact key d hd)
    rw [add_comm]; exact le_sub_iff_add_le.1 this

theorem directedOn_image {D : Set A} (hdir : DirectedOn (· ≤ ·) D) {f : A → A}
    (hf : MonotoneOn f D) : DirectedOn (· ≤ ·) (f '' D) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
  exact ⟨f c, ⟨c, hc, rfl⟩, hf ha hc hac, hf hb hc hbc⟩

/-! ## 2. Good operators -/

/-- A bounded operator is **good** when it is positive and preserves least upper bounds of
non-empty directed subsets of some `[0, M·1]`. -/
def Good (T : A →L[ℝ] A) : Prop :=
  (∀ v, 0 ≤ v → 0 ≤ T v) ∧ ∀ (D : Set A) (M : ℝ), D ⊆ Set.Icc 0 (M • ouUnit A) →
    D.Nonempty → DirectedOn (· ≤ ·) D → ∀ s, IsLUB D s → IsLUB (T '' D) (T s)

theorem Good.mono {T : A →L[ℝ] A} (hT : Good T) {v w : A} (h : v ≤ w) : T v ≤ T w := by
  have := hT.1 (w - v) (sub_nonneg.2 h); rwa [map_sub, sub_nonneg] at this

theorem good_add {T T' : A →L[ℝ] A} (hT : Good T) (hT' : Good T') : Good (T + T') := by
  refine ⟨fun v hv => ?_, fun D M hD hne hdir s hs => ?_⟩
  · rw [add_apply]; exact add_nonneg (hT.1 v hv) (hT'.1 v hv)
  · have e : ((T + T' : A →L[ℝ] A) '' D) = (fun d => T d + T' d) '' D := by
      ext v; simp
    rw [e, add_apply]
    exact isLUB_add_of_directed hdir (fun _ _ _ _ h => hT.mono h) (fun _ _ _ _ h => hT'.mono h)
      (hT.2 D M hD hne hdir s hs) (hT'.2 D M hD hne hdir s hs)

theorem good_smul {T : A →L[ℝ] A} (hT : Good T) {c : ℝ} (hc : 0 ≤ c) : Good (c • T) := by
  refine ⟨fun v hv => by rw [smul_apply]; exact ou_smul_nonneg hc (hT.1 v hv),
    fun D M hD hne hdir s hs => ?_⟩
  have e : ((c • T : A →L[ℝ] A) '' D) = (fun v => c • v) '' (T '' D) := by
    rw [Set.image_image]; rfl
  rw [e, smul_apply]
  exact isLUB_smul (hT.2 D M hD hne hdir s hs) (hne.image _) hc

theorem good_mul {T T' : A →L[ℝ] A} (hT : Good T) (hT' : Good T') : Good (T * T') := by
  refine ⟨fun v hv => hT.1 _ (hT'.1 v hv), fun D M hD hne hdir s hs => ?_⟩
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit (T' (M • ouUnit A))
  have hD' : T' '' D ⊆ Set.Icc 0 ((n : ℝ) • ouUnit A) := by
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨hT'.1 d (hD hd).1, (hT'.mono (hD hd).2).trans hn⟩
  have e : ((T * T' : A →L[ℝ] A) '' D) = T '' (T' '' D) := by
    rw [Set.image_image]; rfl
  rw [e]
  exact hT.2 _ _ hD' (hne.image _) (directedOn_image hdir fun _ _ _ _ h => hT'.mono h) _
    (hT'.2 D M hD hne hdir s hs)

theorem ousNorm_zero_A : ousNorm A (0 : A) = 0 :=
  le_antisymm (ousNorm_le_rc le_rfl (by simp) (by simp)) (ousNorm_nonneg_rc _)

/-- A positive operator preserving least upper bounds of subsets of `[0,1]` is good. -/
theorem good_of_unit {T : A →L[ℝ] A} (hpos : ∀ v, 0 ≤ v → 0 ≤ T v)
    (hT : ∀ (D : Set A), D ⊆ Set.Icc 0 (ouUnit A) → D.Nonempty → ∀ s, IsLUB D s →
      IsLUB (T '' D) (T s)) : Good T := by
  refine ⟨hpos, fun D M hD hne hdir s hs => ?_⟩
  set N := max M 1 with hN
  have hN0 : 0 < N := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hD' : (fun v => N⁻¹ • v) '' D ⊆ Set.Icc 0 (ouUnit A) := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨ou_smul_nonneg (inv_nonneg.2 hN0.le) (hD hd).1, ?_⟩
    have h1 : d ≤ N • ouUnit A := (hD hd).2.trans (ou_smul_unit_mono (le_max_left _ _))
    have := ou_smul_le_smul (inv_nonneg.2 hN0.le) h1
    rwa [_root_.smul_smul, inv_mul_cancel₀ hN0.ne', one_smul] at this
  have hs' := isLUB_smul hs hne (inv_nonneg.2 hN0.le)
  have h1 := hT _ hD' (hne.image _) _ hs'
  have h2 := isLUB_smul h1 (hne.image _ |>.image _) hN0.le
  have e1 : (fun v => N • v) '' (T '' ((fun v => N⁻¹ • v) '' D)) = T '' D := by
    rw [Set.image_image, Set.image_image]
    congr 1; funext v
    rw [map_smul, _root_.smul_smul, mul_inv_cancel₀ hN0.ne', one_smul]
  rw [e1, map_smul, _root_.smul_smul, mul_inv_cancel₀ hN0.ne', one_smul] at h2
  exact h2

theorem Uo_smul (c : ℝ) (r : A) : Uo (c • r) = (c * c) • Uo r := by
  ext v
  rw [smul_apply, Uo_apply, Uo_apply]
  simp only [jQ, JBAlgebra.smul_mul, jb_mul_smul, _root_.smul_smul, smul_sub]
  module

/-- `U_r` is good for every `r ≥ 0`. -/
theorem good_Uo {r : A} (hr : 0 ≤ r) : Good (Uo r) := by
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit r
  set N : ℝ := (n : ℝ) + 1
  have hN : 0 < N := by positivity
  set r' := N⁻¹ • r
  have hr'0 : 0 ≤ r' := ou_smul_nonneg (inv_nonneg.2 hN.le) hr
  have hr'1 : r' ≤ ouUnit A := by
    have h1 : r ≤ N • ouUnit A := hn.trans (ou_smul_unit_mono (by linarith))
    have := ou_smul_le_smul (inv_nonneg.2 hN.le) h1
    rwa [_root_.smul_smul, inv_mul_cancel₀ hN.ne', one_smul] at this
  have e : Uo r = (N * N) • Uo r' := by
    rw [← Uo_smul, _root_.smul_smul, mul_inv_cancel₀ hN.ne', one_smul]
  rw [e]
  refine good_smul (good_of_unit (fun v hv => by rw [Uo_apply]; exact jQ_nonneg _ hv)
    fun D hD hne s hs => ?_) (by positivity)
  have hs1 : s ∈ Set.Icc 0 (ouUnit A) :=
    ⟨(hD hne.some_mem).1.trans (hs.1 hne.some_mem), hs.2 fun v hv => (hD hv).2⟩
  have := jQ_isLUB hr'0 hr'1 hD hs1 hs
  have e2 : (Uo r' : A → A) = jQ r' := funext fun v => Uo_apply r' v
  rw [e2]; exact this

/-! ## 3. Differences of good operators -/

/-- `T` is a difference of good operators. -/
def Nrm (T : A →L[ℝ] A) : Prop := ∃ P N : A →L[ℝ] A, Good P ∧ Good N ∧ T = P - N

theorem nrm_sub {T T' : A →L[ℝ] A} (hT : Nrm T) (hT' : Nrm T') : Nrm (T - T') := by
  obtain ⟨P, N, hP, hN, rfl⟩ := hT
  obtain ⟨P', N', hP', hN', rfl⟩ := hT'
  exact ⟨P + N', N + P', good_add hP hN', good_add hN hP', by abel⟩

theorem nrm_mul {T T' : A →L[ℝ] A} (hT : Nrm T) (hT' : Nrm T') : Nrm (T * T') := by
  obtain ⟨P, N, hP, hN, rfl⟩ := hT
  obtain ⟨P', N', hP', hN', rfl⟩ := hT'
  exact ⟨P * P' + N * N', P * N' + N * P', good_add (good_mul hP hP') (good_mul hN hN'),
    good_add (good_mul hP hN') (good_mul hN hP'), by noncomm_ring⟩

/-- `N L_v = U_{(N+v)/2} - U_{(N-v)/2}`. -/
theorem Uo_diff (v w : A) (N : ℝ) :
    Uo ((2⁻¹ : ℝ) • (N • ouUnit A + v)) w - Uo ((2⁻¹ : ℝ) • (N • ouUnit A - v)) w =
      N • (v * w) := by
  rw [Uo_apply, Uo_apply]
  simp only [jQ, JBAlgebra.add_mul, jb_mul_add, jb_sub_mul, jb_mul_sub, JBAlgebra.smul_mul,
    jb_mul_smul, JBAlgebra.one_mul, JBAlgebra.mul_one, JBAlgebra.mul_comm (ouUnit A) v,
    _root_.smul_smul, smul_add, smul_sub]
  module

theorem nrm_mulC (v : A) : Nrm (mulC v) := by
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit v
  obtain ⟨n', hn'⟩ := ou_exists_le_smul_unit (-v)
  set N : ℝ := (n : ℝ) + n' + 1
  have hN : 0 < N := by positivity
  have c1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have c2 : (0 : ℝ) ≤ n' := Nat.cast_nonneg n'
  have h1 : 0 ≤ (2⁻¹ : ℝ) • (N • ouUnit A + v) := by
    refine ou_smul_nonneg (by norm_num) ?_
    have : -v ≤ N • ouUnit A := hn'.trans (ou_smul_unit_mono (by linarith))
    rw [← sub_nonneg, sub_neg_eq_add] at this; exact this
  have h2 : 0 ≤ (2⁻¹ : ℝ) • (N • ouUnit A - v) := by
    refine ou_smul_nonneg (by norm_num) ?_
    have : v ≤ N • ouUnit A := hn.trans (ou_smul_unit_mono (by linarith))
    exact sub_nonneg.2 this
  refine ⟨N⁻¹ • Uo ((2⁻¹ : ℝ) • (N • ouUnit A + v)), N⁻¹ • Uo ((2⁻¹ : ℝ) • (N • ouUnit A - v)),
    good_smul (good_Uo h1) (inv_nonneg.2 hN.le), good_smul (good_Uo h2) (inv_nonneg.2 hN.le), ?_⟩
  ext w
  rw [sub_apply, smul_apply,
    smul_apply, ← smul_sub, Uo_diff, _root_.smul_smul,
    inv_mul_cancel₀ hN.ne', one_smul, mulC_apply]

/-- A difference of good operators vanishing on a directed set vanishes at its supremum. -/
theorem Nrm.eq_zero {T : A →L[ℝ] A} (hT : Nrm T) {D : Set A} (hD : D ⊆ Set.Icc 0 (ouUnit A))
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) {s : A} (hs : IsLUB D s)
    (h0 : ∀ d ∈ D, T d = 0) : T s = 0 := by
  obtain ⟨P, N, hP, hN, rfl⟩ := hT
  have hD1 : D ⊆ Set.Icc 0 ((1 : ℝ) • ouUnit A) := by rwa [one_smul]
  have h1 := hP.2 D 1 hD1 hne hdir s hs
  have h2 := hN.2 D 1 hD1 hne hdir s hs
  have e : (P '' D) = (N '' D) := Set.image_congr fun d hd => by
    have := h0 d hd
    rwa [sub_apply, sub_eq_zero] at this
  rw [e] at h1
  rw [sub_apply, h1.unique h2, sub_self]

/-- **Operator commutation is normal**, in every JB-algebra: if `x` operator-commutes with
every element of a non-empty directed `D ⊆ [0,1]`, it operator-commutes with `sup D`. -/
theorem opComm_of_isLUB {x : A} {D : Set A} (hD : D ⊆ Set.Icc 0 (ouUnit A)) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) {s : A} (hs : IsLUB D s) (h : ∀ d ∈ D, OpComm x d) :
    OpComm x s := fun w => by
  have hT : Nrm (mulC x * mulC w - mulC (x * w)) :=
    nrm_sub (nrm_mul (nrm_mulC x) (nrm_mulC w)) (nrm_mulC _)
  have := hT.eq_zero hD hne hdir hs fun d hd => by
    rw [sub_apply, mul_apply_eq_comp, mulC_apply, mulC_apply,
      mulC_apply, JBAlgebra.mul_comm w d, h d hd w, JBAlgebra.mul_comm d, sub_self]
  rw [sub_apply, mul_apply_eq_comp, mulC_apply, mulC_apply,
    mulC_apply, sub_eq_zero, JBAlgebra.mul_comm w s] at this
  rw [this, JBAlgebra.mul_comm]

end

/-! ## 4. `JBWCommSup` holds in every JBW-algebra -/

section JBW

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hW : JBWAlgebra A]

include hW

attribute [local instance] ousNormedAddCommGroup ousNormedSpace

/-- **The JBW commutation input `JBWCommSup` holds in every JBW-algebra.** -/
theorem jbwCommSup : JBWCommSup A :=
  ⟨fun _ _ _ hD hne hdir _ hx hDc x' hx' =>
    opComm_of_isLUB hD hne hdir hx fun _ hd => hDc hd x' hx'⟩

/-! ## 5. `mul_mem` in every JBW-algebra -/

open Papers.REC.JBWProj

theorem ph_of_opComm {p y : A} (hp : p * p = p) (h : OpComm p y) : JBPeirce.Ph p y = 0 := by
  have h1 := h p
  rw [hp, JBAlgebra.mul_comm y p] at h1
  rw [JBPeirce.Ph_apply, h1, sub_self]

theorem opComm_of_ph {p y : A} (hp : p * p = p) (h : JBPeirce.Ph p y = 0) : OpComm p y :=
  fun w => comm_of_Ph hp h w

/-- `spectral_approx_norm` of `JBWProj` with its idempotents explicit: `x` is within `δ` of
`c·1 + δ Σ_{i<m} p_{i+1}`, `p_j = sproj (rampF x δ j)` the spectral projection of
`{x > -‖x‖ + jδ}`. -/
theorem spectral_approx_expl (a : A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (m : ℕ) (c : ℝ), ousNorm A (a - (c • ouUnit A + δ • ∑ i ∈ Finset.range m,
      sproj (rampF a δ (i + 1)))) ≤ δ := by
  set M := ousNorm A a with hM
  set m := ⌈2 * M / δ⌉₊ with hm
  have hK : 2 * M ≤ ((m + 1 : ℕ) : ℝ) * δ := by
    have := Nat.le_ceil (2 * M / δ)
    rw [div_le_iff₀ hδ] at this
    push_cast
    nlinarith
  refine ⟨m, -M, ousNorm_le_rc hδ.le ((neg_nonpos.2 (ou_smul_unit_nonneg hδ.le)).trans ?_) ?_⟩
  · -- lower bound
    have hsum := sum_clamp a hδ hK
    rw [← hM] at hsum
    rw [Finset.sum_range_succ] at hsum
    have h1 : δ • ∑ i ∈ Finset.range m, sproj (rampF a δ (i + 1)) ≤
        ∑ i ∈ Finset.range m, jbCfc a (clampF a δ i) := by
      rw [Finset.smul_sum]; exact Finset.sum_le_sum fun i _ => proj_le_clamp a hδ i
    have h2 : 0 ≤ jbCfc a (clampF a δ m) :=
      (jbCfc_nonneg_iff a _).2 fun t => le_min (le_max_right _ _) hδ.le
    have : δ • ∑ i ∈ Finset.range m, sproj (rampF a δ (i + 1)) ≤ a + M • ouUnit A := by
      rw [← hsum]; exact h1.trans (le_add_of_nonneg_right h2)
    rw [neg_smul, sub_nonneg]
    calc -(M • ouUnit A) + δ • ∑ i ∈ Finset.range m, sproj (rampF a δ (i + 1))
        ≤ -(M • ouUnit A) + (a + M • ouUnit A) := add_le_add le_rfl this
      _ = a := by abel
  · -- upper bound
    have hsum := sum_clamp a hδ hK
    rw [← hM] at hsum
    have h1 : ∑ j ∈ Finset.range (m + 1), jbCfc a (clampF a δ j) ≤
        δ • ∑ j ∈ Finset.range (m + 1), sproj (rampF a δ j) := by
      rw [Finset.smul_sum]; exact Finset.sum_le_sum fun j _ => clamp_le_proj a hδ j
    rw [hsum, Finset.sum_range_succ' (fun j => sproj (rampF a δ j)), smul_add] at h1
    have h0 : δ • sproj (rampF a δ 0) ≤ δ • ouUnit A :=
      ou_smul_le_smul hδ.le (sproj_le_one (rampF_nonneg a 0))
    have := h1.trans (add_le_add le_rfl h0)
    rw [neg_smul, sub_le_iff_le_add]
    calc a = a + M • ouUnit A - M • ouUnit A := by abel
      _ ≤ δ • ∑ i ∈ Finset.range m, sproj (rampF a δ (i + 1)) + δ • ouUnit A - M • ouUnit A :=
          sub_le_sub_right this _
      _ = δ • ouUnit A + (-(M • ouUnit A) + δ • ∑ i ∈ Finset.range m,
            sproj (rampF a δ (i + 1))) := by abel

/-- The spectral projections of any `x ∈ C(c)` operator-commute with every `y` in the
operator commutant of `C(c)`: they are suprema of increasing sequences in `C(x) ⊆ C(c)`
(normality, §3). -/
theorem opComm_sproj_of_comm {c x y : A} (hx : x ∈ (Ca c).carrier) (hy : y ∈ comm c)
    {g : C(jbSpec x, ℝ)} (hg : ∀ t, 0 ≤ g t) : OpComm (sproj g) y := by
  refine (opComm_of_isLUB (x := y) (D := Set.range (sseq g)) ?_ ⟨_, ⟨0, rfl⟩⟩ ?_
    (sproj_isLUB hg) ?_).symm
  · rintro _ ⟨n, rfl⟩; exact ⟨sseq_nonneg hg n, sseq_le_one n⟩
  · exact directedOn_range.2 (sseq_mono hg).directed_le
  · rintro _ ⟨n, rfl⟩; exact (hy _ (Ca_le (Ca c) hx (jbCfc_mem x _))).symm

/-- An element operator-commuting with all spectral projections of `x` operator-commutes
with `x` (spectral theorem + closedness). -/
theorem opComm_of_sprojs {x y : A}
    (h : ∀ δ : ℝ, 0 < δ → ∀ j : ℕ, OpComm (sproj (rampF x δ j)) y) : OpComm x y := by
  have hcl := isClosed_opComm_left y
  have : x ∈ closure {z | OpComm z y} := Metric.mem_closure_iff.2 fun ε hε => by
    obtain ⟨m, c, hm⟩ := spectral_approx_expl x (half_pos hε)
    refine ⟨c • ouUnit A + (ε / 2) • ∑ i ∈ Finset.range m, sproj (rampF x (ε / 2) (i + 1)),
      ?_, ?_⟩
    · refine opComm_add_left (opComm_smul_left _ (opComm_one_left y)) (opComm_smul_left _ ?_)
      exact Finset.sum_induction _ (fun z => OpComm z y) (fun _ _ => opComm_add_left)
        (opComm_zero_left y) fun i _ => h _ (half_pos hε) _
    · rw [dist_eq_norm]; exact lt_of_le_of_lt hm (half_lt_self hε)
  exact hcl.closure_subset this

/-- **`JBCommutation.mul_mem` in every JBW-algebra**: the operator commutant of `C(c)` is
closed under the Jordan product.  For `x ∈ C(c)` and each spectral projection `q` of `x`,
`y, z ∈ comm c` lie in `ker P½(q) = V₁(q) + V₀(q)`, a subalgebra; so `q` operator-commutes
with `yz`, and so does `x`. -/
theorem jbw_mul_mem {c y z : A} (hy : y ∈ comm c) (hz : z ∈ comm c) : y * z ∈ comm c :=
  fun x hx => opComm_of_sprojs fun δ _ j => by
    have hg := rampF_nonneg (δ := δ) x j
    have hp := sproj_idem hg
    exact opComm_of_ph hp (Ph_mul hp (ph_of_opComm hp (opComm_sproj_of_comm hx hy hg))
      (ph_of_opComm hp (opComm_sproj_of_comm hx hz hg)))

/-! ## 6. SEA 16 for JBW-algebras from sequential commutation alone -/

variable (A) in
/-- The remaining input: van de Wetering's hard half (with H-O–S's passage to `C(a)`). -/
structure JBSeqComm : Prop where
  mem_comm : ∀ a b : A, 0 ≤ a → 0 ≤ b → sq a b = sq b a → b ∈ comm a

theorem jbCommutation_of_seqComm (H : JBSeqComm A) : JBCommutation A :=
  ⟨H.mem_comm, fun _ _ _ _ hy hz => jbw_mul_mem hy hz⟩

/-- **SEA 16, JBW half, from `mem_comm` alone**: every JBW-algebra in which `U_{√a} b =
U_{√b} a` forces `b` to operator-commute with `C(a)` is a convex normal SEA with
`a ∘ b = U_{√a} b` (`JBWCommSup` and `mul_mem` are now theorems). -/
theorem sea16_jbw_of_seqComm (H : JBSeqComm A) :
    @IsConvex _ (jbEA A) ∧
    ∀ a b : Set.Icc (0 : A) (ouUnit A),
      ∃! r : A, 0 ≤ r ∧ r * r = a.1 ∧
        (@SequentialEffectAlgebra.seq _ (jbEA A)
          (jbwNormalSEA (jbCommutation_of_seqComm H) jbwCommSup).toSequentialEffectAlgebra
            a b).1 = (2 : ℝ) • (r * (r * b.1)) - (r * r) * b.1 :=
  sea16_jbw _ _

end JBW

/-! ## 7. `mem_comm` for idempotent `a`, in every JB-algebra -/

section Idem

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hJ : JBAlgebra A]

include hJ

attribute [local instance] ousNormedAddCommGroup ousNormedSpace

open Papers.REC.JBWProj

theorem opComm_jbPow_idem {p b : A} (hp : p * p = p) (h : OpComm p b) (n : ℕ) :
    OpComm (jbPow p n) b := by
  rcases n with _ | n
  · rw [jbPow_zero]; exact opComm_one_left b
  · have : jbPow p (n + 1) = p := by
      induction n with
      | zero => rw [jbPow_succ, jbPow_zero, JBAlgebra.mul_one]
      | succ n ih => rw [jbPow_succ, ih, hp]
    rw [this]; exact h

/-- For an idempotent `p`, operator-commuting with `p` is the same as lying in the
operator commutant of `C(p)`. -/
theorem mem_comm_of_opComm_idem {p b : A} (hp : p * p = p) (h : OpComm p b) : b ∈ comm p := by
  intro x hx
  have hsub : Set.range (jbEv p) ⊆ {x | OpComm x b} := by
    rintro _ ⟨q, rfl⟩
    induction q using Polynomial.induction_on' with
    | add q q' hq hq' => rw [map_add]; exact opComm_add_left hq hq'
    | monomial n r => rw [jbEv_monomial]; exact opComm_smul_left r (opComm_jbPow_idem hp h n)
  exact (isClosed_opComm_left b).closure_subset_iff.2 hsub (mem_Ca.1 hx)

/-- **Van de Wetering's hard half for a sharp element**, in every JB-algebra: for an
idempotent `p` and `b ≥ 0`, `U_p b = U_{√b} p` forces `b` into the operator commutant of
`C(p)`.  `U_{√b} p ≤ U_{√b} 1 = b`, so `z = b - U_p b ≥ 0` with `U_p z = 0`; then
`(1 - p) z = z` (`nonneg_mem_one`), i.e. `p z = ½ P½(p) b = 0`. -/
theorem mem_comm_idem {p b : A} (hp : p * p = p) (hb : 0 ≤ b) (h : sq p b = sq b p) :
    b ∈ comm p := by
  have hsp : jbSqrt p = p := (jbSqrt_unique (idem_nonneg hp) (idem_nonneg hp) hp).symm
  have e1 : sq p b = JBPeirce.P1 p b := by rw [JBAll.sq, hsp, JBPeirce.P1_eq_jQ hp]
  have hle : JBPeirce.P1 p b ≤ b := by rw [← e1, h]; exact sq_le hb (idem_le_one hp)
  set z := b - JBPeirce.P1 p b with hz
  have hz0 : 0 ≤ z := sub_nonneg.2 hle
  have hP1z : JBPeirce.P1 p z = 0 := by
    rw [hz, map_sub, JBPeirce.P1_idem hp, sub_self]
  have h0 : JBPeirce.P0 (ouUnit A - p) z = 0 := by
    rw [P0_eq_P1_one_sub, sub_sub_cancel, hP1z]
  have h1 := nonneg_mem_one (idem_one_sub hp) hz0 h0
  rw [jb_sub_mul, JBAlgebra.one_mul, sub_eq_self] at h1
  have hd := JBPeirce.peirce_decomp p b
  have hzd : z = JBPeirce.Ph p b + JBPeirce.P0 p b := by
    rw [hz]; exact (eq_sub_of_add_eq' (by rw [← add_assoc]; exact hd)).symm
  rw [hzd, jb_mul_add, P0_self hp, add_zero] at h1
  have hh : p * JBPeirce.Ph p b = (1 / 2 : ℝ) • JBPeirce.Ph p b := JBPeirce.Ph_mem hp b
  rw [hh, smul_eq_zero] at h1
  have hPh : JBPeirce.Ph p b = 0 := h1.resolve_left (by norm_num)
  exact mem_comm_of_opComm_idem hp fun w => comm_of_Ph hp hPh w

/-! ## 8. `mem_comm` for `a` with at most two spectral values, in every JB-algebra -/

theorem P1_mul_self {p : A} (hp : p * p = p) (y : A) :
    JBPeirce.P1 p (y * y) = JBPeirce.P1 p y * JBPeirce.P1 p y +
      JBPeirce.P1 p (JBPeirce.Ph p y * JBPeirce.Ph p y) := by
  have hwd := JBPeirce.peirce_decomp p y
  have m1 := JBPeirce.P1_mem hp y
  have mh := JBPeirce.Ph_mem hp y
  have m0 := JBPeirce.P0_mem hp y
  set w1 := JBPeirce.P1 p y
  set wh := JBPeirce.Ph p y
  set w0 := JBPeirce.P0 p y
  have f11 : JBPeirce.P1 p (w1 * w1) = w1 * w1 :=
    JBPeirce.P1_of_mem1 (JBPeirce.peirce_one_mul_one hp m1 m1)
  have f1h : JBPeirce.P1 p (w1 * wh) = 0 :=
    JBPeirce.P1_of_memh (JBPeirce.peirce_one_mul_half hp m1 mh)
  have fh1 : JBPeirce.P1 p (wh * w1) = 0 := by rw [JBAlgebra.mul_comm]; exact f1h
  have f10 : w1 * w0 = 0 := JBPeirce.peirce_one_mul_zero hp m1 m0
  have f01 : w0 * w1 = 0 := by rw [JBAlgebra.mul_comm]; exact f10
  have f0h : JBPeirce.P1 p (w0 * wh) = 0 :=
    JBPeirce.P1_of_memh (JBPeirce.peirce_zero_mul_half hp m0 mh)
  have fh0 : JBPeirce.P1 p (wh * w0) = 0 := by rw [JBAlgebra.mul_comm]; exact f0h
  have f00 : JBPeirce.P1 p (w0 * w0) = 0 :=
    JBPeirce.P1_of_mem0 (JBPeirce.peirce_zero_mul_zero hp m0 m0)
  conv_lhs => rw [← hwd]
  simp only [JBAlgebra.add_mul, jb_mul_add, map_add, f11, f1h, fh1, f10, f01, f0h, fh0, f00,
    zero_add, add_zero]

theorem jQ_idem_self {p : A} (hp : p * p = p) : jQ p p = p := by
  rw [jQ, hp, hp, two_smul, add_sub_cancel_right]

/-- `U_p U_y p = (P₁(p) y)²` (fundamental formula). -/
theorem jQ_idem_jQ_idem {p : A} (hp : p * p = p) (y : A) :
    jQ p (jQ y p) = JBPeirce.P1 p y * JBPeirce.P1 p y := by
  have hff := jQ_jQ p y p
  rw [jQ_idem_self hp, ← JBPeirce.P1_eq_jQ hp] at hff
  rw [← hff]
  set y1 := JBPeirce.P1 p y
  have m1 := JBPeirce.P1_mem hp y
  have e1 : p * y1 = y1 := by rw [JBPeirce.mem_peirce, one_smul] at m1; exact m1
  have m11 := JBPeirce.peirce_one_mul_one hp m1 m1
  have e2 : p * (y1 * y1) = y1 * y1 := by rw [JBPeirce.mem_peirce, one_smul] at m11; exact m11
  rw [jQ, JBAlgebra.mul_comm y1 p, e1, JBAlgebra.mul_comm (y1 * y1) p, e2, two_smul,
    add_sub_cancel_right]

theorem idem_orth {p : A} (hp : p * p = p) : p * (ouUnit A - p) = 0 := by
  rw [jb_mul_sub, JBAlgebra.mul_one, hp, sub_self]

/-- **The separated two-level case**: `a = l p + m (1 - p)` with `l > m ≥ 0` and
`U_{√a} b = U_{√b} a` force `P½(p) √b = 0`, hence `b` operator-commutes with `p`.
Applying `U_p`: `U_p U_{√a} b = l U_p b = l (y₁² + U_p(y½²))` (`y = √b`), while
`U_p U_y a = l y₁² + m U_p(y½²)`; so `(l - m) U_p(y½²) = 0`. -/
theorem opComm_of_two_level {p b : A} (hp : p * p = p) {l m : ℝ} (hlm : m < l) (hm : 0 ≤ m)
    (hb : 0 ≤ b)
    (h : sq (l • p + m • (ouUnit A - p)) b = sq b (l • p + m • (ouUnit A - p))) :
    OpComm p b := by
  set q := ouUnit A - p with hqdef
  have hq : q * q = q := idem_one_sub hp
  have hpq : p * q = 0 := idem_orth hp
  have hqp : q * p = 0 := by rw [JBAlgebra.mul_comm]; exact hpq
  have hl : 0 ≤ l := hm.trans hlm.le
  set a := l • p + m • q with hadef
  set α := Real.sqrt l
  set β := Real.sqrt m
  set r := α • p + β • q with hrdef
  have hp0 : 0 ≤ p := idem_nonneg hp
  have hq0 : 0 ≤ q := idem_nonneg hq
  have ha0 : 0 ≤ a := add_nonneg (ou_smul_nonneg hl hp0) (ou_smul_nonneg hm hq0)
  have hr0 : 0 ≤ r := add_nonneg (ou_smul_nonneg (Real.sqrt_nonneg _) hp0)
    (ou_smul_nonneg (Real.sqrt_nonneg _) hq0)
  have hαα : α * α = l := Real.mul_self_sqrt hl
  have hββ : β * β = m := Real.mul_self_sqrt hm
  have hrr : r * r = a := by
    simp only [hrdef, hadef, JBAlgebra.add_mul, jb_mul_add, JBAlgebra.smul_mul, jb_mul_smul, hp, hq, hpq,
      hqp, smul_zero, add_zero, zero_add, _root_.smul_smul, hαα, hββ]
  have hsr : jbSqrt a = r := (jbSqrt_unique ha0 hr0 hrr).symm
  -- membership in `C(p)`
  have hpC : p ∈ (Ca p).carrier := self_mem_Ca p
  have hqC : q ∈ (Ca p).carrier := one_sub_mem_Ca p
  have hrC : r ∈ (Ca p).carrier :=
    (Ca p).carrier.add_mem ((Ca p).carrier.smul_mem _ hpC) ((Ca p).carrier.smul_mem _ hqC)
  have hrrC : r * r ∈ (Ca p).carrier := (Ca p).mul_mem hrC hrC
  have hppC : p * p ∈ (Ca p).carrier := (Ca p).mul_mem hpC hpC
  have hcomm : Commute (Uo p) (Uo r) := commute_Uo (opComm_Ca hpC hrC) (opComm_Ca hpC hrrC)
    (opComm_Ca hppC hrC) (opComm_Ca hppC hrrC)
  -- left-hand side
  set z := JBPeirce.P1 p b with hzdef
  have mz := JBPeirce.P1_mem hp b
  have hpz : p * z = z := by rw [JBPeirce.mem_peirce, one_smul] at mz; exact mz
  have hqz : q * z = 0 := by rw [hqdef, jb_sub_mul, JBAlgebra.one_mul, hpz, sub_self]
  have hrz : r * z = α • z := by
    rw [hrdef, JBAlgebra.add_mul, JBAlgebra.smul_mul, JBAlgebra.smul_mul, hpz, hqz, smul_zero, add_zero]
  have haz : a * z = l • z := by
    rw [hadef, JBAlgebra.add_mul, JBAlgebra.smul_mul, JBAlgebra.smul_mul, hpz, hqz, smul_zero, add_zero]
  have hjz : jQ r z = l • z := by
    rw [jQ, hrz, jb_mul_smul, hrz, hrr, haz, ← hαα]; module
  have hL : JBPeirce.P1 p (sq a b) = l • z := by
    have e : Uo p (Uo r b) = Uo r (Uo p b) := by
      rw [← mul_apply_eq_comp, hcomm.eq, mul_apply_eq_comp]
    rw [JBPeirce.P1_eq_jQ hp, JBAll.sq, hsr, ← Uo_apply, ← Uo_apply, e, Uo_apply, Uo_apply,
      ← JBPeirce.P1_eq_jQ hp, hjz]
  -- right-hand side
  set y := jbSqrt b
  have hyy : y * y = b := jbSqrt_mul_self hb
  set y1 := JBPeirce.P1 p y
  set yh := JBPeirce.Ph p y
  have hzy : z = y1 * y1 + JBPeirce.P1 p (yh * yh) := by rw [hzdef, ← hyy, P1_mul_self hp]
  have hR : JBPeirce.P1 p (sq b a) = l • (y1 * y1) + m • JBPeirce.P1 p (yh * yh) := by
    have e1 : jQ y q = b - jQ y p := by rw [hqdef, jQ_sub, jQ_one, hyy]
    rw [JBPeirce.P1_eq_jQ hp, JBAll.sq, hadef, jQ_add, jQ_smul, jQ_smul, e1, jQ_add, jQ_smul, jQ_smul,
      jQ_sub, jQ_idem_jQ_idem hp, ← JBPeirce.P1_eq_jQ hp b, ← hzdef, hzy,
      show JBPeirce.P1 p (jbSqrt b) = y1 from rfl]
    abel_nf
  have heq := h
  have key : (l - m) • JBPeirce.P1 p (yh * yh) = 0 := by
    have := congrArg (JBPeirce.P1 p) heq
    rw [hL, hR, hzy, smul_add] at this
    rw [sub_smul, ← add_right_cancel_iff (a := m • JBPeirce.P1 p (yh * yh)), sub_add_cancel,
      zero_add]
    exact (add_left_cancel this)
  have h0 : JBPeirce.P1 p (yh * yh) = 0 := by
    rw [smul_eq_zero] at key
    exact key.resolve_left (sub_ne_zero.2 hlm.ne')
  -- `y½ = 0`
  have mh := JBPeirce.Ph_mem hp y
  have mhq : yh ∈ JBPeirce.peirce q (1 / 2) := by
    rw [JBPeirce.mem_peirce] at mh ⊢
    rw [hqdef, jb_sub_mul, JBAlgebra.one_mul, mh]
    module
  have hyh : yh = 0 := half_eq_zero hq mhq (by
    rw [P0_eq_P1_one_sub, hqdef, sub_sub_cancel]; exact h0)
  have hPb : JBPeirce.Ph p b = 0 := by rw [← hyy]; exact Ph_mul hp hyh hyh
  exact fun w => comm_of_Ph hp hPb w

/-- **Van de Wetering's hard half for `a` with at most two spectral values**, in every
JB-algebra: `a = l p + m (1 - p)` (`p` idempotent, `l, m ≥ 0`), `b ≥ 0`,
`U_{√a} b = U_{√b} a` ⇒ `b` lies in the operator commutant of `C(a)`. -/
theorem mem_comm_two_level {p a b : A} (hp : p * p = p) {l m : ℝ} (hl : 0 ≤ l) (hm : 0 ≤ m)
    (ha : a = l • p + m • (ouUnit A - p)) (hb : 0 ≤ b) (h : sq a b = sq b a) : b ∈ comm a := by
  have sub : ∀ {p' : A}, p' * p' = p' → OpComm p' b → a ∈ (Ca p').carrier → b ∈ comm a :=
    fun hp' hop haC x hx => mem_comm_of_opComm_idem hp' hop x (Ca_le (Ca _) haC hx)
  rcases lt_trichotomy m l with hlt | heq | hgt
  · subst ha
    exact sub hp (opComm_of_two_level hp hlt hm hb h)
      ((Ca p).carrier.add_mem ((Ca p).carrier.smul_mem _ (self_mem_Ca p))
        ((Ca p).carrier.smul_mem _ (one_sub_mem_Ca p)))
  · have hone : (ouUnit A) * (ouUnit A) = ouUnit A := JBAlgebra.one_mul _
    refine sub hone (opComm_one_left b) ?_
    have : a = l • ouUnit A := by rw [ha, heq, ← smul_add, add_sub_cancel]
    rw [this]; exact (Ca _).carrier.smul_mem _ (Ca _).one_mem
  · have hq := idem_one_sub hp
    have ha' : a = m • (ouUnit A - p) + l • (ouUnit A - (ouUnit A - p)) := by
      rw [ha, sub_sub_cancel, add_comm]
    rw [ha'] at h
    refine sub hq (opComm_of_two_level hq hgt hl hb h) ?_
    rw [ha']
    exact (Ca _).carrier.add_mem ((Ca _).carrier.smul_mem _ (self_mem_Ca _))
      ((Ca _).carrier.smul_mem _ (one_sub_mem_Ca _))

end Idem

end Papers.SEA.JBComm
