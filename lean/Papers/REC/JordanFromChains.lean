import Papers.REC.JordanSymmetry

/-!
# The 9.43 part of Alfsen–Shultz from chain density

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707, `short.tex` §5.4, `prop:is-JB-algebra` (REC 121).

`AlfsenShultzJordanTransplant` (JordanSymmetry.lean) asks that the family of
compressions of REC 121 makes `W` a JB-algebra with `e_i * w = ½(w + (U_i − U_{c i}) w)`,
given that the span of the `e_i` is norm dense.  Here that conclusion is *proved*
(`jb_of_chainDense`) when the density hypothesis is replaced by **chain density**
(`ChainDense`): every `w` is a norm limit of chain combinations
`λ₀ 1 + Σ_k α_k e_{j_k}` with `α_k ≥ 0`, `e_{j_1} ≥ e_{j_2} ≥ …`, and
`U_{j_k} U_{c j_{k'}} = U_{c j_{k'}} U_{j_k}` for the members of each chain (research note
`docs/research/as943-transplant.md` with its Review: (G1) and (G2) bundled).
Directed completeness is not used.

## Route

1. Order lemmas for nested members `e_j ≤ e_i` (`Fam.nA`–`Fam.nD`): `U_j U_{ci} = 0`,
   `U_{ci} U_j = 0`, `U_i U_j = U_j` (kernel condition) and `U_j U_i = U_j` (from
   `e^{tD_i} = 1 + (e^t − 1) U_i + (e^{−t} − 1) U_{ci}` positive, `Fam.expPos`).
2. `T_i := ½(1 + U_i − U_{ci})`: `T_i 1 = e_i`, symmetry `T_i e_j = T_j e_i`
   (`jordan_symmetry`), `T_i e_j = e_j` for `e_j ≤ e_i`, `‖T_i‖ ≤ 1`, and `T_i, T_j`
   commute for chain members.
3. `a ↦ T_a` on finitely supported combinations of `1, e_i`: symmetric, hence it factors
   through the span (the dependency is killed by pairing and density); on chains
   `‖T_a‖ ≤ 3‖a‖` (two extreme layer maps `U_{c j_1}`, `U_{j_n}`, after dropping degenerate
   members `e = 1` at the top and `e = 0` at the bottom, `Fam.normalize`); by symmetry and
   density `‖T_a‖ ≤ 3‖a‖` on the span; extend (`LinearMap.extendOfNorm`).
4. Commutativity, unit and bilinearity by density; the Jordan identity from
   `a * a = Σ (λ_k² − λ_{k−1}²) e_{j_k}` on chains (`T_a`, `T_{a*a}` are combinations of
   commuting `T_{j_k}`) and closedness; `0 ≤ a * a ≤ 1` on chains from the same formula
   and the layer bounds, then by rescaled approximation.
-/

set_option linter.unusedSectionVars false

open Theses.B.Eff
open NormedSpace Filter Topology

namespace Papers.REC

universe u

-- `ChainDense` is defined in `Papers/REC/Reconstruction.lean`.

namespace JFC

attribute [local instance] ousNormedAddCommGroup ousNormedSpace

/-! ## Generalities -/

section Order

variable {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]

theorem le_of_smul_le_smul' {p : W} (hp : 0 ≤ p) (hp0 : p ≠ 0) {r s : ℝ}
    (h : r • p ≤ s • p) : r ≤ s := by
  by_contra hlt
  push Not at hlt
  have hpos : 0 < r - s := sub_pos.2 hlt
  have h1 : (r - s) • p ≤ 0 := by rw [sub_smul]; exact sub_nonpos.2 h
  have h2 := ou_smul_le_smul (inv_pos.2 hpos).le h1
  rw [_root_.smul_smul, inv_mul_cancel₀ hpos.ne', one_smul, smul_zero] at h2
  exact hp0 (le_antisymm h2 hp)

theorem posmono {Φ : W →ₗ[ℝ] W} (hΦ : ∀ v, 0 ≤ v → 0 ≤ Φ v) {v w : W} (h : v ≤ w) :
    Φ v ≤ Φ w := by
  have := hΦ _ (sub_nonneg.2 h)
  rwa [map_sub, sub_nonneg] at this

theorem linext_nonneg {Φ Ψ : W →ₗ[ℝ] W} (h : ∀ v, 0 ≤ v → Φ v = Ψ v) : Φ = Ψ := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨p, q, hp, hq, rfl⟩ := ou_eq_sub_of_nonneg v
  rw [map_sub, map_sub, h p hp, h q hq]

variable [IsOUS W]

theorem pos_eq_zero {Φ : W →ₗ[ℝ] W} (hΦ : ∀ v, 0 ≤ v → 0 ≤ Φ v) (h1 : Φ (ouUnit W) ≤ 0)
    (v : W) : Φ v = 0 := by
  have h0 : Φ (ouUnit W) = 0 := le_antisymm h1 (hΦ _ ou_unit_nonneg)
  have := positive_bound Φ hΦ v
  rw [h0, ousNorm_zero', zero_mul] at this
  exact IsOUS.norm_eq_zero _ (le_antisymm this (ousNorm_nonneg_rc _))

end Order

theorem expIdem {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] {p : 𝔸}
    (hp : IsIdempotentElem p) (s : ℝ) : exp (s • p) = 1 + (Real.exp s - 1) • p := by
  have h1 := exp_series_hasSum_exp' (𝕂 := ℝ) (s • p)
  have hr := exp_series_hasSum_exp' (𝕂 := ℝ) s
  rw [← Real.exp_eq_exp_ℝ] at hr
  have h2 : HasSum (fun n : ℕ => (((n.factorial : ℝ))⁻¹ • s ^ n) • p +
      (if n = 0 then (1 - p) else 0)) (Real.exp s • p + (1 - p)) :=
    (hr.smul_const p).add (hasSum_ite_eq 0 (1 - p))
  have e : (fun n : ℕ => (((n.factorial : ℝ))⁻¹) • (s • p) ^ n) =
      fun n => (((n.factorial : ℝ))⁻¹ • s ^ n) • p + (if n = 0 then (1 - p) else 0) := by
    funext n
    rcases n with _ | n
    · simp
    · rw [smul_pow, hp.pow_succ_eq n, _root_.smul_smul, ite_eq_right_iff.2 fun h => absurd h (Nat.succ_ne_zero n), add_zero,
        smul_eq_mul]
  rw [e] at h1
  rw [h1.unique h2, sub_smul, one_smul]; abel

/-! ## The generic chain sums `μ₀ u + Σ_k (μ_{k+1} − μ_k) q_k` -/

section SV

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- `μ₀ u + Σ_k (μ_{k+1} − μ_k) q_k`: a chain element with the "spectral values" `μ`. -/
def sv (u : V) {n : ℕ} (μ : Fin (n + 1) → ℝ) (q : Fin n → V) : V :=
  μ 0 • u + ∑ k : Fin n, (μ k.succ - μ k.castSucc) • q k

theorem sv_zero (u : V) (μ : Fin 1 → ℝ) (q : Fin 0 → V) : sv u μ q = μ 0 • u := by
  simp [sv]

theorem sv_cons (u : V) {n : ℕ} (μ : Fin (n + 2) → ℝ) (q : Fin (n + 1) → V) :
    sv u μ q = μ 0 • (u - q 0) + sv (q 0) (Fin.tail μ) (Fin.tail q) := by
  simp only [sv, Fin.sum_univ_succ, Fin.tail, Fin.castSucc_zero, Fin.castSucc_succ]
  module

theorem sv_last (u : V) {n : ℕ} (μ : Fin (n + 2) → ℝ) (q : Fin (n + 1) → V) :
    sv u μ q = sv u (Fin.init μ) (Fin.init q) +
      (μ (Fin.last (n + 1)) - μ (Fin.last n).castSucc) • q (Fin.last n) := by
  simp only [sv, Fin.sum_univ_castSucc, Fin.init, Fin.castSucc_zero, Fin.succ_last,
    Fin.castSucc_succ]
  abel

theorem sv_const (u : V) {n : ℕ} (r : ℝ) (q : Fin n → V) : sv u (fun _ => r) q = r • u := by
  simp [sv]

theorem sv_sub (u : V) {n : ℕ} (μ ν : Fin (n + 1) → ℝ) (q : Fin n → V) :
    sv u (fun m => μ m - ν m) q = sv u μ q - sv u ν q := by
  have h : ∀ k : Fin n, ((μ k.succ - ν k.succ) - (μ k.castSucc - ν k.castSucc)) • q k =
      (μ k.succ - μ k.castSucc) • q k - (ν k.succ - ν k.castSucc) • q k := fun k => by module
  simp only [sv, h, Finset.sum_sub_distrib, sub_smul]
  abel

theorem sv_smul (u : V) {n : ℕ} (t : ℝ) (μ : Fin (n + 1) → ℝ) (q : Fin n → V) :
    sv u (fun m => t * μ m) q = t • sv u μ q := by
  simp only [sv, smul_add, Finset.smul_sum, _root_.smul_smul, mul_sub]

theorem map_sv {V' : Type*} [AddCommGroup V'] [Module ℝ V'] {F : Type*} [FunLike F V V']
    [LinearMapClass F ℝ V V'] (f : F) (u : V) {n : ℕ} (μ : Fin (n + 1) → ℝ) (q : Fin n → V) :
    f (sv u μ q) = sv (f u) μ (fun k => f (q k)) := by
  simp [sv, map_add, map_sum, map_smul]

theorem tele : ∀ {n : ℕ} (μ : Fin (n + 1) → ℝ),
    μ 0 + ∑ k : Fin n, (μ k.succ - μ k.castSucc) = μ (Fin.last n)
  | 0, μ => by simp
  | n + 1, μ => by
    have ih := tele (n := n) (fun m => μ m.castSucc)
    rw [Fin.sum_univ_castSucc, ← add_assoc]
    simp only [Fin.castSucc_zero, ← Fin.castSucc_succ] at ih ⊢
    rw [ih, Fin.succ_last]; ring

theorem sv_const_q (x : V) {n : ℕ} (μ : Fin (n + 1) → ℝ) :
    sv x μ (fun _ => x) = μ (Fin.last n) • x := by
  rw [sv, ← Finset.sum_smul, ← add_smul, tele]

theorem sv_zero_q (x : V) {n : ℕ} (μ : Fin (n + 1) → ℝ) :
    sv x μ (fun _ => (0 : V)) = μ 0 • x := by
  simp [sv]

end SV

theorem sv_nonneg {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W]
    [OrderUnitSpace W] : ∀ {n : ℕ} (u : W) (μ : Fin (n + 1) → ℝ) (q : Fin n → W),
    (∀ m, 0 ≤ μ m) → 0 ≤ u → (∀ k, q k ≤ u) → (∀ k, 0 ≤ q k) →
    (∀ k k' : Fin n, k ≤ k' → q k' ≤ q k) → 0 ≤ sv u μ q
  | 0, u, μ, q, hμ, hu, _, _, _ => by rw [sv_zero]; exact ou_smul_nonneg (hμ 0) hu
  | n + 1, u, μ, q, hμ, hu, hqu, hq0, hqa => by
    rw [sv_cons]
    refine add_nonneg (ou_smul_nonneg (hμ 0) (sub_nonneg.2 (hqu 0))) ?_
    exact sv_nonneg (q 0) (Fin.tail μ) (Fin.tail q) (fun m => hμ _) (hq0 0)
      (fun k => hqa 0 k.succ (Fin.zero_le _)) (fun k => hq0 _)
      (fun k k' hk => hqa _ _ (Fin.succ_le_succ_iff.2 hk))

/-! ## The family -/

/-- The family of compressions of `AlfsenShultzJordanFromDerivations`, bundled. -/
structure Fam (W : Type u) [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]
    (ι : Type u) where
  e : ι → W
  U : ι → W →ₗ[ℝ] W
  c : ι → ι
  hB : IsBanachOUS W
  inj : Function.Injective e
  hc : ∀ i, e (c i) = ouUnit W - e i
  hU : ∀ i, (∀ w, 0 ≤ w → 0 ≤ U i w) ∧ U i (ouUnit W) = e i ∧ U i ∘ₗ U i = U i ∧
    U i ∘ₗ U (c i) = 0
  hker : ∀ i w, 0 ≤ w → (U i w = 0 ↔ U (c i) w = w)
  hD : ∀ i, IsOrderDerivation W (U i - U (c i))

namespace Fam

variable {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]
  [IsOUS W] [CompleteSpace W] {ι : Type u} (P : Fam W ι)

theorem cc (i : ι) : P.c (P.c i) = i := P.inj (by rw [P.hc, P.hc]; abel)

theorem pos (i : ι) {w : W} (hw : 0 ≤ w) : 0 ≤ P.U i w := (P.hU i).1 w hw

theorem U1 (i : ι) : P.U i (ouUnit W) = P.e i := (P.hU i).2.1

theorem UU (i : ι) (w : W) : P.U i (P.U i w) = P.U i w := LinearMap.congr_fun (P.hU i).2.2.1 w

theorem Uc (i : ι) (w : W) : P.U i (P.U (P.c i) w) = 0 := LinearMap.congr_fun (P.hU i).2.2.2 w

theorem cU (i : ι) (w : W) : P.U (P.c i) (P.U i w) = 0 := by
  have := P.Uc (P.c i) w; rwa [P.cc] at this

theorem mono (i : ι) {v w : W} (h : v ≤ w) : P.U i v ≤ P.U i w :=
  posmono (fun _ hv => P.pos i hv) h

theorem e_nonneg (i : ι) : 0 ≤ P.e i := P.U1 i ▸ P.pos i ou_unit_nonneg

theorem e_le_one (i : ι) : P.e i ≤ ouUnit W := by
  have := P.e_nonneg (P.c i); rw [P.hc] at this; exact sub_nonneg.1 this

theorem e_add_ec (i : ι) : P.e i + P.e (P.c i) = ouUnit W := by rw [P.hc]; abel

theorem ec_le {i j : ι} (h : P.e j ≤ P.e i) : P.e (P.c i) ≤ P.e (P.c j) := by
  rw [P.hc, P.hc]; exact sub_le_sub_left h _

/-! ### Nested members -/

variable {i j : ι}

theorem nA (h : P.e j ≤ P.e i) (w : W) : P.U j (P.U (P.c i) w) = 0 := by
  refine pos_eq_zero (Φ := P.U j ∘ₗ P.U (P.c i)) (fun v hv => P.pos j (P.pos _ hv)) ?_ w
  show P.U j (P.U (P.c i) (ouUnit W)) ≤ 0
  rw [P.U1]
  calc P.U j (P.e (P.c i)) ≤ P.U j (P.e (P.c j)) := P.mono j (P.ec_le h)
    _ = 0 := by rw [← P.U1 (P.c j), P.Uc]

theorem nB (h : P.e j ≤ P.e i) (w : W) : P.U (P.c i) (P.U j w) = 0 := by
  refine pos_eq_zero (Φ := P.U (P.c i) ∘ₗ P.U j) (fun v hv => P.pos _ (P.pos j hv)) ?_ w
  show P.U (P.c i) (P.U j (ouUnit W)) ≤ 0
  rw [P.U1]
  calc P.U (P.c i) (P.e j) ≤ P.U (P.c i) (P.e i) := P.mono _ h
    _ = 0 := by rw [← P.U1 i, P.cU]

theorem nC (h : P.e j ≤ P.e i) (w : W) : P.U i (P.U j w) = P.U j w := by
  have := linext_nonneg (Φ := P.U i ∘ₗ P.U j) (Ψ := P.U j) (fun v hv => by
    show P.U i (P.U j v) = P.U j v
    have h0 := (P.hker (P.c i) (P.U j v) (P.pos j hv)).1 (P.nB h v)
    rwa [P.cc] at h0)
  exact LinearMap.congr_fun this w

/-- `U_i` as a bounded operator. -/
noncomputable def UL (i : ι) : W →L[ℝ] W :=
  (P.U i).mkContinuous (ousNorm W (P.U i (ouUnit W))) (positive_bound _ fun _ hv => P.pos i hv)

theorem UL_apply (i : ι) (v : W) : P.UL i v = P.U i v := rfl

/-- `e^{tD_i} = 1 + (e^t − 1) U_i + (e^{−t} − 1) U_{c i}`, positive. -/
theorem expPos (i : ι) (t : ℝ) {v : W} (hv : 0 ≤ v) :
    0 ≤ v + (Real.exp t - 1) • P.U i v + (Real.exp (-t) - 1) • P.U (P.c i) v := by
  let _ : NormedAlgebra ℚ (W →L[ℝ] W) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hexp := (P.hD i).expIn (δL := P.UL i - P.UL (P.c i)) (fun w => rfl) t v hv
  have hid : ∀ k, IsIdempotentElem (P.UL k) := fun k =>
    ContinuousLinearMap.ext fun w => P.UU k w
  have hPQ' : P.UL i * P.UL (P.c i) = P.UL (P.c i) * P.UL i := by
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [mul_apply_eq_comp, UL_apply]
    rw [P.Uc, P.cU]
  have hPQ : Commute (P.UL i) (P.UL (P.c i)) := hPQ'
  have hcomm : Commute (t • P.UL i) ((-t) • P.UL (P.c i)) :=
    (hPQ.smul_left t).smul_right (-t)
  have e1 : t • (P.UL i - P.UL (P.c i)) = t • P.UL i + (-t) • P.UL (P.c i) := by
    rw [smul_sub, neg_smul, sub_eq_add_neg]
  rw [e1, exp_add_of_commute hcomm, expIdem (hid i), expIdem (hid (P.c i))] at hexp
  have e2 : ((1 + (Real.exp t - 1) • P.UL i) * (1 + (Real.exp (-t) - 1) • P.UL (P.c i))) v =
      v + (Real.exp t - 1) • P.U i v + (Real.exp (-t) - 1) • P.U (P.c i) v := by
    simp only [mul_apply_eq_comp, _root_.add_apply,
      one_apply_eq_self, _root_.smul_apply, UL_apply, map_add,
      map_smul, P.Uc, smul_zero, add_zero]
  rw [e2] at hexp
  exact hexp

theorem nD (h : P.e j ≤ P.e i) (w : W) : P.U j (P.U i w) = P.U j w := by
  have hΦ : ∀ v, 0 ≤ v → 0 ≤ (P.U j - P.U j ∘ₗ P.U i) v := by
    intro v hv
    show 0 ≤ P.U j v - P.U j (P.U i v)
    have hy : 0 ≤ P.U j (P.U i v) := P.pos j (P.pos i hv)
    have key : ∀ s : ℝ, 0 < s → 0 ≤ (P.U j v - P.U j (P.U i v)) + s • P.U j (P.U i v) := by
      intro s hs
      have := P.pos j (P.expPos i (Real.log s) hv)
      rw [map_add, map_add, map_smul, map_smul, P.nA h, smul_zero, add_zero,
        Real.exp_log hs] at this
      have e : (P.U j v - P.U j (P.U i v)) + s • P.U j (P.U i v) =
          P.U j v + (s - 1) • P.U j (P.U i v) := by rw [sub_smul, one_smul]; abel
      rw [e]; exact this
    refine IsOUS.cone_closed _ fun ε hε =>
      ⟨_, key (ε / (ousNorm W (P.U j (P.U i v)) + 1)) (by
        have := ousNorm_nonneg_rc (P.U j (P.U i v)); positivity), ?_⟩
    rw [sub_add_cancel_left, ousNorm_neg]
    have h0 := ousNorm_nonneg_rc (P.U j (P.U i v))
    calc ousNorm W ((ε / (ousNorm W (P.U j (P.U i v)) + 1)) • P.U j (P.U i v))
        ≤ |ε / (ousNorm W (P.U j (P.U i v)) + 1)| * ousNorm W (P.U j (P.U i v)) :=
          ousNorm_smul_le _ _
      _ < ε := by
        rw [abs_of_pos (by positivity), div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  have h1 : (P.U j - P.U j ∘ₗ P.U i) (ouUnit W) ≤ 0 := by
    show P.U j (ouUnit W) - P.U j (P.U i (ouUnit W)) ≤ 0
    have : P.U i (ouUnit W) = ouUnit W - P.e (P.c i) := by rw [P.U1, P.hc]; abel
    rw [this, map_sub, ← P.U1 (P.c i), P.nA h, sub_zero, sub_self]
  have := pos_eq_zero hΦ h1 w
  rw [LinearMap.sub_apply, LinearMap.comp_apply, sub_eq_zero] at this
  exact this.symm

/-! ### The operators `T_i = ½(1 + U_i − U_{c i})` -/

/-- `T_i := ½(1 + U_i − U_{c i})`. -/
noncomputable def TL (i : ι) : W →L[ℝ] W := (2⁻¹ : ℝ) • (1 + (P.UL i - P.UL (P.c i)))

theorem TL_apply (i : ι) (v : W) :
    P.TL i v = (2⁻¹ : ℝ) • (v + (P.U i v - P.U (P.c i) v)) := rfl

theorem TL_one (i : ι) : P.TL i (ouUnit W) = P.e i := by
  rw [TL_apply, P.U1, P.U1, P.hc]
  have : ouUnit W + (P.e i - (ouUnit W - P.e i)) = (2 : ℝ) • P.e i := by rw [two_smul]; abel
  rw [this, _root_.smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem TL_sym (i j : ι) : P.TL i (P.e j) = P.TL j (P.e i) := by
  rw [TL_apply, TL_apply]
  have := jordan_symmetry P.hB P.e P.U P.c P.inj P.hc P.hU P.hD i j
  simp only [LinearMap.sub_apply] at this
  rw [this]

theorem TL_nest (h : P.e j ≤ P.e i) : P.TL i (P.e j) = P.e j := by
  rw [TL_apply, ← P.U1 j, P.nC h, P.nB h, sub_zero, ← two_smul ℝ, _root_.smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul]

theorem TL_norm_le (i : ι) (v : W) : ‖P.TL i v‖ ≤ ‖v‖ := by
  rw [norm_eq_ousNorm, norm_eq_ousNorm]
  obtain ⟨h1, h2⟩ := ousNorm_bounds_le v
  have hr : 0 ≤ ousNorm W v := ousNorm_nonneg_rc v
  have a1 := P.mono i h1
  have a2 := P.mono i h2
  have b1 := P.mono (P.c i) h1
  have b2 := P.mono (P.c i) h2
  simp only [map_neg, map_smul, P.U1] at a1 a2 b1 b2
  have hs : ousNorm W v • ouUnit W = ousNorm W v • P.e i + ousNorm W v • P.e (P.c i) := by
    rw [← smul_add, P.e_add_ec]
  refine ousNorm_le_rc hr ?_ ?_
  · rw [TL_apply, ← sub_nonneg]
    have e : (2⁻¹ : ℝ) • (v + (P.U i v - P.U (P.c i) v)) - -(ousNorm W v • ouUnit W) =
        (2⁻¹ : ℝ) • ((v + ousNorm W v • ouUnit W) + (P.U i v + ousNorm W v • P.e i) +
          (ousNorm W v • P.e (P.c i) - P.U (P.c i) v)) := by
      rw [hs]; module
    rw [e]
    refine ou_smul_nonneg (by norm_num) (add_nonneg (add_nonneg ?_ ?_) (sub_nonneg.2 b2))
    · have := sub_nonneg.2 h1; rwa [sub_neg_eq_add] at this
    · have := sub_nonneg.2 a1; rwa [sub_neg_eq_add] at this
  · rw [TL_apply, ← sub_nonneg]
    have e : ousNorm W v • ouUnit W - (2⁻¹ : ℝ) • (v + (P.U i v - P.U (P.c i) v)) =
        (2⁻¹ : ℝ) • ((ousNorm W v • ouUnit W - v) + (ousNorm W v • P.e i - P.U i v) +
          (P.U (P.c i) v + ousNorm W v • P.e (P.c i))) := by
      rw [hs]; module
    rw [e]
    refine ou_smul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 a2)) ?_)
    have := sub_nonneg.2 b1; rwa [sub_neg_eq_add] at this

theorem TL_opnorm_le (i : ι) : ‖P.TL i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]; exact P.TL_norm_le i v

theorem TL_comm (h : P.e j ≤ P.e i)
    (hg : P.U i ∘ₗ P.U (P.c j) = P.U (P.c j) ∘ₗ P.U i) :
    P.TL i * P.TL j = P.TL j * P.TL i := by
  have hg' : ∀ w, P.U i (P.U (P.c j) w) = P.U (P.c j) (P.U i w) := fun w =>
    LinearMap.congr_fun hg w
  have h' := P.ec_le h
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [mul_apply_eq_comp, TL_apply, map_add, map_sub, map_smul, P.nC h,
    P.nB h, P.nD h, P.nA h, hg', P.nC h', P.nD h', sub_zero]
  module

/-! ### Chains -/

/-- A chain in "spectral" form: values `μ` increasing, members decreasing, and the
compatibility (G2) of its members. -/
def Chain {n : ℕ} (μ : Fin (n + 1) → ℝ) (j : Fin n → ι) : Prop :=
  (∀ k : Fin n, μ k.castSucc ≤ μ k.succ) ∧ (∀ k k' : Fin n, k ≤ k' → P.e (j k') ≤ P.e (j k)) ∧
    (∀ k k' : Fin n, P.U (j k) ∘ₗ P.U (P.c (j k')) = P.U (P.c (j k')) ∘ₗ P.U (j k))

/-- The vector of a chain, `μ₀ 1 + Σ_k (μ_{k+1} − μ_k) e_{j_k}`. -/
def cv {n : ℕ} (μ : Fin (n + 1) → ℝ) (j : Fin n → ι) : W := sv (ouUnit W) μ (fun k => P.e (j k))

variable {P}

theorem Chain.mono {n : ℕ} {μ : Fin (n + 1) → ℝ} {j : Fin n → ι} (hc : P.Chain μ j) :
    Monotone μ := Fin.monotone_iff_le_succ.2 hc.1

theorem Chain.tail {n : ℕ} {μ : Fin (n + 2) → ℝ} {j : Fin (n + 1) → ι} (hc : P.Chain μ j) :
    P.Chain (Fin.tail μ) (Fin.tail j) :=
  ⟨fun k => hc.1 k.succ, fun _ _ hk => hc.2.1 _ _ (Fin.succ_le_succ_iff.2 hk),
    fun _ _ => hc.2.2 _ _⟩

theorem Chain.init {n : ℕ} {μ : Fin (n + 2) → ℝ} {j : Fin (n + 1) → ι} (hc : P.Chain μ j) :
    P.Chain (Fin.init μ) (Fin.init j) :=
  ⟨fun k => hc.1 k.castSucc, fun _ _ hk => hc.2.1 _ _ (Fin.castSucc_le_castSucc_iff.2 hk),
    fun _ _ => hc.2.2 _ _⟩

variable (P)

theorem cv_drop_first {n : ℕ} (μ : Fin (n + 2) → ℝ) (j : Fin (n + 1) → ι)
    (h0 : P.e (j 0) = ouUnit W) : P.cv μ j = P.cv (Fin.tail μ) (Fin.tail j) := by
  rw [cv, sv_cons]
  simp only [h0, sub_self, smul_zero, zero_add]
  rfl

theorem cv_drop_last {n : ℕ} (μ : Fin (n + 2) → ℝ) (j : Fin (n + 1) → ι)
    (hL : P.e (j (Fin.last n)) = 0) : P.cv μ j = P.cv (Fin.init μ) (Fin.init j) := by
  rw [cv, sv_last, hL, smul_zero, add_zero]
  rfl

theorem U_bot {n : ℕ} (μ : Fin (n + 2) → ℝ) (j : Fin (n + 1) → ι) (hc : P.Chain μ j) :
    P.U (P.c (j 0)) (P.cv μ j) = μ 0 • P.e (P.c (j 0)) := by
  rw [cv, map_sv, P.U1]
  have : (fun k => P.U (P.c (j 0)) (P.e (j k))) = fun _ => (0 : W) := by
    funext k
    rw [← P.U1 (j k), P.nB (hc.2.1 0 k (Fin.zero_le _))]
  rw [this, sv_zero_q]

theorem U_top {n : ℕ} (μ : Fin (n + 2) → ℝ) (j : Fin (n + 1) → ι) (hc : P.Chain μ j) :
    P.U (j (Fin.last n)) (P.cv μ j) = μ (Fin.last (n + 1)) • P.e (j (Fin.last n)) := by
  rw [cv, map_sv, P.U1]
  have : (fun k => P.U (j (Fin.last n)) (P.e (j k))) = fun _ => P.e (j (Fin.last n)) := by
    funext k
    rw [← P.U1 (j k), P.nD (hc.2.1 k _ (Fin.le_last k)), P.U1]
  rw [this, sv_const_q]

theorem TL_below {n : ℕ} (μ : Fin (n + 1) → ℝ) (j : Fin n → ι) (i : ι)
    (hi : ∀ k, P.e i ≤ P.e (j k)) : P.TL i (P.cv μ j) = μ (Fin.last n) • P.e i := by
  rw [cv, map_sv, P.TL_one]
  have : (fun k => P.TL i (P.e (j k))) = fun _ => P.e i := by
    funext k
    rw [P.TL_sym, P.TL_nest (hi k)]
  rw [this, sv_const_q]

/-- Spectral bounds: the order bounds of the vector bound all the values. -/
def SpecBound {n : ℕ} (μ : Fin (n + 1) → ℝ) (a : W) : Prop :=
  ∀ r s : ℝ, r • ouUnit W ≤ a → a ≤ s • ouUnit W → ∀ m, r ≤ μ m ∧ μ m ≤ s

/-- Dropping degenerate members (`e = 1` first, `e = 0` last), every chain vector is the
vector of a chain whose values are bounded by the order bounds of the vector. -/
theorem normalize (hne : ouUnit W ≠ 0) : ∀ (n : ℕ) (μ : Fin (n + 1) → ℝ) (j : Fin n → ι),
    P.Chain μ j → ∃ (n' : ℕ) (μ' : Fin (n' + 1) → ℝ) (j' : Fin n' → ι),
      P.Chain μ' j' ∧ P.cv μ' j' = P.cv μ j ∧ SpecBound μ' (P.cv μ j) := by
  intro n
  induction n with
  | zero =>
    intro μ j hc
    refine ⟨0, μ, j, hc, rfl, fun r s hr hs m => ?_⟩
    have hm : m = 0 := Fin.fin_one_eq_zero m
    subst hm
    have ha : P.cv μ j = μ 0 • ouUnit W := sv_zero _ _ _
    rw [ha] at hr hs
    exact ⟨le_of_smul_le_smul' ou_unit_nonneg hne hr, le_of_smul_le_smul' ou_unit_nonneg hne hs⟩
  | succ n ih =>
    intro μ j hc
    by_cases h0 : P.e (j 0) = ouUnit W
    · obtain ⟨n', μ', j', hc', he, hb⟩ := ih (Fin.tail μ) (Fin.tail j) hc.tail
      have := P.cv_drop_first μ j h0
      exact ⟨n', μ', j', hc', he.trans this.symm, this ▸ hb⟩
    by_cases hL : P.e (j (Fin.last n)) = 0
    · obtain ⟨n', μ', j', hc', he, hb⟩ := ih (Fin.init μ) (Fin.init j) hc.init
      have := P.cv_drop_last μ j hL
      exact ⟨n', μ', j', hc', he.trans this.symm, this ▸ hb⟩
    refine ⟨n + 1, μ, j, hc, rfl, fun r s hr hs m => ?_⟩
    have hb : r ≤ μ 0 := by
      have := P.mono (P.c (j 0)) hr
      rw [map_smul, P.U1, P.U_bot μ j hc] at this
      refine le_of_smul_le_smul' (P.e_nonneg _) ?_ this
      rw [P.hc]; exact sub_ne_zero.2 (Ne.symm h0)
    have ht : μ (Fin.last (n + 1)) ≤ s := by
      have := P.mono (j (Fin.last n)) hs
      rw [map_smul, P.U1, P.U_top μ j hc] at this
      exact le_of_smul_le_smul' (P.e_nonneg _) hL this
    exact ⟨hb.trans (hc.mono (Fin.zero_le m)), (hc.mono (Fin.le_last m)).trans ht⟩

/-- `ChainDense` in the spectral form. -/
theorem dense_chain (hd : ChainDense W ι P.e P.U P.c) (w : W) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (μ : Fin (n + 1) → ℝ) (j : Fin n → ι), P.Chain μ j ∧ ‖w - P.cv μ j‖ < ε := by
  obtain ⟨n, l0, α, j, hα, hnest, hg, hlt⟩ := hd w ε hε
  let α' : ℕ → ℝ := fun i => if h : i < n then α ⟨i, h⟩ else 0
  let μ : Fin (n + 1) → ℝ := fun m => l0 + ∑ i ∈ Finset.range m, α' i
  have hμ : ∀ k : Fin n, μ k.succ - μ k.castSucc = α k := by
    intro k
    simp only [μ, Fin.val_succ, Fin.val_castSucc, Finset.sum_range_succ, α', k.isLt, ↓reduceDIte]
    ring
  refine ⟨n, μ, j, ⟨fun k => by linarith [hμ k, hα k], hnest, hg⟩, ?_⟩
  have : P.cv μ j = l0 • ouUnit W + ∑ k, α k • P.e (j k) := by
    simp only [cv, sv, hμ]
    simp [μ]
  rw [this]; exact hlt

/-! ### The product on the span and its extension -/

/-- Generators: `none ↦ 1`, `some i ↦ e_i`. -/
def gG : Option ι → W
  | none => ouUnit W
  | some i => P.e i

/-- `none ↦ id`, `some i ↦ T_i`. -/
noncomputable def TG : Option ι → (W →L[ℝ] W)
  | none => 1
  | some i => P.TL i

theorem TG_one (x : Option ι) : P.TG x (ouUnit W) = P.gG x := by
  cases x with
  | none => rfl
  | some i => exact P.TL_one i

theorem TG_sym (x y : Option ι) : P.TG x (P.gG y) = P.TG y (P.gG x) := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some j => exact (P.TL_one j).symm
  | some i =>
    cases y with
    | none => exact P.TL_one i
    | some j => exact P.TL_sym i j

/-- Formal combinations of generators to vectors. -/
noncomputable def Fm : (Option ι →₀ ℝ) →ₗ[ℝ] W := Finsupp.linearCombination ℝ P.gG

/-- Formal combinations of generators to operators `Σ λ T`. -/
noncomputable def Hm : (Option ι →₀ ℝ) →ₗ[ℝ] (W →L[ℝ] W) := Finsupp.linearCombination ℝ P.TG

theorem Hm_sym (f h : Option ι →₀ ℝ) : P.Hm f (P.Fm h) = P.Hm h (P.Fm f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f1 f2 ih1 ih2 => rw [map_add, map_add, _root_.add_apply, ih1, ih2, map_add]
  | single x a =>
    induction h using Finsupp.induction_linear with
    | zero => simp
    | add h1 h2 ih1 ih2 =>
      rw [map_add, map_add, map_add, _root_.add_apply, ih1, ih2]
    | single y b =>
      simp only [Hm, Fm, Finsupp.linearCombination_single, _root_.smul_apply,
        map_smul]
      rw [P.TG_sym, smul_comm]

theorem Hm_one (f : Option ι →₀ ℝ) : P.Hm f (ouUnit W) = P.Fm f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f1 f2 ih1 ih2 => rw [map_add, map_add, _root_.add_apply, ih1, ih2]
  | single x a =>
    simp only [Hm, Fm, Finsupp.linearCombination_single, _root_.smul_apply]
    rw [P.TG_one]

/-- The formal combination of a chain. -/
noncomputable def hsv {n : ℕ} (μ : Fin (n + 1) → ℝ) (j : Fin n → ι) : Option ι →₀ ℝ :=
  sv (Finsupp.single none 1) μ (fun k => Finsupp.single (some (j k)) 1)

theorem Fm_hsv {n : ℕ} (μ : Fin (n + 1) → ℝ) (j : Fin n → ι) :
    P.Fm (hsv μ j) = P.cv μ j := by
  rw [hsv, map_sv]
  simp [Fm, gG, cv]

theorem Hm_hsv {n : ℕ} (μ : Fin (n + 1) → ℝ) (j : Fin n → ι) :
    P.Hm (hsv μ j) = sv 1 μ (fun k => P.TL (j k)) := by
  rw [hsv, map_sv]
  simp [Hm, TG]

theorem sv_commute {n : ℕ} (μ ν : Fin (n + 1) → ℝ) (T : Fin n → (W →L[ℝ] W))
    (hT : ∀ k k', Commute (T k) (T k')) : Commute (sv 1 μ T) (sv 1 ν T) := by
  have h1 : ∀ (x : W →L[ℝ] W) (r : ℝ), Commute (r • (1 : W →L[ℝ] W)) x := fun x r =>
    (Commute.one_left x).smul_left r
  have hk : ∀ k, Commute (T k) (sv 1 ν T) := fun k =>
    Commute.add_right (h1 _ _).symm
      (Commute.sum_right _ _ _ fun k' _ => (hT k k').smul_right _)
  exact Commute.add_left (h1 _ _) (Commute.sum_left _ _ _ fun k _ => (hk k).smul_left _)

theorem chain_TL_comm {n : ℕ} {μ : Fin (n + 1) → ℝ} {j : Fin n → ι} (hc : P.Chain μ j)
    (k k' : Fin n) : Commute (P.TL (j k)) (P.TL (j k')) := by
  rcases le_total k k' with h | h
  · exact P.TL_comm (hc.2.1 k k' h) (hc.2.2 k k')
  · exact (P.TL_comm (hc.2.1 k' k h) (hc.2.2 k' k)).symm

variable (hd : ChainDense W ι P.e P.U P.c) (hne : ouUnit W ≠ 0)
include hd

theorem denseRange : DenseRange P.Fm := by
  refine Metric.denseRange_iff.2 fun w r hr => ?_
  obtain ⟨n, μ, j, -, h⟩ := P.dense_chain hd w hr
  exact ⟨hsv μ j, by rw [dist_eq_norm, Fm_hsv]; exact h⟩

theorem Hm_ker (f : Option ι →₀ ℝ) (hf : P.Fm f = 0) : P.Hm f = 0 := by
  have := (P.denseRange hd).equalizer (P.Hm f).continuous continuous_const
    (funext fun h => by
      show P.Hm f (P.Fm h) = 0
      rw [Hm_sym, hf, map_zero])
  exact ContinuousLinearMap.ext fun v => congrFun this v

include hne

theorem chain_bound {n : ℕ} (μ : Fin (n + 1) → ℝ) (j : Fin n → ι) (hc : P.Chain μ j)
    (h : Option ι →₀ ℝ) (hh : P.Fm h = P.cv μ j) : ‖P.Hm h‖ ≤ 3 * ‖P.Fm h‖ := by
  obtain ⟨n', μ', j', hc', he, hsb⟩ := P.normalize hne n μ j hc
  have hH : P.Hm h = sv 1 μ' (fun k => P.TL (j' k)) := by
    rw [← P.Hm_hsv, ← sub_eq_zero, ← map_sub]
    exact P.Hm_ker hd _ (by rw [map_sub, Fm_hsv, hh, he, sub_self])
  rw [hH, hh]
  obtain ⟨b1, b2⟩ := ousNorm_bounds_le (P.cv μ j)
  have hμ := fun m => hsb (-ousNorm W (P.cv μ j)) (ousNorm W (P.cv μ j))
    (by rwa [neg_smul]) b2 m
  have hsv_le : ‖sv (1 : W →L[ℝ] W) μ' (fun k => P.TL (j' k))‖ ≤
      |μ' 0| + ∑ k : Fin n', (μ' k.succ - μ' k.castSucc) := by
    unfold sv
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) ContinuousLinearMap.norm_id_le
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.2 (hc'.1 k))]
      exact mul_le_of_le_one_right (sub_nonneg.2 (hc'.1 k)) (P.TL_opnorm_le _)
  have ht := tele μ'
  have h0 := hμ 0
  have hL := hμ (Fin.last n')
  rw [norm_eq_ousNorm (P.cv μ j)]
  refine hsv_le.trans ?_
  have hsum : ∑ k : Fin n', (μ' k.succ - μ' k.castSucc) = μ' (Fin.last n') - μ' 0 := by
    linarith
  rw [hsum]
  have habs : |μ' 0| ≤ ousNorm W (P.cv μ j) := abs_le.2 ⟨h0.1, h0.2⟩
  linarith [hL.2, h0.1]

theorem Hm_bound (f : Option ι →₀ ℝ) : ‖P.Hm f‖ ≤ 3 * ‖P.Fm f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hA := norm_nonneg (P.Hm f)
  have ha := norm_nonneg (P.Fm f)
  have hK : 0 < 3 * ‖P.Fm f‖ + ‖P.Hm f‖ + 1 := by positivity
  obtain ⟨n, μ, j, hc, hw⟩ := P.dense_chain hd w (div_pos hε hK)
  have hb := P.chain_bound hd hne μ j hc (hsv μ j) (P.Fm_hsv μ j)
  rw [Fm_hsv] at hb
  have h1 : P.Hm f (P.cv μ j) = P.Hm (hsv μ j) (P.Fm f) := by rw [← P.Fm_hsv, P.Hm_sym]
  have h2 : ‖P.Hm f w‖ ≤ ‖P.Hm f (P.cv μ j)‖ + ‖P.Hm f‖ * ‖w - P.cv μ j‖ := by
    have : P.Hm f w = P.Hm f (P.cv μ j) + P.Hm f (w - P.cv μ j) := by
      rw [← map_add, add_sub_cancel]
    rw [this]; exact (norm_add_le _ _).trans (add_le_add le_rfl ((P.Hm f).le_opNorm _))
  have h3 : ‖P.Hm (hsv μ j) (P.Fm f)‖ ≤ 3 * ‖P.cv μ j‖ * ‖P.Fm f‖ :=
    ((P.Hm (hsv μ j)).le_opNorm _).trans (mul_le_mul_of_nonneg_right hb ha)
  have h4 : ‖P.cv μ j‖ ≤ ‖w‖ + ‖w - P.cv μ j‖ := by
    have := norm_sub_le w (w - P.cv μ j); rwa [sub_sub_cancel] at this
  rw [h1] at h2
  set δ := ε / (3 * ‖P.Fm f‖ + ‖P.Hm f‖ + 1)
  have hδ : δ * (3 * ‖P.Fm f‖ + ‖P.Hm f‖ + 1) = ε := div_mul_cancel₀ _ hK.ne'
  have hwd := norm_nonneg (w - P.cv μ j)
  have hδ0 : 0 ≤ δ := (div_pos hε hK).le
  calc ‖P.Hm f w‖ ≤ 3 * (‖w‖ + δ) * ‖P.Fm f‖ + ‖P.Hm f‖ * δ := by
        refine h2.trans (add_le_add (h3.trans ?_) (mul_le_mul_of_nonneg_left hw.le hA))
        exact mul_le_mul_of_nonneg_right (by linarith) ha
    _ ≤ 3 * ‖P.Fm f‖ * ‖w‖ + ε := by nlinarith

omit hd hne

/-- The multiplication operator `a ↦ T_a`, extended from the span. -/
noncomputable def Mop : W →L[ℝ] (W →L[ℝ] W) := P.Hm.extendOfNorm P.Fm

include hd hne

theorem Mop_F (f : Option ι →₀ ℝ) : P.Mop (P.Fm f) = P.Hm f :=
  LinearMap.extendOfNorm_eq (P.denseRange hd) ⟨3, P.Hm_bound hd hne⟩ f

theorem Mop_one : P.Mop (ouUnit W) = 1 := by
  have : ouUnit W = P.Fm (Finsupp.single none 1) := by
    simp [Fm, gG]
  rw [this, P.Mop_F hd hne]
  simp [Hm, TG]

theorem Mop_e (i : ι) : P.Mop (P.e i) = P.TL i := by
  have : P.e i = P.Fm (Finsupp.single (some i) 1) := by
    simp [Fm, gG]
  rw [this, P.Mop_F hd hne]
  simp [Hm, TG]

theorem Mop_cv {n : ℕ} (μ : Fin (n + 1) → ℝ) (j : Fin n → ι) :
    P.Mop (P.cv μ j) = sv 1 μ (fun k => P.TL (j k)) := by
  rw [← P.Fm_hsv, P.Mop_F hd hne, P.Hm_hsv]

theorem Mop_comm (a b : W) : P.Mop a b = P.Mop b a := by
  have hD := P.denseRange hd
  have step1 : ∀ f b, P.Mop (P.Fm f) b = P.Mop b (P.Fm f) := by
    intro f
    have := hD.equalizer (P.Mop (P.Fm f)).continuous
      ((ContinuousLinearMap.apply ℝ W (P.Fm f)).continuous.comp P.Mop.continuous)
      (funext fun h => by
        show P.Mop (P.Fm f) (P.Fm h) = P.Mop (P.Fm h) (P.Fm f)
        rw [P.Mop_F hd hne, P.Mop_F hd hne, Hm_sym])
    exact congrFun this
  have := hD.equalizer ((ContinuousLinearMap.apply ℝ W b).continuous.comp P.Mop.continuous)
    (P.Mop b).continuous (funext fun f => by
      show P.Mop (P.Fm f) b = P.Mop b (P.Fm f)
      exact step1 f b)
  exact congrFun this a

theorem Mop_mul_one (a : W) : P.Mop a (ouUnit W) = a := by
  have := (P.denseRange hd).equalizer
    ((ContinuousLinearMap.apply ℝ W (ouUnit W)).continuous.comp P.Mop.continuous)
    continuous_id (funext fun f => by
      show P.Mop (P.Fm f) (ouUnit W) = P.Fm f
      rw [P.Mop_F hd hne, Hm_one])
  exact congrFun this a

/-- On a chain, `a * a = μ₀² 1 + Σ_k (μ_{k+1}² − μ_k²) e_{j_k}`. -/
theorem sq_cv : ∀ (n : ℕ) (μ : Fin (n + 1) → ℝ) (j : Fin n → ι), P.Chain μ j →
    P.Mop (P.cv μ j) (P.cv μ j) = P.cv (fun m => μ m ^ 2) j := by
  intro n
  induction n with
  | zero =>
    intro μ j _
    have h1 : P.cv μ j = μ 0 • ouUnit W := sv_zero _ _ _
    have h2 : P.cv (fun m => μ m ^ 2) j = (μ 0 ^ 2) • ouUnit W := sv_zero _ _ _
    rw [h1, h2]
    simp only [map_smul, _root_.smul_apply, P.Mop_one hd hne,
      one_apply_eq_self, _root_.smul_smul, sq]
  | succ n ih =>
    intro μ j hc
    have hcv : P.cv μ j = P.cv (Fin.init μ) (Fin.init j) +
        (μ (Fin.last (n + 1)) - μ (Fin.last n).castSucc) • P.e (j (Fin.last n)) :=
      sv_last _ _ _
    have hcv2 : P.cv (fun m => μ m ^ 2) j = P.cv (fun m => Fin.init μ m ^ 2) (Fin.init j) +
        (μ (Fin.last (n + 1)) ^ 2 - μ (Fin.last n).castSucc ^ 2) • P.e (j (Fin.last n)) :=
      sv_last _ _ _
    have h1 : P.Mop (P.e (j (Fin.last n))) = P.TL (j (Fin.last n)) := P.Mop_e hd hne _
    have h2 : P.TL (j (Fin.last n)) (P.cv (Fin.init μ) (Fin.init j)) =
        μ (Fin.last n).castSucc • P.e (j (Fin.last n)) :=
      P.TL_below (Fin.init μ) (Fin.init j) _ fun k => hc.2.1 _ _ (Fin.le_last _)
    have h3 : P.TL (j (Fin.last n)) (P.e (j (Fin.last n))) = P.e (j (Fin.last n)) :=
      P.TL_nest le_rfl
    have h4 : P.Mop (P.cv (Fin.init μ) (Fin.init j)) (P.e (j (Fin.last n))) =
        P.Mop (P.e (j (Fin.last n))) (P.cv (Fin.init μ) (Fin.init j)) := P.Mop_comm hd hne _ _
    rw [hcv, hcv2, ← ih _ _ hc.init]
    simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply,
      h4, h1, h2, h3]
    module

theorem Mop_jordan (a b : W) :
    P.Mop (P.Mop a b) (P.Mop a a) = P.Mop a (P.Mop b (P.Mop a a)) := by
  have hcomm : ∀ x : W, (P.Mop (P.Mop x x)).comp (P.Mop x) = (P.Mop x).comp (P.Mop (P.Mop x x)) := by
    intro x
    have hcl : IsClosed {y : W | (P.Mop (P.Mop y y)).comp (P.Mop y) =
        (P.Mop y).comp (P.Mop (P.Mop y y))} := isClosed_eq (by fun_prop) (by fun_prop)
    refine hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
    obtain ⟨n, μ, j, hc, hw⟩ := P.dense_chain hd x hε
    refine ⟨P.cv μ j, ?_, by rw [dist_eq_norm]; exact hw⟩
    show (P.Mop (P.Mop (P.cv μ j) (P.cv μ j))).comp (P.Mop (P.cv μ j)) =
      (P.Mop (P.cv μ j)).comp (P.Mop (P.Mop (P.cv μ j) (P.cv μ j)))
    rw [P.sq_cv hd hne n μ j hc, P.Mop_cv hd hne, P.Mop_cv hd hne]
    exact (sv_commute _ _ _ (P.chain_TL_comm hc)).eq
  calc P.Mop (P.Mop a b) (P.Mop a a) = P.Mop (P.Mop a a) (P.Mop a b) := P.Mop_comm hd hne _ _
    _ = ((P.Mop (P.Mop a a)).comp (P.Mop a)) b := rfl
    _ = ((P.Mop a).comp (P.Mop (P.Mop a a))) b := by rw [hcomm]
    _ = P.Mop a (P.Mop b (P.Mop a a)) := by
      rw [ContinuousLinearMap.comp_apply, P.Mop_comm hd hne (P.Mop a a) b]

theorem sq_chain {n : ℕ} (μ : Fin (n + 1) → ℝ) (j : Fin n → ι) (hc : P.Chain μ j)
    (h1 : -ouUnit W ≤ P.cv μ j) (h2 : P.cv μ j ≤ ouUnit W) :
    0 ≤ P.Mop (P.cv μ j) (P.cv μ j) ∧ P.Mop (P.cv μ j) (P.cv μ j) ≤ ouUnit W := by
  obtain ⟨n', μ', j', hc', he, hsb⟩ := P.normalize hne n μ j hc
  rw [← he, P.sq_cv hd hne _ _ _ hc']
  have hb := fun m => hsb (-1) 1 (by rwa [neg_smul, one_smul]) (by rwa [one_smul]) m
  have hq1 : ∀ k, P.e (j' k) ≤ ouUnit W := fun k => P.e_le_one _
  have hq0 : ∀ k, 0 ≤ P.e (j' k) := fun k => P.e_nonneg _
  constructor
  · exact sv_nonneg _ _ _ (fun m => sq_nonneg _) ou_unit_nonneg hq1 hq0 hc'.2.1
  · rw [← sub_nonneg]
    have : ouUnit W - P.cv (fun m => μ' m ^ 2) j' = P.cv (fun m => 1 - μ' m ^ 2) j' := by
      rw [cv, cv, sv_sub, sv_const, one_smul]
    rw [this]
    refine sv_nonneg _ _ _ (fun m => ?_) ou_unit_nonneg hq1 hq0 hc'.2.1
    have := hb m
    nlinarith [this.1, this.2]

theorem Mop_sq_mem (a : W) (h1 : -ouUnit W ≤ a) (h2 : a ≤ ouUnit W) :
    0 ≤ P.Mop a a ∧ P.Mop a a ≤ ouUnit W := by
  have hcl : IsClosed {x : W | 0 ≤ P.Mop x x ∧ 0 ≤ ouUnit W - P.Mop x x} :=
    (isClosed_nonneg.preimage (by fun_prop)).inter (isClosed_nonneg.preimage (by fun_prop))
  suffices hs : a ∈ {x : W | 0 ≤ P.Mop x x ∧ 0 ≤ ouUnit W - P.Mop x x} from
    ⟨hs.1, sub_nonneg.1 hs.2⟩
  refine hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  have ha : ‖a‖ ≤ 1 := ousNorm_le_rc zero_le_one (by rwa [one_smul]) (by rwa [one_smul])
  have hδ : 0 < ε / 3 := by positivity
  obtain ⟨n, μ, j, hc, hw⟩ := P.dense_chain hd a hδ
  have hδ1 : 0 < 1 + ε / 3 := by positivity
  have htt : (1 + ε / 3)⁻¹ * (1 + ε / 3) = 1 := inv_mul_cancel₀ hδ1.ne'
  have ht0 : 0 < (1 + ε / 3)⁻¹ := inv_pos.2 hδ1
  have ht1 : (1 + ε / 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hcb : P.cv (fun m => (1 + ε / 3)⁻¹ * μ m) j = (1 + ε / 3)⁻¹ • P.cv μ j := sv_smul _ _ _ _
  have hct : P.Chain (fun m => (1 + ε / 3)⁻¹ * μ m) j :=
    ⟨fun k => mul_le_mul_of_nonneg_left (hc.1 k) ht0.le, hc.2.1, hc.2.2⟩
  have hbn : ‖P.cv μ j‖ ≤ 1 + ε / 3 := by
    have := norm_sub_le a (a - P.cv μ j); rw [sub_sub_cancel] at this; linarith
  have htb : ‖(1 + ε / 3)⁻¹ • P.cv μ j‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg ht0.le]
    calc (1 + ε / 3)⁻¹ * ‖P.cv μ j‖ ≤ (1 + ε / 3)⁻¹ * (1 + ε / 3) :=
          mul_le_mul_of_nonneg_left hbn ht0.le
      _ = 1 := htt
  obtain ⟨l1, l2⟩ := ousNorm_bounds_le ((1 + ε / 3)⁻¹ • P.cv μ j)
  have hm : ousNorm W ((1 + ε / 3)⁻¹ • P.cv μ j) • ouUnit W ≤ ouUnit W := by
    have := ou_smul_unit_mono (X := W) htb; rwa [one_smul] at this
  refine ⟨(1 + ε / 3)⁻¹ • P.cv μ j, ?_, ?_⟩
  · have := P.sq_chain hd hne _ j hct (by rw [hcb]; exact (neg_le_neg hm).trans l1)
      (by rw [hcb]; exact l2.trans hm)
    rw [hcb] at this
    exact ⟨this.1, sub_nonneg.2 this.2⟩
  · rw [dist_eq_norm]
    have e : a - (1 + ε / 3)⁻¹ • P.cv μ j =
        (a - P.cv μ j) + (1 - (1 + ε / 3)⁻¹) • P.cv μ j := by
      rw [sub_smul, one_smul]; abel
    rw [e]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    have : (1 - (1 + ε / 3)⁻¹) * ‖P.cv μ j‖ ≤ (1 - (1 + ε / 3)⁻¹) * (1 + ε / 3) :=
      mul_le_mul_of_nonneg_left hbn (by linarith)
    have e2 : (1 - (1 + ε / 3)⁻¹) * (1 + ε / 3) = ε / 3 := by
      rw [sub_mul, htt, one_mul]; ring
    linarith

end Fam

end JFC

open JFC in
attribute [local instance] ousNormedAddCommGroup ousNormedSpace in
/-- **REC 121, the 9.43 part, from chain density.**  For a Banach order unit space `W`
(REC 41) and a family `(e_i, U_i, c)` satisfying the hypotheses of
`AlfsenShultzJordanFromDerivations` with norm density of the span replaced by
`ChainDense` (and without directed completeness), `W` is a JB-algebra (REC 44) whose
product satisfies `e_i * w = ½(w + (U_i − U_{c i}) w)`.  The symmetry step is
`jordan_symmetry`; the rest follows the plan of `docs/research/as943-transplant.md`
(with its Review): order lemmas for nested members, the product on the span, the bound
`‖T_a‖ ≤ 3‖a‖` on chains and its extension, and the Jordan identity and `0 ≤ a² ≤ 1` on
chains, carried to `W` by density. -/
theorem jb_of_chainDense {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W]
    [OrderUnitSpace W] (hOUS : IsOUS W) (hB : IsBanachOUS W)
    (ι : Type u) (e : ι → W) (U : ι → W →ₗ[ℝ] W) (c : ι → ι)
    (hinj : Function.Injective e)
    (_h01 : ∀ i, 0 ≤ e i ∧ e i ≤ ouUnit W) (hc : ∀ i, e (c i) = ouUnit W - e i)
    (hU : ∀ i, (∀ w, 0 ≤ w → 0 ≤ U i w) ∧ U i (ouUnit W) = e i ∧ U i ∘ₗ U i = U i ∧
      U i ∘ₗ U (c i) = 0)
    (hker : ∀ i w, 0 ≤ w → (U i w = 0 ↔ U (c i) w = w))
    (hD : ∀ i, IsOrderDerivation W (U i - U (c i)))
    (hdense : ChainDense W ι e U c) :
    ∃ _ : Mul W, JBAlgebra W ∧ ∀ i w, e i * w = (2⁻¹ : ℝ) • (w + (U i w - U (c i) w)) := by
  have := hOUS
  by_cases hne : ouUnit W = 0
  · have h0 : ∀ v : W, v = 0 := fun v => ou_eq_zero_of_unit_eq_zero hne v
    let _ : Mul W := ⟨fun _ _ => 0⟩
    exact ⟨inferInstance,
      { toIsOUS := hOUS
        banach := hB
        mul_comm := fun _ _ => (h0 _).trans (h0 _).symm
        mul_one := fun _ => (h0 _).trans (h0 _).symm
        one_mul := fun _ => (h0 _).trans (h0 _).symm
        jordan := fun _ _ => (h0 _).trans (h0 _).symm
        sq_mem := fun _ _ _ => ⟨le_of_eq (h0 _).symm, le_of_eq ((h0 _).trans (h0 _).symm)⟩
        add_mul := fun _ _ _ => (h0 _).trans (h0 _).symm
        smul_mul := fun _ _ _ => (h0 _).trans (h0 _).symm },
      fun _ _ => (h0 _).trans (h0 _).symm⟩
  have : CompleteSpace W := completeSpace_of_banach hB
  let P : Fam W ι := ⟨e, U, c, hB, hinj, hc, hU, hker, hD⟩
  have hd : ChainDense W ι P.e P.U P.c := hdense
  let _ : Mul W := ⟨fun a b => P.Mop a b⟩
  refine ⟨inferInstance,
    { toIsOUS := hOUS
      banach := hB
      mul_comm := fun a b => P.Mop_comm hd hne a b
      mul_one := fun a => P.Mop_mul_one hd hne a
      one_mul := fun a => by
        show P.Mop (ouUnit W) a = a
        rw [P.Mop_one hd hne]; rfl
      jordan := fun a b => P.Mop_jordan hd hne a b
      sq_mem := fun a h1 h2 => P.Mop_sq_mem hd hne a h1 h2
      add_mul := fun a b c => by
        show P.Mop (a + b) c = P.Mop a c + P.Mop b c
        rw [map_add]; rfl
      smul_mul := fun r a b => by
        show P.Mop (r • a) b = r • P.Mop a b
        rw [map_smul]; rfl },
    fun i w => ?_⟩
  show P.Mop (e i) w = _
  rw [P.Mop_e hd hne i]
  rfl

end Papers.REC

