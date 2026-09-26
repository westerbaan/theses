/-
Papers/SEA/JBWCommFull.lean

**SEA 16** (`ex:canonical-sea`, second.tex:475): van de Wetering's hard half for every
JBW-algebra, hence "every JBW-algebra is a convex normal SEA" unconditionally.
Route: `docs/research/jordan-fuglede.md` (reviewed 2026-09-26), with its Step D replaced.

Plan (2026-09-26).  `x = √a`, `y = √b`, `A = x∘y`, `D = [L_x, L_y]`, `U = U_x`, `Q = L_A`.
1. Identities from `jb_lin` only (coefficients found by linear algebra over instances):
   `D` is a derivation; `D(A) = ¼(U_x y² − U_y x²)`; **(JK)** `[Q,U] + DU + UD = 0`.
2. `e^{tΔ}` for a bounded derivation `Δ` is a Jordan automorphism fixing `1`, hence
   positive, hence `‖e^{tΔ} v‖ ≤ ‖v‖`.
3. **Flow** (Step A): if `D(A) = 0` then `[Q,D] = 0` and `F(t) = e^{t(2D+2Q)} U e^{t(2D−2Q)}`
   has derivative `2 e^{…}(JK)e^{…} = 0`; applied to `1`:
   `U_{e^{tA}} U_x e^{−2tA} = e^{−2tD} x²`, of norm `≤ ‖x²‖` for all `t`.
4. **Gap lemma** (Step B, continuous cut-offs only): if `W(τ) = U_{e^{τh}} U_x e^{−2τh}` is
   bounded for `τ > 0` (any `x`), then `U_{k(h)} U_x f(h) = 0` whenever `k ≥ 0` vanishes
   below `β`, `f ≥ 0` vanishes above `α < β` (`f(h) ≤ ‖f‖e^{2τα}e^{−2τh}`,
   `U_{k(h)} = U_{k e^{−τt}(h)} U_{e^{τh}}`, norm `≤ C e^{−2τ(β−α)}`).
   Passage to `p = χ_{>s}(h)`: `u = U_x(1−p) ≥ 0`; `U_{√k(h)} u = 0` for cut-offs `k`
   (`1 − p ≤ 1 − sseq`), so `U_{√u} k(h) = 0` (`sq_eq_zero_comm`), so `U_{√u} ρ(h) = 0`
   (norm limit), so `U_{√u} p = 0` (`good_Uo`, sup of `sseq ≤ (n+1)ρ(h)`), so `U_p u = 0`,
   so `P½(p) x = 0` (`ph_of_jQ_one_sub`).
5. **Powers from spectral projections**: the `sproj (rampF h δ j)` form a chain; their
   span is closed under products; `spectral_approx_expl` + continuity of `jbPow` give:
   operator-commuting with every `χ_{>s}(h)` ⇒ operator-commuting with every `hⁿ`
   ⇒ lying in `comm h`.
6. Main chain: hypothesis ⇒ `D(A) = 0` ⇒ (3,4) `x | A` ⇒ (`jb_lin(x,x,y)`) `y | a`.
   Then (replacing the note's Step D) for `λ > 0`: `x_λ = y + λ ≥ 0` has `[L_{x_λ}, L_a] = 0`,
   so (3,4,5) with the pair `(x_λ, a)` and `h_λ = λ⁻¹ x_λ∘a = a + λ⁻¹ y∘a`: `y | h_λⁿ`;
   `h_λ → a` gives `y | aⁿ`, so `y ∈ comm a`, and `b = y² ∈ comm a` (`jbw_mul_mem`).
7. `jbwSeqComm : JBSeqComm A`, `sea16_jbw_unconditional`.
Status: 1–7 done, no sorry, axiom-clean.  Not covered: JB-algebras that are not JBW (bidual).
-/
import Papers.SEA.JBSeqComm

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.SEA.JBWFull

open Theses.B.Eff Papers.REC Papers.REC.JBCalc Papers.REC.JBMac Papers.SEA.JBAll
  Papers.SEA.JBComm Papers.REC.JBWProj NormedSpace Filter Topology

universe u

noncomputable section

section Ident

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hJ : JBAlgebra A]

include hJ

attribute [local instance] ousNormedAddCommGroup ousNormedSpace jbComplete opRat

/-! ## 1. Identities from the linearised Jordan identity -/

theorem jb_lin_mul (v a b c w : A) :
    v * (a * (b * c * w)) - v * (b * c * (a * w)) + (v * (b * (c * a * w)) - v * (c * a * (b * w)))
      + (v * (c * (a * b * w)) - v * (a * b * (c * w))) = 0 := by
  have := congrArg (fun t => v * t) (jb_lin a b c w)
  simp only [jb_mul_add, jb_mul_sub, jb_mul_zero] at this
  exact this

/-- `[L_x, L_y]` is a derivation. -/
theorem der_apply (x y u v : A) :
    x * (y * (u * v)) - y * (x * (u * v)) =
      (x * (y * u) - y * (x * u)) * v + u * (x * (y * v) - y * (x * v)) := by
  have h1 := jb_lin u y v x
  have h2 := jb_lin v x u y
  have hc : ∀ a b : A, a * b = b * a := JBAlgebra.mul_comm
  simp only [jb_sub_mul, jb_mul_sub]
  simp only [hc] at h1 h2 ⊢
  linear_combination (norm := module) -h1 + h2

/-- `[L_x, L_y](x∘y) = ¼ (U_x y² − U_y x²)`. -/
theorem der_xy (x y : A) :
    x * (y * (x * y)) - y * (x * (x * y)) = (4⁻¹ : ℝ) • (jQ x (y * y) - jQ y (x * x)) := by
  have h1 := jb_lin y x x y
  have h2 := jb_lin y y x x
  have hc : ∀ a b : A, a * b = b * a := JBAlgebra.mul_comm
  simp only [jQ]
  simp only [hc] at h1 h2 ⊢
  linear_combination (norm := module) (2⁻¹ : ℝ) • h1 - (2⁻¹ : ℝ) • h2

/-- `[L_x, L_y]` as a bounded operator. -/
def Dop (x y : A) : A →L[ℝ] A := mulC x * mulC y - mulC y * mulC x

theorem Dop_apply (x y w : A) : Dop x y w = x * (y * w) - y * (x * w) := by
  simp [Dop]

/-- **(JK)** on elements. -/
theorem jk_apply (x y z : A) :
    x * y * ((2 : ℝ) • (x * (x * z)) - x * x * z)
      - ((2 : ℝ) • (x * (x * (x * y * z))) - x * x * (x * y * z))
      + (x * (y * ((2 : ℝ) • (x * (x * z)) - x * x * z))
          - y * (x * ((2 : ℝ) • (x * (x * z)) - x * x * z)))
      + ((2 : ℝ) • (x * (x * (x * (y * z) - y * (x * z)))) - x * x * (x * (y * z) - y * (x * z)))
      = 0 := by
  have h1 := jb_lin y z x (x * x)
  have h2 := jb_lin_mul x x y z x
  have h3 := jb_lin z x x (x * y)
  have h4 := jb_lin (x * z) y x x
  have h5 := jb_lin y x x (x * z)
  have h6 := jb_lin (x * z) x x y
  have h7 := jb_lin_mul x x y x z
  have h8 := jb_lin (x * y) x x z
  have h9 := jb_lin_mul y x x x z
  have h10 := jb_lin (y * z) x x x
  have hc : ∀ a b : A, a * b = b * a := JBAlgebra.mul_comm
  simp only [jb_mul_sub, jb_mul_smul]
  simp only [hc] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
  linear_combination (norm := module) (3⁻¹ : ℝ) • h1 + (4 / 3 : ℝ) • h2 - (3⁻¹ : ℝ) • h3
    - (2 : ℝ) • h4 + (2 / 3 : ℝ) • h5 + (3⁻¹ : ℝ) • h6 - h7 - (2 / 3 : ℝ) • h8
    + (3⁻¹ : ℝ) • h9 + (3⁻¹ : ℝ) • h10

/-- **(JK)** `[L_{xy}, U_x] + D U_x + U_x D = 0`, `D = [L_x, L_y]`. -/
theorem jk (x y : A) :
    mulC (x * y) * Uo x - Uo x * mulC (x * y) + Dop x y * Uo x + Uo x * Dop x y = 0 := by
  ext z
  have := jk_apply x y z
  simp only [Uo, Dop, add_apply, sub_apply, smul_apply, mul_apply_eq_comp, mulC_apply,
    zero_apply] at this ⊢
  exact this

/-- Step C: `x | x∘y` gives `y | x²`. -/
theorem opComm_sq_of_opComm_mul {x y : A} (h : OpComm x (x * y)) : OpComm y (x * x) := by
  intro w
  have h1 := jb_lin x x y w
  have e1 : x * (x * y * w) = x * y * (x * w) := h w
  have e2 : x * (y * x * w) = y * x * (x * w) := by rw [JBAlgebra.mul_comm y x]; exact h w
  rw [e1, e2, sub_self, sub_self, zero_add, zero_add, sub_eq_zero] at h1
  exact h1

/-! ## 2. The exponential of a derivation is a contraction -/

section Deriv

variable {Δ : A →L[ℝ] A} (hΔ : ∀ u v : A, Δ (u * v) = Δ u * v + u * Δ v)

include hΔ

theorem der_one : Δ (ouUnit A) = 0 := by
  have h := hΔ (ouUnit A) (ouUnit A)
  simp only [JBAlgebra.mul_one, JBAlgebra.one_mul] at h
  calc Δ (ouUnit A) = Δ (ouUnit A) + Δ (ouUnit A) - Δ (ouUnit A) := by abel
    _ = Δ (ouUnit A) - Δ (ouUnit A) := by rw [← h]
    _ = 0 := sub_self _

theorem exp_der_one (t : ℝ) : exp (t • Δ) (ouUnit A) = ouUnit A := by
  let g : ℝ → A := fun s => exp (s • Δ) (ouUnit A)
  have hg : ∀ s, HasDerivAt g 0 s := fun s => by
    have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) Δ s).clm_apply (hasDerivAt_const s (ouUnit A))
    simpa [g, der_one hΔ] using this
  have := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  simpa [g] using this

/-- `e^{tΔ}` is a Jordan automorphism. -/
theorem exp_der_mul (t : ℝ) (u v : A) :
    exp (t • Δ) (u * v) = exp (t • Δ) u * exp (t • Δ) v := by
  let E : ℝ → (A →L[ℝ] A) := fun s => exp (s • Δ)
  let G : ℝ → A := fun s => exp ((-s) • Δ) (E s u * E s v)
  have hE : ∀ (s : ℝ) (w : A), HasDerivAt (fun s => E s w) (Δ (E s w)) s := fun s w => by
    have := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Δ s).clm_apply (hasDerivAt_const s w)
    simpa [E] using this
  have he : ∀ s : ℝ, HasDerivAt (fun s : ℝ => exp ((-s) • Δ)) (-(exp ((-s) • Δ) * Δ)) s :=
    fun s => by
      have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) Δ (-s)).scomp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using this
  have hP : ∀ s, HasDerivAt (fun s => E s u * E s v)
      (E s u * Δ (E s v) + Δ (E s u) * E s v) s := fun s => by
    have := mulC.hasDerivAt_of_bilinear (u := fun s => E s u) (v := fun s => E s v)
      (fun _ => hE s u) (fun _ => hE s v)
    simpa only [mulC_apply] using this
  have hG : ∀ s, HasDerivAt G 0 s := fun s => by
    have h1 := (he s).clm_apply (hP s)
    refine h1.congr_deriv ?_
    simp only [neg_apply, mul_apply_eq_comp]
    rw [hΔ, add_comm (Δ (E s u) * E s v), neg_add_cancel]
  have hc := is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt)
    (fun s => (hG s).deriv) t 0
  have h0 : G 0 = u * v := by simp [G, E]
  rw [h0] at hc
  have hinv : exp (t • Δ) * exp ((-t) • Δ) = 1 := by
    rw [neg_smul, exp_mul_exp_neg]
  calc exp (t • Δ) (u * v) = exp (t • Δ) (G t) := by rw [hc]
    _ = (exp (t • Δ) * exp ((-t) • Δ)) (E t u * E t v) := rfl
    _ = _ := by rw [hinv]; rfl

theorem exp_der_nonneg (t : ℝ) {v : A} (hv : 0 ≤ v) : 0 ≤ exp (t • Δ) v := by
  rw [← jbSqrt_mul_self hv, exp_der_mul hΔ]; exact jb_sq_nonneg _

/-- **`‖e^{tΔ} v‖ ≤ ‖v‖`**: a unital Jordan automorphism is positive. -/
theorem exp_der_norm (t : ℝ) (v : A) : ousNorm A (exp (t • Δ) v) ≤ ousNorm A v := by
  obtain ⟨h1, h2⟩ := ousNorm_bounds_le v
  have hmono : ∀ {p q : A}, p ≤ q → exp (t • Δ) p ≤ exp (t • Δ) q := fun h => by
    have := exp_der_nonneg hΔ t (sub_nonneg.2 h); rwa [map_sub, sub_nonneg] at this
  refine ousNorm_le_rc (ousNorm_nonneg_rc v) ?_ ?_
  · have := hmono h1; rwa [map_neg, map_smul, exp_der_one hΔ] at this
  · have := hmono h2; rwa [map_smul, exp_der_one hΔ] at this

end Deriv

/-! ## 3. The flow identity (Step A) -/

theorem Dop_der (x y : A) (u v : A) : Dop x y (u * v) = Dop x y u * v + u * Dop x y v := by
  simp only [Dop_apply]; exact der_apply x y u v

/-- **Step A**: if `[L_x, L_y](x∘y) = 0` then
`e^{2t[L_x,L_y]} U_{e^{t x∘y}} U_x e^{−2t x∘y} = x²`. -/
theorem flow (x y : A) (hDA : x * (y * (x * y)) - y * (x * (x * y)) = 0) (t : ℝ) :
    exp (t • ((2 : ℝ) • Dop x y)) (Uo (eE (t • (x * y))) (Uo x (eE ((-2 * t) • (x * y))))) =
      x * x := by
  set Q := mulC (x * y) with hQ
  set D := Dop x y with hD
  set U := Uo x with hU
  have hQD : Commute Q D := by
    ext w
    simp only [mul_apply_eq_comp, hQ, mulC_apply, hD]
    rw [Dop_der, Dop_apply x y (x * y), hDA, jb_zero_mul, zero_add]
  have hJK : Q * U - U * Q + D * U + U * D = 0 := jk x y
  set M := (2 : ℝ) • D + (2 : ℝ) • Q with hM
  set N := (2 : ℝ) • D - (2 : ℝ) • Q with hN
  have hMUN : M * U + U * N = 0 := by
    have : M * U + U * N = (2 : ℝ) • (Q * U - U * Q + D * U + U * D) := by
      simp only [hM, hN, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
      module
    rw [this, hJK, smul_zero]
  let F : ℝ → (A →L[ℝ] A) := fun s => exp (s • M) * U * exp (s • N)
  have hF : ∀ s, HasDerivAt F 0 s := fun s => by
    have h1 := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) M s).mul_const U).mul
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) N s)
    refine h1.congr_deriv ?_
    calc exp (s • M) * M * U * exp (s • N) + exp (s • M) * U * (N * exp (s • N)) =
        exp (s • M) * (M * U + U * N) * exp (s • N) := by noncomm_ring
      _ = 0 := by rw [hMUN, mul_zero, zero_mul]
  have hc := is_const_of_deriv_eq_zero (fun s => (hF s).differentiableAt)
    (fun s => (hF s).deriv) t 0
  have hF0 : F 0 = U := by simp [F]
  rw [hF0] at hc
  have c1 : Commute (t • ((2 : ℝ) • D)) (t • ((2 : ℝ) • Q)) :=
    (((hQD.symm.smul_left (2 : ℝ)).smul_right (2 : ℝ)).smul_left t).smul_right t
  have hsplitM : exp (t • M) = exp (t • ((2 : ℝ) • D)) * exp (t • ((2 : ℝ) • Q)) := by
    rw [hM, smul_add]; exact exp_add_of_commute c1
  have hsplitN : exp (t • N) = exp (-(t • ((2 : ℝ) • Q))) * exp (t • ((2 : ℝ) • D)) := by
    have e : t • N = -(t • ((2 : ℝ) • Q)) + t • ((2 : ℝ) • D) := by
      rw [hN, smul_sub]; abel
    rw [e]; exact exp_add_of_commute c1.symm.neg_left
  have hder2 : ∀ u v : A, ((2 : ℝ) • D) (u * v) = ((2 : ℝ) • D) u * v + u * ((2 : ℝ) • D) v := by
    intro u v
    simp only [smul_apply, hD, Dop_der, smul_add, JBAlgebra.smul_mul, jb_mul_smul]
  have hD1 := exp_der_one hder2 t
  have hQ1 : exp (-(t • ((2 : ℝ) • Q))) (ouUnit A) = eE ((-2 * t) • (x * y)) := by
    rw [eE, map_smul]
    congr 2
    module
  have hUQ : exp (t • ((2 : ℝ) • Q)) = Uo (eE (t • (x * y))) := by
    rw [Uo_eE, map_smul, ← exp_add_of_commute (Commute.refl _)]
    congr 1
    module
  have key := congrArg (fun T : A →L[ℝ] A => T (ouUnit A)) hc
  simp only [F, mul_apply_eq_comp] at key
  rw [hsplitM, hsplitN, mul_apply_eq_comp, mul_apply_eq_comp, hD1, hQ1,
    hUQ] at key
  rw [key, hU, Uo_apply_one]

/-- **Step A, norm form**: `‖U_{e^{t x∘y}} U_x e^{−2t x∘y}‖ ≤ ‖x²‖`. -/
theorem flow_bound (x y : A) (hDA : x * (y * (x * y)) - y * (x * (x * y)) = 0) (t : ℝ) :
    ousNorm A (Uo (eE (t • (x * y))) (Uo x (eE ((-2 * t) • (x * y))))) ≤ ousNorm A (x * x) := by
  set Δ : A →L[ℝ] A := (2 : ℝ) • Dop x y
  have hder : ∀ u v : A, Δ (u * v) = Δ u * v + u * Δ v := by
    intro u v
    simp only [Δ, smul_apply, Dop_der, smul_add, JBAlgebra.smul_mul, jb_mul_smul]
  set W := Uo (eE (t • (x * y))) (Uo x (eE ((-2 * t) • (x * y))))
  have hW : W = exp ((-t) • Δ) (x * x) := by
    rw [← flow x y hDA t, ← mul_apply_eq_comp,
      ← exp_add_of_commute (((Commute.refl Δ).smul_left (-t)).smul_right t), ← add_smul,
      neg_add_cancel, zero_smul, exp_zero, one_apply_eq_self]
  rw [hW]
  exact exp_der_norm hder _ _

/-! ## 4. Functional-calculus helpers -/

/-- `t ↦ e^{ct}` on `sp h`. -/
def expF (h : A) (c : ℝ) : C(jbSpec h, ℝ) :=
  ⟨fun s => Real.exp (c * s.1), Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)⟩

theorem expF_apply (h : A) (c : ℝ) (s : jbSpec h) : expF h c s = Real.exp (c * s.1) := rfl

/-- `e^{c h} = (t ↦ e^{ct})(h)`. -/
theorem eE_smul_eq (h : A) (c : ℝ) : eE (c • h) = jbCfc h (expF h c) := by
  set g : C(jbSpec h, ℝ) := c • specId h with hg
  have e1 : c • h = jbCfc h g := by rw [hg, jbCfc_smul, jbCfc_id]
  rw [e1]
  have h1 := hasSum_eE (jbCfc h g)
  simp only [jbPow_jbCfc] at h1
  have h2 := (jbCfcL h).hasSum (exp_series_hasSum_exp' (𝕂 := ℝ) g)
  simp only [map_smul, jbCfcL_apply] at h2
  rw [h1.unique h2]
  congr 1
  ext s
  have h3 := (ContinuousMap.evalCLM ℝ s).hasSum (exp_series_hasSum_exp' (𝕂 := ℝ) g)
  have h4 := exp_series_hasSum_exp' (𝕂 := ℝ) (g s)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply,
    ContinuousMap.pow_apply] at h3
  rw [h3.unique h4, ← Real.exp_eq_exp_ℝ, expF_apply, hg]
  rfl

/-- `U_{(g²m)(h)} = U_{m(h)} U_{g²(h)}`. -/
theorem Uo_cfc_mul (h : A) (g m : C(jbSpec h, ℝ)) :
    Uo (jbCfc h (g * g * m)) = Uo (jbCfc h m) * Uo (jbCfc h (g * g)) := by
  have hG := jbCfc_mem h g
  have hM := jbCfc_mem h m
  have hGG : jbCfc h g * jbCfc h g ∈ (Ca h).carrier := by
    rw [← jbCfc_mul]; exact jbCfc_mem h _
  have hMM : jbCfc h m * jbCfc h m ∈ (Ca h).carrier := by
    rw [← jbCfc_mul]; exact jbCfc_mem h _
  have e1 : jbCfc h (g * g * m) = Uo (jbCfc h g) (jbCfc h m) := by
    rw [jbCfc_mul, jbCfc_mul, Uo_apply, jQ_of_opComm (opComm_Ca hG hM)]
  have hc : Commute (Uo (jbCfc h g)) (Uo (jbCfc h m)) :=
    commute_Uo (opComm_Ca hG hM) (opComm_Ca hG hMM) (opComm_Ca hGG hM) (opComm_Ca hGG hMM)
  rw [e1, Uo_Uo, hc.eq, mul_assoc, ← Uo_mul_self, jbCfc_mul]

theorem ousNorm_jQ_le (c v : A) : ousNorm A (jQ c v) ≤ 3 * ousNorm A c ^ 2 * ousNorm A v := by
  have h1 := jb_norm_mul_le c (c * v)
  have h2 := jb_norm_mul_le c v
  have h3 := jb_norm_mul_le (c * c) v
  have h4 := jb_norm_mul_le c c
  have hc := ousNorm_nonneg_rc c
  have hv := ousNorm_nonneg_rc v
  have h5 := ousNorm_nonneg_rc (c * v)
  have h6 := ousNorm_nonneg_rc (c * c)
  rw [jQ, sub_eq_add_neg]
  refine (ousNorm_add_le _ _).trans ?_
  rw [ousNorm_neg, ousNorm_smul_eq, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have : ousNorm A (c * (c * v)) ≤ ousNorm A c ^ 2 * ousNorm A v := by
    calc _ ≤ ousNorm A c * ousNorm A (c * v) := h1
      _ ≤ ousNorm A c * (ousNorm A c * ousNorm A v) := mul_le_mul_of_nonneg_left h2 hc
      _ = _ := by ring
  have : ousNorm A (c * c * v) ≤ ousNorm A c ^ 2 * ousNorm A v := by
    calc _ ≤ ousNorm A (c * c) * ousNorm A v := h3
      _ ≤ (ousNorm A c * ousNorm A c) * ousNorm A v := mul_le_mul_of_nonneg_right h4 hv
      _ = _ := by ring
  linarith

theorem ousNorm_mono {v w : A} (h0 : 0 ≤ v) (h : v ≤ w) : ousNorm A v ≤ ousNorm A w :=
  ousNorm_le_rc (ousNorm_nonneg_rc w)
    ((neg_nonpos.2 (smul_nonneg (ousNorm_nonneg_rc w) ou_unit_nonneg)).trans h0)
    (h.trans (ousNorm_bounds_le w).2)

end Ident

/-! ## 5. The gap lemma (Step B) -/

section JBW

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hW : JBWAlgebra A]

include hW

attribute [local instance] ousNormedAddCommGroup ousNormedSpace jbComplete opRat

/-- The flow `τ ↦ U_{e^{τh}} U_x e^{−2τh}`. -/
def flowW (x h : A) (τ : ℝ) : A := Uo (eE (τ • h)) (Uo x (eE ((-2 * τ) • h)))

/-- **Gap lemma**: if the flow is bounded, `U_{k(h)} U_x f(h) = 0` for `k ≥ 0` vanishing below
`β` and `f ≥ 0` vanishing above `α < β`. -/
theorem gap_zero {x h : A} {C : ℝ} (hWb : ∀ τ : ℝ, 0 < τ → ousNorm A (flowW x h τ) ≤ C)
    {α β : ℝ} (hαβ : α < β) {k f : C(jbSpec h, ℝ)} (hf0 : ∀ t, 0 ≤ f t)
    (hk : ∀ t : jbSpec h, t.1 < β → k t = 0) (hf : ∀ t : jbSpec h, α < t.1 → f t = 0) :
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
    have e1 : jbCfc h f ≤ (Fn * Real.exp (2 * τ * α)) • eE ((-2 * τ) • h) := by
      rw [eE_smul_eq, ← jbCfc_smul, jbCfc_le_iff]
      intro t
      simp only [ContinuousMap.smul_apply, expF_apply, smul_eq_mul]
      by_cases ht : α < t.1
      · rw [hf t ht]; positivity
      · replace ht := not_lt.1 ht
        have h1 : f t ≤ Fn := ContinuousMap.apply_le_norm f t
        have h2 : 1 ≤ Real.exp (2 * τ * α) * Real.exp (-2 * τ * t.1) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        calc f t ≤ Fn := h1
          _ ≤ Fn * (Real.exp (2 * τ * α) * Real.exp (-2 * τ * t.1)) :=
            le_mul_of_one_le_right hFn h2
          _ = _ := by ring
    set g : C(jbSpec h, ℝ) := expF h (τ / 2) with hg
    set m : C(jbSpec h, ℝ) := k * expF h (-τ) with hm
    have hk_eq : k = g * g * m := by
      ext t
      simp only [hg, hm, ContinuousMap.mul_apply, expF_apply]
      have : Real.exp (τ / 2 * t.1) * Real.exp (τ / 2 * t.1) * Real.exp (-τ * t.1) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]; congr 1; ring
      linear_combination (-(k t)) * this
    have hgg : jbCfc h (g * g) = eE (τ • h) := by
      rw [eE_smul_eq]; congr 1; ext t
      simp only [hg, ContinuousMap.mul_apply, expF_apply, ← Real.exp_add]; congr 1; ring
    have hUk : Uo (jbCfc h k) = Uo (jbCfc h m) * Uo (eE (τ • h)) := by
      conv_lhs => rw [hk_eq]
      rw [Uo_cfc_mul, hgg]
    have e2 : Z ≤ (Fn * Real.exp (2 * τ * α)) • jQ (jbCfc h k) (jQ x (eE ((-2 * τ) • h))) := by
      rw [← jQ_smul, ← jQ_smul]; exact jQ_mono _ (jQ_mono _ e1)
    have e3 : jQ (jbCfc h k) (jQ x (eE ((-2 * τ) • h))) = jQ (jbCfc h m) (flowW x h τ) := by
      rw [← Uo_apply, ← Uo_apply, hUk, mul_apply_eq_comp, Uo_apply, flowW]
    have hmn : ousNorm A (jbCfc h m) ≤ K * Real.exp (-τ * β) := by
      rw [ousNorm_jbCfc]
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
      simp only [hm, ContinuousMap.mul_apply, expF_apply, norm_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      by_cases ht : t.1 < β
      · rw [hk t ht, abs_zero, zero_mul]; positivity
      · replace ht := not_lt.1 ht
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm k t)
          (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le hK
    have hWt := hWb τ hτ
    have hC : 0 ≤ C := (ousNorm_nonneg_rc _).trans hWt
    have hm0 := ousNorm_nonneg_rc (jbCfc h m)
    have hexp : Real.exp (2 * τ * α) * (Real.exp (-τ * β)) ^ 2 =
        Real.exp (-(2 * (β - α)) * τ) := by
      rw [_root_.sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc ousNorm A Z ≤ ousNorm A ((Fn * Real.exp (2 * τ * α)) •
          jQ (jbCfc h k) (jQ x (eE ((-2 * τ) • h)))) := ousNorm_mono hZ0 e2
      _ = Fn * Real.exp (2 * τ * α) * ousNorm A (jQ (jbCfc h m) (flowW x h τ)) := by
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

/-- `(ρ − c)⁺`. -/
def cutF {h : A} (ρ : C(jbSpec h, ℝ)) (c : ℝ) : C(jbSpec h, ℝ) :=
  ⟨fun t => max (ρ t - c) 0, (ρ.continuous.sub continuous_const).max continuous_const⟩

theorem cutF_apply {h : A} (ρ : C(jbSpec h, ℝ)) (c : ℝ) (t : jbSpec h) :
    cutF ρ c t = max (ρ t - c) 0 := rfl

/-- **Step B**: a bounded flow forces `P½(χ_{>s}(h)) x = 0` for every level. -/
theorem ph_sproj_of_flow {x h : A} {C : ℝ}
    (hWb : ∀ τ : ℝ, 0 < τ → ousNorm A (flowW x h τ) ≤ C) (δ : ℝ) (j : ℕ) :
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
      refine gap_zero hWb (α := s + 1 / ((m : ℝ) + 1)) (β := s + 2 / ((m : ℝ) + 1)) ?_ ?_ ?_ ?_
      · have : 1 / ((m : ℝ) + 1) < 2 / ((m : ℝ) + 1) := div_lt_div_of_pos_right (by norm_num) hm1
        linarith
      · intro t
        simp only [hfF, ContinuousMap.sub_apply, ContinuousMap.one_apply, sfun_apply]
        linarith [min_le_right (((m : ℝ) + 1) * ρ t) 1]
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

theorem opComm_of_flow {x h : A} {C : ℝ}
    (hWb : ∀ τ : ℝ, 0 < τ → ousNorm A (flowW x h τ) ≤ C) (δ : ℝ) (j : ℕ) :
    OpComm (sproj (rampF h δ j)) x :=
  opComm_of_ph (sproj_idem (rampF_nonneg h j)) (ph_sproj_of_flow hWb δ j)

/-! ## 6. From spectral projections to powers -/

theorem sproj_ramp_le (h : A) {δ : ℝ} (hδ : 0 < δ) {i j : ℕ} (hij : i ≤ j) :
    sproj (rampF h δ j) ≤ sproj (rampF h δ i) := by
  have h0j : ∀ t, 0 ≤ rampF h δ j t := rampF_nonneg h j
  have h0i : ∀ t, 0 ≤ rampF h δ i t := rampF_nonneg h i
  refine (sproj_isLUB h0j).2 ?_
  rintro _ ⟨n, rfl⟩
  refine le_trans ?_ ((sproj_isLUB h0i).1 ⟨n, rfl⟩)
  rw [sseq, sseq, jbCfc_le_iff]; intro t
  simp only [sfun_apply, rampF, ContinuousMap.coe_mk]
  refine min_le_min_right _ (mul_le_mul_of_nonneg_left (max_le_max ?_ le_rfl) (by positivity))
  have : (i : ℝ) * δ ≤ j * δ := mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) hδ.le
  linarith

theorem sproj_ramp_mul (h : A) {δ : ℝ} (hδ : 0 < δ) (i j : ℕ) :
    sproj (rampF h δ i) * sproj (rampF h δ j) = sproj (rampF h δ (max i j)) := by
  have hpi := sproj_idem (rampF_nonneg (δ := δ) h i)
  have hpj := sproj_idem (rampF_nonneg (δ := δ) h j)
  rcases le_total i j with hij | hij
  · rw [max_eq_right hij]; exact (idem_le_iff hpj hpi).1 (sproj_ramp_le h hδ hij)
  · rw [max_eq_left hij, JBAlgebra.mul_comm]; exact (idem_le_iff hpi hpj).1 (sproj_ramp_le h hδ hij)

/-- The span of `1` and the spectral projections `χ_{>s}(h)` at mesh `δ`. -/
def pspan (h : A) (δ : ℝ) : Submodule ℝ A :=
  Submodule.span ℝ (insert (ouUnit A) (Set.range fun j => sproj (rampF h δ j)))

theorem proj_mul_mem (h : A) {δ : ℝ} (hδ : 0 < δ) (j : ℕ) {w : A} (hw : w ∈ pspan h δ) :
    sproj (rampF h δ j) * w ∈ pspan h δ := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    rcases hw with rfl | ⟨k, rfl⟩
    · rw [JBAlgebra.mul_one]
      exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
    · rw [sproj_ramp_mul h hδ]
      exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨_, rfl⟩)
  | zero => rw [jb_mul_zero]; exact zero_mem _
  | add w₁ w₂ _ _ h₁ h₂ => rw [jb_mul_add]; exact add_mem h₁ h₂
  | smul c w _ hw' => rw [jb_mul_smul]; exact Submodule.smul_mem _ c hw'

theorem mul_mem_pspan (h : A) {δ : ℝ} (hδ : 0 < δ) {v w : A} (hv : v ∈ pspan h δ)
    (hw : w ∈ pspan h δ) : v * w ∈ pspan h δ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rcases hv with rfl | ⟨k, rfl⟩
    · rw [JBAlgebra.one_mul]; exact hw
    · exact proj_mul_mem h hδ k hw
  | zero => rw [jb_zero_mul]; exact zero_mem _
  | add v₁ v₂ _ _ h₁ h₂ => rw [JBAlgebra.add_mul]; exact add_mem h₁ h₂
  | smul c v _ hv' => rw [JBAlgebra.smul_mul]; exact Submodule.smul_mem _ c hv'

theorem jbPow_mem_pspan (h : A) {δ : ℝ} (hδ : 0 < δ) {v : A} (hv : v ∈ pspan h δ) (n : ℕ) :
    jbPow v n ∈ pspan h δ := by
  induction n with
  | zero => exact Submodule.subset_span (Set.mem_insert _ _)
  | succ n ih => rw [jbPow_succ]; exact mul_mem_pspan h hδ hv ih

theorem opComm_pspan {h z : A} {δ : ℝ} (hz : ∀ j, OpComm (sproj (rampF h δ j)) z) {v : A}
    (hv : v ∈ pspan h δ) : OpComm v z := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rcases hv with rfl | ⟨k, rfl⟩
    · exact opComm_one_left z
    · exact hz k
  | zero => exact opComm_zero_left z
  | add v₁ v₂ _ _ h₁ h₂ => exact opComm_add_left h₁ h₂
  | smul c v _ hv' => exact opComm_smul_left c hv'

theorem continuous_jbPow (n : ℕ) : Continuous fun w : A => jbPow w n := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    show Continuous fun w : A => w * jbPow w n
    exact jb_continuous_mul.comp (continuous_id.prodMk ih)

/-- Operator-commuting with every spectral projection `χ_{>s}(h)` gives operator-commuting
with every power of `h` (spectral theorem, powers of a chain of idempotents, continuity). -/
theorem pow_opComm_of_sprojs {h z : A}
    (hz : ∀ δ : ℝ, 0 < δ → ∀ j : ℕ, OpComm (sproj (rampF h δ j)) z) (n : ℕ) :
    OpComm (jbPow h n) z := by
  have hex : ∀ m : ℕ, ∃ w : A, OpComm (jbPow w n) z ∧ ousNorm A (h - w) ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    have hδ : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨M, c, hM⟩ := spectral_approx_expl h hδ
    refine ⟨_, opComm_pspan (hz _ hδ) (jbPow_mem_pspan h hδ ?_ n), hM⟩
    refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
        Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i + 1, rfl⟩)))
  choose w hw1 hw2 using hex
  have hwt : Tendsto w atTop (𝓝 h) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have : ‖h - w m‖ ≤ 1 / ((m : ℝ) + 1) := hw2 m
    rwa [norm_sub_rev] at this
  exact (isClosed_opComm_left z).mem_of_tendsto (((continuous_jbPow n).tendsto h).comp hwt)
    (Eventually.of_forall hw1)

theorem mem_comm_of_pows {h z : A} (hz : ∀ n : ℕ, OpComm (jbPow h n) z) : z ∈ comm h := by
  intro w hw
  have hsub : Set.range (jbEv h) ⊆ {x | OpComm x z} := by
    rintro _ ⟨q, rfl⟩
    induction q using Polynomial.induction_on' with
    | add q q' hq hq' => rw [map_add]; exact opComm_add_left hq hq'
    | monomial n r => rw [jbEv_monomial]; exact opComm_smul_left r (hz n)
  exact (isClosed_opComm_left z).closure_subset_iff.2 hsub (mem_Ca.1 hw)

/-! ## 7. The hard half for every JBW-algebra -/

/-- Steps A–C: `U_{√a} b = U_{√b} a` gives `√b | a`. -/
theorem opComm_sqrt_of_sq {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : JBAll.sq a b = JBAll.sq b a) :
    OpComm (jbSqrt b) a := by
  set x := jbSqrt a
  set y := jbSqrt b
  have hxx : x * x = a := jbSqrt_mul_self ha
  have hyy : y * y = b := jbSqrt_mul_self hb
  have hDA : x * (y * (x * y)) - y * (x * (x * y)) = 0 := by
    rw [der_xy, hxx, hyy]
    rw [JBAll.sq, JBAll.sq] at h
    rw [h, sub_self, smul_zero]
  have hWb : ∀ τ : ℝ, 0 < τ → ousNorm A (flowW x (x * y) τ) ≤ ousNorm A (x * x) :=
    fun τ _ => flow_bound x y hDA τ
  have hc : OpComm (x * y) x := opComm_of_sprojs fun δ _ j => opComm_of_flow hWb δ j
  have := opComm_sq_of_opComm_mul hc.symm
  rwa [hxx] at this

/-- `y | a` gives `y | aⁿ` (via `x_λ = y + λ`, `h_λ = λ⁻¹ x_λ∘a → a`). -/
theorem opComm_pow_of_opComm {y a : A} (hya : OpComm y a) (n : ℕ) : OpComm (jbPow a n) y := by
  have hl : ∀ m : ℕ,
      OpComm (jbPow (((m : ℝ) + 1)⁻¹ • ((y + ((m : ℝ) + 1) • ouUnit A) * a)) n) y := by
    intro m
    set l : ℝ := (m : ℝ) + 1 with hldef
    set xl := y + l • ouUnit A with hxl
    have hxa : OpComm xl a := opComm_add_left hya (opComm_smul_left _ (opComm_one_left a))
    have hDA : xl * (a * (xl * a)) - a * (xl * (xl * a)) = 0 := by rw [hxa (xl * a), sub_self]
    have hWb : ∀ τ : ℝ, 0 < τ → ousNorm A (flowW xl (l⁻¹ • (xl * a)) τ) ≤ ousNorm A (xl * xl) := by
      intro τ _
      have e : flowW xl (l⁻¹ • (xl * a)) τ =
          Uo (eE ((τ * l⁻¹) • (xl * a))) (Uo xl (eE ((-2 * (τ * l⁻¹)) • (xl * a)))) := by
        rw [flowW, smul_smul, smul_smul, mul_assoc]
      rw [e]; exact flow_bound xl a hDA _
    have hcomm : ∀ δ : ℝ, 0 < δ → ∀ j : ℕ, OpComm (sproj (rampF (l⁻¹ • (xl * a)) δ j)) y := by
      intro δ _ j
      have h1 := opComm_of_flow hWb δ j
      have e : y = xl + (-l) • ouUnit A := by rw [hxl, neg_smul]; abel
      rw [e]; exact opComm_add_right h1 (opComm_smul_right _ (opComm_one_left _).symm)
    exact pow_opComm_of_sprojs hcomm n
  have hlim : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹ • ((y + ((m : ℝ) + 1) • ouUnit A) * a))
      atTop (𝓝 a) := by
    have e : ∀ m : ℕ, ((m : ℝ) + 1)⁻¹ • ((y + ((m : ℝ) + 1) • ouUnit A) * a) =
        a + ((m : ℝ) + 1)⁻¹ • (y * a) := by
      intro m
      have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
      rw [JBAlgebra.add_mul, JBAlgebra.smul_mul, JBAlgebra.one_mul, smul_add, smul_smul,
        inv_mul_cancel₀ hm, one_smul, add_comm]
    simp_rw [e]
    have h0 : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
      simpa using this
    have h1 : Tendsto (fun m : ℕ => a + ((m : ℝ) + 1)⁻¹ • (y * a)) atTop
        (𝓝 (a + (0 : ℝ) • (y * a))) := tendsto_const_nhds.add (h0.smul_const (y * a))
    rwa [zero_smul, add_zero] at h1
  exact (isClosed_opComm_left y).mem_of_tendsto (((continuous_jbPow n).tendsto a).comp hlim)
    (Eventually.of_forall hl)

/-- **Van de Wetering's hard half in every JBW-algebra**: for `a, b ≥ 0`,
`U_{√a} b = U_{√b} a` implies that `b` operator-commutes with every element of `C(a)`. -/
theorem jbw_mem_comm {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : JBAll.sq a b = JBAll.sq b a) :
    b ∈ comm a := by
  have hy : jbSqrt b ∈ comm a :=
    mem_comm_of_pows (opComm_pow_of_opComm (opComm_sqrt_of_sq ha hb h))
  have := jbw_mul_mem hy hy
  rwa [jbSqrt_mul_self hb] at this

/-- **`JBSeqComm` holds in every JBW-algebra.** -/
theorem jbwSeqComm : JBSeqComm A := ⟨fun _ _ ha hb h => jbw_mem_comm ha hb h⟩

/-- **SEA 16, JBW half, unconditional**: every JBW-algebra's unit interval is a convex
normal SEA with `a ∘ b = U_{√a} b`. -/
theorem sea16_jbw_unconditional :
    @IsConvex _ (jbEA A) ∧
    ∀ a b : Set.Icc (0 : A) (ouUnit A),
      ∃! r : A, 0 ≤ r ∧ r * r = a.1 ∧
        (@SequentialEffectAlgebra.seq _ (jbEA A)
          (jbwNormalSEA (jbCommutation_of_seqComm jbwSeqComm) jbwCommSup).toSequentialEffectAlgebra
            a b).1 = (2 : ℝ) • (r * (r * b.1)) - (r * r) * b.1 :=
  sea16_jbw_of_seqComm jbwSeqComm

end JBW

end

end Papers.SEA.JBWFull
