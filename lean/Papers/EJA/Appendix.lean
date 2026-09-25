import Papers.EJA.Prelim

/-!
# EJA, appendix: basic structure of (possibly infinite-dimensional) EJAs

A. Westerbaan, B. Westerbaan, J. van de Wetering, *Pure Maps between Euclidean
Jordan Algebras*, QPL 2018, `../papers/1805.11496/main.tex`, Appendix A.
Unlike §2–§3 these points are about the paper's own definition `PaperEJA`
(EJA 1), a possibly infinite-dimensional real Hilbert space.

Phase 1 covers EJA 41 (the product is bounded).  EJA 42–54 are planned in
`PLAN.md`; EJA 45 needs Kadison's representation theorem (not in Mathlib) and
EJA 54 the Hanche-Olsen–Størmer classification.
-/

namespace Papers.EJA

open scoped InnerProductSpace

universe u

section Bounded

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Mul E] [One E] [PaperEJA E]

theorem PaperEJA.mul_smul (r : ℝ) (a b : E) : a * (r • b) = r • (a * b) := by
  rw [PaperEJA.mul_comm, PaperEJA.smul_mul, PaperEJA.mul_comm]

/-- Left multiplication `L_a b = a * b`, a linear map (EJA 42's `L_a`). -/
def PaperEJA.lmul (a : E) : E →ₗ[ℝ] E where
  toFun b := a * b
  map_add' := PaperEJA.mul_add a
  map_smul' r b := PaperEJA.mul_smul r a b

omit [CompleteSpace E] [One E] [PaperEJA E] in
/-- A linear map bounded by `C` on the unit ball is bounded by `C ‖b‖`. -/
theorem bound_of_unit_ball {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E →ₗ[ℝ] F} {C : ℝ} (h : ∀ b : E, ‖b‖ ≤ 1 → ‖f b‖ ≤ C) (b : E) :
    ‖f b‖ ≤ C * ‖b‖ := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have h1 := h (‖b‖⁻¹ • b) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  rw [map_smul, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hn] at h1
  linarith [mul_comm C ‖b‖]

/-- First step of EJA 41: each `L_a` is bounded — the uniform boundedness
principle applied to the functionals `⟨a * b, ·⟩ = ⟨b, a * ·⟩`, `‖b‖ ≤ 1`. -/
theorem PaperEJA.exists_bound_lmul (a : E) : ∃ C : ℝ, ∀ b : E, ‖a * b‖ ≤ C * ‖b‖ := by
  let g : {b : E // ‖b‖ ≤ 1} → E →L[ℝ] ℝ := fun b => innerSL ℝ (a * b.1)
  have hpt : ∀ c : E, ∃ C, ∀ i, ‖g i c‖ ≤ C := by
    intro c
    refine ⟨‖a * c‖, fun i => ?_⟩
    simp only [g, innerSL_apply_apply]
    rw [PaperEJA.inner_mul (E := E)]
    calc ‖⟪i.1, a * c⟫_ℝ‖ ≤ ‖i.1‖ * ‖a * c‖ := norm_inner_le_norm _ _
      _ ≤ 1 * ‖a * c‖ := by gcongr; exact i.2
      _ = ‖a * c‖ := by ring
  obtain ⟨C, hC⟩ := banach_steinhaus hpt
  refine ⟨C, bound_of_unit_ball (f := PaperEJA.lmul a) (fun b hb => ?_)⟩
  have := hC ⟨b, hb⟩
  simp only [g, innerSL_apply_norm] at this
  exact this

/-- **EJA 41** (main.tex:990, Proposition): for every EJA there is `r > 0` with
`‖a * b‖ ≤ r ‖a‖ ‖b‖` for all `a, b` (Hilbert norm).  The paper's proof: the
uniform boundedness principle twice — once for each `L_a`
(`exists_bound_lmul`), once for the family `L_a`, `‖a‖ ≤ 1`, which is
pointwise bounded since `‖a * b‖ = ‖L_b a‖ ≤ ‖L_b‖`.  (The print's "in
particular `*` is uniformly continuous" is meant on bounded sets: a bounded
bilinear map is continuous, and uniformly so on bounded sets only.) -/
theorem prod_bounded : ∃ r : ℝ, 0 < r ∧ ∀ a b : E, ‖a * b‖ ≤ r * ‖a‖ * ‖b‖ := by
  have hL : ∀ a : E, ∃ C : ℝ, 0 ≤ C ∧ ∀ b : E, ‖a * b‖ ≤ C * ‖b‖ := by
    intro a
    obtain ⟨C, hC⟩ := PaperEJA.exists_bound_lmul a
    exact ⟨max C 0, le_max_right _ _, fun b =>
      le_trans (hC b) (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg b))⟩
  choose C hC0 hC using hL
  let L : E → E →L[ℝ] E := fun a => (PaperEJA.lmul a).mkContinuous (C a) (hC a)
  let g : {a : E // ‖a‖ ≤ 1} → E →L[ℝ] E := fun a => L a.1
  have hpt : ∀ b : E, ∃ K, ∀ i, ‖g i b‖ ≤ K := by
    intro b
    refine ⟨C b, fun i => ?_⟩
    show ‖i.1 * b‖ ≤ C b
    rw [PaperEJA.mul_comm]
    calc ‖b * i.1‖ ≤ C b * ‖i.1‖ := hC b i.1
      _ ≤ C b * 1 := mul_le_mul_of_nonneg_left i.2 (hC0 b)
      _ = C b := mul_one _
  obtain ⟨K, hK⟩ := banach_steinhaus hpt
  refine ⟨max K 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun a b => ?_⟩
  have hball : ∀ a : E, ‖a‖ ≤ 1 → ∀ b : E, ‖a * b‖ ≤ max K 1 * ‖b‖ := by
    intro a ha b
    have h1 : ‖g ⟨a, ha⟩ b‖ ≤ ‖g ⟨a, ha⟩‖ * ‖b‖ := ContinuousLinearMap.le_opNorm _ _
    have h2 := hK ⟨a, ha⟩
    calc ‖a * b‖ = ‖g ⟨a, ha⟩ b‖ := rfl
      _ ≤ ‖g ⟨a, ha⟩‖ * ‖b‖ := h1
      _ ≤ max K 1 * ‖b‖ := by gcongr; exact le_trans h2 (le_max_left _ _)
  -- scale `a` into the unit ball
  let Rb : E →ₗ[ℝ] E :=
    { toFun := fun a => a * b
      map_add' := fun x y => by
        rw [PaperEJA.mul_comm, PaperEJA.mul_add, PaperEJA.mul_comm b, PaperEJA.mul_comm b]
      map_smul' := fun r x => PaperEJA.smul_mul r x b }
  have := bound_of_unit_ball (f := Rb) (C := max K 1 * ‖b‖) (fun a ha => hball a ha b) a
  calc ‖a * b‖ = ‖Rb a‖ := rfl
    _ ≤ max K 1 * ‖b‖ * ‖a‖ := this
    _ = max K 1 * ‖a‖ * ‖b‖ := by ring

end Bounded

end Papers.EJA
