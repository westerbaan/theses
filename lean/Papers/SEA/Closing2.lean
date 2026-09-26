/-
Papers/SEA/Closing2.lean

Cleanup pass (2026-09-26), second round: SEA rows not graded `ok` closed by
new declarations, without touching the committed statements.

* **SEA 13** (second.tex:374, Example), second claim: `C(X)` is
  bounded-directed complete iff the compact Hausdorff space `X` is
  extremally disconnected (`sea13_CX`; cited from Gillman–Jerison in the
  print).  `⇐` scales a bounded directed family into `[0,1]_{C(X)}` and uses
  `Papers.OAP.exists_isLUB_Icc` (the construction behind
  `Papers.OAP.oap16_extremally`); `⇒` is
  `Papers.OAP.extremallyDisconnected_of_relSup`.
* **SEA 58** (`thm:a-convexthm`): the print's "maximal element", from the
  greatest element of `sea58_maximal_unconditional` (`sea58_as_printed`).
-/
import Papers.SEA.PureAConvex

set_option linter.unusedSectionVars false

namespace Papers.SEA

open Theses.B.Eff

universe u

/-! ## SEA 13, second claim: `C(X)` -/

section CX

variable {X : Type u} [TopologicalSpace X]

/-- The affine rescaling `f ↦ m⁻¹ (f - d₀)` used for `sea13_CX`. -/
private theorem cx_rescale_le_iff {m : ℝ} (hm : 0 < m) (d0 f y : C(X, ℝ)) :
    m⁻¹ • (f - d0) ≤ y ↔ f ≤ m • y + d0 := by
  simp only [ContinuousMap.le_def, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    ContinuousMap.add_apply, smul_eq_mul]
  refine forall_congr' fun x => ?_
  rw [inv_mul_le_iff₀ hm, sub_le_iff_le_add]

private theorem cx_le_rescale_iff {m : ℝ} (hm : 0 < m) (d0 f y : C(X, ℝ)) :
    y ≤ m⁻¹ • (f - d0) ↔ m • y + d0 ≤ f := by
  simp only [ContinuousMap.le_def, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    ContinuousMap.add_apply, smul_eq_mul]
  refine forall_congr' fun x => ?_
  rw [le_inv_mul_iff₀ hm, le_sub_iff_add_le]

/-- **SEA 13** (second.tex:374, Example), second claim: a commutative unital
C*-algebra `C(X)` (`X` compact Hausdorff) is bounded-directed complete — every
non-empty bounded directed set of self-adjoint elements, i.e. of real-valued
continuous functions, has a least upper bound — iff `X` is extremally
disconnected.  The print cites Gillman–Jerison 1H, 3N.6.  `⇐`: shift by an
element `d₀` of the set, scale into `[0,1]_{C(X)}`, and take the supremum
there (`Papers.OAP.exists_isLUB_Icc`, the argument of OAP 16); an upper bound
`w` is replaced by `w ⊓ b` for a fixed upper bound `b`.  `⇒`: the supremum of
the continuous functions in `[0,1]` vanishing off an open `U` is `1` on
`cl U` and `0` off it (`Papers.OAP.extremallyDisconnected_of_relSup`). -/
theorem sea13_CX [CompactSpace X] [T2Space X] :
    (∀ D : Set C(X, ℝ), D.Nonempty → DirectedOn (· ≤ ·) D → BddAbove D → ∃ s, IsLUB D s) ↔
      ExtremallyDisconnected X := by
  constructor
  · intro h
    refine Papers.OAP.extremallyDisconnected_of_relSup fun S hS hne hdir => ?_
    obtain ⟨s, hs⟩ := h S hne hdir ⟨1, fun f hf => (hS f hf).2⟩
    obtain ⟨f0, hf0⟩ := hne
    exact ⟨s, le_trans (hS f0 hf0).1 (hs.1 hf0), hs.2 fun f hf => (hS f hf).2,
      fun f hf => hs.1 hf, fun w _ _ hw => hs.2 fun f hf => hw f hf⟩
  · intro hED D hne hdir hbdd
    obtain ⟨d0, hd0⟩ := hne
    obtain ⟨b, hb⟩ := hbdd
    set m : ℝ := ‖b - d0‖ + 1 with hm_def
    have hm : 0 < m := by positivity
    have hφ : ∀ f : C(X, ℝ), d0 ≤ f → f ≤ b →
        m⁻¹ • (f - d0) ∈ Set.Icc (0 : C(X, ℝ)) 1 := by
      intro f h0 h1
      refine ⟨smul_nonneg (inv_nonneg.mpr hm.le) (sub_nonneg.mpr h0), ?_⟩
      rw [ContinuousMap.le_def]
      intro x
      simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul,
        ContinuousMap.one_apply]
      rw [inv_mul_le_iff₀ hm, mul_one]
      have h1x := ContinuousMap.le_def.1 h1 x
      have hn : (b - d0) x ≤ ‖b - d0‖ :=
        le_trans (le_abs_self _) (by
          simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm (b - d0) x)
      rw [ContinuousMap.sub_apply] at hn
      linarith
    let S : Set (Set.Icc (0 : C(X, ℝ)) 1) :=
      {y | ∃ d ∈ D, d0 ≤ d ∧ (y : C(X, ℝ)) = m⁻¹ • (d - d0)}
    have hSne : S.Nonempty := ⟨⟨_, hφ d0 le_rfl (hb hd0)⟩, d0, hd0, le_rfl, rfl⟩
    obtain ⟨g, hg⟩ := Papers.OAP.exists_isLUB_Icc S hSne fun r =>
      ExtremallyDisconnected.open_closure _
        (isOpen_biUnion fun f _ => isOpen_lt continuous_const (f : C(X, ℝ)).continuous)
    refine ⟨m • (g : C(X, ℝ)) + d0, fun d hd => ?_, fun w hw => ?_⟩
    · obtain ⟨e, he, hde, hd0e⟩ := hdir d hd d0 hd0
      have hmem : (⟨_, hφ e hd0e (hb he)⟩ : Set.Icc (0 : C(X, ℝ)) 1) ∈ S :=
        ⟨e, he, hd0e, rfl⟩
      have hle : m⁻¹ • (e - d0) ≤ (g : C(X, ℝ)) := Subtype.coe_le_coe.2 (hg.1 hmem)
      exact le_trans hde ((cx_rescale_le_iff hm d0 e g).1 hle)
    · have hd0w : d0 ≤ w ⊓ b := le_inf (hw hd0) (hb hd0)
      let y : Set.Icc (0 : C(X, ℝ)) 1 := ⟨_, hφ (w ⊓ b) hd0w inf_le_right⟩
      have hy : y ∈ upperBounds S := by
        rintro z ⟨d, hd, -, hz⟩
        show (z : C(X, ℝ)) ≤ m⁻¹ • (w ⊓ b - d0)
        rw [hz]
        exact smul_le_smul_of_nonneg_left
          (sub_le_sub_right (le_inf (hw hd) (hb hd)) _) (inv_nonneg.mpr hm.le)
      have hgy : (g : C(X, ℝ)) ≤ m⁻¹ • (w ⊓ b - d0) := Subtype.coe_le_coe.2 (hg.2 hy)
      exact le_trans ((cx_le_rescale_iff hm d0 _ _).1 hgy) inf_le_left

end CX

/-! ## SEA 58, as printed: a maximal element -/

section SEA58

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

/-- **SEA 58** (`thm:a-convexthm`, second.tex:1768, Theorem), as printed: in
a normal SEA the set `S` of idempotents `p` for which `p ⊙ E` carries an
a-convex action has a maximal element `p₀`, which is central, with
`p₀⊥ ⊙ E` Boolean.  From the greatest element of
`sea58_maximal_unconditional` (antisymmetry). -/
theorem sea58_as_printed :
    ∃ p0 : E, (IsIdempotent p0 ∧ IsAConvex (Downset p0)) ∧
      (∀ q : E, IsIdempotent q → IsAConvex (Downset q) → p0 ≼ q → q = p0) ∧
      IsCentral p0 ∧ IsBooleanIdempotent (orth p0) := by
  obtain ⟨p0, h1, h2, h3, h4⟩ := sea58_maximal_unconditional (E := E)
  exact ⟨p0, h1, fun q hq ha hle => eabasics_le_antisymm (h2 q hq ha) hle, h3, h4⟩

end SEA58

end Papers.SEA
