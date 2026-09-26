/-
Papers/FDS/Closing2.lean

Cleanup pass (2026-09-26): FDS 2.4 for arbitrary (possibly non-unital)
C*-algebras.

* **FDS 2.4** (`rep_ex`): `DirectSums.lean` takes Mathlib's (unital)
  `CStarAlgebra`, where the non-degenerate representations are the unital
  ones.  Here the print's statement for a general C*-algebra
  (`NonUnitalCStarAlgebra`): the non-degenerate `*`-representations
  (`π(𝒜)H` spans a dense subspace, `NDRepObj.IsNondeg`) with the intertwiners
  form a W*-category (`ndRep_wStarCategory`).  Non-degeneracy is equivalent
  to "no non-zero vector is killed by every `π(a)`"
  (`NDRepObj.isNondeg_iff`), which is what makes it closed under `⊕`.
-/
import Papers.FDS.DirectSums

open CategoryTheory
open Theses Theses.A.VN Theses.B.Dils

universe u u₁

namespace Papers.FDS

noncomputable section

section NDReps

variable (𝒜 : Type u₁) [NonUnitalCStarAlgebra 𝒜]

/-- A (not necessarily unital, not necessarily non-degenerate)
`*`-representation of the C*-algebra `𝒜` on a Hilbert space. -/
structure NDRepObj : Type (max u₁ (u + 1)) where
  /-- the Hilbert space -/
  hs : HilbObj.{u}
  /-- the representation -/
  π : 𝒜 →⋆ₙₐ[ℂ] (hs →L[ℂ] hs)

variable {𝒜}

/-- Non-degeneracy: the vectors `π(a) x` span a dense subspace. -/
def NDRepObj.IsNondeg (X : NDRepObj.{u} 𝒜) : Prop :=
  (Submodule.span ℂ (⋃ a, Set.range (X.π a))).topologicalClosure = ⊤

/-- Non-degeneracy is the absence of a non-zero vector killed by all `π(a)`:
the orthogonal complement of `π(𝒜)H` is the common kernel of the `π(a*)`. -/
theorem NDRepObj.isNondeg_iff (X : NDRepObj.{u} 𝒜) :
    X.IsNondeg ↔ ∀ x : X.hs, (∀ a, X.π a x = 0) → x = 0 := by
  have hmem : ∀ x : X.hs, x ∈ (Submodule.span ℂ (⋃ a, Set.range (X.π a)))ᗮ ↔
      ∀ a, X.π a x = 0 := by
    intro x
    constructor
    · intro hx a
      have h : ∀ y, inner ℂ y (X.π a x) = 0 := by
        intro y
        rw [← star_star a, map_star, ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right]
        have hy : X.π (star a) y ∈ ⋃ b, Set.range (X.π b) :=
          Set.mem_iUnion.2 ⟨star a, Set.mem_range_self y⟩
        exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span hy) hx
      have h' := h (X.π a x)
      rwa [inner_self_eq_zero] at h'
    · intro hx
      rw [Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, y, rfl⟩ := Set.mem_iUnion.1 hv
        rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
          ← map_star, hx, inner_zero_right]
      | zero => exact inner_zero_left _
      | add v w _ _ hv hw => rw [inner_add_left, hv, hw, add_zero]
      | smul c v _ hv => rw [inner_smul_left, hv, mul_zero]
  rw [NDRepObj.IsNondeg, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  exact forall_congr' fun x => by rw [hmem]

/-- The intertwiners `f π₁(a) = π₂(a) f`. -/
def ndIntertwiners (X Y : NDRepObj.{u} 𝒜) : Submodule ℂ (X.hs →L[ℂ] Y.hs) where
  carrier := {f | ∀ a, f.comp (X.π a) = (Y.π a).comp f}
  add_mem' {f g} hf hg a := by
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hf a, hg a]
  zero_mem' a := by rw [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  smul_mem' c f hf a := by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hf a]

theorem isClosed_ndIntertwiners (X Y : NDRepObj.{u} 𝒜) :
    IsClosed (ndIntertwiners X Y : Set (X.hs →L[ℂ] Y.hs)) := by
  have h : (ndIntertwiners X Y : Set (X.hs →L[ℂ] Y.hs))
      = ⋂ a, {f | f.comp (X.π a) = (Y.π a).comp f} := by
    ext f; simp [ndIntertwiners]
  rw [h]
  exact isClosed_iInter fun a =>
    isClosed_eq (continuous_id.clm_comp continuous_const) (continuous_const.clm_comp continuous_id)

theorem adjoint_mem_ndIntertwiners {X Y : NDRepObj.{u} 𝒜} {f : X.hs →L[ℂ] Y.hs}
    (hf : f ∈ ndIntertwiners X Y) : ContinuousLinearMap.adjoint f ∈ ndIntertwiners Y X := by
  intro a
  have h := congrArg ContinuousLinearMap.adjoint (hf (star a))
  simp only [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
    star_star] at h
  exact h.symm

variable (𝒜) in
/-- The concrete data of the category of representations of `𝒜` satisfying
`P`, with the intertwiners as morphisms. -/
def ndRepData (P : NDRepObj.{u} 𝒜 → Prop) : ConcreteStarCat.{u} {X : NDRepObj.{u} 𝒜 // P X} where
  hs X := X.1.hs
  hom X Y := ndIntertwiners X.1 Y.1
  isClosed_hom X Y := isClosed_ndIntertwiners X.1 Y.1
  id_mem X a := by rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  comp_mem {X Y Z f g} hf hg a := by
    rw [ContinuousLinearMap.comp_assoc, hf a, ← ContinuousLinearMap.comp_assoc, hg a,
      ContinuousLinearMap.comp_assoc]
  adjoint_mem hf := adjoint_mem_ndIntertwiners hf

/-- The endomorphisms of a representation form a von Neumann subalgebra of
`B(H)` (the commutant of `π(𝒜)`; theses **44XIII** `vna_supremum_commutes`). -/
theorem ndRep_isVNSubalgebra (P : NDRepObj.{u} 𝒜 → Prop) (X : (ndRepData 𝒜 P).Obj) :
    IsVNSubalgebra _ ((ndRepData 𝒜 P).endSubalgebra X) where
  isClosed := (ndRepData 𝒜 P).isClosed_endSubalgebra X
  dirSup_mem D s hD hne hdir hlub := by
    show ∀ a, (s.1 : X.1.hs →L[ℂ] X.1.hs).comp (X.1.π a)
      = (X.1.π a).comp (s.1 : X.1.hs →L[ℂ] X.1.hs)
    intro a
    have hbdd : BddAbove D := ⟨s, hlub.1⟩
    have h := vna_supremum_commutes D ⟨hne, hdir, hbdd⟩ (X.1.π a)
      (fun d hd => (hD d hd a).symm)
    have hs : dirSup D ⟨hne, hdir, hbdd⟩ = s := (isLUB_dirSup D _).unique hlub
    rw [hs] at h
    exact h.symm

/-- The direct sum `π₁ ⊕ π₂` of two representations. -/
def ndProdRep (X Y : NDRepObj.{u} 𝒜) : 𝒜 →⋆ₙₐ[ℂ] (X.hs.prod Y.hs →L[ℂ] X.hs.prod Y.hs) where
  toFun a := blockDiag (X.π a) (Y.π a)
  map_smul' c a := by
    show blockDiag (X.π (c • a)) (Y.π (c • a)) = c • blockDiag (X.π a) (Y.π a)
    rw [map_smul, map_smul]; exact blockDiag_smul _ _ _
  map_zero' := by
    show blockDiag (X.π 0) (Y.π 0) = 0
    rw [map_zero, map_zero]; exact blockDiag_zero
  map_add' a b := by
    show blockDiag (X.π (a + b)) (Y.π (a + b)) = blockDiag (X.π a) (Y.π a) + blockDiag (X.π b) (Y.π b)
    rw [map_add, map_add]; exact blockDiag_add _ _ _ _
  map_mul' a b := by
    show blockDiag (X.π (a * b)) (Y.π (a * b)) = blockDiag (X.π a) (Y.π a) * blockDiag (X.π b) (Y.π b)
    rw [map_mul, map_mul]; exact blockDiag_mul _ _ _ _
  map_star' a := by
    show blockDiag (X.π (star a)) (Y.π (star a)) = star (blockDiag (X.π a) (Y.π a))
    rw [map_star, map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      adjoint_blockDiag]

/-- The direct sum of two representations. -/
def NDRepObj.prod (X Y : NDRepObj.{u} 𝒜) : NDRepObj.{u} 𝒜 := ⟨X.hs.prod Y.hs, ndProdRep X Y⟩

/-- The direct sum of two non-degenerate representations is non-degenerate. -/
theorem NDRepObj.IsNondeg.prod {X Y : NDRepObj.{u} 𝒜} (hX : X.IsNondeg) (hY : Y.IsNondeg) :
    (X.prod Y).IsNondeg := by
  rw [NDRepObj.isNondeg_iff] at hX hY ⊢
  intro z hz
  have h1 : (WithLp.ofLp (z : WithLp 2 (X.hs × Y.hs))).1 = 0 := hX _ fun a => by
    have : X.π a (WithLp.ofLp (z : WithLp 2 (X.hs × Y.hs))).1
        = (WithLp.ofLp (0 : WithLp 2 (X.hs × Y.hs))).1 :=
      congrArg (fun w : WithLp 2 (X.hs × Y.hs) => (WithLp.ofLp w).1) (hz a)
    simpa using this
  have h2 : (WithLp.ofLp (z : WithLp 2 (X.hs × Y.hs))).2 = 0 := hY _ fun a => by
    have : Y.π a (WithLp.ofLp (z : WithLp 2 (X.hs × Y.hs))).2
        = (WithLp.ofLp (0 : WithLp 2 (X.hs × Y.hs))).2 :=
      congrArg (fun w : WithLp 2 (X.hs × Y.hs) => (WithLp.ofLp w).2) (hz a)
    simpa using this
  rw [inl_add_inr z, h1, h2, map_zero, map_zero, add_zero]
  rfl

theorem inl_mem_ndIntertwiners (X Y : NDRepObj.{u} 𝒜) :
    inlCLM X.hs Y.hs ∈ ndIntertwiners X (X.prod Y) := fun a =>
  inlCLM_comp_eq (X.π a) (Y.π a)

theorem inr_mem_ndIntertwiners (X Y : NDRepObj.{u} 𝒜) :
    inrCLM X.hs Y.hs ∈ ndIntertwiners Y (X.prod Y) := fun a =>
  inrCLM_comp_eq (X.π a) (Y.π a)

/-- A concrete category of representations closed under binary direct sums
is a W*-category. -/
theorem ndRepData_wStarCategory (P : NDRepObj.{u} 𝒜 → Prop)
    (hP : ∀ X Y, P X → P Y → P (X.prod Y)) : WStarCategory (ndRepData 𝒜 P).Obj :=
  ConcreteStarCat.wStarCategory_of (ndRep_isVNSubalgebra P) fun X Y =>
    ⟨(⟨X.1.prod Y.1, hP _ _ X.2 Y.2⟩ : {X : NDRepObj 𝒜 // P X}),
      ⟨inlCLM X.1.hs Y.1.hs, inl_mem_ndIntertwiners X.1 Y.1⟩,
      ⟨inrCLM X.1.hs Y.1.hs, inr_mem_ndIntertwiners X.1 Y.1⟩,
      (ConcreteStarCat.isIsometry_iff _).mpr (norm_inlCLM X.1.hs Y.1.hs),
      (ConcreteStarCat.isIsometry_iff _).mpr (norm_inrCLM X.1.hs Y.1.hs)⟩

variable (𝒜) in
/-- **FDS 2.4** (`rep_ex`, direct_sums.tex:301): the category `Rep 𝒜` of
non-degenerate representations of a (possibly non-unital) C*-algebra `𝒜` on
Hilbert spaces, with the intertwiners as morphisms. -/
abbrev NDRep := (ndRepData.{u} 𝒜 NDRepObj.IsNondeg).Obj

/-- **FDS 2.4** (`rep_ex`, direct_sums.tex:301, Example), for an arbitrary
C*-algebra: the category of non-degenerate representations of `𝒜` with the
intertwiners is a W*-category, with the operator norm and the Hermitian
adjoint.  (`rep_wStarCategory` is the unital case.) -/
instance ndRep_wStarCategory : WStarCategory (NDRep.{u} 𝒜) :=
  ndRepData_wStarCategory _ fun _ _ hX hY => hX.prod hY

end NDReps

end

end Papers.FDS
