/-
Thesis A, chapter "Assorted Structure in W*_cpsu" (proc.tex): the
**structural unitaries** of the Hilbert space tensor product (flip and
associator), the identification `B(ℋ) ⊗̄ B(𝒦) = B(ℋ ⊗ 𝒦)`, and the
**transport of von Neumann subalgebras, commutants, `concreteTensor` and
the commutation theorem `CT` along a unitary**.

None of this has a numbered counterpart in `proc.tex`; it is the tensor
plumbing that `docs/COMMUTATION-THEOREM.md` §4 costs as part of the row
"amplification theorem, `B(L₁)⊗̄B(L₂) = B(L₁⊗L₂)`, flip/associator
transport".

## Encoding

* A **unitary** `U : ℋ → ℋ'` is `IsCorner U (1 : ℋ' →L[ℂ] ℋ')`, i.e.
  `U^* U = 1` and `U U^* = 1`.  This is not a coincidence of encoding:
  the corner calculus of `A/Proc/CornerTensor.lean` (`cmpr`, `cext` and
  their ∗-algebra laws) is exactly the conjugation calculus at `e = 1`,
  so `cext U x = U x U^*` inherits multiplicativity, unitality
  (`cext_one` at `e = 1`), star-preservation and injectivity for free,
  and `cext_cmpr` at `e = 1` gives surjectivity.
* Conjugation of a von Neumann subalgebra is `uconj hU S`, the *image*
  `U S U^*`.  That it is again a von Neumann subalgebra is proved
  **algebraically**, through the bicommutant: conjugation commutes with
  `vnComm` (`vnComm_uconj`), so `U S U^* = (U S^□ U^*)^□` for a von
  Neumann `S`, and commutants are von Neumann subalgebras (65III).  No
  ultraweak continuity of `x ↦ U x U^*` is needed.
* `CT_top_right` reads the amplification theorem as an instance of `CT`:
  the commutation theorem holds whenever one factor is the *whole* of
  `B(𝒦)`.  Its only new ingredient beyond `amplification'` is
  `mem_vnComm_top` — that the commutant of `B(ℋ)` is the scalars, which
  the tree did not have and which `concreteTensor_top_top` needs too.
* The flip and the associator are obtained from `hilb_tensor_unique`
  (110V) rather than from `hilb_tensor_universal_property` (110III)
  directly: the point in each case is that a *rearranged* bilinear map
  is again an `IsHilbertTensorProduct`, after which 110V supplies the
  isometric isomorphism, and `LinearIsometryEquiv.adjoint_eq_symm` turns
  it into a unitary in the above sense.  For the flip the rearranged map
  is literally `LinearMap.flip (hilbTensor 𝒦 ℋ).map`; for the associator
  it is `(u, z) ↦ (1 ⊗ Q_z) u`, built out of the ket operators
  `htKet` of `A/Proc/Tensor.lean`, whose composition rule
  `Q_z^* Q_{z'} = ⟨z,z'⟩·1` is exactly the inner-product clause.
-/
import Theses.A.Proc.CornerTensor

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
  TensorProduct ENNReal
open Filter Topology Theses Theses.A.VN

noncomputable section

namespace Theses.A.Proc

universe u

/-! ## Auxiliaries for the Hilbert space tensor product -/

section HilbertAux

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Companion of `htmul_add_left`: `x ⊗ (y + y') = x ⊗ y + x ⊗ y'`. -/
theorem htmul_add_right (x : H) (y y' : K) :
    x ⊗ₕ (y + y') = x ⊗ₕ y + x ⊗ₕ y' := by
  show (hilbTensor H K).map x (y + y') = _
  rw [map_add]; rfl

/-- The **left ket** operator `x ⊗ |·⟩ : 𝒦 → ℋ ⊗ 𝒦`, `y ↦ x ⊗ y`; the
mirror of `htKet`. -/
def htKetL (x : H) : K →L[ℂ] HT H K :=
  LinearMap.mkContinuous
    { toFun := fun y => x ⊗ₕ y
      map_add' := fun y y' => htmul_add_right x y y'
      map_smul' := fun c y => htmul_smul_right c x y } ‖x‖
    (fun y => by
      show ‖x ⊗ₕ y‖ ≤ ‖x‖ * ‖y‖
      rw [norm_htmul])

@[simp] theorem htKetL_apply (x : H) (y : K) : htKetL (K := K) x y = x ⊗ₕ y := rfl

end HilbertAux

/-! ## Unitaries, and conjugation by a unitary

A unitary `U : ℋ → ℋ'` is a corner realisation of the projection `1`;
`cext U x = U x U^*` and `cmpr U y = U^* y U` are then mutually inverse
∗-isomorphisms `B(ℋ) ≅ B(ℋ')`. -/

section Unitary

variable {H H' : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- `IsUnitaryCLM U` says that `U : ℋ → ℋ'` is a unitary: `U^* U = 1` and
`U U^* = 1`.  It is definitionally `IsCorner U 1`, so the whole `cmpr` /
`cext` calculus applies. -/
abbrev IsUnitaryCLM (U : H →L[ℂ] H') : Prop := IsCorner U (1 : H' →L[ℂ] H')

/-- A surjective linear isometry is a unitary. -/
theorem isUnitaryCLM_of_linearIsometryEquiv (φ : H ≃ₗᵢ[ℂ] H') :
    IsUnitaryCLM (φ : H →L[ℂ] H') := by
  have hadj : ContinuousLinearMap.adjoint (φ : H →L[ℂ] H') = (φ.symm : H' →L[ℂ] H) :=
    φ.adjoint_eq_symm
  constructor
  · rw [hadj]
    exact ContinuousLinearMap.ext fun v => φ.symm_apply_apply v
  · rw [hadj]
    exact ContinuousLinearMap.ext fun v => φ.apply_symm_apply v

variable {U : H →L[ℂ] H'} (hU : IsUnitaryCLM U)

include hU

/-- For a unitary `U`, conjugation `x ↦ U x U^*` is inverse to
`y ↦ U^* y U` on the *whole* of `B(ℋ')` (not merely on a corner). -/
theorem ucext_cmpr (x : H' →L[ℂ] H') : cext U (cmpr U x) = x := by
  rw [cext_cmpr hU, one_mul, mul_one]

theorem ucext_one : cext U (1 : H →L[ℂ] H) = 1 := cext_one hU

theorem ucmpr_mul (x x' : H' →L[ℂ] H') :
    cmpr U (x * x') = cmpr U x * cmpr U x' := by
  have h := cmpr_mul_mid hU x x'
  rwa [mul_one] at h

/-- The adjoint of a unitary is a unitary. -/
theorem IsUnitaryCLM.adjoint : IsUnitaryCLM (ContinuousLinearMap.adjoint U) := by
  constructor
  · rw [ContinuousLinearMap.adjoint_adjoint]; exact hU.comp_adjoint
  · rw [ContinuousLinearMap.adjoint_adjoint]; exact hU.adjoint_comp

end Unitary

section Conj

variable {H H' : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {U : H →L[ℂ] H'}

/-- Conjugation by the adjoint is compression by `U`, and vice versa. -/
theorem cext_adjoint (y : H' →L[ℂ] H') :
    cext (ContinuousLinearMap.adjoint U) y = cmpr U y := by
  show ContinuousLinearMap.adjoint U ∘L y ∘L
      ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint U) = _
  rw [ContinuousLinearMap.adjoint_adjoint]; rfl

theorem cmpr_adjoint (x : H →L[ℂ] H) :
    cmpr (ContinuousLinearMap.adjoint U) x = cext U x := by
  show ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint U) ∘L x ∘L
      ContinuousLinearMap.adjoint U = _
  rw [ContinuousLinearMap.adjoint_adjoint]; rfl

/-- **Conjugation of a ∗-subalgebra by a unitary**: `U 𝒜 U^*`. -/
def uconj (hU : IsUnitaryCLM U) (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (H' →L[ℂ] H') where
  carrier := cext U '' (S : Set (H →L[ℂ] H))
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, mul_mem hx hy, cext_mul hU x y⟩
  one_mem' := ⟨1, one_mem S, ucext_one hU⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, add_mem hx hy, cext_add U x y⟩
  zero_mem' := ⟨0, zero_mem S, cext_zero U⟩
  algebraMap_mem' := fun c => ⟨algebraMap ℂ (H →L[ℂ] H) c, S.algebraMap_mem c, by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, cext_smul,
      ucext_one hU]⟩
  star_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨star x, star_mem hx, cext_star U x⟩

variable (hU : IsUnitaryCLM U)

include hU

theorem mem_uconj {S : StarSubalgebra ℂ (H →L[ℂ] H)} {y : H' →L[ℂ] H'} :
    y ∈ uconj hU S ↔ cmpr U y ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [cmpr_cext hU]
  · intro hy
    exact ⟨cmpr U y, hy, ucext_cmpr hU y⟩

theorem cext_mem_uconj {S : StarSubalgebra ℂ (H →L[ℂ] H)} {x : H →L[ℂ] H}
    (hx : x ∈ S) : cext U x ∈ uconj hU S := ⟨x, hx, rfl⟩

theorem coe_uconj (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (uconj hU S : Set (H' →L[ℂ] H')) = cext U '' (S : Set (H →L[ℂ] H)) := rfl

theorem uconj_mono {S T : StarSubalgebra ℂ (H →L[ℂ] H)} (h : S ≤ T) :
    uconj hU S ≤ uconj hU T := by
  intro y hy
  rw [mem_uconj hU] at hy ⊢
  exact h hy

/-- Conjugating by `U` and then by `U^*` is the identity. -/
theorem uconj_uconj_adjoint (T : StarSubalgebra ℂ (H' →L[ℂ] H')) :
    uconj hU (uconj hU.adjoint T) = T := by
  refine SetLike.ext fun y => ?_
  rw [mem_uconj hU, mem_uconj hU.adjoint, cmpr_adjoint, ucext_cmpr hU]

theorem uconj_adjoint_uconj (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    uconj hU.adjoint (uconj hU S) = S := by
  refine SetLike.ext fun x => ?_
  rw [mem_uconj hU.adjoint, mem_uconj hU, cmpr_adjoint, cmpr_cext hU]

theorem uconj_le_iff {S T : StarSubalgebra ℂ (H →L[ℂ] H)} :
    uconj hU S ≤ uconj hU T ↔ S ≤ T := by
  refine ⟨fun h => ?_, uconj_mono hU⟩
  have h2 := uconj_mono hU.adjoint h
  rwa [uconj_adjoint_uconj hU, uconj_adjoint_uconj hU] at h2

@[simp] theorem uconj_top : uconj hU (⊤ : StarSubalgebra ℂ (H →L[ℂ] H)) = ⊤ := by
  refine SetLike.ext fun y => ?_
  simp [mem_uconj hU]

/-- **Conjugation commutes with the commutant.** -/
theorem vnComm_uconj (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    vnComm (uconj hU S) = uconj hU (vnComm S) := by
  refine SetLike.ext fun y => ?_
  rw [mem_uconj hU, mem_vnComm, mem_vnComm]
  constructor
  · intro hy x hx
    have h := hy (cext U x) (cext_mem_uconj hU hx)
    have h2 := congrArg (cmpr U) h
    rwa [ucmpr_mul hU, ucmpr_mul hU, cmpr_cext hU] at h2
  · intro hy s hs
    rw [mem_uconj hU] at hs
    have h := hy (cmpr U s) hs
    have h2 := congrArg (cext U) h
    simp only [cext_mul hU, ucext_cmpr hU] at h2
    exact h2

/-- **Conjugation carries von Neumann subalgebras to von Neumann
subalgebras** — proved through the bicommutant, with no continuity
argument. -/
theorem isVNSubalgebra_uconj {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hS : IsVNSubalgebra (H →L[ℂ] H) S) :
    IsVNSubalgebra (H' →L[ℂ] H') (uconj hU S) := by
  have h : uconj hU S = vnComm (uconj hU (vnComm S)) := by
    rw [vnComm_uconj hU, vnComm_vnComm S hS]
  rw [h]
  exact isVNSubalgebra_vnComm _

/-- **Conjugation commutes with `W*(-)`.** -/
theorem uconj_wstar (G : Set (H →L[ℂ] H)) :
    uconj hU (wstar (H →L[ℂ] H) G) = wstar (H' →L[ℂ] H') (cext U '' G) := by
  refine le_antisymm ?_ ?_
  · -- transport the minimality of `W*(cext U '' G)` back along `U^*`
    have hle : wstar (H →L[ℂ] H) G ≤ uconj hU.adjoint (wstar (H' →L[ℂ] H') (cext U '' G)) := by
      refine sInf_le ⟨isVNSubalgebra_uconj hU.adjoint (isVNSubalgebra_wstar _).1, ?_⟩
      intro g hg
      rw [SetLike.mem_coe, mem_uconj hU.adjoint, cmpr_adjoint]
      exact (isVNSubalgebra_wstar _).2 ⟨g, hg, rfl⟩
    have h2 := uconj_mono hU hle
    rwa [uconj_uconj_adjoint hU] at h2
  · refine sInf_le ⟨isVNSubalgebra_uconj hU (isVNSubalgebra_wstar _).1, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact cext_mem_uconj hU ((isVNSubalgebra_wstar _).2 hg)

end Conj

/-! ## The flip `ℋ ⊗ 𝒦 ≃ 𝒦 ⊗ ℋ` -/

section Flip

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (H K) in
/-- The flipped bilinear map `(x,y) ↦ y ⊗ x : ℋ × 𝒦 → 𝒦 ⊗ ℋ` is again a
tensor product of Hilbert spaces (109II): it has the same range as
`⊗ : 𝒦 × ℋ → 𝒦 ⊗ ℋ`, and its inner products factorise the same way. -/
theorem isHilbertTensorProduct_flip :
    IsHilbertTensorProduct
      ((hilbTensor K H).map.flip : H →ₗ[ℂ] K →ₗ[ℂ] HT K H) := by
  constructor
  · have hset : {t : HT K H | ∃ (x : H) (y : K), t = (hilbTensor K H).map.flip x y}
        = {t : HT K H | ∃ (y : K) (x : H), t = (hilbTensor K H).map y x} := by
      ext t
      exact ⟨fun ⟨x, y, h⟩ => ⟨y, x, h⟩, fun ⟨y, x, h⟩ => ⟨x, y, h⟩⟩
    rw [hset]
    exact (hilbTensor K H).isTensor.dense
  · intro x x' y y'
    show ⟪(hilbTensor K H).map y x, (hilbTensor K H).map y' x'⟫ = _
    rw [(hilbTensor K H).isTensor.inner_mul]
    ring

variable (H K) in
/-- **The flip unitary** `ℋ ⊗ 𝒦 ≃ 𝒦 ⊗ ℋ`, `x ⊗ y ↦ y ⊗ x`. -/
def htFlipEquiv : HT H K ≃ₗᵢ[ℂ] HT K H :=
  (hilb_tensor_unique (hilbTensor H K).map ((hilbTensor K H).map.flip)
    (hilbTensor H K).isTensor (isHilbertTensorProduct_flip H K)).choose

@[simp] theorem htFlipEquiv_htmul (x : H) (y : K) :
    htFlipEquiv H K (x ⊗ₕ y) = y ⊗ₕ x :=
  (hilb_tensor_unique (hilbTensor H K).map ((hilbTensor K H).map.flip)
    (hilbTensor H K).isTensor (isHilbertTensorProduct_flip H K)).choose_spec.1 x y

@[simp] theorem htFlipEquiv_symm_htmul (x : H) (y : K) :
    (htFlipEquiv H K).symm (y ⊗ₕ x) = x ⊗ₕ y := by
  rw [← htFlipEquiv_htmul x y, LinearIsometryEquiv.symm_apply_apply]

variable (H K) in
/-- The flip as a continuous linear map. -/
def htFlip : HT H K →L[ℂ] HT K H := (htFlipEquiv H K : HT H K →L[ℂ] HT K H)

@[simp] theorem htFlip_htmul (x : H) (y : K) : htFlip H K (x ⊗ₕ y) = y ⊗ₕ x :=
  htFlipEquiv_htmul x y

variable (H K) in
theorem isUnitaryCLM_htFlip : IsUnitaryCLM (htFlip H K) :=
  isUnitaryCLM_of_linearIsometryEquiv (htFlipEquiv H K)

theorem adjoint_htFlip_htmul (x : H) (y : K) :
    ContinuousLinearMap.adjoint (htFlip H K) (y ⊗ₕ x) = x ⊗ₕ y := by
  have h : ContinuousLinearMap.adjoint (htFlip H K)
      = ((htFlipEquiv H K).symm : HT K H →L[ℂ] HT H K) :=
    (htFlipEquiv H K).adjoint_eq_symm
  rw [h]
  exact htFlipEquiv_symm_htmul x y

/-- **The flip on operators**: conjugating `a ⊗ b` by the flip gives
`b ⊗ a`. -/
theorem cext_htFlip_opTensor (a : H →L[ℂ] H) (b : K →L[ℂ] K) :
    cext (htFlip H K) (opTensor a b) = opTensor b a := by
  refine ext_htmul fun y x => ?_
  rw [cext_apply, adjoint_htFlip_htmul, opTensor_apply, opTensor_apply, htFlip_htmul]

end Flip

/-! ## The associator `(ℋ ⊗ 𝒦) ⊗ ℒ ≃ ℋ ⊗ (𝒦 ⊗ ℒ)`

The rearranged bilinear map is `(u, z) ↦ (1 ⊗ Q_z) u`, where
`Q_z : 𝒦 → 𝒦 ⊗ ℒ` is the ket operator `htKet` of `A/Proc/Tensor.lean`.
Its inner-product clause is *exactly* the composition rule
`Q_z^* Q_{z'} = ⟨z,z'⟩·1` (`htKet_adjoint_comp`), pushed through
`opTensor_comp` and `opTensor_adjoint'`; no orthonormal basis and no
convergence argument appear. -/

section Assoc

variable {H K L : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem htKet_add (z z' : K) :
    htKet (H := H) (z + z') = htKet (H := H) z + htKet (H := H) z' :=
  ContinuousLinearMap.ext fun x => htmul_add_right x z z'

theorem htKet_smul (c : ℂ) (z : K) :
    htKet (H := H) (c • z) = c • htKet (H := H) z :=
  ContinuousLinearMap.ext fun x => htmul_smul_right c x z

variable (H K L) in
/-- The rearranged bilinear map `(u, z) ↦ (1 ⊗ Q_z) u` of the
associator; on elementary tensors it is `(x ⊗ y, z) ↦ x ⊗ (y ⊗ z)`. -/
def htAssocMap : HT H K →ₗ[ℂ] L →ₗ[ℂ] HT H (HT K L) :=
  LinearMap.mk₂ ℂ (fun u z => opTensor (1 : H →L[ℂ] H) (htKet z) u)
    (fun u u' z => map_add _ u u')
    (fun c u z => map_smul _ c u)
    (fun u z z' => by
      rw [htKet_add, opTensor_add_right]; rfl)
    (fun c u z => by
      rw [htKet_smul, opTensor_smul_right]; rfl)

theorem htAssocMap_apply (u : HT H K) (z : L) :
    htAssocMap H K L u z = opTensor (1 : H →L[ℂ] H) (htKet z) u := rfl

theorem htAssocMap_htmul (x : H) (y : K) (z : L) :
    htAssocMap H K L (x ⊗ₕ y) z = x ⊗ₕ (y ⊗ₕ z) := by
  rw [htAssocMap_apply, opTensor_apply]
  rfl

variable (H K L) in
/-- `(u, z) ↦ (1 ⊗ Q_z) u` is a tensor product of Hilbert spaces
(109II). -/
theorem isHilbertTensorProduct_htAssocMap :
    IsHilbertTensorProduct (htAssocMap H K L) := by
  constructor
  · -- Density.  The range spans everything of the form `x ⊗ (y ⊗ z)`; for
    -- fixed `x` the *closed* preimage of the closure under `w ↦ x ⊗ w`
    -- contains the elementary tensors of `𝒦 ⊗ ℒ`, hence all of `𝒦 ⊗ ℒ`.
    set G : Set (HT H (HT K L)) :=
      {t : HT H (HT K L) | ∃ u z, t = htAssocMap H K L u z} with hG
    set C : Submodule ℂ (HT H (HT K L)) := (Submodule.span ℂ G).topologicalClosure with hC
    have hCcl : IsClosed (C : Set (HT H (HT K L))) :=
      (Submodule.span ℂ G).isClosed_topologicalClosure
    have hGmem : ∀ (x : H) (y : K) (z : L), x ⊗ₕ (y ⊗ₕ z) ∈ C := by
      intro x y z
      refine Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)
      exact ⟨x ⊗ₕ y, z, (htAssocMap_htmul x y z).symm⟩
    have hxw : ∀ (x : H) (w : HT K L), x ⊗ₕ w ∈ C := by
      intro x
      set P : Submodule ℂ (HT K L) :=
        C.comap ((htKetL (K := HT K L) x : HT K L →L[ℂ] HT H (HT K L)) :
          HT K L →ₗ[ℂ] HT H (HT K L)) with hP
      have hPcl : IsClosed (P : Set (HT K L)) :=
        hCcl.preimage (htKetL (K := HT K L) x).continuous
      have hspan : Submodule.span ℂ {t : HT K L | ∃ y z, t = (hilbTensor K L).map y z}
          ≤ P := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨y, z, rfl⟩
        exact hGmem x y z
      have hdense : Dense (P : Set (HT K L)) :=
        Dense.mono (SetLike.coe_subset_coe.2 hspan) (hilbTensor K L).isTensor.dense
      have huniv : (P : Set (HT K L)) = Set.univ := by
        rw [← hPcl.closure_eq, hdense.closure_eq]
      intro w
      have : w ∈ (P : Set (HT K L)) := by rw [huniv]; trivial
      exact this
    have hle : Submodule.span ℂ
        {t : HT H (HT K L) | ∃ x w, t = (hilbTensor H (HT K L)).map x w} ≤ C := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, w, rfl⟩
      exact hxw x w
    have hCdense : Dense (C : Set (HT H (HT K L))) :=
      Dense.mono (SetLike.coe_subset_coe.2 hle) (hilbTensor H (HT K L)).isTensor.dense
    rw [hC] at hCdense
    rw [Submodule.topologicalClosure_coe] at hCdense
    exact dense_closure.mp hCdense
  · intro u u' z z'
    have hcomp : (ContinuousLinearMap.adjoint
          (opTensor (1 : H →L[ℂ] H) (htKet (H := K) z))).comp
        (opTensor (1 : H →L[ℂ] H) (htKet (H := K) z'))
        = (⟪z, z'⟫ : ℂ) • (1 : HT H K →L[ℂ] HT H K) := by
      rw [opTensor_adjoint', opTensor_comp, htKet_adjoint_comp,
        ContinuousLinearMap.adjoint_one]
      rw [show ((1 : H →L[ℂ] H) ∘L (1 : H →L[ℂ] H)) = 1 from rfl]
      rw [opTensor_smul_right, opTensor_one]
    have h := congrArg (fun T : HT H K →L[ℂ] HT H K => T u') hcomp
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      FunLike.coe_smul, Pi.smul_apply, one_apply_eq_self] at h
    show ⟪opTensor (1 : H →L[ℂ] H) (htKet z) u,
      opTensor (1 : H →L[ℂ] H) (htKet z') u'⟫ = _
    rw [← ContinuousLinearMap.adjoint_inner_right, h, inner_smul_right]
    ring

variable (H K L) in
/-- **The associator unitary** `(ℋ ⊗ 𝒦) ⊗ ℒ ≃ ℋ ⊗ (𝒦 ⊗ ℒ)`,
`(x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z)`. -/
def htAssocEquiv : HT (HT H K) L ≃ₗᵢ[ℂ] HT H (HT K L) :=
  (hilb_tensor_unique (hilbTensor (HT H K) L).map (htAssocMap H K L)
    (hilbTensor (HT H K) L).isTensor (isHilbertTensorProduct_htAssocMap H K L)).choose

theorem htAssocEquiv_apply (u : HT H K) (z : L) :
    htAssocEquiv H K L (u ⊗ₕ z) = opTensor (1 : H →L[ℂ] H) (htKet z) u :=
  (hilb_tensor_unique (hilbTensor (HT H K) L).map (htAssocMap H K L)
    (hilbTensor (HT H K) L).isTensor
      (isHilbertTensorProduct_htAssocMap H K L)).choose_spec.1 u z

@[simp] theorem htAssocEquiv_htmul (x : H) (y : K) (z : L) :
    htAssocEquiv H K L ((x ⊗ₕ y) ⊗ₕ z) = x ⊗ₕ (y ⊗ₕ z) := by
  rw [htAssocEquiv_apply, opTensor_apply]
  rfl

variable (H K L) in
/-- The associator as a continuous linear map. -/
def htAssoc : HT (HT H K) L →L[ℂ] HT H (HT K L) :=
  (htAssocEquiv H K L : HT (HT H K) L →L[ℂ] HT H (HT K L))

theorem htAssoc_apply (u : HT H K) (z : L) :
    htAssoc H K L (u ⊗ₕ z) = opTensor (1 : H →L[ℂ] H) (htKet z) u :=
  htAssocEquiv_apply u z

@[simp] theorem htAssoc_htmul (x : H) (y : K) (z : L) :
    htAssoc H K L ((x ⊗ₕ y) ⊗ₕ z) = x ⊗ₕ (y ⊗ₕ z) := htAssocEquiv_htmul x y z

variable (H K L) in
theorem isUnitaryCLM_htAssoc : IsUnitaryCLM (htAssoc H K L) :=
  isUnitaryCLM_of_linearIsometryEquiv (htAssocEquiv H K L)

/-- The associator intertwines `(a ⊗ b) ⊗ c` with `a ⊗ (b ⊗ c)`. -/
theorem htAssoc_comp_opTensor (a : H →L[ℂ] H) (b : K →L[ℂ] K) (c : L →L[ℂ] L) :
    htAssoc H K L ∘L opTensor (opTensor a b) c
      = opTensor a (opTensor b c) ∘L htAssoc H K L := by
  refine ext_htmul fun u z => ?_
  have hket : opTensor b c ∘L htKet (H := K) z = htKet (H := K) (c z) ∘L b :=
    ContinuousLinearMap.ext fun y => by
      show opTensor b c (y ⊗ₕ z) = b y ⊗ₕ c z
      rw [opTensor_apply]
  have hkey : opTensor a (opTensor b c) ∘L opTensor (1 : H →L[ℂ] H) (htKet (H := K) z)
      = opTensor (1 : H →L[ℂ] H) (htKet (H := K) (c z)) ∘L opTensor a b := by
    rw [opTensor_comp, opTensor_comp, hket]
    congr 1
  show htAssoc H K L (opTensor (opTensor a b) c (u ⊗ₕ z))
      = opTensor a (opTensor b c) (htAssoc H K L (u ⊗ₕ z))
  rw [opTensor_apply, htAssoc_apply, htAssoc_apply]
  exact congrArg (fun T : HT H K →L[ℂ] HT H (HT K L) => T u) hkey.symm

/-- **The associator on operators**: conjugating `(a ⊗ b) ⊗ c` by the
associator gives `a ⊗ (b ⊗ c)`. -/
theorem cext_htAssoc_opTensor (a : H →L[ℂ] H) (b : K →L[ℂ] K) (c : L →L[ℂ] L) :
    cext (htAssoc H K L) (opTensor (opTensor a b) c) = opTensor a (opTensor b c) := by
  show htAssoc H K L ∘L opTensor (opTensor a b) c ∘L
    ContinuousLinearMap.adjoint (htAssoc H K L) = _
  rw [← ContinuousLinearMap.comp_assoc, htAssoc_comp_opTensor,
    ContinuousLinearMap.comp_assoc, (isUnitaryCLM_htAssoc H K L).comp_adjoint]
  rfl

end Assoc

/-! ## Transport of `concreteTensor` and of the commutation theorem -/

section TransportTensor

variable {H K H' K' : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  {U : H →L[ℂ] H'} {V : K →L[ℂ] K'}

/-- The tensor product of two unitaries is a unitary. -/
theorem IsUnitaryCLM.opTensor (hU : IsUnitaryCLM U) (hV : IsUnitaryCLM V) :
    IsUnitaryCLM (opTensor U V) := by
  have h := IsCorner.opTensor hU hV
  rwa [opTensor_one] at h

/-- **Conjugation carries `concreteTensor` to `concreteTensor`.** -/
theorem uconj_concreteTensor (hU : IsUnitaryCLM U) (hV : IsUnitaryCLM V)
    (SA : StarSubalgebra ℂ (H →L[ℂ] H)) (SB : StarSubalgebra ℂ (K →L[ℂ] K)) :
    uconj (hU.opTensor hV) (concreteTensor H K SA SB)
      = concreteTensor H' K' (uconj hU SA) (uconj hV SB) := by
  rw [concreteTensor_def, uconj_wstar, concreteTensor_def]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨cext U a, cext_mem_uconj hU ha, cext V b, cext_mem_uconj hV hb,
      cext_opTensor U V a b⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨opTensor a b, ⟨a, ha, b, hb, rfl⟩, cext_opTensor U V a b⟩

/-- **The commutation theorem is invariant under conjugation by
unitaries.**  This is the statement that lets any realisation of a corner
(or of any other Hilbert space defined up to unitary equivalence) be used
where a chosen one was named. -/
theorem CT_uconj_iff (hU : IsUnitaryCLM U) (hV : IsUnitaryCLM V)
    (SA : StarSubalgebra ℂ (H →L[ℂ] H)) (SB : StarSubalgebra ℂ (K →L[ℂ] K)) :
    CT (uconj hU SA) (uconj hV SB) ↔ CT SA SB := by
  have hL : vnComm (concreteTensor H' K' (uconj hU SA) (uconj hV SB))
      = uconj (hU.opTensor hV) (vnComm (concreteTensor H K SA SB)) := by
    rw [← uconj_concreteTensor hU hV, vnComm_uconj]
  have hR : concreteTensor H' K' (vnComm (uconj hU SA)) (vnComm (uconj hV SB))
      = uconj (hU.opTensor hV) (concreteTensor H K (vnComm SA) (vnComm SB)) := by
    rw [vnComm_uconj hU, vnComm_uconj hV, uconj_concreteTensor hU hV]
  show vnComm (concreteTensor H' K' (uconj hU SA) (uconj hV SB))
      = concreteTensor H' K' (vnComm (uconj hU SA)) (vnComm (uconj hV SB)) ↔ _
  rw [hL, hR]
  exact ⟨fun h => le_antisymm ((uconj_le_iff (hU.opTensor hV)).mp (le_of_eq h))
      ((uconj_le_iff (hU.opTensor hV)).mp (le_of_eq h.symm)),
    fun h => congrArg _ h⟩

end TransportTensor

/-! ### The flip on von Neumann algebras -/

section FlipVN

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The flip carries `𝒜 ⊗̄ ℬ` to `ℬ ⊗̄ 𝒜`.** -/
theorem uconj_htFlip_concreteTensor (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K)) :
    uconj (isUnitaryCLM_htFlip H K) (concreteTensor H K SA SB)
      = concreteTensor K H SB SA := by
  rw [concreteTensor_def, uconj_wstar, concreteTensor_def]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, a, ha, cext_htFlip_opTensor a b⟩
  · rintro ⟨b, hb, a, ha, rfl⟩
    exact ⟨opTensor a b, ⟨a, ha, b, hb, rfl⟩, cext_htFlip_opTensor a b⟩

/-- **The commutation theorem is symmetric.** -/
theorem CT_comm (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K)) : CT SA SB ↔ CT SB SA := by
  have hkey : ∀ (S : StarSubalgebra ℂ (H →L[ℂ] H))
      (T : StarSubalgebra ℂ (K →L[ℂ] K)),
      concreteTensor K H T S = uconj (isUnitaryCLM_htFlip H K) (concreteTensor H K S T) :=
    fun S T => (uconj_htFlip_concreteTensor S T).symm
  show _ ↔ vnComm (concreteTensor K H SB SA)
      = concreteTensor K H (vnComm SB) (vnComm SA)
  rw [hkey, hkey, vnComm_uconj]
  refine ⟨fun h => congrArg _ h, fun h => ?_⟩
  exact le_antisymm ((uconj_le_iff (isUnitaryCLM_htFlip H K)).mp (le_of_eq h))
    ((uconj_le_iff (isUnitaryCLM_htFlip H K)).mp (le_of_eq h.symm))

end FlipVN

/-! ## `B(ℋ) ⊗̄ B(𝒦) = B(ℋ ⊗ 𝒦)` -/

section TopTensor

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
open Theses.A.CStar in
/-- Machinery (no thesis counterpart): **the centre of `B(ℋ)` is the
scalars**.  The proof is the one-line rank-one argument: if `a` commutes
with `|x⟩⟨y|` for a *fixed* unit vector `y` and every `x`, then applying
both sides to `y` gives `a x = ⟨y, a y⟩ x`.  No linear-independence case
split is needed. -/
theorem exists_smul_one_of_central {a : H →L[ℂ] H}
    (ha : ∀ x : H →L[ℂ] H, a * x = x * a) :
    ∃ c : ℂ, a = c • (1 : H →L[ℂ] H) := by
  by_cases hH : ∀ v : H, v = 0
  · refine ⟨0, ContinuousLinearMap.ext fun v => ?_⟩
    rw [hH v, map_zero]
    simp
  simp only [not_forall] at hH
  obtain ⟨v₀, hv₀⟩ := hH
  set y : H := (‖v₀‖⁻¹ : ℂ) • v₀ with hy_def
  have hy : ‖y‖ = 1 := norm_smul_inv_norm hv₀
  have hyy : ⟪y, y⟫ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hy]; norm_num
  refine ⟨⟪y, a y⟫, ContinuousLinearMap.ext fun x => ?_⟩
  have h : a (ketbra x y y) = ketbra x y (a y) :=
    congrArg (fun T : H →L[ℂ] H => T y) (ha (ketbra x y))
  have hL : ketbra x y y = x := by
    show ⟪y, y⟫ • x = x
    rw [hyy, one_smul]
  have hR : ketbra x y (a y) = ⟪y, a y⟫ • x := rfl
  rw [hL, hR] at h
  rw [h]
  rfl

/-- **`B(ℋ) ⊗̄ B(𝒦) = B(ℋ ⊗ 𝒦)`** — the concrete tensor product of the
two *full* operator algebras is everything.

The proof is the double commutant theorem plus
`eq_opTensor_one_of_comm`: an operator commuting with every `a ⊗ b`
commutes in particular with every `1 ⊗ b`, hence is an `a₀ ⊗ 1`; it
commutes with every `c ⊗ 1`, so `a₀` is central in `B(ℋ)`, hence a
scalar, hence `a₀ ⊗ 1` is a scalar.  So the commutant of the generating
set consists of scalars, and its commutant — which by 88VI is
`𝒜 ⊗̄ ℬ` — is everything.  (When `𝒦 = 0` the space `ℋ ⊗ 𝒦` is trivial
and there is nothing to prove.) -/
theorem concreteTensor_top_top :
    concreteTensor H K (⊤ : StarSubalgebra ℂ (H →L[ℂ] H))
        (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)) = ⊤ := by
  set G : Set (HT H K →L[ℂ] HT H K) :=
    {x : HT H K →L[ℂ] HT H K | ∃ a ∈ (⊤ : StarSubalgebra ℂ (H →L[ℂ] H)),
      ∃ b ∈ (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)), x = opTensor a b} with hG
  -- 88VI, through `spatialSpan`, identifies `𝒜 ⊗̄ ℬ` with `G^□□`.
  have hdc := (double_commutant (spatialSpan (⊤ : StarSubalgebra ℂ (H →L[ℂ] H))
    (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)))).2.2
  rw [wstar_spatialSpan, coe_spatialSpan, commutant_span] at hdc
  -- every element of `G^□` is a scalar
  have hscalar : ∀ Y ∈ commutant (HT H K →L[ℂ] HT H K) G,
      ∀ X : HT H K →L[ℂ] HT H K, Y * X = X * Y := by
    intro Y hY X
    have hY1 : ∀ b : K →L[ℂ] K,
        Y * opTensor (1 : H →L[ℂ] H) b = opTensor (1 : H →L[ℂ] H) b * Y := fun b =>
      (hY (opTensor (1 : H →L[ℂ] H) b)
        ⟨1, StarSubalgebra.mem_top, b, StarSubalgebra.mem_top, rfl⟩).symm
    obtain ⟨a, rfl⟩ := eq_opTensor_one_of_comm Y hY1
    by_cases hK : ∀ w : K, w = 0
    · exact ContinuousLinearMap.ext fun u => ht_subsingleton hK _ _
    simp only [not_forall] at hK
    obtain ⟨w₀, hw₀⟩ := hK
    have hcent : ∀ c : H →L[ℂ] H, a * c = c * a := by
      intro c
      have h := hY (opTensor c (1 : K →L[ℂ] K))
        ⟨c, StarSubalgebra.mem_top, 1, StarSubalgebra.mem_top, rfl⟩
      rw [← opTensor_mul, ← opTensor_mul, one_mul] at h
      exact (opTensor_one_right_inj (H := H) hw₀ h).symm
    obtain ⟨c₀, rfl⟩ := exists_smul_one_of_central hcent
    rw [opTensor_smul_left, opTensor_one, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  -- hence `G^□□` is everything
  refine SetLike.ext' ?_
  rw [show (concreteTensor H K (⊤ : StarSubalgebra ℂ (H →L[ℂ] H))
      (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)) : Set (HT H K →L[ℂ] HT H K))
      = (wstar (HT H K →L[ℂ] HT H K) G : Set (HT H K →L[ℂ] HT H K)) from rfl,
    ← hdc]
  refine Set.eq_univ_of_forall fun X => ?_
  intro Y hY
  exact hscalar Y hY X

/-! ### The commutation theorem for `(𝒜, B(𝒦))`

The amplification theorem of `A/Proc/Tensor.lean`, read as an instance of
`CT`.  This is the "elementary amplification case" that
`docs/COMMUTATION-THEOREM.md` §1 uses in the derivation of Takesaki
IV.5.9 from IV.5.10, and it is the only instance of the general
commutation theorem the tree can prove outright. -/

theorem isVNSubalgebra_top :
    IsVNSubalgebra (H →L[ℂ] H) (⊤ : StarSubalgebra ℂ (H →L[ℂ] H)) := by
  refine ⟨?_, fun _ _ _ _ _ _ => StarSubalgebra.mem_top⟩
  rw [StarSubalgebra.coe_top]
  exact isClosed_univ

/-- The commutant of `B(ℋ)` is the scalars. -/
theorem mem_vnComm_top {x : H →L[ℂ] H} :
    x ∈ vnComm (⊤ : StarSubalgebra ℂ (H →L[ℂ] H)) ↔ ∃ c : ℂ, x = c • 1 := by
  refine ⟨fun hx => exists_smul_one_of_central fun y =>
      (mem_vnComm.mp hx y StarSubalgebra.mem_top).symm, ?_⟩
  rintro ⟨c, rfl⟩
  exact mem_vnComm.mpr fun s _ => by
    rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- Tensoring with the scalars of `B(𝒦)` adds nothing: the generating set
of `𝒩 ⊗̄ B(𝒦)^□` is `{a ⊗ 1 : a ∈ 𝒩}`. -/
theorem tensorGen_vnComm_top (N : StarSubalgebra ℂ (H →L[ℂ] H)) :
    {x : HT H K →L[ℂ] HT H K | ∃ a ∈ N,
        ∃ b ∈ vnComm (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)), x = opTensor a b}
      = {z : HT H K →L[ℂ] HT H K |
        ∃ a ∈ (N : Set (H →L[ℂ] H)), z = opTensor a (1 : K →L[ℂ] K)} := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨c, rfl⟩ := mem_vnComm_top.mp hb
    refine ⟨c • a, ?_, ?_⟩
    · have : algebraMap ℂ (H →L[ℂ] H) c * a ∈ N := mul_mem (N.algebraMap_mem c) ha
      rwa [← Algebra.smul_def] at this
    · rw [opTensor_smul_right, opTensor_smul_left]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, 1, one_mem _, rfl⟩

/-- **The commutation theorem holds when the second factor is all of
`B(𝒦)`**: `(𝒜 ⊗̄ B(𝒦))^□ = 𝒜^□ ⊗̄ ℂ1`.  This is `amplification'`
(`A/Proc/Tensor.lean`) plus 88VI, packaged as `CT`. -/
theorem CT_top_right (M : StarSubalgebra ℂ (H →L[ℂ] H))
    (hM : IsVNSubalgebra (H →L[ℂ] H) M) :
    CT (K := K) M (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)) := by
  set Gm : Set (HT H K →L[ℂ] HT H K) :=
    {z : HT H K →L[ℂ] HT H K |
      ∃ a ∈ commutant (H →L[ℂ] H) (M : Set (H →L[ℂ] H)),
        z = opTensor a (1 : K →L[ℂ] K)} with hGm
  -- the generating set of `𝒜^□ ⊗̄ B(𝒦)^□` is `Gm`
  have hgen : {x : HT H K →L[ℂ] HT H K | ∃ a ∈ vnComm M,
      ∃ b ∈ vnComm (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)), x = opTensor a b} = Gm := by
    rw [tensorGen_vnComm_top (K := K) (vnComm M), hGm, coe_vnComm]
  -- amplification: `𝒜 ⊗̄ B(𝒦) = Gm^□`
  have hset1 : {x : HT H K →L[ℂ] HT H K | ∃ a ∈ M,
      ∃ b ∈ (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)), x = opTensor a b}
      = {z : HT H K →L[ℂ] HT H K | ∃ a ∈ (M : Set (H →L[ℂ] H)),
        ∃ b : K →L[ℂ] K, z = opTensor a b} := by
    ext x
    exact ⟨fun ⟨a, ha, b, _, h⟩ => ⟨a, ha, b, h⟩,
      fun ⟨a, ha, b, h⟩ => ⟨a, ha, b, StarSubalgebra.mem_top, h⟩⟩
  have hL : (concreteTensor H K M (⊤ : StarSubalgebra ℂ (K →L[ℂ] K)) :
      Set (HT H K →L[ℂ] HT H K)) = commutant (HT H K →L[ℂ] HT H K) Gm := by
    rw [concreteTensor_def, hset1]
    exact amplification' M hM
  -- 88VI: `Gm^□□ = W*(Gm) = 𝒜^□ ⊗̄ B(𝒦)^□`
  have hdc := (double_commutant (spatialSpan (vnComm M)
    (vnComm (⊤ : StarSubalgebra ℂ (K →L[ℂ] K))))).2.2
  rw [wstar_spatialSpan, coe_spatialSpan, commutant_span, hgen] at hdc
  refine SetLike.ext' ?_
  rw [coe_vnComm, hL, hdc, concreteTensor_def, hgen]

end TopTensor

/-! ## Independence of the choice of corner

`CT_of_CT_corner` (`A/Proc/CornerTensor.lean`) has to name the *chosen*
corner `cornerRep (e i) (he i)`, because nothing said that the
commutation theorem for the compressed algebras does not depend on which
realisation of the corner is used.  It does not: any two realisations of
the same projection differ by the unitary `sub'^* sub`, and conjugation
by it carries `cornerAlg` to `cornerAlg` and `CT` to `CT`. -/

section CornerChoice

variable {H K E E' F F' : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']

/-- The unitary `sub'^* sub : E → E'` between two realisations of the same
corner. -/
def cornerTransfer (sub : E →L[ℂ] H) (sub' : E' →L[ℂ] H) : E →L[ℂ] E' :=
  ContinuousLinearMap.adjoint sub' ∘L sub

theorem adjoint_cornerTransfer (sub : E →L[ℂ] H) (sub' : E' →L[ℂ] H) :
    ContinuousLinearMap.adjoint (cornerTransfer sub sub')
      = ContinuousLinearMap.adjoint sub ∘L sub' := by
  rw [cornerTransfer, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

variable {e : H →L[ℂ] H} {sube : E →L[ℂ] H} {sube' : E' →L[ℂ] H}

/-- Two realisations of the same corner differ by a unitary. -/
theorem isUnitaryCLM_cornerTransfer (hse : IsCorner sube e) (hse' : IsCorner sube' e) :
    IsUnitaryCLM (cornerTransfer sube sube') := by
  constructor
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [adjoint_cornerTransfer]
    show ContinuousLinearMap.adjoint sube
      (sube' (ContinuousLinearMap.adjoint sube' (sube v))) = v
    rw [hse'.sub_adjoint_apply]
    have h : e (sube v) = sube v :=
      congrArg (fun T : E →L[ℂ] H => T v) hse.mul_sub
    rw [h, hse.apply_adjoint_apply]
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [adjoint_cornerTransfer]
    show ContinuousLinearMap.adjoint sube'
      (sube (ContinuousLinearMap.adjoint sube (sube' v))) = v
    rw [hse.sub_adjoint_apply]
    have h : e (sube' v) = sube' v :=
      congrArg (fun T : E' →L[ℂ] H => T v) hse'.mul_sub
    rw [h, hse'.apply_adjoint_apply]

/-- Conjugation by `sub'^* sub` turns the compression along `sub` into the
compression along `sub'`. -/
theorem cext_cornerTransfer_cmpr (hse : IsCorner sube e) (hse' : IsCorner sube' e)
    (x : H →L[ℂ] H) :
    cext (cornerTransfer sube sube') (cmpr sube x) = cmpr sube' x := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [cext_apply, adjoint_cornerTransfer]
  show ContinuousLinearMap.adjoint sube'
      (sube (ContinuousLinearMap.adjoint sube
        (x (sube (ContinuousLinearMap.adjoint sube (sube' v))))))
    = ContinuousLinearMap.adjoint sube' (x (sube' v))
  rw [hse.sub_adjoint_apply, hse.sub_adjoint_apply]
  have h1 : e (sube' v) = sube' v :=
    congrArg (fun T : E' →L[ℂ] H => T v) hse'.mul_sub
  rw [h1]
  have h2 : ContinuousLinearMap.adjoint sube' (e (x (sube' v)))
      = ContinuousLinearMap.adjoint sube' (x (sube' v)) :=
    congrArg (fun T : H →L[ℂ] E' => T (x (sube' v))) hse'.adjoint_mul
  exact h2

variable {SA : StarSubalgebra ℂ (H →L[ℂ] H)}

/-- **The compressed algebra does not depend on the realisation of the
corner.** -/
theorem uconj_cornerAlg (hse : IsCorner sube e) (hse' : IsCorner sube' e)
    (heA : e ∈ vnComm SA) :
    uconj (isUnitaryCLM_cornerTransfer hse hse') (cornerAlg hse SA heA)
      = cornerAlg hse' SA heA := by
  refine SetLike.ext' ?_
  rw [coe_uconj]
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [cext_cornerTransfer_cmpr hse hse']
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨cmpr sube x, ⟨x, hx, rfl⟩, cext_cornerTransfer_cmpr hse hse' x⟩

variable {SB : StarSubalgebra ℂ (K →L[ℂ] K)} {f : K →L[ℂ] K}
  {subf : F →L[ℂ] K} {subf' : F' →L[ℂ] K}

end CornerChoice

section CornerPayoff

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

end CornerPayoff

end Theses.A.Proc
