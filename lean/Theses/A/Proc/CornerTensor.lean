/-
Thesis A, chapter "Assorted Structure in W*_cpsu" (proc.tex): the
**corner Hilbert space** `eℋ` of a star projection `e ∈ B(ℋ)`, the
identification `e B(ℋ) e ≅ B(eℋ)`, the **corner tensor identification**
`(e ⊗ f)(ℋ ⊗ 𝒦) ≅ eℋ ⊗ f𝒦`, and the pay-off: the commutation theorem
for the corners implies the relative commutation theorem `RelCT` at the
cut `e ⊗ f`, which by `CT_of_relCT` (`A/Proc/Commutation.lean`) completes
the reduction of the commutation theorem to the cyclic-and-separating
case.

## Encoding

The corner is *not* built as a chosen `Submodule`.  What every consumer
actually uses is a Hilbert space `E` together with an isometry
`sub : E →L[ℂ] ℋ` whose range projection is `e`; that is the Prop-valued
`IsCorner sub e`, two operator equations

    `sub^* sub = 1`,   `sub sub^* = e`.

`CornerRep e` bundles a witness, and `Nonempty (CornerRep e)` (i.e.
`cornerRep_nonempty`) is the existence statement, proved with
`E = ker (1 - e)`.  Working relative to an arbitrary witness rather than
a chosen one costs nothing and buys the tensor identification outright:
`opTensor sub_e sub_f` is *automatically* a witness for `e ⊗ f`
(`IsCorner.opTensor`), so `eℋ ⊗ f𝒦` — the chosen Hilbert tensor product
`HT E F` — *is* the corner `(e ⊗ f)(ℋ ⊗ 𝒦)`, with the identification
carrying `x ⊗ y` to `x ⊗ y` by construction.  No appeal to
`hilb_tensor_unique` is needed.

The two transport maps are `cmpr sub x = sub^* x sub` (compression,
`B(ℋ) → B(E)`) and `cext sub y = sub y sub^*` (extension by zero,
`B(E) → B(ℋ)`); `cext` is an injective ∗-homomorphism onto the corner
`e B(ℋ) e` with `cext 1 = e`, and `cmpr` is its inverse there.

## What is *not* here, and is not needed

The identification of von Neumann algebras `(𝒜 ⊗̄ ℬ)_{e ⊗ f} = 𝒜_e ⊗̄ ℬ_f`
is **not** proved, and the reduction does not use it.  Its `⊆` half is the
elementary generator check `cmpr_opTensor`; its `⊇` half says that the
compression `cmpr` of a von Neumann algebra is again ultraweakly closed —
i.e. that `w ↦ P w P^*` is normal, or that the image of a von Neumann
algebra under a normal ∗-homomorphism is one.  Neither is in the tree,
and neither is needed, because the only place the reduction wants the
`⊇` half is to know that

    `{w : B(eℋ ⊗ f𝒦) | P w P^* ∈ 𝒯}`

is a von Neumann subalgebra for a von Neumann subalgebra `𝒯 ∋ e ⊗ f` of
`B(ℋ ⊗ 𝒦)`; and by the corner reduction theorem
(`mem_vnComm_cornerAlg`) that set is literally a **commutant**
(`cornerAlgVN`), hence a von Neumann subalgebra by 65III
(`commutant_basic_3'`).  That substitution is the one non-obvious step in
this file.
-/
import Theses.A.Proc.Commutation

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
  TensorProduct ENNReal
open Filter Topology Theses Theses.A.VN

noncomputable section

namespace Theses.A.Proc

universe u

/-! ## The corner Hilbert space -/

section Corner

variable {H E : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `IsCorner sub e` says that `sub : E →L[ℂ] ℋ` realises the Hilbert
space `E` as the corner `eℋ` of the star projection `e`: `sub` is an
isometry (`sub^* sub = 1`) whose range projection is `e`
(`sub sub^* = e`). -/
structure IsCorner (sub : E →L[ℂ] H) (e : H →L[ℂ] H) : Prop where
  adjoint_comp : ContinuousLinearMap.adjoint sub ∘L sub = 1
  comp_adjoint : sub ∘L ContinuousLinearMap.adjoint sub = e

namespace IsCorner

variable {sub : E →L[ℂ] H} {e : H →L[ℂ] H}

theorem apply_adjoint_apply (h : IsCorner sub e) (v : E) :
    ContinuousLinearMap.adjoint sub (sub v) = v := by
  have := congrArg (fun T : E →L[ℂ] E => T v) h.adjoint_comp
  simpa using this

theorem sub_adjoint_apply (h : IsCorner sub e) (x : H) :
    sub (ContinuousLinearMap.adjoint sub x) = e x := by
  have := congrArg (fun T : H →L[ℂ] H => T x) h.comp_adjoint
  simpa using this

theorem isStarProjection (h : IsCorner sub e) : IsStarProjection e := by
  refine ⟨?_, ?_⟩
  · refine ContinuousLinearMap.ext fun x => ?_
    show e (e x) = e x
    rw [← h.sub_adjoint_apply, ← h.sub_adjoint_apply x, h.apply_adjoint_apply]
  · show star e = e
    rw [← h.comp_adjoint, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem mul_self (h : IsCorner sub e) : e * e = e := h.isStarProjection.isIdempotentElem

theorem star_eq (h : IsCorner sub e) : star e = e := h.isStarProjection.isSelfAdjoint

/-- `e` acts as the identity on the corner. -/
theorem mul_sub (h : IsCorner sub e) : e ∘L sub = sub := by
  refine ContinuousLinearMap.ext fun v => ?_
  show e (sub v) = sub v
  rw [← h.sub_adjoint_apply, h.apply_adjoint_apply]

theorem adjoint_eq (h : IsCorner sub e) : ContinuousLinearMap.adjoint e = e := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact h.star_eq

theorem adjoint_mul (h : IsCorner sub e) :
    ContinuousLinearMap.adjoint sub ∘L e = ContinuousLinearMap.adjoint sub := by
  have h1 := congrArg ContinuousLinearMap.adjoint h.mul_sub
  rwa [ContinuousLinearMap.adjoint_comp, h.adjoint_eq] at h1

end IsCorner

/-- The compression `x ↦ sub^* x sub : B(ℋ) → B(E)`. -/
def cmpr (sub : E →L[ℂ] H) (x : H →L[ℂ] H) : E →L[ℂ] E :=
  ContinuousLinearMap.adjoint sub ∘L x ∘L sub

/-- Extension by zero `y ↦ sub y sub^* : B(E) → B(ℋ)`. -/
def cext (sub : E →L[ℂ] H) (y : E →L[ℂ] E) : H →L[ℂ] H :=
  sub ∘L y ∘L ContinuousLinearMap.adjoint sub

@[simp] theorem cmpr_apply (sub : E →L[ℂ] H) (x : H →L[ℂ] H) (v : E) :
    cmpr sub x v = ContinuousLinearMap.adjoint sub (x (sub v)) := rfl

@[simp] theorem cext_apply (sub : E →L[ℂ] H) (y : E →L[ℂ] E) (v : H) :
    cext sub y v = sub (y (ContinuousLinearMap.adjoint sub v)) := rfl

/-! ### The ∗-algebra calculus of `cmpr` and `cext` -/

section Calculus

variable {sub : E →L[ℂ] H} {e : H →L[ℂ] H}

theorem cext_cmpr (h : IsCorner sub e) (x : H →L[ℂ] H) :
    cext sub (cmpr sub x) = e * x * e := by
  refine ContinuousLinearMap.ext fun v => ?_
  show sub (ContinuousLinearMap.adjoint sub
    (x (sub (ContinuousLinearMap.adjoint sub v)))) = _
  rw [h.sub_adjoint_apply, h.sub_adjoint_apply]
  rfl

theorem cmpr_cext (h : IsCorner sub e) (y : E →L[ℂ] E) : cmpr sub (cext sub y) = y := by
  refine ContinuousLinearMap.ext fun v => ?_
  show ContinuousLinearMap.adjoint sub
    (sub (y (ContinuousLinearMap.adjoint sub (sub v)))) = y v
  rw [h.apply_adjoint_apply, h.apply_adjoint_apply]

theorem cext_injective (h : IsCorner sub e) : Function.Injective (cext sub) := by
  intro y y' hyy
  rw [← cmpr_cext h y, ← cmpr_cext h y', hyy]

theorem cext_mul (h : IsCorner sub e) (y y' : E →L[ℂ] E) :
    cext sub (y * y') = cext sub y * cext sub y' := by
  refine ContinuousLinearMap.ext fun v => ?_
  show sub (y (y' (ContinuousLinearMap.adjoint sub v)))
      = sub (y (ContinuousLinearMap.adjoint sub
          (sub (y' (ContinuousLinearMap.adjoint sub v)))))
  rw [h.apply_adjoint_apply]

theorem cext_one (h : IsCorner sub e) : cext sub (1 : E →L[ℂ] E) = e :=
  ContinuousLinearMap.ext fun v => h.sub_adjoint_apply v

@[simp] theorem cext_add (sub : E →L[ℂ] H) (y y' : E →L[ℂ] E) :
    cext sub (y + y') = cext sub y + cext sub y' :=
  ContinuousLinearMap.ext fun v => by simp [cext]

@[simp] theorem cext_zero (sub : E →L[ℂ] H) : cext sub 0 = 0 :=
  ContinuousLinearMap.ext fun v => by simp [cext]

@[simp] theorem cext_smul (sub : E →L[ℂ] H) (c : ℂ) (y : E →L[ℂ] E) :
    cext sub (c • y) = c • cext sub y :=
  ContinuousLinearMap.ext fun v => by simp [cext]

theorem cext_star (sub : E →L[ℂ] H) (y : E →L[ℂ] E) :
    cext sub (star y) = star (cext sub y) := by
  show sub ∘L (ContinuousLinearMap.adjoint y) ∘L ContinuousLinearMap.adjoint sub
      = ContinuousLinearMap.adjoint
        (sub ∘L y ∘L ContinuousLinearMap.adjoint sub)
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

@[simp] theorem cmpr_add (sub : E →L[ℂ] H) (x x' : H →L[ℂ] H) :
    cmpr sub (x + x') = cmpr sub x + cmpr sub x' :=
  ContinuousLinearMap.ext fun v => by simp [cmpr]

@[simp] theorem cmpr_zero (sub : E →L[ℂ] H) : cmpr sub 0 = 0 :=
  ContinuousLinearMap.ext fun v => by simp [cmpr]

@[simp] theorem cmpr_smul (sub : E →L[ℂ] H) (c : ℂ) (x : H →L[ℂ] H) :
    cmpr sub (c • x) = c • cmpr sub x :=
  ContinuousLinearMap.ext fun v => by simp [cmpr]

theorem cmpr_star (sub : E →L[ℂ] H) (x : H →L[ℂ] H) :
    cmpr sub (star x) = star (cmpr sub x) := by
  show ContinuousLinearMap.adjoint sub ∘L (ContinuousLinearMap.adjoint x) ∘L sub
      = ContinuousLinearMap.adjoint
        (ContinuousLinearMap.adjoint sub ∘L x ∘L sub)
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

theorem cmpr_one (h : IsCorner sub e) : cmpr sub (1 : H →L[ℂ] H) = 1 :=
  ContinuousLinearMap.ext fun v => h.apply_adjoint_apply v

theorem cmpr_algebraMap (h : IsCorner sub e) (c : ℂ) :
    cmpr sub (algebraMap ℂ (H →L[ℂ] H) c) = algebraMap ℂ (E →L[ℂ] E) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, cmpr_smul,
    cmpr_one h]

/-- `sub^* (x e x') sub = (sub^* x sub)(sub^* x' sub)`: the compression is
multiplicative on the corner. -/
theorem cmpr_mul_mid (h : IsCorner sub e) (x x' : H →L[ℂ] H) :
    cmpr sub (x * e * x') = cmpr sub x * cmpr sub x' := by
  refine ContinuousLinearMap.ext fun v => ?_
  show ContinuousLinearMap.adjoint sub (x (e (x' (sub v))))
      = ContinuousLinearMap.adjoint sub
          (x (sub (ContinuousLinearMap.adjoint sub (x' (sub v)))))
  rw [h.sub_adjoint_apply]

theorem cmpr_mul_e (h : IsCorner sub e) (x : H →L[ℂ] H) :
    cmpr sub (x * e) = cmpr sub x := by
  refine ContinuousLinearMap.ext fun v => ?_
  show ContinuousLinearMap.adjoint sub (x (e (sub v)))
      = ContinuousLinearMap.adjoint sub (x (sub v))
  have := congrArg (fun T : E →L[ℂ] H => T v) h.mul_sub
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at this
  rw [this]

theorem e_mul_cext (h : IsCorner sub e) (y : E →L[ℂ] E) :
    e * cext sub y = cext sub y := by
  refine ContinuousLinearMap.ext fun v => ?_
  show e (sub (y (ContinuousLinearMap.adjoint sub v)))
      = sub (y (ContinuousLinearMap.adjoint sub v))
  have := congrArg (fun T : E →L[ℂ] H => T (y (ContinuousLinearMap.adjoint sub v)))
    h.mul_sub
  simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply] using this

theorem cext_mul_e (h : IsCorner sub e) (y : E →L[ℂ] E) :
    cext sub y * e = cext sub y := by
  refine ContinuousLinearMap.ext fun v => ?_
  show sub (y (ContinuousLinearMap.adjoint sub (e v)))
      = sub (y (ContinuousLinearMap.adjoint sub v))
  have := congrArg (fun T : H →L[ℂ] E => T v) h.adjoint_mul
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at this
  rw [this]

/-- **The corner is `e B(ℋ) e`**: the range of extension by zero is
exactly the corner of `B(ℋ)` cut out by `e`. -/
theorem range_cext (h : IsCorner sub e) :
    Set.range (cext sub) = {x : H →L[ℂ] H | e * x * e = x} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    show e * cext sub y * e = cext sub y
    rw [e_mul_cext h, cext_mul_e h]
  · intro hx
    exact ⟨cmpr sub x, by rw [cext_cmpr h]; exact hx⟩

end Calculus

/-! ### Existence: every star projection has a corner -/

section Existence

variable (H) in
/-- A bundled corner: a Hilbert space together with an isometry onto the
range of `e`.  (Same idiom as `HilbertTensor`.) -/
structure CornerRep (e : H →L[ℂ] H) : Type (u + 1) where
  space : Type u
  [nacg : NormedAddCommGroup space]
  [ips : InnerProductSpace ℂ space]
  [complete : CompleteSpace space]
  sub : space →L[ℂ] H
  isCorner : IsCorner sub e

attribute [instance] CornerRep.nacg CornerRep.ips CornerRep.complete

/-- **The corner Hilbert space exists**: for a star projection `e` the
closed subspace `ker (1 - e) = eℋ` is a Hilbert space, and its inclusion
is an isometry with range projection `e`. -/
theorem cornerRep_nonempty (e : H →L[ℂ] H) (he : IsStarProjection e) :
    Nonempty (CornerRep H e) := by
  set E : Submodule ℂ H := LinearMap.ker ((1 : H →L[ℂ] H) - e).toLinearMap with hE
  have hcl : IsClosed (E : Set H) := ContinuousLinearMap.isClosed_ker _
  have hcs : CompleteSpace E := hcl.completeSpace_coe
  have hee : e * e = e := he.isIdempotentElem
  have hsa : ContinuousLinearMap.adjoint e = e := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact he.isSelfAdjoint
  have hmem : ∀ x : H, e x ∈ E := by
    intro x
    show ((1 : H →L[ℂ] H) - e) (e x) = 0
    rw [sub_apply]
    have h : (e * e) x = e x := by rw [hee]
    exact sub_eq_zero.mpr h.symm
  set sub : E →L[ℂ] H := E.subtypeL with hsub
  set pr : H →L[ℂ] E := (e : H →L[ℂ] H).codRestrict E hmem with hpr
  have hfix : ∀ w : E, e (w : H) = (w : H) := by
    intro w
    have h0 : ((1 : H →L[ℂ] H) - e) (w : H) = 0 := w.2
    rw [sub_apply] at h0
    simpa using (sub_eq_zero.mp h0).symm
  have hadj : ContinuousLinearMap.adjoint sub = pr := by
    refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr ?_).symm
    intro x y
    show ⟪(⟨e x, hmem x⟩ : E), y⟫ = ⟪x, (y : H)⟫
    show ⟪e x, (y : H)⟫ = ⟪x, (y : H)⟫
    rw [← hsa, ContinuousLinearMap.adjoint_inner_left, hfix]
  exact ⟨{ space := E
           sub := sub
           isCorner :=
             { adjoint_comp := by
                 rw [hadj]
                 exact ContinuousLinearMap.ext fun w => Subtype.ext (hfix w)
               comp_adjoint := by rw [hadj]; exact ContinuousLinearMap.ext fun x => rfl } }⟩

/-- A chosen corner Hilbert space `eℋ` for a star projection `e`. -/
def cornerRep (e : H →L[ℂ] H) (he : IsStarProjection e) : CornerRep H e :=
  (cornerRep_nonempty e he).some

/-- The carrier `eℋ` of the chosen corner. -/
abbrev Cnr (e : H →L[ℂ] H) (he : IsStarProjection e) : Type u := (cornerRep e he).space

end Existence

end Corner

/-! ## Von Neumann algebras of the corner

`cornerAlg` is the compressed algebra `S_e = {sub^* x sub : x ∈ S}` for a
projection `e` in the *commutant* of `S` — the algebra that acts on the
corner `eℋ` when one cuts `S` down by `e`.  `mem_vnComm_cornerAlg` is the
reduction theorem `(S_e)^□ = (S^□)_e` transported to `B(eℋ)`, in the form
"`y` commutes with `S_e` iff `sub y sub^*` commutes with `S`"; it is the
corner counterpart of `mem_vnComm_iff_comm_reduced`.

`cornerAlgVN` is the *other* corner construction: for a von Neumann
subalgebra `T ∋ e` it is `{y : sub y sub^* ∈ T}`, which by
`mem_vnComm_cornerAlg` is a commutant, hence a von Neumann subalgebra,
and by `coe_cornerAlgVN` is the compression `T_e` again.  It is what
makes "compression carries von Neumann subalgebras to von Neumann
subalgebras" available without any normality argument. -/

section CornerAlgebra

variable {H E : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {sub : E →L[ℂ] H} {e : H →L[ℂ] H}

omit [CompleteSpace H] in
/-- If `p z p = z` then `p z = z`. -/
theorem corner_mul_left (hp : e * e = e) {z : H →L[ℂ] H} (hz : e * z * e = z) :
    e * z = z := by
  calc e * z = e * (e * z * e) := by rw [hz]
    _ = e * e * z * e := by noncomm_ring
    _ = e * z * e := by rw [hp]
    _ = z := hz

omit [CompleteSpace H] in
/-- If `p z p = z` then `z p = z`. -/
theorem corner_mul_right (hp : e * e = e) {z : H →L[ℂ] H} (hz : e * z * e = z) :
    z * e = z := by
  calc z * e = e * z * e * e := by rw [hz]
    _ = e * z * (e * e) := by noncomm_ring
    _ = e * z * e := by rw [hp]
    _ = z := hz

/-- The corner `p B(ℋ) p` is ∗-closed. -/
theorem star_corner (hse : star e = e) {z : H →L[ℂ] H} (hz : e * z * e = z) :
    e * star z * e = star z := by
  have h1 := congrArg star hz
  simp only [star_mul, hse] at h1
  rw [mul_assoc]
  exact h1

/-- **The commutation transfer.**  If `u` commutes with an element `z` of
the corner `p B(ℋ) p`, then the compressions of `u` and `z` commute in
`B(eℋ)`.  (Note that `u` is *not* assumed to commute with `p`.)  This is
what turns "`z` commutes with `𝒜 ⊗̄ ℬ`" into "`z_e` commutes with
`(𝒜 ⊗̄ ℬ)_e`" — and only the *generators* of the corner algebra are ever
needed. -/
theorem cmpr_comm (h : IsCorner sub e) {u z : H →L[ℂ] H}
    (hz : e * z * e = z) (huz : u * z = z * u) :
    cmpr sub z * cmpr sub u = cmpr sub u * cmpr sub z := by
  refine cext_injective h ?_
  rw [cext_mul h, cext_mul h, cext_cmpr h, cext_cmpr h, hz]
  have hez : e * z = z := corner_mul_left h.mul_self hz
  have hze : z * e = z := corner_mul_right h.mul_self hz
  have hlhs : z * (e * u * e) = u * z := by
    calc z * (e * u * e) = z * e * u * e := by noncomm_ring
      _ = z * u * e := by rw [hze]
      _ = u * z * e := by rw [← huz]
      _ = u * (z * e) := by noncomm_ring
      _ = u * z := by rw [hze]
  have hrhs : e * u * e * z = u * z := by
    calc e * u * e * z = e * u * (e * z) := by noncomm_ring
      _ = e * u * z := by rw [hez]
      _ = e * (u * z) := by noncomm_ring
      _ = e * (z * u) := by rw [huz]
      _ = e * z * u := by noncomm_ring
      _ = z * u := by rw [hez]
      _ = u * z := huz.symm
  rw [hlhs, hrhs]

/-- The compressed algebra `S_e ⊆ B(eℋ)` of a ∗-subalgebra `S ⊆ B(ℋ)`
along a projection `e` of its commutant. -/
def cornerAlg (h : IsCorner sub e) (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (he : e ∈ vnComm S) : StarSubalgebra ℂ (E →L[ℂ] E) where
  carrier := cmpr sub '' (S : Set (H →L[ℂ] H))
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
    refine ⟨x * x', mul_mem hx hx', ?_⟩
    have hcomm : x' * e = e * x' := mem_vnComm.mp he x' hx'
    calc cmpr sub (x * x') = cmpr sub (x * x' * e) := (cmpr_mul_e h _).symm
      _ = cmpr sub (x * e * x') := by rw [mul_assoc, hcomm, ← mul_assoc]
      _ = cmpr sub x * cmpr sub x' := cmpr_mul_mid h x x'
  one_mem' := ⟨1, one_mem S, cmpr_one h⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
    exact ⟨x + x', add_mem hx hx', cmpr_add sub x x'⟩
  zero_mem' := ⟨0, zero_mem S, cmpr_zero sub⟩
  algebraMap_mem' := fun c =>
    ⟨algebraMap ℂ (H →L[ℂ] H) c, S.algebraMap_mem c, cmpr_algebraMap h c⟩
  star_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨star x, star_mem hx, cmpr_star sub x⟩

theorem mem_cornerAlg {h : IsCorner sub e} {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    {he : e ∈ vnComm S} {y : E →L[ℂ] E} :
    y ∈ cornerAlg h S he ↔ ∃ x ∈ S, cmpr sub x = y := Iff.rfl

theorem cmpr_mem_cornerAlg {h : IsCorner sub e} {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    {he : e ∈ vnComm S} {x : H →L[ℂ] H} (hx : x ∈ S) :
    cmpr sub x ∈ cornerAlg h S he := ⟨x, hx, rfl⟩

/-- `sub (sub^* x sub · y) sub^* = x · sub y sub^*` for `x ∈ S` and `e` in
the commutant of `S`. -/
theorem cext_cmpr_mul (h : IsCorner sub e) {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (he : e ∈ vnComm S) {x : H →L[ℂ] H} (hx : x ∈ S) (y : E →L[ℂ] E) :
    cext sub (cmpr sub x * y) = x * cext sub y := by
  have hcomm : x * e = e * x := mem_vnComm.mp he x hx
  calc cext sub (cmpr sub x * y) = cext sub (cmpr sub x) * cext sub y :=
        cext_mul h _ _
    _ = e * x * e * cext sub y := by rw [cext_cmpr h]
    _ = e * x * (e * cext sub y) := by noncomm_ring
    _ = e * x * cext sub y := by rw [e_mul_cext h]
    _ = x * (e * cext sub y) := by rw [← hcomm]; noncomm_ring
    _ = x * cext sub y := by rw [e_mul_cext h]

theorem cext_mul_cmpr (h : IsCorner sub e) {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (he : e ∈ vnComm S) {x : H →L[ℂ] H} (hx : x ∈ S) (y : E →L[ℂ] E) :
    cext sub (y * cmpr sub x) = cext sub y * x := by
  have hcomm : x * e = e * x := mem_vnComm.mp he x hx
  calc cext sub (y * cmpr sub x) = cext sub y * cext sub (cmpr sub x) :=
        cext_mul h _ _
    _ = cext sub y * (e * x * e) := by rw [cext_cmpr h]
    _ = cext sub y * e * (x * e) := by noncomm_ring
    _ = cext sub y * (x * e) := by rw [cext_mul_e h]
    _ = cext sub y * e * x := by rw [hcomm]; noncomm_ring
    _ = cext sub y * x := by rw [cext_mul_e h]

/-- **The reduction theorem in the corner** `(S_e)^□ = (S^□)_e`: an
operator of `B(eℋ)` commutes with the compressed algebra `S_e` exactly
when its extension by zero commutes with `S`. -/
theorem mem_vnComm_cornerAlg (h : IsCorner sub e) (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (he : e ∈ vnComm S) (y : E →L[ℂ] E) :
    y ∈ vnComm (cornerAlg h S he) ↔ cext sub y ∈ vnComm S := by
  constructor
  · intro hy
    refine mem_vnComm.mpr fun x hx => ?_
    have h1 : cmpr sub x * y = y * cmpr sub x :=
      mem_vnComm.mp hy _ (cmpr_mem_cornerAlg (h := h) (he := he) hx)
    have h2 := congrArg (cext sub) h1
    rwa [cext_cmpr_mul h he hx, cext_mul_cmpr h he hx] at h2
  · intro hy
    refine mem_vnComm.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    refine cext_injective h ?_
    rw [cext_cmpr_mul h he hx, cext_mul_cmpr h he hx]
    exact mem_vnComm.mp hy x hx

/-- The compression of a von Neumann subalgebra `T` containing `e`,
presented as the commutant `{y : sub y sub^* ∈ T}` — hence automatically a
von Neumann subalgebra of `B(eℋ)`. -/
def cornerAlgVN (h : IsCorner sub e) (T : StarSubalgebra ℂ (H →L[ℂ] H))
    (heT : e ∈ T) : StarSubalgebra ℂ (E →L[ℂ] E) :=
  vnComm (cornerAlg h (vnComm T) (le_vnComm_vnComm T heT))

theorem isVNSubalgebra_cornerAlgVN (h : IsCorner sub e)
    (T : StarSubalgebra ℂ (H →L[ℂ] H)) (heT : e ∈ T) :
    IsVNSubalgebra (E →L[ℂ] E) (cornerAlgVN h T heT) := isVNSubalgebra_vnComm _

theorem mem_cornerAlgVN {h : IsCorner sub e} {T : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hT : IsVNSubalgebra (H →L[ℂ] H) T) {heT : e ∈ T} {y : E →L[ℂ] E} :
    y ∈ cornerAlgVN h T heT ↔ cext sub y ∈ T := by
  rw [cornerAlgVN, mem_vnComm_cornerAlg, vnComm_vnComm T hT]

/-- **Compression carries von Neumann subalgebras to von Neumann
subalgebras**: for a von Neumann subalgebra `T ∋ e` the compression `T_e`
is a von Neumann subalgebra of `B(eℋ)`, namely `cornerAlgVN`. -/
theorem coe_cornerAlgVN {h : IsCorner sub e} {T : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hT : IsVNSubalgebra (H →L[ℂ] H) T) {heT : e ∈ T} :
    (cornerAlgVN h T heT : Set (E →L[ℂ] E)) = cmpr sub '' (T : Set (H →L[ℂ] H)) := by
  ext y
  rw [SetLike.mem_coe, mem_cornerAlgVN hT]
  constructor
  · intro hy; exact ⟨cext sub y, hy, cmpr_cext h y⟩
  · rintro ⟨x, hx, rfl⟩
    rw [cext_cmpr h]
    exact mul_mem (mul_mem heT hx) heT

/-! ### The trivial corner

A sanity anchor for the definitions: cutting by `e = 1` (with `sub = 1`)
changes nothing. -/

theorem isCorner_one : IsCorner (1 : H →L[ℂ] H) (1 : H →L[ℂ] H) :=
  ⟨by rw [ContinuousLinearMap.adjoint_one]; rfl,
    by rw [ContinuousLinearMap.adjoint_one]; rfl⟩

@[simp] theorem cmpr_one_left (x : H →L[ℂ] H) : cmpr (1 : H →L[ℂ] H) x = x := by
  show ContinuousLinearMap.adjoint (1 : H →L[ℂ] H) ∘L x ∘L 1 = x
  rw [ContinuousLinearMap.adjoint_one]
  rfl

theorem cornerAlg_one (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (he : (1 : H →L[ℂ] H) ∈ vnComm S) : cornerAlg isCorner_one S he = S := by
  refine SetLike.ext' ?_
  show cmpr (1 : H →L[ℂ] H) '' (S : Set (H →L[ℂ] H)) = (S : Set (H →L[ℂ] H))
  ext x
  simp only [Set.mem_image, cmpr_one_left]
  exact ⟨fun ⟨y, hy, hxy⟩ => hxy ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

end CornerAlgebra

/-! ## The corner tensor identification `(e ⊗ f)(ℋ ⊗ 𝒦) ≅ eℋ ⊗ f𝒦`

Nothing here is a construction: `opTensor sub_e sub_f` *is* the
identification, because `IsCorner` is stable under `opTensor`.  What has
to be supplied are the two pieces of the `opTensor` calculus that
`A/Proc/Tensor.lean` states only for endomorphisms — functoriality
`(a' ∘ a) ⊗ (b' ∘ b) = (a' ⊗ b')(a ⊗ b)` and `(a ⊗ b)^* = a^* ⊗ b^*` —
in the generality of maps between different Hilbert spaces. -/

section TensorCorner

variable {H₁ H₂ H₃ K₁ K₂ K₃ : Type u}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
  [NormedAddCommGroup K₃] [InnerProductSpace ℂ K₃] [CompleteSpace K₃]

/-- Functoriality of `⊗` for maps between different Hilbert spaces
(**111V**; `opTensor_mul` is the endomorphism case). -/
theorem opTensor_comp (a : H₁ →L[ℂ] H₂) (a' : H₂ →L[ℂ] H₃)
    (b : K₁ →L[ℂ] K₂) (b' : K₂ →L[ℂ] K₃) :
    opTensor a' b' ∘L opTensor a b = opTensor (a' ∘L a) (b' ∘L b) :=
  ext_htmul fun x y => by
    show opTensor a' b' (opTensor a b (x ⊗ₕ y)) = _
    rw [opTensor_apply, opTensor_apply, opTensor_apply]
    rfl

/-- `(a ⊗ b)^* = a^* ⊗ b^*` for maps between different Hilbert spaces
(`opTensor_adjoint` is the endomorphism case). -/
theorem opTensor_adjoint' (a : H₁ →L[ℂ] H₂) (b : K₁ →L[ℂ] K₂) :
    ContinuousLinearMap.adjoint (opTensor a b)
      = opTensor (ContinuousLinearMap.adjoint a) (ContinuousLinearMap.adjoint b) := by
  refine ext_htmul fun x' y' => ?_
  refine eq_of_inner_htmul fun x y => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, opTensor_apply, opTensor_apply,
    htmul_inner, htmul_inner, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]

end TensorCorner

section TensorCorner2

variable {H K E F : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The corner tensor identification.**  If `sub_e` realises `E` as the
corner `eℋ` and `sub_f` realises `F` as `f𝒦`, then `sub_e ⊗ sub_f`
realises `E ⊗ F` as the corner `(e ⊗ f)(ℋ ⊗ 𝒦)` — and it does so by the
map `x ⊗ y ↦ sub_e x ⊗ sub_f y`, i.e. by "`x ⊗ y ↦ x ⊗ y`". -/
theorem IsCorner.opTensor {sube : E →L[ℂ] H} {subf : F →L[ℂ] K}
    {e : H →L[ℂ] H} {f : K →L[ℂ] K}
    (he : IsCorner sube e) (hf : IsCorner subf f) :
    IsCorner (opTensor sube subf) (opTensor e f) := by
  constructor
  · rw [opTensor_adjoint', opTensor_comp, he.adjoint_comp, hf.adjoint_comp]
    exact opTensor_one
  · rw [opTensor_adjoint', opTensor_comp, he.comp_adjoint, hf.comp_adjoint]

theorem cmpr_opTensor (sube : E →L[ℂ] H) (subf : F →L[ℂ] K)
    (a : H →L[ℂ] H) (b : K →L[ℂ] K) :
    cmpr (opTensor sube subf) (opTensor a b)
      = opTensor (cmpr sube a) (cmpr subf b) := by
  show ContinuousLinearMap.adjoint (opTensor sube subf) ∘L opTensor a b
      ∘L opTensor sube subf = _
  rw [opTensor_adjoint', opTensor_comp, opTensor_comp]
  rfl

theorem cext_opTensor (sube : E →L[ℂ] H) (subf : F →L[ℂ] K)
    (a : E →L[ℂ] E) (b : F →L[ℂ] F) :
    cext (opTensor sube subf) (opTensor a b)
      = opTensor (cext sube a) (cext subf b) := by
  show opTensor sube subf ∘L opTensor a b
      ∘L ContinuousLinearMap.adjoint (opTensor sube subf) = _
  rw [opTensor_adjoint', opTensor_comp, opTensor_comp]
  rfl

end TensorCorner2

/-! ## The pay-off: `RelCT` at the cut `e ⊗ f` from `CT` for the corners

`CT_of_relCT` (`A/Proc/Commutation.lean`) reduces the commutation theorem
to its relative form `RelCT 𝒜 ℬ (e ⊗ f)` at each cut of an increasing
net.  `relCT_of_CT` supplies exactly that, from the commutation theorem
for the *corner* algebras `𝒜_e ⊆ B(eℋ)` and `ℬ_f ⊆ B(f𝒦)` — which is
where cyclic and separating vectors are available.  Together they
complete the reduction.

The two halves of the argument are:

* *down*: the compression `z ↦ P^* z P` of an element `z` of `(𝒜 ⊗̄ ℬ)^□`
  lying in the corner commutes with `𝒜_e ⊗̄ ℬ_f`.  Only the generators
  are checked (`cmpr_comm`, `cmpr_opTensor`), and the passage from
  generators to the whole algebra goes through the commutant of the
  two-element ∗-closed set `{z_e, z_e^*}`, which is a von Neumann
  subalgebra by 65III.
* *up*: `{w : P w P^* ∈ T}` is, for a von Neumann subalgebra `T` of
  `B(ℋ ⊗ 𝒦)` containing `e ⊗ f`, itself a von Neumann subalgebra
  (`cornerAlgVN`) — because by the corner reduction theorem it is a
  *commutant*.  No normality of `w ↦ P w P^*` is needed, and this is the
  step that would otherwise cost an ultraweak-continuity argument. -/

section Payoff

variable {H K E F : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The corner form of the commutation theorem implies the relative
form at that cut.**  If `sub_e` realises `E` as the corner `eℋ` for a
projection `e ∈ 𝒜^□`, `sub_f` realises `F` as `f𝒦` for `f ∈ ℬ^□`, and the
commutation theorem holds for the compressed algebras `𝒜_e ⊆ B(E)` and
`ℬ_f ⊆ B(F)`, then `RelCT 𝒜 ℬ (e ⊗ f)` holds. -/
theorem relCT_of_CT {SA : StarSubalgebra ℂ (H →L[ℂ] H)}
    {SB : StarSubalgebra ℂ (K →L[ℂ] K)} {e : H →L[ℂ] H} {f : K →L[ℂ] K}
    {sube : E →L[ℂ] H} {subf : F →L[ℂ] K}
    (hse : IsCorner sube e) (hsf : IsCorner subf f)
    (heA : e ∈ vnComm SA) (hfB : f ∈ vnComm SB)
    (hCT : CT (cornerAlg hse SA heA) (cornerAlg hsf SB hfB)) :
    RelCT SA SB (opTensor e f) := by
  -- Abstract the cut `p = e ⊗ f` and its corner `P = sub_e ⊗ sub_f`.
  obtain ⟨p, P, hP, hpe, hPe⟩ :
      ∃ (p : HT H K →L[ℂ] HT H K) (P : HT E F →L[ℂ] HT H K),
        IsCorner P p ∧ p = opTensor e f ∧ P = opTensor sube subf :=
    ⟨_, _, hse.opTensor hsf, rfl, rfl⟩
  suffices hgoal : RelCT SA SB p by rwa [hpe] at hgoal
  have hCT' : vnComm (concreteTensor E F (cornerAlg hse SA heA) (cornerAlg hsf SB hfB))
      = concreteTensor E F (vnComm (cornerAlg hse SA heA))
          (vnComm (cornerAlg hsf SB hfB)) := hCT
  have hpp : p * p = p := hP.mul_self
  have hpC : p ∈ vnComm (concreteTensor H K SA SB) := by
    rw [hpe]; exact opTensor_mem_vnComm_concreteTensor heA hfB
  have hTvn := isVNSubalgebra_concreteTensor (vnComm SA) (vnComm SB)
  have hpT : p ∈ concreteTensor H K (vnComm SA) (vnComm SB) := by
    rw [hpe]; exact opTensor_mem_concreteTensor heA hfB
  intro z hz hcomm
  have hzC : z ∈ vnComm (concreteTensor H K SA SB) :=
    (mem_vnComm_iff_comm_reduced hpp hpC hz).mp hcomm
  have hzsC : star z ∈ vnComm (concreteTensor H K SA SB) := star_mem hzC
  have hzs : p * star z * p = star z := star_corner hP.star_eq hz
  -- *Down*: the compression of `z` commutes with `𝒜_e ⊗̄ ℬ_f`.
  have hstep1 : cmpr P z ∈ vnComm (concreteTensor E F
      (cornerAlg hse SA heA) (cornerAlg hsf SB hfB)) := by
    have hstar : ∀ a ∈ ({cmpr P z, star (cmpr P z)} : Set (HT E F →L[ℂ] HT E F)),
        star a ∈ ({cmpr P z, star (cmpr P z)} : Set (HT E F →L[ℂ] HT E F)) := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      rcases ha with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (star_star _)
    obtain ⟨Y, hYvn, hYcoe⟩ := (commutant_basic_3'
      ({cmpr P z, star (cmpr P z)} : Set (HT E F →L[ℂ] HT E F)) hstar).1
    have hgen : ∀ a' ∈ cornerAlg hse SA heA, ∀ b' ∈ cornerAlg hsf SB hfB,
        opTensor a' b' ∈ Y := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hmem : opTensor a b ∈ concreteTensor H K SA SB :=
        opTensor_mem_concreteTensor ha hb
      have hcp : opTensor (cmpr sube a) (cmpr subf b) = cmpr P (opTensor a b) := by
        rw [hPe, cmpr_opTensor]
      have hYm : opTensor (cmpr sube a) (cmpr subf b)
          ∈ (Y : Set (HT E F →L[ℂ] HT E F)) := by
        rw [hYcoe, hcp]
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact cmpr_comm hP hz (mem_vnComm.mp hzC _ hmem)
        · rw [← cmpr_star P z]
          exact cmpr_comm hP hzs (mem_vnComm.mp hzsC _ hmem)
      exact hYm
    have hle := concreteTensor_le hYvn hgen
    refine mem_vnComm.mpr fun s hs => ?_
    have hsY : s ∈ (Y : Set (HT E F →L[ℂ] HT E F)) := hle hs
    rw [hYcoe] at hsY
    exact (hsY _ (Set.mem_insert _ _)).symm
  -- The commutation theorem for the corners.
  rw [hCT'] at hstep1
  -- *Up*: extension by zero lands in `𝒜^□ ⊗̄ ℬ^□`.
  have hle : concreteTensor E F (vnComm (cornerAlg hse SA heA))
        (vnComm (cornerAlg hsf SB hfB))
      ≤ cornerAlgVN hP (concreteTensor H K (vnComm SA) (vnComm SB)) hpT := by
    refine concreteTensor_le (isVNSubalgebra_cornerAlgVN _ _ _) ?_
    intro a' ha' b' hb'
    rw [mem_cornerAlgVN hTvn, hPe, cext_opTensor]
    exact opTensor_mem_concreteTensor
      ((mem_vnComm_cornerAlg hse SA heA a').mp ha')
      ((mem_vnComm_cornerAlg hsf SB hfB b').mp hb')
  have hfin := (mem_cornerAlgVN hTvn).mp (hle hstep1)
  rwa [cext_cmpr hP, hz] at hfin

/-- **The reduction, completed.**  Given increasing nets of projections
`{e_i} ⊆ 𝒜^□` and `{f_j} ⊆ ℬ^□` with supremum `1`, the commutation
theorem for `(𝒜, ℬ)` follows from the commutation theorem for the
corner algebras `𝒜_{e_i} ⊆ B(e_iℋ)` and `ℬ_{f_j} ⊆ B(f_j𝒦)`.

Combined with `exists_orthogonal_separating_family` and
`isLUB_range_finsetSum` (which produce such nets, with `ξ` separating for
each corner) this is the reduction of the commutation theorem to the
cyclic-and-separating case. -/
theorem CT_of_CT_corner {ι κ : Type*} [Nonempty ι] [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty κ] [Preorder κ] [IsDirected κ (· ≤ ·)]
    {SA : StarSubalgebra ℂ (H →L[ℂ] H)} {SB : StarSubalgebra ℂ (K →L[ℂ] K)}
    (e : ι → H →L[ℂ] H) (he : ∀ i, IsStarProjection (e i))
    (hemem : ∀ i, e i ∈ vnComm SA) (hemono : Monotone e) (helub : IsLUB (Set.range e) 1)
    (f : κ → K →L[ℂ] K) (hf : ∀ j, IsStarProjection (f j))
    (hfmem : ∀ j, f j ∈ vnComm SB) (hfmono : Monotone f) (hflub : IsLUB (Set.range f) 1)
    (hcorner : ∀ (i : ι) (j : κ),
      CT (cornerAlg (cornerRep (e i) (he i)).isCorner SA (hemem i))
         (cornerAlg (cornerRep (f j) (hf j)).isCorner SB (hfmem j))) :
    CT SA SB :=
  CT_of_relCT e he hemem hemono helub f hf hfmem hfmono hflub
    fun i j => relCT_of_CT (cornerRep (e i) (he i)).isCorner
      (cornerRep (f j) (hf j)).isCorner (hemem i) (hfmem j) (hcorner i j)

end Payoff

end Theses.A.Proc
