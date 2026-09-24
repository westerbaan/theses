/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations.

**This file has no thesis counterpart**: it is a counterexample, and carries
no DISP code and no audit row.

# The Paschke dilation is not a tensor product of the target

For an ncp-map `φ : 𝓑(ℋ) → 𝓑(𝒦)` between *type I factors* Stinespring's
theorem (**139II**, `Theses/B/Dils/Stinespring.lean`) puts the Paschke
dilation in the shape

  `𝒫 = 𝓑(ℋ ⊗ 𝒦') ,  ϱ = a ↦ a ⊗ 1 ,  h = ad_V`,

i.e. `𝒫 = 𝓑(𝒦') ⊗̄ 𝓑(ℋ)` — a tensor product of the *target* `𝓑(𝒦)`'s kind
with something else.  The general construction of chapter 2 replaces
`ℋ ⊗ 𝒦'` by the self-dual Hilbert `ℬ`-module `X̄ = 𝒜 ⊗_φ ℬ` and puts
`𝒫 = 𝓑^a(X̄)ᵒᵖ = End_ℬ(X̄)`.  This is *not* of the form `𝓑(𝒦) ⊗̄ ℬ` in
general: an orthonormal basis `(eᵢ)` of a Hilbert `ℬ`-module has each
`⟨eᵢ, eᵢ⟩` only a *projection* `pᵢ` of `ℬ` (parsec **1610**, `IsONBasis`), so
the module is one of the `ℓ²((pᵢ))` of **161II** rather than a free `ℬ^I`,
and `End_ℬ(X̄)` is accordingly a *corner* of `𝓑(ℓ²(I)) ⊗̄ ℬ` — a full tensor
product exactly when the Paschke module is free.

This file makes that failure machine-checked, with the smallest possible
example: `𝒜 = ℬ = ℂ × ℂ` and

  `φ : ℂ × ℂ → ℂ × ℂ ,  φ(a, b) = (a, 0)`,

the compression by the projection `(1, 0)` (`notTensorMap`).  It is a
*pure* map (`notTensorMap_isPureMap`): a corner `(a, b) ↦ a` onto `ℂ`
followed by the filter `z ↦ (z, 0)`.  So by **171VII** `paschke_pure` the
`ϱ`-leg of any Paschke dilation of `φ` is surjective, and since `ϱ` factors
through `ℂ` — the triple `(ℂ, (a,b) ↦ a, z ↦ (z,0))` is itself a dilation of
`φ`, and the universal property of **140II** hands out a mediating
`σ : ℂ → 𝒫` with `σ ∘ ϱ' = ϱ` — the whole of `𝒫` is `ℂ·1`:

* `paschke_of_pure_dim` : `Module.finrank ℂ 𝒫 = 1`.

A tensor product `𝓑(𝒦) ⊗̄ ℬ` of the target `ℬ = ℂ × ℂ` with any `𝓑(𝒦)` is
`𝓑(𝒦) × 𝓑(𝒦)`, whose linear dimension is `2·dim 𝓑(𝒦)`, never `1` — and
indeed such an algebra has the non-scalar central idempotent `(1, 0)` as soon
as `𝓑(𝒦) ≠ 0`, while every element of `𝒫` is a scalar.  Hence

* `paschke_not_tensor` : `𝒫` is not `⋆`-isomorphic to `𝓑(𝒦) × 𝓑(𝒦)` for any
  Hilbert space `𝒦`.

Both statements take the dilation as a hypothesis; one exists, by **154III**
`existence_paschke` together with `existence_paschke_5`, so neither is
vacuous.

(The Paschke module here is `X̄ = ℂ` with `⟨1, 1⟩ = φ(1) = (1, 0)`, a
projection which is not `1`: the module is the corner `(1,0)ℬ`, not free, and
`End_ℬ(X̄) = ℂ`.)

The von Neumann algebra structure of `ℂ × ℂ` is **84II**
`FDVNA.vonNeumannAlgebra_of_finiteDimensional` (a finite-dimensional
C*-algebra is a von Neumann algebra); `Theses/B/Eff/VNExamples.lean` proves
the same for a general product, but that file is not on this one's import
path.
-/
import Theses.B.Dils.Pure

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
open Filter Topology Theses Theses.A.CStar Theses.A.VN

namespace Theses.B.Dils

section NotTensor

/-! ## `ℂ × ℂ` as a von Neumann algebra -/

/-- `ℂ × ℂ` is a von Neumann algebra: it is a finite-dimensional
C*-algebra, so **84II** `FDVNA.vonNeumannAlgebra_of_finiteDimensional`
applies.  (Not an `instance`: the general product instance lives in
`Theses/B/Eff/VNExamples.lean`, which is not on this file's import path, and
two instances for the same Prop-valued class would be duplicated work.) -/
theorem vonNeumannAlgebra_prod_complex : Theses.VonNeumannAlgebra (ℂ × ℂ) :=
  FDVNA.vonNeumannAlgebra_of_finiteDimensional

/-! ## Order and normality on `ℂ × ℂ`

Three normality statements, all of them the same two observations: upper
bounds in a product are pairs of upper bounds, and an upper bound of a
non-empty set of self-adjoint complex numbers is self-adjoint (its imaginary
part is forced by `Complex.le_def`). -/

/-- An element of `ℂ` above a self-adjoint one is self-adjoint: `z ≤ w`
forces `z.im = w.im` (`Complex.le_def`). -/
private theorem isSelfAdjoint_of_le_complex {a x : ℂ} (ha : IsSelfAdjoint a)
    (h : a ≤ x) : IsSelfAdjoint x :=
  (Complex.im_eq_zero_iff_isSelfAdjoint x).mp
    (((Complex.le_def.mp h).2).symm.trans
      ((Complex.im_eq_zero_iff_isSelfAdjoint a).mpr ha))

/-- The components of a self-adjoint element of `ℂ × ℂ` are self-adjoint
(`prod_sa_fst` of `Theses/B/Eff/VNExamples.lean`, which is not on this
file's import path). -/
private theorem sa_fst {x : ℂ × ℂ} (hx : IsSelfAdjoint x) : IsSelfAdjoint x.1 :=
  congrArg Prod.fst hx

private theorem sa_snd {x : ℂ × ℂ} (hx : IsSelfAdjoint x) : IsSelfAdjoint x.2 :=
  congrArg Prod.snd hx

/-- Normality of the projection `(a, b) ↦ a`. -/
private theorem preservesDirSups_prodFst {f : ℂ × ℂ → ℂ} (hf : ∀ x, f x = x.1) :
    PreservesDirSups f := by
  intro D s hne _ hlub
  simp only [hf]
  obtain ⟨d₀, hd₀⟩ := hne
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact (Prod.le_def.mp (Subtype.coe_le_coe.mpr (hlub.1 hd))).1
  · intro x hx
    have hx0 : ((d₀ : ℂ × ℂ)).1 ≤ x := hx ⟨d₀, hd₀, rfl⟩
    have hd₀sa : IsSelfAdjoint ((d₀ : ℂ × ℂ)) := d₀.2
    have hssa : IsSelfAdjoint ((s : ℂ × ℂ)) := s.2
    have hsax : IsSelfAdjoint x :=
      isSelfAdjoint_of_le_complex (sa_fst hd₀sa) hx0
    have hs2 : star ((s : ℂ × ℂ).2) = ((s : ℂ × ℂ).2) := sa_snd hssa
    have hsa : IsSelfAdjoint ((x, ((s : ℂ × ℂ)).2) : ℂ × ℂ) := Prod.ext hsax hs2
    have hub : (⟨(x, ((s : ℂ × ℂ)).2), hsa⟩ : selfAdjoint (ℂ × ℂ)) ∈ upperBounds D := by
      intro d hd
      refine Subtype.coe_le_coe.mp (Prod.le_def.mpr ⟨hx ⟨d, hd, rfl⟩, ?_⟩)
      exact (Prod.le_def.mp (Subtype.coe_le_coe.mpr (hlub.1 hd))).2
    exact (Prod.le_def.mp (Subtype.coe_le_coe.mpr (hlub.2 hub))).1

/-- Normality of `z ↦ (z, 0)`. -/
private theorem preservesDirSups_prodInl {f : ℂ → ℂ × ℂ} (hf : ∀ z, f z = (z, 0)) :
    PreservesDirSups f := by
  intro D s hne _ hlub
  simp only [hf]
  obtain ⟨d₀, hd₀⟩ := hne
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact Prod.le_def.mpr ⟨Subtype.coe_le_coe.mpr (hlub.1 hd), le_rfl⟩
  · rintro ⟨x, y⟩ hxy
    have h0 := Prod.le_def.mp (hxy ⟨d₀, hd₀, rfl⟩)
    have hsax : IsSelfAdjoint x := isSelfAdjoint_of_le_complex d₀.2 h0.1
    have hub : (⟨x, hsax⟩ : selfAdjoint ℂ) ∈ upperBounds D := fun d hd =>
      Subtype.coe_le_coe.mp (Prod.le_def.mp (hxy ⟨d, hd, rfl⟩)).1
    exact Prod.le_def.mpr ⟨Subtype.coe_le_coe.mpr (hlub.2 hub), h0.2⟩

/-- Normality of the compression `x ↦ (x.1, 0)`. -/
private theorem preservesDirSups_prodCompress {f : ℂ × ℂ → ℂ × ℂ}
    (hf : ∀ x, f x = (x.1, 0)) : PreservesDirSups f := by
  intro D s hne hdir hlub
  have hfst := preservesDirSups_prodFst (f := fun x : ℂ × ℂ => x.1)
    (fun _ => rfl) D s hne hdir hlub
  simp only [hf]
  obtain ⟨d₀, hd₀⟩ := hne
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact Prod.le_def.mpr ⟨hfst.1 ⟨d, hd, rfl⟩, le_rfl⟩
  · rintro ⟨x, y⟩ hxy
    have h0 := Prod.le_def.mp (hxy ⟨d₀, hd₀, rfl⟩)
    refine Prod.le_def.mpr ⟨hfst.2 ?_, h0.2⟩
    rintro _ ⟨d, hd, rfl⟩
    exact (Prod.le_def.mp (hxy ⟨d, hd, rfl⟩)).1

/-! ## The three maps

`ϱ = (a, b) ↦ a`, the filter `c = z ↦ (z, 0)`, and their composite
`φ = x ↦ (x.1, 0)`.  All three are ∗-homomorphisms (the last two not
unital), so complete positivity is **34IV**.3 `cp_of_mi`. -/

/-- `(a, b) ↦ a` as a linear map. -/
private def fstLin : (ℂ × ℂ) →ₗ[ℂ] ℂ where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `z ↦ (z, 0)` as a linear map. -/
private def inlLin : ℂ →ₗ[ℂ] ℂ × ℂ where
  toFun z := (z, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- `x ↦ (x.1, 0)` as a linear map. -/
private def compressLin : (ℂ × ℂ) →ₗ[ℂ] ℂ × ℂ where
  toFun x := (x.1, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp] private theorem fstLin_apply (x : ℂ × ℂ) : fstLin x = x.1 := rfl

@[simp] private theorem inlLin_apply (z : ℂ) : inlLin z = (z, 0) := rfl

@[simp] private theorem compressLin_apply (x : ℂ × ℂ) : compressLin x = (x.1, 0) := rfl

/-- The nmiu-map `ϱ : ℂ × ℂ → ℂ`, `(a, b) ↦ a` — a surjective unital
∗-homomorphism. -/
noncomputable def notTensorRho : NMIUMap (ℂ × ℂ) ℂ where
  toStarAlgHom := StarAlgHom.fst ℂ ℂ ℂ
  preservesDirSups' := preservesDirSups_prodFst fun _ => rfl

@[simp] theorem notTensorRho_apply (x : ℂ × ℂ) : notTensorRho x = x.1 := rfl

/-- `ϱ` as an ncp-map: the corner of the projection `(1, 0)`. -/
noncomputable def notTensorCorner : NCPMap (ℂ × ℂ) ℂ where
  toCompletelyPositiveMap :=
    { toLinearMap := fstLin
      map_cstarMatrix_nonneg' :=
        (cp_iff _).out 0 1 |>.mp (cp_of_mi fstLin (fun _ _ => rfl) (fun _ => rfl)) }
  preservesDirSups' := preservesDirSups_prodFst fun _ => rfl

@[simp] theorem notTensorCorner_apply (x : ℂ × ℂ) : notTensorCorner x = x.1 := rfl

/-- The filter `c : ℂ → ℂ × ℂ`, `z ↦ (z, 0)`, for the effect `(1, 0)`. -/
noncomputable def notTensorFilter : NCPMap ℂ (ℂ × ℂ) where
  toCompletelyPositiveMap :=
    { toLinearMap := inlLin
      map_cstarMatrix_nonneg' :=
        (cp_iff _).out 0 1 |>.mp
          (cp_of_mi inlLin (fun _ _ => Prod.ext rfl (by simp))
            (fun _ => Prod.ext rfl (by simp))) }
  preservesDirSups' := preservesDirSups_prodInl fun _ => rfl

@[simp] theorem notTensorFilter_apply (z : ℂ) : notTensorFilter z = (z, 0) := rfl

/-- The ncp-map `φ : ℂ × ℂ → ℂ × ℂ`, `(a, b) ↦ (a, 0)`: the compression by
the projection `(1, 0)`, and the counterexample of this file. -/
noncomputable def notTensorMap : NCPMap (ℂ × ℂ) (ℂ × ℂ) where
  toCompletelyPositiveMap :=
    { toLinearMap := compressLin
      map_cstarMatrix_nonneg' :=
        (cp_iff _).out 0 1 |>.mp
          (cp_of_mi compressLin (fun _ _ => Prod.ext rfl (by simp))
            (fun _ => Prod.ext rfl (by simp))) }
  preservesDirSups' := preservesDirSups_prodCompress fun _ => rfl

@[simp] theorem notTensorMap_apply (x : ℂ × ℂ) : notTensorMap x = (x.1, 0) := rfl

/-! ## Auxiliary: linearity of an ncp-map, and positivity into `ℂ × ℂ` -/

/-- The underlying linear map of an ncp-map.  (`ncpLin` of
`Theses/B/Eff/VNExamples.lean` is the same map; that file is not on this
one's import path.) -/
private noncomputable def ncpLinear {A B : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : NCPMap A B) : A →ₗ[ℂ] B := f.toCompletelyPositiveMap.toLinearMap

@[simp] private theorem ncpLinear_apply {A B : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : NCPMap A B) (a : A) : ncpLinear f a = f a := rfl

/-- An ncp-map into `ℂ × ℂ` whose value at `1` has vanishing second
component vanishes in the second component everywhere: `x ↦ (f x).2` is a
positive functional with `ψ(1) = 0`, hence `0 ≤ ψ(a) ≤ ‖a‖·ψ(1) = 0` on
positive `a`, and every element is a complex combination of four positive
ones (`posPart`/`negPart` of the real and imaginary parts). -/
private theorem ncp_snd_eq_zero {C : Type*} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] (f : NCPMap C (ℂ × ℂ)) (h1 : (f 1 : ℂ × ℂ).2 = 0) (x : C) :
    (f x : ℂ × ℂ).2 = 0 := by
  have hmono : ∀ a b : C, a ≤ b → (f a : ℂ × ℂ) ≤ f b := by
    intro a b hab
    simpa using (ncpPositive f).monotone hab
  have hzero : (f (0 : C) : ℂ × ℂ) = 0 := map_zero (ncpLinear f)
  have hadd : ∀ a b : C, (f (a + b) : ℂ × ℂ) = f a + f b := fun a b =>
    map_add (ncpLinear f) a b
  have hsub : ∀ a b : C, (f (a - b) : ℂ × ℂ) = f a - f b := fun a b =>
    map_sub (ncpLinear f) a b
  have hsmul : ∀ (z : ℂ) (a : C), (f (z • a) : ℂ × ℂ) = z • f a := fun z a =>
    map_smul (ncpLinear f) z a
  -- positive elements
  have hpos : ∀ a : C, 0 ≤ a → (f a : ℂ × ℂ).2 = 0 := by
    intro a ha
    have hle1 : a ≤ ((‖a‖ : ℝ) : ℂ) • (1 : C) := by
      have h := le_norm_smul_one ha
      rwa [← IsScalarTower.algebraMap_smul ℂ (‖a‖ : ℝ) (1 : C),
        Complex.coe_algebraMap] at h
    have h2 : (f a : ℂ × ℂ) ≤ ((‖a‖ : ℝ) : ℂ) • f 1 := by
      have h := hmono _ _ hle1
      rwa [hsmul] at h
    have hupper : (f a : ℂ × ℂ).2 ≤ 0 := by
      have h : (f a : ℂ × ℂ).2 ≤ ((‖a‖ : ℝ) : ℂ) * (f 1 : ℂ × ℂ).2 :=
        (Prod.le_def.mp h2).2
      rwa [h1, mul_zero] at h
    have hlower : (0 : ℂ) ≤ (f a : ℂ × ℂ).2 := by
      have h := hmono _ _ ha
      rw [hzero] at h
      exact (Prod.le_def.mp h).2
    exact le_antisymm hupper hlower
  -- self-adjoint elements
  have hsa : ∀ a : C, IsSelfAdjoint a → (f a : ℂ × ℂ).2 = 0 := by
    intro a ha
    have hd : posPart a - negPart a = a := CFC.posPart_sub_negPart a ha
    have h := hsub (posPart a) (negPart a)
    rw [hd] at h
    have h2 : (f a : ℂ × ℂ).2
        = (f (posPart a) : ℂ × ℂ).2 - (f (negPart a) : ℂ × ℂ).2 := by
      rw [h]; rfl
    rw [h2, hpos _ (CFC.posPart_nonneg a), hpos _ (CFC.negPart_nonneg a), sub_zero]
  -- and the general case
  have hx : ((realPart x : C) + Complex.I • (imaginaryPart x : C)) = x :=
    realPart_add_I_smul_imaginaryPart x
  have h := hadd (realPart x : C) (Complex.I • (imaginaryPart x : C))
  rw [hx, hsmul] at h
  have h2 : (f x : ℂ × ℂ).2
      = (f (realPart x : C) : ℂ × ℂ).2
        + Complex.I * (f (imaginaryPart x : C) : ℂ × ℂ).2 := by
    rw [h]; rfl
  rw [h2, hsa _ (realPart x).2, hsa _ (imaginaryPart x).2, mul_zero, add_zero]

/-! ## `φ` is pure: a corner followed by a filter -/

private theorem zero_le_proj : (0 : ℂ × ℂ) ≤ (1, 0) := by
  simp [Prod.le_def]

private theorem proj_le_one : ((1, 0) : ℂ × ℂ) ≤ 1 := by
  simp [Prod.le_def]

/-- **169II**: `ϱ = (a, b) ↦ a` is a corner for the projection `(1, 0)`.

`ϱ(1, 0) = 1 = ϱ(1)`, and if an ncp-map `f : ℂ × ℂ → C` has
`f(1, 0) = f(1)` then `f(0, 1) = 0`, so `f(a, b) = f(a, 0)` and `f` factors
through `ϱ` as `f' = f ∘ (z ↦ (z, 0))`; the factorisation pins `f'`
pointwise, `f'(z) = f'(ϱ(z, 0)) = f(z, 0)`. -/
theorem notTensorCorner_isCornerFor :
    IsCornerFor notTensorCorner ((1, 0) : ℂ × ℂ) := by
  refine ⟨⟨zero_le_proj, proj_le_one⟩, rfl, ?_⟩
  intro C _ _ _ f hf
  have hadd : ∀ a b : ℂ × ℂ, (f (a + b) : C) = f a + f b := fun a b =>
    map_add (ncpLinear f) a b
  have hsmul : ∀ (z : ℂ) (a : ℂ × ℂ), (f (z • a) : C) = z • f a := fun z a =>
    map_smul (ncpLinear f) z a
  have h0 : (f ((0, 1) : ℂ × ℂ) : C) = 0 := by
    have h := hadd ((1, 0) : ℂ × ℂ) ((0, 1) : ℂ × ℂ)
    have he1 : ((1, 0) : ℂ × ℂ) + (0, 1) = 1 := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [he1, hf] at h
    exact (add_eq_left (a := (f (1 : ℂ × ℂ) : C))).mp h.symm
  have hsplit : ∀ x : ℂ × ℂ, (f x : C) = f (x.1, 0) := by
    intro x
    have he : ((x.1, 0) : ℂ × ℂ) + x.2 • (0, 1) = x := by
      refine Prod.ext ?_ ?_ <;> simp
    calc (f x : C) = f (((x.1, 0) : ℂ × ℂ) + x.2 • (0, 1)) := by rw [he]
      _ = f ((x.1, 0) : ℂ × ℂ) + x.2 • f ((0, 1) : ℂ × ℂ) := by rw [hadd, hsmul]
      _ = f ((x.1, 0) : ℂ × ℂ) := by rw [h0, smul_zero, add_zero]
  obtain ⟨g, hg0⟩ := Theses.A.Proc.exists_ncpComp f notTensorFilter
  have hg : ∀ z : ℂ, (g z : C) = f ((z, 0) : ℂ × ℂ) := fun z => hg0 z
  refine ⟨g, fun x => ?_, fun g' hg' => ?_⟩
  · have h : (g (x.1) : C) = f x := (hg x.1).trans (hsplit x).symm
    exact h
  · refine DFunLike.ext _ _ fun z => ?_
    have h : (g' z : C) = f ((z, 0) : ℂ × ℂ) := hg' (z, 0)
    exact h.trans (hg z).symm

/-- **169VIII**: `c = z ↦ (z, 0)` is a filter for the effect `(1, 0)`.

`c(1) = (1, 0)`, and an ncp-map `f : C → ℂ × ℂ` with `f(1) ≤ (1, 0)` has
`(f 1).2 = 0`, hence `(f x).2 = 0` for every `x` (`ncp_snd_eq_zero`); so `f`
factors through `c` by the subunital `f' = x ↦ (f x).1`, uniquely, the
factorisation reading off the first component. -/
theorem notTensorFilter_isFilterFor :
    IsFilterFor notTensorFilter ((1, 0) : ℂ × ℂ) := by
  refine ⟨zero_le_proj, le_rfl, ?_⟩
  intro C _ _ _ f hf1
  have hmono : ∀ a b : C, a ≤ b → (f a : ℂ × ℂ) ≤ f b := by
    intro a b hab
    simpa using (ncpPositive f).monotone hab
  have h1 : (f (1 : C) : ℂ × ℂ).2 = 0 := by
    refine le_antisymm (Prod.le_def.mp hf1).2 ?_
    have h := hmono 0 1 (zero_le_one' C)
    rw [show (f (0 : C) : ℂ × ℂ) = 0 from map_zero (ncpLinear f)] at h
    exact (Prod.le_def.mp h).2
  have hsnd : ∀ x : C, (f x : ℂ × ℂ).2 = 0 := ncp_snd_eq_zero f h1
  obtain ⟨g, hg0⟩ := Theses.A.Proc.exists_ncpComp notTensorCorner f
  have hg : ∀ x : C, (g x : ℂ) = (f x : ℂ × ℂ).1 := fun x => hg0 x
  have hsub : Subunital ⇑g := by
    have h : (g (1 : C) : ℂ) = (f (1 : C) : ℂ × ℂ).1 := hg 1
    show (g (1 : C) : ℂ) ≤ 1
    rw [h]
    exact (Prod.le_def.mp hf1).1
  refine ⟨⟨g, hsub⟩, fun x => ?_, ?_⟩
  · exact Prod.ext (hg x) (hsnd x).symm
  · rintro ⟨g', hg'sub⟩ hgx
    have hgg : g' = g := by
      refine DFunLike.ext _ _ fun x => ?_
      have h1' : (g' x : ℂ) = (f x : ℂ × ℂ).1 := congrArg Prod.fst (hgx x)
      rw [h1', (hg x).symm]
    subst hgg
    rfl

/-- **170I**/**168IV**: `φ(a, b) = (a, 0)` is a **pure** map — the corner
`(a, b) ↦ a` onto `ℂ` followed by the filter `z ↦ (z, 0)`. -/
theorem notTensorMap_isPureMap : IsPureMap notTensorMap :=
  ⟨ℂ, inferInstance, inferInstance, inferInstance, notTensorCorner, notTensorFilter,
    ⟨(1, 0), notTensorCorner_isCornerFor⟩, ⟨(1, 0), notTensorFilter_isFilterFor⟩,
    fun _ => rfl⟩

/-! ## The Paschke dilation of `φ` is one-dimensional -/

/-- The scalars of the Paschke algebra of `φ`: `1 ≠ 0` and every element of
`𝒫` is a complex multiple of `1`.

`φ` is pure, so `ϱ` is surjective (**171VII** `paschke_pure`).  The triple
`(ℂ, (a, b) ↦ a, z ↦ (z, 0))` is a dilation of `φ`, so the universal
property of **140II** gives an ncp-map `σ : ℂ → 𝒫` with `σ(ϱ'(x)) = ϱ(x)`,
i.e. `ϱ(a, b) = σ(a) = a·σ(1) = a·1`; surjectivity of `ϱ` then says every
element of `𝒫` is such a multiple.  And `1 ≠ 0`, since `h(ϱ(1, 0)) =
φ(1, 0) = (1, 0) ≠ 0` while `ϱ(1, 0) = σ(1) = 1`. -/
private theorem notTensor_scalars (D : PaschkeTriple (ℂ × ℂ) (ℂ × ℂ))
    (hD : IsPaschkeDilationOf D ⇑notTensorMap) :
    (1 : D.P) ≠ 0 ∧ ∀ p : D.P, ∃ z : ℂ, z • (1 : D.P) = p := by
  classical
  let _ := D.vn
  let _ : Theses.VonNeumannAlgebra (ℂ × ℂ) := vonNeumannAlgebra_prod_complex
  have hsurj : Function.Surjective ⇑D.ρ :=
    (paschke_pure notTensorMap D hD).mp notTensorMap_isPureMap
  obtain ⟨σ, ⟨hσρ, -⟩, -⟩ :=
    hD.2 ⟨ℂ, inferInstance, notTensorRho, notTensorFilter⟩ (fun _ => rfl)
  have hσval : ∀ x : ℂ × ℂ, (σ x.1 : D.P) = D.ρ x := fun x => hσρ x
  have hσsmul : ∀ z w : ℂ, (σ (z • w) : D.P) = z • σ w := fun z w =>
    map_smul (ncpLinear σ) z w
  have hρ1 : (D.ρ (1 : ℂ × ℂ) : D.P) = 1 := map_one D.ρ.toStarAlgHom
  have hσone : (σ (1 : ℂ) : D.P) = 1 := (hσval (1 : ℂ × ℂ)).trans hρ1
  have hscal : ∀ p : D.P, ∃ z : ℂ, z • (1 : D.P) = p := by
    intro p
    obtain ⟨x, hx⟩ := hsurj p
    refine ⟨x.1, ?_⟩
    calc x.1 • (1 : D.P) = x.1 • σ (1 : ℂ) := by rw [hσone]
      _ = σ (x.1 • (1 : ℂ)) := (hσsmul x.1 1).symm
      _ = σ x.1 := by rw [smul_eq_mul, mul_one]
      _ = D.ρ x := hσval x
      _ = p := hx
  refine ⟨?_, hscal⟩
  intro hone
  have hφ := hD.1 ((1, 0) : ℂ × ℂ)
  have hρ : (D.ρ ((1, 0) : ℂ × ℂ) : D.P) = 1 := (hσval ((1, 0) : ℂ × ℂ)).symm.trans hσone
  rw [hρ, hone, show (D.h (0 : D.P) : ℂ × ℂ) = 0 from map_zero (ncpLinear D.h)] at hφ
  exact one_ne_zero (α := ℂ) (congrArg Prod.fst hφ).symm

/-- **The Paschke dilation of `φ(a, b) = (a, 0)` is one-dimensional.**  See
`notTensor_scalars` for the argument. -/
theorem paschke_of_pure_dim (D : PaschkeTriple (ℂ × ℂ) (ℂ × ℂ))
    (hD : IsPaschkeDilationOf D ⇑notTensorMap) : Module.finrank ℂ D.P = 1 := by
  obtain ⟨hone, hscal⟩ := notTensor_scalars D hD
  exact (finrank_eq_one_iff_of_nonzero' (1 : D.P) hone).mpr hscal

/-- **The Paschke dilation algebra is in general not a tensor product
`𝓑(𝒦) ⊗̄ ℬ` of the target.**

For `𝒜 = ℬ = ℂ × ℂ` and `φ(a, b) = (a, 0)` the Paschke algebra `𝒫` is not
∗-isomorphic to `𝓑(𝒦) ⊗̄ (ℂ × ℂ) = 𝓑(𝒦) × 𝓑(𝒦)` for any Hilbert space `𝒦`.

Every element of `𝒫` is a scalar (`notTensor_scalars`), i.e. `dim 𝒫 = 1`
(`paschke_of_pure_dim`), whereas `dim (𝓑(𝒦) × 𝓑(𝒦)) = 2·dim 𝓑(𝒦)` is never
`1`.  The proof below reads that off the algebra rather than the dimension:
transporting `(1, 0)` back along the isomorphism makes it a scalar `z·1`,
whose two components give `z·1 = 1` and `z·1 = 0`, so `1 = 0` in `𝓑(𝒦)` and
hence in `𝒫` — contradicting `1 ≠ 0`. -/
theorem paschke_not_tensor (D : PaschkeTriple (ℂ × ℂ) (ℂ × ℂ))
    (hD : IsPaschkeDilationOf D ⇑notTensorMap) :
    ¬ ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K), Nonempty (D.P ≃⋆ₐ[ℂ] ((K →L[ℂ] K) × (K →L[ℂ] K))) := by
  rintro ⟨K, _, _, _, ⟨e⟩⟩
  obtain ⟨hone, hscal⟩ := notTensor_scalars D hD
  obtain ⟨z, hz⟩ := hscal (e.symm ((1 : K →L[ℂ] K), (0 : K →L[ℂ] K)))
  have he : z • (1 : (K →L[ℂ] K) × (K →L[ℂ] K))
      = ((1 : K →L[ℂ] K), (0 : K →L[ℂ] K)) := by
    have h : e (z • (1 : D.P)) = ((1 : K →L[ℂ] K), (0 : K →L[ℂ] K)) := by
      rw [hz, e.apply_symm_apply]
    rwa [map_smul, map_one] at h
  have h1 : z • (1 : K →L[ℂ] K) = 1 := congrArg Prod.fst he
  have h2 : z • (1 : K →L[ℂ] K) = 0 := congrArg Prod.snd he
  have hunit : (1 : K →L[ℂ] K) = 0 := by rw [← h1, h2]
  have hprod : (1 : (K →L[ℂ] K) × (K →L[ℂ] K)) = 0 := by
    refine Prod.ext ?_ ?_ <;> simpa using hunit
  refine hone ?_
  calc (1 : D.P) = e.symm 1 := (map_one e.symm).symm
    _ = e.symm 0 := by rw [hprod]
    _ = 0 := map_zero e.symm

end NotTensor

end Theses.B.Dils
