/-
Theses/B/Eff/WStarCat.lean

Minimal bundled categories of von Neumann algebras used as examples in the
effectus chapter (`eff.tex`, thesis B):

* `WStarNCPU`  — von Neumann algebras with ncpu-maps  (thesis: `vN`);
* `WStarCPSU`  — von Neumann algebras with ncpsu-maps (thesis: `vN_cpsu`).

Von Neumann algebras are the Kadison-style `Theses.VonNeumannAlgebra` of
`Theses.Common`; the morphisms are `Theses.NCPUMap` / `Theses.NCPSUMap`.

Identities and compositions of ncpu/ncpsu-maps are obtained here from
*existence* lemmas (`exists_id`, `exists_comp`) via choice; the underlying
mathematical facts (compositions of normal completely positive (sub)unital
maps are again such) are proved in thesis A, and are re-proved here directly
on top of Mathlib's `CompletelyPositiveMap`.
-/
import Theses.Common

open CategoryTheory
open scoped CStarAlgebra

namespace Theses.B.Eff

universe u

/-- A bundled von Neumann algebra (Kadison-style, `Theses.VonNeumannAlgebra`):
the common object type of the categories `WStarNCPU` and `WStarCPSU`. -/
structure WStar : Type (u + 1) where
  carrier : Type u
  [cstarAlgebra : CStarAlgebra carrier]
  [partialOrder : PartialOrder carrier]
  [starOrderedRing : StarOrderedRing carrier]
  [vonNeumannAlgebra : Theses.VonNeumannAlgebra carrier]

attribute [instance] WStar.cstarAlgebra WStar.partialOrder
  WStar.starOrderedRing WStar.vonNeumannAlgebra

instance : CoeSort WStar.{u} (Type u) := ⟨WStar.carrier⟩

/-- Bundle a von Neumann algebra as a `WStar` object. -/
def WStar.of (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Theses.VonNeumannAlgebra A] : WStar := ⟨A⟩

section MapClosure

variable {A B C : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- The identity completely positive map (a unital ∗-homomorphism is
completely positive). -/
private noncomputable def cpId (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : A →CP A :=
  CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (StarAlgHom.id ℂ A)

/-- Composition of completely positive maps (diagrammatic order). -/
private noncomputable def cpComp (f : A →CP B) (g : B →CP C) : A →CP C where
  toLinearMap := (g : B →ₗ[ℂ] C).comp (f : A →ₗ[ℂ] B)
  map_cstarMatrix_nonneg' k M hM :=
    g.map_cstarMatrix_nonneg' k (M.map f.toLinearMap)
      (f.map_cstarMatrix_nonneg' k M hM)

private theorem cp_mono (f : A →CP B) {a b : A} (h : a ≤ b) : f a ≤ f b :=
  OrderHomClass.mono f h

private theorem cp_map_nonneg (f : A →CP B) {a : A} (h : 0 ≤ a) : 0 ≤ f a := by
  simpa using cp_mono f h

private theorem cp_isSelfAdjoint (f : A →CP B) {a : A} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (f a) := by
  rw [← CFC.posPart_sub_negPart a ha, map_sub]
  exact (cp_map_nonneg f (CFC.posPart_nonneg a)).isSelfAdjoint.sub
    (cp_map_nonneg f (CFC.negPart_nonneg a)).isSelfAdjoint

/-- A completely positive map restricted to the self-adjoint parts. -/
private noncomputable def saMap (f : A →CP B) : selfAdjoint A → selfAdjoint B :=
  fun a => ⟨f a, cp_isSelfAdjoint f a.2⟩

/-- The identity preserves bounded directed suprema of self-adjoint
elements. -/
private theorem preservesDirSups_id (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :
    Theses.PreservesDirSups (fun a : A => a) := by
  intro D s hne hdir hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mpr (hlub.1 hd)
  · rintro b hb
    obtain ⟨d, hd⟩ := hne
    have hdb : (d : A) ≤ b := hb ⟨d, hd, rfl⟩
    have hsa : IsSelfAdjoint b := by
      have h0 : (0 : A) ≤ b - d := sub_nonneg.mpr hdb
      simpa using h0.isSelfAdjoint.add d.2
    have hub : (⟨b, hsa⟩ : selfAdjoint A) ∈ upperBounds D := by
      rintro e he
      exact Subtype.coe_le_coe.mp (hb ⟨e, he, rfl⟩)
    exact Subtype.coe_le_coe.mpr (hlub.2 hub)

set_option linter.unusedSectionVars false in
/-- Normality is preserved by composition: if a completely positive `f` and
a map `g` both preserve bounded directed suprema of self-adjoint elements,
then so does `g ∘ f`. -/
private theorem preservesDirSups_comp {g : B → C} (f : A →CP B)
    (hf : Theses.PreservesDirSups (f : A → B))
    (hg : Theses.PreservesDirSups g) :
    Theses.PreservesDirSups (fun a : A => g (f a)) := by
  intro D s hne hdir hlub
  have hfD := hf D s hne hdir hlub
  have hcoe : ∀ d : selfAdjoint A, ((saMap f d : selfAdjoint B) : B) = f d :=
    fun _ => rfl
  have hne' : (saMap f '' D).Nonempty := hne.image _
  have hdir' : DirectedOn (· ≤ ·) (saMap f '' D) := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
    obtain ⟨z, hz, hdz, hez⟩ := hdir d hd e he
    refine ⟨saMap f z, ⟨z, hz, rfl⟩, ?_, ?_⟩
    · exact Subtype.coe_le_coe.mp (cp_mono f (Subtype.coe_le_coe.mpr hdz))
    · exact Subtype.coe_le_coe.mp (cp_mono f (Subtype.coe_le_coe.mpr hez))
  have hlub' : IsLUB (saMap f '' D) (saMap f s) := by
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact Subtype.coe_le_coe.mp (hfD.1 ⟨d, hd, rfl⟩)
    · rintro b hb
      have hbb : (b : B) ∈ upperBounds ((fun d : selfAdjoint A => f d) '' D) := by
        rintro _ ⟨d, hd, rfl⟩
        exact Subtype.coe_le_coe.mpr (hb ⟨d, hd, rfl⟩)
      exact Subtype.coe_le_coe.mp (hfD.2 hbb)
  have h := hg _ (saMap f s) hne' hdir' hlub'
  rwa [Set.image_image] at h

/-- **The identity is an ncpsu-map** (thesis A); stated as an existence
lemma from which `NCPSUMap.id` is obtained by choice. -/
theorem NCPSUMap.exists_id (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] :
    ∃ f : Theses.NCPSUMap A A, ∀ a : A, f.toNCPMap a = a :=
  ⟨⟨⟨cpId A, preservesDirSups_id A⟩, le_refl 1⟩, fun _ => rfl⟩

/-- **ncpsu-maps are closed under composition** (thesis A); stated as an
existence lemma from which `NCPSUMap.comp` is obtained by choice. -/
theorem NCPSUMap.exists_comp (f : Theses.NCPSUMap A B) (g : Theses.NCPSUMap B C) :
    ∃ h : Theses.NCPSUMap A C, ∀ a : A, h.toNCPMap a = g.toNCPMap (f.toNCPMap a) :=
  ⟨⟨⟨cpComp f.toNCPMap.toCompletelyPositiveMap g.toNCPMap.toCompletelyPositiveMap,
      preservesDirSups_comp _ f.toNCPMap.preservesDirSups'
        g.toNCPMap.preservesDirSups'⟩,
    le_trans (cp_mono g.toNCPMap.toCompletelyPositiveMap f.subunital') g.subunital'⟩,
    fun _ => rfl⟩

/-- The identity ncpsu-map. -/
noncomputable def NCPSUMap.id (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : Theses.NCPSUMap A A :=
  (NCPSUMap.exists_id A).choose

/-- Composition of ncpsu-maps (diagrammatic order: first `f`, then `g`). -/
noncomputable def NCPSUMap.comp (f : Theses.NCPSUMap A B)
    (g : Theses.NCPSUMap B C) : Theses.NCPSUMap A C :=
  (NCPSUMap.exists_comp f g).choose

/-- **The identity is an ncpu-map.** -/
theorem NCPUMap.exists_id (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] :
    ∃ f : Theses.NCPUMap A A, ∀ a : A, f.toNCPMap a = a :=
  ⟨⟨⟨cpId A, preservesDirSups_id A⟩, rfl⟩, fun _ => rfl⟩

/-- **ncpu-maps are closed under composition.** -/
theorem NCPUMap.exists_comp (f : Theses.NCPUMap A B) (g : Theses.NCPUMap B C) :
    ∃ h : Theses.NCPUMap A C, ∀ a : A, h.toNCPMap a = g.toNCPMap (f.toNCPMap a) :=
  ⟨⟨⟨cpComp f.toNCPMap.toCompletelyPositiveMap g.toNCPMap.toCompletelyPositiveMap,
      preservesDirSups_comp _ f.toNCPMap.preservesDirSups'
        g.toNCPMap.preservesDirSups'⟩,
    by
      show g.toNCPMap (f.toNCPMap 1) = 1
      rw [f.unital', g.unital']⟩,
    fun _ => rfl⟩

/-- The identity ncpu-map. -/
noncomputable def NCPUMap.id (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : Theses.NCPUMap A A :=
  (NCPUMap.exists_id A).choose

/-- Composition of ncpu-maps (diagrammatic order). -/
noncomputable def NCPUMap.comp (f : Theses.NCPUMap A B)
    (g : Theses.NCPUMap B C) : Theses.NCPUMap A C :=
  (NCPUMap.exists_comp f g).choose

/-! ### Defining equations and the category laws -/

private theorem NCPSUMap.id_apply (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (a : A) : (NCPSUMap.id A).toNCPMap a = a :=
  (NCPSUMap.exists_id A).choose_spec a

private theorem NCPSUMap.comp_apply (f : Theses.NCPSUMap A B)
    (g : Theses.NCPSUMap B C) (a : A) :
    (NCPSUMap.comp f g).toNCPMap a = g.toNCPMap (f.toNCPMap a) :=
  (NCPSUMap.exists_comp f g).choose_spec a

private theorem NCPUMap.id_apply (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (a : A) : (NCPUMap.id A).toNCPMap a = a :=
  (NCPUMap.exists_id A).choose_spec a

private theorem NCPUMap.comp_apply (f : Theses.NCPUMap A B)
    (g : Theses.NCPUMap B C) (a : A) :
    (NCPUMap.comp f g).toNCPMap a = g.toNCPMap (f.toNCPMap a) :=
  (NCPUMap.exists_comp f g).choose_spec a

/-- Extensionality for ncpsu-maps (their underlying functions determine
them). -/
private theorem NCPSUMap.ext' {f g : Theses.NCPSUMap A B}
    (h : ∀ a : A, f.toNCPMap a = g.toNCPMap a) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  have hfg : f = g := DFunLike.coe_injective (funext h)
  subst hfg
  rfl

/-- Extensionality for ncpu-maps. -/
private theorem NCPUMap.ext' {f g : Theses.NCPUMap A B}
    (h : ∀ a : A, f.toNCPMap a = g.toNCPMap a) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  have hfg : f = g := DFunLike.coe_injective (funext h)
  subst hfg
  rfl

private theorem NCPSUMap.id_comp' (f : Theses.NCPSUMap A B) :
    NCPSUMap.comp (NCPSUMap.id A) f = f :=
  NCPSUMap.ext' fun a => by rw [NCPSUMap.comp_apply, NCPSUMap.id_apply]

private theorem NCPSUMap.comp_id' (f : Theses.NCPSUMap A B) :
    NCPSUMap.comp f (NCPSUMap.id B) = f :=
  NCPSUMap.ext' fun a => by rw [NCPSUMap.comp_apply, NCPSUMap.id_apply]

private theorem NCPSUMap.assoc' {D : Type u} [CStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] (f : Theses.NCPSUMap A B) (g : Theses.NCPSUMap B C)
    (h : Theses.NCPSUMap C D) :
    NCPSUMap.comp (NCPSUMap.comp f g) h = NCPSUMap.comp f (NCPSUMap.comp g h) :=
  NCPSUMap.ext' fun a => by rw [NCPSUMap.comp_apply, NCPSUMap.comp_apply,
    NCPSUMap.comp_apply, NCPSUMap.comp_apply]

private theorem NCPUMap.id_comp' (f : Theses.NCPUMap A B) :
    NCPUMap.comp (NCPUMap.id A) f = f :=
  NCPUMap.ext' fun a => by rw [NCPUMap.comp_apply, NCPUMap.id_apply]

private theorem NCPUMap.comp_id' (f : Theses.NCPUMap A B) :
    NCPUMap.comp f (NCPUMap.id B) = f :=
  NCPUMap.ext' fun a => by rw [NCPUMap.comp_apply, NCPUMap.id_apply]

private theorem NCPUMap.assoc' {D : Type u} [CStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] (f : Theses.NCPUMap A B) (g : Theses.NCPUMap B C)
    (h : Theses.NCPUMap C D) :
    NCPUMap.comp (NCPUMap.comp f g) h = NCPUMap.comp f (NCPUMap.comp g h) :=
  NCPUMap.ext' fun a => by rw [NCPUMap.comp_apply, NCPUMap.comp_apply,
    NCPUMap.comp_apply, NCPUMap.comp_apply]

end MapClosure

/-- The category `W*_ncpsu` of von Neumann algebras with normal completely
positive subunital maps — the morphisms at the heart of both theses
(objects wrapped, so that `WStarNCPU` can share the object type `WStar`). -/
structure WStarCPSU : Type (u + 1) where
  of ::
  base : WStar.{u}

/-- The category `W*_ncpsu` of von Neumann algebras with normal completely
positive subunital maps — the category at the heart of both theses.  (The
category laws are proved above, via `NCPSUMap.ext'` and the defining
equations of `NCPSUMap.id`/`comp`.) -/
noncomputable instance : Category.{u} WStarCPSU.{u} where
  Hom A B := Theses.NCPSUMap A.base B.base
  id A := NCPSUMap.id A.base
  comp f g := NCPSUMap.comp f g
  id_comp f := NCPSUMap.id_comp' f
  comp_id f := NCPSUMap.comp_id' f
  assoc f g h := NCPSUMap.assoc' f g h

/-- The category `W*_ncpu` (thesis: `vN`) of von Neumann algebras with
normal completely positive unital maps. -/
structure WStarNCPU : Type (u + 1) where
  of ::
  base : WStar.{u}

/-- The category structure on `W*_ncpu` (category laws proved above). -/
noncomputable instance : Category.{u} WStarNCPU.{u} where
  Hom A B := Theses.NCPUMap A.base B.base
  id A := NCPUMap.id A.base
  comp f g := NCPUMap.comp f g
  id_comp f := NCPUMap.id_comp' f
  comp_id f := NCPUMap.comp_id' f
  assoc f g h := NCPUMap.assoc' f g h

end Theses.B.Eff
