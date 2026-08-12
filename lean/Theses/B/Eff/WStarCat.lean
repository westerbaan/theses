/-
Theses/B/Eff/WStarCat.lean

Minimal bundled categories of von Neumann algebras used as examples in the
effectus chapter (`eff.tex`, thesis B):

* `WStarNCPU`  — von Neumann algebras with ncpu-maps  (thesis: `vN`);
* `WStarCPSU`  — von Neumann algebras with ncpsu-maps (thesis: `vN_cpsu`).

Von Neumann algebras are the Kadison-style `Theses.VonNeumannAlgebra` of
`Theses.Common`; the morphisms are `Theses.NCPUMap` / `Theses.NCPSUMap`.

FIXME(category): identities and compositions of ncpu/ncpsu-maps are obtained
here from `sorry`-ed *existence* lemmas (`exists_id`, `exists_comp`) via
choice, and the category laws are `sorry`-ed.  The underlying mathematical
facts (compositions of normal completely positive (sub)unital maps are again
such) are proved in thesis A; they are not re-stated here.
-/
import Theses.Common

open CategoryTheory

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

/-- FIXME(category): the identity is an ncpsu-map (proved in thesis A);
stated as an existence lemma from which `NCPSUMap.id` is obtained by
choice. -/
theorem NCPSUMap.exists_id (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] :
    ∃ f : Theses.NCPSUMap A A, ∀ a : A, f.toNCPMap a = a := sorry

/-- FIXME(category): ncpsu-maps are closed under composition (proved in
thesis A); stated as an existence lemma from which `NCPSUMap.comp` is
obtained by choice. -/
theorem NCPSUMap.exists_comp (f : Theses.NCPSUMap A B) (g : Theses.NCPSUMap B C) :
    ∃ h : Theses.NCPSUMap A C, ∀ a : A, h.toNCPMap a = g.toNCPMap (f.toNCPMap a) :=
  sorry

/-- The identity ncpsu-map. -/
noncomputable def NCPSUMap.id (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : Theses.NCPSUMap A A :=
  (NCPSUMap.exists_id A).choose

/-- Composition of ncpsu-maps (diagrammatic order: first `f`, then `g`). -/
noncomputable def NCPSUMap.comp (f : Theses.NCPSUMap A B)
    (g : Theses.NCPSUMap B C) : Theses.NCPSUMap A C :=
  (NCPSUMap.exists_comp f g).choose

/-- FIXME(category): the identity is an ncpu-map. -/
theorem NCPUMap.exists_id (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] :
    ∃ f : Theses.NCPUMap A A, ∀ a : A, f.toNCPMap a = a := sorry

/-- FIXME(category): ncpu-maps are closed under composition. -/
theorem NCPUMap.exists_comp (f : Theses.NCPUMap A B) (g : Theses.NCPUMap B C) :
    ∃ h : Theses.NCPUMap A C, ∀ a : A, h.toNCPMap a = g.toNCPMap (f.toNCPMap a) :=
  sorry

/-- The identity ncpu-map. -/
noncomputable def NCPUMap.id (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : Theses.NCPUMap A A :=
  (NCPUMap.exists_id A).choose

/-- Composition of ncpu-maps (diagrammatic order). -/
noncomputable def NCPUMap.comp (f : Theses.NCPUMap A B)
    (g : Theses.NCPUMap B C) : Theses.NCPUMap A C :=
  (NCPUMap.exists_comp f g).choose

end MapClosure

/-- The category `W*_ncpsu` of von Neumann algebras with normal completely
positive subunital maps — the morphisms at the heart of both theses
(objects wrapped, so that `WStarNCPU` can share the object type `WStar`). -/
structure WStarCPSU : Type (u + 1) where
  of ::
  base : WStar.{u}

/-- FIXME(category): the category laws for `WStarCPSU` are `sorry`-ed (they
depend on the `sorry`-ed existence lemmas above and a `FunLike`-style
extensionality for `NCPSUMap`). -/
noncomputable instance : Category.{u} WStarCPSU.{u} where
  Hom A B := Theses.NCPSUMap A.base B.base
  id A := NCPSUMap.id A.base
  comp f g := NCPSUMap.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The category `W*_ncpu` (thesis: `vN`) of von Neumann algebras with
normal completely positive unital maps. -/
structure WStarNCPU : Type (u + 1) where
  of ::
  base : WStar.{u}

/-- FIXME(category): the category laws for `WStarNCPU` are `sorry`-ed. -/
noncomputable instance : Category.{u} WStarNCPU.{u} where
  Hom A B := Theses.NCPUMap A.base B.base
  id A := NCPUMap.id A.base
  comp f g := NCPUMap.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end Theses.B.Eff
