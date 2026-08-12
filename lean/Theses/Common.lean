/-
Shared foundation for the formalization of the theses

  * Abraham Westerbaan, *The Category of Von Neumann Algebras* (arXiv:1804.02203)
  * Bas Westerbaan, *Dagger and Dilation in the Category of Von Neumann
    Algebras* (arXiv:1803.01911)

This file contains the definitions that both theses use throughout and that
are absent from Mathlib: normality (preservation of bounded directed suprema)
and the Kadison-style definition of a von Neumann algebra used by thesis A
(vn.tex, point 42I).

See `CONVENTIONS.md` for the numbering and naming conventions.
-/
import Mathlib

open scoped ComplexOrder CStarAlgebra

namespace Theses

section Normality

variable {A B : Type*}
  [NonUnitalRing A] [StarRing A] [PartialOrder A]
  [NonUnitalRing B] [StarRing B] [PartialOrder B]

/-- A map `f : A → B` between ∗-ordered rings *preserves bounded directed
suprema of self-adjoint elements* when for every nonempty directed set `D` of
self-adjoint elements of `A` having a supremum `s` in the self-adjoint part,
`f s` is the supremum of the image `f '' D` in `B`.

This is the notion of *normality* for positive maps used throughout the
theses (vn.tex 42II for functionals; for general maps thesis A shows it
agrees with ultraweak continuity).  We state it for bare functions so that it
can be applied to positive linear maps, miu-maps, etc. alike. -/
def PreservesDirSups (f : A → B) : Prop :=
  ∀ (D : Set (selfAdjoint A)) (s : selfAdjoint A),
    D.Nonempty → DirectedOn (· ≤ ·) D → IsLUB D s →
      IsLUB ((fun d : selfAdjoint A => f d) '' D) (f s)

end Normality

section VNA

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **42II** (`def-np-functional`, vn.tex:197): an **np-functional** (normal
positive functional) on a C*-algebra: a positive linear map `ω : A → ℂ`
preserving the suprema of bounded directed sets of self-adjoint elements
(whenever they exist). -/
structure NPFunctional extends A →ₚ[ℂ] ℂ where
  preservesDirSups' : PreservesDirSups ⇑toPositiveLinearMap

noncomputable instance : FunLike (NPFunctional A) A ℂ where
  coe ω := ω.toPositiveLinearMap
  coe_injective ω₁ ω₂ h := by
    cases ω₁; cases ω₂
    congr
    exact DFunLike.coe_injective h

/-- **42I** (`vna`, vn.tex:166, Definition (Kadison)): a C*-algebra `A` is a
**von Neumann algebra** when

1. every nonempty bounded directed set of self-adjoint elements of `A` has a
   supremum in the self-adjoint part of `A`, and
2. the normal positive functionals on `A` are faithful: if `a ≥ 0` and
   `ω a = 0` for every np-functional `ω`, then `a = 0`.

This is the abstract definition thesis A works with; Mathlib's `WStarAlgebra`
(Sakai) and `VonNeumannAlgebra H` (concrete, double commutant) are different
definitions, and the theses' statements relating them are formalized against
this one. -/
class VonNeumannAlgebra : Prop where
  isLUB_of_bddAbove_directed :
    ∀ D : Set (selfAdjoint A), D.Nonempty → DirectedOn (· ≤ ·) D → BddAbove D →
      ∃ s : selfAdjoint A, IsLUB D s
  np_faithful :
    ∀ a : A, 0 ≤ a → (∀ ω : NPFunctional A, ω a = 0) → a = 0

variable {A}

/-- The supremum `⋁ D` of a nonempty bounded directed set of self-adjoint
elements of a von Neumann algebra (vn.tex 42I). -/
noncomputable def dirSup [VonNeumannAlgebra A] (D : Set (selfAdjoint A))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D) : selfAdjoint A :=
  (VonNeumannAlgebra.isLUB_of_bddAbove_directed D h.1 h.2.1 h.2.2).choose

set_option linter.unusedSectionVars false in
theorem isLUB_dirSup [VonNeumannAlgebra A] (D : Set (selfAdjoint A))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D) :
    IsLUB D (dirSup D h) :=
  (VonNeumannAlgebra.isLUB_of_bddAbove_directed D h.1 h.2.1 h.2.2).choose_spec

end VNA

section Maps

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- An **miu-map** (multiplicative, involution preserving, unital linear map,
i.e. a unital ∗-homomorphism; cstar.tex 21III): Mathlib's `A →⋆ₐ[ℂ] B`. -/
abbrev MIUMap (A B : Type*) [CStarAlgebra A] [CStarAlgebra B] := A →⋆ₐ[ℂ] B

section Order
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

/-- An **nmiu-map**: a normal unital ∗-homomorphism between von Neumann
algebras (vn.tex; normality = preservation of bounded directed suprema). -/
structure NMIUMap (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    extends A →⋆ₐ[ℂ] B where
  preservesDirSups' : PreservesDirSups ⇑toStarAlgHom

noncomputable instance : FunLike (NMIUMap A B) A B where
  coe f := f.toStarAlgHom
  coe_injective f₁ f₂ h := by
    cases f₁; cases f₂
    congr
    exact DFunLike.coe_injective h

/-- A positive map is **subunital** when `f 1 ≤ 1` (cstar.tex 21II). -/
def Subunital (f : A → B) : Prop := f 1 ≤ 1

/-- An **ncp-map**: a normal completely positive map between von Neumann
algebras.  Complete positivity is Mathlib's `CompletelyPositiveMap`. -/
structure NCPMap (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    extends A →CP B where
  preservesDirSups' : PreservesDirSups ⇑toCompletelyPositiveMap

noncomputable instance : FunLike (NCPMap A B) A B where
  coe f := f.toCompletelyPositiveMap
  coe_injective f₁ f₂ h := by
    cases f₁; cases f₂
    congr
    exact DFunLike.coe_injective h

/-- An **ncpsu-map**: a normal completely positive subunital map, the
morphisms of the category `W*_cpsu` at the heart of both theses. -/
structure NCPSUMap (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    extends NCPMap A B where
  subunital' : Subunital ⇑toNCPMap

/-- An **ncpu-map**: a normal completely positive unital map. -/
structure NCPUMap (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    extends NCPMap A B where
  unital' : toNCPMap 1 = 1

end Order

/-- The **effects** of a C*-algebra: the elements `a` with `0 ≤ a ≤ 1`,
written `[0,1]_A` in the theses. -/
abbrev effects (A : Type*) [CStarAlgebra A] [PartialOrder A] : Set A :=
  Set.Icc 0 1

end Maps

end Theses
