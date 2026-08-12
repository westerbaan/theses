/-
Theses/B/Eff/DiamondAmp.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
4408–5253: ⋄-effectuses (parsecs 206–210) and &-effectuses ("andthen
effectuses", parsecs 211–213).

Design:
* `DiamondEffectus C` is a Prop-class extending `HasQuotients`,
  `HasComprehension` and `HasImages` with the axiom that orthocomplements
  of sharp predicates are sharp.  The maps `f^⋄, f_⋄, f^□, f_□` between the
  sets `SPred` of sharp predicates are `diaPull`, `diaPush`, `boxPull`,
  `boxPush`.
* `AndThenEffectus C` ("&-effectus") adds the unique existence of
  ⋄-positive `asrt_p` maps and purity of quotient-after-comprehension;
  `asrt`, `andThen p q = q ∘ asrt_p` and the corresponding quotient `ζ_s`
  of a chosen comprehension `π_s` are obtained by (unique) choice.
* Not separately formalized: the examples 206III/210III/211IV beyond
  `vNᵒᵖ` (`CvNᵒᵖ`, `EJAᵒᵖ`, `Set`; sharp maps = nmiu-maps), the remarks
  211III/211IIIa on `assert` and polar decomposition, and 208VII (the
  functor to `OMLatGal`, whose data is exactly 207VI + 207III).
-/
import Theses.B.Eff.Quotients

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits

namespace Theses.B.Eff

universe u v

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-! ## ⋄-effectuses (parsec 206) -/

/-- **206II** (`diamond-basics`, eff.tex:4430, Definition): a
**⋄-effectus** is an effectus with quotients, comprehension and images such
that `sᵖ` is sharp for every sharp predicate `s`. -/
class DiamondEffectus (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop
    extends HasQuotients C, HasComprehension C, HasImages C where
  orth_sharp : ∀ {X : C} {s : Pred X}, IsSharp s → IsSharp (orth s)

section Diamond

variable [DiamondEffectus C] {X Y Z : C}

/-- The floor `⌊p⌋ = im π_p` of a predicate is sharp (it is an image; used
implicitly throughout parsecs 206–208). -/
theorem isSharp_floor (p : Pred X) : IsSharp (floorPred p) :=
  ⟨_, _, isImage_imPred _⟩

/-- In a ⋄-effectus ceilings are sharp: `⌈p⌉ = ⌊pᵖ⌋ᵖ` is the
orthocomplement of a sharp predicate (used in 206II to define `f^⋄`, and in
the proof of 207VI). -/
theorem isSharp_ceil (p : Pred X) : IsSharp (ceilPred p) :=
  DiamondEffectus.orth_sharp (isSharp_floor _)

/-- The orthocomplement within the sharp predicates (206II). -/
def SPred.orth (s : SPred X) : SPred X :=
  ⟨EffectAlgebra.orth s.1, DiamondEffectus.orth_sharp s.2⟩

/-- **206II** (`diamond-basics`, eff.tex:4444, Definition): the restriction
`f^⋄ : SPred Y → SPred X` of `f : X ⟶ Y` to sharp predicates,
`f^⋄(s) = ⌈s ∘ f⌉`. -/
noncomputable def diaPull (f : X ⟶ Y) (s : SPred Y) : SPred X :=
  ⟨ceilPred (f ≫ s.1), isSharp_ceil _⟩

/-- **206II** (`diamond-basics`, eff.tex:4449, Definition): the map
`f_⋄ : SPred X → SPred Y` of `f : X ⟶ Y`, `f_⋄(s) = im (f ∘ π_s)`. -/
noncomputable def diaPush (f : X ⟶ Y) (s : SPred X) : SPred Y :=
  ⟨imPred (comprMap s.1 ≫ f), _, _, isImage_imPred _⟩

/-- **206II** (`diamond-basics`, eff.tex:4473, Definition):
`f^□(s) = f^⋄(sᵖ)ᵖ`. -/
noncomputable def boxPull (f : X ⟶ Y) (s : SPred Y) : SPred X :=
  (diaPull f s.orth).orth

/-- **206II** (`diamond-basics`, eff.tex:4474, Definition):
`f_□(s) = f_⋄(sᵖ)ᵖ`. -/
noncomputable def boxPush (f : X ⟶ Y) (s : SPred X) : SPred Y :=
  (diaPush f s.orth).orth

/-- **206II.1** (`diamond-basics`, eff.tex:4453, Definition): maps
`f : X ⟶ Y` and `g : Y ⟶ X` are **⋄-adjoint** when `f^⋄ = g_⋄`. -/
def DiamondAdjoint (f : X ⟶ Y) (g : Y ⟶ X) : Prop :=
  diaPull f = diaPush g

/-- **206II.2** (`diamond-basics`, eff.tex:4458, Definition): an endomap is
**⋄-self-adjoint** when it is ⋄-adjoint to itself. -/
def DiamondSelfAdjoint (f : X ⟶ X) : Prop := DiamondAdjoint f f

/-- **206II.3** (`diamond-basics`, eff.tex:4462, Definition): maps
`f, g : X ⟶ Y` are **⋄-equivalent** when `f^⋄ = g^⋄` (equivalently
`f_⋄ = g_⋄`, 207VIIa). -/
def DiamondEquivalent (f g : X ⟶ Y) : Prop := diaPull f = diaPull g

/-- **206II.4** (`diamond-basics`, eff.tex:4468, Definition): a pure endomap
`f` is **⋄-positive** when `f = g ∘ g` for some ⋄-self-adjoint `g`. -/
def DiamondPositive (f : X ⟶ X) : Prop :=
  IsPure f ∧ ∃ g : X ⟶ X, DiamondSelfAdjoint g ∧ f = g ≫ g

end Diamond

/-- **206III** (eff.tex:4477, Examples): `vNᵒᵖ` is a ⋄-effectus (as are
`CvNᵒᵖ`, `EJAᵒᵖ` and `Set`, not formalized here). -/
theorem diamond_effectus_vn (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    DiamondEffectus WStarCPSU.{u}ᵒᵖ := sorry

/-! ## Basic properties of `(–)^⋄`, `(–)_⋄`, `(–)^□` (parsecs 207–208) -/

section DiamondBasics

variable [DiamondEffectus C] {X Y Z : C}

/-- The supremum of two sharp predicates within the poset `SPred` (helper
for 207V, 208XII). -/
def SPred.IsSup (s t j : SPred X) : Prop :=
  s.1 ≼ j.1 ∧ t.1 ≼ j.1 ∧ ∀ r : SPred X, s.1 ≼ r.1 → t.1 ≼ r.1 → j.1 ≼ r.1

/-- The infimum of two sharp predicates within the poset `SPred` (helper
for 207V, 208IX). -/
def SPred.IsInf (s t m : SPred X) : Prop :=
  m.1 ≼ s.1 ∧ m.1 ≼ t.1 ∧ ∀ r : SPred X, r.1 ≼ s.1 → r.1 ≼ t.1 → r.1 ≼ m.1

/-- **207II** (`exc-diam-order-pres`, eff.tex:4487, Exercise): `f^⋄` and
`f^□` are order preserving. -/
theorem exc_diam_order_pres (f : X ⟶ Y) {s t : SPred Y} (h : s.1 ≼ t.1) :
    (diaPull f s).1 ≼ (diaPull f t).1 ∧
      (boxPull f s).1 ≼ (boxPull f t).1 := sorry

/-- **207III** (`diamond-adjunction`, eff.tex:4491, Proposition): for
`f : X ⟶ Y` and sharp `s, t` we have `f^⋄(s) ≤ tᵖ` iff `f_⋄(t) ≤ sᵖ`. -/
theorem diamond_adjunction (f : X ⟶ Y) (s : SPred Y) (t : SPred X) :
    (diaPull f s).1 ≼ orth t.1 ↔ (diaPush f t).1 ≼ orth s.1 := sorry

/-- **207III** (`diamond-adjunction`, eff.tex:4499, Proposition),
reformulated: `f_⋄` is the left order-adjoint of `f^□`:
`f_⋄(s) ≤ t ⟺ s ≤ f^□(t)`. -/
theorem diamond_adjunction' (f : X ⟶ Y) (s : SPred X) (t : SPred Y) :
    (diaPush f s).1 ≼ t.1 ↔ s.1 ≼ (boxPull f t).1 := sorry

/-- **207V.1** (`order-adj-basics`, eff.tex:4527, Exercise): `f_⋄` is order
preserving. -/
theorem order_adj_basics_1 (f : X ⟶ Y) {s t : SPred X} (h : s.1 ≼ t.1) :
    (diaPush f s).1 ≼ (diaPush f t).1 := sorry

/-- **207V.2** (`order-adj-basics`, eff.tex:4527, Exercise): `f_⋄` preserves
(binary) suprema. -/
theorem order_adj_basics_2 (f : X ⟶ Y) {s t j : SPred X}
    (h : SPred.IsSup s t j) :
    SPred.IsSup (diaPush f s) (diaPush f t) (diaPush f j) := sorry

/-- **207V.3** (`order-adj-basics`, eff.tex:4527, Exercise): `f^□` preserves
(binary) infima. -/
theorem order_adj_basics_3 (f : X ⟶ Y) {s t m : SPred Y}
    (h : SPred.IsInf s t m) :
    SPred.IsInf (boxPull f s) (boxPull f t) (boxPull f m) := sorry

/-- **207V.4** (`order-adj-basics`, eff.tex:4527, Exercise): `f^⋄` preserves
(binary) suprema. -/
theorem order_adj_basics_4 (f : X ⟶ Y) {s t j : SPred Y}
    (h : SPred.IsSup s t j) :
    SPred.IsSup (diaPull f s) (diaPull f t) (diaPull f j) := sorry

/-- **207V.5** (`order-adj-basics`, eff.tex:4527, Exercise):
`f_⋄ ∘ f^□ ∘ f_⋄ = f_⋄`. -/
theorem order_adj_basics_5 (f : X ⟶ Y) (s : SPred X) :
    diaPush f (boxPull f (diaPush f s)) = diaPush f s := sorry

/-- **207V.6** (`order-adj-basics`, eff.tex:4527, Exercise):
`f^□ ∘ f_⋄ ∘ f^□ = f^□`. -/
theorem order_adj_basics_6 (f : X ⟶ Y) (t : SPred Y) :
    boxPull f (diaPush f (boxPull f t)) = boxPull f t := sorry

/-- **207VI.1–2** (`diamond-functor`, eff.tex:4543, Lemma): `(–)^⋄` is
functorial: `(id)^⋄ = id` and `(f ∘ g)^⋄ = g^⋄ ∘ f^⋄`. -/
theorem diamond_functor_pull :
    (∀ s : SPred X, diaPull (𝟙 X) s = s) ∧
      ∀ (g : X ⟶ Y) (f : Y ⟶ Z) (s : SPred Z),
        diaPull (g ≫ f) s = diaPull g (diaPull f s) := sorry

/-- **207VI.3–4** (`diamond-functor`, eff.tex:4543, Lemma): `(–)^□` is
functorial. -/
theorem diamond_functor_box :
    (∀ s : SPred X, boxPull (𝟙 X) s = s) ∧
      ∀ (g : X ⟶ Y) (f : Y ⟶ Z) (s : SPred Z),
        boxPull (g ≫ f) s = boxPull g (boxPull f s) := sorry

/-- **207VI.5–6** (`diamond-functor`, eff.tex:4543, Lemma): `(–)_⋄` is
functorial: `(id)_⋄ = id` and `(f ∘ g)_⋄ = f_⋄ ∘ g_⋄`. -/
theorem diamond_functor_push :
    (∀ s : SPred X, diaPush (𝟙 X) s = s) ∧
      ∀ (g : X ⟶ Y) (f : Y ⟶ Z) (s : SPred X),
        diaPush (g ≫ f) s = diaPush f (diaPush g s) := sorry

/-- **207VIIa** (`diamond-equiv-equiv`, eff.tex:4594, Exercise):
`f^⋄ = g^⋄` iff `f_⋄ = g_⋄`. -/
theorem diamond_equiv_equiv (f g : X ⟶ Y) :
    diaPull f = diaPull g ↔ diaPush f = diaPush g := sorry

/-- **208I** (`image-sharp-is-order-sharp`, eff.tex:4601, Lemma): in a
⋄-effectus sharp predicates are **order sharp**: `p ≤ s` and `p ≤ sᵖ` imply
`p = 0`. -/
theorem image_sharp_is_order_sharp {p s : Pred X} (hs : IsSharp s)
    (h₁ : p ≼ s) (h₂ : p ≼ orth s) : p = 0 := sorry

/-- **208III** (`diamond-oml`, eff.tex:4625, Proposition (Cho)), first half:
in a ⋄-effectus the sharp predicates form a sub-effect algebra of
`Pred X`. -/
theorem diamond_oml_subEA (X : C) :
    ∃ D : SubEffectAlgebra (Pred X),
      D.carrier = { p : Pred X | IsSharp p } := sorry

/-- **208III** (`diamond-oml`, eff.tex:4625, Proposition (Cho)), second
half: `SPred X` is an orthomodular lattice (for the order inherited from
`Pred X`, with orthocomplement `sᵖ`). -/
theorem diamond_oml (X : C) :
    ∃ oml : OrthomodularLattice (SPred X), ∀ s t : SPred X,
      (letI := oml
       (s ≤ t ↔ s.1 ≼ t.1) ∧ sᶜ = s.orth) := sorry

end DiamondBasics

/-- The category `OMLatGal` of orthomodular lattices with Galois
connections between them (Jacobs; needed for 208VII). -/
structure OMLatGalCat : Type (u + 1) where
  carrier : Type u
  [str : OrthomodularLattice carrier]

attribute [instance] OMLatGalCat.str

/-- A Galois connection between orthomodular lattices — the morphisms of
`OMLatGal` (208VII). -/
structure GaloisPair (A B : Type u) [OrthomodularLattice A]
    [OrthomodularLattice B] where
  push : A → B
  pull : B → A
  adj : ∀ (a : A) (b : B), push a ≤ b ↔ a ≤ pull b

instance : Category.{u} OMLatGalCat.{u} where
  Hom A B := GaloisPair A.carrier B.carrier
  id _ := ⟨_root_.id, _root_.id, fun _ _ => Iff.rfl⟩
  comp f g := ⟨g.push ∘ f.push, f.pull ∘ g.pull,
    fun _ _ => (g.adj _ _).trans (f.adj _ _)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- **208VII** (eff.tex:4661, Corollary): in a ⋄-effectus the assignment
`X ↦ SPred X`, `f ↦ (f_⋄, f^□)` yields a functor to `OMLatGal`, the
category of orthomodular lattices with Galois connections (Jacobs). -/
theorem diamond_omlatgal_functor [DiamondEffectus C] :
    ∃ F : C ⥤ OMLatGalCat.{v},
      ∀ X : C, (F.obj X).carrier = SPred X := sorry

section DiamondBasics2

variable [DiamondEffectus C] {X Y Z : C}

/-- **208IX** (`spred-infimum`, eff.tex:4676, Lemma): for sharp `s, t` the
infimum is `s ∧ t = (π_s)_⋄ ((π_s)^□ (t))`. -/
theorem spred_infimum {X : C} (s t : SPred X) :
    SPred.IsInf s t
      (diaPush (comprMap s.1) (boxPull (comprMap s.1) t)) := sorry

/-- **208XII** (`spred-sup`, eff.tex:4709, Exercise): for sharp `s, t` and a
quotient `ξ` for `s`, we have `(ξ^□ ∘ ξ_⋄)(t) = s ∨ t`. -/
theorem spred_sup {X : C} (s t : SPred X) :
    SPred.IsSup s t
      (boxPull (quotMap s.1) (diaPush (quotMap s.1) t)) := sorry

/-! ### ⋄-adjointness (parsec 209) -/

/-- **209II.1** (`exc-diamond-adj`, eff.tex:4722, Exercise): `f^⋄ = g_⋄` iff
`f_⋄ = g^⋄`. -/
theorem exc_diamond_adj_1 (f : X ⟶ Y) (g : Y ⟶ X) :
    DiamondAdjoint f g ↔ diaPush f = diaPull g := sorry

/-- **209II.2** (`exc-diamond-adj`, eff.tex:4722, Exercise): if `f` and `g`
are ⋄-adjoint, then `im f = ⌈1 ∘ g⌉`. -/
theorem exc_diamond_adj_2 {f : X ⟶ Y} {g : Y ⟶ X}
    (h : DiamondAdjoint f g) :
    imPred f = ceilPred (g ≫ truth X) := sorry

/-- **209III.1** (`diamond-squares`, eff.tex:4735, Exercise): if `f` is
⋄-self-adjoint, then so is `f ∘ f`. -/
theorem diamond_squares_1 {f : X ⟶ X} (h : DiamondSelfAdjoint f) :
    DiamondSelfAdjoint (f ≫ f) := sorry

/-- **209III.2** (`diamond-squares`, eff.tex:4735, Exercise): ⋄-positive
maps are ⋄-self-adjoint. -/
theorem diamond_squares_2 {f : X ⟶ X} (h : DiamondPositive f) :
    DiamondSelfAdjoint f := sorry

/-- **209III.3** (`diamond-squares`, eff.tex:4735, Exercise): if `f` is
⋄-positive and `f ∘ f` is pure, then `f ∘ f` is ⋄-positive. -/
theorem diamond_squares_3 {f : X ⟶ X} (h : DiamondPositive f)
    (hp : IsPure (f ≫ f)) : DiamondPositive (f ≫ f) := sorry

/-- **209IV.1** (`iso-diamond-adjoint`, eff.tex:4750, Lemma): for an
isomorphism `α`, the predicate `s ∘ α` is sharp for sharp `s`. -/
theorem iso_diamond_adjoint_1 (α : X ⟶ Y) [IsIso α] {s : Pred Y}
    (hs : IsSharp s) : IsSharp (α ≫ s) := sorry

/-- **209IV.2** (`iso-diamond-adjoint`, eff.tex:4750, Lemma): for an
isomorphism `α`, `α^⋄(s) = s ∘ α` and `α_⋄(s) = s ∘ α⁻¹`; in particular `α`
and `α⁻¹` are ⋄-adjoint. -/
theorem iso_diamond_adjoint_2 (α : X ⟶ Y) [IsIso α] :
    (∀ s : SPred Y, (diaPull α s).1 = α ≫ s.1) ∧
      (∀ s : SPred X, (diaPush α s).1 = inv α ≫ s.1) ∧
      DiamondAdjoint α (inv α) := sorry

/-! ### Sharp maps (parsec 210) -/

/-- **210I** (`sharp-map`, eff.tex:4779, Definition): a map `f` in a
⋄-effectus is **sharp** when `s ∘ f` is sharp for every sharp `s`. -/
def SharpMap (f : X ⟶ Y) : Prop :=
  ∀ s : Pred Y, IsSharp s → IsSharp (f ≫ s)

/-- **210II** (`sharp-ceil`, eff.tex:4784, Exercise): `f` is sharp iff
`⌈p ∘ f⌉ = ⌈p⌉ ∘ f` for every predicate `p`. -/
theorem sharp_ceil (f : X ⟶ Y) :
    SharpMap f ↔ ∀ p : Pred Y, ceilPred (f ≫ p) = f ≫ ceilPred p := sorry

end DiamondBasics2

/-! ## &-effectuses (parsec 211) -/

/-- **211II** (eff.tex:4809, Definition): an **&-effectus** ("andthen
effectus") is a ⋄-effectus such that

1. for each predicate `p` on `X` there is a unique ⋄-positive map
   `asrt_p : X ⟶ X` with `1 ∘ asrt_p = p`; and
2. for every quotient `ξ` and comprehension `π`, the composite `ξ ∘ π` is
   pure. -/
class AndThenEffectus (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop
    extends DiamondEffectus C where
  existsUnique_asrt : ∀ {X : C} (p : Pred X),
    ∃! f : X ⟶ X, DiamondPositive f ∧ f ≫ truth X = p
  quot_after_compr_pure : ∀ {X Y Z : C} {p q : Pred Y}
    (π : X ⟶ Y) (ξ : Y ⟶ Z),
    IsComprehension p π → IsQuotient q ξ → IsPure (π ≫ ξ)

section AndThen

variable [AndThenEffectus C] {X Y Z : C}

/-- **211II** (eff.tex:4818, Definition): the **assert map**
`asrt_p : X ⟶ X` of a predicate `p` — the unique ⋄-positive map with
`1 ∘ asrt_p = p`. -/
noncomputable def asrt (p : Pred X) : X ⟶ X :=
  (AndThenEffectus.existsUnique_asrt p).exists.choose

/-- The defining property of `asrt` (211II). -/
theorem asrt_spec (p : Pred X) :
    DiamondPositive (asrt p) ∧ asrt p ≫ truth X = p :=
  (AndThenEffectus.existsUnique_asrt p).exists.choose_spec

/-- Uniqueness of the assert map (211II). -/
theorem asrt_unique (p : Pred X) (f : X ⟶ X) (hf : DiamondPositive f)
    (h1 : f ≫ truth X = p) : f = asrt p :=
  (AndThenEffectus.existsUnique_asrt p).unique ⟨hf, h1⟩ (asrt_spec p)

/-- **211II** (eff.tex:4830, Definition): the sequential conjunction
`p & q = q ∘ asrt_p` ("`p` andthen `q`"); `p² = p & p`. -/
noncomputable def andThen (p q : Pred X) : Pred X := asrt p ≫ q

/-- **211IV** (`vn-is-andthen-eff`, eff.tex:4876, Examples): `vNᵒᵖ` is an
&-effectus, with `asrt_a(b) = √a b √a` (as are `CvNᵒᵖ` and `EJAᵒᵖ`, not
formalized here; these are the only known examples). -/
theorem vn_is_andthen_eff (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    AndThenEffectus WStarCPSU.{u}ᵒᵖ := sorry

/-- **211V** (`sharp-prop`, eff.tex:4889, Proposition): for a predicate `p`
in an &-effectus the following are equivalent: (1) `p` is sharp;
(2) `p & p = p`; (3) `asrt_p ∘ asrt_p = asrt_p`. -/
theorem sharp_prop (p : Pred X) :
    (IsSharp p ↔ andThen p p = p) ∧
      (IsSharp p ↔ asrt p ≫ asrt p = asrt p) := sorry

/-- **211VII** (`prop-corr-zeta-pi`, eff.tex:4951, Proposition), first
part: for sharp `s` there are a comprehension `π_s` for `s` and a quotient
`ζ_s` for `sᵖ` with `ζ_s ∘ π_s = id` and `π_s ∘ ζ_s = asrt_s`. -/
theorem prop_corr_zeta_pi {s : Pred X} (hs : IsSharp s) :
    ∃ (W : C) (π : W ⟶ X) (ζ : X ⟶ W),
      IsComprehension s π ∧ IsQuotient (orth s) ζ ∧
        π ≫ ζ = 𝟙 W ∧ ζ ≫ π = asrt s := sorry

/-- **211VII** (`prop-corr-zeta-pi`, eff.tex:4960, Proposition), second
part (with the uniqueness of 211IX): for *every* comprehension `π` for a
sharp `s` there is a unique quotient `ζ` for `sᵖ` with `ζ ∘ π = id` and
`π ∘ ζ = asrt_s`. -/
theorem prop_corr_zeta_pi_compr {s : Pred X} (hs : IsSharp s) {W : C}
    {π : W ⟶ X} (hπ : IsComprehension s π) :
    ∃! ζ : X ⟶ W,
      IsQuotient (orth s) ζ ∧ π ≫ ζ = 𝟙 W ∧ ζ ≫ π = asrt s := sorry

/-- **211VII** (`prop-corr-zeta-pi`, eff.tex:4963, Proposition), third
part: conversely, for every quotient `ζ` for `sᵖ` (`s` sharp) there is a
comprehension `π` for `s` with `ζ ∘ π = id` and `π ∘ ζ = asrt_s`. -/
theorem prop_corr_zeta_pi_quot {s : Pred X} (hs : IsSharp s) {W : C}
    {ζ : X ⟶ W} (hζ : IsQuotient (orth s) ζ) :
    ∃ π : W ⟶ X,
      IsComprehension s π ∧ π ≫ ζ = 𝟙 W ∧ ζ ≫ π = asrt s := sorry

/-- **211IX** (`zeta-s-convention`, eff.tex:5002, Notation): the
**corresponding quotient** `ζ_s : X ⟶ {X|s}` of the chosen comprehension
`π_s` for a sharp predicate `s`: the unique quotient for `sᵖ` with
`ζ_s ∘ π_s = id` and `π_s ∘ ζ_s = asrt_s`.  (Beware, 211X:
`ξ_{sᵖ} = ζ_s`.) -/
noncomputable def zetaMap (s : Pred X) (hs : IsSharp s) : X ⟶ comprObj s :=
  (prop_corr_zeta_pi_compr hs (isComprehension_comprMap s)).exists.choose

/-- The defining property of `ζ_s` (211IX). -/
theorem zetaMap_spec (s : Pred X) (hs : IsSharp s) :
    IsQuotient (orth s) (zetaMap s hs) ∧
      comprMap s ≫ zetaMap s hs = 𝟙 (comprObj s) ∧
      zetaMap s hs ≫ comprMap s = asrt s :=
  (prop_corr_zeta_pi_compr hs (isComprehension_comprMap s)).exists.choose_spec

/-- **211XI** (`upm-closed`, eff.tex:5020, Proposition), first half: in an
&-effectus comprehensions are closed under composition. -/
theorem upm_closed_compr {p : Pred Y} {q : Pred Z} {π₁ : X ⟶ Y}
    {π₂ : Y ⟶ Z} (h₁ : IsComprehension p π₁) (h₂ : IsComprehension q π₂) :
    ∃ r : Pred Z, IsComprehension r (π₁ ≫ π₂) := sorry

/-- **211XI** (`upm-closed`, eff.tex:5020, Proposition), second half: in an
&-effectus pure maps are closed under composition. -/
theorem upm_closed_pure {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsPure f) (hg : IsPure g) : IsPure (f ≫ g) := sorry

/-- **211XIV** (`andthen-square-rule`, eff.tex:5075, Exercise):
`asrt_p ∘ asrt_p = asrt_{p & p}`. -/
theorem andthen_square_rule (p : Pred X) :
    asrt p ≫ asrt p = asrt (andThen p p) := sorry

/-- **211XV** (`asrt-absorp-rule`, eff.tex:5079, Exercise): for sharp `s`
(on the codomain) and `t` (on the domain): `im f ≤ s ⟺ asrt_s ∘ f = f` and
`1 ∘ f ≤ t ⟺ f ∘ asrt_t = f`. -/
theorem asrt_absorp_rule (f : X ⟶ Y) {s : Pred Y} {t : Pred X}
    (hs : IsSharp s) (ht : IsSharp t) :
    (imPred f ≼ s ↔ f ≫ asrt s = f) ∧
      ((f ≫ truth Y) ≼ t ↔ asrt t ≫ f = f) := sorry

end AndThen

/-- **211XVI** (eff.tex:5088, Definition): the subcategory `Pure C` of pure
maps of an &-effectus (objects wrapped; closure under composition is
211XI). -/
structure PureCat (C : Type u) : Type u where
  of ::
  base : C

/-- The category structure of `Pure C` (211XVI; that identities are pure
and pure maps compose is `sorry`-ed, cf. 211XI). -/
instance PureCat.category [AndThenEffectus C] : Category.{v} (PureCat C) where
  Hom X Y := { f : X.base ⟶ Y.base // IsPure f }
  id X := ⟨𝟙 X.base, sorry⟩
  comp f g := ⟨f.1 ≫ g.1, sorry⟩
  id_comp _ := Subtype.ext (by simp)
  comp_id _ := Subtype.ext (by simp)
  assoc _ _ _ := Subtype.ext (by simp)

section AndThenMore

variable [AndThenEffectus C] {X Y : C}

/-- **212I** (`zeta-asrt-quot`, eff.tex:5097, Lemma): in an &-effectus,
`ζ_{⌈p⌉} ∘ asrt_p` is a quotient for `pᵖ`. -/
theorem zeta_asrt_quot (p : Pred X) :
    IsQuotient (orth p)
      (asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p)) := sorry

/-- **212III** (`standard-form-map`, eff.tex:5119, Proposition): every map
`f` in an &-effectus factors as
`f = π_{im f} ∘ g ∘ ζ_{⌈1∘f⌉} ∘ asrt_{1∘f}` for a unique total and faithful
`g`. -/
theorem standard_form_map (f : X ⟶ Y) :
    ∃! g : comprObj (ceilPred (f ≫ truth Y)) ⟶ comprObj (imPred f),
      (IsTotal g ∧ FaithfulMap g) ∧
        f = asrt (f ≫ truth Y) ≫
          zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
          comprMap (imPred f) := sorry

/-- **212III.1** (`standard-form-map`, eff.tex:5128, Proposition): if `f`
is pure, the total faithful part `g` of its standard form is an
isomorphism. -/
theorem standard_form_map_pure {f : X ⟶ Y} (hf : IsPure f)
    (g : comprObj (ceilPred (f ≫ truth Y)) ⟶ comprObj (imPred f))
    (hg : f = asrt (f ≫ truth Y) ≫
      zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
      comprMap (imPred f)) : IsIso g := sorry

/-- **212III.2** (`standard-form-map`, eff.tex:5128, Proposition): a pure
faithful map (`im f = 1`) is a quotient. -/
theorem standard_form_map_quot {f : X ⟶ Y} (hf : IsPure f)
    (him : FaithfulMap f) : ∃ p : Pred X, IsQuotient p f := sorry

/-- **212III.3** (`standard-form-map`, eff.tex:5128, Proposition): a pure
total map is a comprehension. -/
theorem standard_form_map_compr {f : X ⟶ Y} (hf : IsPure f)
    (ht : IsTotal f) : ∃ q : Pred Y, IsComprehension q f := sorry

end AndThenMore

/-- **213I** (`andthen-effect-divisoid`, eff.tex:5184, Proposition): if `C`
is an &-effectus, then `(Scal C)ᵒᵖ` (scalars with reversed multiplication)
is an effect divisoid. -/
theorem andthen_effect_divisoid [AndThenEffectus C] :
    Nonempty (EffectDivisoid (Scal C)ᵐᵒᵖ) := sorry

section AndThenSharp

variable [AndThenEffectus C] {X Y Z : C}

/-- **213III** (`perp-sharp-is-orth`, eff.tex:5224, Lemma): in an
&-effectus, if `s ⊥ t` for sharp `s, t` then `s & t = 0 = t & s`. -/
theorem perp_sharp_is_orth {s t : Pred X} (hs : IsSharp s) (ht : IsSharp t)
    (h : Perp s t) : andThen s t = 0 ∧ andThen t s = 0 := sorry

/-- **213V** (`simple-andthen-absorption`, eff.tex:5239, Exercise): for
sharp `s` and any predicate `p`: `p ≤ s ⟺ s & p = p`. -/
theorem simple_andthen_absorption {s p : Pred X} (hs : IsSharp s) :
    p ≼ s ↔ andThen s p = p := sorry

/-- **213VI** (`exc-prod-sharp-maps`, eff.tex:5246, Exercise): a pairing
`⟨f, g⟩` is a sharp map iff both `f` and `g` are sharp maps. -/
theorem exc_prod_sharp_maps (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) :
    SharpMap (effPair f g h) ↔ SharpMap f ∧ SharpMap g := sorry

end AndThenSharp

end Theses.B.Eff
