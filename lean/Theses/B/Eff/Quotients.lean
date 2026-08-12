/-
Theses/B/Eff/Quotients.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
3663–4407: effectuses with quotients (parsecs 197–198), effectuses with
comprehension (199), kernels (200), pure maps (201), images and faithful
maps (202), sharp predicates, floor and ceiling (203–204), and cokernels
(205).

Design:
* `IsQuotient p ξ` / `IsComprehension p π` are the universal properties of
  197II / 199II; `HasQuotients C` / `HasComprehension C` / `HasImages C`
  are Prop-classes asserting existence, with chosen witnesses `quotMap p`
  (`ξ_p`), `comprMap p` (`π_p`) and `imPred f` (`im f`) obtained by choice.
* Kernels/cokernels (200II) are defined with respect to the zero maps of
  the PCM-enrichment (an effectus in partial form has a zero object, so
  these agree with the usual categorical notions).
* Not separately formalized: the concrete examples 197IV/199V/202IV
  (quotients = filters and comprehensions = corners in `vNᵒᵖ`, `EJA`,
  `OUS`, `OUG`), the remark 198IV on the chain of adjunctions
  `Q ⊣ 0 ⊣ U ⊣ 1 ⊣ K` (its constituents are 198II/198III/199VI), the
  purity discussion 201III–201V, and the sharpness example 203III.
-/
import Theses.B.Eff.StatesPredicates

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits

namespace Theses.B.Eff

universe u v

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-! ## Effectuses with quotients (parsec 197) -/

/-- **197II** (`dfn-quotient`, eff.tex:3670, Definition): a map
`ξ : X ⟶ X/p` is a **quotient** for a predicate `p` on `X` when
`1 ∘ ξ ≤ pᵖ` and, universally, every `f : X ⟶ Y` with `1 ∘ f ≤ pᵖ` factors
as `f = f' ∘ ξ` for a unique `f'`. -/
def IsQuotient {X Q : C} (p : Pred X) (ξ : X ⟶ Q) : Prop :=
  (ξ ≫ truth Q) ≼ orth p ∧
    ∀ ⦃Y : C⦄ (f : X ⟶ Y), (f ≫ truth Y) ≼ orth p →
      ∃! f' : Q ⟶ Y, ξ ≫ f' = f

/-- **197II** (`dfn-quotient`, eff.tex:3672, Definition): an **effectus with
quotients**: every predicate has a quotient. -/
class HasQuotients (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop where
  quot : ∀ {X : C} (p : Pred X), ∃ (Q : C) (ξ : X ⟶ Q), IsQuotient p ξ

/-- **197III** (`quot-not`, eff.tex:3695, Notation): the codomain `X/p` of a
chosen quotient for `p`. -/
noncomputable def quotObj [HasQuotients C] {X : C} (p : Pred X) : C :=
  (HasQuotients.quot p).choose

/-- **197III** (`quot-not`, eff.tex:3695, Notation): a chosen quotient
`ξ_p : X ⟶ X/p` for `p`. -/
noncomputable def quotMap [HasQuotients C] {X : C} (p : Pred X) :
    X ⟶ quotObj p :=
  (HasQuotients.quot p).choose_spec.choose

/-- The chosen `ξ_p` is a quotient for `p` (197III). -/
theorem isQuotient_quotMap [HasQuotients C] {X : C} (p : Pred X) :
    IsQuotient p (quotMap p) :=
  (HasQuotients.quot p).choose_spec.choose_spec

section QuotientBasics

variable {X Q Q' Z : C}

/-- **197V.1** (`quotient-basics`, eff.tex:3729, Exercise): postcomposing a
quotient for `p` with an isomorphism yields a quotient for `p`. -/
theorem quotient_basics_1 {p : Pred X} {ξ : X ⟶ Q} (h : IsQuotient p ξ)
    (θ : Q ⟶ Z) [IsIso θ] : IsQuotient p (ξ ≫ θ) := sorry

/-- **197V.2** (`quotient-basics`, eff.tex:3737, Exercise): any two
quotients for `p` differ by a unique isomorphism. -/
theorem quotient_basics_2 {p : Pred X} {ξ₁ : X ⟶ Q} {ξ₂ : X ⟶ Q'}
    (h₁ : IsQuotient p ξ₁) (h₂ : IsQuotient p ξ₂) :
    ∃ θ : Q' ⟶ Q, IsIso θ ∧ ξ₂ ≫ θ = ξ₁ ∧
      ∀ θ' : Q' ⟶ Q, ξ₂ ≫ θ' = ξ₁ → θ' = θ := sorry

/-- **197V.3** (`quotient-basics`, eff.tex:3741, Exercise): isomorphisms are
quotients for `0`. -/
theorem quotient_basics_3 (f : X ⟶ Q) [IsIso f] :
    IsQuotient (0 : Pred X) f := sorry

/-- **197V.4** (`quotient-basics`, eff.tex:3742, Exercise): maps into the
zero object are quotients for `1`. -/
theorem quotient_basics_4 (f : X ⟶ (⊥_ C)) :
    IsQuotient (1 : Pred X) f := sorry

/-- **197V.5** (`quotient-basics`, eff.tex:3743, Exercise): if `ξ` is a
quotient for `p`, then `1 ∘ ξ = pᵖ`. -/
theorem quotient_basics_5 {p : Pred X} {ξ : X ⟶ Q} (h : IsQuotient p ξ) :
    ξ ≫ truth Q = orth p := sorry

/-- **197V.6** (`quotient-basics`, eff.tex:3745, Exercise): quotients are
epic. -/
theorem quotient_basics_6 {p : Pred X} {ξ : X ⟶ Q} (h : IsQuotient p ξ) :
    Epi ξ := sorry

/-- **197VII** (`quotient-total`, eff.tex:3755, Proposition): if
`ξ : X ⟶ X/pᵖ` is a quotient for `pᵖ`, then every `f : X ⟶ Z` with
`1 ∘ f = p` factors as `f = g ∘ ξ` for a unique *total* `g`.  (So every map
factors as a total map after a quotient.) -/
theorem quotient_total {p : Pred X} {ξ : X ⟶ Q} (hξ : IsQuotient (orth p) ξ)
    (f : X ⟶ Z) (hf : f ≫ truth Z = p) :
    ∃! g : Q ⟶ Z, IsTotal g ∧ ξ ≫ g = f := sorry

/-- **197IX** (`quotients-composition`, eff.tex:3772, Proposition): in an
effectus with quotients, quotients are closed under composition: if `ξ₁` is
a quotient for `pᵖ` and `ξ₂` a quotient for `qᵖ`, then `ξ₂ ∘ ξ₁` is a
quotient for `(q ∘ ξ₁)ᵖ`. -/
theorem quotients_composition [HasQuotients C] {Y : C} {p : Pred X}
    {q : Pred Y} {ξ₁ : X ⟶ Y} {ξ₂ : Y ⟶ Z}
    (h₁ : IsQuotient (orth p) ξ₁) (h₂ : IsQuotient (orth q) ξ₂) :
    IsQuotient (orth (ξ₁ ≫ q)) (ξ₁ ≫ ξ₂) := sorry

/-- **197XI** (`quot-fact-system`, eff.tex:3814, Exercise): (quotient, total)
is an orthogonal factorization system: if `t ∘ ξ = t' ∘ ξ'` with `ξ, ξ'`
quotients (for `p`, `p'`) and `t, t'` total, then there is a unique
isomorphism `θ` with `ξ' = θ ∘ ξ` and `t = t' ∘ θ`. -/
theorem quot_fact_system {p : Pred X} {p' : Pred X} {ξ : X ⟶ Q}
    {ξ' : X ⟶ Q'} {t : Q ⟶ Z} {t' : Q' ⟶ Z}
    (hξ : IsQuotient p ξ) (hξ' : IsQuotient p' ξ')
    (ht : IsTotal t) (ht' : IsTotal t') (hcomm : ξ ≫ t = ξ' ≫ t') :
    ∃ θ : Q ⟶ Q', IsIso θ ∧ ξ ≫ θ = ξ' ∧ θ ≫ t' = t ∧
      ∀ θ' : Q ⟶ Q', ξ ≫ θ' = ξ' → θ' = θ := sorry

end QuotientBasics

/-! ## The Grothendieck-style category `∫ Pred_□` (parsec 198) -/

/-- **198II** (`dfn-eff-grothendieck`, eff.tex:3838, Definition): the
category `∫ Pred_□` of an effectus `C`: objects are pairs `(X, p)` of an
object with a predicate; a morphism `(X,p) → (Y,q)` is a map `f : X ⟶ Y`
of `C` with `p ≤ (qᵖ ∘ f)ᵖ`. -/
structure PredSquare (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] :
    Type (max u v) where
  obj : C
  pred : Pred obj

/-- The category structure of `∫ Pred_□` (198II; that identities and
compositions satisfy the predicate inequality is `sorry`-ed). -/
instance : Category.{v} (PredSquare C) where
  Hom P R := { f : P.obj ⟶ R.obj // P.pred ≼ orth (f ≫ orth R.pred) }
  id P := ⟨𝟙 P.obj, sorry⟩
  comp f g := ⟨f.1 ≫ g.1, sorry⟩
  id_comp _ := Subtype.ext (by simp)
  comp_id _ := Subtype.ext (by simp)
  assoc _ _ _ := Subtype.ext (by simp)

/-- **198II** (`dfn-eff-grothendieck`, eff.tex:3852, Definition): the
forgetful functor `U : ∫ Pred_□ → C`. -/
def predSquareForget (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] :
    PredSquare C ⥤ C where
  obj P := P.obj
  map f := f.1

/-- **198II** (`dfn-eff-grothendieck`, eff.tex:3856, Definition): the
functor `0 : C → ∫ Pred_□`, `X ↦ (X, 0)`. -/
def predSquareZero (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] :
    C ⥤ PredSquare C where
  obj X := ⟨X, 0⟩
  map f := ⟨f, sorry⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

/-- **198II** (`dfn-eff-grothendieck`, eff.tex:3856, Definition): the
functor `1 : C → ∫ Pred_□`, `X ↦ (X, 1)`. -/
def predSquareOne (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] :
    C ⥤ PredSquare C where
  obj X := ⟨X, 1⟩
  map f := ⟨f, sorry⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

/-- **198II** (`dfn-eff-grothendieck`, eff.tex:3855, Definition): the
adjunction `0 ⊣ U`. -/
theorem predSquare_zero_adj :
    Nonempty (predSquareZero C ⊣ predSquareForget C) := sorry

/-- **198II** (`dfn-eff-grothendieck`, eff.tex:3855, Definition): the
adjunction `U ⊣ 1`. -/
theorem predSquare_one_adj :
    Nonempty (predSquareForget C ⊣ predSquareOne C) := sorry

/-- **198III** (`exc-quot-adjoint`, eff.tex:3862, Exercise\*): an effectus
has quotients if and only if the functor `0 : C → ∫ Pred_□` has a left
adjoint `Q`. -/
theorem exc_quot_adjoint :
    HasQuotients C ↔
      ∃ Q : PredSquare C ⥤ C, Nonempty (Q ⊣ predSquareZero C) := sorry

/-! ## Effectuses with comprehension (parsec 199) -/

/-- **199II** (`dfn-comprehension`, eff.tex:3912, Definition): a map
`π : {X|p} ⟶ X` is a **comprehension** for a predicate `p` on `X` when
`p ∘ π = 1 ∘ π` and, universally, every `g : Z ⟶ X` with `p ∘ g = 1 ∘ g`
factors as `g = π ∘ g'` for a unique `g'`.  (Comprehensions are *not*
assumed total; cf. 199III and 202VIII.) -/
def IsComprehension {W X : C} (p : Pred X) (π : W ⟶ X) : Prop :=
  π ≫ p = π ≫ truth X ∧
    ∀ ⦃Z : C⦄ (g : Z ⟶ X), g ≫ p = g ≫ truth X →
      ∃! g' : Z ⟶ W, g' ≫ π = g

/-- **199II** (`dfn-comprehension`, eff.tex:3914, Definition): an effectus
**has comprehension** when every predicate has a comprehension. -/
class HasComprehension (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop where
  compr : ∀ {X : C} (p : Pred X), ∃ (W : C) (π : W ⟶ X), IsComprehension p π

/-- **199IV** (`compr-not`, eff.tex:3945, Notation): the domain `{X|p}` of a
chosen comprehension for `p`. -/
noncomputable def comprObj [HasComprehension C] {X : C} (p : Pred X) : C :=
  (HasComprehension.compr p).choose

/-- **199IV** (`compr-not`, eff.tex:3945, Notation): a chosen comprehension
`π_p : {X|p} ⟶ X` for `p`. -/
noncomputable def comprMap [HasComprehension C] {X : C} (p : Pred X) :
    comprObj p ⟶ X :=
  (HasComprehension.compr p).choose_spec.choose

/-- The chosen `π_p` is a comprehension for `p` (199IV). -/
theorem isComprehension_comprMap [HasComprehension C] {X : C} (p : Pred X) :
    IsComprehension p (comprMap p) :=
  (HasComprehension.compr p).choose_spec.choose_spec

/-- **199VI** (`compr-grothendieck`, eff.tex:3977, Exercise\*): an effectus
has comprehension if and only if the functor `1 : C → ∫ Pred_□` has a right
adjoint `K`. -/
theorem compr_grothendieck :
    HasComprehension C ↔
      ∃ K : PredSquare C ⥤ C, Nonempty (predSquareOne C ⊣ K) := sorry

section ComprBasics

variable {W W' X Z : C}

/-- **199VII.1** (`compr-basics`, eff.tex:3983, Exercise): precomposing a
comprehension for `p` with an isomorphism yields a comprehension for
`p`. -/
theorem compr_basics_1 {p : Pred X} {π : W ⟶ X} (h : IsComprehension p π)
    (θ : W' ⟶ W) [IsIso θ] : IsComprehension p (θ ≫ π) := sorry

/-- **199VII.2** (`compr-basics`, eff.tex:3991, Exercise): any two
comprehensions for `p` differ by a unique isomorphism. -/
theorem compr_basics_2 {p : Pred X} {π₁ : W ⟶ X} {π₂ : W' ⟶ X}
    (h₁ : IsComprehension p π₁) (h₂ : IsComprehension p π₂) :
    ∃ θ : W ⟶ W', IsIso θ ∧ θ ≫ π₂ = π₁ ∧
      ∀ θ' : W ⟶ W', θ' ≫ π₂ = π₁ → θ' = θ := sorry

/-- **199VII.3** (`compr-basics`, eff.tex:3995, Exercise): isomorphisms are
comprehensions for `1`. -/
theorem compr_basics_3 (f : W ⟶ X) [IsIso f] :
    IsComprehension (1 : Pred X) f := sorry

/-- **199VII.4** (`compr-basics`, eff.tex:3996, Exercise): the zero map out
of the zero object is a comprehension for `0`. -/
theorem compr_basics_4 (X : C) :
    IsComprehension (0 : Pred X) (0 : (⊥_ C) ⟶ X) := sorry

/-- **199VII.5** (`compr-basics`, eff.tex:3997, Exercise): comprehensions
are monic. -/
theorem compr_basics_5 {p : Pred X} {π : W ⟶ X} (h : IsComprehension p π) :
    Mono π := sorry

/-- **199VII.6** (`compr-basics`, eff.tex:3998, Exercise): `pᵖ ∘ π = 0` for
a comprehension `π` for `p`. -/
theorem compr_basics_6 {p : Pred X} {π : W ⟶ X} (h : IsComprehension p π) :
    π ≫ orth p = 0 := sorry

end ComprBasics

/-! ## Kernels and cokernels (parsec 200) -/

/-- **200II** (eff.tex:4007, Definition): a **kernel** of `f : X ⟶ Y` is an
equalizer of `f` with the zero map: `k` with `f ∘ k = 0` such that every
`g` with `f ∘ g = 0` factors uniquely through `k`.  (Zero maps are those of
the PCM-enrichment; an effectus in partial form has a zero object.) -/
def IsKernel {W X Y : C} (f : X ⟶ Y) (k : W ⟶ X) : Prop :=
  k ≫ f = 0 ∧
    ∀ ⦃Z : C⦄ (g : Z ⟶ X), g ≫ f = 0 → ∃! g' : Z ⟶ W, g' ≫ k = g

/-- **200II** (eff.tex:4017, Definition): a **cokernel** of `f : X ⟶ Y` is
a kernel of `f` in `Cᵒᵖ`. -/
def IsCokernel {X Y W : C} (f : X ⟶ Y) (c : Y ⟶ W) : Prop :=
  f ≫ c = 0 ∧
    ∀ ⦃Z : C⦄ (g : Y ⟶ Z), f ≫ g = 0 → ∃! g' : W ⟶ Z, c ≫ g' = g

/-- **200III** (`effectus-kernels`, eff.tex:4022, Proposition): an effectus
with comprehension has all kernels; a kernel of `f` is given by a
comprehension for `(1 ∘ f)ᵖ`. -/
theorem effectus_kernels {W X Y : C} (f : X ⟶ Y) {π : W ⟶ X}
    (hπ : IsComprehension (orth (f ≫ truth Y)) π) : IsKernel f π := sorry

/-- **200V** (`compr-is-kernel`, eff.tex:4037, Exercise): in an effectus, a
map is a comprehension for `p` if and only if it is a kernel of `pᵖ`. -/
theorem compr_is_kernel {W X : C} (p : Pred X) (f : W ⟶ X) :
    IsComprehension p f ↔ IsKernel (orth p) f := sorry

/-! ## Pure maps (parsec 201) -/

/-- **201II** (eff.tex:4048, Definition): a map in an effectus is **pure**
if it is a comprehension after a quotient. -/
def IsPure {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ (Q : C) (ξ : X ⟶ Q) (π : Q ⟶ Y) (p : Pred X) (q : Pred Y),
    IsQuotient p ξ ∧ IsComprehension q π ∧ f = ξ ≫ π

/-! ## Images and faithful maps (parsec 202) -/

/-- **202I.1** (eff.tex:4097, Definition): a predicate `im` on `Y` is *the*
**image** of `f : X ⟶ Y` when it is the least predicate with
`im ∘ f = 1 ∘ f`. -/
def IsImage {X Y : C} (f : X ⟶ Y) (im : Pred Y) : Prop :=
  f ≫ im = f ≫ truth Y ∧
    ∀ p : Pred Y, f ≫ p = f ≫ truth Y → im ≼ p

/-- **202I.1** (eff.tex:4101, Definition): an effectus **has images** when
every map has an image. -/
class HasImages (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop where
  im : ∀ {X Y : C} (f : X ⟶ Y), ∃ p : Pred Y, IsImage f p

/-- **202II** (eff.tex:4122, Notation): the image `im f` of a map `f` in an
effectus with images (`im f ∘ g` is read as `im (f ∘ g)`; the thesis's
`im^⊥ f` is `orth (imPred f)`). -/
noncomputable def imPred [HasImages C] {X Y : C} (f : X ⟶ Y) : Pred Y :=
  (HasImages.im f).choose

/-- The defining property of `imPred` (202I). -/
theorem isImage_imPred [HasImages C] {X Y : C} (f : X ⟶ Y) :
    IsImage f (imPred f) :=
  (HasImages.im f).choose_spec

/-- **202I.2** (eff.tex:4114, Definition): a map `f : X ⟶ Y` is
**faithful** if `im f = 1`; equivalently, `p ∘ f = 0` implies `p = 0` for
every predicate `p` on `Y`. -/
def FaithfulMap {X Y : C} (f : X ⟶ Y) : Prop :=
  IsImage f (1 : Pred Y)

/-- **202I.2** (eff.tex:4117, Definition): the equivalent characterization
of faithfulness: `p ∘ f = 0` implies `p = 0`. -/
theorem faithfulMap_iff {X Y : C} (f : X ⟶ Y) :
    FaithfulMap f ↔ ∀ p : Pred Y, f ≫ p = 0 → p = 0 := sorry

/-- **202V** (`im-ineq`, eff.tex:4147, Exercise): `im (f ∘ g) ≤ im f`, with
equality when `g` is an isomorphism. -/
theorem im_ineq [HasImages C] {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ X) :
    imPred (g ≫ f) ≼ imPred f ∧
      (∀ (α : Z ⟶ X), IsIso α → imPred (α ≫ f) = imPred f) := sorry

/-- **202VI** (`exc-quot-faithful`, eff.tex:4152, Exercise): quotients are
faithful. -/
theorem exc_quot_faithful {X Q : C} {p : Pred X} {ξ : X ⟶ Q}
    (h : IsQuotient p ξ) : FaithfulMap ξ := sorry

/-- **202VIII** (`compr-total`, eff.tex:4162, Lemma): in an effectus with
quotients, comprehensions are total. -/
theorem compr_total [HasQuotients C] {W X : C} {p : Pred X} {π : W ⟶ X}
    (h : IsComprehension p π) : IsTotal π := sorry

/-! ## Sharp predicates, floor and ceiling (parsecs 203–204) -/

/-- **203I.1** (eff.tex:4185, Definition): a predicate is (image) **sharp**
if it is the image of some map.  (`SPred X` is the set of sharp predicates
on `X`.) -/
def IsSharp {X : C} (p : Pred X) : Prop :=
  ∃ (Y : C) (f : Y ⟶ X), IsImage f p

/-- **203I.1** (eff.tex:4191, Definition): the set `SPred X` of sharp
predicates on `X`. -/
def SPred (X : C) : Type v := { p : Pred X // IsSharp p }

/-- **203I.2** (eff.tex:4194, Definition): the **floor**
`⌊p⌋ = im π_p` of a predicate (comprehensions for the same predicate have
the same image by 202V). -/
noncomputable def floorPred [HasComprehension C] [HasImages C] {X : C}
    (p : Pred X) : Pred X :=
  imPred (comprMap p)

/-- **203I.2** (eff.tex:4198, Definition): the **ceiling**
`⌈p⌉ = ⌊pᵖ⌋ᵖ` of a predicate. -/
noncomputable def ceilPred [HasComprehension C] [HasImages C] {X : C}
    (p : Pred X) : Pred X :=
  orth (floorPred (orth p))

section FloorBasics

variable [HasComprehension C] [HasImages C] {X Y : C}

/-- **203IV.1** (`floor-basics`, eff.tex:4217, Lemma): `⌊p⌋ ≤ p`. -/
theorem floor_basics_1 (p : Pred X) : floorPred p ≼ p := sorry

/-- **203IV.2** (`floor-basics`, eff.tex:4217, Lemma):
`π_p = π_{⌊p⌋} ∘ α` for some isomorphism `α` (indeed `π_p` is also a
comprehension for `⌊p⌋`). -/
theorem floor_basics_2 (p : Pred X) :
    ∃ α : comprObj p ⟶ comprObj (floorPred p),
      IsIso α ∧ α ≫ comprMap (floorPred p) = comprMap p := sorry

/-- **203IV.3** (`floor-basics`, eff.tex:4217, Lemma): `⌊⌊p⌋⌋ = ⌊p⌋`. -/
theorem floor_basics_3 (p : Pred X) :
    floorPred (floorPred p) = floorPred p := sorry

/-- **203IV.4** (`floor-basics`, eff.tex:4217, Lemma): `p ≤ q` implies
`⌊p⌋ ≤ ⌊q⌋`. -/
theorem floor_basics_4 {p q : Pred X} (h : p ≼ q) :
    floorPred p ≼ floorPred q := sorry

/-- **203IV.5** (`floor-basics`, eff.tex:4217, Lemma):
`⌈p⌉ ∘ f ≤ ⌈p ∘ f⌉`. -/
theorem floor_basics_5 (p : Pred X) (f : Y ⟶ X) :
    (f ≫ ceilPred p) ≼ ceilPred (f ≫ p) := sorry

/-- **203IV.6** (`floor-basics`, eff.tex:4217, Lemma): `⌈p⌉ ∘ f = 0` iff
`p ∘ f = 0`. -/
theorem floor_basics_6 (p : Pred X) (f : Y ⟶ X) :
    f ≫ ceilPred p = 0 ↔ f ≫ p = 0 := sorry

/-- **203XII** (`img-of-compr`, eff.tex:4301, Exercise): `p` is sharp iff
`⌊p⌋ = p`; consequently `im π_s = s` for sharp `s`. -/
theorem img_of_compr (p : Pred X) :
    (IsSharp p ↔ floorPred p = p) ∧
      (∀ s : Pred X, IsSharp s → imPred (comprMap s) = s) := sorry

/-- **203XIII** (`ceiling-within-ceiling`, eff.tex:4306, Exercise):
`⌈⌈p⌉ ∘ f⌉ = ⌈p ∘ f⌉`. -/
theorem ceiling_within_ceiling (p : Pred X) (f : Y ⟶ X) :
    ceilPred (f ≫ ceilPred p) = ceilPred (f ≫ p) := sorry

end FloorBasics

/-- **203XIV** (`img-tupling`, eff.tex:4312, Exercise), first half: in an
effectus with images, `im ⟨f, g⟩ = [im f, im g]`. -/
theorem img_tupling [HasImages C] {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) :
    imPred (effPair f g h) = coprod.desc (imPred f) (imPred g) := sorry

/-- **203XIV** (`img-tupling`, eff.tex:4312, Exercise), second half: a
predicate `[p, q]` is sharp iff `p` and `q` are sharp. -/
theorem img_tupling_sharp [HasImages C] {X Y : C} (p : Pred X) (q : Pred Y) :
    IsSharp (coprod.desc p q : X ⨿ Y ⟶ effObj C) ↔ IsSharp p ∧ IsSharp q :=
  sorry

/-- **204I** (`compr-is-full`, eff.tex:4321, Lemma): for sharp predicates
`s, t` on the same object, `s ≤ t` iff `π_s` factors through `π_t`. -/
theorem compr_is_full [HasComprehension C] [HasImages C] {X : C}
    {s t : Pred X} (hs : IsSharp s) (ht : IsSharp t) :
    s ≼ t ↔ ∃ h : comprObj s ⟶ comprObj t, h ≫ comprMap t = comprMap s :=
  sorry

/-- **204III** (eff.tex:4347, Lemma): in an effectus with images,
`im [f, g] = im f ∨ im g` (a supremum among all predicates). -/
theorem im_cotuple_sup [HasImages C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PCM.IsSup (imPred f) (imPred g) (imPred (coprod.desc f g)) := sorry

/-- **204V** (`lattice-compr`, eff.tex:4370, Corollary): in an effectus
with comprehension and images, sharp predicates `s, t` have a supremum
`s ∨ t = im [π_s, π_t]` among all predicates, which is itself sharp. -/
theorem lattice_compr [HasComprehension C] [HasImages C] {X : C}
    {s t : Pred X} (hs : IsSharp s) (ht : IsSharp t) :
    PCM.IsSup s t (imPred (coprod.desc (comprMap s) (comprMap t))) ∧
      IsSharp (imPred (coprod.desc (comprMap s) (comprMap t))) := sorry

/-! ## Cokernels (parsec 205) -/

/-- **205II** (`effectus-cokernels`, eff.tex:4386, Proposition): an effectus
with quotients and images has all cokernels; a cokernel of `f` is given by
a quotient for `im f`. -/
theorem effectus_cokernels [HasImages C] {X Y Q : C} (f : X ⟶ Y)
    {ξ : Y ⟶ Q} (hξ : IsQuotient (imPred f) ξ) : IsCokernel f ξ := sorry

/-- **205IV** (`exc-cokernels`, eff.tex:4400, Exercise): in an effectus
with comprehension and images, a map `f` is a quotient for a sharp
predicate `s` iff `f` is a cokernel of a comprehension `π_s` for `s`. -/
theorem exc_cokernels [HasComprehension C] [HasImages C] {X Z : C}
    {s : Pred X} (hs : IsSharp s) (f : X ⟶ Z) :
    IsQuotient s f ↔ IsCokernel (comprMap s) f := sorry

end Theses.B.Eff
