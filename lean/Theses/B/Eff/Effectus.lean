/-
Theses/B/Eff/Effectus.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines 748–2069:
the definition of an effectus in total form and in partial form (finPACs,
PCM-enrichment), the category of partial maps `Par C`, the subcategory of
total maps `Tot C`, the intermediate lemmas on pullbacks and joint monicity,
and Cho's theorem that the two forms of effectus are equivalent.

Design:
* An *effectus in total form* is a Prop-class `EffectusTotalForm C` over
  `[Category C] [HasFiniteCoproducts C] [HasTerminal C]`.
* The PCM-enrichment of an effectus in partial form is an instance argument
  `[∀ X Y : C, PCM (X ⟶ Y)]`; `FinPAC C` is a Prop-class of compatibility
  axioms over it, and `EffectusPartialForm C` is a data class providing the
  distinguished object `I` and the effect algebra structure of the
  predicates `X ⟶ I` (as extra operations/axioms on top of the hom-PCM,
  so that `EffectAlgebra (X ⟶ I)` is a genuine, `sorry`-free instance).
* `Par C` and `Tot C` are wrapper structures carrying the partial/total map
  category structure; `EffectusTotalStructure`/`EffectusPartialStructure`
  bundle the data needed to say "`D` *is* an effectus in total/partial
  form" in existence statements (Cho's theorem).
-/
import Theses.B.Eff.EffectAlgebras
import Theses.B.Eff.WStarCat
-- for 189aII.3(c): Mathlib's `FinitaryExtensive (CompHausLike P)`
import Mathlib.Topology.Category.CompHaus.Limits

set_option warn.classDefReducibility false
-- several proofs below do not need all of the ambient effectus structure
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits

namespace Theses.B.Eff

universe u v

/-- Two parallel-source maps `f : P ⟶ X`, `g : P ⟶ Y` are **jointly monic**
when `a ≫ f = b ≫ f` and `a ≫ g = b ≫ g` imply `a = b` (used in the third
axiom of 180I, and in 183–186). -/
def JointlyMonic {D : Type u} [Category.{v} D] {P X Y : D}
    (f : P ⟶ X) (g : P ⟶ Y) : Prop :=
  ∀ ⦃Z : D⦄ (a b : Z ⟶ P), a ≫ f = b ≫ f → a ≫ g = b ≫ g → a = b

/-! ## Effectus in total form (parsec 180) -/

/-- **180I** (`dfn-effectus`, eff.tex:755, Definition): a category `C` is an
**effectus in total form** if

1. `C` has finite coproducts and a final object `1`;
2. the squares
   ```
   X+Y --id+!--> X+1        X --!--> 1
    |!+id         |!+id      |κ₁      |κ₁
    v             v          v        v
   1+Y --id+!--> 1+1        X+Y -!+!-> 1+1
   ```
   are pullbacks; and
3. the cotuples `[κ₁,κ₂,κ₂], [κ₂,κ₁,κ₂] : 1+1+1 ⟶ 1+1` are jointly monic. -/
class EffectusTotalForm (C : Type u) [Category.{v} C]
    [HasFiniteCoproducts C] [HasTerminal C] : Prop where
  isPullback_plus : ∀ X Y : C,
    IsPullback (coprod.map (𝟙 X) (terminal.from Y))
      (coprod.map (terminal.from X) (𝟙 Y))
      (coprod.map (terminal.from X) (𝟙 (⊤_ C)))
      (coprod.map (𝟙 (⊤_ C)) (terminal.from Y))
  isPullback_kappa : ∀ X Y : C,
    IsPullback (terminal.from X) (coprod.inl : X ⟶ X ⨿ Y)
      (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
      (coprod.map (terminal.from X) (terminal.from Y))
  jointlyMonic_cotuples :
    JointlyMonic
      (coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr :
        ((⊤_ C) ⨿ (⊤_ C)) ⨿ (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
      (coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr)

/-- **180I** (`dfn-effectus`, eff.tex:792, Definition): an arrow
`X ⟶ Y + 1` is called a **partial map** and written `X ⇸ Y`. -/
abbrev PartialMap {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [HasTerminal C] (X Y : C) :=
  X ⟶ Y ⨿ ⊤_ C

/-! ### The category of partial maps `Par C` (180VI, 186I) -/

/-- The objects of the category `Par C` of partial maps of `C` (a wrapper
structure to keep the two category structures apart). -/
structure Par (C : Type u) : Type u where
  of ::
  base : C

section ParCat

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasTerminal C]

/-- **180VI** (eff.tex:842): the **category of partial maps** `Par C` of an
effectus `C` in total form: same objects, morphisms `X ⟶ Y + 1`, Kleisli
composition `g ⊙ f = [g, κ₂] ∘ f`, identity `κ₁`.  (`Par C` is the Kleisli
category of the monad `(–) + 1`.)  The category structure needs only finite
coproducts and a final object. -/
noncomputable instance Par.category : Category.{v} (Par C) where
  Hom X Y := X.base ⟶ Y.base ⨿ ⊤_ C
  id X := (coprod.inl : X.base ⟶ X.base ⨿ ⊤_ C)
  comp {X Y Z} f g := f ≫ coprod.desc g coprod.inr
  id_comp f := coprod.inl_desc f coprod.inr
  comp_id f := by
    show f ≫ coprod.desc coprod.inl coprod.inr = f
    rw [coprod.desc_inl_inr, Category.comp_id]
  assoc f g h := by
    show (f ≫ coprod.desc g coprod.inr) ≫ coprod.desc h coprod.inr
        = f ≫ coprod.desc (g ≫ coprod.desc h coprod.inr) coprod.inr
    rw [Category.assoc, coprod.desc_comp, coprod.inr_desc]

/-- **186I** (eff.tex:1524, Definition): for `f : X ⟶ Y` in an effectus `C`
in total form, `f̂ = κ₁ ∘ f : X ⇸ Y` — the Kleisli embedding
`C → Par C`. -/
noncomputable def Par.hat {X Y : C} (f : X ⟶ Y) : Par.of X ⟶ Par.of Y :=
  (f ≫ coprod.inl : X ⟶ Y ⨿ ⊤_ C)

/-- **186VI** (`zero-and-one-parc`, eff.tex:1602, Definition): the zero
partial map `0 = κ₂ ∘ ! : X ⇸ Y`. -/
noncomputable def Par.zero (X Y : C) : Par.of X ⟶ Par.of Y :=
  (terminal.from X ≫ coprod.inr : X ⟶ Y ⨿ ⊤_ C)

/-- **186VI** (`zero-and-one-parc`, eff.tex:1602, Definition): the truth
predicate `1 = κ₁ ∘ ! = !̂ : X ⇸ 1`. -/
noncomputable def Par.one (X : C) : Par.of X ⟶ Par.of (⊤_ C) :=
  Par.hat (terminal.from X)

/-- The coproduct-functor on partial maps: `f + g` in `Par C`, computed in
`C` as `[(κ₁+id) ∘ f, (κ₂+id) ∘ g]` (cf. 186III, `beware`). -/
noncomputable def Par.map {X X' Y Y' : C} (f : Par.of X ⟶ Par.of X')
    (g : Par.of Y ⟶ Par.of Y') : Par.of (X ⨿ Y) ⟶ Par.of (X' ⨿ Y') :=
  (coprod.desc
    ((show X ⟶ X' ⨿ ⊤_ C from f) ≫ coprod.map coprod.inl (𝟙 (⊤_ C)))
    ((show Y ⟶ Y' ⨿ ⊤_ C from g) ≫ coprod.map coprod.inr (𝟙 (⊤_ C))) :
      X ⨿ Y ⟶ (X' ⨿ Y') ⨿ ⊤_ C)

/-- The partial projector `▷₁ = [id, 0] : X + Y ⇸ X` in `Par C`
(cf. 180VII, 186X). -/
noncomputable def Par.pproj₁ (X Y : C) : Par.of (X ⨿ Y) ⟶ Par.of X :=
  (coprod.desc coprod.inl (show Y ⟶ X ⨿ ⊤_ C from Par.zero Y X) :
    X ⨿ Y ⟶ X ⨿ ⊤_ C)

/-- The partial projector `▷₂ = [0, id] : X + Y ⇸ Y` in `Par C`. -/
noncomputable def Par.pproj₂ (X Y : C) : Par.of (X ⨿ Y) ⟶ Par.of Y :=
  (coprod.desc (show X ⟶ Y ⨿ ⊤_ C from Par.zero X Y) coprod.inl :
    X ⨿ Y ⟶ Y ⨿ ⊤_ C)

end ParCat

/-! ## Effectus in partial form (180VII) -/

section PartialForm

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]

/-- The partial projector `▷₁ = [id, 0] : X + Y ⟶ X` in a category whose
hom-sets carry PCM structure (180VII). -/
noncomputable def pproj₁ [∀ X Y : C, PCM (X ⟶ Y)] (X Y : C) : X ⨿ Y ⟶ X :=
  coprod.desc (𝟙 X) 0

/-- The partial projector `▷₂ = [0, id] : X + Y ⟶ Y`. -/
noncomputable def pproj₂ [∀ X Y : C, PCM (X ⟶ Y)] (X Y : C) : X ⨿ Y ⟶ Y :=
  coprod.desc 0 (𝟙 Y)

/-- **180VII** (`effectus-in-partial-form`, eff.tex:862, Definition),
part 1: `C` is a **finPAC** (finitarily partially additive category) when it
has finite coproducts `(+, 0)`, is PCM-enriched (each hom-set is a PCM, an
instance argument here; composition preserves `⋁` and `0` on both sides),
and satisfies:

* *(compatible sum)* for `b : X ⟶ Y + Y` we have `▷₁ ∘ b ⊥ ▷₂ ∘ b`; and
* *(untying)* if `f ⊥ g` then `κ₁ ∘ f ⊥ κ₂ ∘ g`. -/
class FinPAC (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] : Prop where
  comp_ovee : ∀ {X Y Z : C} {f g : X ⟶ Y} (h : Perp f g) (k : Y ⟶ Z),
    ∃ h' : Perp (f ≫ k) (g ≫ k), ovee f g h ≫ k = ovee (f ≫ k) (g ≫ k) h'
  ovee_comp : ∀ {W X Y : C} {f g : X ⟶ Y} (h : Perp f g) (k : W ⟶ X),
    ∃ h' : Perp (k ≫ f) (k ≫ g), k ≫ ovee f g h = ovee (k ≫ f) (k ≫ g) h'
  comp_zero : ∀ {X Y Z : C} (f : X ⟶ Y), f ≫ (0 : Y ⟶ Z) = 0
  zero_comp : ∀ {X Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = 0
  compatible_sum : ∀ {X Y : C} (b : X ⟶ Y ⨿ Y),
    Perp (b ≫ pproj₁ Y Y) (b ≫ pproj₂ Y Y)
  untying : ∀ {X Y : C} {f g : X ⟶ Y}, Perp f g →
    Perp (f ≫ (coprod.inl : Y ⟶ Y ⨿ Y)) (g ≫ (coprod.inr : Y ⟶ Y ⨿ Y))

/-- **180VII** (`effectus-in-partial-form`, eff.tex:862, Definition),
part 2: an **effectus in partial form** is a finPAC `C` *with effects*:
there is a distinguished object `I` such that

* each PCM `C(X, I) = Pred X` is an effect algebra (its extra structure —
  truth `one`, orthocomplement `orth` and their axioms — is given here on
  top of the hom-PCM, making `EffectAlgebra (X ⟶ I)` a genuine instance);
* if `1 ∘ f ⊥ 1 ∘ g` then `f ⊥ g`; and
* if `1 ∘ f = 0` then `f = 0`.

A map `f : X ⟶ Y` is **total** if `1 ∘ f = 1` (see `IsTotal`). -/
class EffectusPartialForm (C : Type u) [Category.{v} C]
    [HasFiniteCoproducts C] [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] where
  I : C
  one : ∀ X : C, X ⟶ I
  orth : ∀ {X : C}, (X ⟶ I) → (X ⟶ I)
  perp_orth : ∀ {X : C} (p : X ⟶ I), Perp p (orth p)
  ovee_orth : ∀ {X : C} (p : X ⟶ I), ovee p (orth p) (perp_orth p) = one X
  orth_unique : ∀ {X : C} {p q : X ⟶ I} (h : Perp p q),
    ovee p q h = one X → q = orth p
  eq_zero_of_perp_one : ∀ {X : C} {p : X ⟶ I}, Perp p (one X) → p = 0
  perp_of_one_perp : ∀ {X Y : C} {f g : X ⟶ Y},
    Perp (f ≫ one Y) (g ≫ one Y) → Perp f g
  eq_zero_of_one_zero : ∀ {X Y : C} {f : X ⟶ Y}, f ≫ one Y = 0 → f = 0

end PartialForm

section PartialEffectus

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- The distinguished effect object `I` of an effectus in partial form
(written `1` after convention 189II). -/
abbrev effObj (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : C :=
  EffectusPartialForm.I (C := C)

/-- The truth predicate `1 : X ⟶ I` of an effectus in partial form. -/
def truth (X : C) : X ⟶ effObj C := EffectusPartialForm.one X

/-- **180VII** (`effectus-in-partial-form`, eff.tex:933, Definition): a map
`f : X ⟶ Y` in an effectus in partial form is **total** if `1 ∘ f = 1`. -/
def IsTotal {X Y : C} (f : X ⟶ Y) : Prop := f ≫ truth Y = truth X

/-- **180VII** (`effectus-in-partial-form`, eff.tex:862, Definition): the
predicates `Pred X = C(X, I)` of an effectus in partial form form an effect
algebra (assembled, `sorry`-free, from the hom-PCM and the effects data of
`EffectusPartialForm`). -/
instance predEffectAlgebra (X : C) : EffectAlgebra (X ⟶ effObj C) :=
  { (inferInstance : PCM (X ⟶ effObj C)) with
    one := truth X
    orth := EffectusPartialForm.orth
    perp_orth := EffectusPartialForm.perp_orth
    ovee_orth := EffectusPartialForm.ovee_orth
    orth_unique := fun h => EffectusPartialForm.orth_unique h
    eq_zero_of_perp_one := fun h => EffectusPartialForm.eq_zero_of_perp_one h }

/-! ### The subcategory of total maps `Tot C` -/

/-- The objects of the category `Tot C` of total maps of an effectus `C` in
partial form (a wrapper structure; cf. 181XI). -/
structure Tot (C : Type u) : Type u where
  of ::
  base : C

/-- The wide subcategory `Tot C` of total maps of an effectus in partial
form (181XI; that total maps are closed under identity and composition is
part of the proof of `eff_partial_to_total`, here discharged directly). -/
instance Tot.category : Category.{v} (Tot C) where
  Hom X Y := { f : X.base ⟶ Y.base // IsTotal f }
  id X := ⟨𝟙 X.base, by simp [IsTotal]⟩
  comp {X Y Z} f g := ⟨f.1 ≫ g.1, show (f.1 ≫ g.1) ≫ truth Z.base = truth X.base by
    rw [Category.assoc, show g.1 ≫ truth Z.base = truth Y.base from g.2,
      show f.1 ≫ truth Y.base = truth X.base from f.2]⟩
  id_comp f := Subtype.ext (by simp)
  comp_id f := Subtype.ext (by simp)
  assoc f g h := Subtype.ext (by simp)

end PartialEffectus

/-! ### Bundled effectus structures and Cho's theorem (180X) -/

/-- The bundled data witnessing that a category `D` *is* an effectus in
total form: finite coproducts, a final object, and the axioms of 180I.
Used to state existence results such as Cho's theorem. -/
structure EffectusTotalStructure (D : Type u) [Category.{v} D] where
  hasFiniteCoproducts : HasFiniteCoproducts D
  hasTerminal : HasTerminal D
  effectus : @EffectusTotalForm D _ hasFiniteCoproducts hasTerminal

/-- The bundled data witnessing that a category `D` *is* an effectus in
partial form: finite coproducts, a PCM-enrichment, the finPAC axioms and
the effects structure of 180VII. -/
structure EffectusPartialStructure (D : Type u) [Category.{v} D] where
  hasFiniteCoproducts : HasFiniteCoproducts D
  homPCM : ∀ X Y : D, PCM (X ⟶ Y)
  finPAC : @FinPAC D _ hasFiniteCoproducts homPCM
  effectus : @EffectusPartialForm D _ hasFiniteCoproducts homPCM finPAC

/-! The two halves of Cho's theorem **180X** are stated and proved below,
after the machinery of parsecs 181–187 that they rest on. -/

/-! ## From partial to total (parsec 181) -/

section PartialToTotal

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-! ### Toolkit for the PCM-enrichment -/

/-- Postcomposition preserves `⊥` (from the finPAC axiom `comp_ovee`). -/
private theorem perp_comp_right {X Y Z : C} {f g : X ⟶ Y} (h : Perp f g)
    (k : Y ⟶ Z) : Perp (f ≫ k) (g ≫ k) := (FinPAC.comp_ovee h k).choose

/-- Postcomposition preserves `⋁`. -/
private theorem ovee_comp_right {X Y Z : C} {f g : X ⟶ Y} (h : Perp f g)
    (k : Y ⟶ Z) (h' : Perp (f ≫ k) (g ≫ k)) :
    ovee f g h ≫ k = ovee (f ≫ k) (g ≫ k) h' := (FinPAC.comp_ovee h k).choose_spec

/-- Precomposition preserves `⊥` (from the finPAC axiom `ovee_comp`). -/
private theorem perp_comp_left {W X Y : C} {f g : X ⟶ Y} (h : Perp f g)
    (k : W ⟶ X) : Perp (k ≫ f) (k ≫ g) := (FinPAC.ovee_comp h k).choose

/-- Precomposition preserves `⋁`. -/
private theorem ovee_comp_left {W X Y : C} {f g : X ⟶ Y} (h : Perp f g)
    (k : W ⟶ X) (h' : Perp (k ≫ f) (k ≫ g)) :
    k ≫ ovee f g h = ovee (k ≫ f) (k ≫ g) h' := (FinPAC.ovee_comp h k).choose_spec

private theorem le_comp_left {W X Y : C} {a b : X ⟶ Y} (h : a ≼ b) (k : W ⟶ X) :
    (k ≫ a) ≼ (k ≫ b) := by
  obtain ⟨c, hac, rfl⟩ := h
  exact ⟨k ≫ c, perp_comp_left hac k, (ovee_comp_left hac k _).symm⟩

/-- Every predicate is below the truth predicate. -/
private theorem le_truth {X : C} (p : X ⟶ effObj C) : p ≼ truth X :=
  ⟨EffectusPartialForm.orth p, EffectusPartialForm.perp_orth p,
    EffectusPartialForm.ovee_orth p⟩

private theorem pred_le_antisymm {X : C} {p q : X ⟶ effObj C}
    (h₁ : p ≼ q) (h₂ : q ≼ p) : p = q :=
  eabasics_le_antisymm (E := (X ⟶ effObj C)) h₁ h₂

private theorem inl_pproj₁ (X Y : C) :
    (coprod.inl : X ⟶ X ⨿ Y) ≫ pproj₁ X Y = 𝟙 X := coprod.inl_desc _ _

private theorem inr_pproj₁ (X Y : C) :
    (coprod.inr : Y ⟶ X ⨿ Y) ≫ pproj₁ X Y = 0 := coprod.inr_desc _ _

private theorem inl_pproj₂ (X Y : C) :
    (coprod.inl : X ⟶ X ⨿ Y) ≫ pproj₂ X Y = 0 := coprod.inl_desc _ _

private theorem inr_pproj₂ (X Y : C) :
    (coprod.inr : Y ⟶ X ⨿ Y) ≫ pproj₂ X Y = 𝟙 Y := coprod.inr_desc _ _

private theorem pproj₁_comp {X Y Z : C} (k : X ⟶ Z) :
    pproj₁ X Y ≫ k = coprod.desc k 0 := by
  rw [pproj₁, coprod.desc_comp, Category.id_comp, FinPAC.zero_comp]

private theorem pproj₂_comp {X Y Z : C} (k : Y ⟶ Z) :
    pproj₂ X Y ≫ k = coprod.desc 0 k := by
  rw [pproj₂, coprod.desc_comp, Category.id_comp, FinPAC.zero_comp]

/-- **181II** (`coproj-total`, eff.tex:985, Lemma): in an effectus in
partial form, coprojections are total. -/
theorem coproj_total_inl (X Y : C) : IsTotal (coprod.inl : X ⟶ X ⨿ Y) := by
  refine pred_le_antisymm (le_truth _) ?_
  have h := le_comp_left (le_truth (pproj₁ X Y ≫ truth X)) (coprod.inl : X ⟶ X ⨿ Y)
  rwa [← Category.assoc, inl_pproj₁, Category.id_comp] at h

/-- **181II** (`coproj-total`, eff.tex:985, Lemma): in an effectus in
partial form, coprojections are total (second coprojection). -/
theorem coproj_total_inr (X Y : C) : IsTotal (coprod.inr : Y ⟶ X ⨿ Y) := by
  refine pred_le_antisymm (le_truth _) ?_
  have h := le_comp_left (le_truth (pproj₂ X Y ≫ truth Y)) (coprod.inr : Y ⟶ X ⨿ Y)
  rwa [← Category.assoc, inr_pproj₂, Category.id_comp] at h

variable {X Y Z : C}

/-- Helper for `pcm_middle_four`: the two-element list `[a, b]` sums to
`a ⋁ b`. -/
private theorem pcm_isSumOf_pair {M : Type*} [PCM M] {a b : M} (h : Perp a b) :
    PCM.IsSumOf [a, b] (ovee a b h) := by
  have hb : PCM.IsSumOf [b] b := by
    have hx := PCM.IsSumOf.cons (PCM.IsSumOf.nil (M := M)) (PCM.perp_zero b)
    rwa [PCM.ovee_zero] at hx
  exact PCM.IsSumOf.cons hb h

/-- Helper for `pcm_middle_four`: inversion of `pcm_isSumOf_pair`. -/
private theorem pcm_isSumOf_pair_iff {M : Type*} [PCM M] {a b s : M} :
    PCM.IsSumOf [a, b] s ↔ ∃ h : Perp a b, ovee a b h = s := by
  constructor
  · intro hs
    obtain ⟨t, ht, hat, e⟩ := PCM.isSumOf_cons_iff.mp hs
    obtain ⟨t', ht', hbt', e'⟩ := PCM.isSumOf_cons_iff.mp ht
    rw [PCM.isSumOf_nil_iff] at ht'
    subst ht'
    rw [PCM.ovee_zero] at e'
    subst e'
    exact ⟨hat, e⟩
  · rintro ⟨h, rfl⟩
    exact pcm_isSumOf_pair h

/-- The **middle-four interchange** in a PCM: if `(a ⋁ b) ⋁ (c ⋁ d)` is
defined, then so is `(a ⋁ c) ⋁ (b ⋁ d)`, with the same value.  This is
174IV (`PCM.isSumOf_perm`) for the transposition `[a,b,c,d] ~ [a,c,b,d]`,
and it is what licenses the regrouping in the four-summand computation of
`cotupl-pcm` (eff.tex:1035). -/
private theorem pcm_middle_four {M : Type*} [PCM M] {a b c d : M}
    (hab : Perp a b) (hcd : Perp c d)
    (h : Perp (ovee a b hab) (ovee c d hcd)) :
    ∃ (hac : Perp a c) (hbd : Perp b d)
      (h' : Perp (ovee a c hac) (ovee b d hbd)),
      ovee (ovee a c hac) (ovee b d hbd) h'
        = ovee (ovee a b hab) (ovee c d hcd) h := by
  -- `[a, b, c, d]` sums to `(a ⋁ b) ⋁ (c ⋁ d)`
  have hbcd : Perp b (ovee c d hcd) := PCM.perp_of_ovee_perp hab h
  have habcd : Perp a (ovee b (ovee c d hcd) hbcd) :=
    PCM.perp_ovee_of_ovee_perp hab h
  have hl4 : PCM.IsSumOf [a, b, c, d]
      (ovee a (ovee b (ovee c d hcd) hbcd) habcd) :=
    PCM.IsSumOf.cons (PCM.IsSumOf.cons (pcm_isSumOf_pair hcd) hbcd) habcd
  rw [(PCM.ovee_assoc hab h).symm] at hl4
  -- transpose the middle two summands (174IV)
  have hl5 := PCM.isSumOf_perm (List.Perm.cons a (List.Perm.swap c b [d])) hl4
  obtain ⟨t₁, ht₁, hat₁, e₁⟩ := PCM.isSumOf_cons_iff.mp hl5
  obtain ⟨t₂, ht₂, hct₂, e₂⟩ := PCM.isSumOf_cons_iff.mp ht₁
  obtain ⟨hbd, e₃⟩ := pcm_isSumOf_pair_iff.mp ht₂
  subst e₃; subst e₂
  obtain ⟨hac, h', e⟩ := PCM.assoc_left hct₂ hat₁
  exact ⟨hac, hbd, h', e.trans e₁⟩

/-- `▷₁ ∘ (k + l) = [k, 0]`: the first partial projection absorbs a
coproduct of maps.  A helper for `cotupl_pcm_key` (181IV) and for
`coprod_prod_converse` (181VII); until the audit repair this declaration
carried the **181VII** doc comment, which belongs on `coprod_prod` below. -/
private theorem map_pproj₁ {X Y X' Y' : C} (k : X ⟶ X') (l : Y ⟶ Y') :
    coprod.map k l ≫ pproj₁ X' Y' = coprod.desc k 0 := by
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, coprod.inl_map, Category.assoc, inl_pproj₁,
      Category.comp_id, coprod.inl_desc]
  · rw [← Category.assoc, coprod.inr_map, Category.assoc, inr_pproj₁,
      FinPAC.comp_zero, coprod.inr_desc]

private theorem map_pproj₂ {X Y X' Y' : C} (k : X ⟶ X') (l : Y ⟶ Y') :
    coprod.map k l ≫ pproj₂ X' Y' = coprod.desc 0 l := by
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, coprod.inl_map, Category.assoc, inl_pproj₂,
      FinPAC.comp_zero, coprod.inl_desc]
  · rw [← Category.assoc, coprod.inr_map, Category.assoc, inr_pproj₂,
      Category.comp_id, coprod.inr_desc]

/-- The first display of the proof of `cotupl-pcm` (eff.tex:1020):
`[k, 0] = ▷₁ ∘ (k + l) ⊥ ▷₂ ∘ (k + l) = [0, l]` by the compatible-sum axiom,
and `[k, l] = [k, 0] ⋁ [0, l]` by PCM-enrichment and the two
coprojections. -/
private theorem desc_split (k : X ⟶ Z) (l : Y ⟶ Z) :
    ∃ hp : Perp (coprod.desc k (0 : Y ⟶ Z)) (coprod.desc (0 : X ⟶ Z) l),
      ovee _ _ hp = coprod.desc k l := by
  have hb := FinPAC.compatible_sum (coprod.map k l : X ⨿ Y ⟶ Z ⨿ Z)
  rw [map_pproj₁, map_pproj₂] at hb
  refine ⟨hb, coprod.hom_ext ?_ ?_⟩
  · rw [coprod.inl_desc, ovee_comp_left hb _ (perp_comp_left hb _)]
    exact (PCM.ovee_congr (coprod.inl_desc _ _) (coprod.inl_desc _ _) _
      (PCM.perp_zero k)).trans (PCM.ovee_zero k _)
  · rw [coprod.inr_desc, ovee_comp_left hb _ (perp_comp_left hb _)]
    exact (PCM.ovee_congr (coprod.inr_desc _ _) (coprod.inr_desc _ _) _
      (PCM.zero_perp l)).trans (PCM.zero_ovee l)

/-- The four-summand computation of eff.tex:1030–1045, which establishes
the "if" half of clause 1 of `cotupl-pcm` and clause 2 at one stroke:
`[f,0] = f ∘ ▷₁ ⊥ f' ∘ ▷₁ = [f',0]` and `[f ⋁ f', 0] = [f,0] ⋁ [f',0]` by
PCM-enrichment, similarly `[0, g ⋁ g'] = [0,g] ⋁ [0,g']`, and then
`[f,g] ⋁ [f',g'] = [f,0] ⋁ [0,g] ⋁ [f',0] ⋁ [0,g']
   = [f ⋁ f', 0] ⋁ [0, g ⋁ g'] = [f ⋁ f', g ⋁ g']`
using `desc_split` three times and the middle-four interchange. -/
private theorem cotupl_pcm_key {f f' : X ⟶ Z} {g g' : Y ⟶ Z}
    (hf : Perp f f') (hg : Perp g g') :
    ∃ h : Perp (coprod.desc f g) (coprod.desc f' g'),
      ovee _ _ h = coprod.desc (ovee f f' hf) (ovee g g' hg) := by
  -- `[f, 0] ⊥ [f', 0]` and `[f, 0] ⋁ [f', 0] = [f ⋁ f', 0]`
  have hA : Perp (coprod.desc f (0 : Y ⟶ Z)) (coprod.desc f' (0 : Y ⟶ Z)) := by
    have hx := perp_comp_left hf (pproj₁ X Y)
    rwa [pproj₁_comp, pproj₁_comp] at hx
  have eA : ovee _ _ hA = coprod.desc (ovee f f' hf) (0 : Y ⟶ Z) := by
    have hx := ovee_comp_left hf (pproj₁ X Y) (perp_comp_left hf (pproj₁ X Y))
    rw [pproj₁_comp] at hx
    exact (PCM.ovee_congr (pproj₁_comp (Y := Y) f).symm
      (pproj₁_comp (Y := Y) f').symm hA _).trans hx.symm
  -- `[0, g] ⊥ [0, g']` and `[0, g] ⋁ [0, g'] = [0, g ⋁ g']`
  have hB : Perp (coprod.desc (0 : X ⟶ Z) g) (coprod.desc (0 : X ⟶ Z) g') := by
    have hx := perp_comp_left hg (pproj₂ X Y)
    rwa [pproj₂_comp, pproj₂_comp] at hx
  have eB : ovee _ _ hB = coprod.desc (0 : X ⟶ Z) (ovee g g' hg) := by
    have hx := ovee_comp_left hg (pproj₂ X Y) (perp_comp_left hg (pproj₂ X Y))
    rw [pproj₂_comp] at hx
    exact (PCM.ovee_congr (pproj₂_comp (X := X) g).symm
      (pproj₂_comp (X := X) g').symm hB _).trans hx.symm
  -- `[f ⋁ f', 0] ⊥ [0, g ⋁ g']`, with sum `[f ⋁ f', g ⋁ g']`
  obtain ⟨hS, eS⟩ := desc_split (ovee f f' hf) (ovee g g' hg)
  have hSS : Perp (ovee _ _ hA) (ovee _ _ hB) := by rw [eA, eB]; exact hS
  -- regroup the four summands
  obtain ⟨hac, hbd, h', hmf⟩ := pcm_middle_four hA hB hSS
  obtain ⟨hfg, efg⟩ := desc_split f g
  obtain ⟨hfg', efg'⟩ := desc_split f' g'
  have e1 : ovee _ _ hac = coprod.desc f g :=
    (PCM.ovee_congr rfl rfl hac hfg).trans efg
  have e2 : ovee _ _ hbd = coprod.desc f' g' :=
    (PCM.ovee_congr rfl rfl hbd hfg').trans efg'
  have hres : Perp (coprod.desc f g) (coprod.desc f' g') := by
    rw [← e1, ← e2]; exact h'
  refine ⟨hres, ?_⟩
  calc ovee _ _ hres = ovee (ovee _ _ hac) (ovee _ _ hbd) h' :=
        PCM.ovee_congr e1.symm e2.symm _ _
    _ = ovee (ovee _ _ hA) (ovee _ _ hB) hSS := hmf
    _ = ovee (coprod.desc (ovee f f' hf) (0 : Y ⟶ Z))
          (coprod.desc (0 : X ⟶ Z) (ovee g g' hg)) hS :=
        PCM.ovee_congr eA eB _ _
    _ = coprod.desc (ovee f f' hf) (ovee g g' hg) := eS

/-- **181IV.1** (`cotupl-pcm`, eff.tex:999, Proposition): cotupling
reflects and preserves `⊥`: `[f,g] ⊥ [f',g']` iff `f ⊥ f'` and
`g ⊥ g'`. -/
theorem cotupl_pcm_1 (f f' : X ⟶ Z) (g g' : Y ⟶ Z) :
    Perp (coprod.desc f g) (coprod.desc f' g') ↔ Perp f f' ∧ Perp g g' := by
  constructor
  · intro h
    -- eff.tex:1030, by PCM-enrichment: `f = [f,g] ∘ κ₁ ⊥ [f',g'] ∘ κ₁ = f'`
    refine ⟨?_, ?_⟩
    · have h₁ := perp_comp_left h (coprod.inl : X ⟶ X ⨿ Y)
      rwa [coprod.inl_desc, coprod.inl_desc] at h₁
    · have h₂ := perp_comp_left h (coprod.inr : Y ⟶ X ⨿ Y)
      rwa [coprod.inr_desc, coprod.inr_desc] at h₂
  · rintro ⟨hf, hg⟩
    -- eff.tex:1030–1045, the four-summand computation
    exact (cotupl_pcm_key hf hg).choose

/-- **181IV.2** (`cotupl-pcm`, eff.tex:999, Proposition):
`[f,g] ⋁ [f',g'] = [f ⋁ f', g ⋁ g']`. -/
theorem cotupl_pcm_2 {f f' : X ⟶ Z} {g g' : Y ⟶ Z}
    (h : Perp (coprod.desc f g) (coprod.desc f' g'))
    (hf : Perp f f') (hg : Perp g g') :
    ovee _ _ h = coprod.desc (ovee f f' hf) (ovee g g' hg) := by
  obtain ⟨hp, e⟩ := cotupl_pcm_key hf hg
  exact (PCM.ovee_congr rfl rfl h hp).trans e

/-- **181IV.3** (`cotupl-pcm`, eff.tex:999, Proposition): `[0,0] = 0`. -/
theorem cotupl_pcm_3 (X Y Z : C) :
    coprod.desc (0 : X ⟶ Z) (0 : Y ⟶ Z) = 0 := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc, FinPAC.comp_zero]
  · rw [coprod.inr_desc, FinPAC.comp_zero]

/-- **181IV** (`cotupl-pcm`, eff.tex:999, Proposition): furthermore
`[1,1] = 1` for maps into `I`. -/
theorem cotupl_pcm_one (X Y : C) :
    coprod.desc (truth X) (truth Y) = truth (X ⨿ Y) := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc]; exact (coproj_total_inl X Y).symm
  · rw [coprod.inr_desc]; exact (coproj_total_inr X Y).symm

/-- **181IV** (`cotupl-pcm`, eff.tex:999, Proposition): the cotupling map is
an effect algebra isomorphism `Pred X × Pred Y ≅ Pred (X + Y)`. -/
theorem cotupl_pcm_ea_iso (X Y : C) :
    ∃ φ : EAHom ((X ⟶ effObj C) × (Y ⟶ effObj C)) ((X ⨿ Y) ⟶ effObj C),
      Function.Bijective φ.toFun ∧
      ∀ (p : X ⟶ effObj C) (q : Y ⟶ effObj C),
        φ.toFun (p, q) = coprod.desc p q := by
  refine ⟨{ toFun := fun pq => coprod.desc pq.1 pq.2
            perp_map := fun {a b} h => (cotupl_pcm_1 a.1 b.1 a.2 b.2).2 ⟨h.1, h.2⟩
            ovee_map := fun {a b} h =>
              (cotupl_pcm_2 ((cotupl_pcm_1 a.1 b.1 a.2 b.2).2 ⟨h.1, h.2⟩) h.1 h.2).symm
            map_one := cotupl_pcm_one X Y }, ⟨?_, ?_⟩, fun _ _ => rfl⟩
  · rintro ⟨p, q⟩ ⟨p', q'⟩ hpq
    have hpq' : coprod.desc p q = coprod.desc p' q' := hpq
    have h₁ : (coprod.inl : X ⟶ X ⨿ Y) ≫ coprod.desc p q
        = coprod.inl ≫ coprod.desc p' q' := by rw [hpq']
    have h₂ : (coprod.inr : Y ⟶ X ⨿ Y) ≫ coprod.desc p q
        = coprod.inr ≫ coprod.desc p' q' := by rw [hpq']
    rw [coprod.inl_desc, coprod.inl_desc] at h₁
    rw [coprod.inr_desc, coprod.inr_desc] at h₂
    simp only [Prod.mk.injEq]
    exact ⟨h₁, h₂⟩
  · intro r
    refine ⟨(coprod.inl ≫ r, coprod.inr ≫ r), ?_⟩
    show coprod.desc (coprod.inl ≫ r) (coprod.inr ≫ r) = r
    rw [← coprod.desc_comp, coprod.desc_inl_inr, Category.id_comp]

/-- The pairing `⟨f, g⟩ = (κ₁ ∘ f) ⋁ (κ₂ ∘ g)` of 181VII and its defining
property (eff.tex:1090). -/
private theorem exists_pair (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) :
    ∃ hk : Perp (f ≫ (coprod.inl : X ⟶ X ⨿ Y)) (g ≫ (coprod.inr : Y ⟶ X ⨿ Y)),
      ovee _ _ hk ≫ pproj₁ X Y = f ∧ ovee _ _ hk ≫ pproj₂ X Y = g := by
  have t₁ : (coprod.inl : X ⟶ X ⨿ Y) ≫ truth (X ⨿ Y) = truth X := coproj_total_inl X Y
  have t₂ : (coprod.inr : Y ⟶ X ⨿ Y) ≫ truth (X ⨿ Y) = truth Y := coproj_total_inr X Y
  have h1 : Perp ((f ≫ (coprod.inl : X ⟶ X ⨿ Y)) ≫ truth (X ⨿ Y))
      ((g ≫ (coprod.inr : Y ⟶ X ⨿ Y)) ≫ truth (X ⨿ Y)) := by
    rw [Category.assoc, Category.assoc, t₁, t₂]
    exact h
  have hk : Perp (f ≫ (coprod.inl : X ⟶ X ⨿ Y)) (g ≫ (coprod.inr : Y ⟶ X ⨿ Y)) :=
    EffectusPartialForm.perp_of_one_perp h1
  refine ⟨hk, ?_, ?_⟩
  · rw [ovee_comp_right hk _ (perp_comp_right hk _)]
    refine (PCM.ovee_congr ?_ ?_ _ (PCM.perp_zero f)).trans (PCM.ovee_zero f _)
    · rw [Category.assoc, inl_pproj₁, Category.comp_id]
    · rw [Category.assoc, inr_pproj₁, FinPAC.comp_zero]
  · rw [ovee_comp_right hk _ (perp_comp_right hk _)]
    refine (PCM.ovee_congr ?_ ?_ _ (PCM.zero_perp g)).trans (PCM.zero_ovee g)
    · rw [Category.assoc, inl_pproj₂, FinPAC.comp_zero]
    · rw [Category.assoc, inr_pproj₂, Category.comp_id]

/-- Uniqueness of the pairing (181VII): a map with the right projections is
`(κ₁ ∘ f) ⋁ (κ₂ ∘ g)`, since `(κ₁ ∘ ▷₁) ⋁ (κ₂ ∘ ▷₂) = id`. -/
private theorem pair_unique (f : Z ⟶ X) (g : Z ⟶ Y) (q : Z ⟶ X ⨿ Y)
    (h₁ : q ≫ pproj₁ X Y = f) (h₂ : q ≫ pproj₂ X Y = g)
    (hk : Perp (f ≫ (coprod.inl : X ⟶ X ⨿ Y)) (g ≫ (coprod.inr : Y ⟶ X ⨿ Y))) :
    q = ovee _ _ hk := by
  have hp1 : pproj₁ X Y ≫ (coprod.inl : X ⟶ X ⨿ Y)
      = coprod.desc coprod.inl 0 := pproj₁_comp _
  have hp2 : pproj₂ X Y ≫ (coprod.inr : Y ⟶ X ⨿ Y)
      = coprod.desc 0 coprod.inr := pproj₂_comp _
  have hdd : Perp (coprod.desc (coprod.inl : X ⟶ X ⨿ Y) 0)
      (coprod.desc 0 (coprod.inr : Y ⟶ X ⨿ Y)) :=
    (cotupl_pcm_1 _ _ _ _).2 ⟨PCM.perp_zero _, PCM.zero_perp _⟩
  have hpp : Perp (pproj₁ X Y ≫ (coprod.inl : X ⟶ X ⨿ Y))
      (pproj₂ X Y ≫ (coprod.inr : Y ⟶ X ⨿ Y)) := by rw [hp1, hp2]; exact hdd
  have hid : ovee _ _ hpp = 𝟙 (X ⨿ Y) := by
    refine (PCM.ovee_congr hp1 hp2 hpp hdd).trans ?_
    rw [cotupl_pcm_2 hdd (PCM.perp_zero (coprod.inl : X ⟶ X ⨿ Y))
      (PCM.zero_perp (coprod.inr : Y ⟶ X ⨿ Y)), PCM.ovee_zero, PCM.zero_ovee,
      coprod.desc_inl_inr]
  calc q = q ≫ 𝟙 (X ⨿ Y) := (Category.comp_id q).symm
    _ = q ≫ ovee _ _ hpp := by rw [hid]
    _ = ovee _ _ hk := by
        rw [ovee_comp_left hpp q (perp_comp_left hpp q)]
        exact PCM.ovee_congr (by rw [← Category.assoc, h₁])
          (by rw [← Category.assoc, h₂]) _ hk

/-- **181VII** (`coprod-prod`, eff.tex:1066, Proposition): the coproduct in
an effectus in partial form is almost a (bi)product — for `f : Z ⟶ X` and
`g : Z ⟶ Y` with `1 ∘ f ⊥ 1 ∘ g` there is a **unique** `⟨f,g⟩ : Z ⟶ X + Y`
with `▷₁ ∘ ⟨f,g⟩ = f` and `▷₂ ∘ ⟨f,g⟩ = g`, where `▷₁ = [id,0]` and
`▷₂ = [0,id]`.  (The remaining halves of the bijective correspondence are
`effPair_eq_ovee`, `⟨f,g⟩ = (κ₁ ∘ f) ⋁ (κ₂ ∘ g)`, and
`coprod_prod_converse`.) -/
theorem coprod_prod {f : Z ⟶ X} {g : Z ⟶ Y}
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) :
    ∃! p : Z ⟶ X ⨿ Y, p ≫ pproj₁ X Y = f ∧ p ≫ pproj₂ X Y = g := by
  obtain ⟨hk, e₁, e₂⟩ := exists_pair f g h
  refine ⟨ovee _ _ hk, ⟨e₁, e₂⟩, ?_⟩
  rintro q ⟨q₁, q₂⟩
  exact pair_unique f g q q₁ q₂ hk

/-- **181VII** (`coprod-prod`, eff.tex:1066, Proposition): the pairing
`⟨f, g⟩` of partial maps with `1 ∘ f ⊥ 1 ∘ g`. -/
noncomputable def effPair (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) : Z ⟶ X ⨿ Y :=
  (coprod_prod h).exists.choose

/-- Defining property of `effPair` (181VII). -/
theorem effPair_spec (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) :
    effPair f g h ≫ pproj₁ X Y = f ∧ effPair f g h ≫ pproj₂ X Y = g :=
  (coprod_prod h).exists.choose_spec

/-- **181VII** (`coprod-prod`, eff.tex:1083, Proposition): in fact
`⟨f, g⟩ = (κ₁ ∘ f) ⋁ (κ₂ ∘ g)`. -/
theorem effPair_eq_ovee (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) :
    ∃ hk : Perp (f ≫ (coprod.inl : X ⟶ X ⨿ Y)) (g ≫ (coprod.inr : Y ⟶ X ⨿ Y)),
      effPair f g h = ovee _ _ hk := by
  obtain ⟨hk, -, -⟩ := exists_pair f g h
  exact ⟨hk, pair_unique f g _ (effPair_spec f g h).1 (effPair_spec f g h).2 hk⟩

/-- **181VII** (`coprod-prod`, eff.tex:1085, Proposition), converse
direction: every `h : Z ⟶ X + Y` satisfies `1 ∘ ▷₁ ∘ h ⊥ 1 ∘ ▷₂ ∘ h` (and
`h = ⟨▷₁ ∘ h, ▷₂ ∘ h⟩` by the uniqueness in `coprod_prod`). -/
theorem coprod_prod_converse (p : Z ⟶ X ⨿ Y) :
    Perp ((p ≫ pproj₁ X Y) ≫ truth X) ((p ≫ pproj₂ X Y) ≫ truth Y) := by
  have hb := FinPAC.compatible_sum
    (p ≫ coprod.map (truth X) (truth Y) : Z ⟶ effObj C ⨿ effObj C)
  have e₁ : (p ≫ coprod.map (truth X) (truth Y)) ≫ pproj₁ (effObj C) (effObj C)
      = (p ≫ pproj₁ X Y) ≫ truth X := by
    rw [Category.assoc, Category.assoc, map_pproj₁, pproj₁_comp]
  have e₂ : (p ≫ coprod.map (truth X) (truth Y)) ≫ pproj₂ (effObj C) (effObj C)
      = (p ≫ pproj₂ X Y) ≫ truth Y := by
    rw [Category.assoc, Category.assoc, map_pproj₂, pproj₂_comp]
  rwa [e₁, e₂] at hb

/-- **181IX.1** (`eff-prod-rules`, eff.tex:1137, Exercise):
`[a,b] ∘ ⟨f,g⟩ = (a ∘ f) ⋁ (b ∘ g)`. -/
theorem eff_prod_rules_1 {W : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) (a : X ⟶ W) (b : Y ⟶ W) :
    ∃ hp : Perp (f ≫ a) (g ≫ b),
      effPair f g h ≫ coprod.desc a b = ovee (f ≫ a) (g ≫ b) hp := by
  obtain ⟨hk, he⟩ := effPair_eq_ovee f g h
  have hp : Perp (f ≫ a) (g ≫ b) := by
    have hq := perp_comp_right hk (coprod.desc a b)
    rwa [Category.assoc, coprod.inl_desc, Category.assoc, coprod.inr_desc] at hq
  refine ⟨hp, ?_⟩
  rw [he, ovee_comp_right hk _ (perp_comp_right hk _)]
  exact PCM.ovee_congr (by rw [Category.assoc, coprod.inl_desc])
    (by rw [Category.assoc, coprod.inr_desc]) _ hp

/-- **181IX.2** (`eff-prod-rules`, eff.tex:1137, Exercise):
`1 ∘ ⟨f,g⟩ = (1 ∘ f) ⋁ (1 ∘ g)`. -/
theorem eff_prod_rules_2 (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) :
    effPair f g h ≫ truth (X ⨿ Y) = ovee (f ≫ truth X) (g ≫ truth Y) h := by
  obtain ⟨hk, he⟩ := effPair_eq_ovee f g h
  have t₁ : (coprod.inl : X ⟶ X ⨿ Y) ≫ truth (X ⨿ Y) = truth X := coproj_total_inl X Y
  have t₂ : (coprod.inr : Y ⟶ X ⨿ Y) ≫ truth (X ⨿ Y) = truth Y := coproj_total_inr X Y
  rw [he, ovee_comp_right hk _ (perp_comp_right hk _)]
  exact PCM.ovee_congr (by rw [Category.assoc, t₁]) (by rw [Category.assoc, t₂]) _ h

/-- **181IX.3** (`eff-prod-rules`, eff.tex:1137, Exercise):
`(k + l) ∘ ⟨f,g⟩ = ⟨k ∘ f, l ∘ g⟩`. -/
theorem eff_prod_rules_3 {X' Y' : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) (k : X ⟶ X') (l : Y ⟶ Y')
    (h' : Perp ((f ≫ k) ≫ truth X') ((g ≫ l) ≫ truth Y')) :
    effPair f g h ≫ coprod.map k l = effPair (f ≫ k) (g ≫ l) h' := by
  -- bsols.tex:1679: `(k+l) ∘ ⟨f,g⟩ ≡ [κ₁∘k, κ₂∘l] ∘ ⟨f,g⟩
  --   = (κ₁∘k∘f) ⋁ (κ₂∘l∘g) ≡ ⟨k∘f, l∘g⟩`, i.e. by the first point.
  have hmap : (coprod.map k l : X ⨿ Y ⟶ X' ⨿ Y')
      = coprod.desc (k ≫ coprod.inl) (l ≫ coprod.inr) := by
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_map, coprod.inl_desc]
    · rw [coprod.inr_map, coprod.inr_desc]
  obtain ⟨hp, he⟩ := eff_prod_rules_1 f g h (k ≫ (coprod.inl : X' ⟶ X' ⨿ Y'))
    (l ≫ (coprod.inr : Y' ⟶ X' ⨿ Y'))
  obtain ⟨hk', he'⟩ := effPair_eq_ovee (f ≫ k) (g ≫ l) h'
  rw [hmap, he, he']
  exact PCM.ovee_congr (Category.assoc f k coprod.inl).symm
    (Category.assoc g l coprod.inr).symm _ _

/-- **181IX.4** (`eff-prod-rules`, eff.tex:1137, Exercise):
`⟨f,g⟩ ∘ k = ⟨f ∘ k, g ∘ k⟩`. -/
theorem eff_prod_rules_4 {W : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) (k : W ⟶ Z)
    (h' : Perp ((k ≫ f) ≫ truth X) ((k ≫ g) ≫ truth Y)) :
    k ≫ effPair f g h = effPair (k ≫ f) (k ≫ g) h' := by
  -- bsols.tex:1688: `⟨f,g⟩ ∘ k ≡ ((κ₁∘f) ⋁ (κ₂∘g)) ∘ k
  --   = (κ₁∘f∘k) ⋁ (κ₂∘g∘k) ≡ ⟨f∘k, g∘k⟩`, by PCM-enrichment.
  obtain ⟨hk, he⟩ := effPair_eq_ovee f g h
  obtain ⟨hk', he'⟩ := effPair_eq_ovee (k ≫ f) (k ≫ g) h'
  rw [he, he', ovee_comp_left hk k (perp_comp_left hk k)]
  exact PCM.ovee_congr (Category.assoc k f coprod.inl).symm
    (Category.assoc k g coprod.inr).symm _ _

end PartialToTotal

/-! ## The total maps form an effectus in total form (parsec 181, 181XI) -/

section PartialToTotalStructure

variable {D : Type u} [Category.{v} D] [HasFiniteCoproducts D]
  [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D] [EffectusPartialForm D]

/-! ### 181XIII and the basic totality facts -/

/-- A morphism of `Tot D` is total, read as an equation in `D`. -/
theorem tot_total_base {X Y : Tot D} (f : X ⟶ Y) :
    f.1 ≫ truth Y.base = truth X.base := f.2

theorem tot_comp_base {X Y Z : Tot D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

theorem tot_id_base (X : Tot D) : (𝟙 X : X ⟶ X).1 = 𝟙 X.base := rfl

variable [HasFiniteCoproducts (Tot D)] in
theorem tot_desc_inl {X Y Z : Tot D} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (coprod.inl : X ⟶ X ⨿ Y).1 ≫ (coprod.desc f g).1 = f.1 :=
  congrArg Subtype.val (coprod.inl_desc f g)

variable [HasFiniteCoproducts (Tot D)] in
theorem tot_desc_inr {X Y Z : Tot D} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (coprod.inr : Y ⟶ X ⨿ Y).1 ≫ (coprod.desc f g).1 = g.1 :=
  congrArg Subtype.val (coprod.inr_desc f g)

/-- **181XIII** (`one-m-is-id`): in an effectus in partial form the truth
predicate on the effect object `I` is the identity, `1 = id_I`. -/
theorem one_m_is_id : truth (effObj D) = 𝟙 (effObj D) := by
  have hperp := EffectusPartialForm.perp_orth (𝟙 (effObj D))
  have hovee := EffectusPartialForm.ovee_orth (𝟙 (effObj D))
  have h2 := perp_comp_right hperp (truth (effObj D))
  rw [Category.id_comp] at h2
  have h3 : EffectusPartialForm.orth (𝟙 (effObj D)) ≫ truth (effObj D) = 0 :=
    EffectusPartialForm.eq_zero_of_perp_one (PCM.perp_comm h2)
  have h4 : EffectusPartialForm.orth (𝟙 (effObj D)) = 0 :=
    EffectusPartialForm.eq_zero_of_one_zero h3
  calc truth (effObj D) = ovee _ _ hperp := hovee.symm
    _ = ovee (𝟙 (effObj D)) 0 (PCM.perp_zero _) := PCM.ovee_congr rfl h4 _ _
    _ = 𝟙 (effObj D) := PCM.ovee_zero _ _

/-- A predicate composed with `1 : I ⟶ I` is itself (**181XIII**). -/
theorem comp_truth_effObj {X : D} (p : X ⟶ effObj D) : p ≫ truth (effObj D) = p := by
  rw [one_m_is_id, Category.comp_id]

/-- The truth predicate is a total map. -/
theorem isTotal_truth (X : D) : IsTotal (truth X) := comp_truth_effObj _

/-- **181XII**: the cotuple of two total maps is total. -/
theorem isTotal_desc {X Y Z : D} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : IsTotal f) (hg : IsTotal g) : IsTotal (coprod.desc f g) := by
  show coprod.desc f g ≫ truth Z = truth (X ⨿ Y)
  rw [coprod.desc_comp, show f ≫ truth Z = truth X from hf,
    show g ≫ truth Z = truth Y from hg, cotupl_pcm_one]

/-- **181XII**: the unique map out of the initial object is total. -/
theorem isTotal_initial (X : D) : IsTotal (initial.to X) :=
  initialIsInitial.hom_ext _ _

/-- The partial projections are jointly monic (the uniqueness half of
**181VII**). -/
theorem pproj_jm {X Y Z : D} {p q : Z ⟶ X ⨿ Y}
    (h₁ : p ≫ pproj₁ X Y = q ≫ pproj₁ X Y)
    (h₂ : p ≫ pproj₂ X Y = q ≫ pproj₂ X Y) : p = q :=
  (coprod_prod (coprod_prod_converse p)).unique ⟨rfl, rfl⟩ ⟨h₁.symm, h₂.symm⟩

/-! ### `Tot D` has finite coproducts and a final object -/

/-- **181XIII**: the effect object is the final object of `Tot D`. -/
noncomputable def totIsTerminal : IsTerminal (Tot.of (effObj D)) :=
  IsTerminal.ofUniqueHom (fun X => ⟨truth X.base, isTotal_truth _⟩) (fun X m => by
    refine Subtype.ext ?_
    have h : (m.1 : X.base ⟶ effObj D) ≫ truth (effObj D) = truth X.base := m.2
    rw [comp_truth_effObj] at h
    exact h)

/-- **181XII**: `0` is the initial object of `Tot D`. -/
noncomputable def totIsInitial : IsInitial (Tot.of (⊥_ D)) :=
  IsInitial.ofUniqueHom (fun Y => ⟨initial.to Y.base, isTotal_initial _⟩)
    (fun _ _ => Subtype.ext (initialIsInitial.hom_ext _ _))

/-- **181XII**: the coproduct of `D` is the coproduct of `Tot D`. -/
noncomputable def totBinaryCofan (X Y : Tot D) : BinaryCofan X Y :=
  BinaryCofan.mk
    (⟨coprod.inl, coproj_total_inl X.base Y.base⟩ : X ⟶ Tot.of (X.base ⨿ Y.base))
    (⟨coprod.inr, coproj_total_inr X.base Y.base⟩ : Y ⟶ Tot.of (X.base ⨿ Y.base))

noncomputable def totBinaryCofanIsColimit (X Y : Tot D) : IsColimit (totBinaryCofan X Y) :=
  BinaryCofan.IsColimit.mk _
    (fun {T} f g => (⟨coprod.desc f.1 g.1, isTotal_desc f.2 g.2⟩ :
      Tot.of (X.base ⨿ Y.base) ⟶ T))
    (fun f g => Subtype.ext (coprod.inl_desc _ _))
    (fun f g => Subtype.ext (coprod.inr_desc _ _))
    (fun f g m h₁ h₂ => Subtype.ext (coprod.hom_ext
      (by rw [coprod.inl_desc]; exact congrArg Subtype.val h₁)
      (by rw [coprod.inr_desc]; exact congrArg Subtype.val h₂)))

theorem totHasTerminal : HasTerminal (Tot D) := totIsTerminal.hasTerminal

theorem totHasFiniteCoproducts : HasFiniteCoproducts (Tot D) :=
  letI : HasInitial (Tot D) := totIsInitial.hasInitial
  letI : ∀ X Y : Tot D, HasColimit (pair X Y) := fun X Y =>
    HasColimit.mk ⟨totBinaryCofan X Y, totBinaryCofanIsColimit X Y⟩
  letI : HasBinaryCoproducts (Tot D) := hasBinaryCoproducts_of_hasColimit_pair (Tot D)
  hasFiniteCoproducts_of_has_binary_and_initial

/-! ### Bridging: coordinates for an arbitrary coproduct structure on `Tot D` -/

section Bridge

variable [HasFiniteCoproducts (Tot D)]

/-- The comparison isomorphism between a chosen coproduct of `Tot D` and the
coproduct inherited from `D`. -/
noncomputable def totCoprodIso (X Y : Tot D) :
    (X ⨿ Y : Tot D) ≅ Tot.of (X.base ⨿ Y.base) :=
  IsColimit.coconePointUniqueUpToIso (coprodIsCoprod X Y) (totBinaryCofanIsColimit X Y)

theorem totCoprodIso_inl (X Y : Tot D) :
    (coprod.inl : X ⟶ X ⨿ Y) ≫ (totCoprodIso X Y).hom
      = (⟨coprod.inl, coproj_total_inl _ _⟩ : X ⟶ Tot.of (X.base ⨿ Y.base)) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod X Y)
    (totBinaryCofanIsColimit X Y) (Discrete.mk WalkingPair.left)

theorem totCoprodIso_inr (X Y : Tot D) :
    (coprod.inr : Y ⟶ X ⨿ Y) ≫ (totCoprodIso X Y).hom
      = (⟨coprod.inr, coproj_total_inr _ _⟩ : Y ⟶ Tot.of (X.base ⨿ Y.base)) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod X Y)
    (totBinaryCofanIsColimit X Y) (Discrete.mk WalkingPair.right)

theorem totCoprodIso_inl_base (X Y : Tot D) :
    (coprod.inl : X ⟶ X ⨿ Y).1 ≫ (totCoprodIso X Y).hom.1
      = (coprod.inl : X.base ⟶ X.base ⨿ Y.base) :=
  congrArg Subtype.val (totCoprodIso_inl X Y)

theorem totCoprodIso_inr_base (X Y : Tot D) :
    (coprod.inr : Y ⟶ X ⨿ Y).1 ≫ (totCoprodIso X Y).hom.1
      = (coprod.inr : Y.base ⟶ X.base ⨿ Y.base) :=
  congrArg Subtype.val (totCoprodIso_inr X Y)

theorem totCoprodIso_inv_inl_base (X Y : Tot D) :
    (coprod.inl : X.base ⟶ X.base ⨿ Y.base) ≫ (totCoprodIso X Y).inv.1
      = (coprod.inl : X ⟶ X ⨿ Y).1 := by
  rw [← totCoprodIso_inl_base, Category.assoc]
  exact congrArg (fun t => (coprod.inl : X ⟶ X ⨿ Y).1 ≫ t)
    (congrArg Subtype.val (totCoprodIso X Y).hom_inv_id) |>.trans (Category.comp_id _)

theorem totCoprodIso_inv_inr_base (X Y : Tot D) :
    (coprod.inr : Y.base ⟶ X.base ⨿ Y.base) ≫ (totCoprodIso X Y).inv.1
      = (coprod.inr : Y ⟶ X ⨿ Y).1 := by
  rw [← totCoprodIso_inr_base, Category.assoc]
  exact congrArg (fun t => (coprod.inr : Y ⟶ X ⨿ Y).1 ≫ t)
    (congrArg Subtype.val (totCoprodIso X Y).hom_inv_id) |>.trans (Category.comp_id _)

theorem totCoprodIso_hom_inv_base (X Y : Tot D) :
    (totCoprodIso X Y).hom.1 ≫ (totCoprodIso X Y).inv.1 = 𝟙 (X ⨿ Y : Tot D).base :=
  congrArg Subtype.val (totCoprodIso X Y).hom_inv_id

theorem totCoprodIso_inv_hom_base (X Y : Tot D) :
    (totCoprodIso X Y).inv.1 ≫ (totCoprodIso X Y).hom.1 = 𝟙 (X.base ⨿ Y.base) :=
  congrArg Subtype.val (totCoprodIso X Y).inv_hom_id

/-- Maps out of a coproduct of `Tot D` are determined, *as maps of `D`*, by
their restrictions along the two coprojections. -/
theorem tot_hom_ext_base {X Y : Tot D} {Z : D}
    {u u' : (X ⨿ Y : Tot D).base ⟶ Z}
    (h₁ : (coprod.inl : X ⟶ X ⨿ Y).1 ≫ u = (coprod.inl : X ⟶ X ⨿ Y).1 ≫ u')
    (h₂ : (coprod.inr : Y ⟶ X ⨿ Y).1 ≫ u = (coprod.inr : Y ⟶ X ⨿ Y).1 ≫ u') :
    u = u' := by
  have key : (totCoprodIso X Y).inv.1 ≫ u = (totCoprodIso X Y).inv.1 ≫ u' := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, ← Category.assoc, totCoprodIso_inv_inl_base]; exact h₁
    · rw [← Category.assoc, ← Category.assoc, totCoprodIso_inv_inr_base]; exact h₂
  calc u = ((totCoprodIso X Y).hom.1 ≫ (totCoprodIso X Y).inv.1) ≫ u := by
        rw [totCoprodIso_hom_inv_base, Category.id_comp]
    _ = ((totCoprodIso X Y).hom.1 ≫ (totCoprodIso X Y).inv.1) ≫ u' := by
        rw [Category.assoc, Category.assoc, key]
    _ = u' := by rw [totCoprodIso_hom_inv_base, Category.id_comp]

/-- The first partial projection `▷₁ : X + Y ⟶ X` of a chosen coproduct
of `Tot D` (a map of `D`, not of `Tot D`). -/
noncomputable def tp₁ (X Y : Tot D) : (X ⨿ Y : Tot D).base ⟶ X.base :=
  (totCoprodIso X Y).hom.1 ≫ pproj₁ X.base Y.base

/-- The second partial projection `▷₂ : X + Y ⟶ Y`. -/
noncomputable def tp₂ (X Y : Tot D) : (X ⨿ Y : Tot D).base ⟶ Y.base :=
  (totCoprodIso X Y).hom.1 ≫ pproj₂ X.base Y.base

theorem tinl_tp₁ (X Y : Tot D) :
    (coprod.inl : X ⟶ X ⨿ Y).1 ≫ tp₁ X Y = 𝟙 X.base := by
  rw [tp₁, ← Category.assoc, totCoprodIso_inl_base, inl_pproj₁]

theorem tinr_tp₁ (X Y : Tot D) :
    (coprod.inr : Y ⟶ X ⨿ Y).1 ≫ tp₁ X Y = 0 := by
  rw [tp₁, ← Category.assoc, totCoprodIso_inr_base, inr_pproj₁]

theorem tinl_tp₂ (X Y : Tot D) :
    (coprod.inl : X ⟶ X ⨿ Y).1 ≫ tp₂ X Y = 0 := by
  rw [tp₂, ← Category.assoc, totCoprodIso_inl_base, inl_pproj₂]

theorem tinr_tp₂ (X Y : Tot D) :
    (coprod.inr : Y ⟶ X ⨿ Y).1 ≫ tp₂ X Y = 𝟙 Y.base := by
  rw [tp₂, ← Category.assoc, totCoprodIso_inr_base, inr_pproj₂]

/-- **181VII** for `Tot D`: `▷₁, ▷₂` are jointly monic. -/
theorem tp_jm {X Y : Tot D} {Z : D} {p q : Z ⟶ (X ⨿ Y : Tot D).base}
    (h₁ : p ≫ tp₁ X Y = q ≫ tp₁ X Y) (h₂ : p ≫ tp₂ X Y = q ≫ tp₂ X Y) : p = q := by
  have key : p ≫ (totCoprodIso X Y).hom.1 = q ≫ (totCoprodIso X Y).hom.1 := by
    refine pproj_jm ?_ ?_
    · rw [Category.assoc, Category.assoc]; exact h₁
    · rw [Category.assoc, Category.assoc]; exact h₂
  calc p = (p ≫ (totCoprodIso X Y).hom.1) ≫ (totCoprodIso X Y).inv.1 := by
        rw [Category.assoc, totCoprodIso_hom_inv_base, Category.comp_id]
    _ = (q ≫ (totCoprodIso X Y).hom.1) ≫ (totCoprodIso X Y).inv.1 := by rw [key]
    _ = q := by rw [Category.assoc, totCoprodIso_hom_inv_base, Category.comp_id]

/-- **181VII** for `Tot D`: the pairing `⟨f, g⟩`. -/
noncomputable def tpair {X Y : Tot D} {Z : D} (f : Z ⟶ X.base) (g : Z ⟶ Y.base)
    (h : Perp (f ≫ truth X.base) (g ≫ truth Y.base)) : Z ⟶ (X ⨿ Y : Tot D).base :=
  effPair f g h ≫ (totCoprodIso X Y).inv.1

theorem tpair_tp₁ {X Y : Tot D} {Z : D} (f : Z ⟶ X.base) (g : Z ⟶ Y.base)
    (h : Perp (f ≫ truth X.base) (g ≫ truth Y.base)) :
    tpair (X := X) (Y := Y) f g h ≫ tp₁ X Y = f := by
  rw [tpair, tp₁, Category.assoc, ← Category.assoc ((totCoprodIso X Y).inv.1),
    totCoprodIso_inv_hom_base, Category.id_comp]
  exact (effPair_spec f g h).1

theorem tpair_tp₂ {X Y : Tot D} {Z : D} (f : Z ⟶ X.base) (g : Z ⟶ Y.base)
    (h : Perp (f ≫ truth X.base) (g ≫ truth Y.base)) :
    tpair (X := X) (Y := Y) f g h ≫ tp₂ X Y = g := by
  rw [tpair, tp₂, Category.assoc, ← Category.assoc ((totCoprodIso X Y).inv.1),
    totCoprodIso_inv_hom_base, Category.id_comp]
  exact (effPair_spec f g h).2

/-- **181VII** converse for `Tot D`: the two projections of any map are
orthogonal after composing with `1`. -/
theorem tp_perp {X Y : Tot D} {Z : D} (p : Z ⟶ (X ⨿ Y : Tot D).base) :
    Perp ((p ≫ tp₁ X Y) ≫ truth X.base) ((p ≫ tp₂ X Y) ≫ truth Y.base) := by
  have h := coprod_prod_converse (p ≫ (totCoprodIso X Y).hom.1)
  simp only [Category.assoc] at h ⊢
  simpa only [tp₁, tp₂, Category.assoc] using h

/-- Any map into a coproduct of `Tot D` is the pairing of its projections. -/
theorem tpair_eta {X Y : Tot D} {Z : D} (p : Z ⟶ (X ⨿ Y : Tot D).base) :
    tpair (X := X) (Y := Y) (p ≫ tp₁ X Y) (p ≫ tp₂ X Y) (tp_perp p) = p :=
  tp_jm (by rw [tpair_tp₁]) (by rw [tpair_tp₂])

/-- **181IX.2** for `Tot D`: `1 ∘ ⟨f,g⟩ = (1 ∘ f) ⋁ (1 ∘ g)`. -/
theorem tpair_truth {X Y : Tot D} {Z : D} (f : Z ⟶ X.base) (g : Z ⟶ Y.base)
    (h : Perp (f ≫ truth X.base) (g ≫ truth Y.base)) :
    tpair (X := X) (Y := Y) f g h ≫ truth (X ⨿ Y : Tot D).base
      = ovee (f ≫ truth X.base) (g ≫ truth Y.base) h := by
  rw [tpair, Category.assoc,
    show (totCoprodIso X Y).inv.1 ≫ truth (X ⨿ Y : Tot D).base = truth (X.base ⨿ Y.base) from
      (totCoprodIso X Y).inv.2]
  exact eff_prod_rules_2 f g h

/-- `▷₁ ∘ (k + l) = k ∘ ▷₁`. -/
theorem tot_map_tp₁ {X Y X' Y' : Tot D} (k : X ⟶ X') (l : Y ⟶ Y') :
    (coprod.map k l : (X ⨿ Y : Tot D) ⟶ X' ⨿ Y').1 ≫ tp₁ X' Y' = tp₁ X Y ≫ k.1 := by
  refine tot_hom_ext_base ?_ ?_
  · rw [← Category.assoc,
      show (coprod.inl : X ⟶ X ⨿ Y).1 ≫ (coprod.map k l : (X ⨿ Y : Tot D) ⟶ X' ⨿ Y').1
        = k.1 ≫ (coprod.inl : X' ⟶ X' ⨿ Y').1 from congrArg Subtype.val (coprod.inl_map k l),
      Category.assoc, tinl_tp₁, Category.comp_id, ← Category.assoc, tinl_tp₁, Category.id_comp]
  · rw [← Category.assoc,
      show (coprod.inr : Y ⟶ X ⨿ Y).1 ≫ (coprod.map k l : (X ⨿ Y : Tot D) ⟶ X' ⨿ Y').1
        = l.1 ≫ (coprod.inr : Y' ⟶ X' ⨿ Y').1 from congrArg Subtype.val (coprod.inr_map k l),
      Category.assoc, tinr_tp₁, FinPAC.comp_zero, ← Category.assoc, tinr_tp₁,
      FinPAC.zero_comp]

/-- `▷₂ ∘ (k + l) = l ∘ ▷₂`. -/
theorem tot_map_tp₂ {X Y X' Y' : Tot D} (k : X ⟶ X') (l : Y ⟶ Y') :
    (coprod.map k l : (X ⨿ Y : Tot D) ⟶ X' ⨿ Y').1 ≫ tp₂ X' Y' = tp₂ X Y ≫ l.1 := by
  refine tot_hom_ext_base ?_ ?_
  · rw [← Category.assoc,
      show (coprod.inl : X ⟶ X ⨿ Y).1 ≫ (coprod.map k l : (X ⨿ Y : Tot D) ⟶ X' ⨿ Y').1
        = k.1 ≫ (coprod.inl : X' ⟶ X' ⨿ Y').1 from congrArg Subtype.val (coprod.inl_map k l),
      Category.assoc, tinl_tp₂, FinPAC.comp_zero, ← Category.assoc, tinl_tp₂,
      FinPAC.zero_comp]
  · rw [← Category.assoc,
      show (coprod.inr : Y ⟶ X ⨿ Y).1 ≫ (coprod.map k l : (X ⨿ Y : Tot D) ⟶ X' ⨿ Y').1
        = l.1 ≫ (coprod.inr : Y' ⟶ X' ⨿ Y').1 from congrArg Subtype.val (coprod.inr_map k l),
      Category.assoc, tinr_tp₂, Category.comp_id, ← Category.assoc, tinr_tp₂,
      Category.id_comp]

end Bridge

section Axioms

variable [HasFiniteCoproducts (Tot D)] [HasTerminal (Tot D)]

/-- The truth predicate on the final object of `Tot D` is an isomorphism of
`D` (both `⊤_ (Tot D)` and `Tot.of I` are final, by **181XIII**). -/
theorem truth_terminal_isIso : IsIso (truth (⊤_ (Tot D)).base) := by
  have hhom : (IsTerminal.uniqueUpToIso (terminalIsTerminal (C := Tot D)) totIsTerminal).hom.1
      = truth (⊤_ (Tot D)).base := by
    have h := tot_total_base
      (IsTerminal.uniqueUpToIso (terminalIsTerminal (C := Tot D)) totIsTerminal).hom
    rwa [show truth (Tot.of (effObj D)).base = 𝟙 (effObj D) from one_m_is_id,
      Category.comp_id] at h
  refine ⟨(IsTerminal.uniqueUpToIso (terminalIsTerminal (C := Tot D)) totIsTerminal).inv.1,
    ?_, ?_⟩
  · rw [← hhom]
    exact congrArg Subtype.val
      (IsTerminal.uniqueUpToIso (terminalIsTerminal (C := Tot D)) totIsTerminal).hom_inv_id
  · rw [← hhom]
    exact congrArg Subtype.val
      (IsTerminal.uniqueUpToIso (terminalIsTerminal (C := Tot D)) totIsTerminal).inv_hom_id

/-- **181XIV** (`eff.tex:1206`): the left square of the effectus axioms is a
pullback in `Tot D`. -/
theorem tot_isPullback_plus (X Y : Tot D) :
    IsPullback (coprod.map (𝟙 X) (terminal.from Y))
      (coprod.map (terminal.from X) (𝟙 Y))
      (coprod.map (terminal.from X) (𝟙 (⊤_ (Tot D))))
      (coprod.map (𝟙 (⊤_ (Tot D))) (terminal.from Y)) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [coprod.map_map, coprod.map_map, Category.id_comp, Category.comp_id,
      Category.id_comp, Category.comp_id]
  · intro Z φ φ' h₁ h₂
    refine Subtype.ext (tp_jm ?_ ?_)
    · have h := congrArg (fun t => (Subtype.val t) ≫ tp₁ X (⊤_ (Tot D))) h₁
      simpa only [tot_comp_base, Category.assoc, tot_map_tp₁, tot_id_base,
        Category.comp_id] using h
    · have h := congrArg (fun t => (Subtype.val t) ≫ tp₂ (⊤_ (Tot D)) Y) h₂
      simpa only [tot_comp_base, Category.assoc, tot_map_tp₂, tot_id_base,
        Category.comp_id] using h
  · intro Z a b hab
    have hu_eq : a.1 ≫ tp₂ X (⊤_ (Tot D))
        = (b.1 ≫ tp₂ (⊤_ (Tot D)) Y) ≫ (terminal.from Y).1 := by
      have h := congrArg (fun t => (Subtype.val t) ≫ tp₂ (⊤_ (Tot D)) (⊤_ (Tot D))) hab
      simpa only [tot_comp_base, Category.assoc, tot_map_tp₂, tot_id_base,
        Category.comp_id] using h
    have hw_eq : (a.1 ≫ tp₁ X (⊤_ (Tot D))) ≫ (terminal.from X).1
        = b.1 ≫ tp₁ (⊤_ (Tot D)) Y := by
      have h := congrArg (fun t => (Subtype.val t) ≫ tp₁ (⊤_ (Tot D)) (⊤_ (Tot D))) hab
      simpa only [tot_comp_base, Category.assoc, tot_map_tp₁, tot_id_base,
        Category.comp_id] using h
    set α := a.1 ≫ tp₁ X (⊤_ (Tot D)) with hα
    set u := a.1 ≫ tp₂ X (⊤_ (Tot D)) with hu
    set β := b.1 ≫ tp₂ (⊤_ (Tot D)) Y with hβ
    have hdec := tpair_truth (X := X) (Y := ⊤_ (Tot D)) α u (tp_perp a.1)
    rw [tpair_eta a.1, tot_total_base a] at hdec
    have huβ : u ≫ truth (⊤_ (Tot D)).base = β ≫ truth Y.base := by
      rw [hu_eq, Category.assoc, tot_total_base (terminal.from Y)]
    have hperp : Perp (α ≫ truth X.base) (β ≫ truth Y.base) := by
      have h0 : Perp (α ≫ truth X.base) (u ≫ truth (⊤_ (Tot D)).base) := tp_perp a.1
      rwa [huβ] at h0
    refine ⟨⟨tpair (X := X) (Y := Y) α β hperp, ?_⟩, ?_, ?_⟩
    · show tpair (X := X) (Y := Y) α β hperp ≫ truth (X ⨿ Y : Tot D).base = truth Z.base
      rw [tpair_truth, hdec]
      exact PCM.ovee_congr rfl huβ.symm _ _
    · refine Subtype.ext (tp_jm ?_ ?_)
      · rw [tot_comp_base, Category.assoc, tot_map_tp₁, ← Category.assoc, tpair_tp₁,
          tot_id_base, Category.comp_id]
      · rw [tot_comp_base, Category.assoc, tot_map_tp₂, ← Category.assoc, tpair_tp₂,
          ← hu_eq]
    · refine Subtype.ext (tp_jm ?_ ?_)
      · rw [tot_comp_base, Category.assoc, tot_map_tp₁, ← Category.assoc, tpair_tp₁,
          hw_eq]
      · rw [tot_comp_base, Category.assoc, tot_map_tp₂, ← Category.assoc, tpair_tp₂,
          tot_id_base, Category.comp_id]

/-- **181XV** (`eff.tex:1246`): the right square of the effectus axioms is a
pullback in `Tot D`. -/
theorem tot_isPullback_kappa (X Y : Tot D) :
    IsPullback (terminal.from X) (coprod.inl : X ⟶ X ⨿ Y)
      (coprod.inl : (⊤_ (Tot D)) ⟶ (⊤_ (Tot D)) ⨿ (⊤_ (Tot D)))
      (coprod.map (terminal.from X) (terminal.from Y)) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · exact (coprod.inl_map _ _).symm
  · intro Z φ φ' _ h₂
    refine Subtype.ext ?_
    have h := congrArg (fun t => (Subtype.val t) ≫ tp₁ X Y) h₂
    simpa only [tot_comp_base, Category.assoc, tinl_tp₁, Category.comp_id] using h
  · intro Z a b hab
    have hA : (b.1 ≫ tp₁ X Y) ≫ (terminal.from X).1 = a.1 := by
      have h := congrArg (fun t => (Subtype.val t) ≫ tp₁ (⊤_ (Tot D)) (⊤_ (Tot D))) hab
      simp only [tot_comp_base, Category.assoc, tot_map_tp₁, tinl_tp₁,
        Category.comp_id] at h
      rw [Category.assoc]
      exact h.symm
    have hB : (b.1 ≫ tp₂ X Y) ≫ (terminal.from Y).1 = 0 := by
      have h := congrArg (fun t => (Subtype.val t) ≫ tp₂ (⊤_ (Tot D)) (⊤_ (Tot D))) hab
      simp only [tot_comp_base, Category.assoc, tot_map_tp₂, tinl_tp₂,
        FinPAC.comp_zero] at h
      rw [Category.assoc]
      exact h.symm
    set α := b.1 ≫ tp₁ X Y with hα
    set β := b.1 ≫ tp₂ X Y with hβ
    have hαtot : IsTotal α := by
      show α ≫ truth X.base = truth Z.base
      rw [← tot_total_base (terminal.from X), ← Category.assoc, hA, tot_total_base a]
    have hβ0 : β = 0 := by
      refine EffectusPartialForm.eq_zero_of_one_zero ?_
      show β ≫ truth Y.base = 0
      rw [← tot_total_base (terminal.from Y), ← Category.assoc, hB, FinPAC.zero_comp]
    refine ⟨⟨α, hαtot⟩, terminalIsTerminal.hom_ext _ _, ?_⟩
    refine Subtype.ext (tp_jm ?_ ?_)
    · rw [tot_comp_base, Category.assoc, tinl_tp₁, Category.comp_id]
    · rw [tot_comp_base, Category.assoc, tinl_tp₂, FinPAC.comp_zero]
      exact hβ0.symm

/-- Any map into a coproduct of `Tot D` decomposes `1` into the two
components (**181IX.2**). -/
theorem truth_decomp {X Y : Tot D} {Z : D} (p : Z ⟶ (X ⨿ Y : Tot D).base) :
    ovee ((p ≫ tp₁ X Y) ≫ truth X.base) ((p ≫ tp₂ X Y) ≫ truth Y.base) (tp_perp p)
      = p ≫ truth (X ⨿ Y : Tot D).base := by
  have h := tpair_truth (X := X) (Y := Y) (p ≫ tp₁ X Y) (p ≫ tp₂ X Y) (tp_perp p)
  rw [tpair_eta p] at h
  exact h.symm

/-- Two total maps into a coproduct of `Tot D` that agree in the first
coordinate agree in the second one after composing with `1`: both are the
orthocomplement of the same predicate (**181XVI**). -/
theorem tot_snd_coord_eq {X Y Z : Tot D} (f g : Z ⟶ X ⨿ Y)
    (h : f.1 ≫ tp₁ X Y = g.1 ≫ tp₁ X Y) :
    (f.1 ≫ tp₂ X Y) ≫ truth Y.base = (g.1 ≫ tp₂ X Y) ≫ truth Y.base := by
  have e₁ : ovee ((f.1 ≫ tp₁ X Y) ≫ truth X.base) ((f.1 ≫ tp₂ X Y) ≫ truth Y.base)
      (tp_perp f.1) = truth Z.base := by
    rw [truth_decomp f.1]; exact tot_total_base f
  have e₂ : ovee ((g.1 ≫ tp₁ X Y) ≫ truth X.base) ((g.1 ≫ tp₂ X Y) ≫ truth Y.base)
      (tp_perp g.1) = truth Z.base := by
    rw [truth_decomp g.1]; exact tot_total_base g
  have hperp : Perp ((f.1 ≫ tp₁ X Y) ≫ truth X.base) ((g.1 ≫ tp₂ X Y) ≫ truth Y.base) := by
    rw [h]; exact tp_perp g.1
  have e₂' : ovee ((f.1 ≫ tp₁ X Y) ≫ truth X.base) ((g.1 ≫ tp₂ X Y) ≫ truth Y.base) hperp
      = truth Z.base := by
    rw [← e₂]; exact PCM.ovee_congr (by rw [h]) rfl _ _
  rw [EffectusPartialForm.orth_unique (tp_perp f.1) e₁,
    EffectusPartialForm.orth_unique hperp e₂']

/-- **181XVI** (`eff.tex:1272`): the two cotuples `1+1+1 ⟶ 1+1` are jointly
monic in `Tot D`. -/
theorem tot_jointlyMonic_cotuples :
    JointlyMonic
      (coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr :
        ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) ⨿ (⊤_ (Tot D)) ⟶ (⊤_ (Tot D)) ⨿ (⊤_ (Tot D)))
      (coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr) := by
  intro Z f₁ f₂ h₁ h₂
  -- `▷₁ ∘ m₁ = [id,0,0]` and `▷₁ ∘ m₂ = [0,id,0]`
  have S : (coprod.desc (coprod.inr : (⊤_ (Tot D)) ⟶ (⊤_ (Tot D)) ⨿ (⊤_ (Tot D)))
        coprod.inl).1 ≫ tp₁ (⊤_ (Tot D)) (⊤_ (Tot D)) = tp₂ (⊤_ (Tot D)) (⊤_ (Tot D)) := by
    refine tot_hom_ext_base ?_ ?_
    · rw [← Category.assoc, tot_desc_inl, tinr_tp₁, tinl_tp₂]
    · rw [← Category.assoc, tot_desc_inr, tinl_tp₁, tinr_tp₂]
  have L1 : (coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr :
        ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) ⨿ (⊤_ (Tot D)) ⟶ (⊤_ (Tot D)) ⨿ (⊤_ (Tot D))).1
      ≫ tp₁ (⊤_ (Tot D)) (⊤_ (Tot D))
      = tp₁ ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) (⊤_ (Tot D)) ≫ tp₁ (⊤_ (Tot D)) (⊤_ (Tot D)) := by
    refine tot_hom_ext_base ?_ ?_
    · rw [← Category.assoc, tot_desc_inl, coprod.desc_inl_inr, tot_id_base,
        Category.id_comp, ← Category.assoc, tinl_tp₁, Category.id_comp]
    · rw [← Category.assoc, tot_desc_inr, tinr_tp₁, ← Category.assoc, tinr_tp₁,
        FinPAC.zero_comp]
  have L2 : (coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr :
        ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) ⨿ (⊤_ (Tot D)) ⟶ (⊤_ (Tot D)) ⨿ (⊤_ (Tot D))).1
      ≫ tp₁ (⊤_ (Tot D)) (⊤_ (Tot D))
      = tp₁ ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) (⊤_ (Tot D)) ≫ tp₂ (⊤_ (Tot D)) (⊤_ (Tot D)) := by
    refine tot_hom_ext_base ?_ ?_
    · rw [← Category.assoc, tot_desc_inl, S, ← Category.assoc, tinl_tp₁, Category.id_comp]
    · rw [← Category.assoc, tot_desc_inr, tinr_tp₁, ← Category.assoc, tinr_tp₁,
        FinPAC.zero_comp]
  -- the first two coordinates agree
  have ha : (f₁.1 ≫ tp₁ ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) (⊤_ (Tot D)))
        ≫ tp₁ (⊤_ (Tot D)) (⊤_ (Tot D))
      = (f₂.1 ≫ tp₁ ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) (⊤_ (Tot D)))
        ≫ tp₁ (⊤_ (Tot D)) (⊤_ (Tot D)) := by
    have h := congrArg (fun t => (Subtype.val t) ≫ tp₁ (⊤_ (Tot D)) (⊤_ (Tot D))) h₁
    simp only [tot_comp_base, Category.assoc] at h
    rw [Category.assoc, Category.assoc, ← L1, ← Category.assoc, ← Category.assoc]
    simpa only [Category.assoc] using h
  have hb : (f₁.1 ≫ tp₁ ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) (⊤_ (Tot D)))
        ≫ tp₂ (⊤_ (Tot D)) (⊤_ (Tot D))
      = (f₂.1 ≫ tp₁ ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) (⊤_ (Tot D)))
        ≫ tp₂ (⊤_ (Tot D)) (⊤_ (Tot D)) := by
    have h := congrArg (fun t => (Subtype.val t) ≫ tp₁ (⊤_ (Tot D)) (⊤_ (Tot D))) h₂
    simp only [tot_comp_base, Category.assoc] at h
    rw [Category.assoc, Category.assoc, ← L2, ← Category.assoc, ← Category.assoc]
    simpa only [Category.assoc] using h
  have hp : f₁.1 ≫ tp₁ ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) (⊤_ (Tot D))
      = f₂.1 ≫ tp₁ ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) (⊤_ (Tot D)) := tp_jm ha hb
  have := truth_terminal_isIso (D := D)
  have hc' : f₁.1 ≫ tp₂ ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) (⊤_ (Tot D))
      = f₂.1 ≫ tp₂ ((⊤_ (Tot D)) ⨿ (⊤_ (Tot D))) (⊤_ (Tot D)) :=
    (cancel_mono (truth (⊤_ (Tot D)).base)).mp (tot_snd_coord_eq f₁ f₂ hp)
  exact Subtype.ext (tp_jm hp hc')

end Axioms

section Assemble

variable (D)

/-- **181XI** (`eff-partial-to-total`, eff.tex:1165, Theorem): the total maps
of an effectus in partial form form an effectus in total form. -/
theorem tot_effectusTotalForm [HasFiniteCoproducts (Tot D)] [HasTerminal (Tot D)] :
    EffectusTotalForm (Tot D) where
  isPullback_plus := tot_isPullback_plus
  isPullback_kappa := tot_isPullback_kappa
  jointlyMonic_cotuples := tot_jointlyMonic_cotuples

end Assemble

end PartialToTotalStructure

/-! ## Interlude on pullbacks and joint monicity (parsecs 183–184) -/

section Pullbacks

variable {D : Type u} [Category.{v} D]

/-- **183II** (`exc-jointly-monic-pullback`, eff.tex:1336, Exercise): the
legs of a pullback square are jointly monic. -/
theorem exc_jointly_monic_pullback {P A B X : D}
    {m₁ : P ⟶ B} {m₂ : P ⟶ A} {f : B ⟶ X} {g : A ⟶ X}
    (h : IsPullback m₁ m₂ f g) : JointlyMonic m₁ m₂ :=
  fun _ _ _ h₀ h₁ => h.hom_ext h₀ h₁

/-- **183III.1** (`pullback-lemma`, eff.tex:1347, Exercise): *pullback
lemma*, pasting: if the left and right inner squares are pullbacks, then so
is the outer rectangle. -/
theorem pullback_lemma_1 {A B E X Y Z : D}
    {f : A ⟶ B} {g : B ⟶ E} {k : A ⟶ X} {l : B ⟶ Y} {m : E ⟶ Z}
    {f' : X ⟶ Y} {g' : Y ⟶ Z}
    (h₁ : IsPullback f k l f') (h₂ : IsPullback g l m g') :
    IsPullback (f ≫ g) k m (f' ≫ g') :=
  h₁.paste_horiz h₂

/-- **183III.2** (`pullback-lemma`, eff.tex:1347, Exercise): if the outer
rectangle is a pullback and `g`, `l` are jointly monic, then the left inner
square is a pullback.  (Stronger than the usual formulation, which assumes
the right square is a pullback; see remark 183IV.) -/
theorem pullback_lemma_2 {A B E X Y Z : D}
    {f : A ⟶ B} {g : B ⟶ E} {k : A ⟶ X} {l : B ⟶ Y} {m : E ⟶ Z}
    {f' : X ⟶ Y} {g' : Y ⟶ Z}
    (wl : f ≫ l = k ≫ f') (wr : g ≫ m = l ≫ g')
    (houter : IsPullback (f ≫ g) k m (f' ≫ g'))
    (hjm : JointlyMonic g l) :
    IsPullback f k l f' := by
  refine IsPullback.mk' wl ?_ ?_
  · intro T φ φ' hf hk
    refine houter.hom_ext ?_ hk
    rw [← Category.assoc, ← Category.assoc, hf]
  · intro T a b hab
    have hcond : (a ≫ g) ≫ m = b ≫ f' ≫ g' := by
      rw [Category.assoc, wr, ← Category.assoc, hab, Category.assoc]
    refine ⟨houter.lift (a ≫ g) b hcond, ?_, houter.lift_snd _ _ _⟩
    refine hjm _ _ ?_ ?_
    · rw [Category.assoc, houter.lift_fst]
    · rw [Category.assoc, wl, ← Category.assoc, houter.lift_snd, hab]

/-- **184II** (`joint-monicity-stable`, eff.tex:1401, Lemma): joint
monicity is stable under (pullback-like) pasting: if the pairs `(m₁, m₂)`,
`(n₁, g₁)`, `(n₂, g₂)` and `(h₁, h₂)` in the commuting diagram
```
P  --h₁-> P₁ --n₁-> X₁
|h₂       |g₁       |f₁
v         v         v
P₂ --g₂-> A  --m₁-> B₁
|n₂       |m₂
v         v
X₂ --f₂-> B₂
```
are jointly monic, then so is `(n₁ ∘ h₁, n₂ ∘ h₂)`. -/
theorem joint_monicity_stable {P P₁ P₂ A X₁ X₂ B₁ B₂ : D}
    {h₁ : P ⟶ P₁} {h₂ : P ⟶ P₂} {n₁ : P₁ ⟶ X₁} {n₂ : P₂ ⟶ X₂}
    {g₁ : P₁ ⟶ A} {g₂ : P₂ ⟶ A} {m₁ : A ⟶ B₁} {m₂ : A ⟶ B₂}
    {f₁ : X₁ ⟶ B₁} {f₂ : X₂ ⟶ B₂}
    (w₁ : n₁ ≫ f₁ = g₁ ≫ m₁) (w₂ : n₂ ≫ f₂ = g₂ ≫ m₂)
    (w : h₁ ≫ g₁ = h₂ ≫ g₂)
    (jm : JointlyMonic m₁ m₂) (jn₁ : JointlyMonic n₁ g₁)
    (jn₂ : JointlyMonic n₂ g₂) (jh : JointlyMonic h₁ h₂) :
    JointlyMonic (h₁ ≫ n₁) (h₂ ≫ n₂) := by
  intro Z a b ha hb
  have ha' := reassoc_of% ha
  have hb' := reassoc_of% hb
  have hw := reassoc_of% w
  -- the two composites into `A` agree, by joint monicity of `(m₁, m₂)`
  have hA : a ≫ h₁ ≫ g₁ = b ≫ h₁ ≫ g₁ := by
    refine jm _ _ ?_ ?_
    · simp only [Category.assoc]
      rw [← w₁]
      exact ha' f₁
    · simp only [Category.assoc]
      rw [hw, ← w₂]
      exact hb' f₂
  refine jh _ _ (jn₁ _ _ ?_ ?_) (jn₂ _ _ ?_ ?_)
  · simpa only [Category.assoc] using ha
  · simpa only [Category.assoc] using hA
  · simpa only [Category.assoc] using hb
  · simp only [Category.assoc]
    rw [← w]
    simpa only [Category.assoc] using hA

end Pullbacks

/-! ## From total to partial (parsecs 185–187) -/

section TotalToPartial

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasTerminal C]
  [EffectusTotalForm C]

/-- The rectangle `(1,3)` of the proof of 185I (eff.tex:1487): pasting the
square to be proved on top of the axiom square `!+id, id+!`. -/
private theorem tot_pullbacks_left_aux {P A B : C} (f : A ⟶ B) :
    IsPullback (coprod.map (𝟙 P) f) (coprod.map (terminal.from P) (𝟙 A))
      (coprod.map (terminal.from P) (𝟙 B)) (coprod.map (𝟙 (⊤_ C)) f) := by
  have hf : f ≫ terminal.from B = terminal.from A := terminalIsTerminal.hom_ext _ _
  refine pullback_lemma_2 (g := coprod.map (𝟙 P) (terminal.from B))
    (m := coprod.map (terminal.from P) (𝟙 (⊤_ C)))
    (g' := coprod.map (𝟙 (⊤_ C)) (terminal.from B)) ?_ ?_ ?_
    (exc_jointly_monic_pullback (EffectusTotalForm.isPullback_plus P B))
  · simp only [coprod.map_map, Category.id_comp, Category.comp_id]
  · simp only [coprod.map_map, Category.id_comp, Category.comp_id]
  · rw [show coprod.map (𝟙 P) f ≫ coprod.map (𝟙 P) (terminal.from B)
        = coprod.map (𝟙 P) (terminal.from A) by
      rw [coprod.map_map, Category.comp_id, hf],
    show coprod.map (𝟙 (⊤_ C)) f ≫ coprod.map (𝟙 (⊤_ C)) (terminal.from B)
        = coprod.map (𝟙 (⊤_ C)) (terminal.from A) by
      rw [coprod.map_map, Category.comp_id, hf]]
    exact EffectusTotalForm.isPullback_plus P A

/-- **185I** (`tot-pullbacks`, eff.tex:1458, Proposition), left square: in
an effectus in total form every square
`(id+f, g+id; g+id, id+f)` on `X+A`, `X+B`, `Y+A`, `Y+B` is a pullback. -/
theorem tot_pullbacks_left {X Y A B : C} (g : X ⟶ Y) (f : A ⟶ B) :
    IsPullback (coprod.map (𝟙 X) f) (coprod.map g (𝟙 A))
      (coprod.map g (𝟙 B)) (coprod.map (𝟙 Y) f) := by
  have hg : g ≫ terminal.from Y = terminal.from X := terminalIsTerminal.hom_ext _ _
  refine IsPullback.flip ?_
  refine pullback_lemma_2 (g := coprod.map (terminal.from Y) (𝟙 A))
    (m := coprod.map (𝟙 (⊤_ C)) f)
    (g' := coprod.map (terminal.from Y) (𝟙 B)) ?_ ?_ ?_
    (exc_jointly_monic_pullback (tot_pullbacks_left_aux (P := Y) f).flip)
  · simp only [coprod.map_map, Category.id_comp, Category.comp_id]
  · simp only [coprod.map_map, Category.id_comp, Category.comp_id]
  · rw [show coprod.map g (𝟙 A) ≫ coprod.map (terminal.from Y) (𝟙 A)
        = coprod.map (terminal.from X) (𝟙 A) by
      rw [coprod.map_map, Category.comp_id, hg],
    show coprod.map g (𝟙 B) ≫ coprod.map (terminal.from Y) (𝟙 B)
        = coprod.map (terminal.from X) (𝟙 B) by
      rw [coprod.map_map, Category.comp_id, hg]]
    exact (tot_pullbacks_left_aux (P := X) f).flip

/-- **185I** (`tot-pullbacks`, eff.tex:1458, Proposition), right square: in
an effectus in total form every square `(f, κ₁; κ₁, f+g)` is a pullback. -/
theorem tot_pullbacks_right {X Y A B : C} (f : X ⟶ Y) (g : A ⟶ B) :
    IsPullback f (coprod.inl : X ⟶ X ⨿ A)
      (coprod.inl : Y ⟶ Y ⨿ B) (coprod.map f g) := by
  -- paste the axiom square for `Y, B` on the right of the square to be shown;
  -- the outer rectangle is the axiom square for `X, A` (eff.tex:1509)
  have hr := EffectusTotalForm.isPullback_kappa (C := C) Y B
  refine pullback_lemma_2 (coprod.inl_map f g).symm hr.w ?_
    (exc_jointly_monic_pullback hr)
  have e₁ : f ≫ terminal.from Y = terminal.from X := terminalIsTerminal.hom_ext _ _
  have e₂ : coprod.map f g ≫ coprod.map (terminal.from Y) (terminal.from B)
      = coprod.map (terminal.from X) (terminal.from A) := by
    rw [coprod.map_map, e₁,
      show g ≫ terminal.from B = terminal.from A from terminalIsTerminal.hom_ext _ _]
  rw [e₁, e₂]
  exact EffectusTotalForm.isPullback_kappa X A

/-- **186II** (`par-c-coprod`, eff.tex:1536, Exercise): if `κ₁, κ₂` form a
coproduct in `C`, then `κ̂₁, κ̂₂` form a coproduct in `Par C`. -/
theorem par_c_coprod (X Y : C) :
    Nonempty (IsColimit (BinaryCofan.mk
      (Par.hat (coprod.inl : X ⟶ X ⨿ Y)) (Par.hat (coprod.inr : Y ⟶ X ⨿ Y)))) := by
  refine ⟨BinaryCofan.IsColimit.mk _
    (fun {T} f g => (coprod.desc f g : X ⨿ Y ⟶ T.base ⨿ ⊤_ C)) ?_ ?_ ?_⟩
  · intro T f g
    show ((coprod.inl : X ⟶ X ⨿ Y) ≫ coprod.inl) ≫
      coprod.desc (coprod.desc f g) coprod.inr = f
    rw [Category.assoc, coprod.inl_desc, coprod.inl_desc]
  · intro T f g
    show ((coprod.inr : Y ⟶ X ⨿ Y) ≫ coprod.inl) ≫
      coprod.desc (coprod.desc f g) coprod.inr = g
    rw [Category.assoc, coprod.inl_desc, coprod.inr_desc]
  · intro T f g m hf hg
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc]
      rw [← hf]
      show _ = ((coprod.inl : X ⟶ X ⨿ Y) ≫ coprod.inl) ≫
        coprod.desc (show X ⨿ Y ⟶ T.base ⨿ ⊤_ C from m) coprod.inr
      rw [Category.assoc, coprod.inl_desc]
    · rw [coprod.inr_desc]
      rw [← hg]
      show _ = ((coprod.inr : Y ⟶ X ⨿ Y) ≫ coprod.inl) ≫
        coprod.desc (show X ⨿ Y ⟶ T.base ⨿ ⊤_ C from m) coprod.inr
      rw [Category.assoc, coprod.inl_desc]

/-- **186II** (`par-c-coprod`, eff.tex:1536, Exercise): `0` is also the
initial object of `Par C`. -/
theorem par_c_initial : Nonempty (IsInitial (Par.of (⊥_ C))) :=
  ⟨IsInitial.ofUniqueHom
    (fun Y => (initial.to (Y.base ⨿ ⊤_ C) : Par.of (⊥_ C) ⟶ Y))
    (fun Y m => initialIsInitial.hom_ext
      (show (⊥_ C) ⟶ Y.base ⨿ ⊤_ C from m) _)⟩

/-- `! : 1 ⟶ 1` is the identity. -/
private theorem terminal_from_self :
    terminal.from (⊤_ C) = 𝟙 (⊤_ C) := terminalIsTerminal.hom_ext _ _

/-- The identity of `Par C` is `κ₁`. -/
private theorem par_id_eq (X : C) :
    (show X ⟶ X ⨿ ⊤_ C from 𝟙 (Par.of X)) = coprod.inl := rfl

/-- Since `Par C(Z, W) = C(Z, W + 1)` naturally in `W`, a square of partial
maps is a pullback in `Par C` as soon as the square obtained by
post-composing each map with `[–, κ₂] : (–) + 1 ⟶ (–) + 1` is a pullback
in `C`.  (This is what makes the reduction of the proof of 186IV to
185I work.) -/
private theorem par_isPullback_of_isPullback {P B₁ B₂ Z : C}
    (fst : Par.of P ⟶ Par.of B₁) (snd : Par.of P ⟶ Par.of B₂)
    (f : Par.of B₁ ⟶ Par.of Z) (g : Par.of B₂ ⟶ Par.of Z)
    (h : IsPullback
      (coprod.desc (show P ⟶ B₁ ⨿ ⊤_ C from fst) coprod.inr)
      (coprod.desc (show P ⟶ B₂ ⨿ ⊤_ C from snd) coprod.inr)
      (coprod.desc (show B₁ ⟶ Z ⨿ ⊤_ C from f) coprod.inr)
      (coprod.desc (show B₂ ⟶ Z ⨿ ⊤_ C from g) coprod.inr)) :
    IsPullback fst snd f g := by
  refine IsPullback.mk' ?_ (fun _ _ _ hφ hφ' => h.hom_ext hφ hφ')
    (fun _ a b hab => ⟨h.lift a b hab, h.lift_fst _ _ _, h.lift_snd _ _ _⟩)
  have hw := (coprod.inl : P ⟶ P ⨿ ⊤_ C) ≫= h.w
  rw [← Category.assoc, ← Category.assoc, coprod.inl_desc, coprod.inl_desc] at hw
  exact hw

/-- **186IV** (`par-pullbacks`, eff.tex:1562, Proposition), left square:
squares `(id+f̂, ĝ+id; ĝ+id, id+f̂)` are pullbacks in `Par C`. -/
theorem par_pullbacks_left {X Y A B : C} (g : X ⟶ Y) (f : A ⟶ B) :
    IsPullback (Par.map (𝟙 (Par.of X)) (Par.hat f))
      (Par.map (Par.hat g) (𝟙 (Par.of A)))
      (Par.map (Par.hat g) (𝟙 (Par.of B)))
      (Par.map (𝟙 (Par.of Y)) (Par.hat f)) := by
  -- it suffices that the square `(id+(f+id), g+id; g+id, id+(f+id))` on
  -- `X+(A+1)`, … is a pullback in `C`, which is 185I (eff.tex:1585)
  refine par_isPullback_of_isPullback _ _ _ _ ?_
  refine (tot_pullbacks_left g (coprod.map f (𝟙 (⊤_ C)))).of_iso
    (coprod.associator X A (⊤_ C)).symm (coprod.associator X B (⊤_ C)).symm
    (coprod.associator Y A (⊤_ C)).symm (coprod.associator Y B (⊤_ C)).symm
    ?_ ?_ ?_ ?_
  all_goals
    ext <;> simp [Par.map, Par.hat, par_id_eq, coprod.inl_desc, coprod.inr_desc]

/-- **186IV** (`par-pullbacks`, eff.tex:1562, Proposition), right square:
squares `(f̂+id, ▷₁; ▷₁, f̂)` are pullbacks in `Par C`. -/
theorem par_pullbacks_right {A B X : C} (f : A ⟶ B) :
    IsPullback (Par.map (Par.hat f) (𝟙 (Par.of X)))
      (Par.pproj₁ A X) (Par.pproj₁ B X) (Par.hat f) := by
  -- it suffices that the square `(f+id, id+!; id+!, f+id)` on `A+(X+1)`, …
  -- is a pullback in `C`, which is 185I (eff.tex:1592)
  refine par_isPullback_of_isPullback _ _ _ _ ?_
  refine (tot_pullbacks_left f (terminal.from (X ⨿ ⊤_ C))).flip.of_iso
    (coprod.associator A X (⊤_ C)).symm (coprod.associator B X (⊤_ C)).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals
    ext <;> simp [Par.map, Par.hat, Par.pproj₁, Par.zero, par_id_eq,
      coprod.inl_desc, coprod.inr_desc, terminal_from_self]

/-- The canonical iso `0 + 1 ≅ 1` (used for the zero object of `Par C`):
`[!, id] ≫ κ₂ = id`. -/
private theorem coprod_initial_inr :
    (coprod.desc (initial.to (⊤_ C)) (𝟙 (⊤_ C))) ≫ (coprod.inr : (⊤_ C) ⟶ (⊥_ C) ⨿ ⊤_ C)
      = 𝟙 ((⊥_ C) ⨿ ⊤_ C) := by
  refine coprod.hom_ext ?_ ?_
  · exact initialIsInitial.hom_ext _ _
  · rw [← Category.assoc, coprod.inr_desc, Category.id_comp, Category.comp_id]

/-- **186VII** (`toteff-zero`, eff.tex:1609, Exercise): `0` is a zero
object in `Par C` (initial part). -/
theorem toteff_zero_initial : Nonempty (IsInitial (Par.of (⊥_ C))) := par_c_initial

/-- **186VII** (`toteff-zero`, eff.tex:1609, Exercise): `0` is a zero
object in `Par C` (terminal part). -/
theorem toteff_zero_terminal : Nonempty (IsTerminal (Par.of (⊥_ C))) := by
  refine ⟨IsTerminal.ofUniqueHom
    (fun X => (terminal.from X.base ≫ coprod.inr : X.base ⟶ (⊥_ C) ⨿ ⊤_ C)) ?_⟩
  intro X m
  have hm : (show X.base ⟶ (⊥_ C) ⨿ ⊤_ C from m) ≫
      coprod.desc (initial.to (⊤_ C)) (𝟙 (⊤_ C)) = terminal.from X.base :=
    terminalIsTerminal.hom_ext _ _
  show (show X.base ⟶ (⊥_ C) ⨿ ⊤_ C from m) = terminal.from X.base ≫ coprod.inr
  rw [← hm, Category.assoc, coprod_initial_inr, Category.comp_id]

/-- **186VII** (`toteff-zero`, eff.tex:1609, Exercise): the unique map
`X ⟶ 0 ⟶ Y` in `Par C` is the zero map of 186VI. -/
theorem toteff_zero_comp (X Y : C)
    (u : Par.of X ⟶ Par.of (⊥_ C)) (v : Par.of (⊥_ C) ⟶ Par.of Y) :
    u ≫ v = Par.zero X Y := by
  have hv : coprod.desc (show (⊥_ C) ⟶ Y ⨿ ⊤_ C from v) coprod.inr
      = terminal.from ((⊥_ C) ⨿ ⊤_ C) ≫ (coprod.inr : (⊤_ C) ⟶ Y ⨿ ⊤_ C) := by
    refine coprod.hom_ext ?_ ?_
    · exact initialIsInitial.hom_ext _ _
    · rw [coprod.inr_desc, ← Category.assoc,
        show (coprod.inr : (⊤_ C) ⟶ (⊥_ C) ⨿ ⊤_ C) ≫ terminal.from ((⊥_ C) ⨿ ⊤_ C)
          = 𝟙 (⊤_ C) from terminalIsTerminal.hom_ext _ _, Category.id_comp]
  show (show X ⟶ (⊥_ C) ⨿ ⊤_ C from u) ≫ coprod.desc v coprod.inr
      = terminal.from X ≫ coprod.inr
  rw [hv, ← Category.assoc]
  congr 1
  exact terminalIsTerminal.hom_ext _ _

/-- `1 + 1 : Y + 1 ⟶ 1 + 1` written as a cotuple. -/
private theorem coprod_map_terminal (Y : C) :
    coprod.map (terminal.from Y) (terminal.from (⊤_ C))
      = coprod.desc (terminal.from Y ≫ coprod.inl)
          (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ ⊤_ C) := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_map, coprod.inl_desc]
  · rw [coprod.inr_map, coprod.inr_desc,
      show terminal.from (⊤_ C) = 𝟙 (⊤_ C) from terminalIsTerminal.hom_ext _ _,
      Category.id_comp]

/-- The second-coprojection variant of the right pullback square of 180I,
obtained from the axiom by swapping the two summands. -/
private theorem isPullback_kappa_inr (Y : C) :
    IsPullback (terminal.from (⊤_ C)) (coprod.inr : (⊤_ C) ⟶ Y ⨿ ⊤_ C)
      (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ ⊤_ C)
      (coprod.map (terminal.from Y) (terminal.from (⊤_ C))) := by
  refine (EffectusTotalForm.isPullback_kappa (⊤_ C) Y).of_iso (Iso.refl _) (Iso.refl _)
    (coprod.braiding (⊤_ C) Y) (coprod.braiding (⊤_ C) (⊤_ C)) ?_ ?_ ?_ ?_
  · simp
  · simp
    exact coprod.inl_desc _ _
  · simp
    exact coprod.inl_desc _ _
  · refine coprod.hom_ext ?_ ?_ <;> simp

/-- **186VIII.1** (`pardp`, eff.tex:1614, Proposition): a partial map `f`
with `1 ⊙ f = 1` is `ĝ` for a unique total map `g` of `C`. -/
theorem pardp_1 {X Y : C} (f : Par.of X ⟶ Par.of Y)
    (h : f ≫ Par.one Y = Par.one X) : ∃! g : X ⟶ Y, f = Par.hat g := by
  have hsq := EffectusTotalForm.isPullback_kappa (C := C) Y (⊤_ C)
  have h' : terminal.from X ≫ (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ ⊤_ C)
      = (show X ⟶ Y ⨿ ⊤_ C from f) ≫
        coprod.map (terminal.from Y) (terminal.from (⊤_ C)) := by
    rw [coprod_map_terminal]
    exact h.symm
  refine ⟨hsq.lift (terminal.from X) f h', (hsq.lift_snd _ _ _).symm, ?_⟩
  intro g hg
  refine hsq.hom_ext (terminalIsTerminal.hom_ext _ _) ?_
  rw [hsq.lift_snd]
  exact hg.symm

/-- **186VIII.2** (`pardp`, eff.tex:1614, Proposition): a partial map `f`
with `1 ⊙ f = 0` is the zero map. -/
theorem pardp_2 {X Y : C} (f : Par.of X ⟶ Par.of Y)
    (h : f ≫ Par.one Y = Par.zero X (⊤_ C)) : f = Par.zero X Y := by
  have hsq := isPullback_kappa_inr (C := C) Y
  have h' : terminal.from X ≫ (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ ⊤_ C)
      = (show X ⟶ Y ⨿ ⊤_ C from f) ≫
        coprod.map (terminal.from Y) (terminal.from (⊤_ C)) := by
    rw [coprod_map_terminal]
    exact h.symm
  have hlift := hsq.lift_snd (terminal.from X) f h'
  show (show X ⟶ Y ⨿ ⊤_ C from f) = terminal.from X ≫ coprod.inr
  rw [← hlift, terminalIsTerminal.hom_ext (hsq.lift (terminal.from X) f h')
    (terminal.from X)]

/-- The rebracketing `A + (X + 1) ≅ (X + A) + 1`, used for the
`▷₂`-variant of the right pullback square of 186IV. -/
private noncomputable def swapAssocIso (X A : C) :
    A ⨿ (X ⨿ ⊤_ C) ≅ (X ⨿ A) ⨿ ⊤_ C where
  hom := coprod.desc (coprod.inr ≫ coprod.inl)
    (coprod.desc (coprod.inl ≫ coprod.inl) coprod.inr)
  inv := coprod.desc (coprod.desc (coprod.inl ≫ coprod.inr) coprod.inl)
    (coprod.inr ≫ coprod.inr)
  hom_inv_id := by ext <;> simp [coprod.inl_desc, coprod.inr_desc]
  inv_hom_id := by ext <;> simp [coprod.inl_desc, coprod.inr_desc]

/-- The `▷₂`-variant of the right pullback square of 186IV: squares
`(id+f̂, ▷₂; ▷₂, f̂)` are pullbacks in `Par C`.  (The diagram in the proof of
186X uses both variants; this one reduces to 185I in the same way, via the
rebracketing `A+(X+1) ≅ (X+A)+1`.) -/
private theorem par_pullbacks_right₂ {A B X : C} (f : A ⟶ B) :
    IsPullback (Par.map (𝟙 (Par.of X)) (Par.hat f))
      (Par.pproj₂ X A) (Par.pproj₂ X B) (Par.hat f) := by
  refine par_isPullback_of_isPullback _ _ _ _ ?_
  refine (tot_pullbacks_left f (terminal.from (X ⨿ ⊤_ C))).flip.of_iso
    (swapAssocIso X A) (swapAssocIso X B) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals
    ext <;> simp [Par.map, Par.hat, Par.pproj₂, Par.zero, par_id_eq,
      swapAssocIso, coprod.inl_desc, coprod.inr_desc, terminal_from_self]

/-- `▷₁ : 1+1 ⇸ 1` is the cotuple `[κ₁,κ₂,κ₂]` of the joint monicity axiom
of 180I. -/
private theorem par_pproj₁_one :
    (coprod.desc (show (⊤_ C) ⨿ ⊤_ C ⟶ (⊤_ C) ⨿ ⊤_ C from
        Par.pproj₁ (⊤_ C) (⊤_ C)) coprod.inr :
      ((⊤_ C) ⨿ ⊤_ C) ⨿ ⊤_ C ⟶ (⊤_ C) ⨿ ⊤_ C)
      = coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr := by
  simp [Par.pproj₁, Par.zero, terminal_from_self]

/-- `▷₂ : 1+1 ⇸ 1` is the cotuple `[κ₂,κ₁,κ₂]` of the joint monicity axiom
of 180I. -/
private theorem par_pproj₂_one :
    (coprod.desc (show (⊤_ C) ⨿ ⊤_ C ⟶ (⊤_ C) ⨿ ⊤_ C from
        Par.pproj₂ (⊤_ C) (⊤_ C)) coprod.inr :
      ((⊤_ C) ⨿ ⊤_ C) ⨿ ⊤_ C ⟶ (⊤_ C) ⨿ ⊤_ C)
      = coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr := by
  simp [Par.pproj₂, Par.zero, terminal_from_self]

/-- The joint monicity axiom of 180I, read in `Par C`: `▷₁, ▷₂ : 1+1 ⇸ 1`
are jointly monic (eff.tex:1703). -/
private theorem par_pproj_jointlyMonic_one :
    JointlyMonic (Par.pproj₁ (⊤_ C) (⊤_ C)) (Par.pproj₂ (⊤_ C) (⊤_ C)) := by
  intro Z a b ha hb
  refine EffectusTotalForm.jointlyMonic_cotuples a b ?_ ?_
  · rw [← par_pproj₁_one]
    exact ha
  · rw [← par_pproj₂_one]
    exact hb

/-- **186X** (`pproj-joint-monicity`, eff.tex:1667, Proposition): the
partial projectors `▷₁, ▷₂` are jointly monic in `Par C`. -/
theorem pproj_joint_monicity (X Y : C) :
    JointlyMonic (Par.pproj₁ X Y) (Par.pproj₂ X Y) := by
  -- the diagram of eff.tex:1676: the three inner squares are pullbacks by
  -- 186IV, the pair `▷₁, ▷₂ : 1+1 ⇸ 1` is jointly monic by the axiom, and
  -- 184II propagates joint monicity to the outer `▷₁, ▷₂`
  have hTL := par_pullbacks_left (terminal.from X) (terminal.from Y)
  have hTR := par_pullbacks_right (X := ⊤_ C) (terminal.from X)
  have hBL := par_pullbacks_right₂ (X := ⊤_ C) (terminal.from Y)
  have key := joint_monicity_stable hTR.w.symm hBL.w.symm hTL.w
    par_pproj_jointlyMonic_one
    (exc_jointly_monic_pullback hTR.flip)
    (exc_jointly_monic_pullback hBL.flip)
    (exc_jointly_monic_pullback hTL)
  have e₁ : Par.map (𝟙 (Par.of X)) (Par.hat (terminal.from Y)) ≫
      Par.pproj₁ X (⊤_ C) = Par.pproj₁ X Y := by
    show (show X ⨿ Y ⟶ (X ⨿ ⊤_ C) ⨿ ⊤_ C from
        Par.map (𝟙 (Par.of X)) (Par.hat (terminal.from Y))) ≫
        coprod.desc (show X ⨿ ⊤_ C ⟶ X ⨿ ⊤_ C from Par.pproj₁ X (⊤_ C))
          coprod.inr
      = (show X ⨿ Y ⟶ X ⨿ ⊤_ C from Par.pproj₁ X Y)
    ext <;> simp [Par.map, Par.hat, Par.pproj₁, Par.zero, par_id_eq,
      coprod.inl_desc, coprod.inr_desc, terminal_from_self]
  have e₂ : Par.map (Par.hat (terminal.from X)) (𝟙 (Par.of Y)) ≫
      Par.pproj₂ (⊤_ C) Y = Par.pproj₂ X Y := by
    show (show X ⨿ Y ⟶ ((⊤_ C) ⨿ Y) ⨿ ⊤_ C from
        Par.map (Par.hat (terminal.from X)) (𝟙 (Par.of Y))) ≫
        coprod.desc (show (⊤_ C) ⨿ Y ⟶ Y ⨿ ⊤_ C from Par.pproj₂ (⊤_ C) Y)
          coprod.inr
      = (show X ⨿ Y ⟶ Y ⨿ ⊤_ C from Par.pproj₂ X Y)
    ext <;> simp [Par.map, Par.hat, Par.pproj₂, Par.zero, par_id_eq,
      coprod.inl_desc, coprod.inr_desc, terminal_from_self]
  rwa [e₁, e₂] at key

end TotalToPartial

/-! ## `Par C` is an effectus in partial form (parsec 187) -/

section TotalToPartialStructure

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasTerminal C]

/-! ### The calculus of concrete partial maps -/

/-- The underlying map `X ⟶ Y + 1` of `C` of a partial map `f : X ⇸ Y`
(definitionally the identity; it exists to fix the elaboration). -/
def pval {X Y : Par C} (f : X ⟶ Y) : X.base ⟶ Y.base ⨿ ⊤_ C := f

theorem pval_inj {X Y : Par C} {f g : X ⟶ Y} (h : pval f = pval g) : f = g := h

theorem pval_comp {X Y Z : Par C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pval (f ≫ g) = pval f ≫ coprod.desc (pval g) coprod.inr := rfl

theorem pval_id (X : Par C) : pval (𝟙 X) = coprod.inl := rfl

theorem pval_hat {X Y : C} (w : X ⟶ Y) :
    pval (Par.hat w : Par.of X ⟶ Par.of Y) = w ≫ coprod.inl := rfl

theorem pval_zero (X Y : C) :
    pval (Par.zero X Y : Par.of X ⟶ Par.of Y) = terminal.from X ≫ coprod.inr := rfl

theorem pval_pproj₁ (X Y : C) :
    pval (Par.pproj₁ X Y) = coprod.desc coprod.inl (terminal.from Y ≫ coprod.inr) := rfl

theorem pval_pproj₂ (X Y : C) :
    pval (Par.pproj₂ X Y) = coprod.desc (terminal.from X ≫ coprod.inr) coprod.inl := rfl

theorem pval_map {X Y X' Y' : C} (u : Par.of X ⟶ Par.of X') (w : Par.of Y ⟶ Par.of Y') :
    pval (Par.map u w)
      = coprod.desc (pval u ≫ coprod.map coprod.inl (𝟙 (⊤_ C)))
          (pval w ≫ coprod.map coprod.inr (𝟙 (⊤_ C))) := rfl

theorem pval_one (X : C) : pval (Par.one X) = terminal.from X ≫ coprod.inl := rfl

/-- `!` out of `1` is the identity (a copy of `terminal_from_self` outside the
`EffectusTotalForm` section). -/
theorem par_terminal_self : terminal.from (⊤_ C) = 𝟙 (⊤_ C) :=
  terminalIsTerminal.hom_ext _ _

attribute [local simp] pval_comp pval_id pval_hat pval_zero pval_pproj₁ pval_pproj₂
  pval_map pval_one par_terminal_self

/-- `ŵ ⊙ g = w ∘ g`. -/
theorem par_hat_comp {X Y : C} {Z : Par C} (w : X ⟶ Y) (g : Par.of Y ⟶ Z) :
    pval ((Par.hat w : Par.of X ⟶ Par.of Y) ≫ g) = w ≫ pval g := by
  simp [coprod.inl_desc, Category.assoc]

theorem par_hat_hat {X Y Z : C} (w : X ⟶ Y) (w' : Y ⟶ Z) :
    (Par.hat w : Par.of X ⟶ Par.of Y) ≫ Par.hat w' = Par.hat (w ≫ w') := by
  refine pval_inj ?_
  simp [coprod.inl_desc, Category.assoc]

theorem par_hat_id (X : C) : Par.hat (𝟙 X) = 𝟙 (Par.of X) := by
  refine pval_inj ?_
  simp

theorem par_zero_comp {X : Par C} {Y : C} {Z : Par C} (g : Par.of Y ⟶ Z) :
    (Par.zero X.base Y : X ⟶ Par.of Y) ≫ g = Par.zero X.base Z.base := by
  refine pval_inj ?_
  simp [coprod.inr_desc, Category.assoc]

theorem par_comp_zero {X Y : Par C} {Z : C} (f : X ⟶ Y) :
    f ≫ (Par.zero Y.base Z : Y ⟶ Par.of Z) = Par.zero X.base Z := by
  refine pval_inj ?_
  have e : coprod.desc (terminal.from Y.base ≫ (coprod.inr : (⊤_ C) ⟶ Z ⨿ ⊤_ C))
        (coprod.inr : (⊤_ C) ⟶ Z ⨿ ⊤_ C)
      = terminal.from (Y.base ⨿ ⊤_ C) ≫ (coprod.inr : (⊤_ C) ⟶ Z ⨿ ⊤_ C) := by
    refine coprod.hom_ext ?_ ?_ <;>
      simp [coprod.inl_desc, coprod.inr_desc, ← Category.assoc]
  simp only [pval_comp, pval_zero, e, ← Category.assoc]
  simp

theorem par_hat_pproj₁_inl (X Y : C) :
    (Par.hat (coprod.inl : X ⟶ X ⨿ Y) : Par.of X ⟶ Par.of (X ⨿ Y)) ≫ Par.pproj₁ X Y
      = 𝟙 (Par.of X) := by
  refine pval_inj ?_
  simp [coprod.inl_desc, Category.assoc]

theorem par_hat_pproj₁_inr (X Y : C) :
    (Par.hat (coprod.inr : Y ⟶ X ⨿ Y) : Par.of Y ⟶ Par.of (X ⨿ Y)) ≫ Par.pproj₁ X Y
      = Par.zero Y X := by
  refine pval_inj ?_
  simp [coprod.inl_desc, coprod.inr_desc, Category.assoc]

theorem par_hat_pproj₂_inl (X Y : C) :
    (Par.hat (coprod.inl : X ⟶ X ⨿ Y) : Par.of X ⟶ Par.of (X ⨿ Y)) ≫ Par.pproj₂ X Y
      = Par.zero X Y := by
  refine pval_inj ?_
  simp [coprod.inl_desc, Category.assoc]

theorem par_hat_pproj₂_inr (X Y : C) :
    (Par.hat (coprod.inr : Y ⟶ X ⨿ Y) : Par.of Y ⟶ Par.of (X ⨿ Y)) ≫ Par.pproj₂ X Y
      = 𝟙 (Par.of Y) := by
  refine pval_inj ?_
  simp [coprod.inl_desc, coprod.inr_desc, Category.assoc]

/-- Maps out of `Par.of (X ⨿ Y)` are determined by their restrictions along
the two (hatted) coprojections. -/
theorem par_hom_ext {X Y : C} {Z : Par C} {f g : Par.of (X ⨿ Y) ⟶ Z}
    (h₁ : (Par.hat (coprod.inl : X ⟶ X ⨿ Y) : Par.of X ⟶ Par.of (X ⨿ Y)) ≫ f
      = (Par.hat (coprod.inl : X ⟶ X ⨿ Y) : Par.of X ⟶ Par.of (X ⨿ Y)) ≫ g)
    (h₂ : (Par.hat (coprod.inr : Y ⟶ X ⨿ Y) : Par.of Y ⟶ Par.of (X ⨿ Y)) ≫ f
      = (Par.hat (coprod.inr : Y ⟶ X ⨿ Y) : Par.of Y ⟶ Par.of (X ⨿ Y)) ≫ g) :
    f = g := by
  refine pval_inj (coprod.hom_ext ?_ ?_)
  · have e := congrArg pval h₁
    rwa [par_hat_comp, par_hat_comp] at e
  · have e := congrArg pval h₂
    rwa [par_hat_comp, par_hat_comp] at e

theorem par_inl_map {X Y X' Y' : C} (u : Par.of X ⟶ Par.of X') (w : Par.of Y ⟶ Par.of Y') :
    (Par.hat (coprod.inl : X ⟶ X ⨿ Y) : Par.of X ⟶ Par.of (X ⨿ Y)) ≫ Par.map u w
      = u ≫ Par.hat (coprod.inl : X' ⟶ X' ⨿ Y') := by
  refine pval_inj ?_
  rw [par_hat_comp, pval_map, coprod.inl_desc, pval_comp, pval_hat]
  congr 1
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_map, coprod.inl_desc]
  · rw [coprod.inr_map, coprod.inr_desc, Category.id_comp]

theorem par_inr_map {X Y X' Y' : C} (u : Par.of X ⟶ Par.of X') (w : Par.of Y ⟶ Par.of Y') :
    (Par.hat (coprod.inr : Y ⟶ X ⨿ Y) : Par.of Y ⟶ Par.of (X ⨿ Y)) ≫ Par.map u w
      = w ≫ Par.hat (coprod.inr : Y' ⟶ X' ⨿ Y') := by
  refine pval_inj ?_
  rw [par_hat_comp, pval_map, coprod.inr_desc, pval_comp, pval_hat]
  congr 1
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_map, coprod.inl_desc]
  · rw [coprod.inr_map, coprod.inr_desc, Category.id_comp]

theorem par_map_pproj₁ {X Y X' Y' : C} (u : Par.of X ⟶ Par.of X') (w : Par.of Y ⟶ Par.of Y') :
    Par.map u w ≫ Par.pproj₁ X' Y' = Par.pproj₁ X Y ≫ u := by
  refine par_hom_ext ?_ ?_
  · rw [← Category.assoc, ← Category.assoc, par_inl_map, par_hat_pproj₁_inl,
      Category.assoc, par_hat_pproj₁_inl, Category.comp_id, Category.id_comp]
  · rw [← Category.assoc, ← Category.assoc, par_inr_map, par_hat_pproj₁_inr,
      Category.assoc, par_hat_pproj₁_inr, par_comp_zero, par_zero_comp]

theorem par_map_pproj₂ {X Y X' Y' : C} (u : Par.of X ⟶ Par.of X') (w : Par.of Y ⟶ Par.of Y') :
    Par.map u w ≫ Par.pproj₂ X' Y' = Par.pproj₂ X Y ≫ w := by
  refine par_hom_ext ?_ ?_
  · rw [← Category.assoc, ← Category.assoc, par_inl_map, par_hat_pproj₂_inl,
      Category.assoc, par_hat_pproj₂_inl, par_comp_zero, par_zero_comp]
  · rw [← Category.assoc, ← Category.assoc, par_inr_map, par_hat_pproj₂_inr,
      Category.assoc, par_hat_pproj₂_inr, Category.comp_id, Category.id_comp]

theorem par_one_eq (X : C) : Par.one X = Par.hat (terminal.from X) := rfl


/-! ### 187III–IV: the PCM-enrichment of `Par C` -/

section ParPCM

variable [EffectusTotalForm C]

/-- The codiagonal `∇ = [id, id] : Y + Y ⇸ Y` of `Par C`. -/
noncomputable def parNabla (Y : C) : Par.of (Y ⨿ Y) ⟶ Par.of Y :=
  Par.hat (coprod.desc (𝟙 Y) (𝟙 Y))

/-- **187III**: `b` is a **bound** for `f ⊥ g`. -/
def ParBound {X Y : Par C} (f g : X ⟶ Y) (b : X ⟶ Par.of (Y.base ⨿ Y.base)) : Prop :=
  b ≫ Par.pproj₁ Y.base Y.base = f ∧ b ≫ Par.pproj₂ Y.base Y.base = g

/-- **186X**: a bound is unique if it exists. -/
theorem parBound_unique {X Y : Par C} {f g : X ⟶ Y}
    {b b' : X ⟶ Par.of (Y.base ⨿ Y.base)}
    (hb : ParBound f g b) (hb' : ParBound f g b') : b = b' :=
  pproj_joint_monicity Y.base Y.base b b'
    (hb.1.trans hb'.1.symm) (hb.2.trans hb'.2.symm)

/-! the identities of `∇`, `swap` and `▷ᵢ` used in 187III -/

theorem par_swap_pproj₁ (Y : C) :
    (Par.hat (coprod.desc (coprod.inr : Y ⟶ Y ⨿ Y) coprod.inl) :
        Par.of (Y ⨿ Y) ⟶ Par.of (Y ⨿ Y)) ≫ Par.pproj₁ Y Y = Par.pproj₂ Y Y := by
  refine par_hom_ext ?_ ?_
  · rw [← Category.assoc, par_hat_hat, coprod.inl_desc, par_hat_pproj₁_inr,
      par_hat_pproj₂_inl]
  · rw [← Category.assoc, par_hat_hat, coprod.inr_desc, par_hat_pproj₁_inl,
      par_hat_pproj₂_inr]

theorem par_swap_pproj₂ (Y : C) :
    (Par.hat (coprod.desc (coprod.inr : Y ⟶ Y ⨿ Y) coprod.inl) :
        Par.of (Y ⨿ Y) ⟶ Par.of (Y ⨿ Y)) ≫ Par.pproj₂ Y Y = Par.pproj₁ Y Y := by
  refine par_hom_ext ?_ ?_
  · rw [← Category.assoc, par_hat_hat, coprod.inl_desc, par_hat_pproj₂_inr,
      par_hat_pproj₁_inl]
  · rw [← Category.assoc, par_hat_hat, coprod.inr_desc, par_hat_pproj₂_inl,
      par_hat_pproj₁_inr]

theorem par_swap_nabla (Y : C) :
    (Par.hat (coprod.desc (coprod.inr : Y ⟶ Y ⨿ Y) coprod.inl) :
        Par.of (Y ⨿ Y) ⟶ Par.of (Y ⨿ Y)) ≫ parNabla Y = parNabla Y := by
  rw [parNabla, par_hat_hat]
  congr 1
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc]
  · rw [← Category.assoc, coprod.inr_desc, coprod.inl_desc, coprod.inr_desc]

theorem par_inl_nabla (Y : C) :
    (Par.hat (coprod.inl : Y ⟶ Y ⨿ Y) : Par.of Y ⟶ Par.of (Y ⨿ Y)) ≫ parNabla Y
      = 𝟙 (Par.of Y) := by
  rw [parNabla, par_hat_hat, coprod.inl_desc, par_hat_id]

theorem par_inr_nabla (Y : C) :
    (Par.hat (coprod.inr : Y ⟶ Y ⨿ Y) : Par.of Y ⟶ Par.of (Y ⨿ Y)) ≫ parNabla Y
      = 𝟙 (Par.of Y) := by
  rw [parNabla, par_hat_hat, coprod.inr_desc, par_hat_id]

theorem par_map_nabla {Y Z : C} (k : Par.of Y ⟶ Par.of Z) :
    Par.map k k ≫ parNabla Z = parNabla Y ≫ k := by
  refine par_hom_ext ?_ ?_
  · rw [← Category.assoc, ← Category.assoc, par_inl_map, par_inl_nabla,
      Category.assoc, par_inl_nabla, Category.comp_id, Category.id_comp]
  · rw [← Category.assoc, ← Category.assoc, par_inr_map, par_inr_nabla,
      Category.assoc, par_inr_nabla, Category.comp_id, Category.id_comp]

/-! `e = [id, κ₂] : (Y+Y)+Y ⇸ Y+Y`, the map of 187III -/

theorem par_e_pproj₁ (Y : C) :
    (Par.hat (coprod.desc (𝟙 (Y ⨿ Y)) (coprod.inr : Y ⟶ Y ⨿ Y)) :
        Par.of ((Y ⨿ Y) ⨿ Y) ⟶ Par.of (Y ⨿ Y)) ≫ Par.pproj₁ Y Y
      = Par.pproj₁ (Y ⨿ Y) Y ≫ Par.pproj₁ Y Y := by
  refine par_hom_ext ?_ ?_
  · rw [← Category.assoc, par_hat_hat, coprod.inl_desc, par_hat_id, Category.id_comp,
      ← Category.assoc, par_hat_pproj₁_inl, Category.id_comp]
  · rw [← Category.assoc, par_hat_hat, coprod.inr_desc, par_hat_pproj₁_inr,
      ← Category.assoc, par_hat_pproj₁_inr, par_zero_comp]

theorem par_e_pproj₂ (Y : C) :
    (Par.hat (coprod.desc (𝟙 (Y ⨿ Y)) (coprod.inr : Y ⟶ Y ⨿ Y)) :
        Par.of ((Y ⨿ Y) ⨿ Y) ⟶ Par.of (Y ⨿ Y)) ≫ Par.pproj₂ Y Y
      = Par.map (Par.pproj₂ Y Y) (𝟙 (Par.of Y)) ≫ parNabla Y := by
  refine par_hom_ext ?_ ?_
  · rw [← Category.assoc, par_hat_hat, coprod.inl_desc, par_hat_id, Category.id_comp,
      ← Category.assoc, par_inl_map, Category.assoc, par_inl_nabla, Category.comp_id]
  · rw [← Category.assoc, par_hat_hat, coprod.inr_desc, par_hat_pproj₂_inr,
      ← Category.assoc, par_inr_map, Category.assoc, par_inr_nabla, Category.comp_id]

theorem par_e_nabla (Y : C) :
    (Par.hat (coprod.desc (𝟙 (Y ⨿ Y)) (coprod.inr : Y ⟶ Y ⨿ Y)) :
        Par.of ((Y ⨿ Y) ⨿ Y) ⟶ Par.of (Y ⨿ Y)) ≫ parNabla Y
      = Par.map (parNabla Y) (𝟙 (Par.of Y)) ≫ parNabla Y := by
  refine par_hom_ext ?_ ?_
  · rw [← Category.assoc, par_hat_hat, coprod.inl_desc, par_hat_id, Category.id_comp,
      ← Category.assoc, par_inl_map, Category.assoc, par_inl_nabla, Category.comp_id]
  · rw [← Category.assoc, par_hat_hat, coprod.inr_desc, par_inr_nabla,
      ← Category.assoc, par_inr_map, Category.assoc, par_inr_nabla, Category.comp_id]

/-- **187III**: `f ⊥ g` in `Par C` iff a bound exists. -/
def ParPerp {X Y : Par C} (f g : X ⟶ Y) : Prop := ∃ b, ParBound f g b

/-- **187III**: `f ⋁ g = ∇ ⊙ b` for the (unique) bound `b`. -/
noncomputable def parOvee {X Y : Par C} (f g : X ⟶ Y) (h : ParPerp f g) : X ⟶ Y :=
  h.choose ≫ parNabla Y.base

theorem parOvee_eq {X Y : Par C} {f g : X ⟶ Y} (h : ParPerp f g)
    {b : X ⟶ Par.of (Y.base ⨿ Y.base)} (hb : ParBound f g b) :
    parOvee f g h = b ≫ parNabla Y.base := by
  rw [parOvee, parBound_unique h.choose_spec hb]

theorem parPerp_comm {X Y : Par C} {f g : X ⟶ Y} (h : ParPerp f g) : ParPerp g f :=
  ⟨h.choose ≫ Par.hat (coprod.desc coprod.inr coprod.inl),
    ⟨by rw [Category.assoc, par_swap_pproj₁]; exact h.choose_spec.2,
     by rw [Category.assoc, par_swap_pproj₂]; exact h.choose_spec.1⟩⟩

/-- **187III**, partial associativity, in one construction. -/
theorem par_assoc_data {X Y : Par C} {f g k : X ⟶ Y} (hab : ParPerp f g)
    (h : ParPerp (parOvee f g hab) k) :
    ∃ (hgk : ParPerp g k) (h' : ParPerp f (parOvee g k hgk)),
      parOvee (parOvee f g hab) k h = parOvee f (parOvee g k hgk) h' := by
  obtain ⟨b, hb⟩ := id hab
  obtain ⟨c, hc⟩ := id h
  have hfg : parOvee f g hab = b ≫ parNabla Y.base := parOvee_eq hab hb
  have hsq := par_pullbacks_right (X := Y.base) (coprod.desc (𝟙 Y.base) (𝟙 Y.base))
  have hcond : c ≫ Par.pproj₁ Y.base Y.base
      = b ≫ Par.hat (coprod.desc (𝟙 Y.base) (𝟙 Y.base)) := by
    rw [hc.1, hfg]; rfl
  set d := hsq.lift c b hcond with hddef
  have hd₁ : d ≫ Par.map (parNabla Y.base) (𝟙 (Par.of Y.base)) = c := hsq.lift_fst c b hcond
  have hd₂ : d ≫ Par.pproj₁ (Y.base ⨿ Y.base) Y.base = b := hsq.lift_snd c b hcond
  have hd₂' : d ≫ Par.pproj₂ (Y.base ⨿ Y.base) Y.base = k := by
    have e : d ≫ Par.pproj₂ (Y.base ⨿ Y.base) Y.base
        = (d ≫ Par.map (parNabla Y.base)
            (𝟙 (Par.of Y.base))) ≫ Par.pproj₂ Y.base Y.base := by
      rw [Category.assoc, par_map_pproj₂, Category.comp_id]
    rw [e, hd₁, hc.2]
  have hbgk : ParBound g k (d ≫ Par.map (Par.pproj₂ Y.base Y.base) (𝟙 (Par.of Y.base))) := by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, par_map_pproj₁, ← Category.assoc, hd₂, hb.2]
    · rw [Category.assoc, par_map_pproj₂, Category.comp_id, hd₂']
  refine ⟨⟨_, hbgk⟩, ?_⟩
  have hgk : parOvee g k ⟨_, hbgk⟩
      = (d ≫ Par.map (Par.pproj₂ Y.base Y.base) (𝟙 (Par.of Y.base))) ≫ parNabla Y.base :=
    parOvee_eq _ hbgk
  have hbf : ParBound f (parOvee g k ⟨_, hbgk⟩)
      (d ≫ Par.hat (coprod.desc (𝟙 (Y.base ⨿ Y.base)) coprod.inr)) := by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, par_e_pproj₁, ← Category.assoc, hd₂, hb.1]
    · rw [Category.assoc, par_e_pproj₂, hgk, Category.assoc]
  refine ⟨⟨_, hbf⟩, ?_⟩
  have e1 : parOvee (parOvee f g hab) k h = c ≫ parNabla Y.base := parOvee_eq h hc
  have e2 : parOvee f (parOvee g k ⟨_, hbgk⟩) ⟨_, hbf⟩
      = (d ≫ Par.hat (coprod.desc (𝟙 (Y.base ⨿ Y.base)) coprod.inr)) ≫ parNabla Y.base :=
    parOvee_eq _ hbf
  rw [e1, e2, Category.assoc, par_e_nabla, ← Category.assoc, hd₁]


theorem par_zero_bound {X Y : Par C} (a : X ⟶ Y) :
    ParBound (Par.zero X.base Y.base) a (a ≫ Par.hat coprod.inr) :=
  ⟨by rw [Category.assoc, par_hat_pproj₁_inr, par_comp_zero],
   by rw [Category.assoc, par_hat_pproj₂_inr, Category.comp_id]⟩

/-- **187IV**: postcomposition preserves `⊥` and `⋁`. -/
theorem par_comp_ovee {X Y Z : Par C} {f g : X ⟶ Y} (h : ParPerp f g) (k : Y ⟶ Z) :
    ∃ h' : ParPerp (f ≫ k) (g ≫ k), parOvee f g h ≫ k = parOvee (f ≫ k) (g ≫ k) h' := by
  have hb : ParBound (f ≫ k) (g ≫ k) (h.choose ≫ Par.map k k) :=
    ⟨by rw [Category.assoc, par_map_pproj₁, ← Category.assoc, h.choose_spec.1],
     by rw [Category.assoc, par_map_pproj₂, ← Category.assoc, h.choose_spec.2]⟩
  refine ⟨⟨_, hb⟩, ?_⟩
  rw [parOvee_eq h h.choose_spec, parOvee_eq (⟨_, hb⟩ : ParPerp (f ≫ k) (g ≫ k)) hb]
  simp only [Category.assoc]
  rw [par_map_nabla]

/-- **187IV**: precomposition preserves `⊥` and `⋁`. -/
theorem par_ovee_comp {W X Y : Par C} {f g : X ⟶ Y} (h : ParPerp f g) (k : W ⟶ X) :
    ∃ h' : ParPerp (k ≫ f) (k ≫ g), k ≫ parOvee f g h = parOvee (k ≫ f) (k ≫ g) h' := by
  have hb : ParBound (k ≫ f) (k ≫ g) (k ≫ h.choose) :=
    ⟨by rw [Category.assoc, h.choose_spec.1], by rw [Category.assoc, h.choose_spec.2]⟩
  refine ⟨⟨_, hb⟩, ?_⟩
  rw [parOvee_eq h h.choose_spec, parOvee_eq (⟨_, hb⟩ : ParPerp (k ≫ f) (k ≫ g)) hb]
  simp only [Category.assoc]

/-- **187III–IV** (`eff-total-to-partial`, eff.tex:1719): the hom-sets of
`Par C` are PCMs. -/
noncomputable instance parHomPCM (X Y : Par C) : PCM (X ⟶ Y) where
  zero := Par.zero X.base Y.base
  Perp := ParPerp
  ovee := parOvee
  perp_comm := parPerp_comm
  ovee_comm := fun {a b} h => by
    have hb := h.choose_spec
    rw [parOvee_eq h hb,
      parOvee_eq (parPerp_comm h) (b := h.choose ≫ Par.hat (coprod.desc coprod.inr coprod.inl))
        ⟨by rw [Category.assoc, par_swap_pproj₁]; exact hb.2,
         by rw [Category.assoc, par_swap_pproj₂]; exact hb.1⟩,
      Category.assoc, par_swap_nabla]
  perp_of_ovee_perp := fun hab h => (par_assoc_data hab h).choose
  perp_ovee_of_ovee_perp := fun hab h => (par_assoc_data hab h).choose_spec.choose
  ovee_assoc := fun hab h => (par_assoc_data hab h).choose_spec.choose_spec
  zero_perp := fun a => ⟨_, par_zero_bound a⟩
  zero_ovee := fun a =>
    (parOvee_eq (⟨_, par_zero_bound a⟩ : ParPerp (Par.zero X.base Y.base) a)
        (par_zero_bound a)).trans
      (by rw [Category.assoc, par_inr_nabla, Category.comp_id])

theorem par_zero_eq' (X Y : Par C) : (0 : X ⟶ Y) = Par.zero X.base Y.base := rfl

theorem par_perp_iff {X Y : Par C} {f g : X ⟶ Y} :
    Perp f g ↔ ∃ b, ParBound f g b := Iff.rfl

/-! ### `Par C` has finite coproducts -/

noncomputable def parCoprodCofan (X Y : Par C) : BinaryCofan X Y :=
  BinaryCofan.mk
    (Par.hat (coprod.inl : X.base ⟶ X.base ⨿ Y.base) : X ⟶ Par.of (X.base ⨿ Y.base))
    (Par.hat (coprod.inr : Y.base ⟶ X.base ⨿ Y.base) : Y ⟶ Par.of (X.base ⨿ Y.base))

noncomputable def parCoprodIsColimit (X Y : Par C) : IsColimit (parCoprodCofan X Y) :=
  (par_c_coprod X.base Y.base).some

theorem parHasFiniteCoproducts : HasFiniteCoproducts (Par C) :=
  letI : HasInitial (Par C) := par_c_initial.some.hasInitial
  letI : ∀ X Y : Par C, HasColimit (pair X Y) := fun X Y =>
    HasColimit.mk ⟨parCoprodCofan X Y, parCoprodIsColimit X Y⟩
  letI : HasBinaryCoproducts (Par C) := hasBinaryCoproducts_of_hasColimit_pair (Par C)
  hasFiniteCoproducts_of_has_binary_and_initial

section ParBridge

variable [HasFiniteCoproducts (Par C)]

noncomputable def parCoprodIso (X Y : Par C) :
    (X ⨿ Y : Par C) ≅ Par.of (X.base ⨿ Y.base) :=
  IsColimit.coconePointUniqueUpToIso (coprodIsCoprod X Y) (parCoprodIsColimit X Y)

theorem parCoprodIso_inl (X Y : Par C) :
    (coprod.inl : X ⟶ X ⨿ Y) ≫ (parCoprodIso X Y).hom
      = (Par.hat (coprod.inl : X.base ⟶ X.base ⨿ Y.base) : X ⟶ Par.of (X.base ⨿ Y.base)) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod X Y)
    (parCoprodIsColimit X Y) (Discrete.mk WalkingPair.left)

theorem parCoprodIso_inr (X Y : Par C) :
    (coprod.inr : Y ⟶ X ⨿ Y) ≫ (parCoprodIso X Y).hom
      = (Par.hat (coprod.inr : Y.base ⟶ X.base ⨿ Y.base) : Y ⟶ Par.of (X.base ⨿ Y.base)) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod X Y)
    (parCoprodIsColimit X Y) (Discrete.mk WalkingPair.right)

theorem par_pproj₁_eq (X Y : Par C) :
    (pproj₁ X Y : (X ⨿ Y : Par C) ⟶ X)
      = (parCoprodIso X Y).hom ≫ Par.pproj₁ X.base Y.base := by
  refine coprod.hom_ext ?_ ?_
  · rw [pproj₁, coprod.inl_desc, ← Category.assoc, parCoprodIso_inl, par_hat_pproj₁_inl]
  · rw [pproj₁, coprod.inr_desc, ← Category.assoc, parCoprodIso_inr, par_hat_pproj₁_inr]
    rfl

theorem par_pproj₂_eq (X Y : Par C) :
    (pproj₂ X Y : (X ⨿ Y : Par C) ⟶ Y)
      = (parCoprodIso X Y).hom ≫ Par.pproj₂ X.base Y.base := by
  refine coprod.hom_ext ?_ ?_
  · rw [pproj₂, coprod.inl_desc, ← Category.assoc, parCoprodIso_inl, par_hat_pproj₂_inl]
    rfl
  · rw [pproj₂, coprod.inr_desc, ← Category.assoc, parCoprodIso_inr, par_hat_pproj₂_inr]

/-- **187V**: `Par C` is a finPAC. -/
noncomputable instance parFinPAC : FinPAC (Par C) where
  comp_ovee := fun h k => par_comp_ovee h k
  ovee_comp := fun h k => par_ovee_comp h k
  comp_zero := fun f => par_comp_zero f
  zero_comp := fun f => par_zero_comp f
  compatible_sum := fun {X Y} b =>
    ⟨b ≫ (parCoprodIso Y Y).hom,
      ⟨by rw [par_pproj₁_eq, ← Category.assoc], by rw [par_pproj₂_eq, ← Category.assoc]⟩⟩
  untying := fun {X Y f g} h =>
    ⟨h.choose ≫ Par.map (coprod.inl : Y ⟶ Y ⨿ Y) (coprod.inr : Y ⟶ Y ⨿ Y),
      ⟨by rw [Category.assoc, par_map_pproj₁, ← Category.assoc, h.choose_spec.1],
       by rw [Category.assoc, par_map_pproj₂, ← Category.assoc, h.choose_spec.2]⟩⟩


end ParBridge

/-! ### 187VI: the effect algebra of predicates -/

noncomputable def parSwapTop : (⊤_ C) ⨿ (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C) :=
  coprod.desc (W := ((⊤_ C) ⨿ (⊤_ C) : C)) (X := (⊤_ C : C)) (Y := (⊤_ C : C))
    coprod.inr coprod.inl

/-- **187VI**: the orthosupplement `p^⊥ = [κ₂,κ₁] ∘ p` of a predicate. -/
noncomputable def parOrthAux {Z : C} (q : Z ⟶ (⊤_ C) ⨿ (⊤_ C)) : Z ⟶ (⊤_ C) ⨿ (⊤_ C) :=
  q ≫ parSwapTop

/-- **187VI**: the orthosupplement `p^⊥ = [κ₂,κ₁] ∘ p` of a predicate. -/
noncomputable def parOrth {X : Par C} (p : X ⟶ Par.of (⊤_ C)) : X ⟶ Par.of (⊤_ C) :=
  parOrthAux (pval p)

theorem pval_parOrth {X : Par C} (p : X ⟶ Par.of (⊤_ C)) :
    pval (parOrth p) = pval p ≫ parSwapTop := rfl

theorem parSwapTop_eq :
    (parSwapTop : (⊤_ C) ⨿ (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
      = coprod.desc (W := ((⊤_ C) ⨿ (⊤_ C) : C)) (X := (⊤_ C : C)) (Y := (⊤_ C : C))
          coprod.inr coprod.inl := rfl

theorem par_nabla_top : parNabla (⊤_ C) = Par.one ((⊤_ C) ⨿ (⊤_ C)) := by
  rw [parNabla, par_one_eq]
  congr 1
  exact terminalIsTerminal.hom_ext _ _

theorem par_hat_pval_pproj₁ {X : Par C} (p : X ⟶ Par.of (⊤_ C)) :
    (Par.hat (pval p) : X ⟶ Par.of ((⊤_ C) ⨿ ⊤_ C)) ≫ Par.pproj₁ (⊤_ C) (⊤_ C) = p := by
  refine pval_inj ?_
  rw [par_hat_comp, pval_pproj₁, par_terminal_self, Category.id_comp,
    coprod.desc_inl_inr, Category.comp_id]

theorem par_hat_pval_pproj₂ {X : Par C} (p : X ⟶ Par.of (⊤_ C)) :
    (Par.hat (pval p) : X ⟶ Par.of ((⊤_ C) ⨿ ⊤_ C)) ≫ Par.pproj₂ (⊤_ C) (⊤_ C)
      = parOrth p := by
  refine pval_inj ?_
  rw [par_hat_comp, pval_pproj₂, par_terminal_self, Category.id_comp, pval_parOrth,
    parSwapTop_eq]

theorem par_hat_pval_nabla {X : Par C} (p : X ⟶ Par.of (⊤_ C)) :
    (Par.hat (pval p) : X ⟶ Par.of ((⊤_ C) ⨿ ⊤_ C)) ≫ parNabla (⊤_ C)
      = Par.one X.base := by
  refine pval_inj ?_
  rw [par_hat_comp, parNabla, pval_hat, pval_one, ← Category.assoc]
  congr 1
  exact terminalIsTerminal.hom_ext _ _

theorem par_perp_orth {X : Par C} (p : X ⟶ Par.of (⊤_ C)) : ParPerp p (parOrth p) :=
  ⟨Par.hat (pval p), par_hat_pval_pproj₁ p, par_hat_pval_pproj₂ p⟩

theorem par_ovee_orth {X : Par C} (p : X ⟶ Par.of (⊤_ C)) :
    parOvee p (parOrth p) (par_perp_orth p) = Par.one X.base := by
  rw [parOvee_eq (par_perp_orth p) ⟨par_hat_pval_pproj₁ p, par_hat_pval_pproj₂ p⟩,
    par_hat_pval_nabla]

/-- **187VI**: `p^⊥` is the unique orthosupplement. -/
theorem par_orth_unique {X : Par C} {p q : X ⟶ Par.of (⊤_ C)} (h : ParPerp p q)
    (he : parOvee p q h = Par.one X.base) : q = parOrth p := by
  obtain ⟨b, hb₁, hb₂⟩ := id h
  have hbe : b ≫ Par.one ((⊤_ C) ⨿ (⊤_ C)) = Par.one X.base := by
    rw [← par_nabla_top, ← parOvee_eq h ⟨hb₁, hb₂⟩]
    exact he
  obtain ⟨c, hc, -⟩ := pardp_1 b hbe
  have hp : pval p = c := by
    rw [← hb₁, hc]
    refine (par_hat_comp c (Par.pproj₁ (⊤_ C) (⊤_ C))).trans ?_
    rw [pval_pproj₁, par_terminal_self, Category.id_comp, coprod.desc_inl_inr,
      Category.comp_id]
  refine pval_inj ?_
  rw [← hb₂, hc, par_hat_comp, pval_pproj₂, par_terminal_self, Category.id_comp,
    pval_parOrth, parSwapTop_eq, hp]

/-- **187VI**, zero–one axiom.  (Derived from the uniqueness of the
orthosupplement together with **186VIII.2**, rather than from the pullback
square of the thesis' diagram.) -/
theorem par_eq_zero_of_perp_one {X : Par C} {p : X ⟶ Par.of (⊤_ C)}
    (h : ParPerp p (Par.one X.base)) : p = Par.zero X.base (⊤_ C) := by
  have h' : ParPerp (Par.one X.base) p := parPerp_comm h
  have hso : ParPerp (parOvee (Par.one X.base) p h')
      (parOrth (parOvee (Par.one X.base) p h')) :=
    par_perp_orth _
  have hpt : ParPerp p (parOrth (parOvee (Par.one X.base) p h')) :=
    PCM.perp_of_ovee_perp (c := parOrth (parOvee (Par.one X.base) p h')) h' hso
  have ht1 : ParPerp (Par.one X.base)
      (parOvee p (parOrth (parOvee (Par.one X.base) p h')) hpt) :=
    PCM.perp_ovee_of_ovee_perp (c := parOrth (parOvee (Par.one X.base) p h')) h' hso
  have hassoc := PCM.ovee_assoc (c := parOrth (parOvee (Par.one X.base) p h')) h' hso
  have hone : parOvee (Par.one X.base)
      (parOvee p (parOrth (parOvee (Par.one X.base) p h')) hpt) ht1 = Par.one X.base :=
    hassoc.symm.trans (par_ovee_orth (parOvee (Par.one X.base) p h'))
  have ht0 : parOvee p (parOrth (parOvee (Par.one X.base) p h')) hpt
      = parOrth (Par.one X.base) := par_orth_unique ht1 hone
  have horth_one : parOrth (Par.one X.base) = Par.zero X.base (⊤_ C) := by
    refine pval_inj ?_
    rw [pval_parOrth, parSwapTop_eq, pval_one, pval_zero, Category.assoc, coprod.inl_desc]
  obtain ⟨d, hd₁, hd₂⟩ := id hpt
  have hd : d ≫ Par.one ((⊤_ C) ⨿ (⊤_ C)) = Par.zero X.base (⊤_ C) := by
    rw [← par_nabla_top, ← parOvee_eq hpt ⟨hd₁, hd₂⟩, ht0, horth_one]
  have hd0 : d = Par.zero X.base ((⊤_ C) ⨿ ⊤_ C) := pardp_2 d hd
  rw [← hd₁, hd0, par_zero_comp]


/-! ### local copies of the two `private` helpers of `section TotalToPartial` -/

/-! ### 187VII: the last two axioms -/

/-- **187VII**: if `1 ∘ f ⊥ 1 ∘ g` then `f ⊥ g`. -/
theorem par_perp_of_one_perp {X Y : Par C} {f g : X ⟶ Y}
    (h : ParPerp (f ≫ Par.one Y.base) (g ≫ Par.one Y.base)) : ParPerp f g := by
  obtain ⟨b, hb₁, hb₂⟩ := h
  have hsq1 := par_pullbacks_right (X := ⊤_ C) (terminal.from Y.base)
  have hc1 : b ≫ Par.pproj₁ (⊤_ C) (⊤_ C) = f ≫ Par.hat (terminal.from Y.base) := hb₁
  have hcf : (hsq1.lift b f hc1) ≫ Par.pproj₁ Y.base (⊤_ C) = f := hsq1.lift_snd b f hc1
  have hcb : (hsq1.lift b f hc1) ≫ Par.map (Par.hat (terminal.from Y.base))
      (𝟙 (Par.of (⊤_ C))) = b := hsq1.lift_fst b f hc1
  have hsq2 := par_pullbacks_right₂ (X := Y.base) (terminal.from Y.base)
  have hc2 : (hsq1.lift b f hc1) ≫ Par.pproj₂ Y.base (⊤_ C)
      = g ≫ Par.hat (terminal.from Y.base) := by
    have e : (hsq1.lift b f hc1) ≫ Par.pproj₂ Y.base (⊤_ C)
        = ((hsq1.lift b f hc1) ≫ Par.map (Par.hat (terminal.from Y.base))
            (𝟙 (Par.of (⊤_ C)))) ≫ Par.pproj₂ (⊤_ C) (⊤_ C) := by
      rw [Category.assoc, par_map_pproj₂, Category.comp_id]
    rw [e, hcb]
    exact hb₂
  refine ⟨hsq2.lift (hsq1.lift b f hc1) g hc2, ?_, ?_⟩
  · have e : (hsq2.lift (hsq1.lift b f hc1) g hc2) ≫ Par.pproj₁ Y.base Y.base
        = ((hsq2.lift (hsq1.lift b f hc1) g hc2) ≫ Par.map (𝟙 (Par.of Y.base))
            (Par.hat (terminal.from Y.base))) ≫ Par.pproj₁ Y.base (⊤_ C) := by
      rw [Category.assoc, par_map_pproj₁, Category.comp_id]
    rw [e, hsq2.lift_fst, hcf]
  · exact hsq2.lift_snd (hsq1.lift b f hc1) g hc2

/-! ### 187I: `Par C` is an effectus in partial form -/

section ParAssemble

variable [HasFiniteCoproducts (Par C)]

/-- **187I** (`eff-total-to-partial`, eff.tex:1713, Theorem). -/
noncomputable instance parEffectusPartialForm : EffectusPartialForm (Par C) where
  I := Par.of (⊤_ C)
  one X := Par.one X.base
  orth := parOrth
  perp_orth := par_perp_orth
  ovee_orth := par_ovee_orth
  orth_unique := par_orth_unique
  eq_zero_of_perp_one := par_eq_zero_of_perp_one
  perp_of_one_perp := par_perp_of_one_perp
  eq_zero_of_one_zero := fun {_ _ f} h => pardp_2 f h

end ParAssemble

end ParPCM

end TotalToPartialStructure

/-! ## Cho's theorem, part 3: nothing is lost (parsec 188) -/

section ParTotEquiv

variable {D : Type u} [Category.{v} D] [HasFiniteCoproducts D]
  [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D] [EffectusPartialForm D]
  [HasFiniteCoproducts (Tot D)] [HasTerminal (Tot D)]

-- **181XIII**: the truth predicate on the final object of `Tot D` is an
-- isomorphism.  Made a local instance so that `inv (1 : (⊤_ (Tot D)).base ⟶ I)`
-- elaborates in the definition of the thesis's `P'` below.
attribute [local instance] truth_terminal_isIso

/-- **188III**: `▷₁ ∘ [g, κ₂] = (▷₁ ∘ g) ∘ ▷₁`. -/
theorem tot_desc_tp₁ {Y Z : Tot D} (g : Y ⟶ Z ⨿ ⊤_ (Tot D)) :
    (coprod.desc g (coprod.inr : (⊤_ (Tot D)) ⟶ Z ⨿ ⊤_ (Tot D))).1 ≫ tp₁ Z (⊤_ (Tot D))
      = tp₁ Y (⊤_ (Tot D)) ≫ (g.1 ≫ tp₁ Z (⊤_ (Tot D))) := by
  refine tot_hom_ext_base ?_ ?_
  · rw [← Category.assoc, tot_desc_inl, ← Category.assoc, tinl_tp₁, Category.id_comp]
  · rw [← Category.assoc, tot_desc_inr, tinr_tp₁, ← Category.assoc, tinr_tp₁,
      FinPAC.zero_comp]

/-- **188III** (`proof-cho-thm`, eff.tex:1943): the identity-on-objects functor
`P : Par (Tot D) ⟶ D`, `P f = ▷₁ ∘ f`. -/
noncomputable def parTotFunctor : Par (Tot D) ⥤ D where
  obj X := X.base.base
  map {X Y} f := (pval f).1 ≫ tp₁ Y.base (⊤_ (Tot D))
  map_id X := by
    show (pval (𝟙 X)).1 ≫ tp₁ X.base (⊤_ (Tot D)) = 𝟙 X.base.base
    rw [pval_id]
    exact tinl_tp₁ X.base (⊤_ (Tot D))
  map_comp {X Y Z} f g := by
    show (pval (f ≫ g)).1 ≫ tp₁ Z.base (⊤_ (Tot D))
      = ((pval f).1 ≫ tp₁ Y.base (⊤_ (Tot D))) ≫ ((pval g).1 ≫ tp₁ Z.base (⊤_ (Tot D)))
    rw [pval_comp, tot_comp_base, Category.assoc, tot_desc_tp₁, ← Category.assoc]

instance parTotFunctor_faithful : (parTotFunctor (D := D)).Faithful where
  map_injective {X Y f g} h := by
    have := truth_terminal_isIso (D := D)
    have h₁ : (pval f).1 ≫ tp₁ Y.base (⊤_ (Tot D)) = (pval g).1 ≫ tp₁ Y.base (⊤_ (Tot D)) := h
    refine pval_inj (Subtype.ext (tp_jm h₁ ?_))
    exact (cancel_mono (truth (⊤_ (Tot D)).base)).mp
      (tot_snd_coord_eq (pval f) (pval g) h₁)

/-- The second component of the thesis's inverse `P' f = ⟨f, (1 ∘ f)ᵖ⟩`
(**188III**): the orthosupplement `(1 ∘ f)ᵖ`, read as a map into
`(⊤_ (Tot D)).base` along the isomorphism `1 : (⊤_ (Tot D)).base ≅ I` that
**181XIII** supplies (`truth_terminal_isIso`).  The transport is needed only
because `⊤_ (Tot D)` is *a* final object of `Tot D`, not `Tot.of I` on the
nose. -/
noncomputable def parTotOrth {X Y : D} (f : X ⟶ Y) : X ⟶ (⊤_ (Tot D)).base :=
  EffectusPartialForm.orth (f ≫ truth Y) ≫ inv (truth (⊤_ (Tot D)).base)

theorem parTotOrth_truth {X Y : D} (f : X ⟶ Y) :
    parTotOrth f ≫ truth (⊤_ (Tot D)).base
      = EffectusPartialForm.orth (f ≫ truth Y) := by
  rw [parTotOrth, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem parTotOrth_perp {X Y : D} (f : X ⟶ Y) :
    Perp (f ≫ truth Y) (parTotOrth f ≫ truth (⊤_ (Tot D)).base) := by
  rw [parTotOrth_truth]
  exact EffectusPartialForm.perp_orth _

/-- **188III** (`proof-cho-thm`, eff.tex:1955): the thesis's inverse
`P' f = ⟨f, (1 ∘ f)ᵖ⟩`, on morphisms.  It is total because
`1 ∘ ⟨f, (1 ∘ f)ᵖ⟩ = (1 ∘ f) ⋁ (1 ∘ f)ᵖ = 1` (**181IX.2** and the effect
algebra axiom for `ᵖ`). -/
noncomputable def parTotInvMap {X Y : D} (f : X ⟶ Y) :
    (Par.of (Tot.of X) : Par (Tot D)) ⟶ Par.of (Tot.of Y) :=
  (⟨tpair (X := Tot.of Y) (Y := ⊤_ (Tot D)) f (parTotOrth f) (parTotOrth_perp f), by
      refine Eq.trans
        (tpair_truth (X := Tot.of Y) (Y := ⊤_ (Tot D)) f _ (parTotOrth_perp f)) ?_
      refine (PCM.ovee_congr rfl (parTotOrth_truth f) _
        (EffectusPartialForm.perp_orth _)).trans ?_
      exact EffectusPartialForm.ovee_orth _⟩ :
    (Tot.of X : Tot D) ⟶ Tot.of Y ⨿ ⊤_ (Tot D))

/-- **188III**, the thesis's first computation:
`P P' f = ▷₁ ∘ ⟨f, (1 ∘ f)ᵖ⟩ = f`. -/
theorem parTotFunctor_map_inv {X Y : D} (f : X ⟶ Y) :
    (parTotFunctor (D := D)).map (parTotInvMap f) = f :=
  tpair_tp₁ (X := Tot.of Y) (Y := ⊤_ (Tot D)) f (parTotOrth f) (parTotOrth_perp f)

/-- **188III**, the thesis's second computation:
`P' P f = ⟨▷₁ ∘ f, (1 ∘ ▷₁ ∘ f)ᵖ⟩ = f`.

The thesis writes this as
`⟨▷₁ ∘ f, (1 ∘ ▷₁ ∘ f)ᵖ⟩ = (κ₁ ∘ ▷₁ ∘ f) ⋁ (κ₂ ∘ ▷₁ ∘ f)ᵖ = f`; the content
is that the *second* projection of `f` is the orthosupplement of the first,
`1 ∘ ▷₂ ∘ f = (1 ∘ ▷₁ ∘ f)ᵖ`, which is the decomposition of `1` along a
coproduct (**181IX.2**, `truth_decomp`) together with totality of `f` and the
uniqueness of orthosupplements. -/
theorem parTotInvMap_map {X Y : Par (Tot D)} (f : X ⟶ Y) :
    parTotInvMap ((parTotFunctor (D := D)).map f) = f := by
  have hd : ovee (((pval f).1 ≫ tp₁ Y.base (⊤_ (Tot D))) ≫ truth Y.base.base)
      (((pval f).1 ≫ tp₂ Y.base (⊤_ (Tot D))) ≫ truth (⊤_ (Tot D)).base)
      (tp_perp (pval f).1) = truth X.base.base := by
    rw [truth_decomp (pval f).1]
    exact tot_total_base (pval f)
  have horth : ((pval f).1 ≫ tp₂ Y.base (⊤_ (Tot D))) ≫ truth (⊤_ (Tot D)).base
      = EffectusPartialForm.orth
          (((pval f).1 ≫ tp₁ Y.base (⊤_ (Tot D))) ≫ truth Y.base.base) :=
    EffectusPartialForm.orth_unique (tp_perp (pval f).1) hd
  have key : parTotOrth ((parTotFunctor (D := D)).map f)
      = (pval f).1 ≫ tp₂ Y.base (⊤_ (Tot D)) := by
    show EffectusPartialForm.orth
        (((pval f).1 ≫ tp₁ Y.base (⊤_ (Tot D))) ≫ truth Y.base.base)
        ≫ inv (truth (⊤_ (Tot D)).base) = _
    rw [← horth, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine pval_inj (Subtype.ext (tp_jm (X := Y.base) (Y := ⊤_ (Tot D)) ?_ ?_))
  · exact tpair_tp₁ (X := Tot.of Y.base.base) (Y := ⊤_ (Tot D)) _ _ _
  · exact (tpair_tp₂ (X := Tot.of Y.base.base) (Y := ⊤_ (Tot D)) _ _ _).trans key

/-- **188III** (`proof-cho-thm`, eff.tex:1955): the thesis's **inverse
functor** `P' : D ⟶ Par (Tot D)`, `P' f = ⟨f, (1 ∘ f)ᵖ⟩`, identity on
objects.  Functoriality is not argued separately in the thesis — it follows
from the two computations `P P' = id` and `P' P = id` together with
functoriality of `P`, and that is how it is obtained here. -/
noncomputable def parTotInv : D ⥤ Par (Tot D) where
  obj Z := Par.of (Tot.of Z)
  map f := parTotInvMap f
  map_id X := by
    have h := parTotInvMap_map (𝟙 (Par.of (Tot.of X)))
    rwa [(parTotFunctor (D := D)).map_id] at h
  map_comp {X Y Z} f g := by
    have h := parTotInvMap_map (parTotInvMap f ≫ parTotInvMap g)
    rwa [(parTotFunctor (D := D)).map_comp, parTotFunctor_map_inv,
      parTotFunctor_map_inv] at h

/-- **188III**: `P ⋙ P' = 𝟭` — an equality of functors, on the nose. -/
theorem parTotFunctor_comp_inv :
    parTotFunctor (D := D) ⋙ parTotInv = 𝟭 (Par (Tot D)) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => ?_)
  show parTotInvMap ((parTotFunctor (D := D)).map f) = 𝟙 _ ≫ f ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact parTotInvMap_map f

/-- **188III**: `P' ⋙ P = 𝟭` — an equality of functors, on the nose. -/
theorem parTotInv_comp_functor :
    parTotInv (D := D) ⋙ parTotFunctor = 𝟭 D := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => ?_)
  show (parTotFunctor (D := D)).map (parTotInvMap f) = 𝟙 _ ≫ f ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact parTotFunctor_map_inv f

instance parTotFunctor_full : (parTotFunctor (D := D)).Full where
  map_surjective {_ _} h := ⟨parTotInvMap h, parTotFunctor_map_inv h⟩

instance parTotFunctor_essSurj : (parTotFunctor (D := D)).EssSurj where
  mem_essImage Z := ⟨Par.of (Tot.of Z), ⟨Iso.refl Z⟩⟩

/-- **188III** (`proof-cho-thm`, eff.tex:1943): `Par (Tot D) ≅ D`.

The thesis asserts an **isomorphism of categories**, not merely an
equivalence: `P` is the *identity on objects* and has a genuine two-sided
inverse `P' f = ⟨f, (1 ∘ f)ᵖ⟩`.  That is the first conjunct — two functors,
both identity-on-objects (`parTotFunctor` and `parTotInv`), whose composites
are equal to the identity functors *on the nose*.  (Until the audit repair
only the second conjunct, `Nonempty (Par (Tot D) ≌ D)`, was stated; the
weakening propagated into `cho_thm_3_par_tot`.  This is the same repair as
179III.1 `ea_equiv_emod_two` in `B/Eff/EffectAlgebras`.)  The equivalence is
kept as the second conjunct. -/
theorem par_tot_equiv :
    (∃ (P : Par (Tot D) ⥤ D) (P' : D ⥤ Par (Tot D)),
        (∀ X : Par (Tot D), P.obj X = X.base.base) ∧
        (∀ Z : D, P'.obj Z = Par.of (Tot.of Z)) ∧
        P ⋙ P' = 𝟭 (Par (Tot D)) ∧ P' ⋙ P = 𝟭 D) ∧
      Nonempty (Par (Tot D) ≌ D) := by
  refine ⟨⟨parTotFunctor, parTotInv, fun _ => rfl, fun _ => rfl,
    parTotFunctor_comp_inv, parTotInv_comp_functor⟩, ?_⟩
  have : (parTotFunctor (D := D)).IsEquivalence :=
    { faithful := parTotFunctor_faithful, full := parTotFunctor_full,
      essSurj := parTotFunctor_essSurj }
  exact ⟨(parTotFunctor (D := D)).asEquivalence⟩

end ParTotEquiv


section TotParEquiv

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasTerminal C]
  [EffectusTotalForm C] [HasFiniteCoproducts (Par C)]

/-- **188IV** (`proof-cho-thm`, eff.tex:1969): the identity-on-objects functor
`Q : C ⟶ Tot (Par C)`, `Q g = ĝ`. -/
noncomputable def totParFunctor : C ⥤ Tot (Par C) where
  obj Z := Tot.of (Par.of Z)
  map {Z W} g := ⟨Par.hat g, by
    show (Par.hat g : Par.of Z ⟶ Par.of W) ≫ truth (Par.of W) = truth (Par.of Z)
    show (Par.hat g : Par.of Z ⟶ Par.of W) ≫ Par.one W = Par.one Z
    rw [par_one_eq, par_hat_hat, par_one_eq]
    congr 1
    exact terminalIsTerminal.hom_ext _ _⟩
  map_id Z := Subtype.ext (par_hat_id Z)
  map_comp f g := Subtype.ext (par_hat_hat f g).symm

instance totParFunctor_faithful : (totParFunctor (C := C)).Faithful where
  map_injective {Z W g g'} h := by
    have h' : (Par.hat g : Par.of Z ⟶ Par.of W) = Par.hat g' := congrArg Subtype.val h
    have ht : (Par.hat g : Par.of Z ⟶ Par.of W) ≫ Par.one W = Par.one Z := by
      rw [par_one_eq, par_hat_hat, par_one_eq]
      congr 1
      exact terminalIsTerminal.hom_ext _ _
    have hu := pardp_1 (Par.hat g : Par.of Z ⟶ Par.of W) ht
    exact hu.unique rfl h'

instance totParFunctor_full : (totParFunctor (C := C)).Full where
  map_surjective {Z W} f := by
    obtain ⟨g, hg, -⟩ := pardp_1 (f.1 : Par.of Z ⟶ Par.of W) f.2
    exact ⟨g, Subtype.ext hg.symm⟩

instance totParFunctor_essSurj : (totParFunctor (C := C)).EssSurj where
  mem_essImage X := ⟨X.base.base, ⟨Iso.refl X⟩⟩

/-- **188IV** (`proof-cho-thm`, eff.tex:1975): the inverse of `Q` on
morphisms.  This is the whole of the thesis's argument: "It is an isomorphism
by the first part of `pardp`: for every `f` in `Tot (Par C)` there is a
unique `g` in `C` with `f = ĝ`." -/
noncomputable def totParInvMap {X Y : Tot (Par C)} (f : X ⟶ Y) :
    X.base.base ⟶ Y.base.base :=
  (pardp_1 (f.1 : Par.of X.base.base ⟶ Par.of Y.base.base) f.2).choose

theorem totParInvMap_hat {X Y : Tot (Par C)} (f : X ⟶ Y) :
    (f.1 : Par.of X.base.base ⟶ Par.of Y.base.base) = Par.hat (totParInvMap f) :=
  (pardp_1 (f.1 : Par.of X.base.base ⟶ Par.of Y.base.base) f.2).choose_spec.1

theorem totParInvMap_unique {X Y : Tot (Par C)} (f : X ⟶ Y)
    (g : X.base.base ⟶ Y.base.base)
    (hg : (f.1 : Par.of X.base.base ⟶ Par.of Y.base.base) = Par.hat g) :
    g = totParInvMap f :=
  (pardp_1 (f.1 : Par.of X.base.base ⟶ Par.of Y.base.base) f.2).choose_spec.2 g hg

/-- **188IV** (`proof-cho-thm`, eff.tex:1975): the **inverse functor**
`Q' : Tot (Par C) ⟶ C` of `Q g = ĝ`, identity on objects, sending `f` to the
unique `g` with `f = ĝ` (**186VIII**.1).  Functoriality is the uniqueness
half of `pardp` applied to `id = 𝟙̂` and to `ĝ ⊙ ĥ = (g ∘ h)^` — the two
identities the thesis recalls just before defining `Q`. -/
noncomputable def totParInv : Tot (Par C) ⥤ C where
  obj X := X.base.base
  map f := totParInvMap f
  map_id X :=
    (totParInvMap_unique (𝟙 X) (𝟙 X.base.base) (par_hat_id X.base.base).symm).symm
  map_comp {X Y Z} f g :=
    (totParInvMap_unique (f ≫ g) (totParInvMap f ≫ totParInvMap g) (by
      show (f.1 ≫ g.1 : Par.of X.base.base ⟶ Par.of Z.base.base) = _
      rw [totParInvMap_hat f, totParInvMap_hat g, par_hat_hat])).symm

/-- **188IV**: `Q ⋙ Q' = 𝟭` — an equality of functors, on the nose. -/
theorem totParFunctor_comp_inv :
    totParFunctor (C := C) ⋙ totParInv = 𝟭 C := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => ?_)
  show totParInvMap ((totParFunctor (C := C)).map f) = 𝟙 _ ≫ f ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact (totParInvMap_unique ((totParFunctor (C := C)).map f) f rfl).symm

/-- **188IV**: `Q' ⋙ Q = 𝟭` — an equality of functors, on the nose. -/
theorem totParInv_comp_functor :
    totParInv (C := C) ⋙ totParFunctor = 𝟭 (Tot (Par C)) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => ?_)
  show (totParFunctor (C := C)).map (totParInvMap f) = 𝟙 _ ≫ f ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact Subtype.ext (totParInvMap_hat f).symm

/-- **188IV** (`proof-cho-thm`, eff.tex:1969): `Tot (Par C) ≅ C`.

As in 188III the thesis asserts an **isomorphism of categories**: `Q g = ĝ`
is the identity on objects and is inverted by `pardp`.  That is the first
conjunct — `totParFunctor` and `totParInv`, both identity-on-objects, with
composites equal to the identity functors *on the nose*.  (Until the audit
repair only the second conjunct was stated, and the weakening propagated into
`cho_thm_3_tot_par`.)  The equivalence is kept as the second conjunct. -/
theorem tot_par_equiv :
    (∃ (Q : C ⥤ Tot (Par C)) (Q' : Tot (Par C) ⥤ C),
        (∀ Z : C, Q.obj Z = Tot.of (Par.of Z)) ∧
        (∀ X : Tot (Par C), Q'.obj X = X.base.base) ∧
        Q ⋙ Q' = 𝟭 C ∧ Q' ⋙ Q = 𝟭 (Tot (Par C))) ∧
      Nonempty (Tot (Par C) ≌ C) := by
  refine ⟨⟨totParFunctor, totParInv, fun _ => rfl, fun _ => rfl,
    totParFunctor_comp_inv, totParInv_comp_functor⟩, ?_⟩
  have : (totParFunctor (C := C)).IsEquivalence :=
    { faithful := totParFunctor_faithful, full := totParFunctor_full,
      essSurj := totParFunctor_essSurj }
  exact ⟨(totParFunctor (C := C)).asEquivalence.symm⟩

end TotParEquiv

/-! ## Cho's theorem (180X; proved in parsecs 187 and 188) -/

section ChoTotal

variable (C : Type u) [Category.{v} C] [HasFiniteCoproducts C] [HasTerminal C]
  [EffectusTotalForm C]

/-- **180X.1** (`cho-thm`, eff.tex:948, Theorem (Cho)) = **187I**
(`eff-total-to-partial`, eff.tex:1713, Theorem): if `C` is an effectus in
total form, then `Par C` is an effectus in partial form, with `I = 1`. -/
theorem cho_thm_1 :
    ∃ s : EffectusPartialStructure (Par C), s.effectus.I = Par.of (⊤_ C) :=
  letI := parHasFiniteCoproducts (C := C)
  ⟨{ hasFiniteCoproducts := parHasFiniteCoproducts
     homPCM := parHomPCM
     finPAC := parFinPAC
     effectus := parEffectusPartialForm }, rfl⟩

/-- **180X.3** (`cho-thm`, eff.tex:948, Theorem (Cho)), second half (proved
in 188IV): nothing is lost passing to partial maps: `Tot (Par C) ≅ C`, for the
structure of an effectus in partial form on `Par C` constructed in `cho_thm_1`.

"Nothing is lost" is an **isomorphism of categories**, and that is the first
conjunct: two identity-on-objects functors whose composites are the identity
functors on the nose (see `tot_par_equiv`).  Until the audit repair only the
equivalence, now the second conjunct, was asserted.

(An earlier formulation quantified over *every* structure of an effectus in
partial form on `Par C`.  That is strictly stronger than 188IV: the notion of
*total* map depends on the effect object `I` and the truth predicate `1` of the
structure, and we could not show — nor does the thesis claim — that it is
independent of them.  See PROVING-LOG, session 12.) -/
theorem cho_thm_3_tot_par :
    letI := parHasFiniteCoproducts (C := C)
    (∃ (Q : C ⥤ Tot (Par C)) (Q' : Tot (Par C) ⥤ C),
        (∀ Z : C, Q.obj Z = Tot.of (Par.of Z)) ∧
        (∀ X : Tot (Par C), Q'.obj X = X.base.base) ∧
        Q ⋙ Q' = 𝟭 C ∧ Q' ⋙ Q = 𝟭 (Tot (Par C))) ∧
      Nonempty (Tot (Par C) ≌ C) :=
  letI := parHasFiniteCoproducts (C := C)
  tot_par_equiv

end ChoTotal

section ChoPartial

variable (D : Type u) [Category.{v} D] [HasFiniteCoproducts D]
  [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D] [EffectusPartialForm D]

/-- **180X.2** (`cho-thm`, eff.tex:948, Theorem (Cho)) = **181XI**
(`eff-partial-to-total`, eff.tex:1165, Theorem): the total maps of an
effectus `D` in partial form form an effectus in total form `Tot D`. -/
theorem eff_partial_to_total : Nonempty (EffectusTotalStructure (Tot D)) :=
  letI := totHasFiniteCoproducts (D := D)
  letI := totHasTerminal (D := D)
  ⟨{ hasFiniteCoproducts := totHasFiniteCoproducts
     hasTerminal := totHasTerminal
     effectus := tot_effectusTotalForm D }⟩

/-- **180X.3** (`cho-thm`, eff.tex:948, Theorem (Cho)), first half (proved
in 188III): `Par (Tot D) ≅ D`, for any structure of an effectus in total
form on `Tot D` as produced by `eff_partial_to_total`.

As in `cho_thm_3_tot_par`, "nothing is lost" is an **isomorphism of
categories** — the first conjunct, `P` and `P'` both identity-on-objects with
composites equal to the identity functors on the nose (see `par_tot_equiv`) —
and not merely the equivalence, which is kept as the second conjunct. -/
theorem cho_thm_3_par_tot (s : EffectusTotalStructure (Tot D)) :
    letI := s.hasFiniteCoproducts
    letI := s.hasTerminal
    (∃ (P : Par (Tot D) ⥤ D) (P' : D ⥤ Par (Tot D)),
        (∀ X : Par (Tot D), P.obj X = X.base.base) ∧
        (∀ Z : D, P'.obj Z = Par.of (Tot.of Z)) ∧
        P ⋙ P' = 𝟭 (Par (Tot D)) ∧ P' ⋙ P = 𝟭 D) ∧
      Nonempty (Par (Tot D) ≌ D) :=
  letI := s.hasFiniteCoproducts
  letI := s.hasTerminal
  par_tot_equiv

end ChoPartial

/-! ## Distinguishing the two forms, and examples (parsecs 189, 189a) -/

/-- The canonical isomorphism `0 + A ≅ A`. -/
private noncomputable def coprodInitialIso {C : Type u} [Category.{v} C]
    [HasFiniteCoproducts C] (A : C) : (⊥_ C) ⨿ A ≅ A where
  hom := coprod.desc (initial.to A) (𝟙 A)
  inv := coprod.inr
  hom_inv_id := by
    refine coprod.hom_ext ?_ ?_
    · exact initialIsInitial.hom_ext _ _
    · rw [← Category.assoc, coprod.inr_desc, Category.id_comp, Category.comp_id]
  inv_hom_id := by rw [coprod.inr_desc]

private theorem coprodInitialIso_inr {C : Type u} [Category.{v} C]
    [HasFiniteCoproducts C] (A : C) :
    (coprod.inr : A ⟶ (⊥_ C) ⨿ A) ≫ (coprodInitialIso A).hom = 𝟙 A :=
  (coprodInitialIso A).inv_hom_id

/-- **189I.1** (`distinction-part-tot-eff`, eff.tex:1986, Exercise): the
initial object of an effectus in total form is strict: any map into `0` is
an isomorphism. -/
theorem distinction_part_tot_eff_1 {C : Type u} [Category.{v} C]
    [HasFiniteCoproducts C] [HasTerminal C] [EffectusTotalForm C]
    {X : C} (f : X ⟶ ⊥_ C) : IsIso f := by
  -- the right pullback square of 185I for `𝟙 : 0 ⟶ 0` and `f : X ⟶ 0`,
  -- transported along `0 + A ≅ A` (bsols.tex:1804)
  have hsq : IsPullback (𝟙 (⊥_ C)) (initial.to X) (𝟙 (⊥_ C)) f := by
    refine (tot_pullbacks_right (𝟙 (⊥_ C)) f).of_iso (Iso.refl _) (Iso.refl _)
      (coprodInitialIso X) (coprodInitialIso (⊥_ C)) ?_ ?_ ?_ ?_
    · simp
    · exact initialIsInitial.hom_ext _ _
    · exact initialIsInitial.hom_ext _ _
    · refine coprod.hom_ext ?_ ?_
      · exact initialIsInitial.hom_ext _ _
      · rw [← Category.assoc, coprod.inr_map, Category.assoc, coprodInitialIso_inr,
          Category.comp_id, ← Category.assoc, coprodInitialIso_inr, Category.id_comp]
  have hl := hsq.lift_fst f (𝟙 X) (by rw [Category.comp_id, Category.id_comp])
  have hr := hsq.lift_snd f (𝟙 X) (by rw [Category.comp_id, Category.id_comp])
  rw [Category.comp_id] at hl
  rw [hl] at hr
  exact ⟨⟨initial.to X, hr, initialIsInitial.hom_ext _ _⟩⟩

/-- **189I.2** (`distinction-part-tot-eff`, eff.tex:1986, Exercise): if `C`
is an effectus in both total and partial form, then every object of `C` is
isomorphic to `0`. -/
theorem distinction_part_tot_eff_2 {C : Type u} [Category.{v} C]
    [HasFiniteCoproducts C] [HasTerminal C] [EffectusTotalForm C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
    (X : C) : Nonempty (X ≅ ⊥_ C) := by
  -- `0` is a zero object of an effectus in partial form, so `X ⟶ 0` has the
  -- zero map, which is an isomorphism by the previous point
  have := distinction_part_tot_eff_1 (0 : X ⟶ ⊥_ C)
  exact ⟨asIso (0 : X ⟶ ⊥_ C)⟩

-- **180V** (`effectus-vn`, eff.tex:827) and **189aI**
-- (`effexamplesintro`, eff.tex:2020, Examples), `effectus_vn` and
-- `effectus_vn_partial`: `vNᵒᵖ` is an effectus in total resp. partial
-- form.  Moved to `Theses/B/Eff/VNExamples.lean` (author ruling
-- 2026-08-17): they need thesis A's von Neumann theory, and this file must
-- keep importing only `Theses.Common` (and `Theses.B.Eff.WStarCat`).

/-! ### Extensive categories (189aII.3) -/

section ExtensiveEffectus

variable {C : Type u} [Category.{v} C] [FinitaryExtensive C]

/-- The van Kampen property of the coproduct cocone `X ⨿ Y`, in the form we use:
a cofan `(inl', inr')` over `(X', Y')` lying over `X ⨿ Y` is a colimit iff both
its squares are pullbacks. -/
private theorem ext_vk {X Y X' Y' P : C} (inl' : X' ⟶ P) (inr' : Y' ⟶ P)
    (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : P ⟶ X ⨿ Y)
    (hX : αX ≫ coprod.inl = inl' ≫ f) (hY : αY ≫ coprod.inr = inr' ≫ f) :
    Nonempty (IsColimit (BinaryCofan.mk inl' inr')) ↔
      (IsPullback inl' αX f coprod.inl ∧ IsPullback inr' αY f coprod.inr) :=
  (BinaryCofan.isVanKampen_iff
      (BinaryCofan.mk (coprod.inl : X ⟶ X ⨿ Y) coprod.inr)).mp
    (FinitaryExtensive.van_kampen' _ (coprodIsCoprod X Y))
    (X' := X') (Y' := Y') (BinaryCofan.mk inl' inr') αX αY f hX hY

/-- Coproducts in a finitary extensive category are *universal*: any map
`m : Z ⟶ X ⨿ Y` decomposes `Z` as the coproduct of the two pullbacks. -/
private theorem ext_decomp {X Y Z : C} (m : Z ⟶ X ⨿ Y) :
    Nonempty (IsColimit (BinaryCofan.mk
      (pullback.snd (coprod.inl : X ⟶ X ⨿ Y) m)
      (pullback.snd (coprod.inr : Y ⟶ X ⨿ Y) m))) := by
  have h₁ : IsPullback (pullback.snd (coprod.inl : X ⟶ X ⨿ Y) m)
      (pullback.fst (coprod.inl : X ⟶ X ⨿ Y) m) m coprod.inl :=
    (IsPullback.of_hasPullback _ _).flip
  have h₂ : IsPullback (pullback.snd (coprod.inr : Y ⟶ X ⨿ Y) m)
      (pullback.fst (coprod.inr : Y ⟶ X ⨿ Y) m) m coprod.inr :=
    (IsPullback.of_hasPullback _ _).flip
  exact (ext_vk _ _ _ _ m h₁.w.symm h₂.w.symm).mpr ⟨h₁, h₂⟩

variable [HasTerminal C]

omit [FinitaryExtensive C] in
private theorem ext_terminal_self : terminal.from (⊤_ C) = 𝟙 (⊤_ C) :=
  terminal.hom_ext _ _

/-- Transporting the coproduct cocone along an isomorphism of its vertex. -/
private noncomputable def cofanOfIso {X Y P : C} (e : X ⨿ Y ≅ P) :
    IsColimit (BinaryCofan.mk (coprod.inl ≫ e.hom) (coprod.inr ≫ e.hom)) :=
  (coprodIsCoprod X Y).ofIsoColimit (Cocone.ext e (by rintro ⟨⟨⟩⟩ <;> rfl))

/-- `(1+1)+1` is *also* the coproduct of `1` and `1+1`, with injections
`κ₁∘κ₁` and `[κ₂∘κ₁, κ₂]`. -/
private noncomputable def cofanAssoc : IsColimit (BinaryCofan.mk
    (coprod.inl ≫ coprod.inl : (⊤_ C) ⟶ ((⊤_ C) ⨿ (⊤_ C)) ⨿ (⊤_ C))
    (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr)) := by
  have h1 : (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ ((⊤_ C) ⨿ (⊤_ C))) ≫
      (coprod.associator (⊤_ C) (⊤_ C) (⊤_ C)).inv
      = coprod.inl ≫ coprod.inl := by
    rw [coprod.associator_inv, coprod.inl_desc]
  have h2 : (coprod.inr : (⊤_ C) ⨿ (⊤_ C) ⟶ (⊤_ C) ⨿ ((⊤_ C) ⨿ (⊤_ C))) ≫
      (coprod.associator (⊤_ C) (⊤_ C) (⊤_ C)).inv
      = coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr := by
    rw [coprod.associator_inv, coprod.inr_desc]
  rw [← h1, ← h2]
  exact cofanOfIso (coprod.associator (⊤_ C) (⊤_ C) (⊤_ C)).symm

/-- **189aII.3**, third axiom: the cotuples `[κ₁,κ₂,κ₂]` and `[κ₂,κ₁,κ₂]`
are jointly monic in a finitary extensive category with a final object. -/
private theorem ext_jointlyMonic :
    JointlyMonic
      (coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr :
        ((⊤_ C) ⨿ (⊤_ C)) ⨿ (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
      (coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr) := by
  intro Z a b hf hg
  -- `F⁻¹(κ₁)` is the first summand, `F⁻¹(κ₂)` the last two
  obtain ⟨F1, F2⟩ :=
    (ext_vk (coprod.inl ≫ coprod.inl : (⊤_ C) ⟶ ((⊤_ C) ⨿ (⊤_ C)) ⨿ (⊤_ C))
      (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr)
      (𝟙 (⊤_ C)) (terminal.from ((⊤_ C) ⨿ (⊤_ C)))
      (coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr)
      (by simp [coprod.inl_desc])
      (by
        refine coprod.hom_ext ?_ ?_ <;>
          simp [coprod.inl_desc, coprod.inr_desc, ext_terminal_self])).mp ⟨cofanAssoc⟩
  -- over the first summand both `a` and `b` factor through `κ₁∘κ₁`
  have key₁ : ∀ c : Z ⟶ ((⊤_ C) ⨿ (⊤_ C)) ⨿ (⊤_ C),
      c ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr =
        a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr →
      pullback.snd (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
          (a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr) ≫ c =
        terminal.from _ ≫ (coprod.inl ≫ coprod.inl) := by
    intro c hc
    have hw : (pullback.snd (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
          (a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr) ≫ c) ≫
        coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr =
          pullback.fst (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
            (a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr) ≫ coprod.inl := by
      rw [Category.assoc, hc, ← pullback.condition]
    rw [← F1.lift_fst _ _ hw]
    congr 1
    exact terminal.hom_ext _ _
  -- over the last two summands both factor through `N = [κ₂∘κ₁, κ₂]`, and `G`
  -- recovers the factorisation because `N ∘ G = id`
  have hGN : (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr :
      (⊤_ C) ⨿ (⊤_ C) ⟶ ((⊤_ C) ⨿ (⊤_ C)) ⨿ (⊤_ C)) ≫
      coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr = 𝟙 _ := by
    refine coprod.hom_ext ?_ ?_ <;> simp [coprod.inl_desc, coprod.inr_desc]
  have key₂ : ∀ c : Z ⟶ ((⊤_ C) ⨿ (⊤_ C)) ⨿ (⊤_ C),
      c ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr =
        a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr →
      pullback.snd (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
          (a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr) ≫ c =
        (pullback.snd (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
          (a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr) ≫ c ≫
            coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr) ≫
          coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr := by
    intro c hc
    have hw : (pullback.snd (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
          (a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr) ≫ c) ≫
        coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr =
          pullback.fst (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
            (a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr) ≫ coprod.inr := by
      rw [Category.assoc, hc, ← pullback.condition]
    obtain ⟨L, hL⟩ : ∃ L, L ≫ coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr =
          pullback.snd (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
            (a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr) ≫ c :=
      ⟨F2.lift _ _ hw, F2.lift_fst _ _ hw⟩
    have h3 : pullback.snd (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
          (a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr) ≫ c ≫
            coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr = L := by
      rw [← Category.assoc, ← hL, Category.assoc, hGN, Category.comp_id]
    rw [h3, hL]
  -- `Z` is the coproduct of the two pieces, so `a = b`
  obtain ⟨hcol⟩ := ext_decomp (a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr)
  refine BinaryCofan.IsColimit.hom_ext hcol ?_ ?_
  · exact (key₁ a rfl).trans (key₁ b hf.symm).symm
  · have h2 : (pullback.snd (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
          (a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr) ≫ a ≫
            coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr) ≫
          (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr :
            (⊤_ C) ⨿ (⊤_ C) ⟶ ((⊤_ C) ⨿ (⊤_ C)) ⨿ (⊤_ C)) =
        (pullback.snd (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
          (a ≫ coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr) ≫ b ≫
            coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr) ≫
          (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr :
            (⊤_ C) ⨿ (⊤_ C) ⟶ ((⊤_ C) ⨿ (⊤_ C)) ⨿ (⊤_ C)) := by
      rw [hg]
    exact (key₂ a rfl).trans (h2.trans (key₂ b hf.symm).symm)


/-- **189aII.3**, second axiom: the `κ₁`-square is a pullback. -/
private theorem ext_isPullback_kappa (X Y : C) :
    IsPullback (terminal.from X) (coprod.inl : X ⟶ X ⨿ Y)
      (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
      (coprod.map (terminal.from X) (terminal.from Y)) :=
  (((ext_vk (coprod.inl : X ⟶ X ⨿ Y) (coprod.inr : Y ⟶ X ⨿ Y)
      (terminal.from X) (terminal.from Y)
      (coprod.map (terminal.from X) (terminal.from Y))
      (by rw [coprod.inl_map]) (by rw [coprod.inr_map])).mp
    ⟨coprodIsCoprod X Y⟩).1).flip

/-- The `κ₂`-form of the second axiom. -/
private theorem ext_isPullback_kappa_inr (X Y : C) :
    IsPullback (terminal.from Y) (coprod.inr : Y ⟶ X ⨿ Y)
      (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C))
      (coprod.map (terminal.from X) (terminal.from Y)) :=
  (((ext_vk (coprod.inl : X ⟶ X ⨿ Y) (coprod.inr : Y ⟶ X ⨿ Y)
      (terminal.from X) (terminal.from Y)
      (coprod.map (terminal.from X) (terminal.from Y))
      (by rw [coprod.inl_map]) (by rw [coprod.inr_map])).mp
    ⟨coprodIsCoprod X Y⟩).2).flip

omit [FinitaryExtensive C] [HasTerminal C] in
/-- A square with a unique diagonal filler is a pullback.  (Stated with
plainly typed data, so that the projections of an arbitrary `PullbackCone`
never have to be rewritten.) -/
private theorem isPullback_of_existsUnique {W X Y S : C} {fst : W ⟶ X} {snd : W ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (w : fst ≫ f = snd ≫ g)
    (h : ∀ (T : C) (p : T ⟶ X) (q : T ⟶ Y), p ≫ f = q ≫ g →
      ∃! l : T ⟶ W, l ≫ fst = p ∧ l ≫ snd = q) :
    IsPullback fst snd f g := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun s => (h s.pt s.fst s.snd s.condition).choose) (fun s => ?_) (fun s => ?_)
    (fun s m h₁ h₂ => ?_))
  · exact (h s.pt s.fst s.snd s.condition).choose_spec.1.1
  · exact (h s.pt s.fst s.snd s.condition).choose_spec.1.2
  · exact (h s.pt s.fst s.snd s.condition).choose_spec.2 m ⟨h₁, h₂⟩

/-- **189aII.3**, first axiom: the `+`-square is a pullback. -/
private theorem ext_isPullback_plus (X Y : C) :
    IsPullback (coprod.map (𝟙 X) (terminal.from Y))
      (coprod.map (terminal.from X) (𝟙 Y))
      (coprod.map (terminal.from X) (𝟙 (⊤_ C)))
      (coprod.map (𝟙 (⊤_ C)) (terminal.from Y)) := by
  -- the decompositions of `u = !+id : X+1 → 1+1` and `v = id+! : 1+Y → 1+1`
  obtain ⟨A1, A2⟩ :=
    (ext_vk (coprod.inl : X ⟶ X ⨿ (⊤_ C)) (coprod.inr : (⊤_ C) ⟶ X ⨿ (⊤_ C))
      (terminal.from X) (𝟙 (⊤_ C)) (coprod.map (terminal.from X) (𝟙 (⊤_ C)))
      (by rw [coprod.inl_map]) (by rw [coprod.inr_map])).mp ⟨coprodIsCoprod _ _⟩
  obtain ⟨B1, B2⟩ :=
    (ext_vk (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ Y) (coprod.inr : Y ⟶ (⊤_ C) ⨿ Y)
      (𝟙 (⊤_ C)) (terminal.from Y) (coprod.map (𝟙 (⊤_ C)) (terminal.from Y))
      (by rw [coprod.inl_map]) (by rw [coprod.inr_map])).mp ⟨coprodIsCoprod _ _⟩
  have hmono₁ : Mono (coprod.inl : X ⟶ X ⨿ (⊤_ C)) :=
    FinitaryExtensive.mono_inl_of_isColimit (colimit.isColimit (pair X (⊤_ C)))
  have hmono₂ : Mono (coprod.inr : Y ⟶ (⊤_ C) ⨿ Y) :=
    FinitaryExtensive.mono_inr_of_isColimit (colimit.isColimit (pair (⊤_ C) Y))
  have hmap : coprod.map (𝟙 X) (terminal.from Y) ≫
        coprod.map (terminal.from X) (𝟙 (⊤_ C)) =
      coprod.map (terminal.from X) (terminal.from Y) := by
    refine coprod.hom_ext ?_ ?_ <;> simp [coprod.inl_map, coprod.inr_map]
  have hmap' : coprod.map (terminal.from X) (𝟙 Y) ≫
        coprod.map (𝟙 (⊤_ C)) (terminal.from Y) =
      coprod.map (terminal.from X) (terminal.from Y) := by
    refine coprod.hom_ext ?_ ?_ <;> simp [coprod.inl_map, coprod.inr_map]
  refine isPullback_of_existsUnique (hmap.trans hmap'.symm) (fun T p q hpq => ?_)
  set m : T ⟶ (⊤_ C) ⨿ (⊤_ C) := p ≫ coprod.map (terminal.from X) (𝟙 (⊤_ C)) with hm
  obtain ⟨hcol⟩ := ext_decomp m
  set k₁ : pullback (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C)) m ⟶ T :=
    pullback.snd (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C)) m with hk₁
  set k₂ : pullback (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C)) m ⟶ T :=
    pullback.snd (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C)) m with hk₂
  have hc₁ : k₁ ≫ m = terminal.from _ ≫ coprod.inl := by
    rw [hk₁, ← pullback.condition]
    congr 1
    exact terminal.hom_ext _ _
  have hc₂ : k₂ ≫ m = terminal.from _ ≫ coprod.inr := by
    rw [hk₂, ← pullback.condition]
    congr 1
    exact terminal.hom_ext _ _
  -- restrictions of `p` and `q` to the two pieces of `T`
  have hp₁ : (k₁ ≫ p) ≫ coprod.map (terminal.from X) (𝟙 (⊤_ C)) =
      terminal.from _ ≫ coprod.inl := (Category.assoc _ _ _).trans hc₁
  have hp₂' : (k₂ ≫ p) ≫ coprod.map (terminal.from X) (𝟙 (⊤_ C)) =
      terminal.from _ ≫ coprod.inr := (Category.assoc _ _ _).trans hc₂
  have hq₁' : (k₁ ≫ q) ≫ coprod.map (𝟙 (⊤_ C)) (terminal.from Y) =
      terminal.from _ ≫ coprod.inl :=
    (Category.assoc _ _ _).trans ((congrArg (fun t => k₁ ≫ t) hpq.symm).trans hc₁)
  have hq₂ : (k₂ ≫ q) ≫ coprod.map (𝟙 (⊤_ C)) (terminal.from Y) =
      terminal.from _ ≫ coprod.inr :=
    (Category.assoc _ _ _).trans ((congrArg (fun t => k₂ ≫ t) hpq.symm).trans hc₂)
  -- on the second piece `p` is `κ₂ ∘ !`; on the first piece `q` is `κ₁ ∘ !`
  have hp₂ : k₂ ≫ p = terminal.from _ ≫ coprod.inr := by
    obtain ⟨L, hL⟩ : ∃ L, L ≫ (coprod.inr : (⊤_ C) ⟶ X ⨿ (⊤_ C)) = k₂ ≫ p :=
      ⟨A2.lift _ _ hp₂', A2.lift_fst _ _ hp₂'⟩
    rw [← hL]
    congr 1
    exact terminal.hom_ext _ _
  have hq₁ : k₁ ≫ q = terminal.from _ ≫ coprod.inl := by
    obtain ⟨L, hL⟩ : ∃ L, L ≫ (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ Y) = k₁ ≫ q :=
      ⟨B1.lift _ _ hq₁', B1.lift_fst _ _ hq₁'⟩
    rw [← hL]
    congr 1
    exact terminal.hom_ext _ _
  -- the two components of the filler
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, t₁ ≫ (coprod.inl : X ⟶ X ⨿ (⊤_ C)) = k₁ ≫ p :=
    ⟨A1.lift _ _ hp₁, A1.lift_fst _ _ hp₁⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t₂, t₂ ≫ (coprod.inr : Y ⟶ (⊤_ C) ⨿ Y) = k₂ ≫ q :=
    ⟨B2.lift _ _ hq₂, B2.lift_fst _ _ hq₂⟩
  obtain ⟨D, hd₁, hd₂⟩ : ∃ D : T ⟶ X ⨿ Y, k₁ ≫ D = t₁ ≫ coprod.inl ∧
      k₂ ≫ D = t₂ ≫ coprod.inr :=
    ⟨BinaryCofan.IsColimit.desc hcol _ _, BinaryCofan.IsColimit.inl_desc hcol _ _,
      BinaryCofan.IsColimit.inr_desc hcol _ _⟩
  refine ⟨D, ⟨?_, ?_⟩, ?_⟩
  · have e₁ : k₁ ≫ (D ≫
        coprod.map (𝟙 X) (terminal.from Y)) = k₁ ≫ p := by
      rw [← Category.assoc, hd₁, Category.assoc, coprod.inl_map, Category.id_comp]
      exact ht₁
    have e₂ : k₂ ≫ (D ≫
        coprod.map (𝟙 X) (terminal.from Y)) = k₂ ≫ p := by
      rw [← Category.assoc, hd₂, Category.assoc, coprod.inr_map, ← Category.assoc, hp₂]
      congr 1
      exact terminal.hom_ext _ _
    exact BinaryCofan.IsColimit.hom_ext hcol e₁ e₂
  · have e₁ : k₁ ≫ (D ≫
        coprod.map (terminal.from X) (𝟙 Y)) = k₁ ≫ q := by
      rw [← Category.assoc, hd₁, Category.assoc, coprod.inl_map, ← Category.assoc, hq₁]
      congr 1
      exact terminal.hom_ext _ _
    have e₂ : k₂ ≫ (D ≫
        coprod.map (terminal.from X) (𝟙 Y)) = k₂ ≫ q := by
      rw [← Category.assoc, hd₂, Category.assoc, coprod.inr_map, Category.id_comp]
      exact ht₂
    exact BinaryCofan.IsColimit.hom_ext hcol e₁ e₂
  · rintro l ⟨hl₁, hl₂⟩
    have e₁ : k₁ ≫ l = k₁ ≫ D := by
      rw [hd₁]
      have hcond : (k₁ ≫ l) ≫ coprod.map (terminal.from X) (terminal.from Y) =
          terminal.from _ ≫ coprod.inl := by
        rw [← hmap, ← Category.assoc, Category.assoc k₁ l, hl₁]
        exact hp₁
      obtain ⟨r, hr⟩ : ∃ r, r ≫ (coprod.inl : X ⟶ X ⨿ Y) = k₁ ≫ l :=
        ⟨(ext_isPullback_kappa X Y).flip.lift _ _ hcond,
          (ext_isPullback_kappa X Y).flip.lift_fst _ _ hcond⟩
      have hrt : r ≫ (coprod.inl : X ⟶ X ⨿ (⊤_ C)) =
          t₁ ≫ (coprod.inl : X ⟶ X ⨿ (⊤_ C)) := by
        rw [ht₁, ← hl₁, ← Category.assoc, ← hr, Category.assoc, coprod.inl_map,
          Category.id_comp]
      rw [← hr, hmono₁.right_cancellation _ _ hrt]
    have e₂ : k₂ ≫ l = k₂ ≫ D := by
      rw [hd₂]
      have hcond : (k₂ ≫ l) ≫ coprod.map (terminal.from X) (terminal.from Y) =
          terminal.from _ ≫ coprod.inr := by
        rw [← hmap', ← Category.assoc, Category.assoc k₂ l, hl₂]
        exact hq₂
      obtain ⟨r, hr⟩ : ∃ r, r ≫ (coprod.inr : Y ⟶ X ⨿ Y) = k₂ ≫ l :=
        ⟨(ext_isPullback_kappa_inr X Y).flip.lift _ _ hcond,
          (ext_isPullback_kappa_inr X Y).flip.lift_fst _ _ hcond⟩
      have hrt : r ≫ (coprod.inr : Y ⟶ (⊤_ C) ⨿ Y) =
          t₂ ≫ (coprod.inr : Y ⟶ (⊤_ C) ⨿ Y) := by
        rw [ht₂, ← hl₂, ← Category.assoc, ← hr, Category.assoc, coprod.inr_map,
          Category.id_comp]
      rw [← hr, hmono₂.right_cancellation _ _ hrt]
    exact BinaryCofan.IsColimit.hom_ext hcol e₁ e₂

/-- **189aII.3** (`effexamplesintro`, eff.tex:2043): every finitary extensive
category with a final object is an effectus in total form. -/
private theorem ext_effectusTotalForm : EffectusTotalForm C where
  isPullback_plus := ext_isPullback_plus
  isPullback_kappa := ext_isPullback_kappa
  jointlyMonic_cotuples := ext_jointlyMonic

end ExtensiveEffectus


/-- **189aII.3** (`effexamplesintro`, eff.tex:2043, Examples): every
(finitary) extensive category with a final object is an effectus in total
form.

Two of the point's three sub-items are formalized below —
**(a) `Set`** as `extensive_effectus_set` and **(c) `CH`** as
`extensive_effectus_compHaus`.  **(b) `CRngᵒᵖ`** is *not*, and this is a
costing rather than an oversight: Mathlib has no `FinitaryExtensive` instance
for `CommRingCatᵒᵖ`, and the only handle in reach is
`FinitaryExtensive Scheme` (`Mathlib.AlgebraicGeometry.Limits`) transported
along `AffineScheme ≌ CommRingCatᵒᵖ`, which additionally needs
`AffineScheme.forgetToScheme` to preserve *and reflect* finite coproducts and
pullbacks of coprojections — a development of its own, on top of an
`AlgebraicGeometry` import nothing else in this tree uses.  Proving
extensivity by hand is the same content: a coproduct in `CRngᵒᵖ` is the
product ring `R × S`, and the van Kampen property is the statement that an
`R × S`-algebra splits uniquely along the central idempotents `(1,0)` and
`(0,1)`.

The neighbouring examples 189aII.1 (`OUSᵒᵖ`), 189aII.2 (`OUGᵒᵖ`) and 189aIII
(`EJAᵒᵖ`) are separate points, each citing `[effintro]`/`[eja]`, and none of
those three categories exists in the tree. -/
theorem extensive_effectus (C : Type u) [Category.{v} C]
    [HasFiniteCoproducts C] [HasTerminal C] [FinitaryExtensive C] :
    EffectusTotalForm C := ext_effectusTotalForm

/-- **189aII.3(a)** (`effexamplesintro`, eff.tex:2049, Examples): `Set`, the
category of sets and functions, is extensive with a final object — hence an
effectus in total form.  Extensivity is Mathlib's `types.finitaryExtensive`;
the rest is `extensive_effectus`. -/
theorem extensive_effectus_set : EffectusTotalForm (Type u) :=
  extensive_effectus (Type u)

/-- **189aII.3(c)** (`effexamplesintro`, eff.tex:2056, Examples): `CH`, the
category of compact Hausdorff spaces and continuous maps, is extensive with a
final object — hence an effectus in total form.  Extensivity is Mathlib's
instance for `CompHausLike P` (`CompHaus = CompHausLike (fun _ => True)`),
obtained by reflection along the forgetful functor to `TopCat`.

The `letI` is a universe-inference workaround, not mathematics: instance
synthesis for `HasFiniteCoproducts CompHaus.{u}` gets stuck on
`u =?= max ?v ?w`, because Mathlib's `CompHausLike` instance is stated in two
universes, so `FinitaryExtensive.hasFiniteCoproducts` has to be named. -/
theorem extensive_effectus_compHaus :
    letI : HasFiniteCoproducts CompHaus.{u} := FinitaryExtensive.hasFiniteCoproducts
    EffectusTotalForm CompHaus.{u} :=
  letI : HasFiniteCoproducts CompHaus.{u} := FinitaryExtensive.hasFiniteCoproducts
  extensive_effectus CompHaus.{u}

end Theses.B.Eff
