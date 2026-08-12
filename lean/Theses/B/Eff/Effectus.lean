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

section ChoTotal

variable (C : Type u) [Category.{v} C] [HasFiniteCoproducts C] [HasTerminal C]
  [EffectusTotalForm C]

/-- **180X.1** (`cho-thm`, eff.tex:948, Theorem (Cho)) = **187I**
(`eff-total-to-partial`, eff.tex:1713, Theorem): if `C` is an effectus in
total form, then `Par C` is an effectus in partial form, with `I = 1`. -/
theorem cho_thm_1 :
    ∃ s : EffectusPartialStructure (Par C), s.effectus.I = Par.of (⊤_ C) :=
  sorry

/-- **180X.3** (`cho-thm`, eff.tex:948, Theorem (Cho)), second half (proved
in 188IV): nothing is lost passing to partial maps: `Tot (Par C) ≅ C`, for
any structure of an effectus in partial form on `Par C` as in `cho_thm_1`. -/
theorem cho_thm_3_tot_par (s : EffectusPartialStructure (Par C)) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    Nonempty (Tot (Par C) ≌ C) := sorry

end ChoTotal

section ChoPartial

variable (D : Type u) [Category.{v} D] [HasFiniteCoproducts D]
  [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D] [EffectusPartialForm D]

/-- **180X.2** (`cho-thm`, eff.tex:948, Theorem (Cho)) = **181XI**
(`eff-partial-to-total`, eff.tex:1165, Theorem): the total maps of an
effectus `D` in partial form form an effectus in total form `Tot D`. -/
theorem eff_partial_to_total : Nonempty (EffectusTotalStructure (Tot D)) :=
  sorry

/-- **180X.3** (`cho-thm`, eff.tex:948, Theorem (Cho)), first half (proved
in 188III): `Par (Tot D) ≅ D`, for any structure of an effectus in total
form on `Tot D` as produced by `eff_partial_to_total`. -/
theorem cho_thm_3_par_tot (s : EffectusTotalStructure (Tot D)) :
    letI := s.hasFiniteCoproducts
    letI := s.hasTerminal
    Nonempty (Par (Tot D) ≌ D) := sorry

end ChoPartial

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

/-- **181IV.1** (`cotupl-pcm`, eff.tex:999, Proposition): cotupling
reflects and preserves `⊥`: `[f,g] ⊥ [f',g']` iff `f ⊥ f'` and
`g ⊥ g'`. -/
theorem cotupl_pcm_1 (f f' : X ⟶ Z) (g g' : Y ⟶ Z) :
    Perp (coprod.desc f g) (coprod.desc f' g') ↔ Perp f f' ∧ Perp g g' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h₁ := perp_comp_left h (coprod.inl : X ⟶ X ⨿ Y)
      rwa [coprod.inl_desc, coprod.inl_desc] at h₁
    · have h₂ := perp_comp_left h (coprod.inr : Y ⟶ X ⨿ Y)
      rwa [coprod.inr_desc, coprod.inr_desc] at h₂
  · rintro ⟨hf, hg⟩
    -- put the two summands into the two summands of `Z + Z` and use the
    -- compatible sum axiom (cf. eff.tex:1020)
    have hu : Perp (f ≫ (coprod.inl : Z ⟶ Z ⨿ Z)) (f' ≫ coprod.inr) :=
      FinPAC.untying hf
    have hv : Perp (g ≫ (coprod.inl : Z ⟶ Z ⨿ Z)) (g' ≫ coprod.inr) :=
      FinPAC.untying hg
    have hb := FinPAC.compatible_sum
      (coprod.desc (ovee _ _ hu) (ovee _ _ hv) : X ⨿ Y ⟶ Z ⨿ Z)
    have e₁ : coprod.desc (ovee _ _ hu) (ovee _ _ hv) ≫ pproj₁ Z Z
        = coprod.desc f g := by
      rw [coprod.desc_comp]
      congr 1
      · rw [ovee_comp_right hu _ (perp_comp_right hu _)]
        refine (PCM.ovee_congr ?_ ?_ _ (PCM.perp_zero f)).trans (PCM.ovee_zero f _)
        · rw [Category.assoc, inl_pproj₁, Category.comp_id]
        · rw [Category.assoc, inr_pproj₁, FinPAC.comp_zero]
      · rw [ovee_comp_right hv _ (perp_comp_right hv _)]
        refine (PCM.ovee_congr ?_ ?_ _ (PCM.perp_zero g)).trans (PCM.ovee_zero g _)
        · rw [Category.assoc, inl_pproj₁, Category.comp_id]
        · rw [Category.assoc, inr_pproj₁, FinPAC.comp_zero]
    have e₂ : coprod.desc (ovee _ _ hu) (ovee _ _ hv) ≫ pproj₂ Z Z
        = coprod.desc f' g' := by
      rw [coprod.desc_comp]
      congr 1
      · rw [ovee_comp_right hu _ (perp_comp_right hu _)]
        refine (PCM.ovee_congr ?_ ?_ _ (PCM.zero_perp f')).trans (PCM.zero_ovee f')
        · rw [Category.assoc, inl_pproj₂, FinPAC.comp_zero]
        · rw [Category.assoc, inr_pproj₂, Category.comp_id]
      · rw [ovee_comp_right hv _ (perp_comp_right hv _)]
        refine (PCM.ovee_congr ?_ ?_ _ (PCM.zero_perp g')).trans (PCM.zero_ovee g')
        · rw [Category.assoc, inl_pproj₂, FinPAC.comp_zero]
        · rw [Category.assoc, inr_pproj₂, Category.comp_id]
    rwa [e₁, e₂] at hb

/-- **181IV.2** (`cotupl-pcm`, eff.tex:999, Proposition):
`[f,g] ⋁ [f',g'] = [f ⋁ f', g ⋁ g']`. -/
theorem cotupl_pcm_2 {f f' : X ⟶ Z} {g g' : Y ⟶ Z}
    (h : Perp (coprod.desc f g) (coprod.desc f' g'))
    (hf : Perp f f') (hg : Perp g g') :
    ovee _ _ h = coprod.desc (ovee f f' hf) (ovee g g' hg) := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc, ovee_comp_left h _ (perp_comp_left h _)]
    exact PCM.ovee_congr (coprod.inl_desc _ _) (coprod.inl_desc _ _) _ hf
  · rw [coprod.inr_desc, ovee_comp_left h _ (perp_comp_left h _)]
    exact PCM.ovee_congr (coprod.inr_desc _ _) (coprod.inr_desc _ _) _ hg

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

/-- **181VII** (`coprod-prod`, eff.tex:1066, Proposition): the coproduct in
an effectus in partial form is almost a biproduct — for `f : Z ⟶ X` and
`g : Z ⟶ Y` with `1 ∘ f ⊥ 1 ∘ g` there is a unique `⟨f,g⟩ : Z ⟶ X + Y`
with `▷₁ ∘ ⟨f,g⟩ = f` and `▷₂ ∘ ⟨f,g⟩ = g`. -/
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
  obtain ⟨hk, -, -⟩ := exists_pair (f ≫ k) (g ≫ l) h'
  have e₁ : (effPair f g h ≫ coprod.map k l) ≫ pproj₁ X' Y' = f ≫ k := by
    rw [Category.assoc, map_pproj₁, ← pproj₁_comp (Y := Y) k, ← Category.assoc,
      (effPair_spec f g h).1]
  have e₂ : (effPair f g h ≫ coprod.map k l) ≫ pproj₂ X' Y' = g ≫ l := by
    rw [Category.assoc, map_pproj₂, ← pproj₂_comp (X := X) l, ← Category.assoc,
      (effPair_spec f g h).2]
  rw [pair_unique _ _ _ e₁ e₂ hk,
    pair_unique _ _ _ (effPair_spec (f ≫ k) (g ≫ l) h').1
      (effPair_spec (f ≫ k) (g ≫ l) h').2 hk]

/-- **181IX.4** (`eff-prod-rules`, eff.tex:1137, Exercise):
`⟨f,g⟩ ∘ k = ⟨f ∘ k, g ∘ k⟩`. -/
theorem eff_prod_rules_4 {W : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) (k : W ⟶ Z)
    (h' : Perp ((k ≫ f) ≫ truth X) ((k ≫ g) ≫ truth Y)) :
    k ≫ effPair f g h = effPair (k ≫ f) (k ≫ g) h' := by
  obtain ⟨hk, -, -⟩ := exists_pair (k ≫ f) (k ≫ g) h'
  have e₁ : (k ≫ effPair f g h) ≫ pproj₁ X Y = k ≫ f := by
    rw [Category.assoc, (effPair_spec f g h).1]
  have e₂ : (k ≫ effPair f g h) ≫ pproj₂ X Y = k ≫ g := by
    rw [Category.assoc, (effPair_spec f g h).2]
  rw [pair_unique _ _ _ e₁ e₂ hk,
    pair_unique _ _ _ (effPair_spec (k ≫ f) (k ≫ g) h').1
      (effPair_spec (k ≫ f) (k ≫ g) h').2 hk]

end PartialToTotal

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

/-- **186IV** (`par-pullbacks`, eff.tex:1562, Proposition), left square:
squares `(id+f̂, ĝ+id; ĝ+id, id+f̂)` are pullbacks in `Par C`. -/
theorem par_pullbacks_left {X Y A B : C} (g : X ⟶ Y) (f : A ⟶ B) :
    IsPullback (Par.map (𝟙 (Par.of X)) (Par.hat f))
      (Par.map (Par.hat g) (𝟙 (Par.of A)))
      (Par.map (Par.hat g) (𝟙 (Par.of B)))
      (Par.map (𝟙 (Par.of Y)) (Par.hat f)) := sorry

/-- **186IV** (`par-pullbacks`, eff.tex:1562, Proposition), right square:
squares `(f̂+id, ▷₁; ▷₁, f̂)` are pullbacks in `Par C`. -/
theorem par_pullbacks_right {A B X : C} (f : A ⟶ B) :
    IsPullback (Par.map (Par.hat f) (𝟙 (Par.of X)))
      (Par.pproj₁ A X) (Par.pproj₁ B X) (Par.hat f) := sorry

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

/-- **186X** (`pproj-joint-monicity`, eff.tex:1667, Proposition): the
partial projectors `▷₁, ▷₂` are jointly monic in `Par C`. -/
theorem pproj_joint_monicity (X Y : C) :
    JointlyMonic (Par.pproj₁ X Y) (Par.pproj₂ X Y) := sorry

end TotalToPartial

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
  -- transported along `0 + A ≅ A` (bsols.tex:1801)
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

/-- **180V** (`effectus-vn`, eff.tex:827) and **189aI**
(`effexamplesintro`, eff.tex:2020, Examples): the main example — the
opposite `vNᵒᵖ` of the category of von Neumann algebras with ncpu-maps is
an effectus in total form. -/
theorem effectus_vn : Nonempty (EffectusTotalStructure WStarNCPU.{u}ᵒᵖ) := sorry

/-- **180V** (`effectus-vn`, eff.tex:827): the partial maps of the effectus
`vNᵒᵖ` correspond to the ncpsu-maps: `(W*_ncpsu)ᵒᵖ` is an effectus in
partial form (its effect object being `ℂ`). -/
theorem effectus_vn_partial :
    Nonempty (EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) := sorry

/-- **189aII.3** (`effexamplesintro`, eff.tex:2043, Examples): every
(finitary) extensive category with a final object is an effectus in total
form.  (The other examples of 189a — `OUSᵒᵖ`, `OUGᵒᵖ`, `Set`, `CRngᵒᵖ`,
`CH`, `EJAᵒᵖ` — are instances of general facts not formalized here.) -/
theorem extensive_effectus (C : Type u) [Category.{v} C]
    [HasFiniteCoproducts C] [HasTerminal C] [FinitaryExtensive C] :
    EffectusTotalForm C := sorry

end Theses.B.Eff
