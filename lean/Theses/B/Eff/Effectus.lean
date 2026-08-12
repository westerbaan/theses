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

/-- **181II** (`coproj-total`, eff.tex:985, Lemma): in an effectus in
partial form, coprojections are total. -/
theorem coproj_total_inl (X Y : C) : IsTotal (coprod.inl : X ⟶ X ⨿ Y) := sorry

/-- **181II** (`coproj-total`, eff.tex:985, Lemma): in an effectus in
partial form, coprojections are total (second coprojection). -/
theorem coproj_total_inr (X Y : C) : IsTotal (coprod.inr : Y ⟶ X ⨿ Y) := sorry

variable {X Y Z : C}

/-- **181IV.1** (`cotupl-pcm`, eff.tex:999, Proposition): cotupling
reflects and preserves `⊥`: `[f,g] ⊥ [f',g']` iff `f ⊥ f'` and
`g ⊥ g'`. -/
theorem cotupl_pcm_1 (f f' : X ⟶ Z) (g g' : Y ⟶ Z) :
    Perp (coprod.desc f g) (coprod.desc f' g') ↔ Perp f f' ∧ Perp g g' := sorry

/-- **181IV.2** (`cotupl-pcm`, eff.tex:999, Proposition):
`[f,g] ⋁ [f',g'] = [f ⋁ f', g ⋁ g']`. -/
theorem cotupl_pcm_2 {f f' : X ⟶ Z} {g g' : Y ⟶ Z}
    (h : Perp (coprod.desc f g) (coprod.desc f' g'))
    (hf : Perp f f') (hg : Perp g g') :
    ovee _ _ h = coprod.desc (ovee f f' hf) (ovee g g' hg) := sorry

/-- **181IV.3** (`cotupl-pcm`, eff.tex:999, Proposition): `[0,0] = 0`. -/
theorem cotupl_pcm_3 (X Y Z : C) :
    coprod.desc (0 : X ⟶ Z) (0 : Y ⟶ Z) = 0 := sorry

/-- **181IV** (`cotupl-pcm`, eff.tex:999, Proposition): furthermore
`[1,1] = 1` for maps into `I`. -/
theorem cotupl_pcm_one (X Y : C) :
    coprod.desc (truth X) (truth Y) = truth (X ⨿ Y) := sorry

/-- **181IV** (`cotupl-pcm`, eff.tex:999, Proposition): the cotupling map is
an effect algebra isomorphism `Pred X × Pred Y ≅ Pred (X + Y)`. -/
theorem cotupl_pcm_ea_iso (X Y : C) :
    ∃ φ : EAHom ((X ⟶ effObj C) × (Y ⟶ effObj C)) ((X ⨿ Y) ⟶ effObj C),
      Function.Bijective φ.toFun ∧
      ∀ (p : X ⟶ effObj C) (q : Y ⟶ effObj C),
        φ.toFun (p, q) = coprod.desc p q := sorry

/-- **181VII** (`coprod-prod`, eff.tex:1066, Proposition): the coproduct in
an effectus in partial form is almost a biproduct — for `f : Z ⟶ X` and
`g : Z ⟶ Y` with `1 ∘ f ⊥ 1 ∘ g` there is a unique `⟨f,g⟩ : Z ⟶ X + Y`
with `▷₁ ∘ ⟨f,g⟩ = f` and `▷₂ ∘ ⟨f,g⟩ = g`. -/
theorem coprod_prod {f : Z ⟶ X} {g : Z ⟶ Y}
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) :
    ∃! p : Z ⟶ X ⨿ Y, p ≫ pproj₁ X Y = f ∧ p ≫ pproj₂ X Y = g := sorry

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
      effPair f g h = ovee _ _ hk := sorry

/-- **181VII** (`coprod-prod`, eff.tex:1085, Proposition), converse
direction: every `h : Z ⟶ X + Y` satisfies `1 ∘ ▷₁ ∘ h ⊥ 1 ∘ ▷₂ ∘ h` (and
`h = ⟨▷₁ ∘ h, ▷₂ ∘ h⟩` by the uniqueness in `coprod_prod`). -/
theorem coprod_prod_converse (p : Z ⟶ X ⨿ Y) :
    Perp ((p ≫ pproj₁ X Y) ≫ truth X) ((p ≫ pproj₂ X Y) ≫ truth Y) := sorry

/-- **181IX.1** (`eff-prod-rules`, eff.tex:1137, Exercise):
`[a,b] ∘ ⟨f,g⟩ = (a ∘ f) ⋁ (b ∘ g)`. -/
theorem eff_prod_rules_1 {W : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) (a : X ⟶ W) (b : Y ⟶ W) :
    ∃ hp : Perp (f ≫ a) (g ≫ b),
      effPair f g h ≫ coprod.desc a b = ovee (f ≫ a) (g ≫ b) hp := sorry

/-- **181IX.2** (`eff-prod-rules`, eff.tex:1137, Exercise):
`1 ∘ ⟨f,g⟩ = (1 ∘ f) ⋁ (1 ∘ g)`. -/
theorem eff_prod_rules_2 (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) :
    effPair f g h ≫ truth (X ⨿ Y) = ovee (f ≫ truth X) (g ≫ truth Y) h := sorry

/-- **181IX.3** (`eff-prod-rules`, eff.tex:1137, Exercise):
`(k + l) ∘ ⟨f,g⟩ = ⟨k ∘ f, l ∘ g⟩`. -/
theorem eff_prod_rules_3 {X' Y' : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) (k : X ⟶ X') (l : Y ⟶ Y')
    (h' : Perp ((f ≫ k) ≫ truth X') ((g ≫ l) ≫ truth Y')) :
    effPair f g h ≫ coprod.map k l = effPair (f ≫ k) (g ≫ l) h' := sorry

/-- **181IX.4** (`eff-prod-rules`, eff.tex:1137, Exercise):
`⟨f,g⟩ ∘ k = ⟨f ∘ k, g ∘ k⟩`. -/
theorem eff_prod_rules_4 {W : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) (k : W ⟶ Z)
    (h' : Perp ((k ≫ f) ≫ truth X) ((k ≫ g) ≫ truth Y)) :
    k ≫ effPair f g h = effPair (k ≫ f) (k ≫ g) h' := sorry

end PartialToTotal

/-! ## Interlude on pullbacks and joint monicity (parsecs 183–184) -/

section Pullbacks

variable {D : Type u} [Category.{v} D]

/-- **183II** (`exc-jointly-monic-pullback`, eff.tex:1336, Exercise): the
legs of a pullback square are jointly monic. -/
theorem exc_jointly_monic_pullback {P A B X : D}
    {m₁ : P ⟶ B} {m₂ : P ⟶ A} {f : B ⟶ X} {g : A ⟶ X}
    (h : IsPullback m₁ m₂ f g) : JointlyMonic m₁ m₂ := sorry

/-- **183III.1** (`pullback-lemma`, eff.tex:1347, Exercise): *pullback
lemma*, pasting: if the left and right inner squares are pullbacks, then so
is the outer rectangle. -/
theorem pullback_lemma_1 {A B E X Y Z : D}
    {f : A ⟶ B} {g : B ⟶ E} {k : A ⟶ X} {l : B ⟶ Y} {m : E ⟶ Z}
    {f' : X ⟶ Y} {g' : Y ⟶ Z}
    (h₁ : IsPullback f k l f') (h₂ : IsPullback g l m g') :
    IsPullback (f ≫ g) k m (f' ≫ g') := sorry

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
    IsPullback f k l f' := sorry

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
    JointlyMonic (h₁ ≫ n₁) (h₂ ≫ n₂) := sorry

end Pullbacks

/-! ## From total to partial (parsecs 185–187) -/

section TotalToPartial

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasTerminal C]
  [EffectusTotalForm C]

/-- **185I** (`tot-pullbacks`, eff.tex:1458, Proposition), left square: in
an effectus in total form every square
`(id+f, g+id; g+id, id+f)` on `X+A`, `X+B`, `Y+A`, `Y+B` is a pullback. -/
theorem tot_pullbacks_left {X Y A B : C} (g : X ⟶ Y) (f : A ⟶ B) :
    IsPullback (coprod.map (𝟙 X) f) (coprod.map g (𝟙 A))
      (coprod.map g (𝟙 B)) (coprod.map (𝟙 Y) f) := sorry

/-- **185I** (`tot-pullbacks`, eff.tex:1458, Proposition), right square: in
an effectus in total form every square `(f, κ₁; κ₁, f+g)` is a pullback. -/
theorem tot_pullbacks_right {X Y A B : C} (f : X ⟶ Y) (g : A ⟶ B) :
    IsPullback f (coprod.inl : X ⟶ X ⨿ A)
      (coprod.inl : Y ⟶ Y ⨿ B) (coprod.map f g) := sorry

/-- **186II** (`par-c-coprod`, eff.tex:1536, Exercise): if `κ₁, κ₂` form a
coproduct in `C`, then `κ̂₁, κ̂₂` form a coproduct in `Par C`. -/
theorem par_c_coprod (X Y : C) :
    Nonempty (IsColimit (BinaryCofan.mk
      (Par.hat (coprod.inl : X ⟶ X ⨿ Y)) (Par.hat (coprod.inr : Y ⟶ X ⨿ Y)))) :=
  sorry

/-- **186II** (`par-c-coprod`, eff.tex:1536, Exercise): `0` is also the
initial object of `Par C`. -/
theorem par_c_initial : Nonempty (IsInitial (Par.of (⊥_ C))) := sorry

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

/-- **186VII** (`toteff-zero`, eff.tex:1609, Exercise): `0` is a zero
object in `Par C` (initial part). -/
theorem toteff_zero_initial : Nonempty (IsInitial (Par.of (⊥_ C))) := sorry

/-- **186VII** (`toteff-zero`, eff.tex:1609, Exercise): `0` is a zero
object in `Par C` (terminal part). -/
theorem toteff_zero_terminal : Nonempty (IsTerminal (Par.of (⊥_ C))) := sorry

/-- **186VII** (`toteff-zero`, eff.tex:1609, Exercise): the unique map
`X ⟶ 0 ⟶ Y` in `Par C` is the zero map of 186VI. -/
theorem toteff_zero_comp (X Y : C)
    (u : Par.of X ⟶ Par.of (⊥_ C)) (v : Par.of (⊥_ C) ⟶ Par.of Y) :
    u ≫ v = Par.zero X Y := sorry

/-- **186VIII.1** (`pardp`, eff.tex:1614, Proposition): a partial map `f`
with `1 ⊙ f = 1` is `ĝ` for a unique total map `g` of `C`. -/
theorem pardp_1 {X Y : C} (f : Par.of X ⟶ Par.of Y)
    (h : f ≫ Par.one Y = Par.one X) : ∃! g : X ⟶ Y, f = Par.hat g := sorry

/-- **186VIII.2** (`pardp`, eff.tex:1614, Proposition): a partial map `f`
with `1 ⊙ f = 0` is the zero map. -/
theorem pardp_2 {X Y : C} (f : Par.of X ⟶ Par.of Y)
    (h : f ≫ Par.one Y = Par.zero X (⊤_ C)) : f = Par.zero X Y := sorry

/-- **186X** (`pproj-joint-monicity`, eff.tex:1667, Proposition): the
partial projectors `▷₁, ▷₂` are jointly monic in `Par C`. -/
theorem pproj_joint_monicity (X Y : C) :
    JointlyMonic (Par.pproj₁ X Y) (Par.pproj₂ X Y) := sorry

end TotalToPartial

/-! ## Distinguishing the two forms, and examples (parsecs 189, 189a) -/

/-- **189I.1** (`distinction-part-tot-eff`, eff.tex:1986, Exercise): the
initial object of an effectus in total form is strict: any map into `0` is
an isomorphism. -/
theorem distinction_part_tot_eff_1 {C : Type u} [Category.{v} C]
    [HasFiniteCoproducts C] [HasTerminal C] [EffectusTotalForm C]
    {X : C} (f : X ⟶ ⊥_ C) : IsIso f := sorry

/-- **189I.2** (`distinction-part-tot-eff`, eff.tex:1986, Exercise): if `C`
is an effectus in both total and partial form, then every object of `C` is
isomorphic to `0`. -/
theorem distinction_part_tot_eff_2 {C : Type u} [Category.{v} C]
    [HasFiniteCoproducts C] [HasTerminal C] [EffectusTotalForm C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
    (X : C) : Nonempty (X ≅ ⊥_ C) := sorry

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
