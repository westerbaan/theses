/-
Papers/REC/Effectus.lean

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707 (2021): §2.1 (effectus theory), §2.2
(directed completeness) and §3 (pure maps and ⋄-adjointness) — points
REC 1–36 and REC 62–86 of `../papers/REC-points.csv`.

Why §3 sits in this file and not in its own: a new file cannot import another
new file in the session that creates it (`scripts/lean1.sh` writes no olean),
and §3 needs the filters (REC 23) and the directed-complete effectuses of §2.
`Papers/REC/PLAN.md` has the file layout of the whole paper.

Design:
* The effectus of the paper is the *effectus in partial form* of thesis B
  (REC 9 = eff.tex 180VII), so everything is stated over the tree's
  `[∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]`.  Composition
  is Mathlib's diagrammatic `f ≫ g`, i.e. the paper's `g ∘ f`.
* The paper's **filter** for `p` is thesis B's **quotient** for `p^⊥`
  (the paper says so, footnote to REC 23).  `IsFilter p ξ` is defined as
  printed and `isFilter_iff_isQuotient` is the bridge; `HasFilters` is
  equivalent to the tree's `HasQuotients`.
* Where a point is already a theorem of the tree it is restated here in the
  paper's words and proved by citing the tree ("thin"); the audit row says so.
* The monoidal effectus (REC 28) is a Prop-class over Mathlib's
  `MonoidalCategory`/`SymmetricCategory`, with the paper's identification of
  the tensor unit and the effect object as an equation `𝟙_ C = effObj C`.
-/
import Theses.B.Eff.DiamondAmp
import Theses.B.Eff.ExtensiveExamples
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.EqToHom

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Limits hiding HasImages
open Theses.B.Eff
open scoped unitInterval

namespace Papers.REC

universe u v w

/-! ## §2.1 Effectus theory -/

/-- **REC 1** (short.tex:207, Definition): a category `C` is an **effectus in
total form** iff it has finite coproducts and a final object `1`, the two
squares `X+Y → X+1 / 1+Y → 1+1` and `X → 1 / X+Y → 1+1` are pullbacks, and the
cotuples `[κ₁,κ₂,κ₂], [κ₂,κ₁,κ₂] : 1+1+1 → 1+1` are jointly monic.  This is
thesis B's 180I verbatim (`Theses.B.Eff.EffectusTotalForm`).  The partial maps
`X → Y + 1`, the states `1 → X` and the predicates `X → 1+1` of the point are
the tree's `PartialMap`, and `Par(C)` is the tree's `Par C`. -/
abbrev IsEffectusInTotalForm (D : Type u) [Category.{v} D] [HasFiniteCoproducts D]
    [HasTerminal D] : Prop :=
  EffectusTotalForm D

section SetInstances

/-- The effectus structures on `Set` and `Par(Set)`, installed locally as in
thesis B's `ExtensiveExamples` (190IV.3(a)). -/
local instance instEffectusTotalFormTypeREC : EffectusTotalForm (Type u) :=
  extensive_effectus_set

local instance instHasFiniteCoproductsParTypeREC :
    HasFiniteCoproducts (Par (Type u)) := parHasFiniteCoproducts

/-- **REC 2** (`ex:effectus`, short.tex:245, Example), item 1: the category of
sets and functions is an effectus in total form, and the predicates on a set `A`
correspond to the subsets of `A` (read in the partial form `Par Set`, where
predicates live).  Thin: `extensive_effectus_set`, `set_pred_subset`. -/
theorem rec2_set :
    IsEffectusInTotalForm (Type u) ∧
      ∀ A : Type u, Nonempty (Pred (Par.of A) ≃ Set A) :=
  ⟨extensive_effectus_set, fun A => ⟨set_pred_subset A⟩⟩

/-- **REC 2** (`ex:effectus`, short.tex:245, Example), item 2: the category of
sets and probabilistic functions — the Kleisli category of the finite
distribution monad, i.e. of the monad of finite `[0,1]`-convex combinations —
is an effectus in total form.  Thin: thesis B's `exc_dm_effectus_kleisli` at the
effect monoid `M = [0,1]`.  (Item 3, C*-algebras with positive unital maps, is
not formalised: the tree has `vNᵒᵖ` with normal *completely* positive maps and
`OUSᵒᵖ`, neither of which is this category.) -/
theorem rec2_kleisli_distribution :
    Nonempty (EffectusTotalStructure (Kleisli (exc_dm_effectus_monad I))) :=
  exc_dm_effectus_kleisli I

end SetInstances

section PCMs

variable {M : Type u} {N : Type v} {L : Type w} [PCM M] [PCM N] [PCM L]

/-- **REC 4** (`def:pcm`, short.tex:280, Definition): a map `f : M → N` between
PCMs is **additive** if `f 0 = 0` and `f x ⊻ f y = f (x ⊻ y)` whenever
`x ⊥ y` (Kleene equality: the left side is then defined).  (The PCM itself is
thesis B's `PCM`, 174II, whose axioms are the Kleene-equality axioms of the
point written out.) -/
structure IsAdditive (f : M → N) : Prop where
  map_zero : f 0 = 0
  map_ovee : ∀ {x y : M} (h : Perp x y),
    ∃ h' : Perp (f x) (f y), ovee (f x) (f y) h' = f (ovee x y h)

/-- **REC 4** (`def:pcm`, short.tex:280, Definition): a map `g : M × N → L` is
**biadditive** if all its restrictions `g(x,-)` and `g(-,y)` are additive. -/
def IsBiadditive (g : M → N → L) : Prop :=
  (∀ x : M, IsAdditive (g x)) ∧ ∀ y : N, IsAdditive (fun x => g x y)

end PCMs

/-- **REC 4** (`def:pcm`, short.tex:280, Definition): a category is **enriched
over PCMs** if each homset is a PCM and the composition maps are biadditive. -/
def EnrichedOverPCMs (D : Type u) [Category.{v} D] [∀ X Y : D, PCM (X ⟶ Y)] : Prop :=
  ∀ X Y Z : D, IsBiadditive (fun (f : X ⟶ Y) (g : Y ⟶ Z) => f ≫ g)

section FinPACs

variable (D : Type u) [Category.{v} D] [HasFiniteCoproducts D] [∀ X Y : D, PCM (X ⟶ Y)]

/-- **REC 5** (short.tex:315, Definition): a family `f₁ : B → A₁`,
`f₂ : B → A₂` is **compatible** if there is `f : B → A₁ + A₂` with
`▷ᵢ ∘ f = fᵢ`, for the partial projections `▷ᵢ` (thesis B's `pproj₁/₂`).
(The point allows any finite index set; like thesis B we use binary
coproducts, from which the finite case follows by induction.) -/
def Compatible {B A₁ A₂ : D} (f₁ : B ⟶ A₁) (f₂ : B ⟶ A₂) : Prop :=
  ∃ f : B ⟶ A₁ ⨿ A₂, f ≫ pproj₁ A₁ A₂ = f₁ ∧ f ≫ pproj₂ A₁ A₂ = f₂

/-- **REC 5** (short.tex:315, Definition): a **finPAC** is a category with
finite coproducts, enriched over PCMs, satisfying the *compatible sum axiom*
(compatible pairs `f, g : A → B` are summable) and the *untying axiom* (if
`f ⊥ g` then `κ₁ ∘ f ⊥ κ₂ ∘ g`).  This is exactly thesis B's class `FinPAC`,
whose four composition fields are the biadditivity of composition. -/
theorem finPAC_iff :
    FinPAC D ↔
      EnrichedOverPCMs D ∧
        (∀ {A B : D} (f g : A ⟶ B), Compatible D f g → Perp f g) ∧
        (∀ {A B : D} {f g : A ⟶ B}, Perp f g →
          Perp (f ≫ (coprod.inl : B ⟶ B ⨿ B)) (g ≫ (coprod.inr : B ⟶ B ⨿ B))) := by
  constructor
  · intro hF
    refine ⟨fun X Y Z => ⟨fun f => ⟨FinPAC.comp_zero f, fun h => ?_⟩,
      fun g => ⟨FinPAC.zero_comp g, fun h => ?_⟩⟩, ?_, fun h => FinPAC.untying h⟩
    · obtain ⟨h', e⟩ := FinPAC.ovee_comp h f
      exact ⟨h', e.symm⟩
    · obtain ⟨h', e⟩ := FinPAC.comp_ovee h g
      exact ⟨h', e.symm⟩
    · rintro A B f g ⟨b, rfl, rfl⟩
      exact FinPAC.compatible_sum b
  · rintro ⟨hE, hC, hU⟩
    exact
      { comp_ovee := fun {X Y Z} {f g} h k => by
          obtain ⟨h', e⟩ := (hE X Y Z).2 k |>.map_ovee h
          exact ⟨h', e.symm⟩
        ovee_comp := fun {W X Y} {f g} h k => by
          obtain ⟨h', e⟩ := (hE W X Y).1 k |>.map_ovee h
          exact ⟨h', e.symm⟩
        comp_zero := fun {X Y Z} f => ((hE X Y Z).1 f).map_zero
        zero_comp := fun {X Y Z} f => ((hE X Y Z).2 f).map_zero
        compatible_sum := fun {X Y} b => hC _ _ ⟨b, rfl, rfl⟩
        untying := fun h => hU h }

end FinPACs

section EffectAlgebras

variable {E : Type u} [EffectAlgebra E]

/-- **REC 6** (`def:EA`, short.tex:347, Definition): in an effect algebra the
relation `x ≤ y :⟺ ∃ z, x ⊻ z = y` is a partial order with minimum `0` and
maximum `1 = 0^⊥`.  (The effect algebra itself is thesis B's
`EffectAlgebra`, 175I, verbatim.)  Thin: 176 `pcm_preorder_*`,
`eabasics_le_antisymm`, `eabasics_orth_zero`. -/
theorem rec6_partialOrder :
    (∀ a : E, a ≼ a) ∧ (∀ {a b c : E}, a ≼ b → b ≼ c → a ≼ c) ∧
      (∀ {a b : E}, a ≼ b → b ≼ a → a = b) ∧ (∀ a : E, (0 : E) ≼ a) ∧
      (∀ a : E, a ≼ 1) ∧ (1 : E) = orth 0 :=
  ⟨pcm_preorder_refl, fun h h' => pcm_preorder_trans h h', eabasics_le_antisymm,
    fun a => ⟨a, PCM.zero_perp a, PCM.zero_ovee a⟩,
    fun a => ⟨orth a, EffectAlgebra.perp_orth a, EffectAlgebra.ovee_orth a⟩,
    eabasics_orth_zero.symm⟩

/-- **REC 6** (`def:EA`, short.tex:347, Definition): `x ↦ x^⊥` is an order
anti-isomorphism (it is an involution, `eabasics_orth_orth`, and reverses the
order both ways). -/
theorem rec6_orth_antiIso :
    (∀ a : E, orth (orth a) = a) ∧ ∀ a b : E, a ≼ b ↔ orth b ≼ orth a :=
  ⟨eabasics_orth_orth, fun _ _ => eabasics_le_iff_orth_le⟩

/-- **REC 6** (`def:EA`, short.tex:347, Definition): `x ⊥ y` iff `x ≤ y^⊥`. -/
theorem rec6_perp_iff (a b : E) : Perp a b ↔ a ≼ orth b :=
  eabasics_perp_iff_le_orth

/-- **REC 6** (`def:EA`, short.tex:347, Definition): additive maps between
effect algebras are monotone. -/
theorem rec6_additive_monotone {F : Type v} [EffectAlgebra F] {f : E → F}
    (hf : IsAdditive f) {a b : E} (h : a ≼ b) : f a ≼ f b := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨h', e⟩ := hf.map_ovee hc
  exact ⟨f c, h', e⟩

end EffectAlgebras

/-! ### REC 7: orthomodular lattices as effect algebras -/

/-- The six-element orthomodular lattice `MO₂`: `⊥ < a, a', b, b' < ⊤`, with
`a ↔ a'` and `b ↔ b'` the orthocomplement.  Used to refute REC 7 as printed. -/
inductive MO2 : Type
  | bot | a | na | b | nb | top
  deriving DecidableEq

namespace MO2

/-- The order of `MO₂` as a Boolean relation. -/
def leb : MO2 → MO2 → Bool
  | bot, _ => true
  | _, top => true
  | x, y => decide (x = y)

def sup (x y : MO2) : MO2 := if leb x y then y else if leb y x then x else top
def inf (x y : MO2) : MO2 := if leb x y then x else if leb y x then y else bot
def compl : MO2 → MO2
  | bot => top | a => na | na => a | b => nb | nb => b | top => bot

instance : Fintype MO2 :=
  ⟨⟨{bot, a, na, b, nb, top}, by decide⟩, fun x => by cases x <;> decide⟩

theorem leb_refl : ∀ x, leb x x = true := by decide
theorem leb_trans : ∀ x y z, leb x y = true → leb y z = true → leb x z = true := by decide
theorem leb_antisymm : ∀ x y, leb x y = true → leb y x = true → x = y := by decide
theorem leb_sup_left : ∀ x y, leb x (sup x y) = true := by decide
theorem leb_sup_right : ∀ x y, leb y (sup x y) = true := by decide
theorem sup_leb : ∀ x y z, leb x z = true → leb y z = true → leb (sup x y) z = true := by
  decide
theorem inf_leb_left : ∀ x y, leb (inf x y) x = true := by decide
theorem inf_leb_right : ∀ x y, leb (inf x y) y = true := by decide
theorem leb_inf : ∀ x y z, leb x y = true → leb x z = true → leb x (inf y z) = true := by
  decide
theorem inf_compl' : ∀ x, inf x (compl x) = bot := by decide
theorem sup_compl' : ∀ x, sup x (compl x) = top := by decide
theorem compl_antitone' : ∀ x y, leb x y = true → leb (compl y) (compl x) = true := by
  decide
theorem compl_compl' : ∀ x, compl (compl x) = x := by decide
theorem orthomodular' : ∀ x y, leb x y = true → sup x (inf (compl x) y) = y := by decide

instance : Lattice MO2 where
  le x y := leb x y = true
  le_refl := leb_refl
  le_trans := leb_trans
  le_antisymm := leb_antisymm
  sup := sup
  le_sup_left := leb_sup_left
  le_sup_right := leb_sup_right
  sup_le := sup_leb
  inf := inf
  inf_le_left := inf_leb_left
  inf_le_right := inf_leb_right
  le_inf := leb_inf

instance : BoundedOrder MO2 where
  top := top
  le_top x := by cases x <;> rfl
  bot := bot
  bot_le x := by cases x <;> rfl

instance : OrthomodularLattice MO2 where
  compl := compl
  inf_compl := inf_compl'
  sup_compl := sup_compl'
  compl_antitone := fun {x y} h => compl_antitone' x y h
  compl_compl := compl_compl'
  orthomodular := fun {x y} h => orthomodular' x y h

end MO2

/-- **REC 7** (`ex:orthomodularlattice`, short.tex:374, Example), **as printed,
is false**: the point makes an orthomodular lattice into an effect algebra with
`x ⊥ y ⟺ x ∧ y = 0` and `x ⊻ y = x ∨ y`; but in `MO₂` both `a ⊻ a' = 1` and
`a ⊻ b = 1`, so the orthosupplement of `a` is not unique, and no effect algebra
structure has this orthogonality and sum.  (The cited source, thesis B's 175II.4
and SEA's Example 3 use `x ⊥ y ⟺ x ≤ y^⊥`; the two agree exactly for Boolean
algebras, REC 16.  The corrected statement is `rec7_corrected`.) -/
theorem rec7_as_printed_false :
    ∃ (L : Type) (_ : OrthomodularLattice L),
      ¬ ∃ E : EffectAlgebra L, (∀ x y : L, @Perp L E.toPCM x y ↔ x ⊓ y = ⊥) ∧
        ∀ (x y : L) (h : @Perp L E.toPCM x y), @ovee L E.toPCM x y h = x ⊔ y := by
  refine ⟨MO2, inferInstance, ?_⟩
  rintro ⟨E, hP, hO⟩
  let _ := E
  -- the unit of `E` is `⊤`
  have h1 : (1 : MO2) = ⊤ := by
    have := EffectAlgebra.ovee_orth (⊤ : MO2)
    rw [hO] at this
    rw [← this]
    exact top_sup_eq _
  have hab : Perp MO2.a MO2.b := (hP _ _).2 rfl
  have hana : Perp MO2.a MO2.na := (hP _ _).2 rfl
  have eb : MO2.b = orth MO2.a :=
    EffectAlgebra.orth_unique hab (by rw [hO, h1]; rfl)
  have ena : MO2.na = orth MO2.a :=
    EffectAlgebra.orth_unique hana (by rw [hO, h1]; rfl)
  exact absurd (eb.trans ena.symm) (by decide)

/-- **REC 7** (`ex:orthomodularlattice`, short.tex:374, Example), corrected: an
orthomodular lattice is an effect algebra with `x ⊥ y ⟺ x ≤ y^⊥`,
`x ⊻ y = x ∨ y` and orthosupplement the orthocomplement, and the lattice order
coincides with the effect algebra order.  Thin for the structure: thesis B's
`orthomodularEffectAlgebra` (175II.4); the order clause is proved here. -/
theorem rec7_corrected (L : Type u) [OrthomodularLattice L] :
    let _ := orthomodularEffectAlgebra L
    (∀ x y : L, Perp x y ↔ x ≤ yᶜ) ∧ (∀ (x y : L) (h : Perp x y), ovee x y h = x ⊔ y) ∧
      (∀ x : L, orth x = xᶜ) ∧ ∀ x y : L, x ≼ y ↔ x ≤ y := by
  let _ := orthomodularEffectAlgebra L
  refine ⟨fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ => rfl, fun x y => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨c, _, rfl⟩
    exact le_sup_left
  · refine ⟨xᶜ ⊓ y, ?_, OrthomodularLattice.orthomodular h⟩
    show x ≤ (xᶜ ⊓ y)ᶜ
    have := Ortholattice.compl_antitone (inf_le_left : xᶜ ⊓ y ≤ xᶜ)
    rwa [Ortholattice.compl_compl] at this


/-- **REC 8** (short.tex:382, Example): for a unital C*-algebra `𝔄` the set of
effects `[0,1]_𝔄 = {a : 0 ≤ a ≤ 1}` is an effect algebra (with `a ⊥ b` iff
`a + b ≤ 1`, and `a ⊻ b = a + b`).  Thin: the order-interval effect algebra of
thesis B 175II.2 on the ordered additive group `𝔄`; the elements of `[0,1]_𝔄`
are automatically self-adjoint. -/
noncomputable def rec8_effects (𝔄 : Type u) [CStarAlgebra 𝔄] [PartialOrder 𝔄]
    [StarOrderedRing 𝔄] : EffectAlgebra (Set.Icc (0 : 𝔄) 1) :=
  orderIntervalEffectAlgebra 𝔄 1 zero_le_one

/-- **REC 9** (`def:effectus`, short.tex:387, Definition): an **effectus in
partial form** is a finPAC `C` with a distinguished unit object `I` such that
every `C(A, I)` is an effect algebra, `1 ∘ f = 0` implies `f = 0`, and
`1 ∘ f ⊥ 1 ∘ g` implies `f ⊥ g`; a map is **total** when `1 ∘ f = 1`.
This is thesis B's 180VII, `EffectusPartialForm`, verbatim; "total" is
`IsTotal`.  The name below is only the paper's name for the tree's class. -/
abbrev IsEffectusInPartialForm (D : Type u) [Category.{v} D] [HasFiniteCoproducts D]
    [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D] : Type (max u v) :=
  EffectusPartialForm D

/-- **REC 10** (short.tex:416, Remark): for an effectus in total form `C`, the
category `Par(C)` of partial maps is an effectus in partial form (with `I = 1`),
and nothing is lost: `Tot(Par(C)) ≃ C`.  Thin: Cho's theorem as thesis B
180X states it, `cho_thm_1` and `cho_thm_3_tot_par` (the converse direction is
`eff_partial_to_total`).  The "2-categorical" strengthening of the remark is not
in the tree and not formalised. -/
theorem rec10_par_tot (D : Type u) [Category.{v} D] [HasFiniteCoproducts D]
    [HasTerminal D] [EffectusTotalForm D] :
    ∃ s : EffectusPartialStructure (Par D),
      @EffectusPartialForm.I _ _ s.hasFiniteCoproducts s.homPCM s.finPAC s.effectus =
        Par.of (⊤_ D) :=
  cho_thm_1 D

/-- **REC 10** (short.tex:416, Remark), converse: for an effectus in partial
form `D`, the total maps form an effectus in total form `Tot(D)`.  Thin:
`eff_partial_to_total` (180X.2). -/
theorem rec10_tot (D : Type u) [Category.{v} D] [HasFiniteCoproducts D]
    [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D] [EffectusPartialForm D] :
    Nonempty (EffectusTotalStructure (Tot D)) :=
  eff_partial_to_total D

section SetInstances'

local instance instEffectusTotalFormTypeREC' : EffectusTotalForm (Type u) :=
  extensive_effectus_set

local instance instHasFiniteCoproductsParTypeREC' :
    HasFiniteCoproducts (Par (Type u)) := parHasFiniteCoproducts

/-- **REC 11** (short.tex:425, Example), first sentence: the category of sets and
partial functions, `Par(Set)`, is an effectus in partial form; its scalars are
the two-element effect monoid.  Thin: the instances on `Par (Type u)` and
`set_scalars_two`.  (The Kleisli category of the subdistribution monad,
C*-algebras with contractive positive maps and `EAᵒᵖ` are not formalised here.) -/
theorem rec11_pfn :
    Nonempty (EffectusPartialForm (Par (Type u))) ∧ ScalarsAreTwo (Par (Type u)) :=
  ⟨⟨inferInstance⟩, set_scalars_two⟩

end SetInstances'

section Effectus

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **REC 12** (short.tex:441, Definition): `Pred(A)` is the effect algebra of
predicates `A → I` (thesis B's `Pred A` with `predEffectAlgebra`), and
`Pred(f)(p) = p ∘ f` (thesis B's `predMap`).  `Pred` is a functor
`C → EAᵒᵖ`, where the morphisms of `EA` are the *additive* maps (REC 6):
`Pred(id) = id`, `Pred(g ∘ f) = Pred(f) ∘ Pred(g)`, and every `Pred(f)` is
additive. -/
theorem rec12_pred_functor :
    (∀ (A : C) (p : Pred A), predMap (𝟙 A) p = p) ∧
      (∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (p : Pred D),
        predMap (f ≫ g) p = predMap f (predMap g p)) ∧
      ∀ {A B : C} (f : A ⟶ B), IsAdditive (predMap f) :=
  ⟨fun _ p => Category.id_comp p, fun f g p => Category.assoc f g p,
    fun f => ⟨FinPAC.comp_zero f, fun h => by
      obtain ⟨h', e⟩ := FinPAC.ovee_comp h f
      exact ⟨h', e.symm⟩⟩⟩

/-- **REC 13** (short.tex:449, Definition): an effectus is **separated by
predicates** if `p ∘ f = p ∘ g` for all predicates `p` implies `f = g`.  Thin:
thesis B's `SeparatingPredicates` (190II.7), verbatim. -/
theorem rec13_separatedByPredicates_iff :
    SeparatingPredicates C ↔
      ∀ {A B : C} (f g : A ⟶ B), (∀ p : Pred B, f ≫ p = g ≫ p) → f = g :=
  ⟨fun h _ _ f g => h f g, fun h _ _ f g => h f g⟩

/-- **REC 14** (short.tex:456, Definition): an effectus is **separated by
states** when `f = g` iff `f ∘ ω = g ∘ ω` for all states `ω : I → A`.  Thin:
thesis B's `SeparatingStates` (190II.7), whose states are the total maps
`I → A` (`Stat`). -/
theorem rec14_separatedByStates_iff :
    SeparatingStates C ↔
      ∀ {A B : C} (f g : A ⟶ B), f = g ↔ ∀ ω : Stat A, ω.1 ≫ f = ω.1 ≫ g := by
  constructor
  · intro h A B f g
    exact ⟨fun e _ => e ▸ rfl, h f g⟩
  · intro h A B f g hfg
    exact (h f g).2 hfg

end Effectus

/-! ### Effect monoids -/

section EffectMonoids

variable {M : Type u}

/-- **REC 15** (`def:effectmonoid`, short.tex:469, Definition): an **effect
monoid** satisfies the paper's axioms — unit, bi-additivity of `·` on both
sides, associativity.  Thesis B's `EffectMonoid` (178II) takes the four-fold
distributive law `(a ⊻ b)(c ⊻ d) = ac ⊻ bc ⊻ ad ⊻ bd` instead; this theorem is
the direction "tree ⇒ paper" (thin: `emon_mul_ovee`, `emon_ovee_mul`), and
`EffectMonoid.ofBiadditive` below is the direction "paper ⇒ tree". -/
theorem rec15_axioms [EffectMonoid M] :
    (∀ a : M, a * 1 = a ∧ 1 * a = a) ∧
      (∀ (a : M) {b c : M} (h : Perp b c),
        (∃ h' : Perp (a * b) (a * c), a * ovee b c h = ovee (a * b) (a * c) h') ∧
          ∃ h' : Perp (b * a) (c * a), ovee b c h * a = ovee (b * a) (c * a) h') ∧
      ∀ a b c : M, a * (b * c) = a * b * c :=
  ⟨fun a => ⟨EffectMonoid.mul_one a, EffectMonoid.one_mul a⟩,
    fun a _ _ h => ⟨emon_mul_ovee a h, emon_ovee_mul a h⟩,
    fun a b c => (EffectMonoid.mul_assoc a b c).symm⟩

/-- **REC 15** (`def:effectmonoid`, short.tex:469, Definition), the direction
"paper ⇒ tree": an effect algebra with a unital, associative, bi-additive
multiplication is an effect monoid in thesis B's sense (the four-fold law is
two applications of bi-additivity). -/
def EffectMonoid.ofBiadditive (M : Type u) [EffectAlgebra M] [Mul M]
    (mul_one : ∀ a : M, a * 1 = a) (one_mul : ∀ a : M, 1 * a = a)
    (mul_ovee : ∀ (a : M) {b c : M} (h : Perp b c),
      ∃ h' : Perp (a * b) (a * c), a * ovee b c h = ovee (a * b) (a * c) h')
    (ovee_mul : ∀ (a : M) {b c : M} (h : Perp b c),
      ∃ h' : Perp (b * a) (c * a), ovee b c h * a = ovee (b * a) (c * a) h')
    (mul_assoc : ∀ a b c : M, a * (b * c) = a * b * c) : EffectMonoid M :=
  { (inferInstance : EffectAlgebra M), (inferInstance : Mul M) with
    one_mul := one_mul
    mul_one := mul_one
    mul_assoc := fun a b c => (mul_assoc a b c).symm
    distrib := by
      intro a b c d hab hcd
      obtain ⟨h1, e1⟩ := mul_ovee (ovee a b hab) hcd
      obtain ⟨h2, e2⟩ := ovee_mul c hab
      obtain ⟨h3, e3⟩ := ovee_mul d hab
      have hp : Perp (ovee (a * c) (b * c) h2) (ovee (a * d) (b * d) h3) := by
        rw [← e2, ← e3]; exact h1
      have key : ovee a b hab * ovee c d hcd
          = ovee (ovee (a * c) (b * c) h2) (ovee (a * d) (b * d) h3) hp :=
        e1.trans (PCM.ovee_congr e2 e3 h1 hp)
      rw [key]
      exact isSumOf_append (isSumOf_pair _ _ h2) (isSumOf_pair _ _ h3) hp }

/-- **REC 15** (`def:effectmonoid`, short.tex:469, Definition): an element `p`
of an effect monoid is **idempotent** when `p² = p · p = p`. -/
def IsIdempotent [Mul M] (p : M) : Prop := p * p = p

/-- **REC 16** (`ex:booleanalgebra`, short.tex:509, Example): a Boolean algebra
is an effect algebra with `x ⊥ y ⟺ x ∧ y = 0` and `x ⊻ y = x ∨ y`, and a
*commutative* effect monoid with `x · y = x ∧ y`.  Thin: thesis B's
`booleanEffectMonoid` (178III.2).  (For Boolean algebras the printed
orthogonality `x ∧ y = 0` of REC 7 is the right one; see REC 7.) -/
theorem rec16_boolean (B : Type u) [BooleanAlgebra B] :
    letI := booleanEffectMonoid B
    (∀ x y : B, Perp x y ↔ x ⊓ y = ⊥) ∧ (∀ (x y : B) (h : Perp x y), ovee x y h = x ⊔ y) ∧
      (∀ x y : B, x * y = x ⊓ y) ∧ EffectMonoid.Commutative B := by
  let _ := booleanEffectMonoid B
  exact ⟨fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun x y => inf_comm x y⟩

/-- **REC 17** (short.tex:521, Example): in any effectus the scalars form an
effect monoid with `s · t := s ∘ t`.  Thin: thesis B's `scalEffectMonoid`
(190II.2); in Mathlib's diagrammatic order `s ∘ t` is `t ≫ s`. -/
theorem rec17_scalars {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] (s t : Scal C) :
    s * t = t ≫ s :=
  rfl

/-- **REC 18** (`ex:CX`, short.tex:526, Example): for a (compact Hausdorff)
space `X`, the unit interval `[0,1]_{C(X)} = C(X,[0,1])` is a *commutative*
effect monoid.  The effect monoid is thesis B's
`continuousUnitIntervalEffectMonoid` on `[0,1]` of `C(X,ℝ)` (pointwise
operations); the paper's `C(X)` is complex-valued, and its unit interval is
the same set of real-valued functions. -/
theorem rec18_continuous_commutative (X : Type u) [TopologicalSpace X] :
    @EffectMonoid.Commutative _ (continuousUnitIntervalEffectMonoid X) := by
  let _ := continuousUnitIntervalEffectMonoid X
  intro f g
  apply Subtype.ext
  show (f : C(X, ℝ)) * g = (g : C(X, ℝ)) * f
  exact mul_comm _ _

end EffectMonoids

/-! ### Direct sums and irreducibility (REC 20) -/

section DirectSums

/-- An **isomorphism of effect monoids**: a mutually inverse pair of effect
monoid homomorphisms (as in thesis B's `IsRealEffectus`, a bijective morphism
need not have a morphism inverse, so both directions are given). -/
structure EMIso (M : Type u) (N : Type v) [EffectMonoid M] [EffectMonoid N] where
  hom : EffectMonoidHom M N
  inv : EffectMonoidHom N M
  inv_hom : ∀ a : M, inv.toFun (hom.toFun a) = a
  hom_inv : ∀ b : N, hom.toFun (inv.toFun b) = b

/-- **REC 20** (short.tex:558, Example): the **direct sum** `E₁ ⊕ E₂` of two
effect monoids is the cartesian product with pointwise operations, again an
effect monoid.  (For effect algebras this is thesis B's `prodEffectAlgebra`,
175III; the multiplication is Mathlib's pointwise `Prod.instMul`.) -/
instance prodEffectMonoid (M N : Type u) [EffectMonoid M] [EffectMonoid N] :
    EffectMonoid (M × N) :=
  EffectMonoid.ofBiadditive (M × N)
    (fun a => Prod.ext (EffectMonoid.mul_one a.1) (EffectMonoid.mul_one a.2))
    (fun a => Prod.ext (EffectMonoid.one_mul a.1) (EffectMonoid.one_mul a.2))
    (fun a _ _ h => by
      obtain ⟨h1, e1⟩ := emon_mul_ovee a.1 h.1
      obtain ⟨h2, e2⟩ := emon_mul_ovee a.2 h.2
      exact ⟨⟨h1, h2⟩, Prod.ext e1 e2⟩)
    (fun a _ _ h => by
      obtain ⟨h1, e1⟩ := emon_ovee_mul a.1 h.1
      obtain ⟨h2, e2⟩ := emon_ovee_mul a.2 h.2
      exact ⟨⟨h1, h2⟩, Prod.ext e1 e2⟩)
    (fun a b c => Prod.ext (EffectMonoid.mul_assoc a.1 b.1 c.1).symm
      (EffectMonoid.mul_assoc a.2 b.2 c.2).symm)

/-- **REC 20** (short.tex:558, Example): an effect monoid is **irreducible**
when it cannot be written as a non-trivial direct sum: whenever `M ≅ E₁ ⊕ E₂`
(as effect monoids), one of the summands is the zero effect monoid `{0}`
(i.e. has at most one element). -/
def IsIrreducible (M : Type u) [EffectMonoid M] : Prop :=
  ∀ (E₁ E₂ : Type u) [EffectMonoid E₁] [EffectMonoid E₂],
    EMIso M (E₁ × E₂) → Subsingleton E₁ ∨ Subsingleton E₂

end DirectSums

/-! ### REC 21: corners of an effect monoid -/

section Corner

variable {M : Type u} [EffectMonoid M]

/-- Helper: `a ⊻ b = a` forces `b = 0` (cancellation). -/
theorem ovee_eq_self_left {E : Type v} [EffectAlgebra E] {a b : E} (h : Perp a b)
    (e : ovee a b h = a) : b = 0 := by
  have h0 : Perp a 0 := PCM.perp_zero a
  have e' : ovee b a (PCM.perp_comm h) = ovee 0 a (PCM.perp_comm h0) :=
    (PCM.ovee_comm h).symm.trans ((e.trans (PCM.ovee_zero a h0).symm).trans
      (PCM.ovee_comm h0))
  exact eabasics_cancellation _ _ e'

/-- Helper: left cancellation. -/
theorem ovee_left_cancel {E : Type v} [EffectAlgebra E] {a b c : E} (h₁ : Perp c a)
    (h₂ : Perp c b) (e : ovee c a h₁ = ovee c b h₂) : a = b :=
  eabasics_cancellation (PCM.perp_comm h₁) (PCM.perp_comm h₂)
    ((PCM.ovee_comm h₁).symm.trans (e.trans (PCM.ovee_comm h₂)))

theorem eq_zero_of_le_zero {E : Type v} [EffectAlgebra E] {a : E} (h : a ≼ 0) : a = 0 :=
  eabasics_le_antisymm h ⟨a, PCM.zero_perp a, PCM.zero_ovee a⟩

variable {p : M}

/-- For an idempotent `p`, `p · p^⊥ = 0` (OAP 18). -/
theorem idem_mul_orth (hp : p * p = p) : p * orth p = 0 := by
  obtain ⟨h, e⟩ := emon_mul_ovee p (EffectAlgebra.perp_orth p)
  rw [EffectAlgebra.ovee_orth, EffectMonoid.mul_one] at e
  have h' : Perp p (p * orth p) := by rw [hp] at h; exact h
  exact ovee_eq_self_left h' ((PCM.ovee_congr hp.symm rfl h' h).trans e.symm)

/-- For an idempotent `p`, `p^⊥ · p = 0`. -/
theorem orth_mul_idem (hp : p * p = p) : orth p * p = 0 := by
  obtain ⟨h, e⟩ := emon_ovee_mul p (EffectAlgebra.perp_orth p)
  rw [EffectAlgebra.ovee_orth, EffectMonoid.one_mul] at e
  have h' : Perp p (orth p * p) := by rw [hp] at h; exact h
  exact ovee_eq_self_left h' ((PCM.ovee_congr hp.symm rfl h' h).trans e.symm)

/-- The orthosupplement of an idempotent is idempotent. -/
theorem orth_idem (hp : p * p = p) : orth p * orth p = orth p := by
  obtain ⟨h, e⟩ := emon_ovee_mul (orth p) (EffectAlgebra.perp_orth p)
  rw [EffectAlgebra.ovee_orth, EffectMonoid.one_mul] at e
  have h' : Perp 0 (orth p * orth p) := PCM.zero_perp _
  exact (e.trans ((PCM.ovee_congr (idem_mul_orth hp) rfl h h').trans
    (PCM.zero_ovee _))).symm

/-- Idempotents of an effect monoid are central (OAP 20; used by the paper in
REC 21 and REC 92): `p · a · p^⊥ ≤ p · p^⊥ = 0` and `p^⊥ · a · p = 0`, whence
`p · a = p · a · p = a · p`. -/
theorem idem_central (hp : p * p = p) (a : M) : p * a = a * p := by
  have z1 : p * a * orth p = 0 :=
    eq_zero_of_le_zero ((idem_mul_orth hp) ▸ emon_mul_mono_left (emon_mul_le_self p a) _)
  have z2 : orth p * (a * p) = 0 :=
    eq_zero_of_le_zero ((orth_mul_idem hp) ▸
      emon_mul_mono_right _ (emon_mul_le_self_right a p))
  have e1 : p * a = p * a * p := by
    obtain ⟨h, e⟩ := emon_mul_ovee (p * a) (EffectAlgebra.perp_orth p)
    rw [EffectAlgebra.ovee_orth, EffectMonoid.mul_one] at e
    exact e.trans ((PCM.ovee_congr rfl z1 h (PCM.perp_zero _)).trans (PCM.ovee_zero _ _))
  have e2 : a * p = p * (a * p) := by
    obtain ⟨h, e⟩ := emon_ovee_mul (a * p) (EffectAlgebra.perp_orth p)
    rw [EffectAlgebra.ovee_orth, EffectMonoid.one_mul] at e
    exact e.trans ((PCM.ovee_congr rfl z2 h (PCM.perp_zero _)).trans (PCM.ovee_zero _ _))
  calc p * a = p * a * p := e1
    _ = p * (a * p) := EffectMonoid.mul_assoc p a p
    _ = a * p := e2.symm

/-- **REC 21** (`cornersexample`, short.tex:566, Example): the **corner**
`pM := {p · a ; a ∈ M}` of an effect monoid at an idempotent `p`. -/
def Corner (p : M) : Type u := { x : M // ∃ a, x = p * a }

theorem corner_fix (hp : p * p = p) {x : M} (hx : ∃ a, x = p * a) : p * x = x := by
  obtain ⟨a, rfl⟩ := hx
  rw [← EffectMonoid.mul_assoc, hp]

theorem corner_fix_right (hp : p * p = p) {x : M} (hx : ∃ a, x = p * a) : x * p = x := by
  rw [← idem_central hp, corner_fix hp hx]

theorem corner_le (hp : p * p = p) {x : M} (hx : ∃ a, x = p * a) : x ≼ p := by
  rw [← corner_fix hp hx]
  exact emon_mul_le_self p x

theorem corner_ovee_fix (hp : p * p = p) {x y : M} (hx : ∃ a, x = p * a)
    (hy : ∃ a, y = p * a) (h : Perp x y) : p * ovee x y h = ovee x y h := by
  obtain ⟨h', e⟩ := emon_mul_ovee p h
  rw [e]
  exact PCM.ovee_congr (corner_fix hp hx) (corner_fix hp hy) h' h

/-- **REC 21** (`cornersexample`, short.tex:566, Example): the corner `pM` is an
effect algebra with the partial sum of `M`, unit `p` and `(p · a)^⊥ := p · a^⊥`. -/
noncomputable def cornerEA (hp : p * p = p) : EffectAlgebra (Corner p) where
  zero := ⟨0, 0, (exc_emonzero p).1.symm⟩
  Perp x y := Perp x.1 y.1
  ovee x y h := ⟨ovee x.1 y.1 h, ovee x.1 y.1 h, (corner_ovee_fix hp x.2 y.2 h).symm⟩
  perp_comm h := PCM.perp_comm h
  ovee_comm h := Subtype.ext (PCM.ovee_comm h)
  perp_of_ovee_perp hab h := PCM.perp_of_ovee_perp hab h
  perp_ovee_of_ovee_perp hab h := PCM.perp_ovee_of_ovee_perp hab h
  ovee_assoc hab h := Subtype.ext (PCM.ovee_assoc hab h)
  zero_perp a := PCM.zero_perp a.1
  zero_ovee a := Subtype.ext (PCM.zero_ovee a.1)
  one := ⟨p, 1, (EffectMonoid.mul_one p).symm⟩
  orth x := ⟨p * orth x.1, orth x.1, rfl⟩
  perp_orth x := by
    obtain ⟨h, -⟩ := emon_mul_ovee p (EffectAlgebra.perp_orth x.1)
    show Perp x.1 (p * orth x.1)
    rw [corner_fix hp x.2] at h
    exact h
  ovee_orth x := by
    apply Subtype.ext
    show ovee x.1 (p * orth x.1) _ = p
    obtain ⟨h, e⟩ := emon_mul_ovee p (EffectAlgebra.perp_orth x.1)
    rw [EffectAlgebra.ovee_orth, EffectMonoid.mul_one] at e
    exact (PCM.ovee_congr (corner_fix hp x.2).symm rfl _ h).trans e.symm
  orth_unique {x y} h e := by
    apply Subtype.ext
    show y.1 = p * orth x.1
    have e1 : ovee x.1 y.1 h = p := congrArg Subtype.val e
    obtain ⟨h2, e2⟩ := emon_mul_ovee p (EffectAlgebra.perp_orth x.1)
    rw [EffectAlgebra.ovee_orth, EffectMonoid.mul_one] at e2
    have h2' : Perp x.1 (p * orth x.1) := by rw [corner_fix hp x.2] at h2; exact h2
    refine ovee_left_cancel h h2' (e1.trans (e2.trans ?_))
    exact PCM.ovee_congr (corner_fix hp x.2) rfl _ _
  eq_zero_of_perp_one {x} h := by
    apply Subtype.ext
    show x.1 = 0
    have h' : x.1 ≼ orth p := eabasics_perp_iff_le_orth.1 h
    have := emon_mul_mono_right p h'
    rw [corner_fix hp x.2, idem_mul_orth hp] at this
    exact eq_zero_of_le_zero this

/-- **REC 21** (`cornersexample`, short.tex:566, Example): the corner `pM` is an
effect monoid, with the multiplication of `M` (`pM` is closed under it) and
unit `p`. -/
noncomputable def cornerEM (hp : p * p = p) : EffectMonoid (Corner p) :=
  letI := cornerEA hp
  letI : Mul (Corner p) := ⟨fun x y => ⟨x.1 * y.1, by
    obtain ⟨a, ha⟩ := x.2
    exact ⟨a * y.1, by rw [ha, EffectMonoid.mul_assoc]⟩⟩⟩
  EffectMonoid.ofBiadditive (Corner p)
    (fun x => Subtype.ext (corner_fix_right hp x.2))
    (fun x => Subtype.ext (corner_fix hp x.2))
    (fun a b c h => by
      obtain ⟨h', e⟩ := emon_mul_ovee a.1 (show Perp b.1 c.1 from h)
      exact ⟨h', Subtype.ext e⟩)
    (fun a b c h => by
      obtain ⟨h', e⟩ := emon_ovee_mul a.1 (show Perp b.1 c.1 from h)
      exact ⟨h', Subtype.ext e⟩)
    (fun a b c => Subtype.ext (EffectMonoid.mul_assoc a.1 b.1 c.1).symm)

/-- Elements of `pM` and `p^⊥M` are orthogonal. -/
theorem corner_perp (hp : p * p = p) {x y : M} (hx : ∃ a, x = p * a)
    (hy : ∃ a, y = orth p * a) : Perp x y := by
  rw [eabasics_perp_iff_le_orth]
  have hy' : y ≼ orth p := corner_le (orth_idem hp) hy
  have : p ≼ orth y := by
    have := eabasics_le_iff_orth_le.1 hy'
    rwa [eabasics_orth_orth] at this
  exact pcm_preorder_trans (corner_le hp hx) this

/-- The middle-four interchange in a PCM (thesis B's private
`pcm_middle_four`, Effectus.lean, re-proved). -/
theorem pcm_middle_four' {N : Type v} [PCM N] {a b c d : N}
    (hab : Perp a b) (hcd : Perp c d) (h : Perp (ovee a b hab) (ovee c d hcd)) :
    ∃ (hac : Perp a c) (hbd : Perp b d) (h' : Perp (ovee a c hac) (ovee b d hbd)),
      ovee (ovee a c hac) (ovee b d hbd) h' = ovee (ovee a b hab) (ovee c d hcd) h := by
  have hbcd : Perp b (ovee c d hcd) := PCM.perp_of_ovee_perp hab h
  have habcd : Perp a (ovee b (ovee c d hcd) hbcd) := PCM.perp_ovee_of_ovee_perp hab h
  have hl4 : PCM.IsSumOf [a, b, c, d] (ovee a (ovee b (ovee c d hcd) hbcd) habcd) :=
    PCM.IsSumOf.cons (PCM.IsSumOf.cons (isSumOf_pair _ _ hcd) hbcd) habcd
  rw [(PCM.ovee_assoc hab h).symm] at hl4
  have hl5 := PCM.isSumOf_perm (List.Perm.cons a (List.Perm.swap c b [d])) hl4
  obtain ⟨t₁, ht₁, hat₁, e₁⟩ := PCM.isSumOf_cons_iff.mp hl5
  obtain ⟨t₂, ht₂, hct₂, e₂⟩ := PCM.isSumOf_cons_iff.mp ht₁
  obtain ⟨t₃, ht₃, hbt₃, e₃⟩ := PCM.isSumOf_cons_iff.mp ht₂
  obtain ⟨t₄, ht₄, hdt₄, e₄⟩ := PCM.isSumOf_cons_iff.mp ht₃
  rw [PCM.isSumOf_nil_iff] at ht₄
  subst ht₄
  rw [PCM.ovee_zero] at e₄
  subst e₄
  subst e₃
  subst e₂
  obtain ⟨hac, h', e⟩ := PCM.assoc_left hct₂ hat₁
  exact ⟨hac, hbt₃, h', e.trans e₁⟩

section CornerIso

variable (hp : p * p = p)

/-- The map `a ↦ (p · a, p^⊥ · a)` of REC 21. -/
noncomputable def cornerSplit (a : M) : Corner p × Corner (orth p) :=
  (⟨p * a, a, rfl⟩, ⟨orth p * a, a, rfl⟩)

/-- Its inverse `(x, y) ↦ x ⊻ y`. -/
noncomputable def cornerJoin (u : Corner p × Corner (orth p)) : M :=
  ovee u.1.1 u.2.1 (corner_perp hp u.1.2 u.2.2)

include hp in
theorem cornerJoin_cornerSplit (a : M) : cornerJoin hp (cornerSplit a) = a := by
  obtain ⟨h, e⟩ := emon_ovee_mul a (EffectAlgebra.perp_orth p)
  rw [EffectAlgebra.ovee_orth, EffectMonoid.one_mul] at e
  exact (PCM.ovee_congr rfl rfl _ h).trans e.symm

theorem corner_cross (hp : p * p = p) {y : M} (hy : ∃ a, y = orth p * a) : p * y = 0 := by
  obtain ⟨a, rfl⟩ := hy
  rw [← EffectMonoid.mul_assoc, idem_mul_orth hp, (exc_emonzero a).2]

theorem corner_cross' (hp : p * p = p) {x : M} (hx : ∃ a, x = p * a) : orth p * x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  rw [← EffectMonoid.mul_assoc, orth_mul_idem hp, (exc_emonzero a).2]

include hp in
theorem cornerSplit_cornerJoin (u : Corner p × Corner (orth p)) :
    cornerSplit (cornerJoin hp u) = u := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := u
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show p * ovee x y _ = x
    obtain ⟨h, e⟩ := emon_mul_ovee p (corner_perp hp hx hy)
    rw [e, PCM.ovee_congr (corner_fix hp hx) (corner_cross hp hy) h (PCM.perp_zero _),
      PCM.ovee_zero]
  · show orth p * ovee x y _ = y
    obtain ⟨h, e⟩ := emon_mul_ovee (orth p) (corner_perp hp hx hy)
    rw [e, PCM.ovee_congr (corner_cross' hp hx) (corner_fix (orth_idem hp) hy) h
      (PCM.zero_perp _), PCM.zero_ovee]

end CornerIso

/-- **REC 21** (`cornersexample`, short.tex:566, Example): for an idempotent `p`,
`a ↦ (p · a, p^⊥ · a)` is an isomorphism of effect monoids
`M ≅ pM ⊕ p^⊥M` (cited from OAP 21; proved here, using that idempotents are
central). -/
noncomputable def rec21_cornerIso (hp : p * p = p) :
    @EMIso M (Corner p × Corner (orth p)) _
      (@prodEffectMonoid _ _ (cornerEM hp) (cornerEM (orth_idem hp))) := by
  letI := cornerEM hp
  letI := cornerEM (orth_idem hp)
  have hq := orth_idem hp
  -- the forward map is an effect monoid homomorphism
  let F : EffectMonoidHom M (Corner p × Corner (orth p)) :=
    { toFun := cornerSplit
      perp_map := fun h => ⟨(emon_mul_ovee p h).1, (emon_mul_ovee (orth p) h).1⟩
      ovee_map := fun h => Prod.ext (Subtype.ext (emon_mul_ovee p h).2)
        (Subtype.ext (emon_mul_ovee (orth p) h).2)
      map_one := Prod.ext (Subtype.ext (EffectMonoid.mul_one p))
        (Subtype.ext (EffectMonoid.mul_one (orth p)))
      map_mul := fun a b => Prod.ext (Subtype.ext (by
          show p * (a * b) = p * a * (p * b)
          rw [EffectMonoid.mul_assoc, ← EffectMonoid.mul_assoc a p b, ← idem_central hp a,
            EffectMonoid.mul_assoc p a b, ← EffectMonoid.mul_assoc p p, hp]))
        (Subtype.ext (by
          show orth p * (a * b) = orth p * a * (orth p * b)
          rw [EffectMonoid.mul_assoc, ← EffectMonoid.mul_assoc a (orth p) b,
            ← idem_central hq a, EffectMonoid.mul_assoc (orth p) a b,
            ← EffectMonoid.mul_assoc (orth p) (orth p), hq])) }
  have hFG : ∀ u, F.toFun (cornerJoin hp u) = u := cornerSplit_cornerJoin hp
  have hGF : ∀ a, cornerJoin hp (F.toFun a) = a := cornerJoin_cornerSplit hp
  -- the inverse map preserves orthogonality and sums (middle-four interchange)
  have hG : ∀ {u v : Corner p × Corner (orth p)} (h : Perp u v),
      ∃ h' : Perp (cornerJoin hp u) (cornerJoin hp v),
        cornerJoin hp (ovee u v h) = ovee (cornerJoin hp u) (cornerJoin hp v) h' := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ ⟨h1, h2⟩
    replace h1 : Perp x x' := h1
    replace h2 : Perp y y' := h2
    have hxx : ∃ a, ovee x x' h1 = p * a := ⟨ovee x x' h1, (corner_ovee_fix hp hx hx' h1).symm⟩
    have hyy : ∃ a, ovee y y' h2 = orth p * a :=
      ⟨ovee y y' h2, (corner_ovee_fix hq hy hy' h2).symm⟩
    obtain ⟨hac, hbd, h', e⟩ := pcm_middle_four' h1 h2 (corner_perp hp hxx hyy)
    exact ⟨h', e.symm⟩
  exact
    { hom := F
      inv :=
        { toFun := cornerJoin hp
          perp_map := fun h => (hG h).1
          ovee_map := fun h => (hG h).2
          map_one := by
            show ovee p (orth p) _ = 1
            exact EffectAlgebra.ovee_orth p
          map_mul := fun u v => by
            rw [← hFG u, ← hFG v, ← F.map_mul, hGF, hGF, hGF] }
      inv_hom := hGF
      hom_inv := hFG }

/-- An effect monoid homomorphism maps `0` to `0`. -/
theorem EffectMonoidHom.map_zero' {N : Type v} [EffectMonoid N] (f : EffectMonoidHom M N) :
    f.toFun 0 = 0 := by
  have h := f.perp_map (PCM.zero_perp (0 : M))
  have e := f.ovee_map (PCM.zero_perp (0 : M))
  rw [PCM.zero_ovee] at e
  exact ovee_eq_self_left h e.symm

theorem subsingleton_of_one_eq_zero {E : Type v} [EffectAlgebra E] (h : (1 : E) = 0) :
    Subsingleton E :=
  ⟨fun x y => by
    have hx : x = 0 := eq_zero_of_le_zero (h ▸ (rec6_partialOrder (E := E)).2.2.2.2.1 x)
    have hy : y = 0 := eq_zero_of_le_zero (h ▸ (rec6_partialOrder (E := E)).2.2.2.2.1 y)
    rw [hx, hy]⟩

/-- **REC 21** (`cornersexample`, short.tex:566, Example), last sentence: an
effect monoid is irreducible (REC 20) iff it has no non-trivial idempotents. -/
theorem rec21_irreducible_iff : IsIrreducible M ↔ ∀ p : M, p * p = p → p = 0 ∨ p = 1 := by
  constructor
  · intro hirr p hp
    let _ := cornerEM hp
    let _ := cornerEM (orth_idem hp)
    rcases hirr _ _ (rec21_cornerIso hp) with h | h
    · left
      have := congrArg Subtype.val (Subsingleton.elim (1 : Corner p) 0)
      exact this
    · right
      have : orth p = 0 := congrArg Subtype.val (Subsingleton.elim (1 : Corner (orth p)) 0)
      rw [← eabasics_orth_orth p, this, eabasics_orth_zero]
  · intro hid E₁ E₂ _ _ φ
    -- `e := φ⁻¹(1, 0)` is an idempotent of `M`
    set e := φ.inv.toFun ((1 : E₁), (0 : E₂)) with he
    have hmul : ((1 : E₁), (0 : E₂)) * ((1 : E₁), (0 : E₂)) = ((1 : E₁), (0 : E₂)) :=
      Prod.ext (EffectMonoid.mul_one _) ((exc_emonzero _).1)
    have hee : e * e = e := by
      rw [he, ← φ.inv.map_mul]
      exact congrArg _ hmul
    rcases hid e hee with h0 | h1
    · left
      have : ((1 : E₁), (0 : E₂)) = ((0 : E₁), (0 : E₂)) := by
        rw [← φ.hom_inv ((1 : E₁), (0 : E₂)), ← he, h0, EffectMonoidHom.map_zero']
        rfl
      exact subsingleton_of_one_eq_zero (congrArg Prod.fst this)
    · right
      have : ((1 : E₁), (0 : E₂)) = ((1 : E₁), (1 : E₂)) := by
        rw [← φ.hom_inv ((1 : E₁), (0 : E₂)), ← he, h1, φ.hom.map_one]
        rfl
      exact subsingleton_of_one_eq_zero (congrArg Prod.snd this).symm

end Corner

/-! ### Filters and comprehensions (§2.1.2) -/

section FiltersComprehensions

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **REC 22** (`def:comprehension`, short.tex:587, Definition): a
**comprehension** for `p : A → I` is a map `π : A_p → A` with
`1 ∘ π = p ∘ π`, final with this property.  This is thesis B's
`IsComprehension` (199II) verbatim; "has comprehensions" is `HasComprehension`. -/
theorem rec22_isComprehension_iff {W X : C} (p : Pred X) (π : W ⟶ X) :
    IsComprehension p π ↔
      (π ≫ truth X = π ≫ p ∧
        ∀ ⦃B : C⦄ (f : B ⟶ X), f ≫ truth X = f ≫ p → ∃! f' : B ⟶ W, f' ≫ π = f) :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, fun _ f hf => h2 f hf.symm⟩,
    fun ⟨h1, h2⟩ => ⟨h1.symm, fun _ f hf => h2 f hf.symm⟩⟩

/-- **REC 23** (`def:filter`, short.tex:603, Definition): a **filter** for a
predicate `p : A → I` is a map `ξ : A → A^p` with `1 ∘ ξ ≤ p` which is initial
with this property: every `f : A → B` with `1 ∘ f ≤ p` factors uniquely as
`f = f' ∘ ξ`. -/
def IsFilter {X Q : C} (p : Pred X) (ξ : X ⟶ Q) : Prop :=
  (ξ ≫ truth Q) ≼ p ∧
    ∀ ⦃B : C⦄ (f : X ⟶ B), (f ≫ truth B) ≼ p → ∃! f' : Q ⟶ B, ξ ≫ f' = f

/-- **REC 23** (`def:filter`, short.tex:603, Definition), footnote: a filter for
`p` is exactly a *quotient* for `p^⊥` in the sense of thesis B (197II). -/
theorem isFilter_iff_isQuotient {X Q : C} (p : Pred X) (ξ : X ⟶ Q) :
    IsFilter p ξ ↔ IsQuotient (orth p) ξ := by
  unfold IsFilter IsQuotient
  rw [eabasics_orth_orth]

/-- **REC 23** (`def:filter`, short.tex:603, Definition): an effectus **has
filters** when every predicate has a filter. -/
class HasFilters (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop where
  filter : ∀ {X : C} (p : Pred X), ∃ (Q : C) (ξ : X ⟶ Q), IsFilter p ξ

/-- **REC 23**, footnote: having filters is having thesis B's quotients. -/
theorem hasFilters_iff_hasQuotients : HasFilters C ↔ HasQuotients C := by
  constructor
  · intro h
    refine ⟨fun p => ?_⟩
    obtain ⟨Q, ξ, hξ⟩ := h.filter (orth p)
    refine ⟨Q, ξ, ?_⟩
    have := (isFilter_iff_isQuotient _ ξ).1 hξ
    rwa [eabasics_orth_orth] at this
  · intro h
    exact ⟨fun p => by
      obtain ⟨Q, ξ, hξ⟩ := h.quot (orth p)
      exact ⟨Q, ξ, (isFilter_iff_isQuotient p ξ).2 hξ⟩⟩

theorem hasQuotients_of_hasFilters [h : HasFilters C] : HasQuotients C :=
  hasFilters_iff_hasQuotients.1 h

instance hasFilters_of_hasQuotients [h : HasQuotients C] : HasFilters C :=
  hasFilters_iff_hasQuotients.2 h

/-- A chosen filter `ξ^p : A → A^p` for `p` (the tree's chosen quotient for
`p^⊥`). -/
noncomputable def filterMap [HasQuotients C] {X : C} (p : Pred X) :
    X ⟶ quotObj (orth p) :=
  quotMap (orth p)

theorem isFilter_filterMap [HasQuotients C] {X : C} (p : Pred X) :
    IsFilter p (filterMap p) :=
  (isFilter_iff_isQuotient _ _).2 (isQuotient_quotMap _)

/-- **REC 25** (`rem:kernels`, short.tex:643, Remark), the halves in the tree:
an effectus with comprehensions has all kernels (thesis B 200III), and one with
filters and images has all cokernels (205II).  Thin: `effectus_has_all_kernels`,
`effectus_has_all_cokernels`.  (The converses, and the refinement "images +
filters of *sharp* predicates suffice", are not formalised.) -/
theorem rec25_kernels_cokernels :
    (HasComprehension C → HasAllKernels C) ∧
      (HasFilters C → HasImages C → HasAllCokernels C) :=
  ⟨fun _ => inferInstance, fun _ _ =>
    have := hasQuotients_of_hasFilters (C := C); inferInstance⟩

/-- **REC 26** (`chainofadjs`, short.tex:654, Remark): with `Pred_□(C)` the
Grothendieck category (thesis B's `PredSquare C`, 198II), the forgetful functor
`U` has the `0`-embedding as left and the `1`-embedding as right adjoint; the
`0`-embedding has a left adjoint iff `C` has filters, and the `1`-embedding a
right adjoint iff `C` has comprehensions.  Thin: `predSquare_zero_adj`,
`predSquare_one_adj`, `exc_quot_adjoint` (198III), `compr_grothendieck` (199VI). -/
theorem rec26_adjunctions :
    Nonempty (predSquareZero C ⊣ predSquareForget C) ∧
      Nonempty (predSquareForget C ⊣ predSquareOne C) ∧
      (HasFilters C ↔ ∃ Q, Nonempty (Q ⊣ predSquareZero C)) ∧
      (HasComprehension C ↔ ∃ K, Nonempty (predSquareOne C ⊣ K)) :=
  ⟨predSquare_zero_adj, predSquare_one_adj,
    hasFilters_iff_hasQuotients.trans exc_quot_adjoint, compr_grothendieck⟩

/-- **REC 27** (short.tex:679, Proposition): in an effectus with filters and
comprehensions, every filter is epic, every comprehension is monic, a filter `ξ`
for `a` has `1 ∘ ξ = a`, and comprehensions are total.  Thin: thesis B 197V.6,
199VII.5, 197V.5 and 202VIII. -/
theorem rec27 [HasFilters C] [HasComprehension C] :
    (∀ {X Q : C} {p : Pred X} {ξ : X ⟶ Q}, IsFilter p ξ → Epi ξ) ∧
      (∀ {W X : C} {p : Pred X} {π : W ⟶ X}, IsComprehension p π → Mono π) ∧
      (∀ {X Q : C} {a : Pred X} {ξ : X ⟶ Q}, IsFilter a ξ → ξ ≫ truth Q = a) ∧
      (∀ {W X : C} {p : Pred X} {π : W ⟶ X}, IsComprehension p π → IsTotal π) := by
  have := hasQuotients_of_hasFilters (C := C)
  refine ⟨fun h => quotient_basics_6 ((isFilter_iff_isQuotient _ _).1 h),
    fun h => compr_basics_5 h, fun {X Q a ξ} h => ?_, fun h => compr_total h⟩
  have := quotient_basics_5 ((isFilter_iff_isQuotient _ _).1 h)
  rwa [eabasics_orth_orth] at this

end FiltersComprehensions

/-! ### Monoidal effectuses (REC 28, 29) -/

section Monoidal

variable (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
  [MonoidalCategory C] [SymmetricCategory C]

/-- **REC 28** (`def:monoidal-effectus`, short.tex:693, Definition): an
effectus is **monoidal** when it has a symmetric monoidal structure `(⊗, I)`
such that the tensor unit *is* the effect object `I`, the tensor product is
biadditive (`(f ⊻ g) ⊗ h = (f ⊗ h) ⊻ (g ⊗ h)` and `0 ⊗ h = 0`), and
`1_A ⊗ 1_B = 1_{A⊗B}`.  The last equation silently identifies `I ⊗ I` with `I`;
we make that identification the left unitor `λ_I` (transported along the
equation of the first clause). -/
class MonoidalEffectus : Prop where
  unit_eq : 𝟙_ C = effObj C
  ovee_tensor : ∀ {A B A' B' : C} {f g : A ⟶ B} (h : Perp f g) (k : A' ⟶ B'),
    ∃ h' : Perp (f ⊗ₘ k) (g ⊗ₘ k), ovee f g h ⊗ₘ k = ovee (f ⊗ₘ k) (g ⊗ₘ k) h'
  zero_tensor : ∀ {A B A' B' : C} (k : A' ⟶ B'), (0 : A ⟶ B) ⊗ₘ k = 0
  truth_tensor : ∀ A B : C,
    (truth A ⊗ₘ truth B) ≫ eqToHom (congrArg (fun X => X ⊗ effObj C) unit_eq.symm) ≫
      (λ_ (effObj C)).hom = truth (A ⊗ B)

variable {C} [MonoidalEffectus C]

/-- A scalar `s : I → I`, seen as an endomorphism of the tensor unit. -/
noncomputable def unitScalar (s : Scal C) : 𝟙_ C ⟶ 𝟙_ C :=
  eqToHom (MonoidalEffectus.unit_eq (C := C)) ≫ s ≫
    eqToHom (MonoidalEffectus.unit_eq (C := C)).symm

/-- **REC 29** (short.tex:701, running text before the Lemma): the **scalar
multiplication** `s · f := λ_B ∘ (s ⊗ f) ∘ λ_A⁻¹` of a monoidal effectus. -/
noncomputable def smulHom (s : Scal C) {A B : C} (f : A ⟶ B) : A ⟶ B :=
  (λ_ A).inv ≫ (unitScalar s ⊗ₘ f) ≫ (λ_ B).hom

/-- Helper: `s · f = (s · id) ∘ f`. -/
theorem smulHom_eq_id_comp (s : Scal C) {A B : C} (f : A ⟶ B) :
    smulHom s f = smulHom s (𝟙 A) ≫ f := by
  simp only [smulHom, MonoidalCategory.tensorHom_def, Category.assoc,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [leftUnitor_naturality]

/-- Helper: `s · f = f ∘ (s · id)`. -/
theorem smulHom_eq_comp_id (s : Scal C) {A B : C} (f : A ⟶ B) :
    smulHom s f = f ≫ smulHom s (𝟙 B) := by
  simp only [smulHom, MonoidalCategory.tensorHom_def', Category.assoc,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [← Category.assoc (λ_ A).inv, ← leftUnitor_inv_naturality, Category.assoc]

/-- Helper: conjugating a partial sum by two maps. -/
theorem ovee_conj {W X Y Z : C} (a : W ⟶ X) (b : Y ⟶ Z) {f g : X ⟶ Y}
    (h : Perp f g) :
    ∃ h' : Perp (a ≫ f ≫ b) (a ≫ g ≫ b),
      a ≫ ovee f g h ≫ b = ovee (a ≫ f ≫ b) (a ≫ g ≫ b) h' := by
  obtain ⟨h1, e1⟩ := FinPAC.comp_ovee h b
  obtain ⟨h2, e2⟩ := FinPAC.ovee_comp h1 a
  exact ⟨h2, by rw [e1, e2]⟩

/-- Helper: the endomorphisms of the tensor unit commute (Eckmann–Hilton). -/
theorem unit_endo_comm (a b : 𝟙_ C ⟶ 𝟙_ C) : a ≫ b = b ≫ a := by
  have e1 : 𝟙_ C ◁ b ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ b := by
    rw [← unitors_equal]; exact leftUnitor_naturality b
  have e2 : a ▷ 𝟙_ C ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ a :=
    rightUnitor_naturality a
  calc a ≫ b = (ρ_ (𝟙_ C)).inv ≫ (a ▷ 𝟙_ C ≫ 𝟙_ C ◁ b) ≫ (ρ_ (𝟙_ C)).hom := by
        simp only [Category.assoc, e1]
        rw [← Category.assoc (a ▷ 𝟙_ C), e2]
        simp
    _ = (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ b ≫ a ▷ 𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom := by
        rw [← whisker_exchange]
    _ = b ≫ a := by
        simp only [Category.assoc, e2]
        rw [← Category.assoc (𝟙_ C ◁ b), e1]
        simp

/-- Helper: the scalar multiplication by `s` on the identity of the effect
object `I` is `s` itself (this is where `λ_I = ρ_I` enters). -/
theorem conj_unit_eq {X : C} (hX : 𝟙_ C = X) (s : X ⟶ X) :
    (λ_ X).inv ≫ ((eqToHom hX ≫ s ≫ eqToHom hX.symm) ⊗ₘ 𝟙 X) ≫ (λ_ X).hom = s := by
  subst hX
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, tensorHom_id]
  rw [unitors_inv_equal, unitors_equal, rightUnitor_naturality, Iso.inv_hom_id_assoc]

theorem smulHom_id_effObj (s : Scal C) : smulHom s (𝟙 (effObj C)) = s :=
  conj_unit_eq MonoidalEffectus.unit_eq s

theorem unitScalar_comp (s t : Scal C) :
    unitScalar (t ≫ s) = unitScalar t ≫ unitScalar s := by
  simp [unitScalar]

/-- **REC 29** (`lem:monoidal-effectus-facts`, short.tex:704, Lemma), first
item: scalar multiplication respects composition,
`g ∘ (s · f) = s · (g ∘ f) = (s · g) ∘ f` (in diagrammatic order:
`(s · f) ≫ g = s · (f ≫ g) = f ≫ (s · g)`). -/
theorem rec29_comp (s : Scal C) {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
    smulHom s f ≫ g = smulHom s (f ≫ g) ∧ smulHom s (f ≫ g) = f ≫ smulHom s g := by
  constructor
  · rw [smulHom_eq_id_comp s f, smulHom_eq_id_comp s (f ≫ g), Category.assoc]
  · rw [smulHom_eq_comp_id s (f ≫ g), smulHom_eq_comp_id s g, Category.assoc]

theorem unitScalar_ovee {s t : Scal C} (h : Perp s t) :
    ∃ h', unitScalar (ovee s t h) = ovee (unitScalar s) (unitScalar t) h' :=
  ovee_conj _ _ h

/-- **REC 29** (`lem:monoidal-effectus-facts`, short.tex:704, Lemma), second
item, first half: `(s ⊻ t) · f = s · f ⊻ t · f`. -/
theorem rec29_ovee_left {s t : Scal C} (h : Perp s t) {A B : C} (f : A ⟶ B) :
    ∃ h' : Perp (smulHom s f) (smulHom t f),
      smulHom (ovee s t h) f = ovee (smulHom s f) (smulHom t f) h' := by
  obtain ⟨h1, e1⟩ := unitScalar_ovee h
  obtain ⟨h2, e2⟩ := MonoidalEffectus.ovee_tensor h1 f
  obtain ⟨h3, e3⟩ := ovee_conj (λ_ A).inv (λ_ B).hom h2
  exact ⟨h3, by simp only [smulHom]; rw [e1, e2, e3]⟩

/-- **REC 29** (`lem:monoidal-effectus-facts`, short.tex:704, Lemma), second
item, second half: `s · (f ⊻ g) = s · f ⊻ s · g`.  (The paper's biadditivity
axiom is only in the first variable of `⊗`; this half needs none, because
`s · f = (s · id) ∘ f` and composition is biadditive.) -/
theorem rec29_ovee_right (s : Scal C) {A B : C} {f g : A ⟶ B} (h : Perp f g) :
    ∃ h' : Perp (smulHom s f) (smulHom s g),
      smulHom s (ovee f g h) = ovee (smulHom s f) (smulHom s g) h' := by
  obtain ⟨h1, e1⟩ := FinPAC.ovee_comp h (smulHom s (𝟙 A))
  have hf := smulHom_eq_id_comp s f
  have hg := smulHom_eq_id_comp s g
  refine ⟨by rw [hf, hg]; exact h1, ?_⟩
  rw [smulHom_eq_id_comp s (ovee f g h), e1]
  exact PCM.ovee_congr hf.symm hg.symm _ _

/-- **REC 29** (`lem:monoidal-effectus-facts`, short.tex:704, Lemma), third
item: for a predicate `p : A → I`, `s · p = s ∘ p`. -/
theorem rec29_pred (s : Scal C) {A : C} (p : Pred A) : smulHom s p = p ≫ s := by
  rw [smulHom_eq_comp_id, smulHom_id_effObj]

/-- **REC 29** (`lem:monoidal-effectus-facts`, short.tex:704, Lemma), third
item, "in particular": `s · t = s ∘ t`, so that
`s · (t · f) = (s · t) · f = (s ∘ t) · f`.  (The first equation of the chain
uses that the scalars of a monoidal category commute, `unit_endo_comm`.) -/
theorem rec29_scalar_action (s t : Scal C) {A B : C} (f : A ⟶ B) :
    smulHom s t = t ≫ s ∧ smulHom s (smulHom t f) = smulHom (smulHom s t) f ∧
      smulHom (smulHom s t) f = smulHom (t ≫ s) f := by
  have hst : smulHom s t = t ≫ s := rec29_pred s t
  refine ⟨hst, ?_, by rw [hst]⟩
  rw [hst, smulHom_eq_id_comp t f, ← (rec29_comp s (smulHom t (𝟙 A)) f).1,
    smulHom_eq_id_comp s (smulHom t (𝟙 A)), smulHom_eq_id_comp (t ≫ s) f]
  congr 1
  simp only [smulHom, tensorHom_id, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, unitScalar_comp, unit_endo_comm]

end Monoidal


/-! ## §2.2 Directed completeness -/

section DirectedComplete

variable {E : Type u} [EffectAlgebra E]

/-- **REC 30** (short.tex:719, Definition), footnote: a subset `U` of an effect
algebra is **upwards directed** if any two of its elements have an upper bound
in `U`. -/
def IsUpDirected (D : Set E) : Prop := ∀ x ∈ D, ∀ y ∈ D, ∃ z ∈ D, x ≼ z ∧ y ≼ z

/-- Downwards directed subsets (REC 30, footnote). -/
def IsDownDirected (D : Set E) : Prop := ∀ x ∈ D, ∀ y ∈ D, ∃ z ∈ D, z ≼ x ∧ z ≼ y

/-- `s` is the supremum of `D` for the effect algebra order. -/
def IsSupOf (D : Set E) (s : E) : Prop := (∀ x ∈ D, x ≼ s) ∧ ∀ u, (∀ x ∈ D, x ≼ u) → s ≼ u

/-- `m` is the infimum of `D` for the effect algebra order. -/
def IsInfOf (D : Set E) (m : E) : Prop := (∀ x ∈ D, m ≼ x) ∧ ∀ l, (∀ x ∈ D, l ≼ x) → l ≼ m

/-- **REC 30** (short.tex:719, Definition), footnote: an effect algebra is
**directed complete** when every upwards-directed subset has a supremum. -/
def DirectedCompleteEA (E : Type u) [EffectAlgebra E] : Prop :=
  ∀ D : Set E, IsUpDirected D → ∃ s, IsSupOf D s

theorem mem_orth_image {D : Set E} {x : E} : x ∈ orth '' D ↔ orth x ∈ D := by
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [eabasics_orth_orth]
  · intro h; exact ⟨orth x, h, eabasics_orth_orth x⟩

/-- **REC 30** (short.tex:719, Definition), footnote: as `( )^⊥` is an order
anti-automorphism, upwards-directed completeness is equivalent to
downwards-directed completeness. -/
theorem directedCompleteEA_iff_down :
    DirectedCompleteEA E ↔ ∀ D : Set E, IsDownDirected D → ∃ m, IsInfOf D m := by
  constructor
  · intro h D hD
    have hup : IsUpDirected (orth '' D) := by
      intro x hx y hy
      rw [mem_orth_image] at hx hy
      obtain ⟨z, hz, hzx, hzy⟩ := hD _ hx _ hy
      refine ⟨orth z, mem_orth_image.2 (by rwa [eabasics_orth_orth]), ?_, ?_⟩
      · have := eabasics_le_iff_orth_le.1 hzx; rwa [eabasics_orth_orth] at this
      · have := eabasics_le_iff_orth_le.1 hzy; rwa [eabasics_orth_orth] at this
    obtain ⟨s, hs1, hs2⟩ := h _ hup
    refine ⟨orth s, fun x hx => ?_, fun l hl => ?_⟩
    · have := hs1 (orth x) (mem_orth_image.2 (by rwa [eabasics_orth_orth]))
      rwa [eabasics_le_iff_orth_le, eabasics_orth_orth] at this
    · have : s ≼ orth l := hs2 _ fun x hx => by
        have := hl _ (mem_orth_image.1 hx)
        rwa [eabasics_le_iff_orth_le, eabasics_orth_orth] at this
      rwa [eabasics_le_iff_orth_le, eabasics_orth_orth] at this
  · intro h D hD
    have hdown : IsDownDirected (orth '' D) := by
      intro x hx y hy
      rw [mem_orth_image] at hx hy
      obtain ⟨z, hz, hxz, hyz⟩ := hD _ hx _ hy
      refine ⟨orth z, mem_orth_image.2 (by rwa [eabasics_orth_orth]), ?_, ?_⟩
      · have := eabasics_le_iff_orth_le.1 hxz; rwa [eabasics_orth_orth] at this
      · have := eabasics_le_iff_orth_le.1 hyz; rwa [eabasics_orth_orth] at this
    obtain ⟨m, hm1, hm2⟩ := h _ hdown
    refine ⟨orth m, fun x hx => ?_, fun u hu => ?_⟩
    · have := hm1 (orth x) (mem_orth_image.2 (by rwa [eabasics_orth_orth]))
      rwa [eabasics_le_iff_orth_le, eabasics_orth_orth] at this
    · have : orth u ≼ m := hm2 _ fun x hx => by
        have := hu _ (mem_orth_image.1 hx)
        rwa [eabasics_le_iff_orth_le, eabasics_orth_orth] at this
      rwa [eabasics_le_iff_orth_le, eabasics_orth_orth] at this

end DirectedComplete

section DirectedCompleteEffectus

variable (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **REC 30** (short.tex:719, Definition): an effectus is **directed complete**
when all its predicate spaces `Pred(A)` are directed complete. -/
def DirectedCompleteEffectus : Prop := ∀ A : C, DirectedCompleteEA (Pred A)

/-- **REC 30** (short.tex:719, Definition): a directed-complete effectus is
**normal** when the suprema are preserved by all maps (the maps are Scott
continuous): for `f : A → B` and a directed `D ⊆ Pred(B)` with supremum `s`,
`s ∘ f` is the supremum of `{p ∘ f : p ∈ D}`. -/
def NormalEffectus : Prop :=
  DirectedCompleteEffectus C ∧
    ∀ {A B : C} (f : A ⟶ B) (D : Set (Pred B)) (s : Pred B),
      IsUpDirected D → IsSupOf D s → IsSupOf ((fun p => f ≫ p) '' D) (f ≫ s)

end DirectedCompleteEffectus

/-- The effect-algebra order of a Boolean algebra (with the effect algebra of
REC 16) is its lattice order. -/
theorem boolean_le_iff {B : Type u} [BooleanAlgebra B] (x y : B) :
    @PCM.le B (booleanEffectAlgebra B).toPCM x y ↔ x ≤ y := by
  let _ := booleanEffectAlgebra B
  constructor
  · rintro ⟨c, _, rfl⟩
    exact le_sup_left
  · intro h
    exact ⟨y \ x, inf_sdiff_self_right, sup_sdiff_cancel_right h⟩

/-- **REC 32** (short.tex:751, Example): any complete Boolean algebra is a
directed-complete effect monoid (with the effect monoid of REC 16). -/
theorem rec32_completeBoolean (B : Type u) [CompleteBooleanAlgebra B] :
    @DirectedCompleteEA B (booleanEffectMonoid B).toEffectAlgebra := by
  let _ := booleanEffectMonoid B
  intro D _
  refine ⟨sSup D, fun x hx => (boolean_le_iff x _).2 (le_sSup hx), fun u hu => ?_⟩
  exact (boolean_le_iff _ u).2 (sSup_le fun x hx => (boolean_le_iff x u).1 (hu x hx))

/-- **REC 34** (`thm:effect-monoids`, short.tex:761, Theorem), *the statement*:
every directed-complete effect monoid `M` is isomorphic to `B ⊕ C(X,[0,1])` for
a complete Boolean algebra `B` and an extremally-disconnected compact Hausdorff
space `X`.  This is OAP's main theorem (`mainthmdirectedcomplete`, OAP 69),
which the paper cites; it is recorded here as a `Prop` and enters the later
points as a hypothesis until `Papers/OAP` can be imported, when it is
discharged by OAP 69. -/
def EffectMonoidDCClassification : Prop :=
  ∀ (M : Type u) [EffectMonoid M], DirectedCompleteEA M →
    ∃ (B : Type u) (_ : CompleteBooleanAlgebra B) (X : Type u) (_ : TopologicalSpace X),
      CompactSpace X ∧ T2Space X ∧ ExtremallyDisconnected X ∧
        Nonempty (@EMIso M (B × Set.Icc (0 : C(X, ℝ)) 1) _
          (@prodEffectMonoid _ _ (booleanEffectMonoid B) (continuousUnitIntervalEffectMonoid X)))

/-- **REC 35** (`corscalars`, short.tex:768, Corollary): in a directed-complete
effectus the scalars are `Pred(I) ≅ B ⊕ C(X,[0,1])` for a complete Boolean
algebra `B` and an extremally-disconnected compact Hausdorff space `X`.  From
REC 34, as in the paper (the scalars are the predicates on `I`). -/
theorem rec35_scalars {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
    (h34 : EffectMonoidDCClassification.{v}) (hdc : DirectedCompleteEffectus C) :
    ∃ (B : Type v) (_ : CompleteBooleanAlgebra B) (X : Type v) (_ : TopologicalSpace X),
      CompactSpace X ∧ T2Space X ∧ ExtremallyDisconnected X ∧
        Nonempty (@EMIso (Scal C) (B × Set.Icc (0 : C(X, ℝ)) 1) _
          (@prodEffectMonoid _ _ (booleanEffectMonoid B) (continuousUnitIntervalEffectMonoid X))) :=
  h34 (Scal C) (hdc (effObj C))

/-- **REC 36** (short.tex:776, Theorem), *the statement*: an irreducible
directed-complete effect monoid is isomorphic to `{0}`, `{0,1}` or `[0,1]`.
Cited from OAP (OAP 71; it also follows from REC 34, since a connected
extremally-disconnected space is a point).  Recorded as a `Prop`, to enter the
later points as a hypothesis until `Papers/OAP` can be imported. -/
def IrreducibleDCClassification : Prop :=
  ∀ (M : Type u) [EffectMonoid M], DirectedCompleteEA M → IsIrreducible M →
    Subsingleton M ∨ Nonempty (EMIso M Bool) ∨ Nonempty (EMIso M I)

/-! ## §3 Pure maps and ⋄-adjointness -/

section Images

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **REC 62** (short.tex:1079, Definition): the **image** of `f : A → B` is the
smallest predicate `p` on `B` with `p ∘ f = 1 ∘ f`.  Thesis B's `IsImage`
(202I) verbatim; "has images" is `HasImages`. -/
theorem rec62_isImage_iff {X Y : C} (f : X ⟶ Y) (p : Pred Y) :
    IsImage f p ↔ (f ≫ p = f ≫ truth Y ∧ ∀ q : Pred Y, f ≫ q = f ≫ truth Y → p ≼ q) :=
  Iff.rfl

/-- **REC 63** (`lem:imageofcomposedmaps`, short.tex:1090, Lemma): if
`im(f ∘ g)` and `im f` exist, then `im(f ∘ g) ≤ im f`; if moreover `g` is an
isomorphism, they are equal.  The paper's proof; its first sentence concludes
"hence `im f ≤ im(f ∘ g)`", a slip for the inequality the computation (and the
statement) gives. -/
theorem rec63 {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ X) {i j : Pred Y}
    (hi : IsImage (g ≫ f) i) (hj : IsImage f j) :
    i ≼ j ∧ (IsIso g → i = j) := by
  have h1 : ∀ {Z' : C} (g' : Z' ⟶ X) {i' : Pred Y}, IsImage (g' ≫ f) i' → i' ≼ j := by
    intro Z' g' i' hi'
    -- `1 ∘ (f ∘ g) = (1 ∘ f) ∘ g = (im f ∘ f) ∘ g = im f ∘ (f ∘ g)`
    refine hi'.2 j ?_
    rw [Category.assoc, hj.1, Category.assoc]
  refine ⟨h1 g hi, fun hg => eabasics_le_antisymm (h1 g hi) ?_⟩
  -- `im f = im((f ∘ g) ∘ g⁻¹) ≤ im(f ∘ g)`
  have hj' : IsImage (inv g ≫ (g ≫ f)) j := by
    rwa [IsIso.inv_hom_id_assoc]
  exact hj'.2 i (by rw [Category.assoc, hi.1, ← Category.assoc])

/-- **REC 64** (`def:effectus-sharp`, short.tex:1100, Definition): a predicate
`p` on `A` is **sharp** if it is the image of some map `f : B → A`; `SPred(A)`
is the set of sharp predicates.  Thesis B's `IsSharp` and `SPred` (203I.1). -/
theorem rec64_isSharp_iff {X : C} (p : Pred X) :
    IsSharp p ↔ ∃ (B : C) (f : B ⟶ X), IsImage f p :=
  Iff.rfl

/-- **REC 65** (`def:floorceiling`, short.tex:1106, Definition): the **floor**
`⌊p⌋ := im π` for *any* comprehension `π` of `p` (thesis B's `floorPred` uses a
chosen one), well defined by the footnote's argument (two comprehensions differ
by an isomorphism, REC 63); the **ceiling** is `⌈p⌉ := ⌊p^⊥⌋^⊥` (`ceilPred`). -/
theorem rec65_floor_wd [HasComprehension C] [HasImages C] {W X : C} {p : Pred X}
    {π : W ⟶ X} (hπ : IsComprehension p π) :
    imPred π = floorPred p ∧ ceilPred p = orth (floorPred (orth p)) := by
  refine ⟨?_, rfl⟩
  obtain ⟨θ, hθ, e, -⟩ := compr_basics_2 hπ (isComprehension_comprMap p)
  rw [← e]
  exact (im_ineq (comprMap p) θ).2 θ hθ

/-- A comprehension for `p` is one for its image `⌊p⌋` (proof of REC 66 b;
thesis B's `isComprehension_imPred`, re-proved outside a ⋄-effectus). -/
theorem isComprehension_imPred' [HasImages C] {W X : C} {p : Pred X} {π : W ⟶ X}
    (h : IsComprehension p π) : IsComprehension (imPred π) π := by
  refine ⟨(isImage_imPred π).1, ?_⟩
  intro V g hg
  refine h.2 g ?_
  refine eabasics_le_antisymm (comp_le_comp g (pred_le_truth p)) ?_
  rw [← hg]
  exact comp_le_comp g ((isImage_imPred π).2 p h.1)

section FloorCeiling

variable [HasComprehension C] [HasImages C] {X Y : C}

/-- **REC 66** (`prop:floorceiling`, short.tex:1124, Proposition) a):
`⌊p⌋ ≤ p ≤ ⌈p⌉`.  (Printed "effectus with images and compressions": the
hypotheses are images and *comprehensions*.)  Thin: 203IV.1, `le_ceilPred`. -/
theorem rec66_a (p : Pred X) : floorPred p ≼ p ∧ p ≼ ceilPred p :=
  ⟨floor_basics_1 p, le_ceilPred p⟩

/-- **REC 66** (`prop:floorceiling`, short.tex:1124, Proposition) b):
`⌊⌊p⌋⌋ = ⌊p⌋`.  Thin: 203IV.3. -/
theorem rec66_b (p : Pred X) : floorPred (floorPred p) = floorPred p :=
  floor_basics_3 p

/-- **REC 66** (`prop:floorceiling`, short.tex:1124, Proposition) c): for
`q ≤ p`, `⌊q⌋ ≤ ⌊p⌋` and `⌈q⌉ ≤ ⌈p⌉`.  Thin: 203IV.4, `ceilPred_mono`. -/
theorem rec66_c {p q : Pred X} (h : q ≼ p) :
    floorPred q ≼ floorPred p ∧ ceilPred q ≼ ceilPred p :=
  ⟨floor_basics_4 h, ceilPred_mono h⟩

/-- **REC 66** (`prop:floorceiling`, short.tex:1124, Proposition) d):
`⌈p ∘ f⌉ = ⌈⌈p⌉ ∘ f⌉`.  Thin: 203XIII `ceiling_within_ceiling`. -/
theorem rec66_d (p : Pred X) (f : Y ⟶ X) : ceilPred (f ≫ p) = ceilPred (f ≫ ceilPred p) :=
  (ceiling_within_ceiling p f).symm

/-- **REC 66** (`prop:floorceiling`, short.tex:1124, Proposition) e):
`⌈p⌉ ∘ f = 0 ⟺ p ∘ f = 0`.  Thin: 203IV.6. -/
theorem rec66_e (p : Pred X) (f : Y ⟶ X) : f ≫ ceilPred p = 0 ↔ f ≫ p = 0 :=
  floor_basics_6 p f

/-- **REC 66** (`prop:floorceiling`, short.tex:1124, Proposition) f): `p` is
sharp iff `⌊p⌋ = p`.  Thin: 203XII `img_of_compr`. -/
theorem rec66_f (p : Pred X) : IsSharp p ↔ floorPred p = p :=
  (img_of_compr p).1

end FloorCeiling

end Images

section Diamond

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **REC 67** (`def:diamond-effect-theory`, short.tex:1175, Definition): an
effectus is a **⋄-effectus** when it has images, filters, comprehensions, and
`p` is sharp iff `p^⊥` is sharp.  This is thesis B's `DiamondEffectus` (206II),
which asks for quotients (= filters, REC 23) and for one direction of the
equivalence (the other follows as `p^⊥⊥ = p`). -/
theorem rec67_diamondEffectus_iff :
    DiamondEffectus C ↔
      HasImages C ∧ HasFilters C ∧ HasComprehension C ∧
        ∀ {X : C} (p : Pred X), IsSharp p ↔ IsSharp (orth p) := by
  constructor
  · intro h
    refine ⟨inferInstance, inferInstance, inferInstance, fun p => ⟨fun hp =>
      DiamondEffectus.orth_sharp hp, fun hp => ?_⟩⟩
    have := DiamondEffectus.orth_sharp hp
    rwa [eabasics_orth_orth] at this
  · rintro ⟨hI, hF, hC, hS⟩
    have := hasQuotients_of_hasFilters (C := C)
    exact { orth_sharp := fun hp => (hS _).1 hp }

variable [DiamondEffectus C] {X Y Z : C}

/-- **REC 68** (short.tex:1180, Definition): in a ⋄-effectus,
`f^⋄ : SPred(B) → SPred(A)` is `f^⋄(p) = ⌈p ∘ f⌉`, `f_⋄ : SPred(A) → SPred(B)`
is `f_⋄(p) = im(f ∘ π_p)` for *any* comprehension `π_p` of `p`, and
`f^□(p) = (f^⋄(p^⊥))^⊥`.  Thesis B's `diaPull`, `diaPush` (with a chosen
comprehension) and `boxPull`; the clause below is the independence of `f_⋄`
from the comprehension. -/
theorem rec68 (f : X ⟶ Y) (s : SPred X) {W : C} {π : W ⟶ X}
    (hπ : IsComprehension s.1 π) (t : SPred Y) :
    (diaPull f t).1 = ceilPred (f ≫ t.1) ∧ (diaPush f s).1 = imPred (π ≫ f) ∧
      boxPull f t = (diaPull f t.orth).orth := by
  refine ⟨rfl, ?_, rfl⟩
  obtain ⟨θ, hθ, e, -⟩ := compr_basics_2 hπ (isComprehension_comprMap s.1)
  show imPred (comprMap s.1 ≫ f) = imPred (π ≫ f)
  rw [← e, Category.assoc]
  exact ((im_ineq (comprMap s.1 ≫ f) θ).2 θ hθ).symm

/-- **REC 69** (`prop:galois-properties`, short.tex:1194, Proposition) a):
`f^⋄` and `f^□` are monotone.  Thin: 207II. -/
theorem rec69_a (f : X ⟶ Y) {s t : SPred Y} (h : s.1 ≼ t.1) :
    (diaPull f s).1 ≼ (diaPull f t).1 ∧ (boxPull f s).1 ≼ (boxPull f t).1 :=
  exc_diam_order_pres f h

/-- **REC 69** (`prop:galois-properties`, short.tex:1194, Proposition) b): for
`p ∈ SPred(B)`, `q ∈ SPred(A)` (printed `SEff`), `f^⋄(p) ≤ q^⊥ ⟺ f_⋄(q) ≤ p^⊥`.
Thin: 207III. -/
theorem rec69_b (f : X ⟶ Y) (p : SPred Y) (q : SPred X) :
    (diaPull f p).1 ≼ orth q.1 ↔ (diaPush f q).1 ≼ orth p.1 :=
  diamond_adjunction f p q

/-- **REC 69** (`prop:galois-properties`, short.tex:1194, Proposition) c):
`f_⋄ ⊣ f^□` is a Galois connection.  (The printed proof exchanges `p` and `q`
in its middle step.)  Thin: 207III, reformulated. -/
theorem rec69_c (f : X ⟶ Y) (q : SPred X) (p : SPred Y) :
    (diaPush f q).1 ≼ p.1 ↔ q.1 ≼ (boxPull f p).1 :=
  diamond_adjunction' f q p

/-- **REC 69** (`prop:galois-properties`, short.tex:1194, Proposition) d):
`f_⋄` is monotone.  Thin: 207V.1. -/
theorem rec69_d (f : X ⟶ Y) {s t : SPred X} (h : s.1 ≼ t.1) :
    (diaPush f s).1 ≼ (diaPush f t).1 :=
  order_adj_basics_1 f h

/-- **REC 69** (`prop:galois-properties`, short.tex:1194, Proposition) e):
`f_⋄ ∘ f^□ ∘ f_⋄ = f_⋄`.  Thin: 207V.5. -/
theorem rec69_e (f : X ⟶ Y) (s : SPred X) :
    diaPush f (boxPull f (diaPush f s)) = diaPush f s :=
  order_adj_basics_5 f s

/-- **REC 69** (`prop:galois-properties`, short.tex:1194, Proposition) f):
`id^⋄ = id_⋄ = id^□ = id`.  Thin: 207VI. -/
theorem rec69_f :
    (∀ s : SPred X, diaPull (𝟙 X) s = s) ∧ (∀ s : SPred X, diaPush (𝟙 X) s = s) ∧
      ∀ s : SPred X, boxPull (𝟙 X) s = s :=
  ⟨diaPull_id, diaPush_id, boxPull_id⟩

/-- **REC 69** (`prop:galois-properties`, short.tex:1194, Proposition) g):
`(f ∘ g)^⋄ = g^⋄ ∘ f^⋄` and `(f ∘ g)^□ = g^□ ∘ f^□`, for `g : X → Y` and
`f : Y → Z` (the point's hypotheses give `f : A → B`, `g : B → C`, for which
only `g ∘ f` is defined; the composable reading is the one below).  Thin: 207VI. -/
theorem rec69_g (g : X ⟶ Y) (f : Y ⟶ Z) :
    (∀ s : SPred Z, diaPull (g ≫ f) s = diaPull g (diaPull f s)) ∧
      ∀ s : SPred Z, boxPull (g ≫ f) s = boxPull g (boxPull f s) :=
  ⟨diaPull_comp g f, boxPull_comp g f⟩

/-- **REC 69** (`prop:galois-properties`, short.tex:1194, Proposition) h):
`(f ∘ g)_⋄ = f_⋄ ∘ g_⋄`.  Thin: 207VI. -/
theorem rec69_h (g : X ⟶ Y) (f : Y ⟶ Z) (s : SPred X) :
    diaPush (g ≫ f) s = diaPush f (diaPush g s) :=
  diaPush_comp g f s

/-- **REC 70** (short.tex:1234, Definition): `f : A → B` and `g : B → A` are
**⋄-adjoint** when `f^⋄ = g_⋄`; an endomap is **⋄-self-adjoint** when
`f^⋄ = f_⋄`.  Thesis B's `DiamondAdjoint`, `DiamondSelfAdjoint` (206II.1–2). -/
theorem rec70_diamondAdjoint_iff (f : X ⟶ Y) (g : Y ⟶ X) (e : X ⟶ X) :
    (DiamondAdjoint f g ↔ diaPull f = diaPush g) ∧
      (DiamondSelfAdjoint e ↔ diaPull e = diaPush e) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- **REC 71** (short.tex:1238, Lemma): ⋄-adjointness is symmetric,
`f^⋄ = g_⋄ ⟺ g^⋄ = f_⋄`.  The paper's proof: REC 69 b) twice gives
`f_⋄(p) ≤ q^⊥ ⟺ g^⋄(p) ≤ q^⊥` for all sharp `q`, and one takes
`q := f_⋄(p)^⊥` and `q := g^⋄(p)^⊥`.  (Thesis B's 209II.1 is the same fact.) -/
theorem rec71 (f : X ⟶ Y) (g : Y ⟶ X) : DiamondAdjoint f g ↔ DiamondAdjoint g f := by
  have key : ∀ {A B : C} (f : A ⟶ B) (g : B ⟶ A), DiamondAdjoint f g →
      diaPush f = diaPull g := by
    intro A B f g h
    funext p
    have step : ∀ q : SPred B,
        ((diaPush f p).1 ≼ orth q.1 ↔ (diaPull g p).1 ≼ orth q.1) := by
      intro q
      rw [← rec69_b f q p, h, ← rec69_b g p q]
    apply Subtype.ext
    apply eabasics_le_antisymm
    · have := (step (diaPull g p).orth).2
      rw [spred_orth_val, eabasics_orth_orth] at this
      exact this (pcm_preorder_refl _)
    · have := (step (diaPush f p).orth).1
      rw [spred_orth_val, eabasics_orth_orth] at this
      exact this (pcm_preorder_refl _)
  exact ⟨fun h => (key f g h).symm, fun h => (key g f h).symm⟩

/-- **REC 72** (short.tex:1250, Remark): a map `f` is **rigid** if every `g`
with `f^⋄ = g^⋄` and `1 ∘ f = 1 ∘ g` equals `f`.  (The remark's claims — that
`⋄`-adjoints are not unique and that not every map is rigid — are about
examples, `½ f` and von Neumann algebras, and are not formalised.) -/
def IsRigid (f : X ⟶ Y) : Prop :=
  ∀ g : X ⟶ Y, diaPull f = diaPull g → f ≫ truth Y = g ≫ truth Y → f = g

end Diamond

/-! ### Compatible filters and comprehensions; assert maps -/

section Compatible

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **REC 74** (`def:compatible-quotients-comprehensions`, short.tex:1270,
Definition): in an effectus with filters and comprehensions, the filters and
comprehensions are **compatible** when for every comprehension `π_p` of a
*sharp* predicate `p` there is a filter `ξ^p` of `p` with `ξ^p ∘ π_p = id`. -/
class CompatibleFiltersComprehensions (C : Type u) [Category.{v} C]
    [HasFiniteCoproducts C] [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C]
    [EffectusPartialForm C] : Prop where
  compatible : ∀ {W X : C} {p : Pred X} (π : W ⟶ X), IsSharp p → IsComprehension p π →
    ∃ ξ : X ⟶ W, IsFilter p ξ ∧ π ≫ ξ = 𝟙 W

variable [HasFilters C] [HasComprehension C] [CompatibleFiltersComprehensions C]

/-- The chosen compatible filter for the chosen comprehension of a sharp `p`. -/
noncomputable def compatFilter {X : C} (p : Pred X) (hp : IsSharp p) :
    X ⟶ comprObj p :=
  (CompatibleFiltersComprehensions.compatible (comprMap p) hp
    (isComprehension_comprMap p)).choose

theorem compatFilter_spec {X : C} (p : Pred X) (hp : IsSharp p) :
    IsFilter p (compatFilter p hp) ∧ comprMap p ≫ compatFilter p hp = 𝟙 _ :=
  (CompatibleFiltersComprehensions.compatible (comprMap p) hp
    (isComprehension_comprMap p)).choose_spec

/-- **REC 75** (`def:sharp-assert`, short.tex:1277, Definition): the **assert
map** of a sharp predicate `p` is `asrt_p := π_p ∘ ξ^p` for a compatible pair
of a comprehension and a filter for `p` (here: the chosen ones). -/
noncomputable def asrtSharp {X : C} (p : Pred X) (hp : IsSharp p) : X ⟶ X :=
  compatFilter p hp ≫ comprMap p

/-- **REC 75** (`def:sharp-assert`, short.tex:1277, Definition), well-definedness
(the paragraph after the definition): any compatible pair `π'`, `ξ'` for `p`
gives the same map, `π' ∘ ξ' = asrt_p` — the two comprehensions differ by an
isomorphism `Θ₁`, the two filters by `Θ₂`, and `id = ξ' ∘ π'` forces
`Θ₂ = Θ₁⁻¹`. -/
theorem asrtSharp_eq {X W : C} {p : Pred X} (hp : IsSharp p) {π : W ⟶ X}
    {ξ : X ⟶ W} (hπ : IsComprehension p π) (hξ : IsFilter p ξ) (hc : π ≫ ξ = 𝟙 W) :
    ξ ≫ π = asrtSharp p hp := by
  obtain ⟨hξ0, hc0⟩ := compatFilter_spec p hp
  -- `π = Θ₁ ≫ π_p`
  obtain ⟨θ₁, hθ₁, e₁, -⟩ := compr_basics_2 hπ (isComprehension_comprMap p)
  -- `ξ_p ≫ Θ₂ = ξ`
  obtain ⟨θ₂, -, e₂, -⟩ := quotient_basics_2 ((isFilter_iff_isQuotient _ _).1 hξ)
    ((isFilter_iff_isQuotient _ _).1 hξ0)
  have := hθ₁
  -- `id = π ≫ ξ = Θ₁ ≫ π_p ≫ ξ_p ≫ Θ₂ = Θ₁ ≫ Θ₂`
  have h12 : θ₁ ≫ θ₂ = 𝟙 W := by
    rw [← hc, ← e₁, ← e₂, Category.assoc, ← Category.assoc (comprMap p), hc0,
      Category.id_comp]
  have h21 : θ₂ ≫ θ₁ = 𝟙 _ := by
    have : θ₂ = inv θ₁ := by
      rw [← Category.id_comp θ₂, ← IsIso.inv_hom_id θ₁, Category.assoc, h12,
        Category.comp_id]
    rw [this, IsIso.inv_hom_id]
  rw [← e₁, ← e₂, Category.assoc, ← Category.assoc θ₂, h21, Category.id_comp]
  rfl

/-- **REC 75** (`def:sharp-assert`, short.tex:1277), the paragraph after the
definition: `asrt_p ∘ asrt_p = asrt_p`. -/
theorem asrtSharp_idem {X : C} (p : Pred X) (hp : IsSharp p) :
    asrtSharp p hp ≫ asrtSharp p hp = asrtSharp p hp := by
  simp only [asrtSharp, Category.assoc]
  rw [← Category.assoc (comprMap p), (compatFilter_spec p hp).2, Category.id_comp]

/-- Helper: precomposing with an epimorphism does not change the image. -/
theorem isImage_comp_epi {W X Y : C} (ξ : W ⟶ X) [Epi ξ] {f : X ⟶ Y} {i : Pred Y}
    (hf : IsImage f i) : IsImage (ξ ≫ f) i := by
  refine ⟨by rw [Category.assoc, hf.1, Category.assoc], fun q hq => hf.2 q ?_⟩
  rw [Category.assoc, Category.assoc] at hq
  exact (cancel_epi ξ).1 hq

/-- **REC 75** (short.tex:1289, the sentence after Example 76):
`1 ∘ asrt_p = im(asrt_p) = p`. -/
theorem asrtSharp_truth_image [HasImages C] {X : C} (p : Pred X) (hp : IsSharp p) :
    asrtSharp p hp ≫ truth X = p ∧ IsImage (asrtSharp p hp) p := by
  have := hasQuotients_of_hasFilters (C := C)
  obtain ⟨hξ, -⟩ := compatFilter_spec p hp
  have : Epi (compatFilter p hp) :=
    quotient_basics_6 ((isFilter_iff_isQuotient _ _).1 hξ)
  refine ⟨?_, ?_⟩
  · rw [asrtSharp, Category.assoc, compr_total (isComprehension_comprMap p)]
    exact (rec27 (C := C)).2.2.1 hξ
  · refine isImage_comp_epi _ ?_
    have h := isImage_imPred (comprMap p)
    rwa [(img_of_compr p).2 p hp] at h

/-- **REC 77** (`lem:assert-image`, short.tex:1291, Lemma) a): for a sharp `p`
and `f : B → A`, `im f ≤ p ⟺ asrt_p ∘ f = f`.  The paper's proof (thesis B's
211XV is the same statement in an &-effectus). -/
theorem rec77_a [HasImages C] {X B : C} (p : Pred X) (hp : IsSharp p) (f : B ⟶ X) :
    imPred f ≼ p ↔ f ≫ asrtSharp p hp = f := by
  obtain ⟨-, hc⟩ := compatFilter_spec p hp
  constructor
  · intro h
    -- `p ∘ f = 1 ∘ f`
    have hpf : f ≫ p = f ≫ truth X := by
      refine eabasics_le_antisymm (comp_le_comp f (pred_le_truth p)) ?_
      rw [← (isImage_imPred f).1]
      exact comp_le_comp f h
    obtain ⟨g, hg, -⟩ := (isComprehension_comprMap p).2 f hpf
    -- `f̄ = ξ^p ∘ π_p ∘ f̄ = ξ^p ∘ f`, so `f = π_p ∘ ξ^p ∘ f`
    rw [← hg, asrtSharp, ← Category.assoc, Category.assoc g, hc, Category.comp_id]
  · intro h
    have h1 := (rec63 (asrtSharp p hp) f (isImage_imPred (f ≫ asrtSharp p hp))
      (asrtSharp_truth_image p hp).2).1
    rwa [h] at h1

/-- **REC 77** (`lem:assert-image`, short.tex:1291, Lemma) b): for a sharp `p`
and `g : A → B`, `1 ∘ g ≤ p ⟺ g ∘ asrt_p = g`.  The paper's proof. -/
theorem rec77_b [HasImages C] {X B : C} (p : Pred X) (hp : IsSharp p) (g : X ⟶ B) :
    (g ≫ truth B) ≼ p ↔ asrtSharp p hp ≫ g = g := by
  obtain ⟨hξ, hc⟩ := compatFilter_spec p hp
  constructor
  · intro h
    obtain ⟨g', hg', -⟩ := hξ.2 g h
    -- `ḡ = ḡ ∘ ξ^p ∘ π_p = g ∘ π_p`, so `g = g ∘ π_p ∘ ξ^p`
    rw [← hg', asrtSharp, Category.assoc, ← Category.assoc (comprMap p), hc,
      Category.id_comp]
  · intro h
    rw [← h, Category.assoc]
    have := comp_le_comp (asrtSharp p hp) (pred_le_truth (g ≫ truth B))
    rwa [(asrtSharp_truth_image p hp).1] at this

end Compatible

/-! ### Pure maps -/

section Pure

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **REC 78** (`def:pure`, short.tex:1352, Definition): a map is **pure** when
it is `π ∘ ξ` for some filter `ξ` and comprehension `π`.  Thesis B's `IsPure`
(201II, quotient then comprehension) — the same, as filters are quotients. -/
theorem rec78_isPure_iff {X Y : C} (f : X ⟶ Y) :
    IsPure f ↔ ∃ (Q : C) (ξ : X ⟶ Q) (π : Q ⟶ Y) (p : Pred X) (q : Pred Y),
      IsFilter p ξ ∧ IsComprehension q π ∧ f = ξ ≫ π := by
  constructor
  · rintro ⟨Q, ξ, π, p, q, hξ, hπ, rfl⟩
    refine ⟨Q, ξ, π, orth p, q, ?_, hπ, rfl⟩
    rw [isFilter_iff_isQuotient, eabasics_orth_orth]
    exact hξ
  · rintro ⟨Q, ξ, π, p, q, hξ, hπ, rfl⟩
    exact ⟨Q, ξ, π, orth p, q, (isFilter_iff_isQuotient _ _).1 hξ, hπ, rfl⟩

/-- **REC 80** (short.tex:1369, Lemma), first item: in an effectus with filters,
a composition of filters is a filter: if `ξ^q` is a filter for `q` and `ξ^p` one
for `p` (a predicate on the codomain of `ξ^q`), then `ξ^p ∘ ξ^q` is a filter
for `p ∘ ξ^q`.  Thin: thesis B 197IX `quotients_composition`, whose proof is
the paper's. -/
theorem rec80_filters [HasFilters C] {X Y Z : C} {q : Pred X} {p : Pred Y}
    {ξq : X ⟶ Y} {ξp : Y ⟶ Z} (hq : IsFilter q ξq) (hp : IsFilter p ξp) :
    IsFilter (ξq ≫ p) (ξq ≫ ξp) := by
  have := hasQuotients_of_hasFilters (C := C)
  rw [isFilter_iff_isQuotient] at hq hp ⊢
  exact quotients_composition hq hp

/-- **REC 80** (short.tex:1369, Lemma), second item: if the effectus also has
images and compatible comprehensions, a composition of comprehensions is a
comprehension: `π_p ∘ π_q` is a comprehension for `im(π_p ∘ π_q)`.  The paper's
proof, which assumes `p` sharp (compatibility is only available for sharp
predicates); the general case reduces to it because `π_p` is also a
comprehension for the sharp predicate `⌊p⌋ = im π_p`
(`isComprehension_imPred'`). -/
theorem rec80_comprehensions [HasFilters C] [HasComprehension C] [HasImages C]
    [CompatibleFiltersComprehensions C] {V W X : C} {p : Pred X} {q : Pred W}
    {πp : W ⟶ X} {πq : V ⟶ W} (hp : IsComprehension p πp) (hq : IsComprehension q πq) :
    IsComprehension (imPred (πq ≫ πp)) (πq ≫ πp) := by
  have := hasQuotients_of_hasFilters (C := C)
  -- replace `p` by the sharp predicate `p' = im π_p`
  set p' := imPred πp with hp'def
  have hp' : IsComprehension p' πp := isComprehension_imPred' hp
  have hsharp : IsSharp p' := ⟨_, _, isImage_imPred πp⟩
  obtain ⟨ξ, -, hc⟩ :=
    CompatibleFiltersComprehensions.compatible πp hsharp hp'
  set r := imPred (πq ≫ πp) with hr
  have hr1 : (πq ≫ πp) ≫ r = (πq ≫ πp) ≫ truth X := (isImage_imPred _).1
  -- `im(π_p ∘ π_q) ≤ im π_p = p'`
  have hrp : r ≼ p' := (rec63 πp πq (isImage_imPred _) (isImage_imPred _)).1
  -- `im(π_p ∘ π_q) ≤ q ∘ ξ^p`
  have hrq : r ≼ ξ ≫ q := by
    refine (isImage_imPred (πq ≫ πp)).2 _ ?_
    rw [Category.assoc, ← Category.assoc πp, hc, Category.id_comp, hq.1,
      Category.assoc, compr_total hp]
  refine ⟨hr1, fun B f hf => ?_⟩
  -- `p' ∘ f = 1 ∘ f`
  have hf' : f ≫ p' = f ≫ truth X := by
    refine eabasics_le_antisymm (comp_le_comp f (pred_le_truth p')) ?_
    rw [← hf]
    exact comp_le_comp f hrp
  obtain ⟨g₁, hg₁, -⟩ := hp'.2 f hf'
  -- `q ∘ g₁ = 1 ∘ g₁`
  have hg₁q : g₁ ≫ q = g₁ ≫ truth W := by
    refine eabasics_le_antisymm (comp_le_comp g₁ (pred_le_truth q)) ?_
    have e1 : g₁ ≫ q = f ≫ ξ ≫ q := by
      rw [← hg₁, Category.assoc, ← Category.assoc πp, hc, Category.id_comp]
    have e2 : g₁ ≫ truth W = f ≫ r := by
      rw [hf, ← hg₁, Category.assoc, compr_total hp]
    rw [e1, e2]
    exact comp_le_comp f hrq
  obtain ⟨g₂, hg₂, -⟩ := hq.2 g₁ hg₁q
  refine ⟨g₂, ?_, fun g' hg' => ?_⟩
  · show g₂ ≫ πq ≫ πp = f
    rw [← Category.assoc, hg₂, hg₁]
  · have hg'' : g' ≫ πq ≫ πp = f := hg'
    have : Mono πp := compr_basics_5 hp
    have : Mono πq := compr_basics_5 hq
    exact (cancel_mono (πq ≫ πp)).1 (by rw [hg'', ← Category.assoc, hg₂, hg₁])

end Pure

/-! ### Further properties of ⋄-effectuses (§3.5) -/

section DiamondFurther

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [DiamondEffectus C]

/-- **REC 82** (`lem:ortho-sharp`, short.tex:1419, Lemma): a sharp predicate `p`
in a ⋄-effectus is **ortho-sharp**: `p ∧ p^⊥ = 0`.  Thin: thesis B 208I
(`image_sharp_is_order_sharp`), whose argument is the paper's. -/
theorem rec82 {X : C} {p : Pred X} (hp : IsSharp p) : PCM.IsInf p (orth p) 0 :=
  ⟨zero_le_hom p, zero_le_hom _, fun q h1 h2 => by
    rw [image_sharp_is_order_sharp hp h1 h2]; exact pcm_preorder_refl _⟩

/-- **REC 83** (short.tex:1434, Lemma), first item: for sharp `p, q` the
supremum `p ∨ q` in `Pred(A)` exists and is sharp.  Thin: thesis B 204V
(`lattice_compr`), `p ∨ q = im [π_p, π_q]`. -/
theorem rec83_sup {X : C} {p q : Pred X} (hp : IsSharp p) (hq : IsSharp q) :
    ∃ j : Pred X, PCM.IsSup p q j ∧ IsSharp j :=
  ⟨_, lattice_compr hp hq⟩

/-- **REC 83** (short.tex:1434, Lemma), the formula of the proof: for sharp
`p, q`, `p ∧ q = (π_p)_⋄((π_p)^□(q))` in `SPred(A)`.  Thin: thesis B 208IX. -/
theorem rec83_inf {X : C} (s t : SPred X) :
    SPred.IsInf s t (diaPush (comprMap s.1) (boxPull (comprMap s.1) t)) :=
  spred_infimum s t

/-- **REC 83** (short.tex:1434, Lemma), second item: `SPred(A)` is an
ortholattice for the inherited order, with orthocomplement `p^⊥`.  Thin:
thesis B 208III gives the (stronger) orthomodular lattice. -/
theorem rec83_ortholattice (X : C) :
    ∃ ol : Ortholattice (SPred X), ∀ s t : SPred X,
      (letI := ol; (s ≤ t ↔ s.1 ≼ t.1) ∧ sᶜ = s.orth) := by
  obtain ⟨oml, h⟩ := diamond_oml X
  exact ⟨oml.toOrtholattice, h⟩

/-- **REC 84** (`prop:spred-is-oml`, short.tex:1455, Proposition):
`SPred(A)` is a sub-effect-algebra of `Pred(A)`, and an orthomodular lattice.
Thin: thesis B 208III (`diamond_oml_subEA`, `diamond_oml`). -/
theorem rec84 (X : C) :
    (∃ D : SubEffectAlgebra (Pred X), D.carrier = { p : Pred X | IsSharp p }) ∧
      ∃ oml : OrthomodularLattice (SPred X), ∀ s t : SPred X,
        (letI := oml; (s ≤ t ↔ s.1 ≼ t.1) ∧ sᶜ = s.orth) :=
  ⟨diamond_oml_subEA X, diamond_oml X⟩

/-- **REC 85** (short.tex:1465, Definition): `OMLatGal` is the category of
orthomodular lattices and Galois connections (Jacobs).  Thesis B's
`OMLatGalCat` (208VII). -/
abbrev OMLatGal : Type (u + 1) := OMLatGalCat.{u}

/-- **REC 86** (short.tex:1469, Proposition): `A ↦ SPred(A)`,
`f ↦ (f_⋄, f^□)` is a functor `C → OMLatGal`.  Thin: thesis B 208VII. -/
theorem rec86 :
    ∃ F : C ⥤ OMLatGal.{v},
      (∀ X : C, (F.obj X).carrier = SPred X) ∧
      ∀ (X Y : C) (f : X ⟶ Y),
        HEq (F.map f).push (diaPush f) ∧ HEq (F.map f).pull (boxPull f) :=
  diamond_omlatgal_functor

end DiamondFurther

end Papers.REC
