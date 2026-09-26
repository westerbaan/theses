/-
Papers/SIG/Pfn.lean

SIG's deterministic side: the σ-effectus `Pfn` of sets and partial functions
and the points around it — SIG 14 (`Pfn` is a σ-effectus; `St X ≅ X`,
`Pred X ≅ 𝒫 X`, `Tot Pfn ≅ Set`), SIG 22 (the scalars of `Pfn` are `{0,1}`),
SIG 32 (σ-weight `{0,1}`-modules are pointed sets), SIG 47
(`sWMod[{0,1}] ≃ Pfn`, a morphism of σ-effectuses), SIG 48 (a
substate-separated σ-effectus with scalars `{0,1}` embeds in `Pfn`), SIG 49
(the contravariant powerset functor `Pfn → ωBAᵒᵖ`) and SIG 50.

Design (see `Papers/SIG/PLAN.md`):
* `Pfn` is Mathlib's `PartialFun` (objects types, morphisms `X →. Y`, i.e.
  `X → Part Y`).  Its hom-sets carry the pointwise σ-PAM (`pointwiseSigmaPAM`)
  over the *pointed* σ-PAM of `Part Y`: a family of elements of a pointed set
  is summable iff at most one member differs from the point, and then the sum
  is that member (`pointedSigmaPAM`).  So a family of partial functions is
  summable iff their domains are pairwise disjoint, and the sum merges them,
  as printed.
* Countable coproducts are the Σ-types `Σ j, X j` with injections
  `x ↦ ⟨j, x⟩`; the unit is `PUnit`.
* The pointed σ-PAM also is the σ-PAM of every σ-weight `{0,1}`-module
  (SIG 32), which is how `sWMod[{0,1}]` becomes Mathlib's `Pointed`, and then
  `PartialFun` through Mathlib's `partialFunEquivPointed` (SIG 47).
-/
import Papers.SIG.WeightModules
import Mathlib.CategoryTheory.Category.PartialFun

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits Theses.B.Eff

namespace Papers.SIG

open SigmaPAM

universe u v w u' v' w'

/-! ## The pointed σ-PAM -/

section Pointed

variable {X : Type u} (x₀ : X)

/-- A family in a pointed set with **at most one** member different from the
point. -/
def AtMostOne {J : Type} (x : J → X) : Prop :=
  ∀ i j, x i ≠ x₀ → x j ≠ x₀ → i = j

open Classical in
/-- The sum of a family with at most one non-point member: that member, or the
point. -/
noncomputable def pointedSum {J : Type} (x : J → X) : X :=
  if h : ∃ j, x j ≠ x₀ then x h.choose else x₀

variable {x₀}

theorem pointedSum_eq {J : Type} {x : J → X} (hx : AtMostOne x₀ x) {j : J} (hj : x j ≠ x₀) :
    pointedSum x₀ x = x j := by
  have h : ∃ j, x j ≠ x₀ := ⟨j, hj⟩
  rw [pointedSum, dite_cond_eq_true (eq_true h), hx _ _ h.choose_spec hj]

theorem pointedSum_eq_point {J : Type} {x : J → X} (hx : ∀ j, x j = x₀) :
    pointedSum x₀ x = x₀ := by
  rw [pointedSum, dite_cond_eq_false (eq_false (by push Not; exact hx))]

theorem pointedSum_ne_iff {J : Type} {x : J → X} (hx : AtMostOne x₀ x) :
    pointedSum x₀ x ≠ x₀ ↔ ∃ j, x j ≠ x₀ := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    exact h (pointedSum_eq_point h')
  · rintro ⟨j, hj⟩
    rw [pointedSum_eq hx hj]; exact hj

theorem atMostOne_sub {J : Type} {x : J → X} (hx : AtMostOne x₀ x) {I : Type} (f : I → J)
    (hf : Function.Injective f) : AtMostOne x₀ (x ∘ f) :=
  fun i j hi hj => hf (hx _ _ hi hj)

variable (x₀)

/-- The **pointed σ-PAM** on a pointed set `(X, x₀)`: a countable family is
summable iff at most one member differs from `x₀`, and its sum is that member
(or `x₀`).  (The σ-PAM of `Part Y` behind `Pfn`'s hom-sets, SIG 14, and of
every σ-weight `{0,1}`-module, SIG 32.) -/
noncomputable def pointedSigmaPAM : SigmaPAM X where
  Summable x := AtMostOne x₀ x
  sum x _ := pointedSum x₀ x
  nonempty := ⟨x₀⟩
  summable_iff_partition {J K} _ _ x p := by
    constructor
    · intro hx
      refine ⟨fun k => atMostOne_sub hx _ Subtype.val_injective, ?_⟩
      intro k k' hk hk'
      obtain ⟨⟨i, rfl⟩, hi⟩ := (pointedSum_ne_iff (atMostOne_sub hx _ Subtype.val_injective)).1 hk
      obtain ⟨⟨j, rfl⟩, hj⟩ :=
        (pointedSum_ne_iff (atMostOne_sub hx _ Subtype.val_injective)).1 hk'
      exact congrArg p (hx i j hi hj)
    · rintro ⟨h, h'⟩ i j hi hj
      have hpi : pointedSum x₀ (fun j' : {j' // p j' = p i} => x j'.1) ≠ x₀ :=
        (pointedSum_ne_iff (h _)).2 ⟨⟨i, rfl⟩, hi⟩
      have hpj : pointedSum x₀ (fun j' : {j' // p j' = p j} => x j'.1) ≠ x₀ :=
        (pointedSum_ne_iff (h _)).2 ⟨⟨j, rfl⟩, hj⟩
      have e : p j = p i := h' _ _ hpj hpi
      exact congrArg Subtype.val (h (p i) ⟨i, rfl⟩ ⟨j, e⟩ hi hj)
  sum_partition {J K} _ _ x p hx h h' := by
    show pointedSum x₀ x = pointedSum x₀ _
    by_cases hex : ∃ j, x j ≠ x₀
    · obtain ⟨j, hj⟩ := hex
      have hb : pointedSum x₀ (fun j' : {j' // p j' = p j} => x j'.1) = x j :=
        pointedSum_eq (h _) (j := ⟨j, rfl⟩) hj
      rw [pointedSum_eq hx hj, pointedSum_eq h' (j := p j) (by rw [hb]; exact hj), hb]
    · push Not at hex
      rw [pointedSum_eq_point hex, pointedSum_eq_point]
      intro k
      exact pointedSum_eq_point fun j => hex j.1
  summable_unique x i j _ _ := Subsingleton.elim i j
  sum_unique {J} _ x _ := by
    show pointedSum x₀ x = x default
    by_cases hd : x default = x₀
    · rw [hd]; exact pointedSum_eq_point fun j => by rw [Subsingleton.elim j default]; exact hd
    · exact pointedSum_eq (fun i j _ _ => Subsingleton.elim i j) hd
  limit {J} _ x h i j hi hj := by
    classical
    have := h {i, j} ⟨i, by simp⟩ ⟨j, by simp⟩ hi hj
    exact congrArg Subtype.val this

/-- Sums in the pointed σ-PAM. -/
theorem pointed_sumsTo_iff {J : Type} [Countable J] (x : J → X) (s : X) :
    @SumsTo X (pointedSigmaPAM x₀) J _ x s ↔
      AtMostOne x₀ x ∧ (∀ j, x j ≠ x₀ → s = x j) ∧ ((∀ j, x j = x₀) → s = x₀) := by
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨hx, fun j hj => pointedSum_eq hx hj, fun h => pointedSum_eq_point h⟩
  · rintro ⟨hx, h1, h2⟩
    refine ⟨hx, ?_⟩
    show pointedSum x₀ x = s
    by_cases hex : ∃ j, x j ≠ x₀
    · obtain ⟨j, hj⟩ := hex
      rw [pointedSum_eq hx hj, h1 j hj]
    · push Not at hex
      rw [pointedSum_eq_point hex, h2 hex]

theorem pointed_summable_iff {J : Type} [Countable J] (x : J → X) :
    @Summable X (pointedSigmaPAM x₀) J _ x ↔ AtMostOne x₀ x := Iff.rfl

end Pointed

/-! ## SIG 14: the σ-effectus `Pfn` -/

/-- The σ-PAM on `Part Y`: the pointed σ-PAM at `Part.none` (a family is
summable iff at most one member is defined). -/
noncomputable instance partSigmaPAM (Y : Type u) : SigmaPAM (Part Y) :=
  pointedSigmaPAM Part.none

theorem part_ne_none_iff {Y : Type u} (o : Part Y) : o ≠ Part.none ↔ o.Dom := by
  rw [Ne, Part.eq_none_iff']; exact not_not

theorem part_sumsTo_iff {Y : Type u} {J : Type} [Countable J] (x : J → Part Y) (s : Part Y) :
    SumsTo x s ↔ (∀ i j, (x i).Dom → (x j).Dom → i = j) ∧ (∀ j, (x j).Dom → s = x j) ∧
      ((∀ j, ¬(x j).Dom) → ¬s.Dom) := by
  rw [show SumsTo x s ↔ _ from pointed_sumsTo_iff (Part.none : Part Y) x s]
  simp only [AtMostOne, part_ne_none_iff, ← Part.eq_none_iff']

theorem part_summable_iff {Y : Type u} {J : Type} [Countable J] (x : J → Part Y) :
    Summable x ↔ ∀ i j, (x i).Dom → (x j).Dom → i = j := by
  show AtMostOne _ x ↔ _
  simp only [AtMostOne, part_ne_none_iff]

/-- `o.bind` is σ-additive in the function argument. -/
theorem part_sumsTo_bind_left {X : Type u} {Y : Type v} {J : Type} [Countable J] (o : Part X)
    {f : J → X → Part Y} {s : X → Part Y} (h : ∀ a, SumsTo (fun j => f j a) (s a)) :
    SumsTo (fun j => o.bind (f j)) (o.bind s) := by
  rcases Part.eq_none_or_eq_some o with rfl | ⟨a, rfl⟩
  · simp only [Part.bind_none]
    exact (part_sumsTo_iff _ _).2 ⟨fun _ _ h => h.elim, fun _ h => h.elim, fun _ h => h⟩
  · simp only [Part.bind_some]; exact h a

/-- `(-).bind g` is σ-additive. -/
theorem part_sumsTo_bind_right {X : Type u} {Y : Type v} {J : Type} [Countable J]
    {x : J → Part X} {s : Part X} (h : SumsTo x s) (g : X → Part Y) :
    SumsTo (fun j => (x j).bind g) (s.bind g) := by
  rw [part_sumsTo_iff] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i j hi hj => h1 i j (Part.bind_dom.1 hi).1 (Part.bind_dom.1 hj).1,
    fun j hj => by rw [h2 j (Part.bind_dom.1 hj).1], fun hn hs => ?_⟩
  obtain ⟨hs', -⟩ := Part.bind_dom.1 hs
  by_cases hex : ∃ j, (x j).Dom
  · obtain ⟨j, hj⟩ := hex
    rw [h2 j hj] at hs
    exact hn j hs
  · push Not at hex
    exact h3 hex hs'

namespace Pfn

/-- The data of the pointwise σ-PAM on `Pfn(X, Y) = X → Part Y`. -/
theorem homData (X Y : Type u) :
    PointwiseData (H := X →. Y) (D := X) (E := fun _ => Part Y) (fun f a => f a) where
  inj f g h := funext fun a => congrFun h a
  nonempty := ⟨fun _ => Part.none⟩
  sub f P := by
    rintro ⟨g, hg⟩
    exact ⟨fun a => sum _ (summable_subfamily (hg a).summable P), fun a => sumsTo_sum _⟩
  lim f h := by
    refine ⟨fun a => sum (fun j => f j a) (limit _ fun F => ?_), fun a => sumsTo_sum _⟩
    obtain ⟨g, hg⟩ := h F
    exact (hg a).summable

/-- **SIG 14** (`ex:pfn`, main.tex:537): the σ-PAM on the hom-sets of `Pfn`:
pointwise sums in `Part Y`. -/
noncomputable instance pfunSigmaPAM (X Y : Type u) : SigmaPAM (X →. Y) :=
  pointwiseSigmaPAM (homData X Y)

/-- **SIG 14**: the σ-PAM on `Pfn(X, Y)`. -/
noncomputable instance homSigmaPAM (X Y : PartialFun.{u}) : SigmaPAM (X ⟶ Y) :=
  pfunSigmaPAM X Y

theorem hom_sumsTo_iff {X Y : Type u} {J : Type} [Countable J] (f : J → (X →. Y))
    (g : X →. Y) : SumsTo f g ↔ ∀ a, SumsTo (fun j => (f j a : Part Y)) (g a) :=
  pointwise_sumsTo_iff (homData X Y) f g

/-- **SIG 14** (`ex:pfn`, main.tex:537, Example): partial functions are
summable iff their domains of definition are pairwise disjoint. -/
theorem hom_summable_iff {X Y : Type u} {J : Type} [Countable J] (f : J → (X →. Y)) :
    Summable f ↔ ∀ a i j, (f i a).Dom → (f j a).Dom → i = j := by
  constructor
  · rintro ⟨g, hg⟩ a
    exact ((part_sumsTo_iff _ _).1 (hg a)).1
  · intro h
    refine ⟨fun a => sum (fun j => (f j a : Part Y)) ((part_summable_iff _).2 (h a)),
      fun a => sumsTo_sum _⟩

/-- **SIG 14** (`ex:pfn`, main.tex:539, Example): the sum of partial
functions with pairwise disjoint domains merges them: `y ∈ (⋁ f) a` iff
`y ∈ f j a` for some `j`. -/
theorem hom_sumsTo_iff' {X Y : Type u} {J : Type} [Countable J] (f : J → (X →. Y))
    (g : X →. Y) : SumsTo f g ↔ (∀ a i j, (f i a).Dom → (f j a).Dom → i = j) ∧
      ∀ a y, y ∈ g a ↔ ∃ j, y ∈ f j a := by
  rw [hom_sumsTo_iff]
  constructor
  · intro h
    refine ⟨fun a => ((part_sumsTo_iff _ _).1 (h a)).1, fun a y => ?_⟩
    obtain ⟨-, h2, h3⟩ := (part_sumsTo_iff _ _).1 (h a)
    constructor
    · intro hy
      by_contra hn
      push Not at hn
      refine h3 (fun j hj => ?_) (Part.dom_iff_mem.2 ⟨y, hy⟩)
      exact hn j (h2 j hj ▸ hy)
    · rintro ⟨j, hj⟩
      rw [h2 j (Part.dom_iff_mem.2 ⟨y, hj⟩)]; exact hj
  · rintro ⟨h1, h2⟩ a
    refine (part_sumsTo_iff _ _).2 ⟨h1 a, fun j hj => Part.ext fun y => ?_, fun hn hg => ?_⟩
    · rw [h2 a y]
      constructor
      · rintro ⟨k, hk⟩
        rwa [h1 a j k hj (Part.dom_iff_mem.2 ⟨y, hk⟩)]
      · intro hy; exact ⟨j, hy⟩
    · obtain ⟨j, hj⟩ := (h2 a _).1 (Part.get_mem hg)
      exact hn j (Part.dom_iff_mem.2 ⟨_, hj⟩)

/-- Binary sums of partial functions: `f ⊥ g` iff their domains are disjoint,
and then `f ⊕ g` is defined where one of them is, with that value. -/
theorem pair_sumsTo_iff {X Y : Type u} (f g s : X →. Y) :
    SumsTo ![f, g] s ↔ (∀ a, ¬((f a).Dom ∧ (g a).Dom)) ∧ ∀ a y, y ∈ s a ↔ y ∈ f a ∨ y ∈ g a := by
  rw [hom_sumsTo_iff']
  refine and_congr ⟨fun h a ⟨hf, hg⟩ => absurd (h a 0 1 hf hg) (by decide), fun h a i j hi hj => ?_⟩
    (forall_congr' fun a => forall_congr' fun y => by simp [Fin.exists_fin_two])
  fin_cases i <;> fin_cases j
  · rfl
  · exact (h a ⟨hi, hj⟩).elim
  · exact (h a ⟨hj, hi⟩).elim
  · rfl

theorem pair_summable_iff {X Y : Type u} (f g : X →. Y) :
    Summable ![f, g] ↔ ∀ a, ¬((f a).Dom ∧ (g a).Dom) := by
  rw [hom_summable_iff]
  refine ⟨fun h a ⟨hf, hg⟩ => absurd (h a 0 1 hf hg) (by decide), fun h a i j hi hj => ?_⟩
  fin_cases i <;> fin_cases j
  · rfl
  · exact (h a ⟨hi, hj⟩).elim
  · exact (h a ⟨hj, hi⟩).elim
  · rfl

/-- Summability is inherited by families with smaller domains. -/
theorem summable_of_dom {X Y Z : Type u} {J : Type} [Countable J] {f : J → (X →. Y)}
    (hf : Summable f) (g : J → (X →. Z)) (h : ∀ j a, (g j a).Dom → (f j a).Dom) : Summable g :=
  (hom_summable_iff g).2 fun a i j hi hj =>
    (hom_summable_iff f).1 hf a i j (h i a hi) (h j a hj)

theorem comp_apply {X Y Z : PartialFun.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : X) :
    (f ≫ g) a = (f a).bind g := rfl

theorem id_apply {X : PartialFun.{u}} (a : X) : (𝟙 X : X ⟶ X) a = Part.some a := rfl

theorem zero_apply {X Y : PartialFun.{u}} (a : X) : (0 : X ⟶ Y) a = Part.none := by
  have h := (hom_sumsTo_iff (X := X) (Y := Y) (Empty.elim : Empty → (X ⟶ Y)) _).1
    (sumsTo_of_isEmpty (M := X ⟶ Y) _) a
  exact Part.eq_none_iff'.2 (((part_sumsTo_iff _ _).1 h).2.2 fun j => j.elim)

theorem hom_ext {X Y : PartialFun.{u}} {f g : X ⟶ Y} (h : ∀ a, f a = g a) : f = g := funext h

/-! ### Countable coproducts -/

/-- **SIG 14** (`ex:pfn`, main.tex:527): the coproduct of `(X_j)_j` in `Pfn`
is the disjoint union `Σ j, X_j` with the injections `x ↦ ⟨j, x⟩`. -/
def sigmaCofan {J : Type} (X : J → PartialFun.{u}) : Cofan X :=
  Cofan.mk (PartialFun.of (Σ j, (X j : Type u)))
    fun j => (fun x => Part.some ⟨j, x⟩ : (X j : Type u) →. Σ j, (X j : Type u))

/-- The cotuple of `(f_j : X_j ⇀ Y)_j`. -/
def sigmaDesc {J : Type} {X : J → PartialFun.{u}} {Y : PartialFun.{u}} (f : ∀ j, X j ⟶ Y) :
    (sigmaCofan X).pt ⟶ Y :=
  (fun p => f p.1 p.2 : (Σ j, (X j : Type u)) →. (Y : Type u))

theorem sigmaCofan_inj_apply {J : Type} (X : J → PartialFun.{u}) (j : J) (x : X j) :
    (sigmaCofan X).inj j x = Part.some ⟨j, x⟩ := rfl

/-- **SIG 14**: `Σ j, X_j` is a coproduct in `Pfn`. -/
def sigmaCofanIsColimit {J : Type} (X : J → PartialFun.{u}) : IsColimit (sigmaCofan X) :=
  Cofan.IsColimit.mk _ (fun t => sigmaDesc t.inj)
    (fun t j => funext fun x => Part.bind_some _ _)
    (fun t m hm => funext fun ⟨j, x⟩ => by
      exact (Part.bind_some _ _).symm.trans (congrFun (hm j) x))

instance hasCoproductsOfShape (J : Type) : HasCoproductsOfShape J PartialFun.{u} :=
  ⟨fun F => by
    have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
      HasColimit.mk ⟨_, sigmaCofanIsColimit (F.obj ∘ Discrete.mk)⟩
    exact hasColimit_of_iso Discrete.natIsoFunctor⟩

instance : HasCountableCoproducts PartialFun.{u} :=
  ⟨fun _ _ => inferInstance⟩

/-- Mathlib's chosen coproduct `∐ X` is `Σ j, X_j`. -/
noncomputable def coprodIso {J : Type} (X : J → PartialFun.{u}) :
    ∐ X ≅ (sigmaCofan X).pt :=
  (colimit.isColimit _).coconePointUniqueUpToIso (sigmaCofanIsColimit X)

theorem ι_coprodIso {J : Type} (X : J → PartialFun.{u}) (j : J) :
    Sigma.ι X j ≫ (coprodIso X).hom = (sigmaCofan X).inj j :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk j)

open Classical in
/-- The partial projection of `Σ _ : J, B` onto the `i`-th summand. -/
noncomputable def cproj {J : Type} (B : PartialFun.{u}) (i : J) :
    (sigmaCofan (fun _ : J => B)).pt ⟶ B :=
  fun p => if p.1 = i then Part.some p.2 else Part.none

theorem cproj_apply_self {J : Type} (B : PartialFun.{u}) (i : J) (x : B) :
    cproj B i ⟨i, x⟩ = Part.some x := by
  simp [cproj]

theorem cproj_apply_ne {J : Type} (B : PartialFun.{u}) {i k : J} (h : k ≠ i) (x : B) :
    cproj B i ⟨k, x⟩ = Part.none := by
  simp [cproj, h]

theorem cproj_dom {J : Type} (B : PartialFun.{u}) {i : J} {p : (sigmaCofan (fun _ : J => B)).pt}
    (h : (cproj B i p).Dom) : p.1 = i := by
  by_contra hne
  obtain ⟨k, x⟩ := p
  rw [cproj_apply_ne B hne] at h
  exact h

/-- The partial projections of `∐_J B` are the projections of `Σ _ : J, B`. -/
theorem pproj_eq {J : Type} (B : PartialFun.{u}) (i : J) :
    pproj (fun _ : J => B) i = (coprodIso (fun _ : J => B)).hom ≫ cproj B i := by
  classical
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [← Category.assoc, ι_coprodIso]
  by_cases hk : k = i
  · subst hk
    rw [ι_pproj_self]
    exact funext fun x => ((Part.bind_some _ _).trans (cproj_apply_self B k x)).symm
  · rw [ι_pproj_ne _ hk]
    exact funext fun x => (zero_apply x).trans
      ((Part.bind_some _ _).trans (cproj_apply_ne B hk x)).symm

/-! ### `Pfn` is a σ-effectus -/

/-- **SIG 14** (`ex:pfn`, main.tex:527, Example): `Pfn` is a σ-PAC —
composition is σ-biadditive for the merge of disjoint partial functions,
compatible families (those factoring through `∐_J B`) have disjoint domains,
and untying holds. -/
instance sigmaPAC : SigmaPAC PartialFun.{u} where
  comp_sigmaBiadditive X Y Z := by
    refine ⟨fun g => isSigmaAdditive_of_sumsTo fun x s hs => ?_,
      fun f => isSigmaAdditive_of_sumsTo fun x s hs => ?_⟩
    · have hs' := (hom_sumsTo_iff (X := X) (Y := Y) _ _).1 hs
      exact (hom_sumsTo_iff (X := X) (Y := Z) _ _).2 fun a =>
        part_sumsTo_bind_right (hs' a) g
    · have hs' := (hom_sumsTo_iff (X := Y) (Y := Z) _ _).1 hs
      exact (hom_sumsTo_iff (X := X) (Y := Z) _ _).2 fun a =>
        part_sumsTo_bind_left (f a) hs'
  compatible_sum {J} _ {A B} f := by
    rintro ⟨h, hh⟩
    refine (hom_summable_iff (X := A) (Y := B) f).2 fun a i j hi hj => ?_
    rw [← hh i, pproj_eq, ← Category.assoc, comp_apply] at hi
    rw [← hh j, pproj_eq, ← Category.assoc, comp_apply] at hj
    obtain ⟨hd, hi'⟩ := Part.bind_dom.1 hi
    obtain ⟨hd', hj'⟩ := Part.bind_dom.1 hj
    exact (cproj_dom _ hi').symm.trans (cproj_dom _ hj')
  untying {A B f g} h := by
    refine summable_of_dom (X := A) (Y := B) (Z := (B ⨿ B : PartialFun.{u})) h _ fun j a hj => ?_
    fin_cases j
    · exact (Part.bind_dom.1 hj).1
    · exact (Part.bind_dom.1 hj).1

/-- The sum of two partial functions with disjoint domains: `y ∈ (f ⊕ g) a`
iff `y ∈ f a` or `y ∈ g a`. -/
theorem mem_pairSum {X Y : Type u} {f g : X →. Y} (h : Summable ![f, g]) (a : X) (y : Y) :
    y ∈ sum ![f, g] h a ↔ y ∈ f a ∨ y ∈ g a :=
  ((pair_sumsTo_iff f g _).1 (sumsTo_sum h)).2 a y

theorem dom_pairSum {X Y : Type u} {f g : X →. Y} (h : Summable ![f, g]) (a : X) :
    (sum ![f, g] h a).Dom ↔ (f a).Dom ∨ (g a).Dom := by
  simp only [Part.dom_iff_mem, mem_pairSum h]
  constructor
  · rintro ⟨y, hy | hy⟩
    · exact Or.inl ⟨y, hy⟩
    · exact Or.inr ⟨y, hy⟩
  · rintro (⟨y, hy⟩ | ⟨y, hy⟩)
    · exact ⟨y, Or.inl hy⟩
    · exact ⟨y, Or.inr hy⟩

/-- The unit object `I = {*}` of `Pfn`. -/
abbrev unitObj : PartialFun.{u} := PUnit.{u + 1}

/-- A predicate `X ⇀ {*}` is determined by its domain. -/
theorem pred_ext {X : PartialFun.{u}} {p q : X ⟶ unitObj} (h : ∀ a, (p a).Dom ↔ (q a).Dom) :
    p = q :=
  funext fun a => Part.ext' (h a) fun _ _ => rfl

/-- The truth predicate: defined everywhere. -/
def truthPfn (X : PartialFun.{u}) : X ⟶ unitObj :=
  (fun _ => Part.some PUnit.unit : (X : Type u) →. PUnit.{u + 1})

/-- The orthosupplement of a predicate: defined exactly off its domain. -/
def orthPfn {X : PartialFun.{u}} (p : X ⟶ unitObj) : X ⟶ unitObj :=
  (fun a => ⟨¬(p a).Dom, fun _ => PUnit.unit⟩ : (X : Type u) →. PUnit.{u + 1})

theorem perp_iff {X Y : PartialFun.{u}} (f g : X ⟶ Y) :
    Perp f g ↔ ∀ a, ¬((f a).Dom ∧ (g a).Dom) :=
  pair_summable_iff (X := X) (Y := Y) f g

theorem ovee_dom {X Y : PartialFun.{u}} {f g : X ⟶ Y} (h : Perp f g) (a : X) :
    (ovee f g h a).Dom ↔ (f a).Dom ∨ (g a).Dom :=
  dom_pairSum (X := X) (Y := Y) h a

theorem comp_dom {X Y Z : PartialFun.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : X) :
    ((f ≫ g) a).Dom ↔ ∃ h : (f a).Dom, (g ((f a).get h)).Dom :=
  Part.bind_dom

theorem comp_truth_dom {X Y : PartialFun.{u}} (f : X ⟶ Y) (a : X) :
    ((f ≫ truthPfn Y) a).Dom ↔ (f a).Dom :=
  (comp_dom f _ a).trans ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩

theorem zero_dom {X Y : PartialFun.{u}} (a : X) : ¬((0 : X ⟶ Y) a).Dom := by
  rw [zero_apply]; exact Part.not_none_dom

/-- **SIG 14** (`ex:pfn`, main.tex:527, Example): the category `Pfn` of sets
and partial functions is a **σ-effectus**, with unit `I = {*}`: its
predicates `X ⇀ {*}` (subsets, by their domains) form an effect algebra with
truth the total predicate and orthosupplement the complement of the domain;
`1 ∘ f = 0` forces `f = 0` (empty domain); and `1 ∘ f ⊥ 1 ∘ g` (disjoint
domains) gives `f ⊥ g`. -/
noncomputable instance sigmaEffectus : SigmaEffectus PartialFun.{u} where
  I := unitObj
  one := truthPfn
  orth := orthPfn
  perp_orth p := (perp_iff _ _).2 fun _ ⟨h1, h2⟩ => h2 h1
  ovee_orth p := pred_ext fun a => by
    rw [ovee_dom]
    exact ⟨fun _ => trivial, fun _ => em _⟩
  orth_unique {X p q} h e := pred_ext fun a => by
    have hd := (ovee_dom h a).1 (e ▸ trivial)
    show (q a).Dom ↔ ¬(p a).Dom
    exact ⟨fun hq hp => (perp_iff p q).1 h a ⟨hp, hq⟩, fun hp => hd.resolve_left hp⟩
  eq_zero_of_perp_one {X p} h := pred_ext fun a =>
    ⟨fun hp => ((perp_iff p _).1 h a ⟨hp, trivial⟩).elim, fun h0 => (zero_dom a h0).elim⟩
  eq_zero_of_one_zero {X Y f} h := funext fun a => by
    rw [zero_apply]
    refine Part.eq_none_iff'.2 fun hf => zero_dom (Y := unitObj) a ?_
    rw [← h]
    exact (comp_truth_dom f a).2 hf
  perp_of_one_perp {X Y f g} h := by
    refine summable_of_dom (X := X) (Y := unitObj) (Z := Y) h ![f, g] fun j a hj => ?_
    fin_cases j
    · exact (comp_truth_dom f a).2 hj
    · exact (comp_truth_dom g a).2 hj

theorem effObj_eq : effObj PartialFun.{u} = unitObj := rfl

theorem truth_eq (X : PartialFun.{u}) : truth X = truthPfn X := rfl

theorem orth_eq {X : PartialFun.{u}} (p : Pred X) : orth p = orthPfn p := rfl

/-! ### SIG 14: states, predicates, total maps -/

theorem isTotal_const {X : PartialFun.{u}} (x : X) :
    IsTotal (C := PartialFun.{u}) (fun _ => Part.some x : unitObj.{u} ⟶ X) :=
  funext fun _ => Part.bind_some _ _

/-- **SIG 14** (`ex:pfn`, main.tex:544, Example): the states of `X` in `Pfn`
are its elements, `St X ≅ X`. -/
noncomputable def statEquiv (X : Type u) : Stat (PartialFun.of X) ≃ X where
  toFun ω := (ω.1 PUnit.unit).get <| (comp_truth_dom ω.1 PUnit.unit).1 <| by
    rw [show ω.1 ≫ truthPfn (PartialFun.of X) = truthPfn unitObj from ω.2]; trivial
  invFun x := ⟨fun _ => Part.some x, isTotal_const (X := PartialFun.of X) x⟩
  left_inv ω := Subtype.ext <| funext fun t => by
    cases t
    exact Part.some_get _
  right_inv x := rfl

/-- **SIG 14** (`ex:pfn`, main.tex:545, Example): the predicates on `X` in
`Pfn` are its subsets, `Pred X ≅ 𝒫 X`, via the domain of definition. -/
def predEquiv (X : Type u) : Pred (PartialFun.of X) ≃ Set X where
  toFun p := {a | (p a).Dom}
  invFun S := (fun a => ⟨a ∈ S, fun _ => PUnit.unit⟩ : X →. PUnit.{u + 1})
  left_inv p := pred_ext fun a => Iff.rfl
  right_inv S := rfl

/-- **SIG 14** (main.tex:545): the bijection `Pred X ≅ 𝒫 X` is an isomorphism
of effect algebras onto the Boolean effect algebra `𝒫 X` (SIG 8): it sends
truth to `X`, orthosupplement to complement, `⊥` to disjointness and `⊕` to
union. -/
theorem predEquiv_spec (X : Type u) :
    predEquiv X (truth (PartialFun.of X)) = Set.univ ∧
      (∀ p : Pred (PartialFun.of X), predEquiv X (orth p) = (predEquiv X p)ᶜ) ∧
      (∀ p q : Pred (PartialFun.of X), Perp p q ↔ Disjoint (predEquiv X p) (predEquiv X q)) ∧
      ∀ (p q : Pred (PartialFun.of X)) (h : Perp p q),
        predEquiv X (ovee p q h) = predEquiv X p ∪ predEquiv X q := by
  refine ⟨rfl, fun p => rfl, fun p q => ?_, fun p q h => Set.ext fun a => ovee_dom h a⟩
  refine (perp_iff p q).trans ?_
  rw [Set.disjoint_left]
  exact ⟨fun h a hp hq => h a ⟨hp, hq⟩, fun h a ⟨hp, hq⟩ => h hp hq⟩

/-- A total partial function is defined everywhere. -/
theorem dom_of_isTotal {X Y : PartialFun.{u}} {f : X ⟶ Y} (hf : IsTotal f) (a : X) :
    (f a).Dom :=
  (comp_truth_dom f a).1 (by rw [show f ≫ truthPfn Y = truthPfn X from hf]; trivial)

/-- The functor `Set → Tot(Pfn)`: a function as a total partial function. -/
def typeToTot : Type u ⥤ Tot PartialFun.{u} where
  obj T := Tot.of (PartialFun.of T)
  map g := ⟨fun x => Part.some (g x), funext fun _ => Part.bind_some _ _⟩
  map_id T := rfl
  map_comp f g := Subtype.ext <| funext fun x => (Part.bind_some _ _).symm

/-- The functor `Tot(Pfn) → Set`. -/
noncomputable def totToType : Tot PartialFun.{u} ⥤ Type u where
  obj X := (X.base : Type u)
  map f := TypeCat.ofHom fun x => (f.1 x).get (dom_of_isTotal f.2 x)
  map_id X := rfl
  map_comp f g := by
    ext x
    exact Part.get_eq_of_mem (Part.mem_bind (Part.get_mem (dom_of_isTotal f.2 x))
      (Part.get_mem (dom_of_isTotal g.2 _))) (dom_of_isTotal (f ≫ g).2 x)

/-- **SIG 14** (`ex:pfn`, main.tex:546, Example): the total maps of `Pfn` are
the everywhere-defined partial functions, and `Tot(Pfn) ≅ Set`. -/
noncomputable def totEquiv : Tot PartialFun.{u} ≌ Type u where
  functor := totToType
  inverse := typeToTot
  unitIso := NatIso.ofComponents (fun X => Iso.refl _) fun {X Y} f => by
    refine Subtype.ext (funext fun x => ?_)
    show (f.1 x).bind Part.some = (Part.some x).bind _
    exact (Part.bind_some_right _).trans ((Part.some_get (dom_of_isTotal f.2 x)).symm.trans
      (Part.bind_some _ _).symm)
  counitIso := NatIso.ofComponents (fun T => Iso.refl _) fun f => rfl
  functor_unitIso_comp X := rfl

/-! ## SIG 22: the scalars of `Pfn` -/

/-- A scalar of `Pfn` is determined by whether it is defined. -/
def scalDom (p : Scal PartialFun.{u}) : Prop := (p PUnit.unit).Dom

theorem scal_ext {p q : Scal PartialFun.{u}} (h : scalDom p ↔ scalDom q) : p = q :=
  pred_ext (X := unitObj) fun _ => h

theorem scalDom_mul (p q : Scal PartialFun.{u}) : scalDom (p * q) ↔ scalDom p ∧ scalDom q :=
  (comp_dom q p PUnit.unit).trans ⟨fun ⟨h, h'⟩ => ⟨h', h⟩, fun ⟨h', h⟩ => ⟨h, h'⟩⟩

open Classical in
/-- `Pfn({*},{*}) → {0,1}`: is the scalar defined? -/
noncomputable def scalToBool : EffectMonoidHom (Scal PartialFun.{u}) Bool where
  toFun p := decide (scalDom p)
  perp_map {p q} h := by
    have hn : ¬(scalDom p ∧ scalDom q) := (perp_iff p q).1 h PUnit.unit
    show (decide (scalDom p) && decide (scalDom q)) = false
    by_cases hp : scalDom p
    · have hq : ¬scalDom q := fun hq => hn ⟨hp, hq⟩
      simp [hp, hq]
    · simp [hp]
  ovee_map {p q} h := by
    have e : scalDom (ovee p q h) ↔ scalDom p ∨ scalDom q := ovee_dom h PUnit.unit
    show decide (scalDom (ovee p q h)) = (decide (scalDom p) || decide (scalDom q))
    by_cases hp : scalDom p <;> by_cases hq : scalDom q <;> simp [e, hp, hq]
  map_one := decide_eq_true trivial
  map_mul p q := by
    show decide (scalDom (p * q)) = (decide (scalDom p) && decide (scalDom q))
    by_cases hp : scalDom p <;> by_cases hq : scalDom q <;> simp [scalDom_mul, hp, hq]

/-- `{0,1} → Pfn({*},{*})`: `1` is the identity, `0` the empty function. -/
def boolScal (b : Bool) : Scal PartialFun.{u} :=
  (fun _ => ⟨b = true, fun _ => PUnit.unit⟩ : PUnit.{u + 1} →. PUnit.{u + 1})

/-- `{0,1} → Pfn({*},{*})` as an effect monoid morphism. -/
def boolToScal : EffectMonoidHom Bool (Scal PartialFun.{u}) where
  toFun := boolScal
  perp_map {b c} h := (perp_iff _ _).2 fun _ ⟨hb, hc⟩ => by
    change (b && c) = false at h
    change b = true at hb
    change c = true at hc
    simp [hb, hc] at h
  ovee_map {b c} h := scal_ext <| (iff_of_eq (Bool.or_eq_true b c)).trans (ovee_dom (f := boolScal b) (g := boolScal c) _ PUnit.unit).symm
  map_one := scal_ext ⟨fun _ => trivial, fun _ => rfl⟩
  map_mul b c := scal_ext <| (iff_of_eq (Bool.and_eq_true b c)).trans
    (scalDom_mul (boolScal b) (boolScal c)).symm

open Classical in
/-- **SIG 22** (`ex:booleanalgebra`, main.tex:711, Example): in `Pfn` the
scalars are `{0,1}`: the effect monoid `Pfn({*}, {*})` is isomorphic to the
Boolean effect monoid `Bool`, a scalar being determined by whether it is
defined. -/
theorem scalars_bool : EMIso (Scal PartialFun.{u}) Bool :=
  ⟨scalToBool, boolToScal,
    fun p => scal_ext (show scalDom (boolScal (decide (scalDom p))) ↔ scalDom p from
      decide_eq_true_iff),
    fun b => Bool.eq_iff_iff.2
      (show decide (scalDom (boolScal b)) = true ↔ b = true from decide_eq_true_iff)⟩

end Pfn

end Papers.SIG

namespace Papers.SIG

open SigmaPAM

/-! ## SIG 32: σ-weight `{0,1}`-modules are pointed sets -/

section BoolModules

theorem pointed_zero {X : Type u} (x₀ : X) : @zero X (pointedSigmaPAM x₀) = x₀ :=
  pointedSum_eq_point fun j => j.elim

/-- A σ-PAM is determined by its sums. -/
theorem sigmaPAM_ext {T : Type u} {p q : SigmaPAM T}
    (h : ∀ (J : Type) [Countable J] (x : J → T) (s : T),
      @SumsTo T p J _ x s ↔ @SumsTo T q J _ x s) : p = q := by
  obtain ⟨S1, s1, n1, a1, b1, c1, d1, e1⟩ := p
  obtain ⟨S2, s2, n2, a2, b2, c2, d2, e2⟩ := q
  have hS : ∀ (J : Type) [Countable J] (x : J → T), S1 x ↔ S2 x := fun J _ x =>
    ⟨fun hx => ((h J x _).1 ⟨hx, rfl⟩).1, fun hx => ((h J x _).2 ⟨hx, rfl⟩).1⟩
  have e : @S1 = @S2 := by
    funext J inst x
    exact propext (hS J x)
  subst e
  have e' : @s1 = @s2 := by
    funext J inst x hx
    obtain ⟨hx', e⟩ := (h J x (s1 x hx)).1 ⟨hx, rfl⟩
    exact e.symm
  subst e'
  rfl

/-- The binary sums of the pointed σ-PAM of `({0,1}, 0)` are those of the
Boolean effect algebra `{0,1}`. -/
theorem bool_sigmaPAMExtends : @SigmaPAMExtends Bool _ (pointedSigmaPAM false) := by
  intro a b s
  refine Iff.trans ?_ (pointed_sumsTo_iff false ![a, b] s).symm
  have : (∃ h : Perp a b, ovee a b h = s) ↔ (a && b) = false ∧ (a || b) = s :=
    ⟨fun ⟨h, e⟩ => ⟨h, e⟩, fun ⟨h, e⟩ => ⟨h, e⟩⟩
  rw [this]
  simp only [AtMostOne, Fin.forall_fin_two]
  cases a <;> cases b <;> cases s <;> simp

/-- Canonical countable sums in `{0,1}`: at most one term is `1`, and the sum
is `1` iff some term is. -/
theorem bool_isCSum_iff {J : Type} [Countable J] (r : J → Bool) (s : Bool) :
    IsCSum r s ↔ AtMostOne false r ∧ (∀ j, r j ≠ false → s = r j) ∧
      ((∀ j, r j = false) → s = false) :=
  ((@sigmaPAM_extends_omegaComplete Bool _ (pointedSigmaPAM false)
    bool_sigmaPAMExtends).2 J r s).symm.trans (pointed_sumsTo_iff false r s)

instance factBoolSigma : Fact (IsSigmaEffectMonoid Bool) := ⟨bool_isSigmaEffectMonoid⟩

section OfPointed

variable {X : Type} (x₀ : X)

theorem cond_ne_point {x : X} (hx : x ≠ x₀) (b : Bool) : cond b x x₀ ≠ x₀ ↔ b ≠ false := by
  cases b <;> simp [hx]

open Classical in
/-- **SIG 32** (`ex:weight-module-bool`, main.tex:947, Example): every pointed
set `(X, x₀)` is a σ-weight `{0,1}`-module: the pointed σ-PAM (a family is
summable iff at most one member differs from `x₀`), `1 · x = x`,
`0 · x = x₀`, and weight `|x| = 1` iff `x ≠ x₀`. -/
noncomputable def ofPointed : SWMod Bool :=
  letI := pointedSigmaPAM x₀
  { carrier := X
    pam := pointedSigmaPAM x₀
    act := ⟨fun b x => cond b x x₀⟩
    weight := fun x => decide (x ≠ x₀)
    one_smul := fun x => rfl
    mul_smul := fun r s x => by cases r <;> cases s <;> rfl
    smul_left := fun x J _ r s hrs => by
      show SumsTo (fun j => cond (r j) x x₀) (cond s x x₀)
      rw [pointed_sumsTo_iff]
      rcases eq_or_ne x x₀ with rfl | hx
      · simp [AtMostOne]
      obtain ⟨h1, h2, h3⟩ := (bool_isCSum_iff r s).1 hrs
      refine ⟨fun i j hi hj => h1 i j ((cond_ne_point x₀ hx _).1 hi)
        ((cond_ne_point x₀ hx _).1 hj), fun j hj => ?_, fun h => ?_⟩
      · rw [h2 j ((cond_ne_point x₀ hx _).1 hj)]
      · have : ∀ j, r j = false := fun j => by
          by_contra hn
          exact (cond_ne_point x₀ hx _).2 hn (h j)
        rw [h3 this]; rfl
    smul_right := fun r J _ x s h => by
      cases r
      · show SumsTo (fun _ => x₀) x₀
        exact (pointed_sumsTo_iff _ _ _).2
          ⟨fun _ _ h => (h rfl).elim, fun _ h => (h rfl).elim, fun _ => rfl⟩
      · exact h
    weight_sumsTo := fun x s h => by
      obtain ⟨h1, h2, h3⟩ := (pointed_sumsTo_iff x₀ x s).1 h
      refine (bool_isCSum_iff _ _).2 ⟨fun i j hi hj => h1 i j (by simpa using hi)
        (by simpa using hj), fun j hj => ?_, fun h => ?_⟩
      · have hj' : x j ≠ x₀ := by simpa using hj
        rw [h2 j hj']
      · have : ∀ j, x j = x₀ := fun j => by simpa using h j
        simp [h3 this]
    weight_smul := fun r x => by
      cases r
      · show decide (x₀ ≠ x₀) = (false && decide (x ≠ x₀)); simp
      · show decide (x ≠ x₀) = (true && decide (x ≠ x₀)); simp
    eq_zero_of_weight := fun x h => by
      rw [pointed_zero]
      by_contra hx
      have : decide (x ≠ x₀) = true := decide_eq_true hx
      exact absurd (this.symm.trans h) (by decide)
    summable_of_weight := fun x hx => by
      obtain ⟨s, hs⟩ := exists_isCSum bool_isSigmaEffectMonoid.1 hx
      have h1 := ((bool_isCSum_iff _ _).1 hs).1
      exact fun i j hi hj => h1 i j (by simpa using hi) (by simpa using hj) }

theorem ofPointed_sumsTo_iff {J : Type} [Countable J] (x : J → X) (s : X) :
    @SumsTo (ofPointed x₀).carrier (ofPointed x₀).pam J _ x s ↔
      @SumsTo X (pointedSigmaPAM x₀) J _ x s := Iff.rfl

theorem ofPointed_zero : (zero : (ofPointed x₀).carrier) = x₀ := pointed_zero x₀

end OfPointed

namespace SWMod

/-- A σ-weight module is determined by its carrier, σ-PAM, action and
weight. -/
theorem ext' {M : Type u} [EffectMonoid M] (X Y : SWMod M) (hc : X.carrier = Y.carrier)
    (hp : HEq X.pam Y.pam) (ha : HEq X.act Y.act) (hw : HEq X.weight Y.weight) : X = Y := by
  cases X; cases Y
  cases hc; cases hp; cases ha; cases hw
  rfl

variable (X : SWMod Bool)

theorem bool_weight_eq_false_iff (x : X.carrier) : X.weight x = false ↔ x = zero :=
  ⟨X.eq_zero_of_weight x, fun h => h ▸ X.weight_zero⟩

/-- **SIG 32** (main.tex:955): in a σ-weight `{0,1}`-module all nonzero
elements have weight `1` and so cannot be summed with nonzero elements: a
family sums to `s` iff at most one member is nonzero and `s` is that member
(or `0`) — the pointed σ-PAM of `(X, 0)`. -/
theorem bool_sumsTo_iff {J : Type} [Countable J] (x : J → X.carrier) (s : X.carrier) :
    SumsTo x s ↔ @SumsTo X.carrier (pointedSigmaPAM zero) J _ x s := by
  have hne : ∀ y : X.carrier, y ≠ zero → X.weight y ≠ false := fun y hy hw =>
    hy ((bool_weight_eq_false_iff X y).1 hw)
  have fwd : ∀ s, SumsTo x s → @SumsTo X.carrier (pointedSigmaPAM zero) J _ x s := by
    intro s h
    have hw := (bool_isCSum_iff _ _).1 (X.weight_sumsTo x s h)
    refine (pointed_sumsTo_iff _ _ _).2 ⟨fun i j hi hj => hw.1 i j (hne _ hi) (hne _ hj),
      fun j hj => ?_, fun h0 => ?_⟩
    · have hj' : ∀ l, l ≠ j → x l = zero := fun l hl => by
        by_contra hn
        exact hl (hw.1 l j (hne _ hn) (hne _ hj))
      exact h.unique (sumsTo_single x j hj')
    · exact h.unique ((sumsTo_congr fun j => (h0 j).symm).1 (sumsTo_zero_family J))
  refine ⟨fwd s, fun h => ?_⟩
  have hx : Summable x := by
    refine X.summable_of_weight x fun F => ?_
    have h1 := ((pointed_sumsTo_iff _ _ _).1 h).1
    obtain ⟨t, ht⟩ : ∃ t, IsCSum (fun j => X.weight (x j)) t := by
      classical
      refine ⟨decide (∃ j, X.weight (x j) ≠ false), (bool_isCSum_iff _ _).2
        ⟨fun i j hi hj => h1 i j
          (fun e => hi (show X.weight (x i) = false by rw [e]; exact X.weight_zero))
          (fun e => hj (show X.weight (x j) = false by rw [e]; exact X.weight_zero)),
          fun j hj => ?_, fun h0 => ?_⟩⟩
      · have : ∃ j, X.weight (x j) ≠ false := ⟨j, hj⟩
        simp only [this, decide_true]
        cases hwj : X.weight (x j)
        · exact (hj hwj).elim
        · rfl
      · simp [h0]
    exact ht.1 F
  have := fwd _ (sumsTo_sum hx)
  rw [(@SumsTo.unique X.carrier (pointedSigmaPAM zero) J _ _ _ _ h this)]
  exact sumsTo_sum hx

theorem bool_summable_iff {J : Type} [Countable J] (x : J → X.carrier) :
    Summable x ↔ AtMostOne zero x := by
  constructor
  · intro h; exact ((bool_sumsTo_iff X x _).1 (sumsTo_sum h)).1
  · intro h
    exact ((bool_sumsTo_iff X x _).2 ((pointed_sumsTo_iff _ _ _).2
      ⟨h, fun j hj => pointedSum_eq h hj, fun h0 => pointedSum_eq_point h0⟩)).1

/-- **SIG 32** (main.tex:947): in a σ-weight `{0,1}`-module the action is
trivial: `1 · x = x`, `0 · x = 0`. -/
theorem bool_smul (b : Bool) (x : X.carrier) : b • x = cond b x zero := by
  cases b
  · refine X.eq_zero_of_weight _ ?_
    rw [X.weight_smul]; rfl
  · exact X.one_smul x

open Classical in
/-- **SIG 32** (main.tex:955): the weight is `|x| = 1` iff `x ≠ 0`. -/
theorem bool_weight (x : X.carrier) : X.weight x = decide (x ≠ zero) := by
  by_cases hx : x = zero
  · rw [hx, X.weight_zero]; simp; rfl
  · rw [decide_eq_true hx]
    cases hw : X.weight x
    · exact (hx ((bool_weight_eq_false_iff X x).1 hw)).elim
    · rfl

open Classical in
/-- **SIG 32** (main.tex:958): a σ-weight `{0,1}`-module is the σ-weight
module of its pointed set `(X, 0)`: the structure is determined by the
carrier and `0`. -/
theorem ofPointed_eq : ofPointed (zero : X.carrier) = X := by
  have hpam : pointedSigmaPAM (zero : X.carrier) = X.pam :=
    sigmaPAM_ext fun J _ x s => (bool_sumsTo_iff X x s).symm
  have hact : (⟨fun b x => cond b x zero⟩ : SMul Bool X.carrier) = X.act := by
    have : X.act = ⟨fun b x => b • x⟩ := rfl
    rw [this]
    congr
    funext b x
    exact (bool_smul X b x).symm
  have hw : (fun x => decide (x ≠ zero)) = X.weight := funext fun x => (bool_weight X x).symm
  exact ext' _ _ rfl (heq_of_eq hpam) (heq_of_eq hact) (heq_of_eq hw)

end SWMod

/-- Pointed maps preserve pointed sums. -/
theorem pointed_map_sumsTo {X Y : Type u} {x₀ : X} {y₀ : Y} (g : X → Y) (hg : g x₀ = y₀)
    {J : Type} [Countable J] {x : J → X} {s : X} (h : @SumsTo X (pointedSigmaPAM x₀) J _ x s) :
    @SumsTo Y (pointedSigmaPAM y₀) J _ (fun j => g (x j)) (g s) := by
  obtain ⟨h1, h2, h3⟩ := (pointed_sumsTo_iff x₀ x s).1 h
  have hne : ∀ j, g (x j) ≠ y₀ → x j ≠ x₀ := fun j hj e => hj (by rw [e, hg])
  refine (pointed_sumsTo_iff y₀ _ _).2 ⟨fun i j hi hj => h1 i j (hne i hi) (hne j hj),
    fun j hj => by rw [h2 j (hne j hj)], fun h0 => ?_⟩
  by_cases hex : ∃ j, x j ≠ x₀
  · obtain ⟨j, hj⟩ := hex
    rw [h2 j hj, h0 j]
  · push Not at hex
    rw [h3 hex, hg]

/-- **SIG 32** (`ex:weight-module-bool`, main.tex:947): the functor
`sWMod[{0,1}] → pSet`, `X ↦ (X, 0)`, to Mathlib's category `Pointed` of
pointed types. -/
noncomputable def toPointed : SWMod Bool ⥤ Pointed.{0} where
  obj X := ⟨X.carrier, zero⟩
  map f := ⟨f.toFun, f.map_zero⟩

/-- A pointed map between σ-weight `{0,1}`-modules is a morphism of
`sWMod[{0,1}]`. -/
noncomputable def homOfPointed {X Y : SWMod Bool} (g : toPointed.obj X ⟶ toPointed.obj Y) :
    X ⟶ Y where
  toFun := g.toFun
  sigma x s h := (Y.bool_sumsTo_iff _ _).2
    (pointed_map_sumsTo g.toFun g.map_point ((X.bool_sumsTo_iff _ _).1 h))
  map_smul r x := by
    cases r
    · exact (congrArg g.toFun (X.bool_smul false x)).trans
        (g.map_point.trans (Y.bool_smul false (g.toFun x)).symm)
    · exact (congrArg g.toFun (X.bool_smul true x)).trans (Y.bool_smul true (g.toFun x)).symm
  weight_le x := by
    by_cases hx : x = zero
    · have hz : (g.toFun x : Y.carrier) = (zero : Y.carrier) := by subst hx; exact g.map_point
      have h1 : Y.weight (g.toFun x) = 0 := (congrArg Y.weight hz).trans Y.weight_zero
      have h2 : X.weight x = 0 := (congrArg X.weight hx).trans X.weight_zero
      exact (congrArg₂ (· ≼ ·) h1 h2).mpr (pcm_preorder_refl _)
    · have h2 : X.weight x = 1 := by
        classical
        exact (X.bool_weight x).trans (decide_eq_true hx)
      exact (congrArg (Y.weight (g.toFun x) ≼ ·) h2).mpr (ea_le_one _)

instance : toPointed.Faithful :=
  ⟨fun h => SWMod.hom_ext fun a => congrFun (congrArg Pointed.Hom.toFun h) a⟩

instance : toPointed.Full := ⟨fun g => ⟨homOfPointed g, rfl⟩⟩

theorem toPointed_ofPointed (P : Pointed.{0}) : toPointed.obj (ofPointed P.point) = P := by
  cases P with
  | mk X x => exact congrArg (Pointed.mk X) (ofPointed_zero x)

theorem ofPointed_toPointed (X : SWMod Bool) : ofPointed (toPointed.obj X).point = X :=
  X.ofPointed_eq

instance : toPointed.EssSurj :=
  ⟨fun P => ⟨ofPointed P.point, ⟨eqToIso (toPointed_ofPointed P)⟩⟩⟩

instance : toPointed.IsEquivalence where

/-- **SIG 32** (`ex:weight-module-bool`, main.tex:960, Example): σ-weight
`{0,1}`-modules are precisely pointed sets, `sWMod[{0,1}] ≅ pSet`: the
functor `X ↦ (X, 0)` is full, faithful and bijective on objects (an
isomorphism of categories).  With `SWMod.bool_sumsTo_iff`, `bool_smul`,
`bool_weight`: the σ-PAM, action and weight are the pointed ones. -/
theorem sWMod_bool_iso_pointed :
    toPointed.Full ∧ toPointed.Faithful ∧ Function.Bijective toPointed.obj :=
  ⟨inferInstance, inferInstance,
    ⟨fun X Y h => (ofPointed_toPointed X).symm.trans
      ((congrArg (fun P : Pointed.{0} => ofPointed P.point) h).trans (ofPointed_toPointed Y)),
    fun P => ⟨ofPointed P.point, toPointed_ofPointed P⟩⟩⟩

/-! ## SIG 47: `sWMod[{0,1}] ≃ Pfn` -/

/-- **SIG 47** (`prop:equiv-pfn-wmod`, main.tex:1313): the functor
`sWMod[{0,1}] → Pfn` sending `X` to `X ∖ {0}` and `f` to the partial
function `x ↦ f x`, defined iff `f x ≠ 0` — `pSet ≃ Pfn` is Mathlib's
`pointedToPartialFun`. -/
noncomputable def toPfn : SWMod Bool ⥤ PartialFun.{0} := toPointed ⋙ pointedToPartialFun

theorem toPfn_obj (X : SWMod Bool) : (toPfn.obj X : Type) = {x : X.carrier // x ≠ zero} := rfl

instance : pointedToPartialFun.IsEquivalence :=
  partialFunEquivPointed.isEquivalence_inverse

instance : toPfn.IsEquivalence := by unfold toPfn; infer_instance

/-- **SIG 47** (`prop:equiv-pfn-wmod`, main.tex:1313, Proposition): an
equivalence of categories `sWMod[{0,1}] ≃ Pfn`. -/
noncomputable def sWModBoolEquivPfn : SWMod Bool ≌ PartialFun.{0} := toPfn.asEquivalence

theorem unit_zero_bool : (zero : (SWMod.unit Bool factBoolSigma.out).carrier) = false :=
  SWMod.unit_zero

/-- The unit comparison `{*} ≅ {0,1} ∖ {0}`. -/
def unitEquivBool : PUnit.{1} ≃ {b : (SWMod.unit Bool factBoolSigma.out).carrier // b ≠ zero} where
  toFun _ := ⟨true, fun h => Bool.noConfusion (h.trans unit_zero_bool)⟩
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv b := by
    obtain ⟨b, hb⟩ := b
    rw [unit_zero_bool] at hb
    cases b
    · exact (hb rfl).elim
    · rfl

/-- **SIG 47** (`prop:equiv-pfn-wmod`, main.tex:1314, Proposition): the
equivalence `sWMod[{0,1}] ≃ Pfn` is a morphism of σ-effectuses: it preserves
countable coproducts (as an equivalence) and the unit, `{0,1} ∖ {0} ≅ {*}`,
compatibly with the truth maps. -/
noncomputable def toPfnMorphism : SigmaEffectusMorphism (SWMod Bool) PartialFun.{0} where
  F := toPfn
  preserves J _ := inferInstance
  u := PartialFun.Iso.mk unitEquivBool
  map_truth A := funext fun x => by
    obtain ⟨a, hx⟩ := x
    have hx' : (show A.carrier from a) ≠ zero := hx
    have hw : A.weight a = true := by
      classical
      exact (A.bool_weight _).trans (decide_eq_true hx')
    refine Part.ext' ⟨fun _ => Part.bind_dom.2 ⟨trivial, trivial⟩, fun _ => ?_⟩
      fun h1 h2 => Subtype.ext ?_
    · exact fun e => Bool.noConfusion ((hw.symm.trans e).trans unit_zero_bool)
    · exact hw

end BoolModules

/-! ## The σ-effectus `ωBAᵒᵖ` (the claim before SIG 49) -/

section BooleanSups

variable {B : Type u} [BooleanAlgebra B]

/-- In a Boolean algebra `a ∧ -` preserves existing suprema. -/
theorem isLUB_inf_left' {ι : Type v} {x : ι → B} {s : B} (h : IsLUB (Set.range x) s) (a : B) :
    IsLUB (Set.range fun i => a ⊓ x i) (a ⊓ s) := by
  refine ⟨?_, fun c hc => ?_⟩
  · rintro _ ⟨i, rfl⟩; exact inf_le_inf_left a (h.1 ⟨i, rfl⟩)
  · have hb : ∀ i, x i ≤ c ⊔ aᶜ := fun i => by
      have h1 : a ⊓ x i ≤ c := hc ⟨i, rfl⟩
      calc x i = (a ⊓ x i) ⊔ (aᶜ ⊓ x i) := by
              rw [← inf_sup_right, sup_compl_eq_top, top_inf_eq]
        _ ≤ c ⊔ aᶜ := sup_le_sup h1 inf_le_left
    have : s ≤ c ⊔ aᶜ := h.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
    calc a ⊓ s ≤ a ⊓ (c ⊔ aᶜ) := inf_le_inf_left a this
      _ = a ⊓ c := by rw [inf_sup_left, inf_compl_eq_bot, sup_bot_eq]
      _ ≤ c := inf_le_right

theorem disjoint_of_isLUB {ι : Type v} {x : ι → B} {s : B} (h : IsLUB (Set.range x) s) {a : B}
    (ha : ∀ i, Disjoint a (x i)) : Disjoint a s := by
  rw [disjoint_iff]
  exact le_bot_iff.1 ((isLUB_inf_left' h a).2 (by rintro _ ⟨i, rfl⟩; exact (ha i).eq_bot.le))

theorem isLUB_range_const {ι : Type v} [Nonempty ι] (b : B) : IsLUB (Set.range fun _ : ι => b) b := by
  rw [Set.range_const]; exact isLUB_singleton

theorem isGLB_range_const {ι : Type v} [Nonempty ι] (b : B) : IsGLB (Set.range fun _ : ι => b) b := by
  rw [Set.range_const]; exact isGLB_singleton

theorem range_pair (a b : B) : Set.range ![a, b] = {a, b} := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- `![a, b, b, …]`. -/
def seq2 (a b : B) : ℕ → B := fun n => if n = 0 then a else b

theorem range_seq2 (a b : B) : Set.range (seq2 a b) = {a, b} := by
  ext y
  simp only [Set.mem_range, seq2, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, rfl⟩
    by_cases hn : n = 0
    · left; simp [hn]
    · right; simp [hn]
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- Every sequence (hence every countable family) has a supremum. -/
def CountablyComplete (B : Type u) [BooleanAlgebra B] : Prop :=
  ∀ a : ℕ → B, ∃ s, IsLUB (Set.range a) s

theorem exists_isLUB_countable (hB : CountablyComplete B) {J : Type} [Countable J] (x : J → B) :
    ∃ s, IsLUB (Set.range x) s := by
  cases isEmpty_or_nonempty J
  · refine ⟨⊥, ?_⟩
    rw [Set.range_eq_empty]
    exact isLUB_empty
  · obtain ⟨e, he⟩ := exists_surjective_nat J
    obtain ⟨s, hs⟩ := hB (x ∘ e)
    exact ⟨s, by rwa [he.range_comp] at hs⟩

/-- The **σ-PAM of disjoint joins** of an ω-complete Boolean algebra: a
countable family is summable iff it is pairwise disjoint, and its sum is its
join. -/
noncomputable def disjointSigmaPAM (hB : CountablyComplete B) : SigmaPAM B where
  Summable x := ∀ i j, i ≠ j → Disjoint (x i) (x j)
  sum x _ := (exists_isLUB_countable hB x).choose
  nonempty := ⟨⊥⟩
  summable_iff_partition {J K} _ _ x p := by
    have hs := fun k => (exists_isLUB_countable hB (fun j : {j // p j = k} => x j.1)).choose_spec
    constructor
    · intro hx
      refine ⟨fun k i j hij => hx i.1 j.1 (fun e => hij (Subtype.ext e)), fun k k' hkk => ?_⟩
      refine disjoint_of_isLUB (hs k') fun j => (disjoint_of_isLUB (hs k) fun i => ?_).symm
      exact hx j.1 i.1 (fun e => hkk (by rw [← i.2, ← j.2, e]))
    · rintro ⟨hb, hsum⟩ i j hij
      by_cases hp : p i = p j
      · exact hb (p j) ⟨i, hp⟩ ⟨j, rfl⟩ (fun e => hij (congrArg Subtype.val e))
      · exact (hsum (p i) (p j) hp).mono ((hs (p i)).1 ⟨⟨i, rfl⟩, rfl⟩)
          ((hs (p j)).1 ⟨⟨j, rfl⟩, rfl⟩)
  sum_partition {J K} _ _ x p hx h h' := by
    have hs := fun k => (exists_isLUB_countable hB (fun j : {j // p j = k} => x j.1)).choose_spec
    refine ((exists_isLUB_countable hB x).choose_spec).unique ?_
    refine (isLUB_congr ?_).2 (exists_isLUB_countable hB _).choose_spec
    ext c
    constructor
    · intro hc
      rintro _ ⟨k, rfl⟩
      exact (hs k).2 (by rintro _ ⟨j, rfl⟩; exact hc ⟨j.1, rfl⟩)
    · intro hc
      rintro _ ⟨j, rfl⟩
      exact le_trans ((hs (p j)).1 ⟨⟨j, rfl⟩, rfl⟩) (hc ⟨p j, rfl⟩)
  summable_unique x i j h := (h (Subsingleton.elim i j)).elim
  sum_unique {J} _ x _ := by
    refine ((exists_isLUB_countable hB x).choose_spec).unique ?_
    rw [Set.range_unique]; exact isLUB_singleton
  limit {J} _ x h i j hij := by
    classical
    exact h {i, j} ⟨i, by simp⟩ ⟨j, by simp⟩ (fun e => hij (congrArg Subtype.val e))

theorem disjoint_sumsTo_iff (hB : CountablyComplete B) {J : Type} [Countable J] (x : J → B)
    (s : B) : @SumsTo B (disjointSigmaPAM hB) J _ x s ↔
      (∀ i j, i ≠ j → Disjoint (x i) (x j)) ∧ IsLUB (Set.range x) s := by
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨hx, (exists_isLUB_countable hB x).choose_spec⟩
  · rintro ⟨hx, hs⟩
    exact ⟨hx, (exists_isLUB_countable hB x).choose_spec.unique hs⟩

end BooleanSups

/-- An **ω-complete Boolean algebra** (every countable family has a join). -/
structure OmegaBA : Type (u + 1) where
  carrier : Type u
  [ba : BooleanAlgebra carrier]
  complete : CountablyComplete carrier

attribute [instance] OmegaBA.ba

namespace OmegaBA

instance : CoeSort OmegaBA.{u} (Type u) := ⟨OmegaBA.carrier⟩

/-- The σ-PAM of disjoint joins on an ω-complete Boolean algebra. -/
noncomputable instance sigmaPAM (A : OmegaBA.{u}) : SigmaPAM A.carrier :=
  disjointSigmaPAM A.complete

theorem sumsTo_iff {A : OmegaBA.{u}} {J : Type} [Countable J] (x : J → A.carrier) (s : A.carrier) :
    SumsTo x s ↔ (∀ i j, i ≠ j → Disjoint (x i) (x j)) ∧ IsLUB (Set.range x) s :=
  disjoint_sumsTo_iff A.complete x s

/-- A morphism of `ωBA`: a function preserving countable joins (`⊥` and joins
of sequences) and nonempty countable meets (meets of sequences). -/
@[ext]
structure Hom (A B : OmegaBA.{u}) : Type u where
  toFun : A.carrier → B.carrier
  map_bot : toFun ⊥ = ⊥
  map_sup : ∀ (a : ℕ → A.carrier) (s : A.carrier), IsLUB (Set.range a) s →
    IsLUB (Set.range fun n => toFun (a n)) (toFun s)
  map_inf : ∀ (a : ℕ → A.carrier) (s : A.carrier), IsGLB (Set.range a) s →
    IsGLB (Set.range fun n => toFun (a n)) (toFun s)

/-- The category `ωBA` of ω-complete Boolean algebras. -/
instance : Category OmegaBA.{u} where
  Hom := Hom
  id A := ⟨id, rfl, fun _ _ h => h, fun _ _ h => h⟩
  comp f g := ⟨g.toFun ∘ f.toFun, by simp [f.map_bot, g.map_bot],
    fun a s h => g.map_sup _ _ (f.map_sup a s h), fun a s h => g.map_inf _ _ (f.map_inf a s h)⟩

theorem hom_ext {A B : OmegaBA.{u}} {f g : A ⟶ B} (h : ∀ a, f.toFun a = g.toFun a) : f = g :=
  Hom.ext (funext h)

@[simp] theorem comp_toFun {A B C : OmegaBA.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A.carrier) :
    (f ≫ g).toFun a = g.toFun (f.toFun a) := rfl

@[simp] theorem id_toFun {A : OmegaBA.{u}} (a : A.carrier) : (𝟙 A : A ⟶ A).toFun a = a := rfl

variable {A B : OmegaBA.{u}}

theorem Hom.map_sup₂ (f : A ⟶ B) (a b : A.carrier) : f.toFun (a ⊔ b) = f.toFun a ⊔ f.toFun b := by
  have h := f.map_sup (seq2 a b) (a ⊔ b) (by rw [range_seq2]; exact isLUB_pair)
  have e : (Set.range fun n => f.toFun (seq2 a b n)) = {f.toFun a, f.toFun b} := by
    rw [← range_seq2]; ext y; simp only [Set.mem_range, seq2]
    constructor <;> rintro ⟨n, rfl⟩ <;> exact ⟨n, by split_ifs <;> rfl⟩
  rw [e] at h
  exact h.unique isLUB_pair

theorem Hom.map_inf₂ (f : A ⟶ B) (a b : A.carrier) : f.toFun (a ⊓ b) = f.toFun a ⊓ f.toFun b := by
  have h := f.map_inf (seq2 a b) (a ⊓ b) (by rw [range_seq2]; exact isGLB_pair)
  have e : (Set.range fun n => f.toFun (seq2 a b n)) = {f.toFun a, f.toFun b} := by
    rw [← range_seq2]; ext y; simp only [Set.mem_range, seq2]
    constructor <;> rintro ⟨n, rfl⟩ <;> exact ⟨n, by split_ifs <;> rfl⟩
  rw [e] at h
  exact h.unique isGLB_pair

theorem Hom.mono (f : A ⟶ B) {a b : A.carrier} (h : a ≤ b) : f.toFun a ≤ f.toFun b := by
  have := f.map_sup₂ a b
  rw [sup_eq_right.2 h] at this
  rw [this]; exact le_sup_left

theorem Hom.disjoint (f : A ⟶ B) {a b : A.carrier} (h : Disjoint a b) :
    Disjoint (f.toFun a) (f.toFun b) := by
  rw [disjoint_iff, ← f.map_inf₂, h.eq_bot, f.map_bot]

theorem Hom.map_isLUB (f : A ⟶ B) {J : Type} [Countable J] {x : J → A.carrier} {s : A.carrier}
    (h : IsLUB (Set.range x) s) : IsLUB (Set.range fun j => f.toFun (x j)) (f.toFun s) := by
  cases isEmpty_or_nonempty J
  · rw [Set.range_eq_empty] at h ⊢
    rw [show s = ⊥ from le_bot_iff.1 (h.2 (by simp)), f.map_bot]
    exact isLUB_empty
  · obtain ⟨e, he⟩ := exists_surjective_nat J
    have := f.map_sup (x ∘ e) s (by rwa [he.range_comp])
    rwa [show (Set.range fun n => f.toFun ((x ∘ e) n)) = Set.range fun j => f.toFun (x j) from
      he.range_comp (fun j => f.toFun (x j))] at this

/-- Morphisms of `ωBA` are σ-additive for the disjoint-join σ-PAM. -/
theorem Hom.sumsTo (f : A ⟶ B) {J : Type} [Countable J] {x : J → A.carrier} {s : A.carrier}
    (h : SumsTo x s) : SumsTo (fun j => f.toFun (x j)) (f.toFun s) := by
  rw [sumsTo_iff] at h ⊢
  exact ⟨fun i j hij => f.disjoint (h.1 i j hij), f.map_isLUB h.2⟩

/-! ### Products in `ωBA` -/

theorem eval_image_range {J : Type} {D : J → Type u} (a : ℕ → ∀ j, D j) (j : J) :
    Function.eval j '' Set.range a = Set.range fun n => a n j :=
  (Set.range_comp _ _).symm

theorem isLUB_pi_range {J : Type} {D : J → Type u} [∀ j, Preorder (D j)] (a : ℕ → ∀ j, D j)
    (s : ∀ j, D j) : IsLUB (Set.range a) s ↔ ∀ j, IsLUB (Set.range fun n => a n j) (s j) := by
  rw [isLUB_pi]; simp only [eval_image_range]

theorem isGLB_pi_range {J : Type} {D : J → Type u} [∀ j, Preorder (D j)] (a : ℕ → ∀ j, D j)
    (s : ∀ j, D j) : IsGLB (Set.range a) s ↔ ∀ j, IsGLB (Set.range fun n => a n j) (s j) := by
  rw [isGLB_pi]; simp only [eval_image_range]

/-- The product `∏ D_j` in `ωBA` (pointwise operations). -/
def pi {J : Type} (D : J → OmegaBA.{u}) : OmegaBA.{u} where
  carrier := ∀ j, (D j).carrier
  complete a := by
    choose s hs using fun j => (D j).complete (fun n => a n j)
    exact ⟨s, (isLUB_pi_range (D := fun j => (D j).carrier) a s).2 hs⟩

def piProj {J : Type} (D : J → OmegaBA.{u}) (j : J) : pi D ⟶ D j where
  toFun x := x j
  map_bot := rfl
  map_sup a s h := (isLUB_pi_range (D := fun j => (D j).carrier) a s).1 h j
  map_inf a s h := (isGLB_pi_range (D := fun j => (D j).carrier) a s).1 h j

def piLift {J : Type} {D : J → OmegaBA.{u}} {X : OmegaBA.{u}} (f : ∀ j, X ⟶ D j) : X ⟶ pi D where
  toFun x j := (f j).toFun x
  map_bot := funext fun j => (f j).map_bot
  map_sup a s h := (isLUB_pi_range (D := fun j => (D j).carrier) _ _).2 fun j =>
    (f j).map_sup a s h
  map_inf a s h := (isGLB_pi_range (D := fun j => (D j).carrier) _ _).2 fun j =>
    (f j).map_inf a s h

def piFan {J : Type} (D : J → OmegaBA.{u}) : Fan D := Fan.mk (pi D) (piProj D)

def piFanIsLimit {J : Type} (D : J → OmegaBA.{u}) : IsLimit (piFan D) :=
  Fan.IsLimit.mk _ (fun s => piLift s.proj) (fun s j => hom_ext fun x => rfl)
    (fun s m hm => hom_ext fun x => funext fun j => by
      have h := congrArg (fun g => Hom.toFun g x) (hm j)
      exact h)

instance hasProductsOfShape (J : Type) : HasProductsOfShape J OmegaBA.{u} :=
  ⟨fun F => by
    have : HasLimit (Discrete.functor (F.obj ∘ Discrete.mk)) := HasLimit.mk ⟨_, piFanIsLimit _⟩
    exact hasLimit_of_iso Discrete.natIsoFunctor.symm⟩

instance : HasCountableCoproducts OmegaBA.{u}ᵒᵖ :=
  ⟨fun _ _ => inferInstance⟩

/-! ### Hom-sums in `ωBAᵒᵖ` -/

/-- The constant-`⊥` morphism. -/
def zeroHom (A B : OmegaBA.{u}) : A ⟶ B where
  toFun _ := ⊥
  map_bot := rfl
  map_sup a s h := isLUB_range_const _
  map_inf a s h := isGLB_range_const _

/-- The core computation: morphisms `f_j : D → E` with pairwise disjoint
`f_j(⊤)` have a pointwise join, again a morphism. -/
theorem exists_pointwise_sum {D E : OmegaBA.{u}} {J : Type} [Countable J] (f : J → (D ⟶ E))
    (h : ∀ i j, i ≠ j → Disjoint ((f i).toFun ⊤) ((f j).toFun ⊤)) :
    ∃ g : D ⟶ E, ∀ a, SumsTo (fun j => (f j).toFun a) (g.toFun a) := by
  have hd : ∀ a, ∀ i j, i ≠ j → Disjoint ((f i).toFun a) ((f j).toFun a) := fun a i j hij =>
    (h i j hij).mono ((f i).mono le_top) ((f j).mono le_top)
  choose G hG using fun a => exists_isLUB_countable E.complete (fun j => (f j).toFun a)
  have hmono : ∀ {a b}, a ≤ b → G a ≤ G b := fun {a b} hab =>
    (hG a).2 (by rintro _ ⟨j, rfl⟩; exact le_trans ((f j).mono hab) ((hG b).1 ⟨j, rfl⟩))
  refine ⟨⟨G, ?_, fun a s hs => ⟨?_, fun c hc => ?_⟩, fun a s hs => ⟨?_, fun c hc => ?_⟩⟩,
    fun a => (sumsTo_iff _ _).2 ⟨hd a, hG a⟩⟩
  · refine (hG ⊥).unique ⟨?_, fun c _ => bot_le⟩
    rintro _ ⟨j, rfl⟩; exact le_of_eq (f j).map_bot
  · rintro _ ⟨n, rfl⟩; exact hmono (hs.1 ⟨n, rfl⟩)
  · refine (hG s).2 ?_
    rintro _ ⟨j, rfl⟩
    exact ((f j).map_sup a s hs).2 (by
      rintro _ ⟨n, rfl⟩
      exact le_trans ((hG (a n)).1 ⟨j, rfl⟩) (hc ⟨n, rfl⟩))
  · rintro _ ⟨n, rfl⟩; exact hmono (hs.1 ⟨n, rfl⟩)
  · -- `c ≤ G(a n)` for all `n`: split `c` along the disjoint `f_j(⊤)`
    have hc0 : c ≤ G ⊤ := le_trans (hc ⟨0, rfl⟩) (hmono le_top)
    have hL := isLUB_inf_left' (hG ⊤) c
    rw [inf_eq_left.2 hc0] at hL
    refine hL.2 ?_
    rintro _ ⟨j, rfl⟩
    refine le_trans ?_ ((hG s).1 ⟨j, rfl⟩)
    refine ((f j).map_inf a s hs).2 ?_
    rintro _ ⟨n, rfl⟩
    have h1 : G (a n) ≤ (f j).toFun (a n) ⊔ ((f j).toFun ⊤)ᶜ := (hG (a n)).2 (by
      rintro _ ⟨k, rfl⟩
      by_cases hk : k = j
      · subst hk; exact le_sup_left
      · exact le_trans (le_trans ((f k).mono le_top) (h k j hk).le_compl_right) le_sup_right)
    calc c ⊓ (f j).toFun ⊤ ≤ ((f j).toFun (a n) ⊔ ((f j).toFun ⊤)ᶜ) ⊓ (f j).toFun ⊤ :=
          inf_le_inf_right _ (le_trans (hc ⟨n, rfl⟩) h1)
      _ = (f j).toFun (a n) ⊓ (f j).toFun ⊤ := by
          rw [inf_sup_right, compl_inf_eq_bot, sup_bot_eq]
      _ ≤ (f j).toFun (a n) := inf_le_left

open Opposite

/-- The data of the pointwise σ-PAM on `ωBAᵒᵖ(X, Y) = ωBA(Y, X)`. -/
theorem homData (X Y : OmegaBA.{u}ᵒᵖ) :
    PointwiseData (fun (f : X ⟶ Y) (a : Y.unop.carrier) => f.unop.toFun a) where
  inj f g h := Quiver.Hom.unop_inj (hom_ext fun a => congrFun h a)
  nonempty := ⟨(zeroHom Y.unop X.unop).op⟩
  sub f P := by
    rintro ⟨g, hg⟩
    have h1 := ((sumsTo_iff _ _).1 (hg ⊤)).1
    obtain ⟨g', hg'⟩ := exists_pointwise_sum (fun j : {j // P j} => (f j.1).unop)
      (fun i j hij => h1 i.1 j.1 (fun e => hij (Subtype.ext e)))
    exact ⟨g'.op, hg'⟩
  lim f h := by
    obtain ⟨g', hg'⟩ := exists_pointwise_sum (fun j => (f j).unop) (fun i j hij => by
      classical
      obtain ⟨g, hg⟩ := h {i, j}
      exact ((sumsTo_iff _ _).1 (hg ⊤)).1 ⟨i, by simp⟩ ⟨j, by simp⟩
        (fun e => hij (congrArg Subtype.val e)))
    exact ⟨g'.op, hg'⟩

/-- The σ-PAM on `ωBAᵒᵖ(X, Y)`: pointwise disjoint joins. -/
noncomputable instance homSigmaPAM (X Y : OmegaBA.{u}ᵒᵖ) : SigmaPAM (X ⟶ Y) :=
  pointwiseSigmaPAM (homData X Y)

theorem hom_sumsTo_iff {X Y : OmegaBA.{u}ᵒᵖ} {J : Type} [Countable J] (f : J → (X ⟶ Y))
    (g : X ⟶ Y) : SumsTo f g ↔ ∀ a, SumsTo (fun j => (f j).unop.toFun a) (g.unop.toFun a) :=
  pointwise_sumsTo_iff (homData X Y) f g

/-- A family in `ωBAᵒᵖ(X, Y)` is summable iff the `f_j(⊤)` are pairwise
disjoint. -/
theorem hom_summable_iff {X Y : OmegaBA.{u}ᵒᵖ} {J : Type} [Countable J] (f : J → (X ⟶ Y)) :
    Summable f ↔ ∀ i j, i ≠ j → Disjoint ((f i).unop.toFun ⊤) ((f j).unop.toFun ⊤) := by
  constructor
  · rintro ⟨g, hg⟩; exact ((sumsTo_iff _ _).1 (hg ⊤)).1
  · intro h
    obtain ⟨g, hg⟩ := exists_pointwise_sum (fun j => (f j).unop) h
    exact ⟨g.op, hg⟩

theorem hom_zero_eq (X Y : OmegaBA.{u}ᵒᵖ) : (0 : X ⟶ Y) = (zeroHom Y.unop X.unop).op := by
  apply Quiver.Hom.unop_inj
  refine hom_ext fun a => ?_
  have h := (hom_sumsTo_iff (Empty.elim : Empty → (X ⟶ Y)) _).1 (sumsTo_of_isEmpty _) a
  have h2 := ((sumsTo_iff _ _).1 h).2
  rw [Set.range_eq_empty] at h2
  exact le_bot_iff.1 (h2.2 (by simp))

theorem perp_iff {X Y : OmegaBA.{u}ᵒᵖ} (p q : X ⟶ Y) :
    Perp p q ↔ Disjoint (p.unop.toFun ⊤) (q.unop.toFun ⊤) := by
  show Summable ![p, q] ↔ _
  rw [hom_summable_iff]
  constructor
  · intro h; exact h 0 1 (by decide)
  · intro h i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact h
    · exact h.symm
    · exact (hij rfl).elim

theorem ovee_apply {X Y : OmegaBA.{u}ᵒᵖ} {p q : X ⟶ Y} (h : Perp p q) (a : Y.unop.carrier) :
    (ovee p q h).unop.toFun a = p.unop.toFun a ⊔ q.unop.toFun a := by
  have := (hom_sumsTo_iff _ _).1 (sumsTo_sum (show Summable ![p, q] from h)) a
  have h2 := ((sumsTo_iff _ _).1 this).2
  have e : (Set.range fun j => (![p, q] j).unop.toFun a) = {p.unop.toFun a, q.unop.toFun a} := by
    rw [← range_pair]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [e] at h2
  exact h2.unique isLUB_pair

theorem unop_comp_apply {X Y Z : OmegaBA.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (z : Z.unop.carrier) :
    (f ≫ g).unop.toFun z = f.unop.toFun (g.unop.toFun z) := rfl

/-! ### `ωBAᵒᵖ` is a σ-effectus -/

/-- The chosen coproduct `∐_J B` of `ωBAᵒᵖ` is the product `∏_J B`. -/
noncomputable def coprodIso (B : OmegaBA.{u}ᵒᵖ) (J : Type) :
    ∐ (fun _ : J => B) ≅ op (pi (fun _ : J => B.unop)) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (Fan.IsLimit.op (piFanIsLimit (fun _ : J => B.unop)))

open Classical in
/-- The inclusion `E → ∏_J E` at `j` (zero elsewhere). -/
noncomputable def inj (E : OmegaBA.{u}) {J : Type} (j : J) : E ⟶ pi (fun _ : J => E) where
  toFun a k := if k = j then a else ⊥
  map_bot := funext fun k => by split_ifs <;> rfl
  map_sup a s h := (isLUB_pi_range (D := fun _ : J => E.carrier) _ _).2 fun k => by
    by_cases hk : k = j
    · simp only [hk, if_true]; exact h
    · simp only [hk, if_false]; exact isLUB_range_const _
  map_inf a s h := (isGLB_pi_range (D := fun _ : J => E.carrier) _ _).2 fun k => by
    by_cases hk : k = j
    · simp only [hk, if_true]; exact h
    · simp only [hk, if_false]; exact isGLB_range_const _

theorem inj_comp_piProj_self (E : OmegaBA.{u}) {J : Type} (j : J) :
    inj E j ≫ piProj (fun _ : J => E) j = 𝟙 E := by
  classical
  refine hom_ext fun a => ?_
  show (if j = j then a else ⊥) = a
  simp

theorem inj_comp_piProj_ne (E : OmegaBA.{u}) {J : Type} {j k : J} (h : k ≠ j) :
    inj E j ≫ piProj (fun _ : J => E) k = zeroHom E E := by
  classical
  refine hom_ext fun a => ?_
  show (if k = j then a else ⊥) = ⊥
  simp [h]

theorem pproj_eq (B : OmegaBA.{u}ᵒᵖ) {J : Type} (j : J) :
    pproj (fun _ : J => B) j = (coprodIso B J).hom ≫ (inj B.unop j).op := by
  refine Sigma.hom_ext _ _ fun k => ?_
  have hι : Sigma.ι (fun _ : J => B) k ≫ (coprodIso B J).hom =
      (piProj (fun _ : J => B.unop) k).op :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk k)
  rw [← Category.assoc, hι, ← op_comp]
  by_cases hk : k = j
  · subst hk
    rw [ι_pproj_self]
    exact (congrArg Quiver.Hom.op (inj_comp_piProj_self B.unop k)).symm
  · rw [ι_pproj_ne _ hk, hom_zero_eq]
    exact congrArg Quiver.Hom.op (inj_comp_piProj_ne B.unop hk).symm

/-- The partial projections of `ωBAᵒᵖ`'s coproducts are compatible, so
compatible families are summable; untying holds since the coprojections'
underlying maps are monotone. -/
instance sigmaPAC : SigmaPAC OmegaBA.{u}ᵒᵖ where
  comp_sigmaBiadditive X Y Z := by
    refine ⟨fun g => isSigmaAdditive_of_sumsTo fun x s hs => ?_,
      fun f => isSigmaAdditive_of_sumsTo fun x s hs => ?_⟩
    · rw [hom_sumsTo_iff] at hs ⊢
      exact fun z => hs (g.unop.toFun z)
    · rw [hom_sumsTo_iff] at hs ⊢
      exact fun z => f.unop.sumsTo (hs z)
  compatible_sum {J} _ {A B} f := by
    classical
    rintro ⟨h, hh⟩
    rw [hom_summable_iff]
    intro i j hij
    let H := (h ≫ (coprodIso B J).hom).unop
    have hval : ∀ j, (f j).unop.toFun ⊤ = H.toFun ((inj B.unop j).toFun ⊤) := by
      intro j
      rw [← hh j, pproj_eq, ← Category.assoc]
      rfl
    rw [hval i, hval j]
    refine H.disjoint ?_
    rw [disjoint_iff]
    funext k
    show (if k = i then ⊤ else ⊥) ⊓ (if k = j then ⊤ else ⊥) = ⊥
    by_cases hk : k = i
    · subst hk; simp [hij]
    · simp [hk]
  untying {A B f g} h := by
    replace h := (perp_iff f g).1 h
    rw [hom_summable_iff]
    intro i j hij
    have e : ∀ (k : A ⟶ B) (c : B ⟶ B ⨿ B), (k ≫ c).unop.toFun ⊤ ≤ k.unop.toFun ⊤ :=
      fun k c => k.unop.mono le_top
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact h.mono (e f _) (e g _)
    · exact h.symm.mono (e g _) (e f _)
    · exact (hij rfl).elim

/-- The unit object `{0,1}` of `ωBAᵒᵖ`. -/
abbrev two : OmegaBA.{0} where
  carrier := Bool
  complete a := ⟨⨆ n, a n, isLUB_iSup⟩

theorem bool_isLUB_true {a : ℕ → Bool} (h : IsLUB (Set.range a) true) : ∃ n, a n = true := by
  by_contra hn
  push Not at hn
  have : true ≤ false := h.2 (by
    rintro _ ⟨n, rfl⟩
    cases hb : a n
    · exact le_rfl
    · exact (hn n hb).elim)
  exact absurd this (by decide)

theorem bool_isLUB_false {a : ℕ → Bool} (h : IsLUB (Set.range a) false) (n : ℕ) : a n = false :=
  le_bot_iff.1 (h.1 ⟨n, rfl⟩)

theorem bool_isGLB_true {a : ℕ → Bool} (h : IsGLB (Set.range a) true) (n : ℕ) : a n = true :=
  top_le_iff.1 (h.1 ⟨n, rfl⟩)

theorem bool_isGLB_false {a : ℕ → Bool} (h : IsGLB (Set.range a) false) : ∃ n, a n = false := by
  by_contra hn
  push Not at hn
  have : true ≤ false := h.2 (by
    rintro _ ⟨n, rfl⟩
    cases hb : a n
    · exact (hn n hb).elim
    · exact le_rfl)
  exact absurd this (by decide)

/-- The morphism `{0,1} → E` sending `1` to `e`. -/
def boolMap (E : OmegaBA.{0}) (e : E.carrier) : two ⟶ E where
  toFun b := cond b e ⊥
  map_bot := rfl
  map_sup a s h := by
    cases s
    · have : ∀ n, a n = false := bool_isLUB_false h
      simp only [this, Bool.cond_false]
      exact isLUB_range_const _
    · obtain ⟨n, hn⟩ := bool_isLUB_true h
      refine ⟨?_, fun c hc => ?_⟩
      · rintro _ ⟨m, rfl⟩
        show cond (a m) e ⊥ ≤ e
        cases a m
        · exact bot_le
        · exact le_rfl
      · have := hc ⟨n, rfl⟩
        simp only [hn, Bool.cond_true] at this
        exact this
  map_inf a s h := by
    cases s
    · obtain ⟨n, hn⟩ := bool_isGLB_false h
      refine ⟨?_, fun c hc => ?_⟩
      · rintro _ ⟨m, rfl⟩; exact bot_le
      · have := hc ⟨n, rfl⟩
        simp only [hn, Bool.cond_false] at this
        exact this
    · have : ∀ n, a n = true := bool_isGLB_true h
      simp only [this, Bool.cond_true]
      exact isGLB_range_const _

theorem eq_boolMap {E : OmegaBA.{0}} (p : two ⟶ E) : p = boolMap E (p.toFun ⊤) := by
  refine hom_ext fun b => ?_
  cases b
  · exact p.map_bot
  · rfl

theorem two_hom_ext {E : OmegaBA.{0}} {p q : two ⟶ E} (h : p.toFun ⊤ = q.toFun ⊤) :
    p = q := by
  rw [eq_boolMap p, eq_boolMap q, h]

theorem eq_zero_of_top {X Y : OmegaBA.{u}ᵒᵖ} {f : X ⟶ Y} (h : f.unop.toFun ⊤ = ⊥) : f = 0 := by
  rw [hom_zero_eq]
  apply Quiver.Hom.unop_inj
  refine hom_ext fun a => ?_
  exact le_bot_iff.1 (h ▸ f.unop.mono le_top)

/-- **SIG 49** (`prop:powerset-functor`, main.tex:1377, the claim before
it): `ωBAᵒᵖ` is a σ-effectus, with unit `{0,1}`: coproducts are products of
Boolean algebras, a family of maps is summable iff the images of `⊤` are
pairwise disjoint (then the sum is the pointwise join), predicates
`{0,1} → A` are the elements of `A`, truth is `⊤`, orthosupplement the
complement. -/
noncomputable instance sigmaEffectus : SigmaEffectus OmegaBA.{0}ᵒᵖ where
  I := op two
  one X := (boolMap X.unop ⊤).op
  orth {X} p := (boolMap X.unop (p.unop.toFun ⊤)ᶜ).op
  perp_orth p := (perp_iff _ _).2 disjoint_compl_right
  ovee_orth {X} p := by
    apply Quiver.Hom.unop_inj
    exact two_hom_ext ((ovee_apply _ ⊤).trans sup_compl_eq_top)
  orth_unique {X p q} h e := by
    have h1 : Disjoint (p.unop.toFun ⊤) (q.unop.toFun ⊤) := (perp_iff p q).1 h
    have h2 : p.unop.toFun ⊤ ⊔ q.unop.toFun ⊤ = ⊤ := by
      have := congrArg (fun g : X ⟶ op two => g.unop.toFun ⊤) e
      exact (ovee_apply h ⊤).symm.trans this
    apply Quiver.Hom.unop_inj
    refine two_hom_ext ?_
    exact (IsCompl.compl_eq ⟨h1, codisjoint_iff.2 h2⟩).symm
  eq_zero_of_perp_one {X p} h :=
    eq_zero_of_top (disjoint_top.1 ((perp_iff p _).1 h))
  eq_zero_of_one_zero {X Y f} h := by
    apply eq_zero_of_top
    have := congrArg (fun g : X ⟶ op two => g.unop.toFun ⊤) h
    simp only at this
    rw [hom_zero_eq] at this
    exact this
  perp_of_one_perp {X Y f g} h := by
    rw [perp_iff] at h ⊢
    exact h

end OmegaBA

/-! ## SIG 49: the powerset functor `Pfn → ωBAᵒᵖ` -/

section Powerset

open Opposite OmegaBA

theorem set_isLUB_iff {X : Type u} (A : ℕ → Set X) (S : Set X) :
    IsLUB (Set.range A) S ↔ S = ⋃ n, A n :=
  ⟨fun h => (h.unique isLUB_iSup).trans (Set.iSup_eq_iUnion A),
    fun h => h ▸ (Set.iSup_eq_iUnion A) ▸ isLUB_iSup⟩

theorem set_isGLB_iff {X : Type u} (A : ℕ → Set X) (S : Set X) :
    IsGLB (Set.range A) S ↔ S = ⋂ n, A n :=
  ⟨fun h => (h.unique isGLB_iInf).trans (Set.iInf_eq_iInter A),
    fun h => h ▸ (Set.iInf_eq_iInter A) ▸ isGLB_iInf⟩

theorem bool_isLUB_iff (b : ℕ → Bool) (t : Bool) :
    IsLUB (Set.range b) t ↔ (t = true ↔ ∃ n, b n = true) := by
  constructor
  · intro h
    cases t
    · exact ⟨fun e => (Bool.noConfusion e), fun ⟨n, hn⟩ =>
        absurd (bool_isLUB_false h n) (by rw [hn]; decide)⟩
    · exact ⟨fun _ => bool_isLUB_true h, fun _ => rfl⟩
  · intro h
    refine ⟨?_, fun c hc => ?_⟩
    · rintro _ ⟨n, rfl⟩
      cases hb : b n
      · exact Bool.false_le _
      · rw [(h.2 ⟨n, hb⟩)]
    · cases ht : t
      · exact Bool.false_le _
      · obtain ⟨n, hn⟩ := h.1 ht
        have := hc ⟨n, rfl⟩
        rw [hn] at this
        exact this

theorem bool_isGLB_iff (b : ℕ → Bool) (t : Bool) :
    IsGLB (Set.range b) t ↔ (t = true ↔ ∀ n, b n = true) := by
  constructor
  · intro h
    cases t
    · refine ⟨fun e => Bool.noConfusion e, fun hall => ?_⟩
      obtain ⟨n, hn⟩ := bool_isGLB_false h
      exact absurd hn (by rw [hall n]; decide)
    · exact ⟨fun _ => bool_isGLB_true h, fun _ => rfl⟩
  · intro h
    refine ⟨?_, fun c hc => ?_⟩
    · rintro _ ⟨n, rfl⟩
      cases ht : t
      · exact Bool.false_le _
      · rw [(h.1 ht) n]
    · cases hc' : c
      · exact Bool.false_le _
      · have : ∀ n, b n = true := fun n => by
          have := hc ⟨n, rfl⟩
          rw [hc'] at this
          exact top_le_iff.1 this
        rw [h.2 this]

/-- The ω-complete Boolean algebra `𝒫 X`. -/
abbrev setObj (X : Type u) : OmegaBA.{u} where
  carrier := Set X
  complete a := ⟨⨆ n, a n, isLUB_iSup⟩

/-- The inverse image `f⁻¹(S) = {x | f x is defined and f x ∈ S}` under a
partial function. -/
def preimg {X Y : Type u} (f : X → Part Y) (S : Set Y) : Set X :=
  {x | ∃ h : (f x).Dom, (f x).get h ∈ S}

theorem mem_preimg {X Y : Type u} (f : X → Part Y) (S : Set Y) (x : X) :
    x ∈ preimg f S ↔ ∃ y, y ∈ f x ∧ y ∈ S :=
  ⟨fun ⟨h, hS⟩ => ⟨_, Part.get_mem h, hS⟩, fun ⟨y, hy, hS⟩ =>
    ⟨Part.dom_iff_mem.2 ⟨y, hy⟩, by rwa [Part.get_eq_of_mem hy]⟩⟩

theorem preimg_mono {X Y : Type u} (f : X → Part Y) {S T : Set Y} (h : S ⊆ T) :
    preimg f S ⊆ preimg f T :=
  fun _ ⟨hd, hS⟩ => ⟨hd, h hS⟩

/-- **SIG 49** (`prop:powerset-functor`, main.tex:1388): `f ↦ f⁻¹` is a
morphism of `ωBA`: it preserves countable joins and nonempty countable meets
(the meet of the empty family, `Y`, is not preserved when `f` is not total). -/
def preHom {X Y : Type u} (f : X →. Y) : setObj Y ⟶ setObj X where
  toFun := preimg f
  map_bot := Set.ext fun x => ⟨fun ⟨_, h⟩ => h, fun h => h.elim⟩
  map_sup a s h := by
    replace h := (set_isLUB_iff a s).1 h
    refine (set_isLUB_iff _ _).2 ?_
    ext x
    rw [h]
    constructor
    · rintro ⟨hd, hs⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hs
      exact Set.mem_iUnion.2 ⟨n, hd, hn⟩
    · intro hx
      obtain ⟨n, hd, hn⟩ := Set.mem_iUnion.1 hx
      exact ⟨hd, Set.mem_iUnion.2 ⟨n, hn⟩⟩
  map_inf a s h := by
    replace h := (set_isGLB_iff a s).1 h
    refine (set_isGLB_iff _ _).2 ?_
    ext x
    rw [h]
    constructor
    · rintro ⟨hd, hs⟩
      exact Set.mem_iInter.2 fun n => ⟨hd, Set.mem_iInter.1 hs n⟩
    · intro hx
      obtain ⟨hd, -⟩ := Set.mem_iInter.1 hx 0
      refine ⟨hd, Set.mem_iInter.2 fun n => ?_⟩
      obtain ⟨hd', h'⟩ := Set.mem_iInter.1 hx n
      exact h'

theorem preimg_injective {X Y : Type u} {f g : X → Part Y} (h : preimg f = preimg g) : f = g := by
  funext x
  refine Part.ext fun y => ?_
  have := congrArg (fun F => x ∈ F {y}) h
  simp only [mem_preimg, Set.mem_singleton_iff, exists_eq_right] at this
  exact Iff.of_eq this

theorem preimg_id (X : Type u) : preimg (fun x : X => Part.some x) = id := by
  funext S; ext x
  rw [mem_preimg]
  exact ⟨fun ⟨y, hy, hS⟩ => (Part.mem_some_iff.1 hy) ▸ hS, fun h => ⟨x, Part.mem_some x, h⟩⟩

theorem preimg_comp {X Y Z : Type u} (f : X → Part Y) (g : Y → Part Z) :
    preimg (fun x => (f x).bind g) = preimg f ∘ preimg g := by
  funext S; ext x
  simp only [Function.comp_apply, mem_preimg, Part.mem_bind_iff]
  exact ⟨fun ⟨z, ⟨y, hy, hz⟩, hS⟩ => ⟨y, hy, z, hz, hS⟩,
    fun ⟨y, hy, z, hz, hS⟩ => ⟨z, ⟨y, hy, hz⟩, hS⟩⟩

open Classical in
theorem preimg_truth (A : Type u) (S : Set PUnit.{u + 1}) :
    preimg (fun _ : A => Part.some PUnit.unit) S =
      cond (decide (PUnit.unit ∈ S)) Set.univ ∅ := by
  by_cases h : PUnit.unit ∈ S
  · simp only [h, decide_true, Bool.cond_true]
    exact Set.eq_univ_of_forall fun x => ⟨trivial, h⟩
  · simp only [h, decide_false, Bool.cond_false]
    exact Set.eq_empty_of_forall_notMem fun x ⟨_, hx⟩ => h hx

/-- **SIG 49** (`prop:powerset-functor`, main.tex:1386): the contravariant
powerset functor `𝒫 : Pfn → ωBAᵒᵖ`, `𝒫(f)(S) = {x | f(x) defined, ∈ S}`. -/
def powerset : PartialFun.{u} ⥤ OmegaBA.{u}ᵒᵖ where
  obj X := op (setObj X)
  map f := (preHom f).op
  map_id X := by
    apply Quiver.Hom.unop_inj
    exact hom_ext fun S => congrFun (preimg_id X) S
  map_comp {X Y Z} f g := by
    apply Quiver.Hom.unop_inj
    exact hom_ext fun S => congrFun (preimg_comp (X := X) (Y := Y) (Z := Z) f g) S

instance : powerset.{u}.Faithful :=
  ⟨fun {X Y} f g h => preimg_injective (X := X) (Y := Y)
    (congrArg (fun k => Hom.toFun (Quiver.Hom.unop k)) h)⟩

/-- The component sets of a cocone over `𝒫 ∘ X`, as plain sets. -/
def coconeSet {J : Type} {X : J → Type u} (t : Cocone (Discrete.functor (C := PartialFun.{u}) X ⋙ powerset))
    (j : J) (z : t.pt.unop.carrier) : Set (X j) :=
  (t.ι.app ⟨j⟩).unop.toFun z

theorem coconeSet_isLUB {J : Type} {X : J → Type u}
    (t : Cocone (Discrete.functor (C := PartialFun.{u}) X ⋙ powerset)) (j : J)
    {a : ℕ → t.pt.unop.carrier} {s : t.pt.unop.carrier} (h : IsLUB (Set.range a) s) :
    coconeSet t j s = ⋃ n, coconeSet t j (a n) :=
  (set_isLUB_iff _ _).1 ((t.ι.app ⟨j⟩).unop.map_sup a s h)

theorem coconeSet_isGLB {J : Type} {X : J → Type u}
    (t : Cocone (Discrete.functor (C := PartialFun.{u}) X ⋙ powerset)) (j : J)
    {a : ℕ → t.pt.unop.carrier} {s : t.pt.unop.carrier} (h : IsGLB (Set.range a) s) :
    coconeSet t j s = ⋂ n, coconeSet t j (a n) :=
  (set_isGLB_iff _ _).1 ((t.ι.app ⟨j⟩).unop.map_inf a s h)

/-- `𝒫 (Σ j, X_j) = ∏ 𝒫 X_j`: the cotuple of a cocone. -/
def sigmaLift {J : Type} (X : J → Type u)
    (t : Cocone (Discrete.functor (C := PartialFun.{u}) X ⋙ powerset)) :
    t.pt.unop ⟶ setObj (Σ j, X j) where
  toFun z := {p | p.2 ∈ coconeSet t p.1 z}
  map_bot := Set.ext fun p => by
    show p.2 ∈ coconeSet t p.1 ⊥ ↔ False
    rw [coconeSet, (t.ι.app ⟨p.1⟩).unop.map_bot]; exact Iff.rfl
  map_sup a s h := by
    refine (set_isLUB_iff _ _).2 ?_
    ext p
    show p.2 ∈ coconeSet t p.1 s ↔ _
    rw [coconeSet_isLUB t p.1 h]
    simp only [Set.mem_iUnion]
    exact Iff.rfl
  map_inf a s h := by
    refine (set_isGLB_iff _ _).2 ?_
    ext p
    show p.2 ∈ coconeSet t p.1 s ↔ _
    rw [coconeSet_isGLB t p.1 h]
    simp only [Set.mem_iInter]
    exact Iff.rfl

theorem preimg_inj {J : Type} (X : J → Type u) (j : J) (S : Set (Σ j, X j)) (x : X j) :
    x ∈ preimg (fun x : X j => (Part.some ⟨j, x⟩ : Part (Σ j, X j))) S ↔
      (⟨j, x⟩ : Σ j, X j) ∈ S := by
  rw [mem_preimg]
  exact ⟨fun ⟨y, hy, hS⟩ => (Part.mem_some_iff.1 hy) ▸ hS, fun h => ⟨_, Part.mem_some _, h⟩⟩

/-- **SIG 49**: `𝒫` sends the coproduct `Σ j, X_j` of `Pfn` to a coproduct of
`ωBAᵒᵖ` (a product `∏ 𝒫 X_j` of `ωBA`). -/
def powersetSigmaIsColimit {J : Type} (X : J → Type u) :
    IsColimit (powerset.mapCocone (Pfn.sigmaCofan (X := X))) where
  desc t := (sigmaLift X t).op
  fac t j := by
    obtain ⟨j⟩ := j
    apply Quiver.Hom.unop_inj
    refine hom_ext fun z => Set.ext fun x => ?_
    exact preimg_inj X j _ x
  uniq t m hm := by
    apply Quiver.Hom.unop_inj
    refine hom_ext fun z => Set.ext fun p => ?_
    obtain ⟨j, x⟩ := p
    have h1 := congrArg (fun k => Hom.toFun (Quiver.Hom.unop k) z) (hm ⟨j⟩)
    have h2 : x ∈ preimg (fun x : X j => (Part.some ⟨j, x⟩ : Part (Σ j, X j))) (m.unop.toFun z) ↔
        x ∈ coconeSet t j z := Iff.of_eq (congrArg (x ∈ ·) h1)
    exact (preimg_inj X j _ x).symm.trans h2

instance powerset_preservesColimitsOfShape (J : Type) :
    PreservesColimitsOfShape (Discrete J) powerset.{u} := by
  constructor
  intro K
  have : PreservesColimit (Discrete.functor (K.obj ∘ Discrete.mk)) powerset.{u} :=
    preservesColimit_of_preserves_colimit_cocone (Pfn.sigmaCofanIsColimit _)
      (powersetSigmaIsColimit (fun j => ((K.obj ∘ Discrete.mk) j : Type u)))
  exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

open Classical in
/-- `𝒫 {*} ≅ {0,1}` in `ωBA`. -/
noncomputable def setPUnitIso : setObj PUnit.{1} ≅ two where
  hom :=
    { toFun := fun S => decide (PUnit.unit ∈ S)
      map_bot := decide_eq_false (Set.notMem_empty _)
      map_sup := fun a s h => by
        rw [set_isLUB_iff] at h
        rw [bool_isLUB_iff, h]
        simp
      map_inf := fun a s h => by
        rw [set_isGLB_iff] at h
        rw [bool_isGLB_iff, h]
        simp }
  inv := boolMap (setObj PUnit.{1}) Set.univ
  hom_inv_id := hom_ext fun S => by
    show cond (decide (PUnit.unit ∈ S)) Set.univ ⊥ = S
    by_cases h : PUnit.unit ∈ S
    · simp only [h, decide_true, Bool.cond_true]
      exact (Set.eq_univ_of_forall fun t => h).symm
    · simp only [h, decide_false, Bool.cond_false]
      exact (Set.eq_empty_of_forall_notMem fun t ht => h ht).symm
  inv_hom_id := hom_ext fun b => by
    cases b
    · exact decide_eq_false (Set.notMem_empty _)
    · exact decide_eq_true (Set.mem_univ _)

/-- **SIG 49** (`prop:powerset-functor`, main.tex:1386, Proposition): the
contravariant powerset functor is a faithful morphism of σ-effectuses
`𝒫 : Pfn → ωBAᵒᵖ`: it preserves countable coproducts
(`𝒫(Σ X_j) = ∏ 𝒫 X_j`), the unit (`𝒫{*} ≅ {0,1}`) and truth maps, and is
faithful (`powerset.Faithful`). -/
noncomputable def powersetMorphism : SigmaEffectusMorphism PartialFun.{0} OmegaBA.{0}ᵒᵖ where
  F := powerset
  preserves J _ := inferInstance
  u := setPUnitIso.op
  map_truth A := by
    apply Quiver.Hom.unop_inj
    refine hom_ext fun S => ?_
    exact preimg_truth A S

end Powerset

/-! ## Composition of morphisms of σ-effectuses -/

/-- Morphisms of σ-effectuses compose. -/
noncomputable def SigmaEffectusMorphism.comp {C : Type u} [Category.{v} C]
    [HasCountableCoproducts C] [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]
    {D : Type u'} [Category.{v'} D] [HasCountableCoproducts D] [∀ X Y : D, SigmaPAM (X ⟶ Y)]
    [SigmaEffectus D] {E : Type w} [Category.{w'} E] [HasCountableCoproducts E]
    [∀ X Y : E, SigmaPAM (X ⟶ Y)] [SigmaEffectus E]
    (F : SigmaEffectusMorphism C D) (G : SigmaEffectusMorphism D E) :
    SigmaEffectusMorphism C E where
  F := F.F ⋙ G.F
  preserves J _ := by
    haveI := F.preserves J
    haveI := G.preserves J
    infer_instance
  u := G.u ≪≫ G.F.mapIso F.u
  map_truth A := by
    show G.F.map (F.F.map (truth A)) = _
    rw [F.map_truth, G.F.map_comp, G.map_truth, Category.assoc]
    rfl

/-! ## SIG 48: substate-separated σ-effectuses with scalars `{0,1}` embed in `Pfn` -/

section Embedding

variable {C : Type u} [Category.{v} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]

section Scalars

variable (hS : EMIso (Scal C) Bool)
include hS

/-- With scalars `{0,1}`, every scalar is `0` or `1`. -/
theorem scal_eq_zero_or_one (s : Scal C) : s = 0 ∨ s = 1 := by
  obtain ⟨φ, ψ, h1, h2⟩ := hS
  cases hs : φ.toFun s
  · left
    rw [← h1 s, hs]
    exact emHom_map_zero ψ
  · right
    rw [← h1 s, hs]
    exact ψ.map_one

theorem scal_zero_ne_one : (0 : Scal C) ≠ 1 := by
  obtain ⟨φ, ψ, h1, h2⟩ := hS
  intro h
  have := congrArg φ.toFun h
  rw [emHom_map_zero φ, φ.map_one] at this
  exact Bool.noConfusion this

theorem scal_perp {s t : Scal C} (h : Perp s t) : s = 0 ∨ t = 0 := by
  rcases scal_eq_zero_or_one hS s with hs | hs
  · exact Or.inl hs
  rcases scal_eq_zero_or_one hS t with ht | ht
  · exact Or.inr ht
  obtain ⟨φ, ψ, h1, h2⟩ := hS
  have := φ.perp_map h
  rw [hs, ht, φ.map_one] at this
  exact Bool.noConfusion (show (true && true) = false from this)

theorem substate_eq_zero_iff {X : C} (ω : Substate X) : ω = 0 ↔ ω ≫ truth X = 0 :=
  ⟨fun h => h ▸ FinPAC.zero_comp _, fun h => EffectusPartialForm.eq_zero_of_one_zero h⟩

/-- With scalars `{0,1}`, the nonzero substates are the states. -/
theorem isTotal_iff_ne_zero {X : C} (ω : Substate X) : IsTotal ω ↔ ω ≠ 0 := by
  have e1 : truth (effObj C) = (1 : Scal C) := rfl
  constructor
  · intro h h0
    have : (0 : Scal C) = 1 := by
      rw [← e1, ← h, h0, FinPAC.zero_comp]
    exact scal_zero_ne_one hS this
  · intro h
    rcases scal_eq_zero_or_one hS (ω ≫ truth X) with h0 | h1
    · exact (h ((substate_eq_zero_iff hS ω).2 h0)).elim
    · exact h1

/-- A nonzero substate of `∐ A_j` lives on exactly one summand. -/
theorem nz_decomp {J : Type} [Countable J] (A : J → C) (ω : Substate (∐ A)) (hω : ω ≠ 0) :
    ∃ j, ω ≫ pproj A j ≠ 0 ∧ (∀ k, k ≠ j → ω ≫ pproj A k = 0) ∧
      ω = (ω ≫ pproj A j) ≫ Sigma.ι A j := by
  classical
  let y : J → Substate (∐ A) := fun j => (ω ≫ pproj A j) ≫ Sigma.ι A j
  have hy : SumsTo y ω := sumsTo_decomp A ω
  have hback : ∀ j, y j ≫ pproj A j = ω ≫ pproj A j := fun j => by
    simp only [y, Category.assoc, ι_pproj_self, Category.comp_id]
  have hone : ∀ i j, i ≠ j → ω ≫ pproj A i = 0 ∨ ω ≫ pproj A j = 0 := by
    intro i j hij
    have hp : Perp (y i) (y j) := by
      have := summable_comp_injective hy.summable ![i, j] (by
        intro a b hab
        fin_cases a <;> fin_cases b <;> first | rfl | exact absurd hab hij |
          exact absurd hab.symm hij)
      exact (sumsTo_congr (fun k => by fin_cases k <;> rfl)).1 (sumsTo_sum this) |>.summable
    obtain ⟨hp', -⟩ := FinPAC.comp_ovee hp (truth (∐ A))
    rcases scal_perp hS hp' with h0 | h0
    · left
      rw [← hback, (substate_eq_zero_iff hS _).2 h0, FinPAC.zero_comp]
    · right
      rw [← hback, (substate_eq_zero_iff hS _).2 h0, FinPAC.zero_comp]
  have hex : ∃ j, ω ≫ pproj A j ≠ 0 := by
    by_contra hn
    push Not at hn
    have : ∀ j, y j = zero := fun j => by
      show (ω ≫ pproj A j) ≫ Sigma.ι A j = zero
      rw [hn j, FinPAC.zero_comp]; rfl
    exact hω (hy.unique ((sumsTo_congr fun j => (this j).symm).1 (sumsTo_zero_family J)))
  obtain ⟨j, hj⟩ := hex
  have hk : ∀ k, k ≠ j → ω ≫ pproj A k = 0 := fun k hk =>
    (hone k j hk).resolve_right hj
  refine ⟨j, hj, hk, hy.unique (sumsTo_single y j fun k hk' => ?_)⟩
  show (ω ≫ pproj A k) ≫ Sigma.ι A k = zero
  rw [hk k hk', FinPAC.zero_comp]; rfl

end Scalars

open Classical in
/-- `f ∘ -` on nonzero substates, undefined where it hits `0`. -/
noncomputable def nzMap {A B : C} (f : A ⟶ B) :
    {ω : Substate A // ω ≠ 0} → Part {ω : Substate B // ω ≠ 0} :=
  fun ω => if h : ω.1 ≫ f = 0 then Part.none else Part.some ⟨ω.1 ≫ f, h⟩

theorem nzMap_of_ne {A B : C} (f : A ⟶ B) (ω : {ω : Substate A // ω ≠ 0}) (h : ω.1 ≫ f ≠ 0) :
    nzMap f ω = Part.some ⟨ω.1 ≫ f, h⟩ := by
  unfold nzMap; rw [dite_cond_eq_false (eq_false h)]

theorem nzMap_of_eq {A B : C} (f : A ⟶ B) (ω : {ω : Substate A // ω ≠ 0}) (h : ω.1 ≫ f = 0) :
    nzMap f ω = Part.none := by
  unfold nzMap; rw [dite_cond_eq_true (eq_true h)]

/-- **SIG 48** (main.tex:1354): the functor `F : C → Pfn`, `F A = {ω ∈ sSt A | ω ≠ 0}`
(the composite `C → sWMod[{0,1}] ≃ Pfn` of SIG 34 and SIG 47, computed). -/
noncomputable def nzFunctor : C ⥤ PartialFun.{v} where
  obj A := PartialFun.of {ω : Substate A // ω ≠ 0}
  map f := nzMap f
  map_id A := funext fun ω => by
    have h : ω.1 ≫ 𝟙 A ≠ 0 := by rw [Category.comp_id]; exact ω.2
    rw [nzMap_of_ne _ _ h]
    exact congrArg Part.some (Subtype.ext (Category.comp_id _))
  map_comp {A B D} f g := funext fun ω => by
    show nzMap (f ≫ g) ω = (nzMap f ω).bind (nzMap g)
    by_cases h1 : ω.1 ≫ f = 0
    · rw [nzMap_of_eq _ _ h1, Part.bind_none, nzMap_of_eq]
      rw [← Category.assoc, h1, FinPAC.zero_comp]
    · rw [nzMap_of_ne _ _ h1, Part.bind_some]
      by_cases h2 : (ω.1 ≫ f) ≫ g = 0
      · rw [nzMap_of_eq g ⟨ω.1 ≫ f, h1⟩ h2,
          nzMap_of_eq (f ≫ g) ω (by rw [← Category.assoc]; exact h2)]
      · rw [nzMap_of_ne g ⟨ω.1 ≫ f, h1⟩ h2,
          nzMap_of_ne (f ≫ g) ω (by rw [← Category.assoc]; exact h2)]
        exact congrArg Part.some (Subtype.ext (Category.assoc _ _ _).symm)

/-- **SIG 48**: `F` is faithful when `C` is substate-separated. -/
theorem nzFunctor_faithful (hsep : SubstateSeparated C) : (nzFunctor (C := C)).Faithful := by
  constructor
  intro A B f g h
  refine hsep f g fun ω => ?_
  by_cases hω : ω = 0
  · rw [hω, FinPAC.zero_comp, FinPAC.zero_comp]
  have e := congrFun h ⟨ω, hω⟩
  change nzMap f ⟨ω, hω⟩ = nzMap g ⟨ω, hω⟩ at e
  by_cases hf : ω ≫ f = 0 <;> by_cases hg : ω ≫ g = 0
  · rw [hf, hg]
  · rw [nzMap_of_eq f ⟨ω, hω⟩ hf, nzMap_of_ne g ⟨ω, hω⟩ hg] at e
    exact absurd e.symm (Part.some_ne_none _)
  · rw [nzMap_of_ne f ⟨ω, hω⟩ hf, nzMap_of_eq g ⟨ω, hω⟩ hg] at e
    exact absurd e (Part.some_ne_none _)
  · rw [nzMap_of_ne f ⟨ω, hω⟩ hf, nzMap_of_ne g ⟨ω, hω⟩ hg] at e
    exact congrArg Subtype.val (Part.some_injective e)

section Preserves

variable (hS : EMIso (Scal C) Bool)
include hS

theorem ι_ne_zero {J : Type} [Countable J] (A : J → C) (j : J) {ν : Substate (A j)} (hν : ν ≠ 0) :
    ν ≫ Sigma.ι A j ≠ 0 := by
  intro h
  apply hν
  have := congrArg (· ≫ pproj A j) h
  simp only [Category.assoc, ι_pproj_self, Category.comp_id, FinPAC.zero_comp] at this
  exact this

/-- The bijection `Σ_j F(A_j) ≅ F(∐ A_j)`, `(j, ν) ↦ κ_j ∘ ν`. -/
noncomputable def nzSigmaEquiv {J : Type} [Countable J] (A : J → C) :
    (Σ j, {ω : Substate (A j) // ω ≠ 0}) ≃ {ω : Substate (∐ A) // ω ≠ 0} :=
  Equiv.ofBijective (fun p => ⟨p.2.1 ≫ Sigma.ι A p.1, ι_ne_zero hS A p.1 p.2.2⟩) <| by
    constructor
    · rintro ⟨j, ν, hν⟩ ⟨k, μ, hμ⟩ e
      have e' : ν ≫ Sigma.ι A j = μ ≫ Sigma.ι A k := congrArg Subtype.val e
      have hjk : j = k := by
        by_contra hjk
        apply hν
        have := congrArg (· ≫ pproj A j) e'
        simp only [Category.assoc, ι_pproj_self, Category.comp_id,
          ι_pproj_ne _ (Ne.symm hjk), FinPAC.comp_zero] at this
        exact this
      subst hjk
      have := congrArg (· ≫ pproj A j) e'
      simp only [Category.assoc, ι_pproj_self, Category.comp_id] at this
      subst this
      rfl
    · rintro ⟨ω, hω⟩
      obtain ⟨j, hj, -, e⟩ := nz_decomp hS A ω hω
      exact ⟨⟨j, ω ≫ pproj A j, hj⟩, Subtype.ext e.symm⟩

/-- `Σ_j F(A_j) ≅ F(∐ A_j)` in `Pfn`. -/
noncomputable def nzSigmaIso {J : Type} [Countable J] (A : J → C) :
    (Pfn.sigmaCofan fun j => (nzFunctor (C := C)).obj (A j)).pt ≅ (nzFunctor (C := C)).obj (∐ A) :=
  PartialFun.Iso.mk (nzSigmaEquiv hS A)

theorem nzFunctor_sigmaComparison {J : Type} [Countable J] (A : J → C) :
    sigmaComparison (nzFunctor (C := C)) A =
      (Pfn.coprodIso (fun j => (nzFunctor (C := C)).obj (A j))).hom ≫ (nzSigmaIso hS A).hom := by
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [ι_comp_sigmaComparison, ← Category.assoc, Pfn.ι_coprodIso]
  refine funext fun ν => ?_
  obtain ⟨ν, hν⟩ := ν
  exact (nzMap_of_ne _ ⟨ν, hν⟩ (ι_ne_zero hS A j hν)).trans (Part.bind_some _ _).symm

theorem nzFunctor_preserves (J : Type) [Countable J] :
    PreservesColimitsOfShape (Discrete J) (nzFunctor (C := C)) := by
  constructor
  intro K
  have key : ∀ A : J → C, PreservesColimit (Discrete.functor A) (nzFunctor (C := C)) := by
    intro A
    have : IsIso (sigmaComparison (nzFunctor (C := C)) A) := by
      rw [nzFunctor_sigmaComparison hS]; infer_instance
    exact PreservesCoproduct.of_iso_comparison _ _
  have := key (K.obj ∘ Discrete.mk)
  exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

/-- `{*} ≅ F(I) = {1}`. -/
noncomputable def nzUnitEquiv : PUnit.{v + 1} ≃ {ω : Substate (effObj C) // ω ≠ 0} where
  toFun _ := ⟨𝟙 _, fun h => scal_zero_ne_one hS (h.symm.trans truth_effObj_eq_id.symm)⟩
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv ω := by
    obtain ⟨ω, hω⟩ := ω
    refine Subtype.ext ?_
    rcases scal_eq_zero_or_one hS ω with h | h
    · exact (hω h).elim
    · exact (h.trans truth_effObj_eq_id).symm

/-- `{*} ≅ F(I)` in `Pfn`. -/
noncomputable def nzUnitIso : effObj PartialFun.{v} ≅ (nzFunctor (C := C)).obj (effObj C) :=
  PartialFun.Iso.mk (nzUnitEquiv hS)

/-- **SIG 48** (main.tex:1354, Theorem): a substate-separated σ-effectus
with scalars `{0,1}` has a faithful morphism of σ-effectuses `F : C → Pfn`,
and `St A ≅ F A` for all `A`.  Here `F A` is the set of nonzero substates of
`A` (the composite of `sSt` and SIG 47). -/
noncomputable def nzMorphism : SigmaEffectusMorphism C PartialFun.{v} where
  F := nzFunctor
  preserves J _ := nzFunctor_preserves hS J
  u := nzUnitIso hS
  map_truth A := funext fun ω => by
    obtain ⟨ω, hω⟩ := ω
    have hne : ω ≫ truth A ≠ 0 := fun h => hω ((substate_eq_zero_iff hS _).2 h)
    have e : ω ≫ truth A = 𝟙 _ := by
      rcases scal_eq_zero_or_one hS (ω ≫ truth A) with h | h
      · exact (hne h).elim
      · exact h.trans truth_effObj_eq_id
    exact (nzMap_of_ne _ ⟨ω, hω⟩ hne).trans ((congrArg Part.some (Subtype.ext e)).trans
      (Part.bind_some _ _).symm)

theorem nzMorphism_faithful (hsep : SubstateSeparated C) : (nzMorphism hS).F.Faithful :=
  nzFunctor_faithful hsep

/-- **SIG 48** (main.tex:1356): `St A ≅ F A`. -/
noncomputable def statEquivNz (A : C) : Stat A ≃ ((nzMorphism hS).F.obj A : Type v) where
  toFun ω := ⟨ω.1, (isTotal_iff_ne_zero hS ω.1).1 ω.2⟩
  invFun ω := ⟨ω.1, (isTotal_iff_ne_zero hS ω.1).2 ω.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **SIG 48** (main.tex:1354, Theorem), in one statement. -/
theorem sig48 (hsep : SubstateSeparated C) :
    ∃ F : SigmaEffectusMorphism C PartialFun.{v}, F.F.Faithful ∧
      ∀ A : C, Nonempty (Stat A ≃ (F.F.obj A : Type v)) :=
  ⟨nzMorphism hS, nzMorphism_faithful hS hsep, fun A => ⟨statEquivNz hS A⟩⟩

end Preserves

/-! ## SIG 50: the embedding into `ωBAᵒᵖ` -/

/-- **SIG 50** (main.tex:1401, Theorem): a substate-separated σ-effectus with
scalars `{0,1}` has a faithful morphism of σ-effectuses `G : C → ωBAᵒᵖ`, the
composite of SIG 48 and SIG 49 (for hom-sets in `Type`, the universe of
`ωBA`). -/
theorem sig50 {C : Type u} [Category.{0} C] [HasCountableCoproducts C]
    [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C] (hS : EMIso (Scal C) Bool)
    (hsep : SubstateSeparated C) :
    ∃ G : SigmaEffectusMorphism C OmegaBA.{0}ᵒᵖ, G.F.Faithful := by
  refine ⟨(nzMorphism hS).comp powersetMorphism, ?_⟩
  have : (nzFunctor (C := C)).Faithful := nzFunctor_faithful hsep
  show (nzFunctor ⋙ powerset).Faithful
  infer_instance

/-- **SIG 50** (main.tex:1432, the text after it): the predicates of a
substate-separated σ-effectus with scalars `{0,1}` form an **orthoalgebra**:
`p ⊥ p` implies `p = 0`. -/
theorem pred_orthoalgebra (hS : EMIso (Scal C) Bool) (hsep : SubstateSeparated C) {A : C}
    (p : Pred A) (h : Perp p p) : p = 0 := by
  refine hsep p 0 fun ω => ?_
  obtain ⟨h', -⟩ := FinPAC.ovee_comp h ω
  rw [FinPAC.comp_zero]
  exact (scal_perp hS h').elim id id

end Embedding

end Papers.SIG
