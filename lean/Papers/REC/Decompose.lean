/-
Papers/REC/Decompose.lean

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707 (2021): §4 "Decomposing into sharp and convex
systems" — points REC 87–99 of `../papers/REC-points.csv`.

Design:
* Effectuses are thesis B's *effectuses in partial form* (REC 9), as in
  `Papers/REC/Effectus.lean`; composition is diagrammatic, `f ≫ g = g ∘ f`.
* **Explicit coproducts.**  Every effectus built here (the Karoubi envelope, the
  parts `C_s`, and the counterexample `BoolMat`) has coproducts given by an
  explicit formula, while the tree's finPAC axioms speak about Mathlib's
  *chosen* coproducts.  `ExplicitCoproducts` packages an explicit binary
  coproduct and initial object, and `ExplicitCoproducts.finPAC_of` turns the
  finPAC axioms stated for the explicit coproduct into `FinPAC` (the comparison
  isomorphism is `coconePointUniqueUpToIso`).
* **The Karoubi envelope** (REC 88) is Mathlib's `Karoubi C`.  The effectus
  structure of REC 89 is built generically on `KCat S`, the full subcategory of
  `Karoubi C` on the objects satisfying a predicate `S.Q`, with effect object
  `(I, S.e)` for an idempotent scalar `S.e`.  `Split C := KCat (splitSpec C)`
  takes all objects and `e = id`; it is isomorphic to `Karoubi C`
  (`splitEquivKaroubi`).  The same construction gives the parts `C_s` of
  REC 90–92: the objects `(A, e_A)` for a central family of idempotents
  `e_A`, with morphisms `f = e_B ∘ f ∘ e_A` and identity `e_A` — exactly the
  printed `C_s`.
* **The splitting theorem.**  REC 90, 91 and 92 share one argument (the proof
  of REC 90).  `CentralSplitting D` records a family of idempotents `e_A`
  natural in `A`, complementary to a second family `e'_A` (`e ⊻ e' = id`,
  `e ∘ e' = 0`), both split; `CentralSplitting.equivalence` is the
  equivalence `D ≌ D_e × D_e'` of the proof of REC 90.  The three
  propositions differ only in how the families and their splittings are
  obtained.
-/
import Papers.REC.Effectus
import Papers.REC.Algebras
import Papers.SEA.Boolean
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.CategoryTheory.Products.Basic

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Idempotents
open CategoryTheory.Limits hiding HasImages
open Theses.B.Eff

namespace Papers.REC

universe u v w

/-! ## Explicit finite coproducts -/

section Explicit

/-- An explicit binary coproduct and initial object in a category `D`. -/
structure ExplicitCoproducts (D : Type u) [Category.{v} D] where
  pt : D → D → D
  inl : ∀ X Y : D, X ⟶ pt X Y
  inr : ∀ X Y : D, Y ⟶ pt X Y
  desc : ∀ {X Y T : D}, (X ⟶ T) → (Y ⟶ T) → (pt X Y ⟶ T)
  inl_desc : ∀ {X Y T : D} (f : X ⟶ T) (g : Y ⟶ T), inl X Y ≫ desc f g = f
  inr_desc : ∀ {X Y T : D} (f : X ⟶ T) (g : Y ⟶ T), inr X Y ≫ desc f g = g
  uniq : ∀ {X Y T : D} (m : pt X Y ⟶ T), m = desc (inl X Y ≫ m) (inr X Y ≫ m)
  init : D
  isInitial : IsInitial init

namespace ExplicitCoproducts

variable {D : Type u} [Category.{v} D] (E : ExplicitCoproducts D)

/-- The explicit cofan is a colimit. -/
def isColimit (X Y : D) : IsColimit (BinaryCofan.mk (E.inl X Y) (E.inr X Y)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => E.desc f g) (fun f g => E.inl_desc f g)
    (fun f g => E.inr_desc f g) (fun f g m h1 h2 => by rw [← h1, ← h2]; exact E.uniq m)

include E in
/-- Finite coproducts from the explicit ones. -/
theorem hasFiniteCoproducts : HasFiniteCoproducts D :=
  letI : HasInitial D := E.isInitial.hasInitial
  letI : ∀ X Y : D, HasColimit (pair X Y) := fun X Y => HasColimit.mk ⟨_, E.isColimit X Y⟩
  letI : HasBinaryCoproducts D := hasBinaryCoproducts_of_hasColimit_pair _
  hasFiniteCoproducts_of_has_binary_and_initial

variable [HasFiniteCoproducts D]

/-- The comparison between the chosen and the explicit coproduct. -/
noncomputable def coprodIso (X Y : D) : X ⨿ Y ≅ E.pt X Y :=
  (coprodIsCoprod X Y).coconePointUniqueUpToIso (E.isColimit X Y)

theorem inl_coprodIso (X Y : D) :
    (coprod.inl : X ⟶ X ⨿ Y) ≫ (E.coprodIso X Y).hom = E.inl X Y :=
  (coprodIsCoprod X Y).comp_coconePointUniqueUpToIso_hom (E.isColimit X Y)
    ⟨WalkingPair.left⟩

theorem inr_coprodIso (X Y : D) :
    (coprod.inr : Y ⟶ X ⨿ Y) ≫ (E.coprodIso X Y).hom = E.inr X Y :=
  (coprodIsCoprod X Y).comp_coconePointUniqueUpToIso_hom (E.isColimit X Y)
    ⟨WalkingPair.right⟩

theorem coprod_desc_eq {X Y T : D} (f : X ⟶ T) (g : Y ⟶ T) :
    coprod.desc f g = (E.coprodIso X Y).hom ≫ E.desc f g := by
  apply coprod.hom_ext
  · rw [coprod.inl_desc, ← Category.assoc, inl_coprodIso, inl_desc]
  · rw [coprod.inr_desc, ← Category.assoc, inr_coprodIso, inr_desc]

theorem coprod_inl_eq (X Y : D) :
    (coprod.inl : X ⟶ X ⨿ Y) = E.inl X Y ≫ (E.coprodIso X Y).inv := by
  rw [← inl_coprodIso, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem coprod_inr_eq (X Y : D) :
    (coprod.inr : Y ⟶ X ⨿ Y) = E.inr X Y ≫ (E.coprodIso X Y).inv := by
  rw [← inr_coprodIso, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The finPAC axioms (thesis B 180VII), with the compatible-sum and untying
axioms stated for the explicit coproduct. -/
theorem finPAC_of [∀ X Y : D, PCM (X ⟶ Y)]
    (comp_ovee : ∀ {X Y Z : D} {f g : X ⟶ Y} (h : Perp f g) (k : Y ⟶ Z),
      ∃ h' : Perp (f ≫ k) (g ≫ k), ovee f g h ≫ k = ovee (f ≫ k) (g ≫ k) h')
    (ovee_comp : ∀ {W X Y : D} {f g : X ⟶ Y} (h : Perp f g) (k : W ⟶ X),
      ∃ h' : Perp (k ≫ f) (k ≫ g), k ≫ ovee f g h = ovee (k ≫ f) (k ≫ g) h')
    (comp_zero : ∀ {X Y Z : D} (f : X ⟶ Y), f ≫ (0 : Y ⟶ Z) = 0)
    (zero_comp : ∀ {X Y Z : D} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = 0)
    (compat : ∀ {X Y : D} (b : X ⟶ E.pt Y Y),
      Perp (b ≫ E.desc (𝟙 Y) 0) (b ≫ E.desc 0 (𝟙 Y)))
    (untie : ∀ {X Y : D} {f g : X ⟶ Y}, Perp f g →
      Perp (f ≫ E.inl Y Y) (g ≫ E.inr Y Y)) : FinPAC D where
  comp_ovee := comp_ovee
  ovee_comp := ovee_comp
  comp_zero := comp_zero
  zero_comp := zero_comp
  compatible_sum := fun {X Y} b => by
    have h1 : pproj₁ Y Y = (E.coprodIso Y Y).hom ≫ E.desc (𝟙 Y) 0 := E.coprod_desc_eq _ _
    have h2 : pproj₂ Y Y = (E.coprodIso Y Y).hom ≫ E.desc 0 (𝟙 Y) := E.coprod_desc_eq _ _
    rw [h1, h2, ← Category.assoc, ← Category.assoc]
    exact compat _
  untying := fun {X Y f g} h => by
    rw [E.coprod_inl_eq, E.coprod_inr_eq, ← Category.assoc, ← Category.assoc]
    exact (comp_ovee (untie h) _).1

end ExplicitCoproducts

end Explicit

/-! ## Generic effect-algebra and finPAC helpers -/

section Helpers

variable {D : Type u} [Category.{v} D] [HasFiniteCoproducts D] [∀ X Y : D, PCM (X ⟶ Y)]
  [FinPAC D]

/-- Conjugating a partial sum by two maps. -/
theorem conj_ovee {W X Y Z : D} (a : W ⟶ X) (b : Y ⟶ Z) {f g : X ⟶ Y} (h : Perp f g) :
    ∃ h' : Perp (a ≫ f ≫ b) (a ≫ g ≫ b),
      a ≫ ovee f g h ≫ b = ovee (a ≫ f ≫ b) (a ≫ g ≫ b) h' := by
  obtain ⟨h1, e1⟩ := FinPAC.comp_ovee h b
  obtain ⟨h2, e2⟩ := FinPAC.ovee_comp h1 a
  exact ⟨h2, by rw [e1, e2]⟩

/-- Postcomposition is monotone. -/
theorem le_comp_right' {X Y Z : D} {a b : X ⟶ Y} (h : a ≼ b) (k : Y ⟶ Z) :
    (a ≫ k) ≼ (b ≫ k) := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨h', e⟩ := FinPAC.comp_ovee hc k
  exact ⟨c ≫ k, h', e.symm⟩

end Helpers

/-- In an effect algebra, `a ⊻ b ≼ b` forces `a = 0`. -/
theorem eq_zero_of_ovee_le {E : Type u} [EffectAlgebra E] {a b : E} (h : Perp a b)
    (hle : ovee a b h ≼ b) : a = 0 := by
  have hge : b ≼ ovee a b h := ⟨a, PCM.perp_comm h, (PCM.ovee_comm h).symm⟩
  have e := eabasics_le_antisymm hle hge
  exact ovee_eq_self_left (PCM.perp_comm h) ((PCM.ovee_comm h).symm.trans e)

/-! ## REC 88–89: the Karoubi envelope as an effectus -/

section KCatSection

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- The explicit coproduct `(A, t) + (B, s) = (A + B, t + s)` in `Karoubi C`. -/
noncomputable def kcoprod (P P' : Karoubi C) : Karoubi C where
  X := P.X ⨿ P'.X
  p := coprod.map P.p P'.p
  idem := by rw [coprod.map_map, P.idem, P'.idem]

/-- The initial object `(0, id)` of `Karoubi C`. -/
noncomputable def kinit : Karoubi C := ⟨⊥_ C, 𝟙 _, Category.comp_id _⟩

variable (C) in
/-- The data of a full subcategory of `Karoubi C` carrying an effectus
structure: the objects satisfy `Q`, the effect object is `(I, e)` for an
idempotent scalar `e`, truth of every object is "inside `e`", and `Q` is closed
under the explicit coproducts and contains the initial object. -/
structure KSpec where
  Q : Karoubi C → Prop
  e : effObj C ⟶ effObj C
  e_idem : e ≫ e = e
  e_mem : Q ⟨effObj C, e, e_idem⟩
  truth_e : ∀ P : Karoubi C, Q P → P.p ≫ truth P.X ≫ e = P.p ≫ truth P.X
  coprod_mem : ∀ P P' : Karoubi C, Q P → Q P' → Q (kcoprod P P')
  init_mem : Q kinit

/-- The full subcategory of `Karoubi C` on the objects satisfying `S.Q`. -/
structure KCat (S : KSpec C) where
  obj : Karoubi C
  prop : S.Q obj

namespace KCat

variable {S : KSpec C}

instance category : Category.{v} (KCat S) where
  Hom X Y := Karoubi.Hom X.obj Y.obj
  id X := ⟨X.obj.p, by rw [X.obj.idem, X.obj.idem]⟩
  comp f g := ⟨f.f ≫ g.f, Karoubi.comp_proof g f⟩
  id_comp f := Karoubi.Hom.ext (Karoubi.p_comp f)
  comp_id f := Karoubi.Hom.ext (Karoubi.comp_p f)
  assoc f g h := Karoubi.Hom.ext (Category.assoc _ _ _)

@[simp] theorem comp_f {X Y Z : KCat S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Karoubi.Hom.f (f ≫ g) = f.f ≫ g.f := rfl

@[simp] theorem id_f (X : KCat S) : Karoubi.Hom.f (𝟙 X) = X.obj.p := rfl

theorem hom_ext {X Y : KCat S} {f g : X ⟶ Y} (h : f.f = g.f) : f = g :=
  Karoubi.Hom.ext h

/-- A morphism of `KCat S` from a morphism of `C`. -/
def homMk {X Y : KCat S} (f : X.obj.X ⟶ Y.obj.X) (h : X.obj.p ≫ f ≫ Y.obj.p = f) : X ⟶ Y :=
  (⟨f, h⟩ : Karoubi.Hom X.obj Y.obj)

@[simp] theorem homMk_f {X Y : KCat S} (f : X.obj.X ⟶ Y.obj.X) (h) :
    Karoubi.Hom.f (homMk (X := X) (Y := Y) f h) = f := rfl

theorem p_comp {X Y : KCat S} (f : X ⟶ Y) : X.obj.p ≫ f.f = f.f := Karoubi.p_comp f

theorem comp_p {X Y : KCat S} (f : X ⟶ Y) : f.f ≫ Y.obj.p = f.f := Karoubi.comp_p f

theorem comp_p_assoc {X Y : KCat S} (f : X ⟶ Y) {Z : C} (h : Y.obj.X ⟶ Z) :
    f.f ≫ Y.obj.p ≫ h = f.f ≫ h := by rw [← Category.assoc, comp_p]

theorem comm {X Y : KCat S} (f : X ⟶ Y) : X.obj.p ≫ f.f ≫ Y.obj.p = f.f :=
  Karoubi.Hom.comm f

/-! ### Explicit coproducts in `KCat S` -/

/-- The coproduct object. -/
noncomputable def pt (X Y : KCat S) : KCat S :=
  ⟨kcoprod X.obj Y.obj, S.coprod_mem _ _ X.prop Y.prop⟩

noncomputable def inl (X Y : KCat S) : X ⟶ pt X Y :=
  homMk (X.obj.p ≫ coprod.inl) (by simp [pt, kcoprod])

noncomputable def inr (X Y : KCat S) : Y ⟶ pt X Y :=
  homMk (Y.obj.p ≫ coprod.inr) (by simp [pt, kcoprod])

noncomputable def desc {X Y T : KCat S} (f : X ⟶ T) (g : Y ⟶ T) : pt X Y ⟶ T :=
  homMk (coprod.desc f.f g.f) (by
    apply coprod.hom_ext <;> simp [pt, kcoprod, p_comp, comp_p])

theorem pt_p (X Y : KCat S) : (pt X Y).obj.p = coprod.map X.obj.p Y.obj.p := rfl

noncomputable def initObj : KCat S := ⟨kinit, S.init_mem⟩

noncomputable def isInitialInit : IsInitial (initObj (S := S)) :=
  IsInitial.ofUniqueHom (fun T => homMk (initial.to T.obj.X) (initial.hom_ext _ _))
    (fun T m => hom_ext (initial.hom_ext _ _))

noncomputable def explicit : ExplicitCoproducts (KCat S) where
  pt := pt
  inl := inl
  inr := inr
  desc := desc
  inl_desc {X Y T} f g := hom_ext (by
    show (X.obj.p ≫ coprod.inl) ≫ coprod.desc f.f g.f = f.f
    rw [Category.assoc, coprod.inl_desc, p_comp])
  inr_desc {X Y T} f g := hom_ext (by
    show (Y.obj.p ≫ coprod.inr) ≫ coprod.desc f.f g.f = g.f
    rw [Category.assoc, coprod.inr_desc, p_comp])
  uniq {X Y T} m := hom_ext (by
    let mf : X.obj.X ⨿ Y.obj.X ⟶ T.obj.X := m.f
    have hm : coprod.map X.obj.p Y.obj.p ≫ mf = mf := p_comp m
    show mf = coprod.desc ((X.obj.p ≫ coprod.inl) ≫ mf) ((Y.obj.p ≫ coprod.inr) ≫ mf)
    apply coprod.hom_ext
    · rw [coprod.inl_desc, Category.assoc]
      conv_lhs => rw [← hm]
      rw [coprod.inl_map_assoc]
    · rw [coprod.inr_desc, Category.assoc]
      conv_lhs => rw [← hm]
      rw [coprod.inr_map_assoc])
  init := initObj
  isInitial := isInitialInit

instance hasFiniteCoproducts : HasFiniteCoproducts (KCat S) :=
  (explicit (S := S)).hasFiniteCoproducts

/-! ### The PCM enrichment -/

theorem ovee_mem {X Y : KCat S} {f g : X ⟶ Y} (h : Perp f.f g.f) :
    X.obj.p ≫ ovee f.f g.f h ≫ Y.obj.p = ovee f.f g.f h := by
  obtain ⟨h', e⟩ := conj_ovee X.obj.p Y.obj.p h
  rw [e]
  exact PCM.ovee_congr (comm f) (comm g) _ _

noncomputable instance homPCM (X Y : KCat S) : PCM (X ⟶ Y) where
  zero := homMk 0 (by rw [FinPAC.zero_comp, FinPAC.comp_zero])
  Perp f g := Perp f.f g.f
  ovee f g h := homMk (ovee f.f g.f h) (ovee_mem h)
  perp_comm h := PCM.perp_comm h
  ovee_comm h := hom_ext (PCM.ovee_comm h)
  perp_of_ovee_perp hab h := PCM.perp_of_ovee_perp (M := X.obj.X ⟶ Y.obj.X) hab h
  perp_ovee_of_ovee_perp hab h := PCM.perp_ovee_of_ovee_perp (M := X.obj.X ⟶ Y.obj.X) hab h
  ovee_assoc hab h := hom_ext (PCM.ovee_assoc (M := X.obj.X ⟶ Y.obj.X) hab h)
  zero_perp a := PCM.zero_perp a.f
  zero_ovee a := hom_ext (PCM.zero_ovee a.f)

@[simp] theorem zero_f {X Y : KCat S} : Karoubi.Hom.f (0 : X ⟶ Y) = 0 := rfl

@[simp] theorem ovee_f {X Y : KCat S} {f g : X ⟶ Y} (h : Perp f g) :
    Karoubi.Hom.f (ovee f g h : X ⟶ Y) = ovee f.f g.f h := rfl

theorem perp_iff {X Y : KCat S} (f g : X ⟶ Y) : Perp f g ↔ Perp f.f g.f := Iff.rfl

/-- `KCat S` is a finPAC. -/
instance finPAC : FinPAC (KCat S) :=
  (explicit (S := S)).finPAC_of
    (fun {X Y Z f g} h k => by
      obtain ⟨h', e⟩ := FinPAC.comp_ovee (show Perp f.f g.f from h) k.f
      exact ⟨h', hom_ext e⟩)
    (fun {W X Y f g} h k => by
      obtain ⟨h', e⟩ := FinPAC.ovee_comp (show Perp f.f g.f from h) k.f
      exact ⟨h', hom_ext e⟩)
    (fun f => hom_ext (FinPAC.comp_zero f.f))
    (fun f => hom_ext (FinPAC.zero_comp f.f))
    (fun {X Y} b => by
      let bf : X.obj.X ⟶ Y.obj.X ⨿ Y.obj.X := b.f
      show Perp (bf ≫ coprod.desc Y.obj.p 0) (bf ≫ coprod.desc 0 Y.obj.p)
      have hb : bf ≫ coprod.map Y.obj.p Y.obj.p = bf := comp_p b
      have e1 : coprod.map Y.obj.p Y.obj.p ≫ pproj₁ Y.obj.X Y.obj.X = coprod.desc Y.obj.p 0 := by
        apply coprod.hom_ext <;> simp [pproj₁, FinPAC.comp_zero]
      have e2 : coprod.map Y.obj.p Y.obj.p ≫ pproj₂ Y.obj.X Y.obj.X = coprod.desc 0 Y.obj.p := by
        apply coprod.hom_ext <;> simp [pproj₂, FinPAC.comp_zero]
      rw [← e1, ← e2, ← Category.assoc, hb, ← Category.assoc, hb]
      exact FinPAC.compatible_sum bf)
    (fun {X Y f g} h => by
      show Perp (f.f ≫ Y.obj.p ≫ coprod.inl) (g.f ≫ Y.obj.p ≫ coprod.inr)
      rw [comp_p_assoc, comp_p_assoc]
      exact FinPAC.untying (show Perp f.f g.f from h))

/-! ### The effects -/

/-- The effect object `(I, e)`. -/
abbrev effI : KCat S := ⟨⟨effObj C, S.e, S.e_idem⟩, S.e_mem⟩

/-- The truth predicate `1_{(A,t)} = 1_A ∘ t`. -/
noncomputable def one (X : KCat S) : X ⟶ effI :=
  homMk (X.obj.p ≫ truth X.obj.X) (by
    simp only [Category.assoc, Karoubi.idem_assoc]
    exact S.truth_e _ X.prop)

/-- The orthosupplement `p^⊥ := e ∘ p^⊥ ∘ t`. -/
noncomputable def orthK {X : KCat S} (p : X ⟶ effI) : X ⟶ effI :=
  homMk (X.obj.p ≫ orth (p.f : X.obj.X ⟶ effObj C) ≫ S.e) (by
    simp only [Category.assoc, Karoubi.idem_assoc, S.e_idem])

theorem perp_orthK {X : KCat S} (p : X ⟶ effI) :
    Perp p.f (X.obj.p ≫ orth (p.f : X.obj.X ⟶ effObj C) ≫ S.e) := by
  obtain ⟨h', -⟩ := conj_ovee X.obj.p S.e (EffectAlgebra.perp_orth (p.f : X.obj.X ⟶ effObj C))
  have hc : X.obj.p ≫ p.f ≫ S.e = p.f := comm p
  rw [hc] at h'
  exact h'

theorem ovee_orthK {X : KCat S} (p : X ⟶ effI) :
    ovee p.f (X.obj.p ≫ orth (p.f : X.obj.X ⟶ effObj C) ≫ S.e) (perp_orthK p) =
      X.obj.p ≫ truth X.obj.X := by
  obtain ⟨h', e⟩ := conj_ovee X.obj.p S.e (EffectAlgebra.perp_orth (p.f : X.obj.X ⟶ effObj C))
  have hl : X.obj.p ≫ ovee (p.f : X.obj.X ⟶ effObj C) (orth p.f)
      (EffectAlgebra.perp_orth _) ≫ S.e = X.obj.p ≫ truth X.obj.X := by
    rw [EffectAlgebra.ovee_orth]; exact S.truth_e _ X.prop
  rw [← hl, e]
  exact PCM.ovee_congr (comm p).symm rfl _ _

noncomputable instance effectus : EffectusPartialForm (KCat S) where
  I := effI
  one := one
  orth := orthK
  perp_orth p := perp_orthK p
  ovee_orth p := hom_ext (ovee_orthK p)
  orth_unique {X p q} h e := hom_ext (by
    have e1 : ovee p.f q.f h = X.obj.p ≫ truth X.obj.X := congrArg Karoubi.Hom.f e
    exact ovee_left_cancel h (perp_orthK p) (e1.trans (ovee_orthK p).symm))
  eq_zero_of_perp_one {X p} h := hom_ext (by
    have h' : Perp p.f (X.obj.p ≫ truth X.obj.X) := h
    have hle := comp_le_comp X.obj.p (le_comp_right' (pred_le_truth (ovee _ _ h')) S.e)
    obtain ⟨h2, e2⟩ := conj_ovee X.obj.p S.e h'
    have ht : X.obj.p ≫ (X.obj.p ≫ truth X.obj.X) ≫ S.e = X.obj.p ≫ truth X.obj.X := by
      simp only [Category.assoc, Karoubi.idem_assoc]; exact S.truth_e _ X.prop
    have hr : X.obj.p ≫ truth X.obj.X ≫ S.e = X.obj.p ≫ truth X.obj.X := S.truth_e _ X.prop
    rw [e2, hr] at hle
    have h3 : Perp p.f (X.obj.p ≫ truth X.obj.X) := by
      rw [comm p, ht] at h2; exact h2
    have : ovee (X.obj.p ≫ p.f ≫ S.e) (X.obj.p ≫ (X.obj.p ≫ truth X.obj.X) ≫ S.e) h2 =
        ovee p.f (X.obj.p ≫ truth X.obj.X) h3 := PCM.ovee_congr (comm p) ht _ _
    rw [this] at hle
    exact eq_zero_of_ovee_le h3 hle)
  perp_of_one_perp {X Y f g} h := by
    have h' : Perp (f.f ≫ Y.obj.p ≫ truth Y.obj.X) (g.f ≫ Y.obj.p ≫ truth Y.obj.X) := h
    rw [comp_p_assoc, comp_p_assoc] at h'
    exact EffectusPartialForm.perp_of_one_perp (C := C) h'
  eq_zero_of_one_zero {X Y f} h := hom_ext (by
    have h' : f.f ≫ Y.obj.p ≫ truth Y.obj.X = 0 := congrArg Karoubi.Hom.f h
    rw [comp_p_assoc] at h'
    exact EffectusPartialForm.eq_zero_of_one_zero (C := C) h')

theorem truth_f (X : KCat S) :
    Karoubi.Hom.f (truth X : Pred X) = (X.obj.p ≫ truth X.obj.X : X.obj.X ⟶ effObj C) := rfl

theorem effObj_eq : effObj (KCat S) = effI := rfl

theorem orth_f {X : KCat S} (p : Pred X) :
    Karoubi.Hom.f (orth p : Pred X) =
      X.obj.p ≫ orth (show X.obj.X ⟶ effObj C from p.f) ≫ S.e := rfl

end KCat

variable (C) in
/-- The specification of the whole Karoubi envelope: all objects, `e = id`. -/
noncomputable def splitSpec : KSpec C where
  Q := fun _ => True
  e := 𝟙 _
  e_idem := Category.id_comp _
  e_mem := trivial
  truth_e := fun _ _ => by rw [Category.comp_id]
  coprod_mem := fun _ _ _ _ => trivial
  init_mem := trivial

variable (C) in
/-- **REC 88** (short.tex:1509, Definition): a morphism `t : A → A` is
**idempotent** when `t ∘ t = t`; the **Karoubi envelope** `Split(C)` has the
idempotents `t : A → A` as objects and as morphisms `(t : A → A) → (s : B → B)`
the `f : A → B` with `s ∘ f ∘ t = f`.  This is Mathlib's `Karoubi C` (whose
morphism condition `t ≫ f ≫ s = f` is the printed one in diagrammatic order);
the effectus structure of REC 89 is put on `Split C`, the full subcategory of
`Karoubi C` on all objects, which is isomorphic to it (`splitEquivKaroubi`). -/
abbrev Split := KCat (splitSpec C)

/-- **REC 88**: a morphism is idempotent when `t ∘ t = t`. -/
def IsIdempotentHom {A : C} (t : A ⟶ A) : Prop := t ≫ t = t

variable (C) in
/-- **REC 88**: `Split C` *is* the Karoubi envelope. -/
noncomputable def splitEquivKaroubi : Split C ≌ Karoubi C where
  functor := { obj := fun X => X.obj, map := fun f => f }
  inverse := { obj := fun P => ⟨P, trivial⟩, map := fun f => f }
  unitIso := NatIso.ofComponents (fun X => Iso.refl _) (fun _ => by simp)
  counitIso := NatIso.ofComponents (fun P => Iso.refl _) (fun _ => by simp)

variable (C) in
/-- **REC 88** (short.tex:1513, the sentence after the definition): `C` embeds
fully and faithfully into `Split(C)` via `A ↦ id_A`, `f ↦ f`.  Thin: Mathlib's
`toKaroubi`. -/
def rec88_embedding : (toKaroubi C).FullyFaithful := fullyFaithfulToKaroubi C

/-- **REC 89** (short.tex:1516, Proposition), main clause: `Split(C)` is again an
effectus in partial form — with effect object `id_I`, truth `1_A ∘ t`, falsity
`0`, orthosupplement `p^⊥ ∘ t`, and coproduct `t + s` (the printed sketch). -/
theorem rec89_effectus : Nonempty (EffectusPartialStructure (Split C)) :=
  ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩⟩

/-- **REC 89** (short.tex:1516, Proposition), first bullet: if `C` is separated
by predicates, so is `Split(C)`.  The paper's proof: for a predicate `p` on `B`,
`p ∘ s` is a predicate on `(B, s)` and `p ∘ f = (p ∘ s) ∘ f`. -/
theorem rec89_predicates (h : SeparatingPredicates C) : SeparatingPredicates (Split C) := by
  intro X Y f g hfg
  refine KCat.hom_ext (h _ _ fun p => ?_)
  have := congrArg Karoubi.Hom.f (hfg (KCat.homMk (Y.obj.p ≫ p) (by
    show Y.obj.p ≫ (Y.obj.p ≫ p) ≫ 𝟙 _ = Y.obj.p ≫ p
    simp)))
  simpa [KCat.comp_p_assoc] using this

/-- **REC 89** (short.tex:1516, Proposition), second bullet, **is false as
printed**: if `C` has a non-trivial idempotent scalar `s` (`s² = s`,
`s ∉ {0, 1}`), then `Split(C)` is *never* separated by states, whether or not
`C` is.  The object `(I, s)` has no states at all — a state `ω` would satisfy
`ω = s ∘ ω` and `1 = s ∘ ω`, whence `s = 1` — while it has the two distinct
endomorphisms `id_{(I,s)} = s` and `0`.  (The printed proof "works
analogously" to the predicate case; the analogue of `p ∘ s` is `t ∘ ω`, which is
a *sub*state of `(A, t)` and need not be a state.)  `rec89_states_false_as_printed`
exhibits an effectus separated by states with such a scalar. -/
theorem rec89_states_not_preserved {s : Scal C} (hs : s ≫ s = s) (h0 : s ≠ 0)
    (h1 : s ≠ 𝟙 _) : ¬ SeparatingStates (Split C) := by
  intro hsep
  let P : Split C := ⟨⟨effObj C, s, hs⟩, trivial⟩
  have hno : ∀ ω : Stat P, False := by
    rintro ⟨ω, hω⟩
    have e1 : ω.f ≫ (s ≫ truth (effObj C)) = 𝟙 _ ≫ truth (effObj C) :=
      congrArg Karoubi.Hom.f hω
    rw [truth_effObj_eq_id, Category.comp_id, Category.comp_id] at e1
    have e2 : ω.f ≫ s = ω.f := KCat.comp_p ω
    have hω1 : ω.f = 𝟙 _ := e2.symm.trans e1
    apply h1
    calc s = ω.f ≫ s := by rw [hω1, Category.id_comp]
      _ = 𝟙 _ := e1
  have := hsep (𝟙 P) 0 (fun ω => (hno ω).elim)
  exact h0 (congrArg Karoubi.Hom.f this)

end KCatSection

/-! ## The splitting theorem (the argument of REC 90) -/

section Splitting

variable {D : Type u} [Category.{v} D] [HasFiniteCoproducts D] [∀ X Y : D, PCM (X ⟶ Y)]
  [FinPAC D] [EffectusPartialForm D]

variable (D) in
/-- A family of idempotents `e_A : A → A`, natural in `A` (`e_B ∘ f = f ∘ e_A`):
the maps `s · id_A` of REC 90–91 and `asrt_{s∘1}` of REC 92. -/
structure CentralIdem where
  e : ∀ A : D, A ⟶ A
  idem : ∀ A : D, e A ≫ e A = e A
  nat : ∀ {A B : D} (f : A ⟶ B), e A ≫ f = f ≫ e B

namespace CentralIdem

variable (ε : CentralIdem D)

theorem idem_assoc {A : D} {Z : D} (h : A ⟶ Z) : ε.e A ≫ ε.e A ≫ h = ε.e A ≫ h := by
  rw [← Category.assoc, ε.idem]

theorem nat_assoc {A B Z : D} (f : A ⟶ B) (h : B ⟶ Z) : ε.e A ≫ f ≫ h = f ≫ ε.e B ≫ h := by
  rw [← Category.assoc, ε.nat, Category.assoc]

theorem truth_e (A : D) : ε.e A ≫ truth A ≫ ε.e (effObj D) = ε.e A ≫ truth A := by
  rw [← Category.assoc, ε.nat, Category.assoc, ε.idem]

/-- The part `D_e`: the objects `(A, e_A)` of the Karoubi envelope. -/
noncomputable def spec : KSpec D where
  Q := fun P => P.p = ε.e P.X
  e := ε.e (effObj D)
  e_idem := ε.idem _
  e_mem := rfl
  truth_e := fun P hP => by rw [hP]; exact ε.truth_e P.X
  coprod_mem := fun P P' hP hP' => by
    show coprod.map P.p P'.p = ε.e (P.X ⨿ P'.X)
    rw [hP, hP']
    apply coprod.hom_ext
    · rw [coprod.inl_map, ε.nat]
    · rw [coprod.inr_map, ε.nat]
  init_mem := by
    show 𝟙 (⊥_ D) = ε.e (⊥_ D)
    exact initial.hom_ext _ _

/-- The category `C_s` of REC 90–92: same objects as `D` (as `(A, e_A)`),
morphisms the `f : A → B` with `e_B ∘ f ∘ e_A = f`, identity `e_A`. -/
abbrev Part := KCat ε.spec

theorem prop (P : ε.Part) : P.obj.p = ε.e P.obj.X := P.prop

theorem comp_e {P R : ε.Part} (φ : P ⟶ R) : φ.f ≫ ε.e R.obj.X = φ.f := by
  rw [← ε.prop R]; exact KCat.comp_p φ

theorem e_comp {P R : ε.Part} (φ : P ⟶ R) : ε.e P.obj.X ≫ φ.f = φ.f := by
  rw [← ε.prop P]; exact KCat.p_comp φ

/-- The object `(A, e_A)` of the part. -/
def toPart (A : D) : ε.Part := ⟨⟨A, ε.e A, ε.idem A⟩, rfl⟩

theorem hom_comm {A B : D} (f : A ⟶ B) : ε.e A ≫ (ε.e A ≫ f) ≫ ε.e B = ε.e A ≫ f := by
  simp only [Category.assoc]
  rw [← ε.nat f, ε.idem_assoc, ε.idem_assoc]

/-- The part is non-trivial (`1 ≠ 0` among its scalars) when `e_I ≠ 0`. -/
theorem part_nontrivial (h : ε.e (effObj D) ≠ 0) : (1 : Scal ε.Part) ≠ 0 := by
  intro h1
  apply h
  have e1 : ε.e (effObj D) ≫ truth (effObj D) = 0 := congrArg Karoubi.Hom.f h1
  rwa [truth_effObj_eq_id, Category.comp_id] at e1

end CentralIdem

variable (D) in
/-- The data of the proof of REC 90: a central idempotent family `e` and a
complementary one `e'` (`e_A ∘ e'_A = 0`, `e_A ⊻ e'_A = id_A`), with chosen
splittings `ξ_A : A → A_e`, `π_A : A_e → A` (`π ∘ ξ = e_A`, `ξ ∘ π = id`) and
likewise for `e'`. -/
structure CentralSplitting where
  ε : CentralIdem D
  ε' : CentralIdem D
  e_e' : ∀ A : D, ε.e A ≫ ε'.e A = 0
  perp : ∀ A : D, Perp (ε.e A) (ε'.e A)
  sum : ∀ A : D, ovee (ε.e A) (ε'.e A) (perp A) = 𝟙 A
  obj : D → D
  ξ : ∀ A : D, A ⟶ obj A
  π : ∀ A : D, obj A ⟶ A
  ξπ : ∀ A : D, ξ A ≫ π A = ε.e A
  πξ : ∀ A : D, π A ≫ ξ A = 𝟙 (obj A)
  obj' : D → D
  ξ' : ∀ A : D, A ⟶ obj' A
  π' : ∀ A : D, obj' A ⟶ A
  ξπ' : ∀ A : D, ξ' A ≫ π' A = ε'.e A
  πξ' : ∀ A : D, π' A ≫ ξ' A = 𝟙 (obj' A)

namespace CentralSplitting

variable (σ : CentralSplitting D)

theorem e'_e (A : D) : σ.ε'.e A ≫ σ.ε.e A = 0 := by
  rw [σ.ε'.nat (σ.ε.e A)]; exact σ.e_e' A

theorem π_e (A : D) : σ.π A ≫ σ.ε.e A = σ.π A := by
  rw [← σ.ξπ, ← Category.assoc, σ.πξ, Category.id_comp]

theorem π'_e' (A : D) : σ.π' A ≫ σ.ε'.e A = σ.π' A := by
  rw [← σ.ξπ', ← Category.assoc, σ.πξ', Category.id_comp]

theorem e_ξ (A : D) : σ.ε.e A ≫ σ.ξ A = σ.ξ A := by
  rw [← σ.ξπ, Category.assoc, σ.πξ, Category.comp_id]

theorem e'_ξ' (A : D) : σ.ε'.e A ≫ σ.ξ' A = σ.ξ' A := by
  rw [← σ.ξπ', Category.assoc, σ.πξ', Category.comp_id]

theorem ξπ_assoc (A : D) {Z : D} (h : A ⟶ Z) : σ.ξ A ≫ σ.π A ≫ h = σ.ε.e A ≫ h := by
  rw [← Category.assoc, σ.ξπ]

theorem ξπ'_assoc (A : D) {Z : D} (h : A ⟶ Z) : σ.ξ' A ≫ σ.π' A ≫ h = σ.ε'.e A ≫ h := by
  rw [← Category.assoc, σ.ξπ']

theorem π_e_assoc (A : D) {Z : D} (h : A ⟶ Z) : σ.π A ≫ σ.ε.e A ≫ h = σ.π A ≫ h := by
  rw [← Category.assoc, σ.π_e]

theorem π'_e'_assoc (A : D) {Z : D} (h : A ⟶ Z) : σ.π' A ≫ σ.ε'.e A ≫ h = σ.π' A ≫ h := by
  rw [← Category.assoc, σ.π'_e']

/-- `e` is the identity on `A_e` (the paper's `s · id_{A_s} = id_{A_s}`). -/
theorem e_obj (A : D) : σ.ε.e (σ.obj A) = 𝟙 _ := by
  calc σ.ε.e (σ.obj A) = σ.ε.e (σ.obj A) ≫ σ.π A ≫ σ.ξ A := by rw [σ.πξ, Category.comp_id]
    _ = σ.π A ≫ σ.ε.e A ≫ σ.ξ A := by rw [σ.ε.nat_assoc]
    _ = 𝟙 _ := by rw [σ.e_ξ, σ.πξ]

theorem e'_obj' (A : D) : σ.ε'.e (σ.obj' A) = 𝟙 _ := by
  calc σ.ε'.e (σ.obj' A) = σ.ε'.e (σ.obj' A) ≫ σ.π' A ≫ σ.ξ' A := by
        rw [σ.πξ', Category.comp_id]
    _ = σ.π' A ≫ σ.ε'.e A ≫ σ.ξ' A := by rw [σ.ε'.nat_assoc]
    _ = 𝟙 _ := by rw [σ.e'_ξ', σ.πξ']

/-- `e` vanishes on `A_{e'}` (the paper's `s^⊥ · id_{A_s} = 0`). -/
theorem e_obj' (A : D) : σ.ε.e (σ.obj' A) = 0 := by
  calc σ.ε.e (σ.obj' A) = σ.ε.e (σ.obj' A) ≫ σ.π' A ≫ σ.ξ' A := by
        rw [σ.πξ', Category.comp_id]
    _ = σ.π' A ≫ σ.ε.e A ≫ σ.ξ' A := by rw [σ.ε.nat_assoc]
    _ = σ.π' A ≫ σ.ε'.e A ≫ σ.ε.e A ≫ σ.ξ' A := by rw [σ.π'_e'_assoc]
    _ = 0 := by rw [← Category.assoc (σ.ε'.e A), σ.e'_e, FinPAC.zero_comp, FinPAC.comp_zero]

theorem e'_obj (A : D) : σ.ε'.e (σ.obj A) = 0 := by
  calc σ.ε'.e (σ.obj A) = σ.ε'.e (σ.obj A) ≫ σ.π A ≫ σ.ξ A := by
        rw [σ.πξ, Category.comp_id]
    _ = σ.π A ≫ σ.ε'.e A ≫ σ.ξ A := by rw [σ.ε'.nat_assoc]
    _ = σ.π A ≫ σ.ε.e A ≫ σ.ε'.e A ≫ σ.ξ A := by rw [σ.π_e_assoc]
    _ = 0 := by rw [← Category.assoc (σ.ε.e A), σ.e_e', FinPAC.zero_comp, FinPAC.comp_zero]

theorem π_ξ' (A : D) : σ.π A ≫ σ.ξ' A = 0 := by
  calc σ.π A ≫ σ.ξ' A = σ.π A ≫ σ.ε.e A ≫ σ.ε'.e A ≫ σ.ξ' A := by
        rw [σ.e'_ξ', σ.π_e_assoc]
    _ = 0 := by rw [← Category.assoc (σ.ε.e A), σ.e_e', FinPAC.zero_comp, FinPAC.comp_zero]

theorem π'_ξ (A : D) : σ.π' A ≫ σ.ξ A = 0 := by
  calc σ.π' A ≫ σ.ξ A = σ.π' A ≫ σ.ε'.e A ≫ σ.ε.e A ≫ σ.ξ A := by
        rw [σ.e_ξ, σ.π'_e'_assoc]
    _ = 0 := by rw [← Category.assoc (σ.ε'.e A), σ.e'_e, FinPAC.zero_comp, FinPAC.comp_zero]

/-- The retraction `π` is total. -/
theorem π_total (A : D) : σ.π A ≫ truth A = truth (σ.obj A) := by
  refine eabasics_le_antisymm (pred_le_truth _) ?_
  have := comp_le_comp (σ.π A) (pred_le_truth (σ.ξ A ≫ truth (σ.obj A)))
  rwa [← Category.assoc, σ.πξ, Category.id_comp] at this

theorem π'_total (A : D) : σ.π' A ≫ truth A = truth (σ.obj' A) := by
  refine eabasics_le_antisymm (pred_le_truth _) ?_
  have := comp_le_comp (σ.π' A) (pred_le_truth (σ.ξ' A ≫ truth (σ.obj' A)))
  rwa [← Category.assoc, σ.πξ', Category.id_comp] at this

theorem ξ_truth (A : D) : σ.ξ A ≫ truth (σ.obj A) = σ.ε.e A ≫ truth A := by
  rw [← σ.π_total, ← Category.assoc, σ.ξπ]

theorem ξ'_truth (A : D) : σ.ξ' A ≫ truth (σ.obj' A) = σ.ε'.e A ≫ truth A := by
  rw [← σ.π'_total, ← Category.assoc, σ.ξπ']

/-- The sum `⟨ξ, ξ'⟩ = κ₁ ∘ ξ ⊻ κ₂ ∘ ξ'` is defined (thesis B 181VII). -/
theorem perp_split (A : D) : Perp (σ.ξ A ≫ coprod.inl) (σ.ξ' A ≫ coprod.inr) := by
  apply EffectusPartialForm.perp_of_one_perp (C := D)
  show Perp ((σ.ξ A ≫ coprod.inl) ≫ truth _) ((σ.ξ' A ≫ coprod.inr) ≫ truth _)
  have h1 : (coprod.inl : σ.obj A ⟶ σ.obj A ⨿ σ.obj' A) ≫ truth _ = truth _ :=
    coproj_total_inl _ _
  have h2 : (coprod.inr : σ.obj' A ⟶ σ.obj A ⨿ σ.obj' A) ≫ truth _ = truth _ :=
    coproj_total_inr _ _
  rw [Category.assoc, Category.assoc, h1, h2, σ.ξ_truth, σ.ξ'_truth]
  exact (FinPAC.comp_ovee (σ.perp A) (truth A)).1

/-- `α = [π, π'] : A_e + A_{e'} → A` is an isomorphism with inverse `⟨ξ, ξ'⟩`. -/
noncomputable def splitIso (A : D) : σ.obj A ⨿ σ.obj' A ≅ A where
  hom := coprod.desc (σ.π A) (σ.π' A)
  inv := ovee (σ.ξ A ≫ coprod.inl) (σ.ξ' A ≫ coprod.inr) (σ.perp_split A)
  hom_inv_id := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, Category.comp_id]
      obtain ⟨h', e⟩ := FinPAC.ovee_comp (σ.perp_split A) (σ.π A)
      rw [e]
      have e1 : σ.π A ≫ σ.ξ A ≫ (coprod.inl : σ.obj A ⟶ σ.obj A ⨿ σ.obj' A) = coprod.inl := by
        rw [← Category.assoc, σ.πξ, Category.id_comp]
      have e2 : σ.π A ≫ σ.ξ' A ≫ (coprod.inr : σ.obj' A ⟶ σ.obj A ⨿ σ.obj' A) = 0 := by
        rw [← Category.assoc, σ.π_ξ', FinPAC.zero_comp]
      rw [PCM.ovee_congr e1 e2 h' (PCM.perp_zero _), PCM.ovee_zero]
    · rw [coprod.inr_desc_assoc, Category.comp_id]
      obtain ⟨h', e⟩ := FinPAC.ovee_comp (σ.perp_split A) (σ.π' A)
      rw [e]
      have e1 : σ.π' A ≫ σ.ξ A ≫ (coprod.inl : σ.obj A ⟶ σ.obj A ⨿ σ.obj' A) = 0 := by
        rw [← Category.assoc, σ.π'_ξ, FinPAC.zero_comp]
      have e2 : σ.π' A ≫ σ.ξ' A ≫ (coprod.inr : σ.obj' A ⟶ σ.obj A ⨿ σ.obj' A) = coprod.inr := by
        rw [← Category.assoc, σ.πξ', Category.id_comp]
      rw [PCM.ovee_congr e1 e2 h' (PCM.zero_perp _), PCM.zero_ovee]
  inv_hom_id := by
    obtain ⟨h', e⟩ := FinPAC.comp_ovee (σ.perp_split A) (coprod.desc (σ.π A) (σ.π' A))
    rw [e]
    have e1 : (σ.ξ A ≫ coprod.inl) ≫ coprod.desc (σ.π A) (σ.π' A) = σ.ε.e A := by
      rw [Category.assoc, coprod.inl_desc, σ.ξπ]
    have e2 : (σ.ξ' A ≫ coprod.inr) ≫ coprod.desc (σ.π A) (σ.π' A) = σ.ε'.e A := by
      rw [Category.assoc, coprod.inr_desc, σ.ξπ']
    rw [PCM.ovee_congr e1 e2 h' (σ.perp A), σ.sum]

/-- The functor `G : D → D_e × D_{e'}`, `A ↦ ((A, e_A), (A, e'_A))`,
`f ↦ (e ∘ f, e' ∘ f)`. -/
noncomputable def partFunctor : D ⥤ σ.ε.Part × σ.ε'.Part where
  obj A := (σ.ε.toPart A, σ.ε'.toPart A)
  map {A B} f := (KCat.homMk (σ.ε.e A ≫ f) (σ.ε.hom_comm f),
    KCat.homMk (σ.ε'.e A ≫ f) (σ.ε'.hom_comm f))
  map_id A := Prod.hom_ext (KCat.hom_ext (Category.comp_id _))
    (KCat.hom_ext (Category.comp_id _))
  map_comp {A B E} f g := Prod.hom_ext
    (KCat.hom_ext (by
      show σ.ε.e A ≫ f ≫ g = (σ.ε.e A ≫ f) ≫ (σ.ε.e B ≫ g)
      rw [Category.assoc, ← σ.ε.nat_assoc, σ.ε.idem_assoc]))
    (KCat.hom_ext (by
      show σ.ε'.e A ≫ f ≫ g = (σ.ε'.e A ≫ f) ≫ (σ.ε'.e B ≫ g)
      rw [Category.assoc, ← σ.ε'.nat_assoc, σ.ε'.idem_assoc]))

theorem joinComp {A B E : D} (f : A ⟶ B) (g : B ⟶ E) (hf : f ≫ σ.ε.e B = f) :
    σ.π A ≫ (f ≫ g) ≫ σ.ξ E = (σ.π A ≫ f ≫ σ.ξ B) ≫ (σ.π B ≫ g ≫ σ.ξ E) := by
  simp only [Category.assoc]
  rw [σ.ξπ_assoc, ← Category.assoc f (σ.ε.e B), hf]

theorem joinComp' {A B E : D} (f : A ⟶ B) (g : B ⟶ E) (hf : f ≫ σ.ε'.e B = f) :
    σ.π' A ≫ (f ≫ g) ≫ σ.ξ' E = (σ.π' A ≫ f ≫ σ.ξ' B) ≫ (σ.π' B ≫ g ≫ σ.ξ' E) := by
  simp only [Category.assoc]
  rw [σ.ξπ'_assoc, ← Category.assoc f (σ.ε'.e B), hf]

/-- The functor `F : D_e × D_{e'} → D`, `(A, B) ↦ A_e + B_{e'}`,
`(f, g) ↦ f_e + g_{e'}` with `f_e = ξ ∘ f ∘ π`. -/
noncomputable def joinFunctor : σ.ε.Part × σ.ε'.Part ⥤ D where
  obj Q := σ.obj Q.1.obj.X ⨿ σ.obj' Q.2.obj.X
  map {Q R} φ := coprod.map (σ.π _ ≫ φ.1.f ≫ σ.ξ _) (σ.π' _ ≫ φ.2.f ≫ σ.ξ' _)
  map_id Q := by
    show coprod.map (σ.π _ ≫ Q.1.obj.p ≫ σ.ξ _) (σ.π' _ ≫ Q.2.obj.p ≫ σ.ξ' _) = 𝟙 _
    rw [σ.ε.prop Q.1, σ.ε'.prop Q.2, σ.e_ξ, σ.e'_ξ', σ.πξ, σ.πξ', coprod.map_id_id]
  map_comp {Q R T} φ ψ := by
    show coprod.map (σ.π _ ≫ (φ.1.f ≫ ψ.1.f) ≫ σ.ξ _) (σ.π' _ ≫ (φ.2.f ≫ ψ.2.f) ≫ σ.ξ' _) =
      coprod.map (σ.π _ ≫ φ.1.f ≫ σ.ξ _) (σ.π' _ ≫ φ.2.f ≫ σ.ξ' _) ≫
        coprod.map (σ.π _ ≫ ψ.1.f ≫ σ.ξ _) (σ.π' _ ≫ ψ.2.f ≫ σ.ξ' _)
    rw [coprod.map_map, σ.joinComp _ _ (σ.ε.comp_e φ.1), σ.joinComp' _ _ (σ.ε'.comp_e φ.2)]

/-- The natural isomorphism `α = [π, π'] : F G ⇒ id`. -/
noncomputable def unitIso' : σ.partFunctor ⋙ σ.joinFunctor ≅ 𝟭 D :=
  NatIso.ofComponents (fun A => σ.splitIso A) (fun {A B} f => by
    show coprod.map (σ.π A ≫ (σ.ε.e A ≫ f) ≫ σ.ξ B) (σ.π' A ≫ (σ.ε'.e A ≫ f) ≫ σ.ξ' B) ≫
        coprod.desc (σ.π B) (σ.π' B) = coprod.desc (σ.π A) (σ.π' A) ≫ f
    apply coprod.hom_ext
    · rw [coprod.inl_map_assoc, coprod.inl_desc, coprod.inl_desc_assoc]
      simp only [Category.assoc]
      rw [σ.ξπ, ← σ.ε.nat f, σ.ε.idem_assoc, σ.π_e_assoc]
    · rw [coprod.inr_map_assoc, coprod.inr_desc, coprod.inr_desc_assoc]
      simp only [Category.assoc]
      rw [σ.ξπ', ← σ.ε'.nat f, σ.ε'.idem_assoc, σ.π'_e'_assoc])

section Counit

variable (Q : σ.ε.Part × σ.ε'.Part)

theorem inl_e (A B : D) :
    (coprod.inl : σ.obj A ⟶ σ.obj A ⨿ σ.obj' B) ≫ σ.ε.e _ = coprod.inl := by
  rw [← σ.ε.nat, σ.e_obj, Category.id_comp]

theorem inr_e (A B : D) :
    (coprod.inr : σ.obj' B ⟶ σ.obj A ⨿ σ.obj' B) ≫ σ.ε.e _ = 0 := by
  rw [← σ.ε.nat, σ.e_obj', FinPAC.zero_comp]

theorem inl_e' (A B : D) :
    (coprod.inl : σ.obj A ⟶ σ.obj A ⨿ σ.obj' B) ≫ σ.ε'.e _ = 0 := by
  rw [← σ.ε'.nat, σ.e'_obj, FinPAC.zero_comp]

theorem inr_e' (A B : D) :
    (coprod.inr : σ.obj' B ⟶ σ.obj A ⨿ σ.obj' B) ≫ σ.ε'.e _ = coprod.inr := by
  rw [← σ.ε'.nat, σ.e'_obj', Category.id_comp]

theorem descπ_e (A B : D) :
    coprod.desc (σ.π A) (0 : σ.obj' B ⟶ A) ≫ σ.ε.e A = coprod.desc (σ.π A) 0 := by
  rw [coprod.desc_comp, σ.π_e, FinPAC.zero_comp]

theorem descπ'_e' (A B : D) :
    coprod.desc (0 : σ.obj A ⟶ B) (σ.π' B) ≫ σ.ε'.e B = coprod.desc 0 (σ.π' B) := by
  rw [coprod.desc_comp, σ.π'_e', FinPAC.zero_comp]

/-- The first component of `β : G F ⇒ id`: `(A_e + B_{e'}, e) ≅ (A, e_A)` in
`D_e`, via `[π, 0]` and `κ₁ ∘ ξ` (the paper's `π_s ∘ ▷₁ ∘ π_s`). -/
noncomputable def leftIso :
    σ.ε.toPart (σ.obj Q.1.obj.X ⨿ σ.obj' Q.2.obj.X) ≅ Q.1 where
  hom := KCat.homMk (coprod.desc (σ.π Q.1.obj.X) 0) (by
    show σ.ε.e _ ≫ coprod.desc (σ.π Q.1.obj.X) 0 ≫ Q.1.obj.p = coprod.desc (σ.π Q.1.obj.X) 0
    rw [σ.ε.prop Q.1, σ.descπ_e, σ.ε.nat, σ.descπ_e])
  inv := KCat.homMk (σ.ξ Q.1.obj.X ≫ coprod.inl) (by
    show Q.1.obj.p ≫ (σ.ξ Q.1.obj.X ≫ coprod.inl) ≫ σ.ε.e _ = σ.ξ Q.1.obj.X ≫ coprod.inl
    rw [σ.ε.prop Q.1, Category.assoc, σ.inl_e, ← Category.assoc, σ.e_ξ])
  hom_inv_id := KCat.hom_ext (by
    show coprod.desc (σ.π Q.1.obj.X) 0 ≫ σ.ξ Q.1.obj.X ≫ coprod.inl = σ.ε.e _
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, ← Category.assoc, σ.πξ, Category.id_comp, σ.inl_e]
    · rw [coprod.inr_desc_assoc, FinPAC.zero_comp, σ.inr_e])
  inv_hom_id := KCat.hom_ext (by
    show (σ.ξ Q.1.obj.X ≫ coprod.inl) ≫ coprod.desc (σ.π Q.1.obj.X) 0 = Q.1.obj.p
    rw [Category.assoc, coprod.inl_desc, σ.ξπ, σ.ε.prop Q.1])

/-- The second component of `β`. -/
noncomputable def rightIso :
    σ.ε'.toPart (σ.obj Q.1.obj.X ⨿ σ.obj' Q.2.obj.X) ≅ Q.2 where
  hom := KCat.homMk (coprod.desc 0 (σ.π' Q.2.obj.X)) (by
    show σ.ε'.e _ ≫ coprod.desc 0 (σ.π' Q.2.obj.X) ≫ Q.2.obj.p = coprod.desc 0 (σ.π' Q.2.obj.X)
    rw [σ.ε'.prop Q.2, σ.descπ'_e', σ.ε'.nat, σ.descπ'_e'])
  inv := KCat.homMk (σ.ξ' Q.2.obj.X ≫ coprod.inr) (by
    show Q.2.obj.p ≫ (σ.ξ' Q.2.obj.X ≫ coprod.inr) ≫ σ.ε'.e _ = σ.ξ' Q.2.obj.X ≫ coprod.inr
    rw [σ.ε'.prop Q.2, Category.assoc, σ.inr_e', ← Category.assoc, σ.e'_ξ'])
  hom_inv_id := KCat.hom_ext (by
    show coprod.desc 0 (σ.π' Q.2.obj.X) ≫ σ.ξ' Q.2.obj.X ≫ coprod.inr = σ.ε'.e _
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, FinPAC.zero_comp, σ.inl_e']
    · rw [coprod.inr_desc_assoc, ← Category.assoc, σ.πξ', Category.id_comp, σ.inr_e'])
  inv_hom_id := KCat.hom_ext (by
    show (σ.ξ' Q.2.obj.X ≫ coprod.inr) ≫ coprod.desc 0 (σ.π' Q.2.obj.X) = Q.2.obj.p
    rw [Category.assoc, coprod.inr_desc, σ.ξπ', σ.ε'.prop Q.2])

end Counit

/-- The natural isomorphism `β : G F ⇒ id`. -/
noncomputable def counitIso' : σ.joinFunctor ⋙ σ.partFunctor ≅ 𝟭 (σ.ε.Part × σ.ε'.Part) :=
  NatIso.ofComponents (fun Q => Iso.prod (σ.leftIso Q) (σ.rightIso Q)) (fun {Q R} φ => by
    refine Prod.hom_ext (KCat.hom_ext ?_) (KCat.hom_ext ?_)
    · show (σ.ε.e _ ≫ coprod.map (σ.π _ ≫ φ.1.f ≫ σ.ξ _) (σ.π' _ ≫ φ.2.f ≫ σ.ξ' _)) ≫
          coprod.desc (σ.π R.1.obj.X) 0 = coprod.desc (σ.π Q.1.obj.X) 0 ≫ φ.1.f
      have e1 : coprod.map (σ.π _ ≫ φ.1.f ≫ σ.ξ _) (σ.π' _ ≫ φ.2.f ≫ σ.ξ' _) ≫
          coprod.desc (σ.π R.1.obj.X) (0 : σ.obj' R.2.obj.X ⟶ R.1.obj.X) =
          coprod.desc (σ.π Q.1.obj.X) 0 ≫ φ.1.f := by
        rw [coprod.map_desc, coprod.desc_comp, FinPAC.comp_zero, FinPAC.zero_comp]
        congr 1
        simp only [Category.assoc]
        rw [σ.ξπ, σ.ε.comp_e]
      rw [Category.assoc, e1, σ.ε.nat, Category.assoc, σ.ε.comp_e]
    · show (σ.ε'.e _ ≫ coprod.map (σ.π _ ≫ φ.1.f ≫ σ.ξ _) (σ.π' _ ≫ φ.2.f ≫ σ.ξ' _)) ≫
          coprod.desc 0 (σ.π' R.2.obj.X) = coprod.desc 0 (σ.π' Q.2.obj.X) ≫ φ.2.f
      have e1 : coprod.map (σ.π _ ≫ φ.1.f ≫ σ.ξ _) (σ.π' _ ≫ φ.2.f ≫ σ.ξ' _) ≫
          coprod.desc (0 : σ.obj R.1.obj.X ⟶ R.2.obj.X) (σ.π' R.2.obj.X) =
          coprod.desc 0 (σ.π' Q.2.obj.X) ≫ φ.2.f := by
        rw [coprod.map_desc, coprod.desc_comp, FinPAC.comp_zero, FinPAC.zero_comp]
        congr 1
        simp only [Category.assoc]
        rw [σ.ξπ', σ.ε'.comp_e]
      rw [Category.assoc, e1, σ.ε'.nat, Category.assoc, σ.ε'.comp_e])

/-- **The splitting theorem** (the proof of REC 90): `D ≌ D_e × D_{e'}`, with
`G(A) = ((A, e_A), (A, e'_A))` and `F(A, B) = A_e + B_{e'}`. -/
noncomputable def equivalence : D ≌ σ.ε.Part × σ.ε'.Part :=
  CategoryTheory.Equivalence.mk σ.partFunctor σ.joinFunctor σ.unitIso'.symm σ.counitIso'

end CentralSplitting

end Splitting


/-! ## Scalars and the unit -/

section ScalarFacts

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

theorem scal_one_eq : (1 : Scal C) = 𝟙 (effObj C) := truth_effObj_eq_id

/-- `s ⊻ s^⊥ = id_I`. -/
theorem scal_ovee_orth (s : Scal C) :
    ovee s (orth s) (EffectAlgebra.perp_orth s) = 𝟙 (effObj C) :=
  (EffectAlgebra.ovee_orth s).trans scal_one_eq

theorem orth_ne_zero_of_ne_one {s : Scal C} (h1 : s ≠ 𝟙 _) : orth s ≠ 0 := by
  intro h
  apply h1
  rw [← eabasics_orth_orth s, h, eabasics_orth_zero, scal_one_eq]

/-- In an effect monoid, `x ≼ t` for an idempotent `t` gives `x · t = x`. -/
theorem mul_idem_of_le {M : Type w} [EffectMonoid M] {t x : M} (ht : t * t = t) (h : x ≼ t) :
    x * t = x := by
  have hz : x * orth t = 0 := by
    have := emon_mul_mono_left h (orth t)
    rw [idem_mul_orth ht] at this
    exact eq_zero_of_le_zero this
  obtain ⟨h', e⟩ := emon_mul_ovee x (EffectAlgebra.perp_orth t)
  rw [EffectAlgebra.ovee_orth, EffectMonoid.mul_one] at e
  conv_rhs => rw [e]
  rw [PCM.ovee_congr rfl hz h' (PCM.perp_zero _), PCM.ovee_zero]

end ScalarFacts

/-! ## REC 90: monoidal effectuses, in the Karoubi envelope -/

section Monoidal

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]

theorem smul_comp (s : Scal C) {A B E : C} (f : A ⟶ B) (g : B ⟶ E) :
    smulHom s f ≫ g = smulHom s (f ≫ g) := (rec29_comp s f g).1

theorem comp_smul (s : Scal C) {A B E : C} (f : A ⟶ B) (g : B ⟶ E) :
    f ≫ smulHom s g = smulHom s (f ≫ g) := (rec29_comp s f g).2.symm

theorem smul_smul (s t : Scal C) {A B : C} (f : A ⟶ B) :
    smulHom s (smulHom t f) = smulHom (t ≫ s) f :=
  (rec29_scalar_action s t f).2.1.trans (rec29_scalar_action s t f).2.2

theorem smul_comp_smul (s t : Scal C) {A B E : C} (f : A ⟶ B) (g : B ⟶ E) :
    smulHom s f ≫ smulHom t g = smulHom (t ≫ s) (f ≫ g) := by
  rw [smul_comp, comp_smul, smul_smul]

theorem smul_zero_scalar {A B : C} (f : A ⟶ B) : smulHom (0 : Scal C) f = 0 := by
  simp only [smulHom, unitScalar, FinPAC.zero_comp, FinPAC.comp_zero,
    MonoidalEffectus.zero_tensor]

theorem smul_one {A B : C} (f : A ⟶ B) : smulHom (𝟙 (effObj C)) f = f := by
  simp [smulHom, unitScalar]

/-- `s ⊻ s^⊥` acts as the identity: `f = s · f ⊻ s^⊥ · f`. -/
theorem smul_split (s : Scal C) {A B : C} (f : A ⟶ B) :
    ∃ h : Perp (smulHom s f) (smulHom (orth s) f),
      ovee (smulHom s f) (smulHom (orth s) f) h = f := by
  obtain ⟨h', e⟩ := rec29_ovee_left (EffectAlgebra.perp_orth s) f
  refine ⟨h', ?_⟩
  rw [← e, scal_ovee_orth, smul_one]

/-- For an idempotent scalar `t`, the family `t · t_P` on `Split(C)`, where
`t_P = P` is the identity of `P = (A, t_P)`. -/
noncomputable def splitScalarIdem (t : Scal C) (ht : t ≫ t = t) : CentralIdem (Split C) where
  e P := KCat.homMk (smulHom t P.obj.p) (by
    rw [smul_comp, P.obj.idem, comp_smul, P.obj.idem])
  idem P := KCat.hom_ext (by
    show smulHom t P.obj.p ≫ smulHom t P.obj.p = smulHom t P.obj.p
    rw [smul_comp_smul, ht, P.obj.idem])
  nat {P Q} f := KCat.hom_ext (by
    show smulHom t P.obj.p ≫ f.f = f.f ≫ smulHom t Q.obj.p
    rw [smul_comp, comp_smul, KCat.p_comp, KCat.comp_p])

theorem smulP_idem (t : Scal C) (ht : t ≫ t = t) (P : Split C) :
    smulHom t P.obj.p ≫ smulHom t P.obj.p = smulHom t P.obj.p := by
  rw [smul_comp_smul, ht, P.obj.idem]

/-- The object `P_t = (A, t · t_P)` splitting `t · id_P` in `Split(C)`. -/
noncomputable def splitScalarObj (t : Scal C) (ht : t ≫ t = t) (P : Split C) : Split C :=
  ⟨⟨P.obj.X, smulHom t P.obj.p, smulP_idem t ht P⟩, trivial⟩

/-- The splitting of `s · id` and `s^⊥ · id` in `Split(C)` (every idempotent
splits there). -/
noncomputable def splitSplitting {s : Scal C} (hs : s ≫ s = s) : CentralSplitting (Split C) where
  ε := splitScalarIdem s hs
  ε' := splitScalarIdem (orth s) (orth_idem hs)
  e_e' P := KCat.hom_ext (by
    show smulHom s P.obj.p ≫ smulHom (orth s) P.obj.p = 0
    rw [smul_comp_smul]
    have : orth s ≫ s = 0 := idem_mul_orth hs
    rw [this, smul_zero_scalar])
  perp P := (smul_split s P.obj.p).1
  sum P := KCat.hom_ext (smul_split s P.obj.p).2
  obj P := splitScalarObj s hs P
  ξ P := KCat.homMk (smulHom s P.obj.p) (by
    show P.obj.p ≫ smulHom s P.obj.p ≫ smulHom s P.obj.p = smulHom s P.obj.p
    rw [smulP_idem s hs, comp_smul, P.obj.idem])
  π P := KCat.homMk (smulHom s P.obj.p) (by
    show smulHom s P.obj.p ≫ smulHom s P.obj.p ≫ P.obj.p = smulHom s P.obj.p
    rw [smul_comp s P.obj.p P.obj.p, P.obj.idem, smulP_idem s hs])
  ξπ P := KCat.hom_ext (smulP_idem s hs P)
  πξ P := KCat.hom_ext (smulP_idem s hs P)
  obj' P := splitScalarObj (orth s) (orth_idem hs) P
  ξ' P := KCat.homMk (smulHom (orth s) P.obj.p) (by
    show P.obj.p ≫ smulHom (orth s) P.obj.p ≫ smulHom (orth s) P.obj.p =
      smulHom (orth s) P.obj.p
    rw [smulP_idem _ (orth_idem hs), comp_smul, P.obj.idem])
  π' P := KCat.homMk (smulHom (orth s) P.obj.p) (by
    show smulHom (orth s) P.obj.p ≫ smulHom (orth s) P.obj.p ≫ P.obj.p =
      smulHom (orth s) P.obj.p
    rw [smul_comp (orth s) P.obj.p P.obj.p, P.obj.idem, smulP_idem _ (orth_idem hs)])
  ξπ' P := KCat.hom_ext (smulP_idem _ (orth_idem hs) P)
  πξ' P := KCat.hom_ext (smulP_idem _ (orth_idem hs) P)

/-- **REC 90** (`prop:monoidal-splits`, short.tex:1547, Proposition): a monoidal
effectus with a non-trivial idempotent scalar `s` has `Split(C) ≅ C_s × C_{s^⊥}`
for non-trivial effectuses `C_s`, `C_{s^⊥}`.  The paper's proof: every idempotent
splits in `Split(C)`, in particular `s · id` and `s^⊥ · id`; `C_s` is the category
with the objects of `Split(C)` and the morphisms `f = s · f`, identity `s · id`
(`(splitSplitting hs).ε.Part`, see `rec90_part_hom_iff`), an effectus with truth
`s · 1` and orthosupplement `s · p^⊥` (the `KCat` construction); and
`F(A,B) = A_s + B_{s^⊥}`, `G(A) = (A, A)` give the equivalence
(`CentralSplitting.equivalence`). -/
theorem rec90 {s : Scal C} (hs : s ≫ s = s) (h0 : s ≠ 0) (h1 : s ≠ 𝟙 _) :
    Nonempty (Split C ≌ (splitSplitting hs).ε.Part × (splitSplitting hs).ε'.Part) ∧
      (1 : Scal (splitSplitting hs).ε.Part) ≠ 0 ∧ (1 : Scal (splitSplitting hs).ε'.Part) ≠ 0 := by
  refine ⟨⟨(splitSplitting hs).equivalence⟩, ?_, ?_⟩
  · refine CentralIdem.part_nontrivial _ fun h => h0 ?_
    have e : smulHom s (𝟙 (effObj C)) = 0 := congrArg Karoubi.Hom.f h
    rwa [smulHom_id_effObj] at e
  · refine CentralIdem.part_nontrivial _ fun h => orth_ne_zero_of_ne_one h1 ?_
    have e : smulHom (orth s) (𝟙 (effObj C)) = 0 := congrArg Karoubi.Hom.f h
    rwa [smulHom_id_effObj] at e

/-- **REC 90**: the morphisms of the part `C_s` between `(P, s · id_P)` and
`(Q, s · id_Q)` are exactly the maps `f : P → Q` of `Split(C)` with `s · f = f`,
as printed. -/
theorem rec90_part_hom_iff {s : Scal C} (hs : s ≫ s = s) {P Q : Split C} (f : P ⟶ Q) :
    (splitSplitting hs).ε.e P ≫ f ≫ (splitSplitting hs).ε.e Q = f ↔
      smulHom s f.f = f.f := by
  have key : Karoubi.Hom.f ((splitSplitting hs).ε.e P ≫ f ≫ (splitSplitting hs).ε.e Q) =
      smulHom s f.f := by
    show smulHom s P.obj.p ≫ f.f ≫ smulHom s Q.obj.p = smulHom s f.f
    rw [comp_smul, smul_comp_smul, hs, KCat.comp_p, KCat.p_comp]
  constructor
  · intro h; rw [← key, h]
  · intro h; exact KCat.hom_ext (key.trans h)

/-! ## REC 91: monoidal effectuses with images and compatible filters and
comprehensions -/

/-- The family `t · id_A` on `C` itself. -/
noncomputable def scalarIdem (t : Scal C) (ht : t ≫ t = t) : CentralIdem C where
  e A := smulHom t (𝟙 A)
  idem A := by rw [smul_comp_smul, ht, Category.id_comp]
  nat f := by rw [smul_comp, comp_smul, Category.id_comp, Category.comp_id]

/-- `s · 1_A` is the image of `s · id_A` (so it is sharp). -/
theorem smul_isImage (t : Scal C) (ht : t ≫ t = t) (A : C) :
    IsImage (smulHom t (𝟙 A)) (truth A ≫ t) := by
  have h1 : ∀ q : Pred A, smulHom t (𝟙 A) ≫ q = q ≫ t := fun q => by
    rw [smul_comp, Category.id_comp, rec29_pred]
  refine ⟨?_, fun q hq => ?_⟩
  · rw [h1, h1, Category.assoc, ht]
  · rw [h1, h1] at hq
    rw [← hq]
    have := comp_le_comp q (pred_le_truth t)
    rwa [comp_truth_effObj] at this

variable [HasImages C] [HasFilters C] [HasComprehension C] [CompatibleFiltersComprehensions C]

theorem smul_isSharp (t : Scal C) (ht : t ≫ t = t) (A : C) : IsSharp (truth A ≫ t) :=
  ⟨_, _, smul_isImage t ht A⟩

/-- The paper's computation: `s · id_A = asrt_{s·1_A}`. -/
theorem smul_eq_asrt (t : Scal C) (ht : t ≫ t = t) (A : C) :
    asrtSharp (truth A ≫ t) (smul_isSharp t ht A) = smulHom t (𝟙 A) := by
  set a := asrtSharp (truth A ≫ t) (smul_isSharp t ht A) with ha
  have htruth : a ≫ truth A = truth A ≫ t := (asrtSharp_truth_image _ _).1
  -- `s^⊥ · asrt = 0`
  have h0 : smulHom (orth t) a = 0 := by
    apply EffectusPartialForm.eq_zero_of_one_zero (C := C)
    show smulHom (orth t) a ≫ truth A = 0
    rw [smul_comp, htruth, rec29_pred, Category.assoc]
    have : t ≫ orth t = 0 := orth_mul_idem ht
    rw [this, FinPAC.comp_zero]
  -- hence `asrt = s · asrt`
  have h2 : a = smulHom t a := by
    obtain ⟨h, e⟩ := smul_split t a
    conv_lhs => rw [← e]
    rw [PCM.ovee_congr rfl h0 h (PCM.perp_zero _), PCM.ovee_zero]
  -- `im(s · id) ≤ s · 1`, so `asrt ∘ (s · id) = s · id`
  have h3 : smulHom t (𝟙 A) ≫ a = smulHom t (𝟙 A) :=
    (rec77_a _ _ _).1 ((isImage_imPred _).2 _ (smul_isImage t ht A).1)
  rw [smul_comp, Category.id_comp, ← h2] at h3
  exact h3

/-- The splitting of `s · id_A` through the comprehension and compatible filter
of `s · 1_A`. -/
noncomputable def monoidalSplitting {s : Scal C} (hs : s ≫ s = s) : CentralSplitting C where
  ε := scalarIdem s hs
  ε' := scalarIdem (orth s) (orth_idem hs)
  e_e' A := by
    show smulHom s (𝟙 A) ≫ smulHom (orth s) (𝟙 A) = 0
    rw [smul_comp_smul]
    have : orth s ≫ s = 0 := idem_mul_orth hs
    rw [this, smul_zero_scalar]
  perp A := (smul_split s (𝟙 A)).1
  sum A := (smul_split s (𝟙 A)).2
  obj A := comprObj (truth A ≫ s)
  ξ A := compatFilter _ (smul_isSharp s hs A)
  π A := comprMap _
  ξπ A := smul_eq_asrt s hs A
  πξ A := (compatFilter_spec _ (smul_isSharp s hs A)).2
  obj' A := comprObj (truth A ≫ orth s)
  ξ' A := compatFilter _ (smul_isSharp (orth s) (orth_idem hs) A)
  π' A := comprMap _
  ξπ' A := smul_eq_asrt (orth s) (orth_idem hs) A
  πξ' A := (compatFilter_spec _ (smul_isSharp (orth s) (orth_idem hs) A)).2

/-- **REC 91** (`prop:monoidal-splits2`, short.tex:1628, Proposition): a monoidal
effectus with images and compatible filters and comprehensions, and a
non-trivial idempotent scalar `s`, has `C ≅ C_s × C_{s^⊥}` for non-trivial
effectuses `C_s`, `C_{s^⊥}` — now `C` itself, not its Karoubi envelope.  The
paper's proof: `s · 1_A` is sharp, being the image of `s · id_A`
(`smul_isImage`), and `s · id_A = asrt_{s·1_A} = π ∘ ξ` (`smul_eq_asrt`), so
`s · id_A` splits; the rest is the proof of REC 90. -/
theorem rec91 {s : Scal C} (hs : s ≫ s = s) (h0 : s ≠ 0) (h1 : s ≠ 𝟙 _) :
    Nonempty (C ≌ (monoidalSplitting hs).ε.Part × (monoidalSplitting hs).ε'.Part) ∧
      (1 : Scal (monoidalSplitting hs).ε.Part) ≠ 0 ∧
      (1 : Scal (monoidalSplitting hs).ε'.Part) ≠ 0 := by
  refine ⟨⟨(monoidalSplitting hs).equivalence⟩, ?_, ?_⟩
  · refine CentralIdem.part_nontrivial _ fun h => h0 ?_
    have e : smulHom s (𝟙 (effObj C)) = 0 := h
    rwa [smulHom_id_effObj] at e
  · refine CentralIdem.part_nontrivial _ fun h => orth_ne_zero_of_ne_one h1 ?_
    have e : smulHom (orth s) (𝟙 (effObj C)) = 0 := h
    rwa [smulHom_id_effObj] at e

/-- **REC 91**: the morphisms of `C_s` are the `f : A → B` with `s · f = f`. -/
theorem rec91_part_hom_iff {s : Scal C} (hs : s ≫ s = s) {A B : C} (f : A ⟶ B) :
    (monoidalSplitting hs).ε.e A ≫ f ≫ (monoidalSplitting hs).ε.e B = f ↔ smulHom s f = f := by
  have key : (monoidalSplitting hs).ε.e A ≫ f ≫ (monoidalSplitting hs).ε.e B = smulHom s f := by
    show smulHom s (𝟙 A) ≫ f ≫ smulHom s (𝟙 B) = smulHom s f
    rw [comp_smul, smul_comp_smul, hs, Category.id_comp, Category.comp_id]
  rw [key]

end Monoidal

/-! ## REC 92: effectuses separated by states or predicates -/

section AssertSplitting

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
  [HasImages C] [HasFilters C] [HasComprehension C] [CompatibleFiltersComprehensions C]

/-- `asrt_{t∘1_A}`, for a scalar `t` with `t ∘ 1_A` sharp. -/
noncomputable def asrtT (t : Scal C) (hsh : ∀ A : C, IsSharp (truth A ≫ t)) (A : C) : A ⟶ A :=
  asrtSharp (truth A ≫ t) (hsh A)

variable {t : Scal C} (ht : t ≫ t = t) (hsh : ∀ A : C, IsSharp (truth A ≫ t))

theorem asrtT_truth (A : C) : asrtT t hsh A ≫ truth A = truth A ≫ t :=
  (asrtSharp_truth_image _ _).1

include ht in
/-- The paper's computation in the proof of REC 92: `p ∘ asrt_{s∘1} = s ∘ p` for
every predicate `p` (REC 77 twice). -/
theorem asrtT_pred {A : C} (r : Pred A) : asrtT t hsh A ≫ r = r ≫ t := by
  have htt : t ≫ orth t = 0 := orth_mul_idem ht
  have ha : asrtT t hsh A ≫ (r ≫ t) = r ≫ t := by
    refine (rec77_b _ (hsh A) (r ≫ t)).1 ?_
    rw [comp_truth_effObj]
    exact le_comp_right' (pred_le_truth r) t
  have hb : asrtT t hsh A ≫ (r ≫ orth t) = 0 := by
    have := comp_le_comp (asrtT t hsh A) (le_comp_right' (pred_le_truth r) (orth t))
    rw [← Category.assoc (asrtT t hsh A) (truth A), asrtT_truth, Category.assoc, htt,
      FinPAC.comp_zero] at this
    exact eq_zero_of_le_zero this
  obtain ⟨h1, e1⟩ := FinPAC.ovee_comp (EffectAlgebra.perp_orth t) r
  rw [scal_ovee_orth, Category.comp_id] at e1
  obtain ⟨h2, e2⟩ := FinPAC.ovee_comp h1 (asrtT t hsh A)
  conv_lhs => rw [e1, e2]
  rw [PCM.ovee_congr ha hb h2 (PCM.perp_zero _), PCM.ovee_zero]

include ht in
/-- For a substate `y : I → A`, `asrt_{s∘1} ∘ y = y ∘ s` (the "extra
complication" of the state-separated case: `s` commutes with all scalars,
OAP 20 / `idem_central`). -/
theorem asrtT_substate {A : C} (y : effObj C ⟶ A) : y ≫ asrtT t hsh A = t ≫ y := by
  have ht' : t * t = t := ht
  set c : Scal C := y ≫ truth A with hc
  have hcomm : t ≫ c ≫ t = t ≫ c := by
    show t * c * t = c * t
    rw [idem_central ht' c, EffectMonoid.mul_assoc, ht']
  -- `(t ∘ y)` has image below `t ∘ 1`
  have ha : (t ≫ y) ≫ asrtT t hsh A = t ≫ y := by
    refine (rec77_a _ (hsh A) (t ≫ y)).1 ((isImage_imPred _).2 _ ?_)
    rw [Category.assoc, ← Category.assoc y, ← hc, hcomm, Category.assoc]
  -- `t^⊥ ∘ (y ≫ asrt) = 0`
  have hb : orth t ≫ y ≫ asrtT t hsh A = 0 := by
    apply EffectusPartialForm.eq_zero_of_one_zero (C := C)
    show (orth t ≫ y ≫ asrtT t hsh A) ≫ truth A = 0
    rw [Category.assoc, Category.assoc, asrtT_truth, ← Category.assoc y, ← hc]
    show t * c * orth t = 0
    rw [idem_central ht' c, EffectMonoid.mul_assoc, idem_mul_orth ht', (exc_emonzero c).1]
  have ha' : t ≫ y ≫ asrtT t hsh A = t ≫ y := by rw [← Category.assoc]; exact ha
  obtain ⟨h1, e1⟩ := FinPAC.comp_ovee (EffectAlgebra.perp_orth t) (y ≫ asrtT t hsh A)
  rw [scal_ovee_orth, Category.id_comp] at e1
  rw [e1, PCM.ovee_congr ha' hb h1 (PCM.perp_zero _), PCM.ovee_zero]

include ht in
/-- `s ∘ 1_A` is sharp in an effectus separated by states (the proof of REC 92
takes `asrt_{s∘1}`, which needs this; the paper does not say why it is sharp).
Its floor `⌊s∘1⌋ = im π` agrees with `s ∘ 1` on every state `ω`, because
`ω ∘ s` factors through the comprehension `π`. -/
theorem isSharp_of_states (hsep : SeparatingStates C) (A : C) : IsSharp (truth A ≫ t) := by
  have ht' : t * t = t := ht
  set p : Pred A := truth A ≫ t with hp
  have hq : IsImage (comprMap p) (imPred (comprMap p)) := isImage_imPred _
  have hle : imPred (comprMap p) ≼ p := hq.2 p (isComprehension_comprMap p).1
  suffices e : imPred (comprMap p) = p by exact ⟨_, _, e ▸ hq⟩
  refine hsep _ _ fun ω => ?_
  have hω : ω.1 ≫ truth A = 𝟙 _ := ω.2.trans truth_effObj_eq_id
  have hωp : ω.1 ≫ p = t := by rw [hp, ← Category.assoc, hω, Category.id_comp]
  rw [hωp]
  -- `t ∘ ω` factors through `π`
  have hf : (t ≫ ω.1) ≫ p = (t ≫ ω.1) ≫ truth A := by
    rw [Category.assoc, hωp, Category.assoc, hω, ht, Category.comp_id]
  obtain ⟨g, hg, -⟩ := (isComprehension_comprMap p).2 (t ≫ ω.1) hf
  have hx : (t ≫ ω.1) ≫ imPred (comprMap p) = t := by
    rw [← hg, Category.assoc, hq.1, ← Category.assoc, hg, Category.assoc, hω, Category.comp_id]
  have hxle : ω.1 ≫ imPred (comprMap p) ≼ t := hωp ▸ comp_le_comp ω.1 hle
  have := mul_idem_of_le ht' hxle
  -- `x · t = t ∘ x = t`
  rw [Category.assoc] at hx
  exact this.symm.trans hx

/-- The family `asrt_{t∘1_A}` is idempotent. -/
theorem asrtT_idem (A : C) : asrtT t hsh A ≫ asrtT t hsh A = asrtT t hsh A :=
  asrtSharp_idem _ _

include ht in
theorem asrtT_effObj : asrtT t hsh (effObj C) = t := by
  have := asrtT_truth hsh (effObj C)
  rwa [truth_effObj_eq_id, Category.comp_id, Category.id_comp] at this

include ht in
/-- The central idempotent family `asrt_{t∘1_A}`, natural under separation. -/
noncomputable def asrtIdem (hsep : SeparatingStates C ∨ SeparatingPredicates C) :
    CentralIdem C where
  e := asrtT t hsh
  idem := asrtT_idem hsh
  nat {A B} f := by
    rcases hsep with hsep | hsep
    · refine hsep _ _ fun ω => ?_
      have e1 := asrtT_substate ht hsh ω.1
      have e2 := asrtT_substate ht hsh (ω.1 ≫ f)
      calc ω.1 ≫ asrtT t hsh A ≫ f = (ω.1 ≫ asrtT t hsh A) ≫ f := (Category.assoc _ _ _).symm
        _ = (t ≫ ω.1) ≫ f := by rw [e1]
        _ = t ≫ ω.1 ≫ f := Category.assoc _ _ _
        _ = (ω.1 ≫ f) ≫ asrtT t hsh B := e2.symm
        _ = ω.1 ≫ f ≫ asrtT t hsh B := Category.assoc _ _ _
    · refine hsep _ _ fun r => ?_
      calc (asrtT t hsh A ≫ f) ≫ r = asrtT t hsh A ≫ (f ≫ r) := Category.assoc _ _ _
        _ = (f ≫ r) ≫ t := asrtT_pred ht hsh _
        _ = f ≫ (r ≫ t) := Category.assoc _ _ _
        _ = f ≫ (asrtT t hsh B ≫ r) := by rw [asrtT_pred ht hsh]
        _ = (f ≫ asrtT t hsh B) ≫ r := (Category.assoc _ _ _).symm

end AssertSplitting

section AssertSplitting2

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
  [HasImages C] [HasFilters C] [HasComprehension C] [CompatibleFiltersComprehensions C]

/-- `asrt_{s∘1} ⊥ asrt_{s^⊥∘1}` (their truths `s∘1`, `s^⊥∘1` are summable). -/
theorem asrtT_perp {s : Scal C} (hsh : ∀ A : C, IsSharp (truth A ≫ s))
    (hsh' : ∀ A : C, IsSharp (truth A ≫ orth s)) (A : C) :
    Perp (asrtT s hsh A) (asrtT (orth s) hsh' A) := by
  apply EffectusPartialForm.perp_of_one_perp (C := C)
  show Perp (asrtT s hsh A ≫ truth A) (asrtT (orth s) hsh' A ≫ truth A)
  rw [asrtT_truth, asrtT_truth]
  exact (FinPAC.ovee_comp (EffectAlgebra.perp_orth s) (truth A)).1

/-- The splitting of the proof of REC 92: `asrt_{s∘1}` and `asrt_{s^⊥∘1}`, split
by the comprehensions and compatible filters of `s∘1`, `s^⊥∘1`. -/
noncomputable def asrtSplitting {s : Scal C} (hs : s ≫ s = s)
    (hsh : ∀ A : C, IsSharp (truth A ≫ s)) (hsh' : ∀ A : C, IsSharp (truth A ≫ orth s))
    (hsep : SeparatingStates C ∨ SeparatingPredicates C) : CentralSplitting C where
  ε := asrtIdem hs hsh hsep
  ε' := asrtIdem (orth_idem hs) hsh' hsep
  e_e' A := by
    apply EffectusPartialForm.eq_zero_of_one_zero (C := C)
    show (asrtT s hsh A ≫ asrtT (orth s) hsh' A) ≫ truth A = 0
    rw [Category.assoc, asrtT_truth, ← Category.assoc, asrtT_pred hs, Category.assoc]
    have h1 : s ≫ orth s = 0 := orth_mul_idem hs
    have h2 : orth s ≫ s = 0 := idem_mul_orth hs
    first | rw [h1, FinPAC.comp_zero] | rw [h2, FinPAC.comp_zero]
  perp A := asrtT_perp hsh hsh' A
  sum A := by
    show ovee (asrtT s hsh A) (asrtT (orth s) hsh' A) (asrtT_perp hsh hsh' A) = 𝟙 A
    rcases hsep with hsep | hsep
    · refine hsep _ _ fun ω => ?_
      obtain ⟨h', e⟩ := FinPAC.ovee_comp (asrtT_perp hsh hsh' A) ω.1
      rw [e, Category.comp_id]
      obtain ⟨h2, e2⟩ := FinPAC.comp_ovee (EffectAlgebra.perp_orth s) ω.1
      rw [scal_ovee_orth, Category.id_comp] at e2
      rw [PCM.ovee_congr (asrtT_substate hs hsh ω.1) (asrtT_substate (orth_idem hs) hsh' ω.1)
        h' h2, ← e2]
    · refine hsep _ _ fun r => ?_
      obtain ⟨h', e⟩ := FinPAC.comp_ovee (asrtT_perp hsh hsh' A) r
      rw [e, Category.id_comp]
      obtain ⟨h2, e2⟩ := FinPAC.ovee_comp (EffectAlgebra.perp_orth s) r
      rw [scal_ovee_orth, Category.comp_id] at e2
      rw [PCM.ovee_congr (asrtT_pred hs hsh r) (asrtT_pred (orth_idem hs) hsh' r) h' h2, ← e2]
  obj A := comprObj (truth A ≫ s)
  ξ A := compatFilter _ (hsh A)
  π A := comprMap _
  ξπ A := rfl
  πξ A := (compatFilter_spec _ (hsh A)).2
  obj' A := comprObj (truth A ≫ orth s)
  ξ' A := compatFilter _ (hsh' A)
  π' A := comprMap _
  ξπ' A := rfl
  πξ' A := (compatFilter_spec _ (hsh' A)).2

theorem asrtSplitting_nontrivial {s : Scal C} (hs : s ≫ s = s)
    (hsh : ∀ A : C, IsSharp (truth A ≫ s)) (hsh' : ∀ A : C, IsSharp (truth A ≫ orth s))
    (hsep : SeparatingStates C ∨ SeparatingPredicates C) (h0 : s ≠ 0) (h1 : s ≠ 𝟙 _) :
    (1 : Scal (asrtSplitting hs hsh hsh' hsep).ε.Part) ≠ 0 ∧
      (1 : Scal (asrtSplitting hs hsh hsh' hsep).ε'.Part) ≠ 0 := by
  refine ⟨CentralIdem.part_nontrivial _ fun h => h0 ?_,
    CentralIdem.part_nontrivial _ fun h => orth_ne_zero_of_ne_one h1 ?_⟩
  · have e : asrtT s hsh (effObj C) = 0 := h
    rwa [asrtT_effObj hs] at e
  · have e : asrtT (orth s) hsh' (effObj C) = 0 := h
    rwa [asrtT_effObj (orth_idem hs)] at e

/-- **REC 92** (`prop:predsep-splits`, short.tex:1643, Proposition), for an
effectus **separated by states**, exactly as printed: with images and
compatible filters and comprehensions and a non-trivial idempotent scalar `s`,
`C ≅ C_s × C_{s^⊥}` for non-trivial effectuses.  The paper's proof, with the
maps `asrt_{s∘1}` in place of `s · id`: `C_s` has the maps `f` with
`im f ≤ s ∘ 1` and `1 ∘ f ≤ s ∘ 1` (`rec92_part_hom_iff`), identity `asrt_{s∘1}`;
`[π_{s∘1}, π_{s^⊥∘1}] ∘ ⟨ξ, ξ'⟩ = asrt_{s∘1} ⊻ asrt_{s^⊥∘1} = id` is checked on
states, using `asrt_{s∘1} ∘ ω = ω ∘ s` (`asrtT_substate`, where `s` commutes with
all scalars).  The paper takes `asrt_{s∘1}` without saying why `s∘1` is sharp;
under state separation it is (`isSharp_of_states`).  This case is true but has
no instances: with comprehensions and state separation the only idempotent
scalars are `0` and `1` (`idem_scalar_trivial`, `Reconstruction.lean`, REC 104). -/
theorem rec92_states (hsep : SeparatingStates C) {s : Scal C} (hs : s ≫ s = s) (h0 : s ≠ 0)
    (h1 : s ≠ 𝟙 _) :
    let σ := asrtSplitting hs (isSharp_of_states hs hsep) (isSharp_of_states (orth_idem hs) hsep)
      (Or.inl hsep)
    Nonempty (C ≌ σ.ε.Part × σ.ε'.Part) ∧ (1 : Scal σ.ε.Part) ≠ 0 ∧ (1 : Scal σ.ε'.Part) ≠ 0 :=
  ⟨⟨CentralSplitting.equivalence _⟩, asrtSplitting_nontrivial hs _ _ _ h0 h1⟩

/-- **REC 92** (`prop:predsep-splits`, short.tex:1643, Proposition), for an
effectus **separated by predicates**: the same conclusion, given that the
predicates `s ∘ 1_A` and `s^⊥ ∘ 1_A` are sharp.  The printed proof takes
`asrt_{s∘1}`, which needs `s ∘ 1` sharp, and does not justify it; in the
monoidal case (REC 91, `smul_isSharp`) and under state separation
(`isSharp_of_states`) it holds, but not from predicate separation alone: without
the sharpness hypothesis the proposition is false (`rec92_false_as_printed`,
witness `LinkedPts` in `Rec92Counter.lean`).  With it the paper's argument
goes through: `p ∘ asrt_{s∘1} = s ∘ p` (`asrtT_pred`) gives
`p ∘ (asrt_{s∘1} ⊻ asrt_{s^⊥∘1}) = p`. -/
theorem rec92_predicates (hsep : SeparatingPredicates C) {s : Scal C} (hs : s ≫ s = s)
    (hsh : ∀ A : C, IsSharp (truth A ≫ s)) (hsh' : ∀ A : C, IsSharp (truth A ≫ orth s))
    (h0 : s ≠ 0) (h1 : s ≠ 𝟙 _) :
    let σ := asrtSplitting hs hsh hsh' (Or.inr hsep)
    Nonempty (C ≌ σ.ε.Part × σ.ε'.Part) ∧ (1 : Scal σ.ε.Part) ≠ 0 ∧ (1 : Scal σ.ε'.Part) ≠ 0 :=
  ⟨⟨CentralSplitting.equivalence _⟩, asrtSplitting_nontrivial hs _ _ _ h0 h1⟩

/-- **REC 92**: the morphisms of the part `C_s`, `f = asrt ∘ f ∘ asrt`, are exactly
the maps with `im f ≤ s ∘ 1` and `1 ∘ f ≤ s ∘ 1`, as printed (REC 77). -/
theorem rec92_part_hom_iff {s : Scal C} (hsh : ∀ A : C, IsSharp (truth A ≫ s)) {A B : C}
    (f : A ⟶ B) :
    asrtT s hsh A ≫ f ≫ asrtT s hsh B = f ↔
      imPred f ≼ truth B ≫ s ∧ (f ≫ truth B) ≼ truth A ≫ s := by
  have hb := rec77_a _ (hsh B) f
  have ha := rec77_b _ (hsh A) f
  have iB : asrtT s hsh B ≫ asrtT s hsh B = asrtT s hsh B := asrtT_idem hsh B
  have iA : asrtT s hsh A ≫ asrtT s hsh A = asrtT s hsh A := asrtT_idem hsh A
  rw [hb, ha]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · show f ≫ asrtT s hsh B = f
      rw [← h]; simp only [Category.assoc, iB]
    · show asrtT s hsh A ≫ f = f
      rw [← h]; simp only [← Category.assoc, iA]
  · rintro ⟨h1, h2⟩
    have h1' : f ≫ asrtT s hsh B = f := h1
    have h2' : asrtT s hsh A ≫ f = f := h2
    rw [h1', h2']

end AssertSplitting2

/-! ## Effect algebra isomorphisms and transport -/

section EAIsoSection

/-- An **isomorphism of effect algebras**: mutually inverse effect algebra
homomorphisms (the `≅` of REC 87, 93, 97). -/
structure EAIso (E : Type u) (F : Type u) [EffectAlgebra E] [EffectAlgebra F] where
  hom : EAHom E F
  inv : EAHom F E
  inv_hom : ∀ a : E, inv.toFun (hom.toFun a) = a
  hom_inv : ∀ b : F, hom.toFun (inv.toFun b) = b

namespace EAIso

variable {E : Type u} {F : Type u} [EffectAlgebra E] [EffectAlgebra F]

theorem le_iff (φ : EAIso E F) {a b : E} : a ≼ b ↔ φ.hom.toFun a ≼ φ.hom.toFun b := by
  constructor
  · exact exc_eamorphism_monotone φ.hom
  · intro h
    have := exc_eamorphism_monotone φ.inv h
    rwa [φ.inv_hom, φ.inv_hom] at this

/-- Being an orthoalgebra transports along an isomorphism. -/
theorem isOrthoalgebra (φ : EAIso E F) (h : IsOrthoalgebra F) : IsOrthoalgebra E := by
  intro a ha
  have := h _ (φ.hom.perp_map ha)
  rw [← φ.inv_hom a, this, exc_eamorphism_map_zero]

/-- Directed completeness transports along an isomorphism. -/
theorem directedComplete (φ : EAIso E F) (h : DirectedCompleteEA F) : DirectedCompleteEA E := by
  intro D hD
  have hD' : IsUpDirected (φ.hom.toFun '' D) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hD x hx y hy
    exact ⟨_, ⟨z, hz, rfl⟩, φ.le_iff.1 hxz, φ.le_iff.1 hyz⟩
  obtain ⟨t, ht1, ht2⟩ := h _ hD'
  refine ⟨φ.inv.toFun t, fun x hx => ?_, fun u hu => ?_⟩
  · rw [φ.le_iff, φ.hom_inv]; exact ht1 _ ⟨x, hx, rfl⟩
  · rw [φ.le_iff, φ.hom_inv]
    exact ht2 _ (by rintro _ ⟨x, hx, rfl⟩; exact φ.le_iff.1 (hu x hx))

/-- A convex structure transports along an isomorphism:
`λ · a := φ⁻¹(λ · φ a)`. -/
def convex (φ : EAIso E F) [ConvexEA F] : ConvexEA E where
  smul l a := φ.inv.toFun (l • φ.hom.toFun a)
  smul_smul l m a := by
    show φ.inv.toFun (l • φ.hom.toFun (φ.inv.toFun (m • φ.hom.toFun a))) =
      φ.inv.toFun ((l * m) • φ.hom.toFun a)
    rw [φ.hom_inv, ConvexEA.smul_smul]
  add_smul l m a h := by
    obtain ⟨h', e⟩ := ConvexEA.add_smul l m (φ.hom.toFun a) h
    refine ⟨φ.inv.perp_map h', ?_⟩
    show ovee (φ.inv.toFun (l • φ.hom.toFun a)) (φ.inv.toFun (m • φ.hom.toFun a)) _ =
      φ.inv.toFun (_ • φ.hom.toFun a)
    rw [← φ.inv.ovee_map h', e]
  one_smul a := by
    show φ.inv.toFun ((1 : unitInterval) • φ.hom.toFun a) = a
    rw [ConvexEA.one_smul, φ.inv_hom]
  smul_ovee l a b h := by
    obtain ⟨h', e⟩ := ConvexEA.smul_ovee l (φ.hom.perp_map h)
    refine ⟨φ.inv.perp_map h', ?_⟩
    show φ.inv.toFun (l • φ.hom.toFun (ovee a b h)) = ovee (φ.inv.toFun (l • φ.hom.toFun a))
      (φ.inv.toFun (l • φ.hom.toFun b)) _
    rw [φ.hom.ovee_map h, e, φ.inv.ovee_map h']

end EAIso

/-- `PCM` homomorphisms are determined by their underlying function. -/
theorem PCMHom.ext' {M : Type u} {N : Type w} [PCM M] [PCM N] {f g : PCMHom M N}
    (h : f.toFun = g.toFun) : f = g := by
  obtain ⟨f₁, _, _⟩ := f
  obtain ⟨g₁, _, _⟩ := g
  dsimp only at h
  subst h
  rfl

/-- The category **EA** of effect algebras with *additive* maps (the codomain of
`Pred : C → EAᵒᵖ`, REC 12: `Pred(f)` preserves `⊻` and `0` but not `1`). -/
structure EAAdd : Type (u + 1) where
  carrier : Type u
  [str : EffectAlgebra carrier]

attribute [instance] EAAdd.str

instance : Category EAAdd.{u} where
  Hom E F := PCMHom E.carrier F.carrier
  id E := PCMHom.id E.carrier
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- **REC 94**: the category **OA** of orthoalgebras (REC 37), with additive maps. -/
structure OACat : Type (u + 1) where
  carrier : Type u
  [str : EffectAlgebra carrier]
  isOA : IsOrthoalgebra carrier

attribute [instance] OACat.str

instance : Category OACat.{u} where
  Hom E F := PCMHom E.carrier F.carrier
  id E := PCMHom.id E.carrier
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- **REC 94**: the category **DCEA_c** of directed-complete convex effect
algebras (REC 39), with additive maps preserving the convex action. -/
structure DCEACCat : Type (u + 1) where
  carrier : Type u
  [str : EffectAlgebra carrier]
  [cvx : ConvexEA carrier]
  dc : DirectedCompleteEA carrier

attribute [instance] DCEACCat.str DCEACCat.cvx

instance : Category DCEACCat.{u} where
  Hom E F := { f : PCMHom E.carrier F.carrier // ∀ (l : unitInterval) (x : E.carrier),
    f.toFun (l • x) = l • f.toFun x }
  id E := ⟨PCMHom.id E.carrier, fun _ _ => rfl⟩
  comp f g := ⟨g.1.comp f.1, fun l x => by
    show g.1.toFun (f.1.toFun (l • x)) = l • g.1.toFun (f.1.toFun x)
    rw [f.2, g.2]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end EAIsoSection

/-! ## REC 87: the predicate spaces split along an idempotent scalar -/

section PredParts

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

variable {t : Scal C} (ht : t ≫ t = t)

/-- `p = t ∘ p ⊻ t^⊥ ∘ p`. -/
theorem pred_split {A : C} (p : Pred A) :
    ∃ h : Perp (p ≫ t) (p ≫ orth t), ovee (p ≫ t) (p ≫ orth t) h = p := by
  obtain ⟨h, e⟩ := FinPAC.ovee_comp (EffectAlgebra.perp_orth t) p
  rw [scal_ovee_orth, Category.comp_id] at e
  exact ⟨h, e.symm⟩

include ht in
/-- The `t`-part `t · Pred(A)` is downward closed. -/
theorem part_of_le {A : C} {p q : Pred A} (hq : q ≫ t = q) (h : p ≼ q) : p ≫ t = p := by
  have hz : p ≫ orth t = 0 := by
    have := le_comp_right' h (orth t)
    rw [← hq, Category.assoc, show t ≫ orth t = 0 from orth_mul_idem ht,
      FinPAC.comp_zero] at this
    exact eq_zero_of_le_zero this
  obtain ⟨h1, e⟩ := pred_split (t := t) p
  conv_rhs => rw [← e]
  rw [PCM.ovee_congr rfl hz h1 (PCM.perp_zero _), PCM.ovee_zero]

/-- The **`t`-part** `t · Pred(A) = {t ∘ p} = {p ; t ∘ p = p}` of the predicates
(the paper's `E₁ = s · E`, `E₂ = s^⊥ · E`). -/
def PredPart (_ht : t ≫ t = t) (A : C) : Type v := { p : Pred A // p ≫ t = p }

namespace PredPart

theorem perp_orth' {A : C} (p : PredPart ht A) :
    Perp p.1 (orth (p.1 : Pred A) ≫ t) := by
  obtain ⟨h', -⟩ := FinPAC.comp_ovee (EffectAlgebra.perp_orth (p.1 : Pred A)) t
  rw [p.2] at h'
  exact h'

theorem ovee_orth' {A : C} (p : PredPart ht A) :
    ovee p.1 (orth (p.1 : Pred A) ≫ t) (perp_orth' ht p) = truth A ≫ t := by
  obtain ⟨h', e⟩ := FinPAC.comp_ovee (EffectAlgebra.perp_orth (p.1 : Pred A)) t
  rw [EffectAlgebra.ovee_orth] at e
  exact (PCM.ovee_congr p.2.symm rfl _ _).trans e.symm

/-- The effect algebra `t · Pred(A)`: the sum of `Pred(A)`, top `t ∘ 1`, and
`p^⊥ := t ∘ p^⊥`. -/
instance ea {A : C} : EffectAlgebra (PredPart ht A) where
  zero := ⟨0, FinPAC.zero_comp _⟩
  Perp p q := Perp p.1 q.1
  ovee p q h := ⟨ovee p.1 q.1 h, by
    obtain ⟨h', e⟩ := FinPAC.comp_ovee h t
    rw [e]; exact PCM.ovee_congr p.2 q.2 _ _⟩
  perp_comm h := PCM.perp_comm h
  ovee_comm h := Subtype.ext (PCM.ovee_comm h)
  perp_of_ovee_perp hab h := PCM.perp_of_ovee_perp (M := Pred A) hab h
  perp_ovee_of_ovee_perp hab h := PCM.perp_ovee_of_ovee_perp (M := Pred A) hab h
  ovee_assoc hab h := Subtype.ext (PCM.ovee_assoc (M := Pred A) hab h)
  zero_perp a := PCM.zero_perp a.1
  zero_ovee a := Subtype.ext (PCM.zero_ovee a.1)
  one := ⟨truth A ≫ t, by rw [Category.assoc, ht]⟩
  orth p := ⟨orth (p.1 : Pred A) ≫ t, by rw [Category.assoc, ht]⟩
  perp_orth p := perp_orth' ht p
  ovee_orth p := Subtype.ext (ovee_orth' ht p)
  orth_unique {p q} h e := Subtype.ext
    (ovee_left_cancel h (perp_orth' ht p)
      ((congrArg Subtype.val e).trans (ovee_orth' ht p).symm))
  eq_zero_of_perp_one {p} h := Subtype.ext (by
    have h' : Perp p.1 (truth A ≫ t) := h
    have hle := le_comp_right' (pred_le_truth (ovee _ _ h')) t
    obtain ⟨h2, e2⟩ := FinPAC.comp_ovee h' t
    rw [e2] at hle
    have ht2 : (truth A ≫ t) ≫ t = truth A ≫ t := by rw [Category.assoc, ht]
    have h3 : ovee (p.1 ≫ t) ((truth A ≫ t) ≫ t) h2 = ovee p.1 (truth A ≫ t) h' :=
      PCM.ovee_congr p.2 ht2 _ _
    rw [h3] at hle
    exact eq_zero_of_ovee_le h' hle)

@[simp] theorem val_ovee {A : C} {p q : PredPart ht A} (h : Perp p q) :
    (ovee p q h).1 = ovee p.1 q.1 h := rfl

@[simp] theorem val_one {A : C} : (1 : PredPart ht A).1 = truth A ≫ t := rfl

@[simp] theorem val_zero {A : C} : (0 : PredPart ht A).1 = 0 := rfl

theorem le_iff {A : C} {p q : PredPart ht A} : p ≼ q ↔ p.1 ≼ q.1 := by
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c.1, hc, rfl⟩
  · rintro ⟨c, hc, e⟩
    have hcq : c ≼ q.1 := ⟨p.1, PCM.perp_comm hc, (PCM.ovee_comm hc).symm.trans e⟩
    exact ⟨⟨c, part_of_le ht q.2 hcq⟩, hc, Subtype.ext e⟩

/-- Elements of the `t`-part are below `t ∘ 1`. -/
theorem le_one {A : C} (p : PredPart ht A) : p.1 ≼ truth A ≫ t := by
  have := le_comp_right' (pred_le_truth p.1) t
  rwa [p.2] at this

/-- Directed completeness passes to the parts. -/
theorem directedComplete {A : C} (h : DirectedCompleteEA (Pred A)) :
    DirectedCompleteEA (PredPart ht A) := by
  intro D hD
  have hD' : IsUpDirected (Subtype.val '' D) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hD x hx y hy
    exact ⟨_, ⟨z, hz, rfl⟩, (le_iff ht).1 hxz, (le_iff ht).1 hyz⟩
  obtain ⟨σ, hσ1, hσ2⟩ := h _ hD'
  have hσ : σ ≼ truth A ≫ t := hσ2 _ (by rintro _ ⟨x, -, rfl⟩; exact le_one ht x)
  have hσt : σ ≫ t = σ := part_of_le ht (by rw [Category.assoc, ht]) hσ
  refine ⟨⟨σ, hσt⟩, fun x hx => (le_iff ht).2 (hσ1 _ ⟨x, hx, rfl⟩), fun u hu => ?_⟩
  exact (le_iff ht).2 (hσ2 _ (by rintro _ ⟨x, hx, rfl⟩; exact (le_iff ht).1 (hu x hx)))

/-- `Pred(f)` restricts to the parts. -/
def map {A B : C} (f : A ⟶ B) : PCMHom (PredPart ht B) (PredPart ht A) where
  toFun p := ⟨f ≫ p.1, by rw [Category.assoc, p.2]⟩
  perp_map h := (FinPAC.ovee_comp h f).1
  ovee_map h := Subtype.ext (FinPAC.ovee_comp h f).2

end PredPart

/-- Elements of the `t`- and `t^⊥`-parts are orthogonal. -/
theorem part_perp {A : C} (x : PredPart ht A) (y : PredPart (orth_idem ht) A) : Perp x.1 y.1 := by
  have hT : Perp (truth A ≫ t) (truth A ≫ orth t) :=
    (FinPAC.ovee_comp (EffectAlgebra.perp_orth t) (truth A)).1
  obtain ⟨h1, -⟩ := eabasics_le_perp_compat (PredPart.le_one ht x) hT
  obtain ⟨h2, -⟩ := eabasics_le_perp_compat (PredPart.le_one (orth_idem ht) y)
    (PCM.perp_comm h1)
  exact PCM.perp_comm h2

theorem part_cross {A : C} (y : PredPart (orth_idem ht) A) : y.1 ≫ t = 0 := by
  have : orth t ≫ t = 0 := idem_mul_orth ht
  rw [← y.2, Category.assoc, this, FinPAC.comp_zero]

theorem part_cross' {A : C} (x : PredPart ht A) : x.1 ≫ orth t = 0 := by
  have : t ≫ orth t = 0 := orth_mul_idem ht
  rw [← x.2, Category.assoc, this, FinPAC.comp_zero]

/-- **REC 87** (the proof's first step): `Pred(A) ≅ t · Pred(A) ⊕ t^⊥ · Pred(A)`,
`p ↦ (t ∘ p, t^⊥ ∘ p)`, with inverse `(p₁, p₂) ↦ p₁ ⊻ p₂`. -/
noncomputable def predSplitIso (A : C) :
    EAIso (Pred A) (PredPart ht A × PredPart (orth_idem ht) A) where
  hom :=
    { toFun := fun p => (⟨p ≫ t, by rw [Category.assoc, ht]⟩,
        ⟨p ≫ orth t, by rw [Category.assoc, show orth t ≫ orth t = orth t from orth_idem ht]⟩)
      perp_map := fun h => ⟨(FinPAC.comp_ovee h t).1, (FinPAC.comp_ovee h (orth t)).1⟩
      ovee_map := fun h => Prod.ext (Subtype.ext (FinPAC.comp_ovee h t).2)
        (Subtype.ext (FinPAC.comp_ovee h (orth t)).2)
      map_one := rfl }
  inv :=
    { toFun := fun u => ovee u.1.1 u.2.1 (part_perp ht u.1 u.2)
      perp_map := fun {u v} h => by
        obtain ⟨hac, hbd, h', -⟩ := pcm_middle_four' (a := u.1.1) (b := v.1.1)
          (c := u.2.1) (d := v.2.1) h.1 h.2 (part_perp ht (ovee u.1 v.1 h.1) (ovee u.2 v.2 h.2))
        exact h'
      ovee_map := fun {u v} h => by
        obtain ⟨hac, hbd, h', e⟩ := pcm_middle_four' (a := u.1.1) (b := v.1.1)
          (c := u.2.1) (d := v.2.1) h.1 h.2 (part_perp ht (ovee u.1 v.1 h.1) (ovee u.2 v.2 h.2))
        exact e.symm
      map_one := (pred_split (t := t) (truth A)).2 }
  inv_hom p := (pred_split p).2
  hom_inv u := by
    obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := u
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show ovee a c _ ≫ t = a
      obtain ⟨h', e⟩ := FinPAC.comp_ovee (part_perp ht ⟨a, ha⟩ ⟨c, hc⟩) t
      rw [e, PCM.ovee_congr ha (part_cross ht ⟨c, hc⟩) h' (PCM.perp_zero _), PCM.ovee_zero]
    · show ovee a c _ ≫ orth t = c
      obtain ⟨h', e⟩ := FinPAC.comp_ovee (part_perp ht ⟨a, ha⟩ ⟨c, hc⟩) (orth t)
      rw [e, PCM.ovee_congr (part_cross' ht ⟨a, ha⟩) hc h' (PCM.zero_perp _), PCM.zero_ovee]

/-- The functor `A ↦ t · Pred(A)`, `f ↦ Pred(f)|` into **EA** (additive maps). -/
noncomputable def predPartFunctor : Cᵒᵖ ⥤ EAAdd.{v} where
  obj A := ⟨PredPart ht A.unop⟩
  map f := PredPart.map ht f.unop
  map_id A := PCMHom.ext' (funext fun p => Subtype.ext (Category.id_comp p.1))
  map_comp f g := PCMHom.ext' (funext fun p => Subtype.ext (Category.assoc _ _ p.1))

end PredParts

section Rec87

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **REC 87** (`prop:effectus-product`, short.tex:1486, Proposition): an effectus
with a non-trivial idempotent scalar `s` has `Pred(C)` embedded non-trivially in
a product of categories.  (Under-specified as printed; formalised as the content
of the printed sketch.)  With `C₁ = s · Pred(−)`, `C₂ = s^⊥ · Pred(−)` (both
functors into **EA**, `predPartFunctor`):

* every `Pred(A)` is isomorphic to `s · Pred(A) ⊕ s^⊥ · Pred(A)` via
  `p ↦ (s ∘ p, s^⊥ ∘ p)` (`predSplitIso`);
* the functor `Pred(C) → C₁ × C₂` is faithful: `Pred(f) = Pred(g)` iff both
  restrictions agree;
* both factors are non-trivial: `1 ≠ 0` in `s · Pred(I)` and `s^⊥ · Pred(I)`. -/
theorem rec87 {s : Scal C} (hs : s ≫ s = s) (h0 : s ≠ 0) (h1 : s ≠ 𝟙 _) :
    (∀ (A : C) (p : Pred A), ((predSplitIso hs A).hom.toFun p).1.1 = p ≫ s ∧
      ((predSplitIso hs A).hom.toFun p).2.1 = p ≫ orth s) ∧
    (∀ {A B : C} (f g : A ⟶ B),
      (∀ p : Pred B, f ≫ p = g ≫ p) ↔
        ((predPartFunctor hs).map f.op = (predPartFunctor hs).map g.op ∧
          (predPartFunctor (orth_idem hs)).map f.op = (predPartFunctor (orth_idem hs)).map g.op)) ∧
    (1 : PredPart hs (effObj C)) ≠ 0 ∧ (1 : PredPart (orth_idem hs) (effObj C)) ≠ 0 := by
  refine ⟨fun A p => ⟨rfl, rfl⟩, fun f g => ⟨fun h => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ p => ?_⟩, ?_, ?_⟩
  · exact PCMHom.ext' (funext fun p => Subtype.ext (h p.1))
  · exact PCMHom.ext' (funext fun p => Subtype.ext (h p.1))
  · have e1 := congrArg Subtype.val (congrFun (congrArg PCMHom.toFun h1)
      ⟨p ≫ s, by rw [Category.assoc, hs]⟩)
    have e2 := congrArg Subtype.val (congrFun (congrArg PCMHom.toFun h2)
      ⟨p ≫ orth s, by rw [Category.assoc, show orth s ≫ orth s = orth s from orth_idem hs]⟩)
    obtain ⟨h, e⟩ := pred_split (t := s) p
    rw [← e]
    obtain ⟨hf, ef⟩ := FinPAC.ovee_comp h f
    obtain ⟨hg, eg⟩ := FinPAC.ovee_comp h g
    rw [ef, eg]
    exact PCM.ovee_congr e1 e2 _ _
  · intro h
    apply h0
    have := congrArg Subtype.val h
    simpa [truth_effObj_eq_id] using this
  · intro h
    apply orth_ne_zero_of_ne_one h1
    have := congrArg Subtype.val h
    simpa [truth_effObj_eq_id] using this

end Rec87

/-! ## REC 93–95: directed-complete effectuses -/

section DirectedCompleteSplit

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

variable (C) in
/-- What the proof of REC 93 uses of REC 35 (`Pred(I) ≅ B ⊕ C(X,[0,1])`): the
idempotent `s ≡ (1, 0)` projecting onto the Boolean part, the fact that the
Boolean part is an orthoalgebra, and the convex action `λ ↦ c_λ ≡ (0, λ)` of
`[0,1]` on the convex part. -/
structure ScalarSplit where
  s : Scal C
  hs : s ≫ s = s
  bool : ∀ x : Scal C, x ≫ s = x → Perp x x → x = 0
  c : unitInterval → Scal C
  c_mul : ∀ l m : unitInterval, c m ≫ c l = c (l * m)
  c_add : ∀ (l m : unitInterval) (h : (l : ℝ) + m ≤ 1),
    ∃ hp : Perp (c l) (c m), ovee (c l) (c m) hp = c ⟨(l : ℝ) + m, add_nonneg l.2.1 m.2.1, h⟩
  c_one : c 1 = orth s

namespace ScalarSplit

variable (σs : ScalarSplit C)

theorem c_orth (l : unitInterval) : σs.c l ≫ orth σs.s = σs.c l := by
  rw [← σs.c_one, σs.c_mul, one_mul]

/-- The convex action on the `s^⊥`-part: `λ · p := c_λ ∘ p`. -/
def convex (A : C) : ConvexEA (PredPart (orth_idem σs.hs) A) where
  smul l p := ⟨p.1 ≫ σs.c l, by rw [Category.assoc, σs.c_orth]⟩
  smul_smul l m x := Subtype.ext (by
    show (x.1 ≫ σs.c m) ≫ σs.c l = x.1 ≫ σs.c (l * m)
    rw [Category.assoc, σs.c_mul])
  add_smul l m x h := by
    obtain ⟨hp, e⟩ := σs.c_add l m h
    obtain ⟨h', e'⟩ := FinPAC.ovee_comp hp x.1
    exact ⟨h', Subtype.ext (e'.symm.trans (congrArg (x.1 ≫ ·) e))⟩
  one_smul x := Subtype.ext (by
    show x.1 ≫ σs.c 1 = x.1
    rw [σs.c_one]; exact x.2)
  smul_ovee l x y h := by
    obtain ⟨h', e⟩ := FinPAC.comp_ovee (show Perp x.1 y.1 from h) (σs.c l)
    exact ⟨h', Subtype.ext e⟩

theorem convex_smul (A : C) (l : unitInterval) (p : PredPart (orth_idem σs.hs) A) :
    ((σs.convex A).smul l p).1 = p.1 ≫ σs.c l := rfl

/-- The `s`-parts of a directed-complete effectus separated by states are
orthoalgebras (the second half of the proof of REC 93). -/
theorem isOrthoalgebra (hsep : SeparatingStates C) (A : C) :
    IsOrthoalgebra (PredPart σs.hs A) := by
  intro p hp
  apply Subtype.ext
  refine hsep p.1 0 fun ω => ?_
  rw [FinPAC.comp_zero]
  refine σs.bool _ ?_ (FinPAC.ovee_comp (show Perp p.1 p.1 from hp) ω.1).1
  rw [Category.assoc, p.2]

end ScalarSplit

/-- REC 35 gives a `ScalarSplit`: from `φ : Pred(I) ≅ B ⊕ C(X,[0,1])` take
`s = φ⁻¹(1, 0)` and `c_λ = φ⁻¹(0, λ)`. -/
theorem scalarSplit_exists (h34 : EffectMonoidDCClassification.{v})
    (hdc : DirectedCompleteEffectus C) : Nonempty (ScalarSplit C) := by
  obtain ⟨B, iB, X, iX, -, -, -, ⟨φ⟩⟩ := rec35_scalars h34 hdc
  letI : EffectMonoid B := booleanEffectMonoid B
  letI : EffectMonoid (Set.Icc (0 : C(X, ℝ)) 1) := continuousUnitIntervalEffectMonoid X
  let K := Set.Icc (0 : C(X, ℝ)) 1
  let cst : unitInterval → K := fun l =>
    ⟨ContinuousMap.const X (l : ℝ), cIcc_mem (fun _ => l.2.1) (fun _ => l.2.2)⟩
  let z : K := ⟨0, cIcc_mem (fun _ => le_refl 0) (fun _ => zero_le_one)⟩
  let s : Scal C := φ.inv.toFun (⊤, z)
  have hs : s ≫ s = s := by
    show φ.inv.toFun (⊤, z) * φ.inv.toFun (⊤, z) = φ.inv.toFun (⊤, z)
    rw [← φ.inv.map_mul]
    congr 1
    exact Prod.ext (show (⊤ : B) ⊓ ⊤ = ⊤ from inf_idem _)
      (Subtype.ext (show (0 : C(X, ℝ)) * 0 = 0 from mul_zero _))
  refine ⟨⟨s, hs, ?_, fun l => φ.inv.toFun (⊥, cst l), ?_, ?_, ?_⟩⟩
  · intro x hx hxx
    have hx' : s * x = x := hx
    have e1 := φ.hom.map_mul s x
    rw [hx'] at e1
    rw [show φ.hom.toFun s = (⊤, z) from φ.hom_inv _] at e1
    have hp := φ.hom.perp_map hxx
    have hy : φ.hom.toFun x = (⊥, z) := by
      refine Prod.ext ?_ ?_
      · have : (φ.hom.toFun x).1 ⊓ (φ.hom.toFun x).1 = ⊥ := hp.1
        rwa [inf_idem] at this
      · rw [e1]
        exact Subtype.ext (show (0 : C(X, ℝ)) * _ = 0 from zero_mul _)
    rw [← φ.inv_hom x, hy]
    exact EffectMonoidHom.map_zero' φ.inv
  · intro l m
    show φ.inv.toFun (⊥, cst l) * φ.inv.toFun (⊥, cst m) = φ.inv.toFun (⊥, cst (l * m))
    rw [← φ.inv.map_mul]
    congr 1
    refine Prod.ext (show (⊥ : B) ⊓ ⊥ = ⊥ from inf_idem _) (Subtype.ext ?_)
    ext x
    show (l : ℝ) * m = ((l * m : unitInterval) : ℝ)
    simp
  · intro l m h
    have hperp : Perp ((⊥ : B), cst l) ((⊥ : B), cst m) :=
      ⟨show (⊥ : B) ⊓ ⊥ = ⊥ from inf_idem _,
        cIcc_perp_of fun x => by show (l : ℝ) + m ≤ 1; exact h⟩
    refine ⟨φ.inv.perp_map hperp, ?_⟩
    rw [← φ.inv.ovee_map hperp]
    congr 1
    refine Prod.ext (show (⊥ : B) ⊔ ⊥ = ⊥ from sup_idem _) (Subtype.ext ?_)
    ext x
    show (l : ℝ) + m = (l : ℝ) + m
    rfl
  · show φ.inv.toFun (⊥, cst 1) = orth (φ.inv.toFun (⊤, z))
    rw [← exc_eamorphism_map_orth φ.inv.toEAHom]
    congr 1
    refine Prod.ext (show (⊥ : B) = ⊤ᶜ from compl_top.symm) (Subtype.ext ?_)
    ext x
    show ((1 : unitInterval) : ℝ) = 1 - 0
    simp

variable [HasImages C] [HasFilters C] [HasComprehension C] [CompatibleFiltersComprehensions C]

/-- **REC 93** (`prop:dc-ortho-convex`, short.tex:1666, Proposition): in a
directed-complete effectus separated by states, `Pred(A) ≅ E₁ ⊕ E₂` with `E₁` an
orthoalgebra and `E₂` convex.  The paper's proof: with `s` the idempotent scalar
projecting onto the Boolean part of `Pred(I) ≅ M₁ ⊕ M₂` (REC 35, from OAP 69,
entering as the hypothesis `h34`), `E₁ = s · Pred(A)` and `E₂ = s^⊥ · Pred(A)`;
`E₂` is convex via `λ · p = (λ · s^⊥) ∘ p` (printed `s₁` for `s^⊥`); if `p ⊥ p` in
`E₁` then `p ∘ ω ⊥ p ∘ ω` in the Boolean part, so `p ∘ ω = 0`, for every state
`ω`, whence `p = 0`.  (The idempotent `s` does not depend on `A`, and it is the
same one for every `A`, which the statement below records.) -/
theorem rec93 (h34 : EffectMonoidDCClassification.{v}) (hdc : DirectedCompleteEffectus C)
    (hsep : SeparatingStates C) :
    ∃ σs : ScalarSplit C, ∀ A : C,
      Nonempty (EAIso (Pred A) (PredPart σs.hs A × PredPart (orth_idem σs.hs) A)) ∧
      IsOrthoalgebra (PredPart σs.hs A) ∧ Nonempty (ConvexEA (PredPart (orth_idem σs.hs) A)) := by
  obtain ⟨σs⟩ := scalarSplit_exists h34 hdc
  exact ⟨σs, fun A => ⟨⟨predSplitIso σs.hs A⟩, σs.isOrthoalgebra hsep A, ⟨σs.convex A⟩⟩⟩

/-- **REC 94** (`prop:effectus-ortho-OUS`, short.tex:1705, Proposition): in a
directed-complete effectus separated by states, `Pred` gives a functor
`C → OAᵒᵖ × DCEA_cᵒᵖ`, `A ↦ (s · Pred(A), s^⊥ · Pred(A))` (here as a functor
`Cᵒᵖ → OA × DCEA_c`).  The further identification `DCEA_c ≅ DCOUS` of the point
is REC 42, which is not formalised (it needs Wright's lemma; `PLAN.md` §1). -/
noncomputable def rec94_functor (σs : ScalarSplit C) (hdc : DirectedCompleteEffectus C)
    (hsep : SeparatingStates C) : Cᵒᵖ ⥤ OACat.{v} × DCEACCat.{v} where
  obj A := (⟨PredPart σs.hs A.unop, σs.isOrthoalgebra hsep _⟩,
    @DCEACCat.mk (PredPart (orth_idem σs.hs) A.unop) _ (σs.convex _)
      (PredPart.directedComplete _ (hdc _)))
  map f := (PredPart.map σs.hs f.unop,
    ⟨PredPart.map (orth_idem σs.hs) f.unop, fun l x => Subtype.ext (Category.assoc _ _ _).symm⟩)
  map_id A := Prod.hom_ext (PCMHom.ext' (funext fun p => Subtype.ext (Category.id_comp p.1)))
    (Subtype.ext (PCMHom.ext' (funext fun p => Subtype.ext (Category.id_comp p.1))))
  map_comp f g := Prod.hom_ext
    (PCMHom.ext' (funext fun p => Subtype.ext (Category.assoc _ _ p.1)))
    (Subtype.ext (PCMHom.ext' (funext fun p => Subtype.ext (Category.assoc _ _ p.1))))

/-- **REC 94**: the functor of `rec94_functor` recovers `Pred(A)` as the direct
sum of its two components (REC 93). -/
theorem rec94 (h34 : EffectMonoidDCClassification.{v}) (hdc : DirectedCompleteEffectus C)
    (hsep : SeparatingStates C) :
    ∃ σs : ScalarSplit C, ∀ A : C,
      Nonempty (EAIso (Pred A) (((rec94_functor σs hdc hsep).obj (Opposite.op A)).1.carrier ×
        ((rec94_functor σs hdc hsep).obj (Opposite.op A)).2.carrier)) := by
  obtain ⟨σs⟩ := scalarSplit_exists h34 hdc
  exact ⟨σs, fun A => ⟨predSplitIso σs.hs A⟩⟩

/-! ### REC 95 -/

section PartPred

variable {t : Scal C} (ht : t ≫ t = t) (hsh : ∀ A : C, IsSharp (truth A ≫ t))
  (hsep' : SeparatingStates C ∨ SeparatingPredicates C)

/-- The predicates of an object `(A, asrt_{t∘1})` of the part `C_t` are the
`t`-part of `Pred(A)`. -/
noncomputable def partPredIso (P : (asrtIdem ht hsh hsep').Part) :
    EAIso (Pred P) (PredPart ht P.obj.X) where
  hom :=
    { toFun := fun q => ⟨q.f, by
        have h := KCat.comp_p q
        change q.f ≫ asrtT t hsh (effObj C) = q.f at h
        rwa [asrtT_effObj ht] at h⟩
      perp_map := fun h => h
      ovee_map := fun h => rfl
      map_one := Subtype.ext (by
        show P.obj.p ≫ truth P.obj.X = truth P.obj.X ≫ t
        rw [(asrtIdem ht hsh hsep').prop P]
        exact asrtT_truth hsh _) }
  inv :=
    { toFun := fun r => KCat.homMk r.1 (by
        show P.obj.p ≫ r.1 ≫ asrtT t hsh (effObj C) = r.1
        rw [(asrtIdem ht hsh hsep').prop P, asrtT_effObj ht, r.2]
        show asrtT t hsh P.obj.X ≫ r.1 = r.1
        rw [asrtT_pred ht, r.2])
      perp_map := fun h => h
      ovee_map := fun h => rfl
      map_one := KCat.hom_ext (by
        show truth P.obj.X ≫ t = P.obj.p ≫ truth P.obj.X
        rw [(asrtIdem ht hsh hsep').prop P]
        exact (asrtT_truth hsh _).symm) }
  inv_hom q := rfl
  hom_inv r := rfl

theorem partPred_isOrthoalgebra (P : (asrtIdem ht hsh hsep').Part)
    (h : IsOrthoalgebra (PredPart ht P.obj.X)) : IsOrthoalgebra (Pred P) :=
  (partPredIso ht hsh hsep' P).isOrthoalgebra h

theorem partPred_directedComplete (P : (asrtIdem ht hsh hsep').Part)
    (h : DirectedCompleteEA (Pred P.obj.X)) : DirectedCompleteEA (Pred P) :=
  (partPredIso ht hsh hsep' P).directedComplete (PredPart.directedComplete ht h)

/-- The convex structure on the predicates of an object of a part. -/
noncomputable def partPredConvex (P : (asrtIdem ht hsh hsep').Part) [ConvexEA (PredPart ht P.obj.X)] :
    ConvexEA (Pred P) :=
  (partPredIso ht hsh hsep' P).convex

/-- `Pred` on a part, as a functor into **EA** with additive maps. -/
noncomputable def partPredMap {P Q : (asrtIdem ht hsh hsep').Part} (f : P ⟶ Q) :
    PCMHom (Pred Q) (Pred P) where
  toFun q := f ≫ q
  perp_map h := (FinPAC.ovee_comp h f).1
  ovee_map h := (FinPAC.ovee_comp h f).2

theorem partPredMap_id (P : (asrtIdem ht hsh hsep').Part) :
    partPredMap ht hsh hsep' (𝟙 P) = PCMHom.id (Pred P) :=
  PCMHom.ext' (funext fun q => Category.id_comp q)

theorem partPredMap_comp {P Q R : (asrtIdem ht hsh hsep').Part} (f : P ⟶ Q) (g : Q ⟶ R) :
    partPredMap ht hsh hsep' (f ≫ g) = (partPredMap ht hsh hsep' f).comp (partPredMap ht hsh hsep' g) :=
  PCMHom.ext' (funext fun q => Category.assoc _ _ q)

end PartPred

/-- The splitting of REC 95: REC 92 (state-separated case) at the idempotent
`s` of the Boolean part of the scalars. -/
noncomputable def dcSplitting (σs : ScalarSplit C) (hsep : SeparatingStates C) :
    CentralSplitting C :=
  asrtSplitting σs.hs (isSharp_of_states σs.hs hsep)
    (isSharp_of_states (orth_idem σs.hs) hsep) (Or.inl hsep)

/-- **REC 95**: `Pred : C₁ → OAᵒᵖ`. -/
noncomputable def rec95_oaFunctor (σs : ScalarSplit C) (hsep : SeparatingStates C) :
    (dcSplitting σs hsep).ε.Partᵒᵖ ⥤ OACat.{v} where
  obj P := @OACat.mk (Pred P.unop) (predEffectAlgebra P.unop)
    (partPred_isOrthoalgebra σs.hs (isSharp_of_states σs.hs hsep) (Or.inl hsep) P.unop
      (σs.isOrthoalgebra hsep _))
  map f := partPredMap σs.hs (isSharp_of_states σs.hs hsep) (Or.inl hsep) f.unop
  map_id P := partPredMap_id σs.hs (isSharp_of_states σs.hs hsep) (Or.inl hsep) P.unop
  map_comp f g := partPredMap_comp σs.hs (isSharp_of_states σs.hs hsep) (Or.inl hsep) g.unop f.unop

/-- **REC 95**: `Pred : C₂ → DCEA_cᵒᵖ`. -/
noncomputable def rec95_dcFunctor (σs : ScalarSplit C) (hdc : DirectedCompleteEffectus C)
    (hsep : SeparatingStates C) : (dcSplitting σs hsep).ε'.Partᵒᵖ ⥤ DCEACCat.{v} where
  obj P := @DCEACCat.mk (Pred P.unop) (predEffectAlgebra P.unop)
    (@partPredConvex _ _ _ _ _ _ _ _ _ _ _ (orth_idem σs.hs) (isSharp_of_states (orth_idem σs.hs) hsep)
      (Or.inl hsep) P.unop (σs.convex _))
    (partPred_directedComplete (orth_idem σs.hs) (isSharp_of_states (orth_idem σs.hs) hsep)
      (Or.inl hsep) P.unop (hdc _))
  map f := ⟨partPredMap (orth_idem σs.hs) (isSharp_of_states (orth_idem σs.hs) hsep) (Or.inl hsep) f.unop, fun l q => KCat.hom_ext
    (Category.assoc _ _ _).symm⟩
  map_id P := Subtype.ext
    (partPredMap_id (orth_idem σs.hs) (isSharp_of_states (orth_idem σs.hs) hsep) (Or.inl hsep) P.unop)
  map_comp f g := Subtype.ext (partPredMap_comp (orth_idem σs.hs)
    (isSharp_of_states (orth_idem σs.hs) hsep) (Or.inl hsep) g.unop f.unop)

/-- **REC 95** (`prop:splits-directed-complete`, short.tex:1720, Proposition): a
directed-complete effectus separated by states, with images and compatible
filters and comprehensions, is equivalent to a product of effectuses
`C ≅ C₁ × C₂`, and `Pred` gives functors `C₁ → OAᵒᵖ` and `C₂ → DCEA_cᵒᵖ`
(`rec95_oaFunctor`, `rec95_dcFunctor`).  The paper's proof: REC 92 at the
idempotent `s` splitting the scalars (REC 35), then REC 93 on the parts.  (The
last step of the print, `DCEA_c ≅ DCOUS`, is REC 42, not formalised.)  No
non-triviality of `s` is needed: if the scalars are purely Boolean or purely
convex, one factor is trivial. -/
theorem rec95 (h34 : EffectMonoidDCClassification.{v}) (hdc : DirectedCompleteEffectus C)
    (hsep : SeparatingStates C) :
    ∃ σs : ScalarSplit C,
      Nonempty (C ≌ (dcSplitting σs hsep).ε.Part × (dcSplitting σs hsep).ε'.Part) ∧
      (∀ P : (dcSplitting σs hsep).ε.Part, @IsOrthoalgebra (Pred P) (predEffectAlgebra P)) ∧
      (∀ P : (dcSplitting σs hsep).ε'.Part,
        @DirectedCompleteEA (Pred P) (predEffectAlgebra P) ∧
          Nonempty (@ConvexEA (Pred P) (predEffectAlgebra P))) := by
  obtain ⟨σs⟩ := scalarSplit_exists h34 hdc
  refine ⟨σs, ⟨CentralSplitting.equivalence _⟩, fun P => ?_, fun P => ⟨?_, ?_⟩⟩
  · exact partPred_isOrthoalgebra σs.hs (isSharp_of_states σs.hs hsep) (Or.inl hsep) P
      (σs.isOrthoalgebra hsep _)
  · exact partPred_directedComplete (orth_idem σs.hs) (isSharp_of_states (orth_idem σs.hs) hsep)
      (Or.inl hsep) P (hdc _)
  · exact ⟨@partPredConvex _ _ _ _ _ _ _ _ _ _ _ (orth_idem σs.hs)
      (isSharp_of_states (orth_idem σs.hs) hsep) (Or.inl hsep) P (σs.convex _)⟩

end DirectedCompleteSplit

/-! ## REC 96–97: sequential effect algebras -/

section SEALemmas

variable {E : Type u} [EffectAlgebra E] [SEA E]

theorem sea_seq_zero (a : E) : SEA.seq a 0 = 0 := by
  obtain ⟨h', e⟩ := SEA.seq_ovee a (PCM.zero_perp (0 : E))
  rw [PCM.zero_ovee] at e
  exact ovee_eq_self_left h' e.symm

theorem sea_zero_seq (a : E) : SEA.seq 0 a = 0 := SEA.seq_eq_zero a 0 (sea_seq_zero a)

theorem sea_seq_one (a : E) : SEA.seq a 1 = a := by
  have h := SEA.comm_orth (a := a) (b := 0) (by rw [sea_seq_zero, sea_zero_seq])
  rwa [eabasics_orth_zero, SEA.one_seq] at h

theorem sea_seq_split (a b : E) :
    ∃ h : Perp (SEA.seq a b) (SEA.seq a (orth b)), ovee (SEA.seq a b) (SEA.seq a (orth b)) h = a := by
  obtain ⟨h', e⟩ := SEA.seq_ovee a (EffectAlgebra.perp_orth b)
  rw [EffectAlgebra.ovee_orth, sea_seq_one] at e
  exact ⟨h', e.symm⟩

theorem sea_seq_le (a b : E) : SEA.seq a b ≼ a :=
  let ⟨h, e⟩ := sea_seq_split a b
  ⟨_, h, e⟩

/-- `a & a^⊥` is summable with itself (the first step of the proof of REC 96). -/
theorem sea_seq_orth_perp_self (a : E) : Perp (SEA.seq a (orth a)) (SEA.seq a (orth a)) := by
  have hc : SEA.seq a (orth a) = SEA.seq (orth a) a := SEA.comm_orth rfl
  have h1 : SEA.seq a (orth a) ≼ a := sea_seq_le _ _
  have h2 : SEA.seq a (orth a) ≼ orth a := by rw [hc]; exact sea_seq_le _ _
  obtain ⟨h3, -⟩ := eabasics_le_perp_compat h1 (EffectAlgebra.perp_orth a)
  obtain ⟨h4, -⟩ := eabasics_le_perp_compat h2 (PCM.perp_comm h3)
  exact PCM.perp_comm h4

theorem sea_idem_of_orth_zero {a : E} (h : SEA.seq a (orth a) = 0) : SEA.IsIdempotent a := by
  obtain ⟨h', e⟩ := sea_seq_split a a
  rw [PCM.ovee_congr rfl h h' (PCM.perp_zero _), PCM.ovee_zero] at e
  exact e

/-- An idempotent `p` absorbs every `a ≤ p`: `p & a = a & p = a`. -/
theorem sea_idem_absorb {p a : E} (hp : SEA.IsIdempotent p) (ha : a ≼ p) :
    SEA.seq p a = a ∧ SEA.seq a p = a := by
  have hpp : SEA.seq p (orth p) = 0 := by
    obtain ⟨h', e⟩ := sea_seq_split p p
    have hp' : SEA.seq p p = p := hp
    have h'' : Perp p (SEA.seq p (orth p)) := by rw [hp'] at h'; exact h'
    exact ovee_eq_self_left h'' ((PCM.ovee_congr hp'.symm rfl h'' h').trans e)
  have h1 : SEA.seq (orth p) p = 0 := SEA.seq_eq_zero _ _ hpp
  obtain ⟨c, hc, e⟩ := ha
  have h2 : SEA.seq (orth p) a = 0 := by
    obtain ⟨h', e'⟩ := SEA.seq_ovee (orth p) hc
    rw [e, h1] at e'
    exact (eabasics_positivity h' e'.symm).1
  have h3 : SEA.seq a (orth p) = 0 := SEA.seq_eq_zero _ _ h2
  have hap : SEA.seq a p = a := by
    obtain ⟨h', e'⟩ := sea_seq_split a p
    rw [PCM.ovee_congr rfl h3 h' (PCM.perp_zero _), PCM.ovee_zero] at e'
    exact e'
  have hcomm : SEA.seq a (orth (orth p)) = SEA.seq (orth (orth p)) a :=
    SEA.comm_orth (h3.trans h2.symm)
  rw [eabasics_orth_orth] at hcomm
  exact ⟨hcomm.symm.trans hap, hap⟩

end SEALemmas

/-- **SEA 44** (`prop:SEAsharpisBoolean`, second.tex:1121, cited by REC 96 as
"[second, Prop. 45]"), *the statement*: a SEA all of whose elements are
idempotent is a Boolean algebra (for its effect-algebra order) with `a & b = a ∧ b`.
Stated for REC's `SEA` class; it holds (`sea44_holds`), from
`Papers.SEA.sea44_booleanAlgebra`. -/
def SEABooleanIsBooleanAlgebra : Prop :=
  ∀ (E : Type u) [EffectAlgebra E] [SEA E], (∀ a : E, SEA.IsIdempotent a) →
    ∃ B : BooleanAlgebra E, letI := B; ∀ a b : E, (a ≼ b ↔ a ≤ b) ∧ SEA.seq a b = a ⊓ b

/-- SEA 44 holds: a REC-SEA is a SEA in the sense of `Papers.SEA` (thesis B's
225IV plus the first half of axiom e) for arbitrary `a, b`), and
`Papers.SEA.sea44_booleanAlgebra` applies. -/
theorem sea44_holds : SEABooleanIsBooleanAlgebra.{u} := by
  intro E _ _ hid
  letI : Papers.SEA.SEAlgebra E :=
    { SEA.toTree (E := E) with seq_comm_seq := fun ha hb => SEA.comm_seq ha hb }
  obtain ⟨B, hle, hseq, -⟩ := Papers.SEA.sea44_booleanAlgebra (E := E) hid
  exact ⟨B, fun a b => ⟨(hle a b).symm, hseq a b⟩⟩

section Rec96

variable {E : Type u} [EffectAlgebra E] [SEA E]

/-- **REC 96** (`lem:ortho-SEA-boolean`, short.tex:1772, Lemma), the in-house half:
in an orthoalgebra that is a SEA every element is idempotent — `a & a^⊥` is
summable with itself (`1 = (a ⊻ a^⊥) & (a ⊻ a^⊥) ≥ 2 (a & a^⊥)`), hence `0`, and
`a = a & a ⊻ a & a^⊥`. -/
theorem rec96_idempotent (hOA : IsOrthoalgebra E) (a : E) : SEA.IsIdempotent a :=
  sea_idem_of_orth_zero (hOA _ (sea_seq_orth_perp_self a))

/-- **REC 96** (`lem:ortho-SEA-boolean`, short.tex:1772, Lemma): an orthoalgebra
that is a SEA is a Boolean algebra with `a & b = a ∧ b`.  The paper's proof:
every element is idempotent (`rec96_idempotent`), and then SEA 44
(`sea44_holds`). -/
theorem rec96 (hOA : IsOrthoalgebra E) :
    ∃ B : BooleanAlgebra E, letI := B; ∀ a b : E, (a ≼ b ↔ a ≤ b) ∧ SEA.seq a b = a ⊓ b :=
  sea44_holds E (rec96_idempotent hOA)

end Rec96

/-- A Boolean algebra structure on a directed-complete effect algebra, whose
order is the effect-algebra order, is complete: `⋁ S` is the directed supremum
of the finite joins. -/
theorem boolean_complete_of_dc {E : Type u} [EffectAlgebra E] (B : BooleanAlgebra E)
    (hle : letI := B; ∀ a b : E, a ≼ b ↔ a ≤ b) (hdc : DirectedCompleteEA E) :
    letI := B; ∀ S : Set E, ∃ j : E, IsLUB S j := by
  letI := B
  classical
  intro S
  let D : Set E := { y | ∃ F : Finset E, (F : Set E) ⊆ S ∧ y = F.sup id }
  have hD : IsUpDirected D := by
    rintro _ ⟨F₁, h₁, rfl⟩ _ ⟨F₂, h₂, rfl⟩
    refine ⟨(F₁ ∪ F₂).sup id, ⟨F₁ ∪ F₂, by simp [Set.union_subset_iff, h₁, h₂], rfl⟩, ?_, ?_⟩
    · exact (hle _ _).2 (Finset.sup_mono Finset.subset_union_left)
    · exact (hle _ _).2 (Finset.sup_mono Finset.subset_union_right)
  obtain ⟨σ, hσ1, hσ2⟩ := hdc D hD
  refine ⟨σ, fun x hx => ?_, fun u hu => ?_⟩
  · have := hσ1 (({x} : Finset E).sup id) ⟨{x}, by simpa using hx, rfl⟩
    rw [Finset.sup_singleton] at this
    exact (hle _ _).1 this
  · refine (hle _ _).1 (hσ2 u ?_)
    rintro _ ⟨F, hF, rfl⟩
    exact (hle _ _).2 (Finset.sup_le fun x hx => hu (hF hx))

section Rec97

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

variable {t : Scal C} (ht : t ≫ t = t) {A : C} [SEA (Pred A)]

include ht in
/-- In the `t`-part, `t ∘ p^⊥ = (t ∘ 1) & p^⊥` once `t ∘ 1` is idempotent. -/
theorem part_orth_eq (hu : SEA.IsIdempotent (truth A ≫ t)) (y : PredPart ht A) :
    orth (y.1 : Pred A) ≫ t = SEA.seq (truth A ≫ t) (orth y.1) := by
  have hy : SEA.seq (truth A ≫ t) y.1 = y.1 := (sea_idem_absorb hu (PredPart.le_one ht y)).1
  obtain ⟨h1, e1⟩ := sea_seq_split (truth A ≫ t) y.1
  have h1' : Perp y.1 (SEA.seq (truth A ≫ t) (orth y.1)) := by
    have := h1; rw [hy] at this; exact this
  have e1' : ovee y.1 (SEA.seq (truth A ≫ t) (orth y.1)) h1' = truth A ≫ t :=
    (PCM.ovee_congr hy.symm rfl h1' h1).trans e1
  exact ovee_left_cancel (PredPart.perp_orth' ht y) h1' ((PredPart.ovee_orth' ht y).trans e1'.symm)

/-- The SEA structure of `Pred(A)` restricts to the `t`-part (a principal
downset below the idempotent `t ∘ 1`; the paper: "as `A_b` is a principal downset
and `p & q ≤ p`, `A_b` is also a SEA"), given that `t ∘ 1` is idempotent. -/
def partSEA (hu : SEA.IsIdempotent (truth A ≫ t)) : SEA (PredPart ht A) where
  seq x y := ⟨SEA.seq x.1 y.1, part_of_le ht x.2 (sea_seq_le _ _)⟩
  seq_ovee x {y z} h := by
    obtain ⟨h', e⟩ := SEA.seq_ovee x.1 (show Perp y.1 z.1 from h)
    exact ⟨h', Subtype.ext e⟩
  one_seq y := Subtype.ext (sea_idem_absorb hu (PredPart.le_one ht y)).1
  seq_eq_zero x y h := Subtype.ext (SEA.seq_eq_zero _ _ (congrArg Subtype.val h))
  comm_orth {x y} h := Subtype.ext (by
    show SEA.seq x.1 (orth (y.1 : Pred A) ≫ t) = SEA.seq (orth (y.1 : Pred A) ≫ t) x.1
    rw [part_orth_eq ht hu y]
    have hxu : SEA.seq x.1 (truth A ≫ t) = SEA.seq (truth A ≫ t) x.1 := by
      rw [(sea_idem_absorb hu (PredPart.le_one ht x)).1, (sea_idem_absorb hu (PredPart.le_one ht x)).2]
    exact SEA.comm_seq hxu (SEA.comm_orth (congrArg Subtype.val h)))
  comm_assoc {x y} h z := Subtype.ext (SEA.comm_assoc (congrArg Subtype.val h) z.1)
  comm_seq {a b c} ha hb :=
    Subtype.ext (SEA.comm_seq (congrArg Subtype.val ha) (congrArg Subtype.val hb))
  comm_ovee {a b c} h ha hb :=
    Subtype.ext (SEA.comm_ovee (show Perp a.1 b.1 from h) (congrArg Subtype.val ha)
      (congrArg Subtype.val hb))

include ht in
/-- In an orthoalgebraic `t`-part every element is idempotent for the SEA of
`Pred(A)` (the argument of REC 96, run inside `Pred(A)`). -/
theorem part_idem (hOA : IsOrthoalgebra (PredPart ht A)) (x : PredPart ht A) :
    SEA.IsIdempotent x.1 := by
  refine sea_idem_of_orth_zero ?_
  have hm : SEA.seq x.1 (orth x.1) ≫ t = SEA.seq x.1 (orth x.1) :=
    part_of_le ht x.2 (sea_seq_le _ _)
  exact congrArg Subtype.val (hOA ⟨_, hm⟩ (sea_seq_orth_perp_self x.1))

/-- **REC 97** (`prop:boolean-and-convex`, short.tex:1786, Proposition): in a
directed-complete effectus with separating states, if `Pred(A)` is a normal SEA
then `Pred(A) ≅ A_b ⊕ A_c` with `A_b` a complete Boolean algebra and `A_c` a
(directed-complete) convex effect algebra.  The paper's proof: REC 93 gives
`A_b` an orthoalgebra and `A_c` convex; `A_b` is a principal downset closed under
`&`, so a SEA (`partSEA`, once its top `s ∘ 1` is known to be idempotent, which
`part_idem` gives), hence Boolean by REC 96.  Completeness, which the paper does
not argue, holds because `A_b` is directed complete (`boolean_complete_of_dc`);
normality of the SEA is not used.  ("More specifically the unit interval of a
directed-complete order unit space" is REC 42, not formalised.) -/
theorem rec97 (h34 : EffectMonoidDCClassification.{v})
    (hdc : DirectedCompleteEffectus C) (hsep : SeparatingStates C) (A : C) [SEA (Pred A)]
    (_hn : IsNormalSEA (Pred A)) :
    ∃ σs : ScalarSplit C,
      Nonempty (EAIso (Pred A) (PredPart σs.hs A × PredPart (orth_idem σs.hs) A)) ∧
      (∃ B : BooleanAlgebra (PredPart σs.hs A), letI := B;
        (∀ a b : PredPart σs.hs A, (a ≼ b ↔ a ≤ b)) ∧ ∀ S : Set (PredPart σs.hs A), ∃ j, IsLUB S j) ∧
      Nonempty (ConvexEA (PredPart (orth_idem σs.hs) A)) ∧
      DirectedCompleteEA (PredPart (orth_idem σs.hs) A) := by
  obtain ⟨σs⟩ := scalarSplit_exists h34 hdc
  have hOA := σs.isOrthoalgebra hsep A
  have hid := part_idem σs.hs hOA
  have hu : SEA.IsIdempotent (truth A ≫ σs.s) := hid 1
  letI : SEA (PredPart σs.hs A) := partSEA σs.hs hu
  obtain ⟨B, hB⟩ := rec96 hOA
  refine ⟨σs, ⟨predSplitIso σs.hs A⟩, ⟨B, fun a b => (hB a b).1, ?_⟩, ⟨σs.convex A⟩,
    PredPart.directedComplete _ (hdc A)⟩
  exact boolean_complete_of_dc B (fun a b => (hB a b).1)
    (PredPart.directedComplete _ (hdc A))

end Rec97

/-! ## REC 98: finite tomography -/

/-- **REC 98** (`def:finite-tomography`, short.tex:1811, Definition): an effectus
has **finite tomography** when every object `A` has finitely many predicates
`p₁, …, p_k` with `f = g ⟺ ∀ i, p_i ∘ f = p_i ∘ g` for all `f, g : B → A`. -/
def FiniteTomography (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop :=
  ∀ A : C, ∃ (k : ℕ) (p : Fin k → Pred A), ∀ {B : C} (f g : B ⟶ A),
    f = g ↔ ∀ i, f ≫ p i = g ≫ p i

/-! ## The effectus `BoolMat M` of Boolean matrices

For a complete Boolean algebra `M`: objects are finite sets, morphisms
`X → Y` are the `M`-valued matrices whose rows consist of pairwise disjoint
entries (the Kleisli category of the subdistribution monad `𝒟_{≤M}` on finite
sets, for Boolean `M`), composed by `(g ∘ f)(x, z) = ⋁_y f(x, y) ∧ g(y, z)`.
It is an effectus in partial form with `I = 1`, predicates `Pred(X) = M^X`, and
scalars `Pred(I) = M`.  It is directed complete, separated by states (the point
states), has finite tomography (the point predicates), and every element of `M`
is an idempotent scalar — the counterexample to REC 99 and to the state clause
of REC 89. -/

section BoolMat

/-- The objects of `BoolMat M`: finite sets (`M` is a parameter only, fixing the
morphisms). -/
@[nolint unusedArguments]
structure BoolMat (M : Type) where
  carrier : Type
  [fin : Finite carrier]

variable (M : Type) [CompleteBooleanAlgebra M]

attribute [instance] BoolMat.fin

namespace BoolMat

variable {M}

/-- The morphisms: row-disjoint `M`-valued matrices. -/
@[ext] structure Hom (X Y : BoolMat M) where
  m : X.carrier → Y.carrier → M
  disj : ∀ x y y', y ≠ y' → m x y ⊓ m x y' = ⊥

open scoped Classical in
/-- The Kronecker delta. -/
noncomputable def δ {α : Type} (a b : α) : M := if a = b then ⊤ else ⊥

theorem iSup_δ_inf {α : Type} (a : α) (f : α → M) : ⨆ y, δ a y ⊓ f y = f a := by
  refine le_antisymm (iSup_le fun y => ?_) (le_iSup_of_le a (by simp [δ]))
  by_cases h : a = y
  · subst h; simp [δ]
  · simp [δ, h]

theorem iSup_inf_δ {α : Type} (f : α → M) (b : α) : ⨆ y, f y ⊓ δ y b = f b := by
  refine le_antisymm (iSup_le fun y => ?_) (le_iSup_of_le b (by simp [δ]))
  by_cases h : y = b
  · subst h; simp [δ]
  · simp [δ, h]

theorem δ_disj {α : Type} (x y y' : α) (h : y ≠ y') : δ (M := M) x y ⊓ δ x y' = ⊥ := by
  by_cases hx : x = y
  · subst hx; simp [δ, h]
  · simp [δ, hx]

theorem comp_disj {X Y Z : BoolMat M} (f : Hom X Y) (g : Hom Y Z) (x : X.carrier)
    (z z' : Z.carrier) (hz : z ≠ z') :
    (⨆ y, f.m x y ⊓ g.m y z) ⊓ (⨆ y, f.m x y ⊓ g.m y z') = ⊥ := by
  rw [iSup_inf_eq]
  refine le_bot_iff.1 (iSup_le fun y => ?_)
  rw [inf_iSup_eq]
  refine iSup_le fun y' => ?_
  by_cases hy : y = y'
  · subst hy
    exact le_of_le_of_eq (inf_le_inf inf_le_right inf_le_right) (g.disj y z z' hz)
  · exact le_of_le_of_eq (inf_le_inf inf_le_left inf_le_left) (f.disj x y y' hy)

noncomputable instance category : Category.{0} (BoolMat M) where
  Hom := Hom
  id X := ⟨δ, δ_disj⟩
  comp f g := ⟨fun x z => ⨆ y, f.m x y ⊓ g.m y z, comp_disj f g⟩
  id_comp f := Hom.ext (funext₂ fun x z => iSup_δ_inf x (fun y => f.m y z))
  comp_id f := Hom.ext (funext₂ fun x z => iSup_inf_δ (fun y => f.m x y) z)
  assoc f g h := Hom.ext (funext₂ fun x w => by
    show ⨆ z, (⨆ y, f.m x y ⊓ g.m y z) ⊓ h.m z w = ⨆ y, f.m x y ⊓ ⨆ z, g.m y z ⊓ h.m z w
    simp only [iSup_inf_eq, inf_iSup_eq, inf_assoc]
    exact iSup_comm)

theorem comp_m {X Y Z : BoolMat M} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.carrier) (z : Z.carrier) :
    Hom.m (f ≫ g) x z = ⨆ y, f.m x y ⊓ g.m y z := rfl

theorem id_m (X : BoolMat M) (x y : X.carrier) : Hom.m (𝟙 X) x y = δ x y := rfl

/-! ### Explicit coproducts -/

noncomputable abbrev sumObj (X Y : BoolMat M) : BoolMat M := ⟨X.carrier ⊕ Y.carrier⟩

noncomputable def inl (X Y : BoolMat M) : X ⟶ sumObj X Y :=
  (⟨fun x w => Sum.elim (fun x' => δ x x') (fun _ => ⊥) w, by
    rintro x (a | a) (b | b) h
    · exact δ_disj x a b (fun e => h (e ▸ rfl))
    all_goals simp⟩ : Hom X (sumObj X Y))

noncomputable def inr (X Y : BoolMat M) : Y ⟶ sumObj X Y :=
  (⟨fun y w => Sum.elim (fun _ => ⊥) (fun y' => δ y y') w, by
    rintro y (a | a) (b | b) h
    · simp
    · simp
    · simp
    · exact δ_disj y a b (fun e => h (e ▸ rfl))⟩ : Hom Y (sumObj X Y))

noncomputable def desc {X Y T : BoolMat M} (f : X ⟶ T) (g : Y ⟶ T) : sumObj X Y ⟶ T :=
  (⟨fun w z => Sum.elim (fun x => f.m x z) (fun y => g.m y z) w, by
    rintro (a | a) z z' h
    · exact f.disj a z z' h
    · exact g.disj a z z' h⟩ : Hom (sumObj X Y) T)

noncomputable abbrev initObj : BoolMat M := ⟨Empty⟩

noncomputable def explicit : ExplicitCoproducts (BoolMat M) where
  pt := sumObj
  inl := inl
  inr := inr
  desc := desc
  inl_desc {X Y T} f g := Hom.ext (funext₂ fun x z => by
    show ⨆ w, _ ⊓ _ = _
    rw [iSup_sum]
    simp only [inl, desc, Sum.elim_inl, Sum.elim_inr, bot_inf_eq, iSup_bot, sup_bot_eq]
    exact iSup_δ_inf x (fun y => f.m y z))
  inr_desc {X Y T} f g := Hom.ext (funext₂ fun y z => by
    show ⨆ w, _ ⊓ _ = _
    rw [iSup_sum]
    simp only [inr, desc, Sum.elim_inl, Sum.elim_inr, bot_inf_eq, iSup_bot, bot_sup_eq]
    exact iSup_δ_inf y (fun y' => g.m y' z))
  uniq {X Y T} m := Hom.ext (funext₂ fun w z => by
    rcases w with x | y
    · show m.m (Sum.inl x) z = ⨆ w, _ ⊓ _
      rw [iSup_sum]
      simp only [inl, Sum.elim_inl, Sum.elim_inr, bot_inf_eq, iSup_bot, sup_bot_eq]
      exact (iSup_δ_inf x (fun a => m.m (Sum.inl a) z)).symm
    · show m.m (Sum.inr y) z = ⨆ w, _ ⊓ _
      rw [iSup_sum]
      simp only [inr, Sum.elim_inl, Sum.elim_inr, bot_inf_eq, iSup_bot, bot_sup_eq]
      exact (iSup_δ_inf y (fun a => m.m (Sum.inr a) z)).symm)
  init := initObj
  isInitial := IsInitial.ofUniqueHom
    (fun T => (⟨fun x => x.elim, fun x => x.elim⟩ : Hom initObj T))
    (fun T m => Hom.ext (funext fun x => x.elim))

instance hasFiniteCoproducts : HasFiniteCoproducts (BoolMat M) :=
  (explicit (M := M)).hasFiniteCoproducts

/-! ### The PCM enrichment -/

theorem ovee_disj {X Y : BoolMat M} (f g : Hom X Y) (h : ∀ x y y', f.m x y ⊓ g.m x y' = ⊥)
    (x : X.carrier) (y y' : Y.carrier) (hy : y ≠ y') :
    (f.m x y ⊔ g.m x y) ⊓ (f.m x y' ⊔ g.m x y') = ⊥ := by
  have h1 := f.disj x y y' hy
  have h2 := g.disj x y y' hy
  have h3 := h x y y'
  have h4 : g.m x y ⊓ f.m x y' = ⊥ := by rw [inf_comm]; exact h x y' y
  simp only [inf_sup_left, inf_sup_right, h1, h2, h3, h4, sup_bot_eq]

noncomputable instance homPCM (X Y : BoolMat M) : PCM (X ⟶ Y) where
  zero := (⟨fun _ _ => ⊥, fun _ _ _ _ => bot_inf_eq _⟩ : Hom X Y)
  Perp f g := ∀ x y y', f.m x y ⊓ g.m x y' = ⊥
  ovee f g h := (⟨fun x y => f.m x y ⊔ g.m x y, ovee_disj f g h⟩ : Hom X Y)
  perp_comm h x y y' := by rw [inf_comm]; exact h x y' y
  ovee_comm h := Hom.ext (funext₂ fun _ _ => sup_comm _ _)
  perp_of_ovee_perp hab h x y y' :=
    le_bot_iff.1 (le_trans (inf_le_inf_right _ le_sup_right) (h x y y').le)
  perp_ovee_of_ovee_perp {a b c} hab h x y y' := by
    have hac : a.m x y ⊓ c.m x y' = ⊥ :=
      le_bot_iff.1 (le_trans (inf_le_inf_right _ le_sup_left) (h x y y').le)
    show a.m x y ⊓ (b.m x y' ⊔ c.m x y') = ⊥
    rw [inf_sup_left, hab x y y', hac, sup_bot_eq]
  ovee_assoc hab h := Hom.ext (funext₂ fun _ _ => sup_assoc _ _ _)
  zero_perp a x y y' := bot_inf_eq _
  zero_ovee a := Hom.ext (funext₂ fun _ _ => bot_sup_eq _)

theorem zero_m {X Y : BoolMat M} (x : X.carrier) (y : Y.carrier) :
    Hom.m (0 : X ⟶ Y) x y = ⊥ := rfl

theorem ovee_m {X Y : BoolMat M} {f g : X ⟶ Y} (h : Perp f g) (x : X.carrier) (y : Y.carrier) :
    Hom.m (ovee f g h : X ⟶ Y) x y = f.m x y ⊔ g.m x y := rfl

theorem perp_iff {X Y : BoolMat M} (f g : X ⟶ Y) :
    Perp f g ↔ ∀ x y y', f.m x y ⊓ g.m x y' = ⊥ := Iff.rfl

/-- A bound for the iterated suprema in composites. -/
theorem iSup_inf_iSup_le {α β : Type} (a : α → M) (b : β → M) (c : M)
    (h : ∀ i j, a i ⊓ b j ≤ c) : (⨆ i, a i) ⊓ (⨆ j, b j) ≤ c := by
  rw [iSup_inf_eq]
  refine iSup_le fun i => ?_
  rw [inf_iSup_eq]
  exact iSup_le fun j => h i j

noncomputable instance finPAC : FinPAC (BoolMat M) :=
  (explicit (M := M)).finPAC_of
    (fun {X Y Z f g} h k => by
      refine ⟨fun x z z' => le_bot_iff.1 (iSup_inf_iSup_le _ _ _ fun y y' =>
        le_of_le_of_eq (inf_le_inf inf_le_left inf_le_left) (h x y y')), ?_⟩
      exact Hom.ext (funext₂ fun x z => by
        show ⨆ y, (f.m x y ⊔ g.m x y) ⊓ k.m y z = (⨆ y, f.m x y ⊓ k.m y z) ⊔ ⨆ y, g.m x y ⊓ k.m y z
        simp only [inf_sup_right, iSup_sup_eq]))
    (fun {W X Y f g} h k => by
      refine ⟨fun w y y' => le_bot_iff.1 (iSup_inf_iSup_le _ _ _ fun x x' => ?_), ?_⟩
      · by_cases hx : x = x'
        · subst hx
          exact le_of_le_of_eq (inf_le_inf inf_le_right inf_le_right) (h x y y')
        · exact le_of_le_of_eq (inf_le_inf inf_le_left inf_le_left) (k.disj w x x' hx)
      · exact Hom.ext (funext₂ fun w y => by
          show ⨆ x, k.m w x ⊓ (f.m x y ⊔ g.m x y) = (⨆ x, k.m w x ⊓ f.m x y) ⊔ ⨆ x, k.m w x ⊓ g.m x y
          simp only [inf_sup_left, iSup_sup_eq]))
    (fun f => Hom.ext (funext₂ fun x z => by
      show ⨆ y, f.m x y ⊓ ⊥ = ⊥
      simp))
    (fun f => Hom.ext (funext₂ fun x z => by
      show ⨆ y, ⊥ ⊓ f.m y z = ⊥
      simp))
    (fun {X Y} b => fun x y y' => by
      show (⨆ w, b.m x w ⊓ Hom.m (desc (𝟙 Y) 0) w y) ⊓ (⨆ w, b.m x w ⊓ Hom.m (desc 0 (𝟙 Y)) w y') = ⊥
      refine le_bot_iff.1 (iSup_inf_iSup_le _ _ _ fun w w' => ?_)
      rcases w with a | a <;> rcases w' with c | c
      · exact le_of_le_of_eq (inf_le_inf le_rfl inf_le_right) (by simp [desc, zero_m])
      · exact le_of_le_of_eq (inf_le_inf inf_le_left inf_le_left)
          (b.disj x (Sum.inl a) (Sum.inr c) Sum.inl_ne_inr)
      · exact le_of_le_of_eq (inf_le_inf inf_le_right le_rfl) (by simp [desc, zero_m])
      · exact le_of_le_of_eq (inf_le_inf le_rfl inf_le_right) (by simp [desc, zero_m]))
    (fun {X Y f g} h => fun x w w' => by
      show (⨆ y, f.m x y ⊓ Hom.m (inl Y Y) y w) ⊓ (⨆ y, g.m x y ⊓ Hom.m (inr Y Y) y w') = ⊥
      refine le_bot_iff.1 (iSup_inf_iSup_le _ _ _ fun y y' => ?_)
      rcases w with a | a <;> rcases w' with c | c
      · exact le_of_le_of_eq (inf_le_inf le_rfl inf_le_right) (by simp [inr])
      · exact le_of_le_of_eq (inf_le_inf inf_le_left inf_le_left) (h x y y')
      · exact le_of_le_of_eq (inf_le_inf inf_le_right le_rfl) (by simp [inl])
      · exact le_of_le_of_eq (inf_le_inf inf_le_right le_rfl) (by simp [inl]))

/-! ### The effects -/

/-- The unit object `I = 1`. -/
noncomputable abbrev unitObj : BoolMat M := ⟨Unit⟩

noncomputable instance effectus : EffectusPartialForm (BoolMat M) where
  I := unitObj
  one X := (⟨fun _ _ => ⊤, fun _ u u' h => absurd rfl h⟩ : Hom X unitObj)
  orth {X} p := (⟨fun x u => (p.m x u)ᶜ, fun _ u u' h => absurd rfl h⟩ :
    Hom X unitObj)
  perp_orth p x u u' := by
    obtain rfl : u = u' := rfl
    exact inf_compl_self _
  ovee_orth p := Hom.ext (funext₂ fun x u => sup_compl_eq_top)
  orth_unique {X p q} h e := Hom.ext (funext₂ fun x u => by
    have h1 : p.m x u ⊓ q.m x u = ⊥ := h x u u
    have h2 : p.m x u ⊔ q.m x u = ⊤ := congrFun (congrFun (congrArg Hom.m e) x) u
    exact (IsCompl.of_eq h1 h2).symm.eq_compl)
  eq_zero_of_perp_one {X p} h := Hom.ext (funext₂ fun x u => by
    have := h x u u
    show p.m x u = ⊥
    simpa using this)
  perp_of_one_perp {X Y f g} h x y y' := by
    have h' := h x () ()
    refine le_bot_iff.1 (le_trans ?_ h'.le)
    exact inf_le_inf (le_iSup_of_le y (by simp)) (le_iSup_of_le y' (by simp))
  eq_zero_of_one_zero {X Y f} h := Hom.ext (funext₂ fun x y => by
    have h' : (⨆ y, f.m x y ⊓ ⊤) = ⊥ := congrFun (congrFun (congrArg Hom.m h) x) ()
    exact le_bot_iff.1 (le_trans (le_iSup_of_le y (by simp)) h'.le))

theorem truth_m (X : BoolMat M) (x : X.carrier) (u : Unit) : Hom.m (truth X) x u = ⊤ := rfl

/-- The order of `Pred(X) = M^X` is the pointwise one. -/
theorem pred_le_iff {X : BoolMat M} (p q : Pred X) : p ≼ q ↔ ∀ x u, p.m x u ≤ q.m x u := by
  constructor
  · rintro ⟨c, hc, rfl⟩ x u
    exact le_sup_left
  · intro h
    refine ⟨(⟨fun x u => q.m x u \ p.m x u, fun _ u u' hu => absurd rfl hu⟩ :
      Hom X unitObj), fun x u u' => ?_, Hom.ext (funext₂ fun x u => ?_)⟩
    · obtain rfl : u = u' := rfl
      exact inf_sdiff_self_right
    · exact sup_sdiff_cancel_right (h x u)

/-- `BoolMat M` is directed complete (every subset of `M^X` has a supremum). -/
theorem directedComplete : DirectedCompleteEffectus (BoolMat M) := by
  intro X D _
  refine ⟨(⟨fun x u => ⨆ p ∈ D, Hom.m p x u,
    fun _ u u' hu => absurd rfl hu⟩ : Hom X unitObj), fun p hp => ?_,
    fun q hq => ?_⟩
  · exact (pred_le_iff _ _).2 fun x u => le_iSup₂_of_le p hp le_rfl
  · exact (pred_le_iff _ _).2 fun x u => iSup₂_le fun p hp => (pred_le_iff _ _).1 (hq p hp) x u

/-- The point state `δ_x : I → X`. -/
noncomputable def pointState {X : BoolMat M} (x : X.carrier) : Stat X :=
  ⟨(⟨fun _ y => δ x y, fun _ y y' h => δ_disj x y y' h⟩ : Hom unitObj X),
    Hom.ext (funext₂ fun _ _ => by
      show ⨆ y, δ x y ⊓ ⊤ = ⊤
      exact le_antisymm le_top (le_iSup_of_le x (by simp [δ])))⟩

theorem pointState_comp {X Y : BoolMat M} (x : X.carrier) (f : X ⟶ Y) (y : Y.carrier) :
    Hom.m ((pointState x).1 ≫ f) () y = f.m x y :=
  iSup_δ_inf x (fun z => f.m z y)

/-- `BoolMat M` is separated by states: the point states give the rows. -/
theorem separatingStates : SeparatingStates (BoolMat M) := by
  intro X Y f g h
  exact Hom.ext (funext₂ fun x y => by
    rw [← pointState_comp x f y, ← pointState_comp x g y, h (pointState x)])

/-- The point predicate `δ_y : X → I`. -/
noncomputable def pointPred {X : BoolMat M} (y : X.carrier) : Pred X :=
  (⟨fun z _ => δ z y, fun _ u u' hu => absurd rfl hu⟩ : Hom X unitObj)

/-- `BoolMat M` has finite tomography (REC 98): the point predicates of a finite
set separate its incoming maps, `(δ_y ∘ f)(x) = f(x, y)`. -/
theorem finiteTomography : FiniteTomography (BoolMat M) := by
  intro X
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin X.carrier
  refine ⟨k, fun i => pointPred (e.symm i), fun f g => ⟨fun h i => h ▸ rfl, fun h => ?_⟩⟩
  refine Hom.ext (funext₂ fun b y => ?_)
  have := congrFun (congrFun (congrArg Hom.m (h (e y))) b) ()
  simp only [Equiv.symm_apply_apply] at this
  have e1 : Hom.m (f ≫ pointPred y) b () = f.m b y := iSup_inf_δ (fun z => f.m b z) y
  have e2 : Hom.m (g ≫ pointPred y) b () = g.m b y := iSup_inf_δ (fun z => g.m b z) y
  rw [← e1, ← e2]
  exact this

/-- The scalars `Pred(I)` are `M`: `σ ↦ σ(∗, ∗)` is an order isomorphism. -/
theorem scal_bijective : Function.Bijective (fun σ : Scal (BoolMat M) => Hom.m σ () ()) := by
  refine ⟨fun σ τ h => Hom.ext (funext₂ fun u u' => ?_), fun a => ?_⟩
  · obtain rfl : u = () := rfl
    obtain rfl : u' = () := rfl
    exact h
  · exact ⟨(⟨fun _ _ => a, fun _ u u' hu => absurd rfl hu⟩ :
      Hom unitObj unitObj), rfl⟩

theorem scal_le_iff (σ τ : Scal (BoolMat M)) : σ ≼ τ ↔ Hom.m σ () () ≤ Hom.m τ () () := by
  rw [pred_le_iff]
  exact ⟨fun h => h () (), fun h x u => h⟩

/-- Every element `a ∈ M` gives an idempotent scalar, non-trivial when
`a ∉ {⊥, ⊤}`. -/
theorem idempotent_scalar (a : M) (ha0 : a ≠ ⊥) (ha1 : a ≠ ⊤) :
    ∃ s : Scal (BoolMat M), s ≫ s = s ∧ s ≠ 0 ∧ s ≠ 𝟙 _ := by
  let s : Scal (BoolMat M) :=
    (⟨fun _ _ => a, fun _ u u' hu => absurd rfl hu⟩ : Hom unitObj unitObj)
  refine ⟨s, Hom.ext (funext₂ fun _ _ => ?_), fun h => ha0 ?_, fun h => ha1 ?_⟩
  · show ⨆ _ : Unit, a ⊓ a = a
    simp
  · exact congrFun (congrFun (congrArg Hom.m h) ()) ()
  · have e : a = δ (M := M) () () := congrFun (congrFun (congrArg Hom.m h) ()) ()
    simpa [δ] using e

end BoolMat

end BoolMat

/-! ## REC 99 is false as printed; REC 89 (states) is false as printed -/

/-- **REC 89**, second bullet, **refuted**: there is an effectus separated by
states whose Karoubi envelope is not (`BoolMat 𝒫(ℕ)`, with the idempotent scalar
`{0}`; `rec89_states_not_preserved`). -/
theorem rec89_states_false_as_printed :
    ∃ (C : Type 1) (_ : Category.{0} C) (_ : HasFiniteCoproducts C)
      (_ : ∀ X Y : C, PCM (X ⟶ Y)) (_ : FinPAC C) (_ : EffectusPartialForm C),
      SeparatingStates C ∧ ¬ SeparatingStates (Split C) := by
  refine ⟨BoolMat (Set ℕ), inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, BoolMat.separatingStates, ?_⟩
  obtain ⟨s, hs, h0, h1⟩ := BoolMat.idempotent_scalar ({0} : Set ℕ)
    (Set.singleton_nonempty 0).ne_empty (fun h => by
      have : (1 : ℕ) ∈ ({0} : Set ℕ) := h ▸ Set.mem_univ 1
      simp at this)
  exact rec89_states_not_preserved hs h0 h1

/-- The conclusion of REC 99, read as weakly as possible: `Pred(I)` is
order-isomorphic to `𝒫(A) ⊕ [0,1]^n` for a finite `A` (an isomorphism of effect
algebras or of effect monoids is in particular an order isomorphism). -/
def REC99Conclusion (C : Type 1) [Category.{0} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop :=
  ∃ (A : Type) (_ : Finite A) (n : ℕ) (f : Scal C → Set A × (Fin n → unitInterval)),
    Function.Bijective f ∧ ∀ a b : Scal C, a ≼ b ↔ f a ≤ f b

/-- `𝒫(ℕ)` is not order-isomorphic to `𝒫(A) × [0,1]^n` with `A` finite: for
`n = 0` the right side is finite; for `n ≥ 1` the element `(∅, ½, …, ½)` has no
complement, while every element of `𝒫(ℕ)` has one. -/
theorem powerset_nat_not_orderIso (A : Type) [Finite A] (n : ℕ)
    (g : Set ℕ → Set A × (Fin n → unitInterval)) (hg : Function.Bijective g)
    (hle : ∀ a b, a ≤ b ↔ g a ≤ g b) : False := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Finite (Set ℕ) := Finite.of_injective g hg.1
    exact not_finite (Set ℕ)
  let e : Set ℕ ≃ Set A × (Fin n → unitInterval) := Equiv.ofBijective g hg
  have hle' : ∀ a b, e.symm a ≤ e.symm b ↔ a ≤ b := fun a b => by
    rw [hle, Equiv.ofBijective_apply_symm_apply g hg, Equiv.ofBijective_apply_symm_apply g hg]
  let half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  let i₀ : Fin n := ⟨0, hn⟩
  let y : Set A × (Fin n → unitInterval) := (∅, fun _ => half)
  let x := e.symm y
  let y' := g xᶜ
  have hy'x : e.symm y' = xᶜ := e.symm_apply_apply _
  -- the bottom and top of the right side
  have hbot : ∀ w, g ⊥ ≤ w := fun w => (hle' (g ⊥) w).1 (by
    rw [show e.symm (g ⊥) = ⊥ from e.symm_apply_apply ⊥]; exact bot_le)
  have htop : ∀ w, w ≤ g ⊤ := fun w => (hle' w (g ⊤)).1 (by
    rw [show e.symm (g ⊤) = ⊤ from e.symm_apply_apply ⊤]; exact le_top)
  -- `z = y ⊓ y'` lies below both, so its preimage is `≤ x ⊓ xᶜ = ⊥`
  let z : Set A × (Fin n → unitInterval) :=
    (∅, fun i => ⟨min (1 / 2) (y'.2 i : ℝ), le_min (by norm_num) (y'.2 i).2.1,
      le_trans (min_le_left _ _) (by norm_num)⟩)
  have hz1 : e.symm z ≤ x := (hle' z y).2
    ⟨le_rfl, fun i => show min (1 / 2) (y'.2 i : ℝ) ≤ 1 / 2 from min_le_left _ _⟩
  have hz2 : e.symm z ≤ xᶜ := hy'x ▸ (hle' z y').2
    ⟨Set.empty_subset _, fun i => show min (1 / 2) (y'.2 i : ℝ) ≤ y'.2 i from min_le_right _ _⟩
  have hzb : e.symm z = ⊥ := le_bot_iff.1 (le_trans (le_inf hz1 hz2) (inf_compl_self x).le)
  have hz : z = g ⊥ := by rw [← hzb]; exact (e.apply_symm_apply z).symm
  have h0 : (y'.2 i₀ : ℝ) = 0 := by
    have h1 : z ≤ (∅, fun _ => (0 : unitInterval)) := by rw [hz]; exact hbot _
    have h2 : min (1 / 2) (y'.2 i₀ : ℝ) ≤ 0 := h1.2 i₀
    have h3 := (y'.2 i₀).2.1
    rcases min_choice (1 / 2 : ℝ) (y'.2 i₀ : ℝ) with h | h <;> rw [h] at h2
    · norm_num at h2
    · linarith
  -- `w = y ⊔ y'` lies above both, so its preimage is `≥ x ⊔ xᶜ = ⊤`
  let w : Set A × (Fin n → unitInterval) :=
    (Set.univ, fun i => ⟨max (1 / 2) (y'.2 i : ℝ), le_trans (by norm_num) (le_max_left _ _),
      max_le (by norm_num) (y'.2 i).2.2⟩)
  have hw1 : x ≤ e.symm w := (hle' y w).2
    ⟨Set.empty_subset _, fun i => show (1 / 2 : ℝ) ≤ max (1 / 2) (y'.2 i : ℝ) from le_max_left _ _⟩
  have hw2 : xᶜ ≤ e.symm w := hy'x ▸ (hle' y' w).2
    ⟨Set.subset_univ _, fun i => show (y'.2 i : ℝ) ≤ max (1 / 2) (y'.2 i : ℝ) from le_max_right _ _⟩
  have hwt : e.symm w = ⊤ := top_le_iff.1 (le_trans (sup_compl_eq_top (x := x)).ge (sup_le hw1 hw2))
  have hw : w = g ⊤ := by rw [← hwt]; exact (e.apply_symm_apply w).symm
  have h1 : (Set.univ, fun _ => (1 : unitInterval)) ≤ w := by rw [hw]; exact htop _
  have h2 : (1 : ℝ) ≤ max (1 / 2) (y'.2 i₀ : ℝ) := h1.2 i₀
  rw [h0] at h2
  norm_num at h2

/-- **REC 99** (short.tex:1816, Proposition) **is false as printed**: "a
directed-complete effectus with finite tomography has `Pred(I) ≅ 𝒫(A) ⊕ [0,1]^n`
for a finite set `A` and `n ∈ ℕ`".  Counterexample: `BoolMat 𝒫(ℕ)` (finite sets
and `𝒫(ℕ)`-valued row-disjoint matrices, i.e. `Kl(𝒟_M)` on finite sets for
`M = 𝒫(ℕ)`) is directed complete and has finite tomography (the point
predicates), but its scalars are `𝒫(ℕ)`, which is not even order-isomorphic to
`𝒫(A) × [0,1]^n` with `A` finite (`powerset_nat_not_orderIso`).  The printed
proof's error: at the object `I` finite tomography is witnessed by `p = id_I`
alone, so "the `p_i` separate `Pred(I)`" constrains nothing. -/
theorem rec99_false_as_printed :
    ¬ ∀ (C : Type 1) [Category.{0} C] [HasFiniteCoproducts C] [∀ X Y : C, PCM (X ⟶ Y)]
      [FinPAC C] [EffectusPartialForm C],
      DirectedCompleteEffectus C → FiniteTomography C → REC99Conclusion C := by
  intro h
  obtain ⟨A, hA, n, f, hf, hle⟩ :=
    h (BoolMat (Set ℕ)) BoolMat.directedComplete BoolMat.finiteTomography
  let φ : Scal (BoolMat (Set ℕ)) → Set ℕ := fun σ => BoolMat.Hom.m σ () ()
  let e := Equiv.ofBijective φ (BoolMat.scal_bijective (M := Set ℕ))
  refine powerset_nat_not_orderIso A n (f ∘ e.symm) (hf.comp e.symm.bijective) fun a b => ?_
  have ha : BoolMat.Hom.m (e.symm a) () () = a := e.apply_symm_apply a
  have hb : BoolMat.Hom.m (e.symm b) () () = b := e.apply_symm_apply b
  show a ≤ b ↔ f (e.symm a) ≤ f (e.symm b)
  rw [← hle, BoolMat.scal_le_iff, ha, hb]

/-- **REC 99**: more generally, finite tomography puts no constraint on a
complete Boolean algebra of scalars — for every complete Boolean algebra `M`
there is a directed-complete effectus with finite tomography, separated by
states, whose scalars are order-isomorphic to `M`. -/
theorem rec99_any_boolean_scalars (M : Type) [CompleteBooleanAlgebra M] :
    DirectedCompleteEffectus (BoolMat M) ∧ FiniteTomography (BoolMat M) ∧
      SeparatingStates (BoolMat M) ∧
      ∃ f : Scal (BoolMat M) → M, Function.Bijective f ∧ ∀ a b, a ≼ b ↔ f a ≤ f b :=
  ⟨BoolMat.directedComplete, BoolMat.finiteTomography, BoolMat.separatingStates,
    _, BoolMat.scal_bijective, BoolMat.scal_le_iff⟩

end Papers.REC
