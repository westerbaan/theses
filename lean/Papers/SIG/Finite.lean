/-
Papers/SIG/Finite.lean

The finite (non-σ) halves of SIG §3.1 (main.tex:769–1004), which the paper
proves only by citation ([Cho19, Prop. 3.4.10, Prop. 3.5.9, Lemma 4.2.11]):

* SIG 28: for an effect monoid `M`, `EMod[M]ᵒᵖ` is an effectus with unit `M`
  and coproducts the cartesian products, with scalars `M`;
* SIG 29: `Pred : C → EMod[M]ᵒᵖ` is a morphism of effectuses;
* SIG 33: `WMod[M]` is an effectus with unit `M` and binary coproducts the
  pairs with orthogonal weights, with scalars `M`;
* SIG 34: `sSt : C → WMod[Mᵒᵖ]` is a morphism of effectuses;
* SIG 32 (finite half): weight `{0,1}`-modules are pointed sets.

Design:
* `EMod M` is the category of effect `M`-modules (the tree's `EffectModule`,
  179II) and **additive** action-preserving maps (subunital; the tree's
  `EModCat` has unital maps).  Its products are Π-types (for every index
  type); its opposite gets the pointwise hom-PCM (`f ⊥ g` iff `f a ⊥ g a`
  for all `a`, equivalently `f 1 ⊥ g 1`).
* `WMod M` is the category of weight `M`-modules (a PCM with a biadditive
  action and an additive, action-preserving weight `|·|` with `|x| = 0 ⇒
  x = 0` and `|x| ⊥ |y| ⇒ x ⊥ y`) and weight-decreasing additive
  action-preserving maps.  Its finite coproducts are built from an explicit
  binary coproduct (pairs with orthogonal weights) and the initial object
  `{0}` (Mathlib's `hasFiniteCoproducts_of_has_binary_and_initial`).
* Effectuses are the tree's `EffectusPartialForm` over `FinPAC` (180VII);
  preservation of finite coproducts is checked on binary coproducts and the
  initial object (`PreservesFiniteCoproducts.of_preserves_binary_and_initial`).
-/
import Papers.SIG.WeightModules

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits Theses.B.Eff Opposite

namespace Papers.SIG

universe u v

/-! ## A PCM lemma: the middle-four interchange -/

/-- If `(a ⊕ b) ⊕ (c ⊕ d)` is defined, so is `(a ⊕ c) ⊕ (b ⊕ d)`, with the
same value. -/
theorem fin_middle_four {P : Type*} [PCM P] {a b c d : P} (hab : Perp a b) (hcd : Perp c d)
    (h : Perp (ovee a b hab) (ovee c d hcd)) :
    ∃ (hac : Perp a c) (hbd : Perp b d) (h' : Perp (ovee a c hac) (ovee b d hbd)),
      ovee (ovee a c hac) (ovee b d hbd) h' = ovee (ovee a b hab) (ovee c d hcd) h := by
  have hbcd : Perp b (ovee c d hcd) := PCM.perp_of_ovee_perp hab h
  have hA : Perp a (ovee b (ovee c d hcd) hbcd) := PCM.perp_ovee_of_ovee_perp hab h
  have e1 : ovee (ovee a b hab) (ovee c d hcd) h = ovee a (ovee b (ovee c d hcd) hbcd) hA :=
    PCM.ovee_assoc hab h
  obtain ⟨hbc, hbcd', e2⟩ := PCM.assoc_left hcd hbcd
  have hcb : Perp c b := PCM.perp_comm hbc
  have e3 : ovee b c hbc = ovee c b hcb := PCM.ovee_comm hbc
  have hcbd : Perp (ovee c b hcb) d := by rw [← e3]; exact hbcd'
  have hbd : Perp b d := PCM.perp_of_ovee_perp hcb hcbd
  have hcbd2 : Perp c (ovee b d hbd) := PCM.perp_ovee_of_ovee_perp hcb hcbd
  have e4 : ovee (ovee c b hcb) d hcbd = ovee c (ovee b d hbd) hcbd2 := PCM.ovee_assoc hcb hcbd
  have E : ovee b (ovee c d hcd) hbcd = ovee c (ovee b d hbd) hcbd2 :=
    e2.symm.trans ((PCM.ovee_congr e3 rfl _ _).trans e4)
  have hA' : Perp a (ovee c (ovee b d hbd) hcbd2) := by rw [← E]; exact hA
  obtain ⟨hac, h', e5⟩ := PCM.assoc_left hcbd2 hA'
  exact ⟨hac, hbd, h', e5.trans ((PCM.ovee_congr rfl E.symm _ _).trans e1.symm)⟩

theorem fin_inl_pproj₁ {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] (X Y : C) : (coprod.inl : X ⟶ X ⨿ Y) ≫ pproj₁ X Y = 𝟙 X :=
  coprod.inl_desc _ _

theorem fin_inr_pproj₁ {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] (X Y : C) : (coprod.inr : Y ⟶ X ⨿ Y) ≫ pproj₁ X Y = 0 :=
  coprod.inr_desc _ _

theorem fin_inl_pproj₂ {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] (X Y : C) : (coprod.inl : X ⟶ X ⨿ Y) ≫ pproj₂ X Y = 0 :=
  coprod.inl_desc _ _

theorem fin_inr_pproj₂ {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] (X Y : C) : (coprod.inr : Y ⟶ X ⨿ Y) ≫ pproj₂ X Y = 𝟙 Y :=
  coprod.inr_desc _ _

/-! ## SIG 24, 28: the category `EMod[M]` and its opposite -/

/-- **SIG 24** (main.tex:771, Definition): an object of `EMod[M]`: an effect
`M`-module (the tree's `EffectModule`, 179II). -/
structure EMod (M : Type u) [EffectMonoid M] : Type (u + 1) where
  carrier : Type u
  [ea : EffectAlgebra carrier]
  [mod : EffectModule M carrier]

attribute [instance] EMod.ea EMod.mod

namespace EMod

variable {M : Type u} [EffectMonoid M]

instance : CoeSort (EMod M) (Type u) := ⟨EMod.carrier⟩

/-- **SIG 24** (main.tex:787, Definition): a morphism of `EMod[M]`: an
additive map preserving the action (subunital: `f 1 = 1` is not required). -/
@[ext]
structure Hom (E F : EMod M) : Type u where
  toFun : E.carrier → F.carrier
  additive : IsAdditive toFun
  map_smul : ∀ (r : M) (a : E.carrier), toFun (r • a) = r • toFun a

/-- **SIG 24** (main.tex:787, Definition): the category `EMod[M]`. -/
instance : Category (EMod M) where
  Hom := Hom
  id E := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun _ _ => rfl⟩
  comp f g := ⟨g.toFun ∘ f.toFun, SEMod.IsAdditive.comp' f.additive g.additive,
    fun r a => by simp [f.map_smul, g.map_smul]⟩

@[simp] theorem id_toFun (E : EMod M) : (𝟙 E : Hom E E).toFun = id := rfl
@[simp] theorem comp_toFun {E F G : EMod M} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

theorem hom_ext {E F : EMod M} {f g : E ⟶ F} (h : ∀ a, f.toFun a = g.toFun a) : f = g :=
  Hom.ext (funext h)

theorem Hom.map_zero {E F : EMod M} (f : E ⟶ F) : f.toFun 0 = 0 := f.additive.1

theorem Hom.mono {E F : EMod M} (f : E ⟶ F) {a b : E.carrier} (h : a ≼ b) :
    f.toFun a ≼ f.toFun b := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨h', e⟩ := f.additive.2 hc
  exact ⟨f.toFun c, h', e⟩

theorem Hom.map_ovee {E F : EMod M} (f : E ⟶ F) {a b : E.carrier} (h : Perp a b) :
    ∃ h' : Perp (f.toFun a) (f.toFun b), ovee (f.toFun a) (f.toFun b) h' = f.toFun (ovee a b h) :=
  f.additive.2 h

theorem iso_hom_one {E F : EMod M} (e : E ≅ F) : e.hom.toFun 1 = 1 := by
  have h1 : e.inv.toFun (e.hom.toFun 1) = 1 := congrArg (fun g => Hom.toFun g 1) e.hom_inv_id
  have h2 : e.inv.toFun 1 = 1 :=
    eabasics_le_antisymm (ea_le_one _) (h1 ▸ e.inv.mono (ea_le_one _))
  have h3 : e.hom.toFun (e.inv.toFun 1) = 1 := congrArg (fun g => Hom.toFun g 1) e.inv_hom_id
  rwa [h2] at h3

/-- The unit object: `M` itself. -/
def unit (M : Type u) [EffectMonoid M] : EMod M :=
  @EMod.mk M _ M _ (selfEffectModule M)

/-- The product `∏ D_j` in `EMod[M]` (any index type). -/
def pi {J : Type} (D : J → EMod M) : EMod M where
  carrier := ∀ j, (D j).carrier

/-- The projection `∏ D_j → D_j`. -/
def piProj {J : Type} (D : J → EMod M) (j : J) : pi D ⟶ D j where
  toFun a := a j
  additive := ⟨rfl, fun h => ⟨h j, rfl⟩⟩
  map_smul r a := pi_smul_apply r a j

/-- The tupling `X → ∏ D_j`. -/
def piLift {J : Type} {D : J → EMod M} {X : EMod M} (f : ∀ j, X ⟶ D j) : X ⟶ pi D where
  toFun x j := (f j).toFun x
  additive := ⟨funext fun j => (f j).map_zero, fun h => by
    choose h' e using fun j => (f j).map_ovee h
    exact ⟨h', funext e⟩⟩
  map_smul r a := funext fun j => ((f j).map_smul r a).trans
    (pi_smul_apply (D := fun j => (D j).carrier) r (fun j => (f j).toFun a) j).symm

/-- The product cone of `EMod[M]`. -/
def piFan {J : Type} (D : J → EMod M) : Fan D := Fan.mk (pi D) (piProj D)

/-- **SIG 28** (main.tex:822): products in `EMod[M]` are the cartesian
products with pointwise operations. -/
def piFanIsLimit {J : Type} (D : J → EMod M) : IsLimit (piFan D) :=
  Fan.IsLimit.mk _ (fun s => piLift s.proj) (fun s j => hom_ext fun x => rfl)
    (fun s m hm => hom_ext fun x => funext fun j => by
      have h := congrArg (fun g => Hom.toFun g x) (hm j)
      exact h)

instance hasProductsOfShape (J : Type) : HasProductsOfShape J (EMod M) :=
  ⟨fun F => by
    have : HasLimit (Discrete.functor (F.obj ∘ Discrete.mk)) := HasLimit.mk ⟨_, piFanIsLimit _⟩
    exact hasLimit_of_iso Discrete.natIsoFunctor.symm⟩

instance : HasFiniteProducts (EMod M) := ⟨fun _ => inferInstance⟩

/-- **SIG 28** (main.tex:822): the finite coproducts of `EMod[M]ᵒᵖ` are the
cartesian products of `EMod[M]`. -/
noncomputable def coproductIsColimit {J : Type} (D : J → EMod M) : IsColimit (piFan D).op :=
  Fan.IsLimit.op (piFanIsLimit D)

/-! ### Binary limits of `EMod[M]`, elementwise -/

section BinaryLimit

variable {A B : EMod M} {c : BinaryFan A B} (hc : IsLimit c)

/-- A limit binary fan is isomorphic to the explicit product. -/
noncomputable def limitIso : c.pt ≅ pi (pairFunction A B) :=
  hc.conePointUniqueUpToIso (piFanIsLimit (pairFunction A B))

include hc in
theorem limitIso_apply (u : c.pt.carrier) (j : WalkingPair) :
    (limitIso hc).hom.toFun u j = (c.π.app ⟨j⟩).toFun u := by
  have := IsLimit.conePointUniqueUpToIso_hom_comp hc (piFanIsLimit (pairFunction A B)) ⟨j⟩
  exact congrArg (fun g => Hom.toFun g u) this

include hc in
/-- In a limit binary fan, elements with orthogonal components are
orthogonal. -/
theorem limit_perp {u v : c.pt.carrier} (h1 : Perp (c.fst.toFun u) (c.fst.toFun v))
    (h2 : Perp (c.snd.toFun u) (c.snd.toFun v)) : Perp u v := by
  have hp : Perp ((limitIso hc).hom.toFun u) ((limitIso hc).hom.toFun v) := by
    intro j
    rw [limitIso_apply hc u j, limitIso_apply hc v j]
    cases j
    · exact h1
    · exact h2
  obtain ⟨hp', -⟩ := (limitIso hc).inv.map_ovee hp
  have e1 : (limitIso hc).inv.toFun ((limitIso hc).hom.toFun u) = u :=
    congrArg (fun g => Hom.toFun g u) (limitIso hc).hom_inv_id
  have e2 : (limitIso hc).inv.toFun ((limitIso hc).hom.toFun v) = v :=
    congrArg (fun g => Hom.toFun g v) (limitIso hc).hom_inv_id
  rw [e1, e2] at hp'
  exact hp'

include hc in
theorem limit_fst_one : c.fst.toFun 1 = 1 := by
  have := limitIso_apply hc 1 WalkingPair.left
  rw [iso_hom_one] at this
  exact this.symm

include hc in
theorem limit_snd_one : c.snd.toFun 1 = 1 := by
  have := limitIso_apply hc 1 WalkingPair.right
  rw [iso_hom_one] at this
  exact this.symm

end BinaryLimit

/-! ### The hom-PCM of `EMod[M]ᵒᵖ` -/

/-- The zero map. -/
def zeroHom (D E : EMod M) : D ⟶ E where
  toFun _ := 0
  additive := ⟨rfl, fun _ => ⟨PCM.zero_perp 0, PCM.zero_ovee 0⟩⟩
  map_smul r _ := (emod_smul_zero r).symm

/-- The pointwise sum of two maps with pointwise orthogonal values. -/
noncomputable def oveeHom {E F : EMod M} (f g : E ⟶ F)
    (h : ∀ a, Perp (f.toFun a) (g.toFun a)) : E ⟶ F where
  toFun a := ovee (f.toFun a) (g.toFun a) (h a)
  additive := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · show ovee (f.toFun 0) (g.toFun 0) (h 0) = 0
      rw [PCM.ovee_congr f.map_zero g.map_zero (h 0) (PCM.zero_perp 0), PCM.zero_ovee]
    · obtain ⟨hf, ef⟩ := f.map_ovee hab
      obtain ⟨hg, eg⟩ := g.map_ovee hab
      have hp : Perp (ovee _ _ hf) (ovee _ _ hg) := by rw [ef, eg]; exact h (ovee a b hab)
      obtain ⟨hac, hbd, h', e⟩ := fin_middle_four hf hg hp
      exact ⟨h', e.trans (PCM.ovee_congr ef eg hp _)⟩
  map_smul r a := by
    obtain ⟨h', e⟩ := EffectModule.smul_perp r (h a)
    exact (PCM.ovee_congr (f.map_smul r a) (g.map_smul r a) _ h').trans e

variable (X Y : (EMod M)ᵒᵖ)

/-- **SIG 28** (the hom-PCMs, [Cho19, Prop. 3.4.10]): `EMod[M]ᵒᵖ(X, Y) =
EMod[M](Y, X)` with the pointwise partial sum. -/
noncomputable instance homPCM : PCM (X ⟶ Y) where
  zero := (zeroHom Y.unop X.unop).op
  Perp f g := ∀ a, Perp (f.unop.toFun a) (g.unop.toFun a)
  ovee f g h := (oveeHom f.unop g.unop h).op
  perp_comm h := fun a => PCM.perp_comm (h a)
  ovee_comm h := Quiver.Hom.unop_inj (hom_ext fun a => PCM.ovee_comm (h a))
  perp_of_ovee_perp hab h := fun a => PCM.perp_of_ovee_perp (hab a) (h a)
  perp_ovee_of_ovee_perp hab h := fun a => PCM.perp_ovee_of_ovee_perp (hab a) (h a)
  ovee_assoc hab h := Quiver.Hom.unop_inj (hom_ext fun a => PCM.ovee_assoc (hab a) (h a))
  zero_perp f := fun a => PCM.zero_perp (f.unop.toFun a)
  zero_ovee f := Quiver.Hom.unop_inj (hom_ext fun a => PCM.zero_ovee (f.unop.toFun a))

variable {X Y}

theorem hom_perp_def (f g : X ⟶ Y) :
    Perp f g ↔ ∀ a, Perp (f.unop.toFun a) (g.unop.toFun a) := Iff.rfl

theorem hom_ovee_apply {f g : X ⟶ Y} (h : Perp f g) (a : Y.unop.carrier) :
    (ovee f g h).unop.toFun a = ovee (f.unop.toFun a) (g.unop.toFun a) (h a) := rfl

theorem hom_zero_apply (a : Y.unop.carrier) : (0 : X ⟶ Y).unop.toFun a = 0 := rfl

/-- **SIG 28** ([Cho19, Prop. 3.4.10]): maps `f, g : Y → X` are summable iff
`f 1 ⊥ g 1`. -/
theorem hom_perp_iff (f g : X ⟶ Y) : Perp f g ↔ Perp (f.unop.toFun 1) (g.unop.toFun 1) := by
  refine ⟨fun h => h 1, fun h a => ?_⟩
  obtain ⟨hp, -⟩ := ovee_le_ovee (f.unop.mono (ea_le_one a)) (g.unop.mono (ea_le_one a)) h
  exact hp

theorem coprod_inl_one (B : (EMod M)ᵒᵖ) :
    (coprod.inl : B ⟶ B ⨿ B).unop.toFun 1 = 1 :=
  limit_fst_one (BinaryCofan.IsColimit.unop (X := B.unop) (Y := B.unop) (coprodIsCoprod B B))

theorem coprod_inr_one (B : (EMod M)ᵒᵖ) :
    (coprod.inr : B ⟶ B ⨿ B).unop.toFun 1 = 1 :=
  limit_snd_one (BinaryCofan.IsColimit.unop (X := B.unop) (Y := B.unop) (coprodIsCoprod B B))

theorem coprod_perp (B : (EMod M)ᵒᵖ) {u v : (B ⨿ B).unop.carrier}
    (h1 : Perp ((coprod.inl : B ⟶ B ⨿ B).unop.toFun u) ((coprod.inl : B ⟶ B ⨿ B).unop.toFun v))
    (h2 : Perp ((coprod.inr : B ⟶ B ⨿ B).unop.toFun u) ((coprod.inr : B ⟶ B ⨿ B).unop.toFun v)) :
    Perp u v :=
  limit_perp (BinaryCofan.IsColimit.unop (X := B.unop) (Y := B.unop) (coprodIsCoprod B B)) h1 h2

/-- **SIG 28** ([Cho19, Prop. 3.4.10]): `EMod[M]ᵒᵖ` is a finPAC. -/
instance finPAC : FinPAC (EMod M)ᵒᵖ where
  comp_ovee {X Y Z f g} h k := ⟨fun z => h (k.unop.toFun z), rfl⟩
  ovee_comp {W X Y f g} h k := by
    refine ⟨fun a => (k.unop.map_ovee (h a)).1, Quiver.Hom.unop_inj (hom_ext fun a => ?_)⟩
    exact ((k.unop.map_ovee (h a)).2).symm
  comp_zero {X Y Z} f := Quiver.Hom.unop_inj (hom_ext fun _ => f.unop.map_zero)
  zero_comp {X Y Z} f := rfl
  compatible_sum {X Y} b := by
    intro a
    show Perp (b.unop.toFun ((pproj₁ Y Y).unop.toFun a)) (b.unop.toFun ((pproj₂ Y Y).unop.toFun a))
    refine (b.unop.map_ovee (coprod_perp Y ?_ ?_)).1
    · have e1 := congrArg (fun g : Y ⟶ Y => g.unop.toFun a) (fin_inl_pproj₁ Y Y)
      have e2 := congrArg (fun g : Y ⟶ Y => g.unop.toFun a) (fin_inl_pproj₂ Y Y)
      show Perp ((coprod.inl ≫ pproj₁ Y Y).unop.toFun a) ((coprod.inl ≫ pproj₂ Y Y).unop.toFun a)
      rw [e1, e2]
      exact PCM.perp_zero _
    · have e1 := congrArg (fun g : Y ⟶ Y => g.unop.toFun a) (fin_inr_pproj₁ Y Y)
      have e2 := congrArg (fun g : Y ⟶ Y => g.unop.toFun a) (fin_inr_pproj₂ Y Y)
      show Perp ((coprod.inr ≫ pproj₁ Y Y).unop.toFun a) ((coprod.inr ≫ pproj₂ Y Y).unop.toFun a)
      rw [e1, e2]
      exact PCM.zero_perp _
  untying {X Y f g} h := by
    rw [hom_perp_iff] at h ⊢
    show Perp (f.unop.toFun ((coprod.inl : Y ⟶ Y ⨿ Y).unop.toFun 1))
      (g.unop.toFun ((coprod.inr : Y ⟶ Y ⨿ Y).unop.toFun 1))
    rw [coprod_inl_one, coprod_inr_one]
    exact h

/-- The map `r ↦ r · e` out of the unit object. -/
def smulMap (E : EMod M) (e : E.carrier) : unit M ⟶ E where
  toFun := fun (r : M) => r • e
  additive := ⟨emod_zero_smul (M := M) e, fun h => EffectModule.perp_smul (M := M) h e⟩
  map_smul r s := EffectModule.mul_smul (M := M) (E := E.carrier) r s e

theorem smulMap_one_apply (E : EMod M) (e : E.carrier) : (smulMap E e).toFun 1 = e :=
  EffectModule.one_smul e

/-- Every map out of the unit object is `r ↦ r · p(1)`. -/
theorem eq_smulMap {E : EMod M} (p : unit M ⟶ E) : p = smulMap E (p.toFun 1) := by
  refine hom_ext fun (r : M) => ?_
  have h := p.map_smul r 1
  show p.toFun r = r • p.toFun 1
  rw [← h]
  congr 1
  exact (EffectMonoid.mul_one r).symm

theorem perp_orth' {X : (EMod M)ᵒᵖ} (p : X ⟶ op (unit M)) :
    Perp p (smulMap X.unop (orth (p.unop.toFun 1))).op := by
  rw [hom_perp_iff]
  show Perp (p.unop.toFun 1) ((smulMap X.unop _).toFun 1)
  rw [smulMap_one_apply]
  exact EffectAlgebra.perp_orth _

theorem zero_of_apply_one {X Y : (EMod M)ᵒᵖ} {f : X ⟶ Y} (h : f.unop.toFun 1 = 0) : f = 0 := by
  apply Quiver.Hom.unop_inj
  refine hom_ext fun a => ?_
  show f.unop.toFun a = 0
  exact eq_zero_of_le_zero (h ▸ f.unop.mono (ea_le_one a))

/-- **SIG 28** (`prop:emod-effectus`, main.tex:816, Proposition), the case of
an effect monoid (cited there as [Cho19, Prop. 3.4.10]): for an effect monoid
`M`, `EMod[M]ᵒᵖ` is an effectus, with unit object `M`, truth maps
`1_E : r ↦ r · 1`, and finite coproducts the cartesian products
(`coproductIsColimit`). -/
noncomputable instance effectus : EffectusPartialForm (EMod M)ᵒᵖ where
  I := op (unit M)
  one X := (smulMap X.unop 1).op
  orth {X} p := (smulMap X.unop (orth (p.unop.toFun 1))).op
  perp_orth p := perp_orth' p
  ovee_orth {X} p := by
    apply Quiver.Hom.unop_inj
    refine hom_ext fun (r : M) => ?_
    show ovee (p.unop.toFun r) (r • orth (p.unop.toFun 1)) _ = r • (1 : X.unop.carrier)
    have hp : p.unop.toFun r = r • p.unop.toFun 1 :=
      congrArg (fun g => Hom.toFun g r) (eq_smulMap p.unop)
    obtain ⟨h'', e''⟩ := EffectModule.smul_perp r (EffectAlgebra.perp_orth (p.unop.toFun 1))
    calc ovee (p.unop.toFun r) _ _
        = ovee (r • p.unop.toFun 1) (r • orth (p.unop.toFun 1)) h'' :=
          PCM.ovee_congr hp rfl _ h''
      _ = r • ovee (p.unop.toFun 1) (orth (p.unop.toFun 1)) _ := e''
      _ = r • 1 := by rw [EffectAlgebra.ovee_orth]
  orth_unique {X p q} h e := by
    have h1 : ovee (p.unop.toFun 1) (q.unop.toFun 1) (h 1) = 1 := by
      have := congrArg (fun g : X ⟶ op (unit M) => g.unop.toFun 1) e
      exact this.trans (smulMap_one_apply X.unop 1)
    have hq : q.unop.toFun 1 = orth (p.unop.toFun 1) := EffectAlgebra.orth_unique (h 1) h1
    apply Quiver.Hom.unop_inj
    rw [eq_smulMap q.unop, hq]
    rfl
  eq_zero_of_perp_one {X p} h := by
    rw [hom_perp_iff] at h
    have h1 : (smulMap X.unop 1).op.unop.toFun 1 = 1 := smulMap_one_apply X.unop 1
    rw [h1] at h
    exact zero_of_apply_one (EffectAlgebra.eq_zero_of_perp_one h)
  eq_zero_of_one_zero {X Y f} h := by
    apply zero_of_apply_one
    have h1 := congrArg (fun g : X ⟶ op (unit M) => g.unop.toFun 1) h
    have h2 : (f ≫ (smulMap Y.unop 1).op).unop.toFun 1 = f.unop.toFun 1 := by
      show f.unop.toFun ((smulMap Y.unop 1).toFun 1) = _
      rw [smulMap_one_apply]
    exact h2.symm.trans h1
  perp_of_one_perp {X Y f g} h := by
    rw [hom_perp_iff] at h ⊢
    have e : ∀ k : X ⟶ Y, (k ≫ (smulMap Y.unop 1).op).unop.toFun 1 = k.unop.toFun 1 := by
      intro k
      show k.unop.toFun ((smulMap Y.unop 1).toFun 1) = _
      rw [smulMap_one_apply]
    rw [e, e] at h
    exact h

/-- Right multiplication `t ↦ t · r` on the unit object. -/
def rmul (r : M) : unit M ⟶ unit M where
  toFun := fun (t : M) => t * r
  additive := ⟨(exc_emonzero r).2, fun {a b} h => by
    obtain ⟨h', e⟩ := emon_ovee_mul r h; exact ⟨h', e.symm⟩⟩
  map_smul s t := EffectMonoid.mul_assoc s t r

/-- **SIG 28** (main.tex:816), "with scalars `M`": the scalars of the
effectus `EMod[M]ᵒᵖ` form an effect monoid isomorphic to `M`, via
`p ↦ p(1)`. -/
theorem effectus_scalars : EMIso (Scal (EMod M)ᵒᵖ) M := by
  let φ : EffectMonoidHom (Scal (EMod M)ᵒᵖ) M :=
    { toFun := fun p => p.unop.toFun 1
      perp_map := fun {p q} h => (hom_perp_iff p q).1 h
      ovee_map := fun {p q} h => rfl
      map_one := smulMap_one_apply (unit M) 1
      map_mul := fun l m => by
        show (m ≫ l).unop.toFun 1 = @HMul.hMul M M M _ (l.unop.toFun 1) (m.unop.toFun 1)
        exact congrArg (fun g => Hom.toFun g (l.unop.toFun 1)) (eq_smulMap m.unop) }
  let ψ : EffectMonoidHom M (Scal (EMod M)ᵒᵖ) :=
    { toFun := fun r => (rmul r).op
      perp_map := fun {r s} h => (hom_perp_iff _ _).2 (by
        show Perp (@HMul.hMul M M M _ 1 r) (@HMul.hMul M M M _ 1 s)
        rw [EffectMonoid.one_mul, EffectMonoid.one_mul]; exact h)
      ovee_map := fun {r s} h => by
        apply Quiver.Hom.unop_inj
        refine hom_ext fun (t : M) => ?_
        obtain ⟨h'', e''⟩ := emon_mul_ovee t h
        exact ((PCM.ovee_congr rfl rfl _ _).trans e''.symm).symm
      map_one := by
        apply Quiver.Hom.unop_inj
        exact hom_ext fun (t : M) => rfl
      map_mul := fun r s => by
        apply Quiver.Hom.unop_inj
        refine hom_ext fun (t : M) => ?_
        show t * (r * s) = (t * r) * s
        exact (EffectMonoid.mul_assoc t r s).symm }
  refine ⟨φ, ψ, fun p => ?_, fun r => EffectMonoid.one_mul r⟩
  apply Quiver.Hom.unop_inj
  refine hom_ext fun (t : M) => ?_
  exact (congrArg (fun g => Hom.toFun g t) (eq_smulMap p.unop)).symm

end EMod

/-! ## Preservation of finite coproducts, checked on binary and nullary ones -/

/-- A functor between categories with finite coproducts preserves them as
soon as it sends binary coproducts to binary coproducts and the initial
object to an initial object. -/
theorem fin_preservesFiniteCoproducts {C : Type u} [Category.{v} C] {D : Type*} [Category D]
    [HasFiniteCoproducts C] [HasFiniteCoproducts D] (F : C ⥤ D)
    (hbin : ∀ X Y : C,
      IsColimit (BinaryCofan.mk (F.map (coprod.inl : X ⟶ X ⨿ Y)) (F.map coprod.inr)))
    (hinit : IsInitial (F.obj (⊥_ C))) : PreservesFiniteCoproducts F := by
  have hp : ∀ X Y : C, PreservesColimit (pair X Y) F := fun X Y =>
    preservesColimit_of_preserves_colimit_cocone (coprodIsCoprod X Y)
      ((isColimitMapCoconeBinaryCofanEquiv F _ _).symm (hbin X Y))
  have : PreservesColimitsOfShape (Discrete WalkingPair) F :=
    ⟨fun {K} => by
      have := hp (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
      exact preservesColimit_of_iso_diagram F (diagramIsoPair K).symm⟩
  have : PreservesColimit (Functor.empty.{0} C) F :=
    preservesInitial_of_iso F (initialIsInitial.uniqueUpToIso hinit)
  have : PreservesColimitsOfShape (Discrete PEmpty.{1}) F :=
    preservesColimitsOfShape_pempty_of_preservesInitial F
  exact ⟨fun n => preservesShape_fin_of_preserves_binary_and_initial F n⟩

/-! ## SIG 29: `Pred : C → EMod[M]ᵒᵖ` -/

section PredFunctor

variable {C : Type u} [Category.{u} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- `Pred A` as an object of `EMod[M]` (SIG 25). -/
noncomputable abbrev finPredObj (A : C) : EMod (Scal C) :=
  EMod.mk (Pred A)

/-- `Pred f = (-) ∘ f`. -/
noncomputable def finPredMap {A B : C} (f : A ⟶ B) : finPredObj B ⟶ finPredObj A where
  toFun p := f ≫ p
  additive := ⟨FinPAC.comp_zero f, fun h => by
    obtain ⟨h', e⟩ := FinPAC.ovee_comp h f; exact ⟨h', e.symm⟩⟩
  map_smul r p := (Category.assoc f p r).symm

/-- **SIG 29**: the functor `Pred : C → EMod[M]ᵒᵖ`, `A ↦ Pred A`. -/
noncomputable def finPredFunctor : C ⥤ (EMod (Scal C))ᵒᵖ where
  obj A := op (finPredObj A)
  map f := (finPredMap f).op
  map_id A := by
    apply Quiver.Hom.unop_inj
    exact EMod.hom_ext fun p => Category.id_comp p
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    exact EMod.hom_ext fun p => Category.assoc f g p

/-- Cotupling `T → Pred X, T → Pred Y` into `T → Pred (X + Y)`. -/
noncomputable def finPredLift {X Y : C} {T : EMod (Scal C)} (f : T ⟶ finPredObj X)
    (g : T ⟶ finPredObj Y) : T ⟶ finPredObj (X ⨿ Y) where
  toFun t := coprod.desc (f.toFun t) (g.toFun t)
  additive := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · show coprod.desc (f.toFun 0) (g.toFun 0) = 0
      rw [f.map_zero, g.map_zero]; exact cotupl_pcm_3 X Y (effObj C)
    · obtain ⟨hf, ef⟩ := f.map_ovee hab
      obtain ⟨hg, eg⟩ := g.map_ovee hab
      have hp := (cotupl_pcm_1 (f.toFun a) (f.toFun b) (g.toFun a) (g.toFun b)).2 ⟨hf, hg⟩
      refine ⟨hp, ?_⟩
      rw [cotupl_pcm_2 hp hf hg, ef, eg]
  map_smul r t := by
    show coprod.desc (f.toFun (r • t)) (g.toFun (r • t)) = coprod.desc (f.toFun t) (g.toFun t) ≫ r
    rw [f.map_smul, g.map_smul]
    exact (coprod.desc_comp _ _ _).symm

/-- `Pred (X + Y)` is the product `Pred X × Pred Y` in `EMod[M]` (cotupling,
181IV). -/
noncomputable def finPredIsLimit (X Y : C) :
    IsLimit (BinaryFan.mk (finPredMap (coprod.inl : X ⟶ X ⨿ Y)) (finPredMap coprod.inr)) :=
  BinaryFan.IsLimit.mk _ (fun f g => finPredLift f g)
    (fun f g => EMod.hom_ext fun t => coprod.inl_desc _ _)
    (fun f g => EMod.hom_ext fun t => coprod.inr_desc _ _)
    (fun f g m h1 h2 => EMod.hom_ext fun t => by
      show m.toFun t = coprod.desc (f.toFun t) (g.toFun t)
      refine coprod.hom_ext ?_ ?_
      · rw [coprod.inl_desc]; exact congrArg (fun k => EMod.Hom.toFun k t) h1
      · rw [coprod.inr_desc]; exact congrArg (fun k => EMod.Hom.toFun k t) h2)

/-- `Pred 0` is terminal in `EMod[M]`. -/
noncomputable def finPredInitialIsTerminal : IsTerminal (finPredObj (⊥_ C)) :=
  IsTerminal.ofUniqueHom (fun T => EMod.zeroHom T _)
    (fun _ _ => EMod.hom_ext fun _ => initial.hom_ext _ _)

instance finPredFunctor_preservesFiniteCoproducts :
    PreservesFiniteCoproducts (finPredFunctor (C := C)) :=
  fin_preservesFiniteCoproducts _ (fun X Y => BinaryFan.IsLimit.op (finPredIsLimit X Y))
    finPredInitialIsTerminal.op

/-- `Pred I` is the unit object `M = C(I, I)`. -/
noncomputable def finUnitPredIso : finPredObj (effObj C) ≅ EMod.unit (Scal C) where
  hom := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun _ _ => rfl⟩
  inv := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun _ _ => rfl⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **SIG 29** (main.tex:840, Proposition), the case of an effectus (cited
there as [Cho19, Lemma 4.2.11]): for an effectus `C` with scalars `M`,
`A ↦ Pred A` is a morphism of effectuses `C → EMod[M]ᵒᵖ`: it preserves finite
coproducts (`Pred (X + Y) ≅ Pred X × Pred Y` by cotupling, `Pred 0 = {0}`),
the unit (`Pred I = M`) and the truth maps. -/
noncomputable def finPredMorphism : EffectusMorphism C (EMod (Scal C))ᵒᵖ where
  F := finPredFunctor
  preserves := inferInstance
  u := finUnitPredIso.op
  map_truth A := by
    apply Quiver.Hom.unop_inj
    refine EMod.hom_ext fun (r : Scal C) => ?_
    show truth A ≫ r = r • (1 : Pred A)
    rfl

end PredFunctor

/-! ## SIG 30, 33: the category `WMod[M]` -/

section PCMHelpers

variable {P : Type*} [PCM P]

theorem fin_le_ovee_left {x y : P} (h : Perp x y) : x ≼ ovee x y h := ⟨y, h, rfl⟩

theorem fin_le_ovee_right {x y : P} (h : Perp x y) : y ≼ ovee x y h :=
  ⟨x, PCM.perp_comm h, (PCM.ovee_comm h).symm⟩

theorem fin_le_of_eq {x y : P} (e : x = y) : x ≼ y := e ▸ pcm_preorder_refl x

theorem fin_le_trans_eq {x y z : P} (h : x ≼ y) (e : y = z) : x ≼ z := e ▸ h

theorem fin_eq_trans_le {x y z : P} (e : x = y) (h : y ≼ z) : x ≼ z := e ▸ h

end PCMHelpers

theorem fin_ominus_eq {E : Type*} [EffectAlgebra E] {a b c : E} (hab : a ≼ b) (h : IsDiff b a c) :
    ominus b a hab = c :=
  isDiff_unique (isDiff_ominus hab) h

/-- Differences add: `(b ⊖ a) ⊕ (d ⊖ c) = (b ⊕ d) ⊖ (a ⊕ c)`. -/
theorem fin_ominus_ovee {E : Type*} [EffectAlgebra E] {a b c d : E} (hab : a ≼ b) (hcd : c ≼ d)
    (hbd : Perp b d) (hac : Perp a c) (h2 : ovee a c hac ≼ ovee b d hbd) :
    ∃ h' : Perp (ominus b a hab) (ominus d c hcd),
      ovee _ _ h' = ominus (ovee b d hbd) (ovee a c hac) h2 := by
  obtain ⟨k1, e1⟩ := isDiff_ominus hab
  obtain ⟨k2, e2⟩ := isDiff_ominus hcd
  have hp : Perp (ovee a (ominus b a hab) k1) (ovee c (ominus d c hcd) k2) := by
    rw [e1, e2]; exact hbd
  obtain ⟨hac', hbd', h', e⟩ := fin_middle_four k1 k2 hp
  refine ⟨hbd', (fin_ominus_eq h2 ⟨h', e.trans (PCM.ovee_congr e1 e2 hp hbd)⟩).symm⟩

/-- **SIG 30** (`def:wpmod`, main.tex:869, Definition): a **weight
`M`-module** is a PCM `X` with a biadditive `M`-action and a weight
`|·| : X → M` which is additive and preserves the action (`|r x| = r |x|`),
such that `|x| = 0` implies `x = 0` and `|x| ⊥ |y|` implies `x ⊥ y`. -/
structure WMod (M : Type u) [EffectMonoid M] : Type (u + 1) where
  carrier : Type u
  [pcm : PCM carrier]
  [act : SMul M carrier]
  weight : carrier → M
  one_smul : ∀ x : carrier, (1 : M) • x = x
  mul_smul : ∀ (r s : M) (x : carrier), (r * s) • x = r • s • x
  smul_biadditive : IsBiadditive (fun (r : M) (x : carrier) => r • x)
  weight_additive : IsAdditive weight
  weight_smul : ∀ (r : M) (x : carrier), weight (r • x) = r * weight x
  eq_zero_of_weight : ∀ x : carrier, weight x = 0 → x = 0
  perp_of_weight : ∀ {x y : carrier}, Perp (weight x) (weight y) → Perp x y

attribute [instance] WMod.pcm WMod.act

namespace WMod

variable {M : Type u} [EffectMonoid M]

instance : CoeSort (WMod M) (Type u) := ⟨WMod.carrier⟩

theorem weight_zero (X : WMod M) : X.weight 0 = 0 := X.weight_additive.1

theorem weight_ovee (X : WMod M) {x y : X.carrier} (h : Perp x y) :
    ∃ h' : Perp (X.weight x) (X.weight y), ovee _ _ h' = X.weight (ovee x y h) :=
  X.weight_additive.2 h

theorem weight_mono (X : WMod M) {x y : X.carrier} (h : x ≼ y) : X.weight x ≼ X.weight y := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨h', e⟩ := X.weight_ovee hc
  exact ⟨_, h', e⟩

theorem smul_zero (X : WMod M) (r : M) : r • (0 : X.carrier) = 0 := (X.smul_biadditive.1 r).1

theorem zero_smul (X : WMod M) (x : X.carrier) : (0 : M) • x = 0 := (X.smul_biadditive.2 x).1

theorem smul_ovee (X : WMod M) (r : M) {x y : X.carrier} (h : Perp x y) :
    ∃ h', ovee (r • x) (r • y) h' = r • ovee x y h := (X.smul_biadditive.1 r).2 h

theorem ovee_smul (X : WMod M) {r s : M} (h : Perp r s) (x : X.carrier) :
    ∃ h', ovee (r • x) (s • x) h' = ovee r s h • x := (X.smul_biadditive.2 x).2 h

/-- **SIG 30** (main.tex:891, Definition): a morphism of `WMod[M]`: an
additive, action-preserving, **weight-decreasing** map. -/
@[ext]
structure Hom (X Y : WMod M) : Type u where
  toFun : X.carrier → Y.carrier
  additive : IsAdditive toFun
  map_smul : ∀ (r : M) (x : X.carrier), toFun (r • x) = r • toFun x
  weight_le : ∀ x : X.carrier, Y.weight (toFun x) ≼ X.weight x

/-- **SIG 30** (main.tex:891, Definition): the category `WMod[M]`. -/
instance : Category (WMod M) where
  Hom := Hom
  id X := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun _ _ => rfl, fun _ => pcm_preorder_refl _⟩
  comp f g := ⟨g.toFun ∘ f.toFun, SEMod.IsAdditive.comp' f.additive g.additive,
    fun r x => by simp [f.map_smul, g.map_smul],
    fun x => pcm_preorder_trans (g.weight_le _) (f.weight_le x)⟩

@[simp] theorem comp_toFun {X Y Z : WMod M} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

theorem hom_ext {X Y : WMod M} {f g : X ⟶ Y} (h : ∀ a, f.toFun a = g.toFun a) : f = g :=
  Hom.ext (funext h)

theorem Hom.map_zero {X Y : WMod M} (f : X ⟶ Y) : f.toFun 0 = 0 := f.additive.1

theorem Hom.map_ovee {X Y : WMod M} (f : X ⟶ Y) {a b : X.carrier} (h : Perp a b) :
    ∃ h' : Perp (f.toFun a) (f.toFun b), ovee (f.toFun a) (f.toFun b) h' = f.toFun (ovee a b h) :=
  f.additive.2 h

/-- An isomorphism of `WMod[M]` preserves weights. -/
theorem iso_weight {X Y : WMod M} (e : X ≅ Y) (x : X.carrier) :
    Y.weight (e.hom.toFun x) = X.weight x := by
  refine eabasics_le_antisymm (e.hom.weight_le x) ?_
  have h := e.inv.weight_le (e.hom.toFun x)
  have e1 : e.inv.toFun (e.hom.toFun x) = x := congrArg (fun g => Hom.toFun g x) e.hom_inv_id
  rwa [e1] at h

/-- An isomorphism of `WMod[M]` reflects orthogonality, and the weight of the
sum is the weight of the image sum. -/
theorem iso_perp {X Y : WMod M} (e : X ≅ Y) {x y : X.carrier}
    (h : Perp (e.hom.toFun x) (e.hom.toFun y)) :
    ∃ h' : Perp x y, X.weight (ovee x y h') = Y.weight (ovee _ _ h) := by
  obtain ⟨h0, e0⟩ := e.inv.map_ovee h
  have hx : e.inv.toFun (e.hom.toFun x) = x := congrArg (fun g => Hom.toFun g x) e.hom_inv_id
  have hy : e.inv.toFun (e.hom.toFun y) = y := congrArg (fun g => Hom.toFun g y) e.hom_inv_id
  have h' : Perp x y := by have := h0; rwa [hx, hy] at this
  refine ⟨h', ?_⟩
  have e1 : ovee x y h' = e.inv.toFun (ovee _ _ h) :=
    (PCM.ovee_congr hx.symm hy.symm h' h0).trans e0
  rw [e1]
  have := iso_weight e.symm (ovee _ _ h)
  exact this

/-- The unit object: `M` itself, with `r · s = rs` and `|s| = s`. -/
abbrev unit (M : Type u) [EffectMonoid M] : WMod M :=
  @WMod.mk M _ M _ ⟨fun r s => r * s⟩ id
    (fun x => EffectMonoid.one_mul x) (fun r s x => EffectMonoid.mul_assoc r s x)
    (@effectModule_biadditive M _ M _ (selfEffectModule M))
    ⟨rfl, fun h => ⟨h, rfl⟩⟩ (fun _ _ => rfl) (fun _ h => h) (fun h => h)

instance unitEffectMonoid : EffectMonoid (unit M).carrier := inferInstanceAs (EffectMonoid M)

/-! ### Binary coproducts: pairs with orthogonal weights -/

section Coprod

variable (X Y : WMod M)

/-- The carrier of the coproduct `X + Y`: pairs `(x, y)` with `|x| ⊥ |y|`. -/
def CP : Type u := {p : X.carrier × Y.carrier // Perp (X.weight p.1) (Y.weight p.2)}

variable {X Y}

theorem wperp_of_le {a a' : X.carrier} {b b' : Y.carrier} (ha : a ≼ a') (hb : b ≼ b')
    (h : Perp (X.weight a') (Y.weight b')) : Perp (X.weight a) (Y.weight b) :=
  (ovee_le_ovee (X.weight_mono ha) (Y.weight_mono hb) h).1

theorem wperp_congr {a a' : X.carrier} {b b' : Y.carrier} (ha : a = a') (hb : b = b')
    (h : Perp (X.weight a) (Y.weight b)) : Perp (X.weight a') (Y.weight b') := ha ▸ hb ▸ h

/-- Orthogonality in `X + Y`: componentwise, with orthogonal weights of the
sum. -/
def CPPerp (p q : CP X Y) : Prop :=
  ∃ h : Perp p.1.1 q.1.1 ∧ Perp p.1.2 q.1.2,
    Perp (X.weight (ovee _ _ h.1)) (Y.weight (ovee _ _ h.2))

noncomputable instance cpPCM : PCM (CP X Y) where
  zero := ⟨(0, 0), by rw [X.weight_zero, Y.weight_zero]; exact PCM.zero_perp 0⟩
  Perp := CPPerp
  ovee p q h := ⟨(ovee p.1.1 q.1.1 h.fst.1, ovee p.1.2 q.1.2 h.fst.2), h.snd⟩
  perp_comm {p q} h := ⟨⟨PCM.perp_comm h.fst.1, PCM.perp_comm h.fst.2⟩,
    wperp_congr (PCM.ovee_comm h.fst.1) (PCM.ovee_comm h.fst.2) h.snd⟩
  ovee_comm {p q} h := Subtype.ext (Prod.ext (PCM.ovee_comm h.fst.1) (PCM.ovee_comm h.fst.2))
  perp_of_ovee_perp {a b c} hab h :=
    ⟨⟨PCM.perp_of_ovee_perp hab.fst.1 h.fst.1, PCM.perp_of_ovee_perp hab.fst.2 h.fst.2⟩,
      wperp_of_le
        (fin_le_trans_eq (fin_le_ovee_right (PCM.perp_ovee_of_ovee_perp hab.fst.1 h.fst.1))
          (PCM.ovee_assoc hab.fst.1 h.fst.1).symm)
        (fin_le_trans_eq (fin_le_ovee_right (PCM.perp_ovee_of_ovee_perp hab.fst.2 h.fst.2))
          (PCM.ovee_assoc hab.fst.2 h.fst.2).symm) h.snd⟩
  perp_ovee_of_ovee_perp {a b c} hab h :=
    ⟨⟨PCM.perp_ovee_of_ovee_perp hab.fst.1 h.fst.1, PCM.perp_ovee_of_ovee_perp hab.fst.2 h.fst.2⟩,
      wperp_congr (PCM.ovee_assoc hab.fst.1 h.fst.1) (PCM.ovee_assoc hab.fst.2 h.fst.2) h.snd⟩
  ovee_assoc {a b c} hab h :=
    Subtype.ext (Prod.ext (PCM.ovee_assoc hab.fst.1 h.fst.1) (PCM.ovee_assoc hab.fst.2 h.fst.2))
  zero_perp a := ⟨⟨PCM.zero_perp _, PCM.zero_perp _⟩,
    wperp_congr (PCM.zero_ovee _).symm (PCM.zero_ovee _).symm a.2⟩
  zero_ovee a := Subtype.ext (Prod.ext (PCM.zero_ovee _) (PCM.zero_ovee _))

theorem cp_perp_iff (p q : CP X Y) : Perp p q ↔ CPPerp p q := Iff.rfl

theorem cp_ovee_val {p q : CP X Y} (h : Perp p q) :
    (ovee p q h).1 = (ovee p.1.1 q.1.1 h.fst.1, ovee p.1.2 q.1.2 h.fst.2) := rfl

theorem cp_zero_val : (0 : CP X Y).1 = (0, 0) := rfl

/-- The weight `|(x, y)| = |x| ⊕ |y|`. -/
def cpWeight (p : CP X Y) : M := ovee (X.weight p.1.1) (Y.weight p.1.2) p.2

theorem cp_smul_perp (r : M) (p : CP X Y) :
    Perp (X.weight (r • p.1.1)) (Y.weight (r • p.1.2)) := by
  rw [X.weight_smul, Y.weight_smul]; exact (emon_mul_ovee r p.2).1

instance cpSMul : SMul M (CP X Y) := ⟨fun r p => ⟨(r • p.1.1, r • p.1.2), cp_smul_perp r p⟩⟩

theorem cp_smul_val (r : M) (p : CP X Y) : (r • p).1 = (r • p.1.1, r • p.1.2) := rfl

variable (X Y)

/-- **SIG 33** (`prop:wmod-effectus`, main.tex:964), [Cho19, Prop. 3.5.9]:
the coproduct `X + Y` of `WMod[M]`, the pairs with orthogonal weights. -/
noncomputable def cp : WMod M where
  carrier := CP X Y
  weight := cpWeight
  one_smul p := Subtype.ext (Prod.ext (X.one_smul _) (Y.one_smul _))
  mul_smul r s p := Subtype.ext (Prod.ext (X.mul_smul r s _) (Y.mul_smul r s _))
  smul_biadditive := by
    refine ⟨fun r => ⟨Subtype.ext (Prod.ext (X.smul_zero r) (Y.smul_zero r)),
      fun {p q} h => ?_⟩, fun p => ⟨Subtype.ext (Prod.ext (X.zero_smul _) (Y.zero_smul _)),
      fun {r s} h => ?_⟩⟩
    · obtain ⟨k1, e1⟩ := X.smul_ovee r h.fst.1
      obtain ⟨k2, e2⟩ := Y.smul_ovee r h.fst.2
      refine ⟨⟨⟨k1, k2⟩, wperp_congr e1.symm e2.symm ?_⟩, Subtype.ext (Prod.ext e1 e2)⟩
      rw [X.weight_smul, Y.weight_smul]; exact (emon_mul_ovee r h.snd).1
    · obtain ⟨k1, e1⟩ := X.ovee_smul h p.1.1
      obtain ⟨k2, e2⟩ := Y.ovee_smul h p.1.2
      refine ⟨⟨⟨k1, k2⟩, wperp_congr e1.symm e2.symm ?_⟩, Subtype.ext (Prod.ext e1 e2)⟩
      rw [X.weight_smul, Y.weight_smul]; exact (emon_mul_ovee _ p.2).1
  weight_additive := by
    refine ⟨?_, fun {p q} h => ?_⟩
    · show ovee (X.weight 0) (Y.weight 0) _ = 0
      exact (PCM.ovee_congr X.weight_zero Y.weight_zero _ (PCM.zero_perp 0)).trans
        (PCM.zero_ovee 0)
    · obtain ⟨a1, ea1⟩ := X.weight_ovee h.fst.1
      obtain ⟨a2, ea2⟩ := Y.weight_ovee h.fst.2
      have hp : Perp (ovee _ _ a1) (ovee _ _ a2) := by rw [ea1, ea2]; exact h.snd
      obtain ⟨hac, hbd, h', e⟩ := fin_middle_four a1 a2 hp
      exact ⟨h', e.trans (PCM.ovee_congr ea1 ea2 hp h.snd)⟩
  weight_smul r p := by
    obtain ⟨k, e⟩ := emon_mul_ovee r p.2
    exact (PCM.ovee_congr (X.weight_smul r _) (Y.weight_smul r _) _ k).trans e.symm
  eq_zero_of_weight p h := by
    obtain ⟨h1, h2⟩ := eabasics_positivity p.2 h
    exact Subtype.ext (Prod.ext (X.eq_zero_of_weight _ h1) (Y.eq_zero_of_weight _ h2))
  perp_of_weight {p q} h := by
    have k1 : Perp p.1.1 q.1.1 := X.perp_of_weight
      (ovee_le_ovee (fin_le_ovee_left p.2) (fin_le_ovee_left q.2) h).1
    have k2 : Perp p.1.2 q.1.2 := Y.perp_of_weight
      (ovee_le_ovee (fin_le_ovee_right p.2) (fin_le_ovee_right q.2) h).1
    refine ⟨⟨k1, k2⟩, ?_⟩
    obtain ⟨a1, ea1⟩ := X.weight_ovee k1
    obtain ⟨a2, ea2⟩ := Y.weight_ovee k2
    obtain ⟨hac, hbd, h', -⟩ := fin_middle_four p.2 q.2 h
    rw [← ea1, ← ea2]
    exact h'

variable {X Y}

theorem cp_weight (p : (cp X Y).carrier) :
    (cp X Y).weight p = ovee (X.weight p.1.1) (Y.weight p.1.2) p.2 := rfl

theorem perp_wzero_r (Y : WMod M) (a : M) : Perp a (Y.weight 0) := by
  rw [Y.weight_zero]; exact PCM.perp_zero a

theorem perp_wzero_l (X : WMod M) (a : M) : Perp (X.weight 0) a := by
  rw [X.weight_zero]; exact PCM.zero_perp a

/-- The left injection `x ↦ (x, 0)`. -/
noncomputable def inl : X ⟶ cp X Y where
  toFun x := ⟨(x, 0), by rw [Y.weight_zero]; exact PCM.perp_zero _⟩
  additive := ⟨rfl, fun {x y} h => ⟨⟨⟨h, PCM.zero_perp 0⟩,
    wperp_congr rfl (PCM.zero_ovee 0).symm (perp_wzero_r Y _)⟩,
    Subtype.ext (Prod.ext rfl (PCM.zero_ovee 0))⟩⟩
  map_smul r x := Subtype.ext (Prod.ext rfl (Y.smul_zero r).symm)
  weight_le x := fin_le_of_eq ((PCM.ovee_congr rfl Y.weight_zero _ (PCM.perp_zero _)).trans
    (PCM.ovee_zero _ _))

/-- The right injection `y ↦ (0, y)`. -/
noncomputable def inr : Y ⟶ cp X Y where
  toFun y := ⟨(0, y), by rw [X.weight_zero]; exact PCM.zero_perp _⟩
  additive := ⟨rfl, fun {x y} h => ⟨⟨⟨PCM.zero_perp 0, h⟩,
    wperp_congr (PCM.zero_ovee 0).symm rfl (perp_wzero_l X _)⟩,
    Subtype.ext (Prod.ext (PCM.zero_ovee 0) rfl)⟩⟩
  map_smul r x := Subtype.ext (Prod.ext (X.smul_zero r).symm rfl)
  weight_le y := fin_le_of_eq ((PCM.ovee_congr X.weight_zero rfl _ (PCM.zero_perp _)).trans
    (PCM.zero_ovee _))

/-- The first projection `(x, y) ↦ x` (the partial projection `▷₁`). -/
def fst : cp X Y ⟶ X where
  toFun p := p.1.1
  additive := ⟨rfl, fun h => ⟨h.fst.1, rfl⟩⟩
  map_smul _ _ := rfl
  weight_le p := fin_le_ovee_left p.2

/-- The second projection `(x, y) ↦ y` (the partial projection `▷₂`). -/
def snd : cp X Y ⟶ Y where
  toFun p := p.1.2
  additive := ⟨rfl, fun h => ⟨h.fst.2, rfl⟩⟩
  map_smul _ _ := rfl
  weight_le p := fin_le_ovee_right p.2

variable {Z : WMod M}

theorem desc_perp (f : X ⟶ Z) (g : Y ⟶ Z) (p : CP X Y) : Perp (f.toFun p.1.1) (g.toFun p.1.2) :=
  Z.perp_of_weight (ovee_le_ovee (f.weight_le _) (g.weight_le _) p.2).1

/-- The cotuple `[f, g] : (x, y) ↦ f x ⊕ g y`. -/
noncomputable def desc (f : X ⟶ Z) (g : Y ⟶ Z) : cp X Y ⟶ Z where
  toFun p := ovee (f.toFun p.1.1) (g.toFun p.1.2) (desc_perp f g p)
  additive := by
    refine ⟨?_, fun {p q} h => ?_⟩
    · exact (PCM.ovee_congr f.map_zero g.map_zero _ (PCM.zero_perp 0)).trans (PCM.zero_ovee 0)
    · obtain ⟨hf, ef⟩ := f.map_ovee h.fst.1
      obtain ⟨hg, eg⟩ := g.map_ovee h.fst.2
      have hp : Perp (ovee _ _ hf) (ovee _ _ hg) := by
        rw [ef, eg]; exact desc_perp f g (ovee p q h)
      obtain ⟨hac, hbd, h', e⟩ := fin_middle_four hf hg hp
      exact ⟨h', e.trans (PCM.ovee_congr ef eg hp _)⟩
  map_smul r p := by
    obtain ⟨k, e⟩ := Z.smul_ovee r (desc_perp f g p)
    exact (PCM.ovee_congr (f.map_smul r _) (g.map_smul r _) _ k).trans e
  weight_le p := by
    obtain ⟨a, ea⟩ := Z.weight_ovee (desc_perp f g p)
    rw [← ea]
    exact (ovee_le_ovee (f.weight_le _) (g.weight_le _) p.2).2

theorem inl_desc (f : X ⟶ Z) (g : Y ⟶ Z) : inl ≫ desc f g = f :=
  hom_ext fun _ => (PCM.ovee_congr rfl g.map_zero _ (PCM.perp_zero _)).trans (PCM.ovee_zero _ _)

theorem inr_desc (f : X ⟶ Z) (g : Y ⟶ Z) : inr ≫ desc f g = g :=
  hom_ext fun _ => (PCM.ovee_congr f.map_zero rfl _ (PCM.zero_perp _)).trans (PCM.zero_ovee _)

theorem inl_perp_inr (p : CP X Y) :
    Perp ((inl : X ⟶ cp X Y).toFun p.1.1) ((inr : Y ⟶ cp X Y).toFun p.1.2) :=
  ⟨⟨PCM.perp_zero _, PCM.zero_perp _⟩,
    wperp_congr (PCM.ovee_zero _ _).symm (PCM.zero_ovee _).symm p.2⟩

theorem eq_ovee_inl_inr (p : CP X Y) : p = ovee _ _ (inl_perp_inr p) :=
  Subtype.ext (Prod.ext (PCM.ovee_zero _ _).symm (PCM.zero_ovee _).symm)

theorem desc_unique (f : X ⟶ Z) (g : Y ⟶ Z) (m : cp X Y ⟶ Z) (h1 : inl ≫ m = f)
    (h2 : inr ≫ m = g) : m = desc f g := by
  refine hom_ext fun p => ?_
  obtain ⟨k, e⟩ := m.map_ovee (inl_perp_inr p)
  calc m.toFun p = m.toFun (ovee _ _ (inl_perp_inr p)) := congrArg m.toFun (eq_ovee_inl_inr p)
    _ = ovee _ _ k := e.symm
    _ = (desc f g).toFun p := PCM.ovee_congr (congrArg (fun k => Hom.toFun k p.1.1) h1)
          (congrArg (fun k => Hom.toFun k p.1.2) h2) _ _

variable (X Y)

/-- The coproduct cocone of `WMod[M]`. -/
noncomputable def cpCofan : BinaryCofan X Y := BinaryCofan.mk inl inr

/-- **SIG 33** ([Cho19, Prop. 3.5.9]): the pairs with orthogonal weights
form the coproduct `X + Y` in `WMod[M]`. -/
noncomputable def cpIsColimit : IsColimit (cpCofan X Y) :=
  BinaryCofan.IsColimit.mk _ (fun f g => desc f g) (fun f g => inl_desc f g)
    (fun f g => inr_desc f g) (fun f g m h1 h2 => desc_unique f g m h1 h2)

end Coprod

/-! ### The initial object `{0}` -/

/-- The trivial PCM on `PUnit`. -/
def punitPCM : PCM PUnit.{u + 1} where
  zero := PUnit.unit
  Perp _ _ := True
  ovee _ _ _ := PUnit.unit
  perp_comm _ := trivial
  ovee_comm _ := rfl
  perp_of_ovee_perp _ _ := trivial
  perp_ovee_of_ovee_perp _ _ := trivial
  ovee_assoc _ _ := rfl
  zero_perp _ := trivial
  zero_ovee _ := rfl

/-- The zero weight module `{0}`. -/
def zeroObj (M : Type u) [EffectMonoid M] : WMod M :=
  @WMod.mk M _ PUnit punitPCM ⟨fun _ _ => PUnit.unit⟩ (fun _ => 0) (fun _ => rfl) (fun _ _ _ => rfl)
    ⟨fun _ => ⟨rfl, fun _ => ⟨trivial, rfl⟩⟩, fun _ => ⟨rfl, fun _ => ⟨trivial, rfl⟩⟩⟩
    ⟨rfl, fun _ => ⟨PCM.zero_perp 0, PCM.zero_ovee 0⟩⟩ (fun r _ => (exc_emonzero r).1.symm)
    (fun _ _ => rfl) (fun _ => trivial)

/-- The zero map. -/
def zeroHom (X Y : WMod M) : X ⟶ Y where
  toFun _ := 0
  additive := ⟨rfl, fun _ => ⟨PCM.zero_perp 0, PCM.zero_ovee 0⟩⟩
  map_smul r _ := (Y.smul_zero r).symm
  weight_le _ := by rw [Y.weight_zero]; exact pcm_zero_le _

/-- `{0}` is initial in `WMod[M]`. -/
def zeroIsInitial : IsInitial (zeroObj M) :=
  IsInitial.ofUniqueHom (fun T => zeroHom _ T) (fun _ m => hom_ext fun _ => m.map_zero)

instance : HasBinaryCoproducts (WMod M) :=
  @hasBinaryCoproducts_of_hasColimit_pair _ _ fun {X Y} => HasColimit.mk ⟨_, cpIsColimit X Y⟩

instance : HasInitial (WMod M) := zeroIsInitial.hasInitial

instance : HasFiniteCoproducts (WMod M) := hasFiniteCoproducts_of_has_binary_and_initial

/-! ### The hom-PCM of `WMod[M]` -/

section Homs

variable {X Y : WMod M}

/-- `f ⊥ g` in `WMod[M](X, Y)`: pointwise orthogonal, with
`|f x ⊕ g x| ≤ |x|`. -/
def HomPerp (f g : X ⟶ Y) : Prop :=
  ∀ x, ∃ h : Perp (f.toFun x) (g.toFun x), Y.weight (ovee _ _ h) ≼ X.weight x

/-- The pointwise sum. -/
noncomputable def oveeHom (f g : X ⟶ Y) (h : HomPerp f g) : X ⟶ Y where
  toFun x := ovee (f.toFun x) (g.toFun x) (h x).fst
  additive := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · exact (PCM.ovee_congr f.map_zero g.map_zero _ (PCM.zero_perp 0)).trans (PCM.zero_ovee 0)
    · obtain ⟨hf, ef⟩ := f.map_ovee hab
      obtain ⟨hg, eg⟩ := g.map_ovee hab
      have hp : Perp (ovee _ _ hf) (ovee _ _ hg) := by rw [ef, eg]; exact (h (ovee a b hab)).fst
      obtain ⟨hac, hbd, h', e⟩ := fin_middle_four hf hg hp
      exact ⟨h', e.trans (PCM.ovee_congr ef eg hp _)⟩
  map_smul r x := by
    obtain ⟨k, e⟩ := Y.smul_ovee r (h x).fst
    exact (PCM.ovee_congr (f.map_smul r x) (g.map_smul r x) _ k).trans e
  weight_le x := (h x).snd

theorem wle_congr {a a' : Y.carrier} {c : M} (e : a = a') (h : Y.weight a ≼ c) :
    Y.weight a' ≼ c := e ▸ h

variable (X Y)

/-- **SIG 33** (the hom-PCMs, [Cho19, Prop. 3.5.9]): `WMod[M](X, Y)` with
the pointwise partial sum, defined when `|f x ⊕ g x| ≤ |x|` for all `x`. -/
noncomputable instance homPCM : PCM (X ⟶ Y) where
  zero := zeroHom X Y
  Perp := HomPerp
  ovee f g h := oveeHom f g h
  perp_comm h x := ⟨PCM.perp_comm (h x).fst, wle_congr (PCM.ovee_comm (h x).fst) (h x).snd⟩
  ovee_comm h := hom_ext fun x => PCM.ovee_comm (h x).fst
  perp_of_ovee_perp hab h x := ⟨PCM.perp_of_ovee_perp (hab x).fst (h x).fst,
    pcm_preorder_trans (Y.weight_mono (fin_le_trans_eq
      (fin_le_ovee_right (PCM.perp_ovee_of_ovee_perp (hab x).fst (h x).fst))
      (PCM.ovee_assoc (hab x).fst (h x).fst).symm)) (h x).snd⟩
  perp_ovee_of_ovee_perp hab h x := ⟨PCM.perp_ovee_of_ovee_perp (hab x).fst (h x).fst,
    wle_congr (PCM.ovee_assoc (hab x).fst (h x).fst) (h x).snd⟩
  ovee_assoc hab h := hom_ext fun x => PCM.ovee_assoc (hab x).fst (h x).fst
  zero_perp f x := ⟨PCM.zero_perp _, wle_congr (PCM.zero_ovee _).symm (f.weight_le x)⟩
  zero_ovee _ := hom_ext fun _ => PCM.zero_ovee _

variable {X Y}

theorem hom_perp_def (f g : X ⟶ Y) : Perp f g ↔ HomPerp f g := Iff.rfl

theorem hom_ovee_apply {f g : X ⟶ Y} (h : Perp f g) (x : X.carrier) :
    (ovee f g h).toFun x = ovee (f.toFun x) (g.toFun x) (h x).fst := rfl

theorem hom_zero_apply (x : X.carrier) : (0 : X ⟶ Y).toFun x = 0 := rfl

end Homs

/-! ### `WMod[M]` is an effectus (SIG 33) -/

section Effectus

/-- The chosen binary coproduct is the explicit one. -/
noncomputable def coprodIsoCP (X Y : WMod M) : X ⨿ Y ≅ cp X Y :=
  (coprodIsCoprod X Y).coconePointUniqueUpToIso (cpIsColimit X Y)

theorem inl_coprodIsoCP (X Y : WMod M) : coprod.inl ≫ (coprodIsoCP X Y).hom = inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod X Y) (cpIsColimit X Y)
    ⟨WalkingPair.left⟩

theorem inr_coprodIsoCP (X Y : WMod M) : coprod.inr ≫ (coprodIsoCP X Y).hom = inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod X Y) (cpIsColimit X Y)
    ⟨WalkingPair.right⟩

theorem pproj₁_eq (X Y : WMod M) : pproj₁ X Y = (coprodIsoCP X Y).hom ≫ fst := by
  refine coprod.hom_ext ?_ ?_
  · rw [fin_inl_pproj₁, ← Category.assoc, inl_coprodIsoCP]; exact hom_ext fun _ => rfl
  · rw [fin_inr_pproj₁, ← Category.assoc, inr_coprodIsoCP]; exact hom_ext fun _ => rfl

theorem pproj₂_eq (X Y : WMod M) : pproj₂ X Y = (coprodIsoCP X Y).hom ≫ snd := by
  refine coprod.hom_ext ?_ ?_
  · rw [fin_inl_pproj₂, ← Category.assoc, inl_coprodIsoCP]; exact hom_ext fun _ => rfl
  · rw [fin_inr_pproj₂, ← Category.assoc, inr_coprodIsoCP]; exact hom_ext fun _ => rfl

/-- **SIG 33** ([Cho19, Prop. 3.5.9]): `WMod[M]` is a finPAC. -/
instance finPAC : FinPAC (WMod M) where
  comp_ovee {X Y Z f g} h k := by
    refine ⟨fun x => ⟨(k.map_ovee (h x).fst).1, wle_congr ((k.map_ovee (h x).fst).2).symm
      (pcm_preorder_trans (k.weight_le _) (h x).snd)⟩, hom_ext fun x => ?_⟩
    exact ((k.map_ovee (h x).fst).2).symm
  ovee_comp {W X Y f g} h k :=
    ⟨fun w => ⟨(h (k.toFun w)).fst, pcm_preorder_trans (h _).snd (k.weight_le w)⟩,
      hom_ext fun _ => rfl⟩
  comp_zero {X Y Z} f := hom_ext fun _ => rfl
  zero_comp {X Y Z} f := hom_ext fun _ => f.map_zero
  compatible_sum {X Y} b := by
    rw [pproj₁_eq, pproj₂_eq]
    intro x
    let p := (coprodIsoCP Y Y).hom.toFun (b.toFun x)
    obtain ⟨a, ea⟩ := Y.weight_ovee (Y.perp_of_weight p.2)
    exact ⟨Y.perp_of_weight p.2, fin_eq_trans_le ea.symm
      (pcm_preorder_trans ((coprodIsoCP Y Y).hom.weight_le _) (b.weight_le x))⟩
  untying {X Y f g} h := by
    intro x
    obtain ⟨k, hk⟩ := h x
    obtain ⟨a, ea⟩ := Y.weight_ovee k
    have hq : Perp ((inl : Y ⟶ cp Y Y).toFun (f.toFun x)) ((inr : Y ⟶ cp Y Y).toFun (g.toFun x)) :=
      ⟨⟨PCM.perp_zero _, PCM.zero_perp _⟩, wperp_congr (PCM.ovee_zero _ _).symm
        (PCM.zero_ovee _).symm a⟩
    have e1 : (coprodIsoCP Y Y).hom.toFun ((coprod.inl : Y ⟶ Y ⨿ Y).toFun (f.toFun x)) =
        (inl : Y ⟶ cp Y Y).toFun (f.toFun x) :=
      congrArg (fun k => Hom.toFun k (f.toFun x)) (inl_coprodIsoCP Y Y)
    have e2 : (coprodIsoCP Y Y).hom.toFun ((coprod.inr : Y ⟶ Y ⨿ Y).toFun (g.toFun x)) =
        (inr : Y ⟶ cp Y Y).toFun (g.toFun x) :=
      congrArg (fun k => Hom.toFun k (g.toFun x)) (inr_coprodIsoCP Y Y)
    have hq' : Perp ((coprodIsoCP Y Y).hom.toFun ((coprod.inl : Y ⟶ Y ⨿ Y).toFun (f.toFun x)))
        ((coprodIsoCP Y Y).hom.toFun ((coprod.inr : Y ⟶ Y ⨿ Y).toFun (g.toFun x))) := by
      rw [e1, e2]; exact hq
    obtain ⟨h', ew⟩ := iso_perp (coprodIsoCP Y Y) hq'
    refine ⟨h', ?_⟩
    show (Y ⨿ Y).weight (ovee _ _ h') ≼ X.weight x
    rw [ew]
    have e3 : ovee _ _ hq' = ovee _ _ hq := PCM.ovee_congr e1 e2 hq' hq
    rw [e3]
    refine fin_eq_trans_le ?_ (fin_eq_trans_le ea hk)
    exact PCM.ovee_congr (congrArg Y.weight (PCM.ovee_zero _ _))
      (congrArg Y.weight (PCM.zero_ovee _)) _ a

/-- The truth map `1_X = |·| : X → M`. -/
def oneHom (X : WMod M) : X ⟶ unit M where
  toFun := X.weight
  additive := X.weight_additive
  map_smul r x := X.weight_smul r x
  weight_le _ := pcm_preorder_refl _

/-- The orthosupplement `p^⊥ : x ↦ |x| ⊖ p(x)`. -/
noncomputable def orthHom {X : WMod M} (p : X ⟶ unit M) : X ⟶ unit M where
  toFun x := ominus (E := M) (X.weight x) (p.toFun x) (p.weight_le x)
  additive := by
    refine ⟨fin_ominus_eq _ ⟨PCM.perp_zero _, (PCM.ovee_zero _ _).trans
      (p.map_zero.trans X.weight_zero.symm)⟩, fun {x y} h => ?_⟩
    obtain ⟨hw, ew⟩ := X.weight_ovee h
    obtain ⟨hp, ep⟩ := p.map_ovee h
    have h2 : @ovee M _ (p.toFun x) (p.toFun y) hp ≼ ovee (X.weight x) (X.weight y) hw := by
      rw [ep, ew]; exact p.weight_le _
    obtain ⟨h', e⟩ := fin_ominus_ovee (p.weight_le x) (p.weight_le y) hw hp h2
    exact ⟨h', e.trans (SWMod.ominus_congr ew ep _ _)⟩
  map_smul r x := by
    have hle : r * p.toFun x ≼ r * X.weight x := emon_mul_mono_right r (p.weight_le x)
    exact (SWMod.ominus_congr (X.weight_smul r x) (p.map_smul r x) _ hle).trans
      (SWMod.ominus_smul r _ _ _ hle)
  weight_le x := exc_dposet_D2 (isDiff_ominus (E := M) _)

/-- **SIG 33** (`prop:wmod-effectus`, main.tex:964, Proposition), the case of
an effect monoid (cited there as [Cho19, Prop. 3.5.9]): for an effect monoid
`M`, `WMod[M]` is an effectus, with unit object `M`, truth maps the weights,
orthosupplement `x ↦ |x| ⊖ p(x)`, and binary coproducts the pairs with
orthogonal weights (`cpIsColimit`). -/
noncomputable instance effectus : EffectusPartialForm (WMod M) where
  I := unit M
  one X := oneHom X
  orth p := orthHom p
  perp_orth p x := ⟨(isDiff_ominus (E := M) (p.weight_le x)).fst,
    fin_le_of_eq (isDiff_ominus (E := M) (p.weight_le x)).snd⟩
  ovee_orth p := hom_ext fun x => (isDiff_ominus (E := M) (p.weight_le x)).snd
  orth_unique {X p q} h e := hom_ext fun x =>
    (fin_ominus_eq (E := M) _ ⟨(h x).fst, congrArg (fun k => Hom.toFun k x) e⟩).symm
  eq_zero_of_perp_one {X p} h := hom_ext fun x => by
    obtain ⟨k, hle⟩ := h x
    show p.toFun x = 0
    have hk : @Perp M _ (p.toFun x) (X.weight x) := k
    have hle' : @ovee M _ (p.toFun x) (X.weight x) hk ≼ X.weight x := hle
    have h2 : @ovee M _ (X.weight x) (p.toFun x) (PCM.perp_comm hk) ≼
        @ovee M _ (X.weight x) 0 (PCM.perp_zero _) :=
      fin_eq_trans_le (PCM.ovee_comm hk).symm (fin_le_trans_eq hle' (PCM.ovee_zero _ _).symm)
    exact eq_zero_of_le_zero (le_of_ovee_le_ovee _ _ h2)
  eq_zero_of_one_zero {X Y f} h :=
    hom_ext fun x => Y.eq_zero_of_weight _ (congrArg (fun k => Hom.toFun k x) h)
  perp_of_one_perp {X Y f g} h x := by
    obtain ⟨k, hle⟩ := h x
    have hp := Y.perp_of_weight k
    obtain ⟨a, ea⟩ := Y.weight_ovee hp
    exact ⟨hp, fin_eq_trans_le ea.symm hle⟩

/-- Right multiplication `t ↦ t · r` on the unit object. -/
def rmul (r : M) : unit M ⟶ unit M where
  toFun := fun (t : M) => t * r
  additive := ⟨(exc_emonzero r).2, fun {a b} h => by
    obtain ⟨h', e⟩ := emon_ovee_mul r h; exact ⟨h', e.symm⟩⟩
  map_smul s t := EffectMonoid.mul_assoc s t r
  weight_le t := fin_le_trans_eq (emon_mul_mono_right t (ea_le_one r)) (EffectMonoid.mul_one t)

/-- **SIG 33** (main.tex:964), "with scalars": the scalars of the effectus
`WMod[M]` are the maps `t ↦ t · r`, and `p ↦ p(1)` is an isomorphism of
effect monoids onto the **opposite** monoid `Mᵒᵖ` (composition of scalars is
`t ↦ t · r · s` for `s ∘ r`).  So the scalars are `M` as an effect algebra,
and as an effect monoid exactly when `M ≅ Mᵒᵖ` (e.g. `M` commutative); this
is the form that makes SIG 34 (`sSt : C → WMod[Mᵒᵖ]`, a morphism of
effectuses, hence scalar-preserving) consistent. -/
theorem effectus_scalars : EMIso (Scal (WMod M)) (MOp M) := by
  let φ : EffectMonoidHom (Scal (WMod M)) (MOp M) :=
    { toFun := fun p => (show MOp M from p.toFun (1 : M))
      perp_map := fun {p q} h => (h (1 : M)).fst
      ovee_map := fun {p q} h => rfl
      map_one := rfl
      map_mul := fun l m => by
        show l.toFun (m.toFun (1 : M)) = @HMul.hMul M M M _ (m.toFun (1 : M)) (l.toFun (1 : M))
        have := l.map_smul (m.toFun (1 : M)) (1 : M)
        exact (congrArg l.toFun (EffectMonoid.mul_one _).symm).trans this }
  let ψ : EffectMonoidHom (MOp M) (Scal (WMod M)) :=
    { toFun := fun r => rmul (M := M) r
      perp_map := fun {r s} h t => by
        obtain ⟨k, e⟩ := emon_mul_ovee (M := M) t h
        exact ⟨k, fin_le_trans_eq (fin_eq_trans_le e.symm
          (emon_mul_mono_right t (ea_le_one _))) (EffectMonoid.mul_one t)⟩
      ovee_map := fun {r s} h => hom_ext fun (t : M) => by
        obtain ⟨k, e⟩ := emon_mul_ovee (M := M) t h
        exact e.trans (PCM.ovee_congr rfl rfl _ _)
      map_one := hom_ext fun (t : M) => EffectMonoid.mul_one t
      map_mul := fun r s => hom_ext fun (t : M) => by
        show @HMul.hMul M M M _ t (@HMul.hMul M M M _ s r) =
          @HMul.hMul M M M _ (@HMul.hMul M M M _ t s) r
        exact (EffectMonoid.mul_assoc t s r).symm }
  refine ⟨φ, ψ, fun p => hom_ext fun (t : M) => ?_, fun r => EffectMonoid.one_mul (M := M) r⟩
  show @HMul.hMul M M M _ t (p.toFun (1 : M)) = p.toFun t
  exact (p.map_smul t (1 : M)).symm.trans (congrArg p.toFun (EffectMonoid.mul_one t))

end Effectus

end WMod

/-! ## SIG 34: `sSt : C → WMod[Mᵒᵖ]` -/

section SubstateFunctor

variable {C : Type u} [Category.{u} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

theorem fin_le_comp_left {W X Y : C} {a b : X ⟶ Y} (h : a ≼ b) (k : W ⟶ X) : k ≫ a ≼ k ≫ b := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨h', e⟩ := FinPAC.ovee_comp hc k
  exact ⟨k ≫ c, h', e.symm⟩

/-- A substate of `X + Y` is the pairing of its two partial projections
(181VII). -/
theorem fin_eq_effPair {Z X Y : C} (ω : Z ⟶ X ⨿ Y) :
    ω = effPair (ω ≫ pproj₁ X Y) (ω ≫ pproj₂ X Y) (coprod_prod_converse ω) :=
  (coprod_prod (coprod_prod_converse ω)).unique ⟨rfl, rfl⟩ (effPair_spec _ _ _)

/-- `1 ∘ ω = (1 ∘ ▷₁ ∘ ω) ⊕ (1 ∘ ▷₂ ∘ ω)` (181IX). -/
theorem fin_truth_decomp {Z X Y : C} (ω : Z ⟶ X ⨿ Y) :
    ω ≫ truth (X ⨿ Y) = ovee ((ω ≫ pproj₁ X Y) ≫ truth X) ((ω ≫ pproj₂ X Y) ≫ truth Y)
      (coprod_prod_converse ω) := by
  have := eff_prod_rules_2 (ω ≫ pproj₁ X Y) (ω ≫ pproj₂ X Y) (coprod_prod_converse ω)
  rw [← fin_eq_effPair ω] at this
  exact this

/-- **SIG 31** (main.tex:910, Example), finite case: the substates
`sSt(A) = C(I, A)` of an effectus with scalars `M` form a weight
`Mᵒᵖ`-module, with action `r · ω = ω ∘ r` and weight `|ω| = 1 ∘ ω`. -/
noncomputable abbrev finSStObj (A : C) : WMod (MOp (Scal C)) where
  carrier := Substate A
  act := ⟨fun r ω => (show Scal C from r) ≫ ω⟩
  weight ω := ω ≫ truth A
  one_smul ω := by
    show truth (effObj C) ≫ ω = ω
    rw [truth_effObj_eq_id, Category.id_comp]
  mul_smul r s ω := Category.assoc (show Scal C from r) (show Scal C from s) ω
  smul_biadditive := by
    refine ⟨fun r => ⟨FinPAC.comp_zero (show Scal C from r), fun h => ?_⟩,
      fun ω => ⟨FinPAC.zero_comp ω, fun h => ?_⟩⟩
    · obtain ⟨h', e⟩ := FinPAC.ovee_comp h (show Scal C from r); exact ⟨h', e.symm⟩
    · obtain ⟨h', e⟩ := FinPAC.comp_ovee h ω; exact ⟨h', e.symm⟩
  weight_additive := ⟨FinPAC.zero_comp _, fun h => by
    obtain ⟨h', e⟩ := FinPAC.comp_ovee h (truth A); exact ⟨h', e.symm⟩⟩
  weight_smul r ω := Category.assoc (show Scal C from r) ω (truth A)
  eq_zero_of_weight ω h := EffectusPartialForm.eq_zero_of_one_zero h
  perp_of_weight h := EffectusPartialForm.perp_of_one_perp h

/-- `sSt f = f ∘ (-)`. -/
noncomputable def finSStMap {A B : C} (f : A ⟶ B) : finSStObj A ⟶ finSStObj B where
  toFun ω := ω ≫ f
  additive := ⟨FinPAC.zero_comp f, fun h => by
    obtain ⟨h', e⟩ := FinPAC.comp_ovee h f; exact ⟨h', e.symm⟩⟩
  map_smul r ω := Category.assoc _ ω f
  weight_le := fun (ω : effObj C ⟶ A) => by
    show (ω ≫ f) ≫ truth B ≼ ω ≫ truth A
    rw [Category.assoc]
    exact fin_le_comp_left (ea_le_one (E := A ⟶ effObj C) (f ≫ truth B)) ω

/-- **SIG 34**: the functor `sSt : C → WMod[Mᵒᵖ]`, `A ↦ C(I, A)`. -/
noncomputable def finSStFunctor : C ⥤ WMod (MOp (Scal C)) where
  obj A := finSStObj A
  map f := finSStMap f
  map_id _ := WMod.hom_ext fun ω => Category.comp_id ω
  map_comp f g := WMod.hom_ext fun ω => (Category.assoc ω f g).symm

section Desc

variable {X Y : C} {T : WMod (MOp (Scal C))} (f : finSStObj X ⟶ T) (g : finSStObj Y ⟶ T)

theorem finSSt_desc_perp (ω : Substate (X ⨿ Y)) :
    Perp (f.toFun (ω ≫ pproj₁ X Y)) (g.toFun (ω ≫ pproj₂ X Y)) :=
  T.perp_of_weight (ovee_le_ovee (f.weight_le _) (g.weight_le _) (coprod_prod_converse ω)).1

/-- The cotuple `[f, g] : sSt(X + Y) → T`, `ω ↦ f(▷₁ ω) ⊕ g(▷₂ ω)`. -/
noncomputable def finSStDesc : finSStObj (X ⨿ Y) ⟶ T where
  toFun ω := ovee (f.toFun (ω ≫ pproj₁ X Y)) (g.toFun (ω ≫ pproj₂ X Y)) (finSSt_desc_perp f g ω)
  additive := by
    refine ⟨?_, fun {ω ω'} h => ?_⟩
    · have z1 : f.toFun ((0 : Substate (X ⨿ Y)) ≫ pproj₁ X Y) = 0 := by
        rw [FinPAC.zero_comp]; exact f.map_zero
      have z2 : g.toFun ((0 : Substate (X ⨿ Y)) ≫ pproj₂ X Y) = 0 := by
        rw [FinPAC.zero_comp]; exact g.map_zero
      exact (PCM.ovee_congr z1 z2 _ (PCM.zero_perp 0)).trans (PCM.zero_ovee 0)
    · obtain ⟨h1, e1⟩ := FinPAC.comp_ovee h (pproj₁ X Y)
      obtain ⟨h2, e2⟩ := FinPAC.comp_ovee h (pproj₂ X Y)
      obtain ⟨hf, ef⟩ := f.map_ovee h1
      obtain ⟨hg, eg⟩ := g.map_ovee h2
      have E1 : f.toFun (ovee ω ω' h ≫ pproj₁ X Y) = ovee _ _ hf := (congrArg f.toFun e1).trans ef.symm
      have E2 : g.toFun (ovee ω ω' h ≫ pproj₂ X Y) = ovee _ _ hg := (congrArg g.toFun e2).trans eg.symm
      have hp : Perp (ovee _ _ hf) (ovee _ _ hg) := by
        rw [← E1, ← E2]; exact finSSt_desc_perp f g (ovee ω ω' h)
      obtain ⟨hac, hbd, h', e⟩ := fin_middle_four hf hg hp
      exact ⟨h', e.trans (PCM.ovee_congr E1.symm E2.symm hp _)⟩
  map_smul r ω := by
    have a1 : f.toFun (((show Scal C from r) ≫ ω) ≫ pproj₁ X Y) = r • f.toFun (ω ≫ pproj₁ X Y) :=
      (congrArg f.toFun (Category.assoc (show Scal C from r) ω _)).trans (f.map_smul r _)
    have a2 : g.toFun (((show Scal C from r) ≫ ω) ≫ pproj₂ X Y) = r • g.toFun (ω ≫ pproj₂ X Y) :=
      (congrArg g.toFun (Category.assoc (show Scal C from r) ω _)).trans (g.map_smul r _)
    obtain ⟨k, e⟩ := T.smul_ovee r (finSSt_desc_perp f g ω)
    exact (PCM.ovee_congr a1 a2 _ k).trans e
  weight_le ω := by
    obtain ⟨a, ea⟩ := T.weight_ovee (finSSt_desc_perp f g ω)
    show T.weight (ovee _ _ (finSSt_desc_perp f g ω)) ≼ ω ≫ truth (X ⨿ Y)
    rw [← ea, fin_truth_decomp ω]
    exact (ovee_le_ovee (f.weight_le _) (g.weight_le _) _).2

theorem finSSt_inl_desc : finSStMap coprod.inl ≫ finSStDesc f g = f := by
  refine WMod.hom_ext fun (ω : Substate X) => ?_
  have a1 : f.toFun ((ω ≫ coprod.inl) ≫ pproj₁ X Y) = f.toFun ω := by
    rw [Category.assoc, fin_inl_pproj₁, Category.comp_id]
  have a2 : g.toFun ((ω ≫ coprod.inl) ≫ pproj₂ X Y) = 0 := by
    rw [Category.assoc, fin_inl_pproj₂, FinPAC.comp_zero]; exact g.map_zero
  exact (PCM.ovee_congr a1 a2 _ (PCM.perp_zero _)).trans (PCM.ovee_zero _ _)

theorem finSSt_inr_desc : finSStMap coprod.inr ≫ finSStDesc f g = g := by
  refine WMod.hom_ext fun (ω : Substate Y) => ?_
  have a1 : f.toFun ((ω ≫ coprod.inr) ≫ pproj₁ X Y) = 0 := by
    rw [Category.assoc, fin_inr_pproj₁, FinPAC.comp_zero]; exact f.map_zero
  have a2 : g.toFun ((ω ≫ coprod.inr) ≫ pproj₂ X Y) = g.toFun ω := by
    rw [Category.assoc, fin_inr_pproj₂, Category.comp_id]
  exact (PCM.ovee_congr a1 a2 _ (PCM.zero_perp _)).trans (PCM.zero_ovee _)

theorem finSSt_desc_unique (m : finSStObj (X ⨿ Y) ⟶ T) (h1 : finSStMap coprod.inl ≫ m = f)
    (h2 : finSStMap coprod.inr ≫ m = g) : m = finSStDesc f g := by
  refine WMod.hom_ext fun (ω : Substate (X ⨿ Y)) => ?_
  obtain ⟨hk, he⟩ := effPair_eq_ovee (ω ≫ pproj₁ X Y) (ω ≫ pproj₂ X Y) (coprod_prod_converse ω)
  have hω : ω = ovee _ _ hk := (fin_eq_effPair ω).trans he
  obtain ⟨k, e⟩ := m.map_ovee (X := finSStObj (X ⨿ Y)) hk
  calc m.toFun ω = m.toFun (ovee _ _ hk) := congrArg m.toFun hω
    _ = ovee _ _ k := e.symm
    _ = (finSStDesc f g).toFun ω :=
        PCM.ovee_congr (congrArg (fun k => WMod.Hom.toFun k (ω ≫ pproj₁ X Y)) h1)
          (congrArg (fun k => WMod.Hom.toFun k (ω ≫ pproj₂ X Y)) h2) _ _

end Desc

/-- `sSt(X + Y)` is the coproduct `sSt X + sSt Y` in `WMod[Mᵒᵖ]` (181VII). -/
noncomputable def finSStIsColimit (X Y : C) :
    IsColimit (BinaryCofan.mk (finSStMap (coprod.inl : X ⟶ X ⨿ Y)) (finSStMap coprod.inr)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => finSStDesc f g) (fun f g => finSSt_inl_desc f g)
    (fun f g => finSSt_inr_desc f g) (fun f g m h1 h2 => finSSt_desc_unique f g m h1 h2)

theorem finSSt_initial_eq_zero (ω : Substate (⊥_ C)) : ω = 0 := by
  refine EffectusPartialForm.eq_zero_of_one_zero ?_
  have : EffectusPartialForm.one (⊥_ C) = (0 : ⊥_ C ⟶ effObj C) := initial.hom_ext _ _
  rw [this]; exact FinPAC.comp_zero ω

/-- `sSt 0 = {0}` is initial in `WMod[Mᵒᵖ]`. -/
noncomputable def finSStInitialIsInitial : IsInitial (finSStObj (⊥_ C)) :=
  IsInitial.ofUniqueHom (fun T => WMod.zeroHom _ T) (fun _ m => WMod.hom_ext fun ω => by
    show m.toFun ω = 0
    rw [finSSt_initial_eq_zero ω]; exact m.map_zero)

instance finSStFunctor_preservesFiniteCoproducts :
    PreservesFiniteCoproducts (finSStFunctor (C := C)) :=
  fin_preservesFiniteCoproducts _ (fun X Y => finSStIsColimit X Y) finSStInitialIsInitial

/-- `sSt I` is the unit object `Mᵒᵖ`. -/
noncomputable def finUnitSStIso : WMod.unit (MOp (Scal C)) ≅ finSStObj (effObj C) where
  hom :=
    { toFun := fun (s : Scal C) => s
      additive := ⟨rfl, fun h => ⟨h, rfl⟩⟩
      map_smul := fun _ _ => rfl
      weight_le := fun (s : Scal C) => by
        show s ≫ truth (effObj C) ≼ s
        rw [truth_effObj_eq_id, Category.comp_id]; exact pcm_preorder_refl _ }
  inv :=
    { toFun := fun (s : Scal C) => s
      additive := ⟨rfl, fun h => ⟨h, rfl⟩⟩
      map_smul := fun _ _ => rfl
      weight_le := fun (s : Scal C) => by
        show s ≼ s ≫ truth (effObj C)
        rw [truth_effObj_eq_id, Category.comp_id]; exact pcm_preorder_refl _ }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **SIG 34** (main.tex:987, Proposition), the case of an effectus (cited
there as [Cho19, Lemma 4.2.11]): for an effectus `C` with scalars `M`,
`A ↦ sSt(A) = C(I, A)` is a morphism of effectuses `C → WMod[Mᵒᵖ]`: it
preserves finite coproducts (`sSt(X + Y) ≅ sSt X + sSt Y` by 181VII,
`sSt 0 = {0}`), the unit (`sSt(I) = Mᵒᵖ`) and the truth maps
(`sSt(1_A) = |·|`). -/
noncomputable def finSStMorphism : EffectusMorphism C (WMod (MOp (Scal C))) where
  F := finSStFunctor
  preserves := inferInstance
  u := finUnitSStIso
  map_truth _ := WMod.hom_ext fun _ => rfl

end SubstateFunctor

/-! ## SIG 32 (finite half): weight `{0,1}`-modules are pointed sets -/

namespace WMod

theorem bool_eq_zero_of_weight_false (X : WMod Bool) {x : X.carrier} (h : X.weight x = false) :
    x = 0 := X.eq_zero_of_weight x h

/-- **SIG 32** (`ex:weight-module-bool`, main.tex:947, Example): in a weight
`{0,1}`-module, nonzero elements have weight `1` ... -/
theorem bool_weight_eq_true_iff (X : WMod Bool) (x : X.carrier) : X.weight x = true ↔ x ≠ 0 := by
  constructor
  · rintro h rfl
    rw [X.weight_zero] at h
    exact Bool.false_ne_true h
  · intro h
    cases hw : X.weight x
    · exact absurd (X.eq_zero_of_weight x hw) h
    · rfl

/-- **SIG 32** (`ex:weight-module-bool`, main.tex:947, Example): ... and so
cannot be summed with nonzero elements: `x ⊥ y` iff `x = 0` or `y = 0`. -/
theorem bool_perp_iff (X : WMod Bool) (x y : X.carrier) : Perp x y ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro h
    have hw : X.weight x ⊓ X.weight y = ⊥ := (X.weight_ovee h).1
    cases hx : X.weight x
    · exact Or.inl (X.eq_zero_of_weight x hx)
    · rw [hx] at hw
      have : X.weight y = false := by simpa using hw
      exact Or.inr (X.eq_zero_of_weight y this)
  · rintro (rfl | rfl)
    · exact PCM.zero_perp _
    · exact PCM.perp_zero _

/-- The functor `WMod[{0,1}] → pSet`, `X ↦ (X, 0)`. -/
abbrev toPointed : WMod Bool ⥤ Pointed.{0} where
  obj X := ⟨X.carrier, 0⟩
  map f := ⟨f.toFun, f.map_zero⟩

instance : toPointed.Faithful where
  map_injective := fun {X Y} _ _ h => hom_ext fun x =>
    congrArg (fun k : toPointed.obj X ⟶ toPointed.obj Y => k.toFun x) h

/-- Every point-preserving map of weight `{0,1}`-modules is a morphism. -/
def ofPointedHom {X Y : WMod Bool} (g : toPointed.obj X ⟶ toPointed.obj Y) : X ⟶ Y where
  toFun := g.toFun
  additive := by
    have e0 : g.toFun 0 = 0 := g.map_point
    refine ⟨e0, fun {x y} h => ?_⟩
    rcases (bool_perp_iff X x y).1 h with rfl | rfl
    · exact ⟨(bool_perp_iff Y _ _).2 (Or.inl e0), (PCM.ovee_congr e0 rfl _ (PCM.zero_perp _)).trans
        ((PCM.zero_ovee _).trans (congrArg g.toFun (PCM.zero_ovee _).symm))⟩
    · exact ⟨(bool_perp_iff Y _ _).2 (Or.inr e0), (PCM.ovee_congr rfl e0 _ (PCM.perp_zero _)).trans
        ((PCM.ovee_zero _ _).trans (congrArg g.toFun (PCM.ovee_zero _ _).symm))⟩
  map_smul r x := by
    cases r
    · exact (congrArg g.toFun (X.zero_smul x)).trans (g.map_point.trans (Y.zero_smul _).symm)
    · exact (congrArg g.toFun (X.one_smul x)).trans (Y.one_smul _).symm
  weight_le x := by
    by_cases hx : x = 0
    · subst hx
      have e0 : g.toFun 0 = 0 := g.map_point
      show Y.weight (g.toFun 0) ≼ X.weight 0
      rw [e0, Y.weight_zero]; exact pcm_zero_le _
    · have : X.weight x = 1 := (bool_weight_eq_true_iff X x).2 hx
      rw [this]; exact ea_le_one _

instance : toPointed.Full where
  map_surjective g := ⟨ofPointedHom g, Pointed.Hom.ext rfl⟩

open Classical in
/-- The weight `{0,1}`-module of a pointed set `(P, p₀)`: `x ⊥ y` iff one of
them is `p₀`, and `x ⊕ p₀ = x = p₀ ⊕ x`; `|x| = 1` iff `x ≠ p₀`. -/
noncomputable def ofPointed (P : Pointed.{0}) : WMod Bool :=
  let _ : PCM P.X :=
    { zero := P.point
      Perp := fun x y => x = P.point ∨ y = P.point
      ovee := fun x y _ => if x = P.point then y else x
      perp_comm := fun h => h.symm
      ovee_comm := by
        intro x y h
        by_cases hx : x = P.point <;> by_cases hy : y = P.point <;> simp_all
      perp_of_ovee_perp := by
        intro a b c hab h
        by_cases ha : a = P.point <;> by_cases hb : b = P.point <;> simp_all
      perp_ovee_of_ovee_perp := by
        intro a b c hab h
        by_cases ha : a = P.point <;> by_cases hb : b = P.point <;>
          by_cases hc : c = P.point <;> simp_all
      ovee_assoc := by
        intro a b c hab h
        by_cases ha : a = P.point <;> by_cases hb : b = P.point <;>
          by_cases hc : c = P.point <;> simp_all
      zero_perp := fun _ => Or.inl rfl
      zero_ovee := fun _ => ite_eq_left_iff.2 fun h => absurd rfl h }
  { carrier := P.X
    act := ⟨fun r x => if r then x else P.point⟩
    weight := fun x => decide (x ≠ P.point)
    one_smul := fun _ => rfl
    mul_smul := by intro r s x; cases r <;> cases s <;> rfl
    smul_biadditive := by
      refine ⟨fun r => ⟨by cases r <;> rfl, fun {x y} h => ?_⟩, fun x => ⟨rfl, fun {r s} h => ?_⟩⟩
      · cases r
        · exact ⟨Or.inl rfl, ite_eq_left_iff.2 fun h => absurd rfl h⟩
        · exact ⟨h, rfl⟩
      · cases r <;> cases s
        · exact ⟨Or.inl rfl, ite_eq_left_iff.2 fun h => absurd rfl h⟩
        · exact ⟨Or.inl rfl, ite_eq_left_iff.2 fun h => absurd rfl h⟩
        · refine ⟨Or.inr rfl, ?_⟩
          show (if x = P.point then P.point else x) = x
          by_cases hx : x = P.point <;> simp [hx]
        · exact absurd (show true ⊓ true = ⊥ from h) (by decide)
    weight_additive := by
      refine ⟨show decide (P.point ≠ P.point) = ⊥ by simp, fun {x y} h => ?_⟩
      rcases h with rfl | rfl
      · refine ⟨show decide (P.point ≠ P.point) ⊓ decide (y ≠ P.point) = ⊥ by simp, ?_⟩
        show decide (P.point ≠ P.point) ⊔ decide (y ≠ P.point) =
          decide ((if P.point = P.point then y else P.point) ≠ P.point)
        simp
      · refine ⟨show decide (x ≠ P.point) ⊓ decide (P.point ≠ P.point) = ⊥ by simp, ?_⟩
        show decide (x ≠ P.point) ⊔ decide (P.point ≠ P.point) =
          decide ((if x = P.point then P.point else x) ≠ P.point)
        by_cases hx : x = P.point <;> simp [hx]
    weight_smul := by
      intro r x; cases r
      · show decide (P.point ≠ P.point) = false ⊓ decide (x ≠ P.point); simp
      · show decide (x ≠ P.point) = true ⊓ decide (x ≠ P.point); simp
    eq_zero_of_weight := by
      intro x h
      have h' : decide (x ≠ P.point) = false := h
      exact (by simpa using h' : x = P.point)
    perp_of_weight := by
      intro x y h
      have h' : decide (x ≠ P.point) ⊓ decide (y ≠ P.point) = ⊥ := h
      show x = P.point ∨ y = P.point
      by_cases hx : x = P.point
      · exact Or.inl hx
      · right; simpa [hx] using h' }

instance : toPointed.EssSurj where
  mem_essImage P := ⟨ofPointed P, ⟨Pointed.Iso.mk (Equiv.refl _) rfl⟩⟩

/-- **SIG 32** (`ex:weight-module-bool`, main.tex:947, Example), finite case:
weight `{0,1}`-modules are pointed sets: `X ↦ (X, 0)` is an equivalence
`WMod[{0,1}] ≃ pSet` (full, faithful, essentially surjective; the structure
of a weight `{0,1}`-module is determined by its zero, `bool_perp_iff`,
`bool_weight_eq_true_iff`). -/
theorem toPointed_isEquivalence : toPointed.IsEquivalence where

end WMod

end Papers.SIG
