/-
Theses/B/Eff/ExtensiveExamples.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
2143–2187: the point 190IV.3 and its three sub-items — the predicates,
states and scalars of the three *extensive* examples of an effectus,
`SET`, `CRngᵒᵖ` and `bCH`, whose effectus structure is 189aII.3
(`extensive_effectus_set`, `_commRing`, `_compHaus` in `B/Eff/Effectus`).

Design:
* Everything is stated in the **partial** form `Par C` of the total-form
  effectus `C`, because that is where `Pred`, `Stat`, `Scal`,
  `SeparatingPredicates` and `SeparatingStates` are defined (190II).  The
  three `EffectusTotalForm` witnesses and the `HasFiniteCoproducts (Par C)`
  they yield are installed as `local instance`s, so that the statements
  below read as they do in the thesis; `CompHaus` additionally needs the
  universe workaround of `extensive_effectus_compHaus`.
* The common combinatorics is done once, in `ScalarsTwo` and `ParPred`:
  a **two-point presentation** of `⊤ + ⊤` (a colimit cofan `i₁, i₂ : ⊤ ⟶ S`)
  gives `Pred (Par.of X) ≃ (X ⟶ S)` (`parPredEquiv`) with `1`, `0` and
  `(–)^⊥` pinned (`parPredEquiv_truth`, `_zero`, `_orth`), and — as soon as
  `S` has exactly the two points `i₁ ≠ i₂` — the scalars are the
  two-element effect monoid `2` (`par_scalarsAreTwo_of_cofan`).  Each of
  the three categories then only has to supply its own `S`.
* "The scalars are `2`" is `ScalarsAreTwo`, a mutually inverse pair of
  effect-monoid morphisms `Scal C ⇄ Bool`, exactly the shape used by
  `IsRealEffectus` (190II.3) for "the scalars are `[0,1]`".
* ⚠ 190IV.3 is stated **for the three named categories, not in general**:
  as printed ("any extensive category with final object has as scalars the
  two-element effect monoid `2`") it is false.  `Scal (Par C)` is
  `C(⊤, ⊤ + ⊤)`, and for `C = Set × Set` — a product of extensive
  categories is extensive, and `(1,1)` is final — that hom-set is
  `Hom((1,1),(2,2)) = 2 × 2`, which has four elements.  What the argument
  needs beyond extensivity is that the final object is *connected*, and
  that is what each of the three cases below verifies.

Not separately formalized:
* the sibling items 190IV.1 (`OUSᵒᵖ`) and 190IV.2 (`OUGᵒᵖ`) of the same
  point: the two categories themselves are in the tree since 2026-09-03
  (`B/Eff/OrderUnit`, 189aII.1 and 189aII.2), but their predicates, states
  and scalars are not computed there; 190V (`EJAᵒᵖ`) has no category at all;
* the orthosupplement of a `bCH` predicate (`1`, `0` are pinned; 190IV.3(c)
  itself only claims the correspondence with clopens);
* 190III, the point this one hangs off, which is
  `effectus_vn_real_separating` in `B/Eff/VNExamples`.
-/
import Theses.B.Eff.StatesPredicates

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped unitInterval

namespace Theses.B.Eff

universe u v

/-! ## "The scalars are the two-element effect monoid `2`" -/

section ScalarsTwo

variable {D : Type u} [Category.{v} D] [HasFiniteCoproducts D]
  [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D] [EffectusPartialForm D]

/-- **190IV** (eff.tex:2153, Examples): an effectus in partial form **has
the two-element effect monoid `2` as scalars** when `Scal D` and `Bool` are
isomorphic as effect monoids.

As in `IsRealEffectus` (190II.3, the same clause with `[0,1]` in place of
`2`), the isomorphism is rendered as a mutually inverse pair of
effect-monoid morphisms: a bijective morphism of effect algebras need not
have a morphism inverse, since nothing forces it to reflect `⊥`. -/
def ScalarsAreTwo (D : Type u) [Category.{v} D] [HasFiniteCoproducts D]
    [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D] [EffectusPartialForm D] : Prop :=
  ∃ (φ : EffectMonoidHom (Scal D) Bool) (ψ : EffectMonoidHom Bool (Scal D)),
    (∀ k, ψ.toFun (φ.toFun k) = k) ∧ ∀ b, φ.toFun (ψ.toFun b) = b

/-- **190IV** (eff.tex:2153, Examples): an effectus whose only scalars are
`0` and `1`, and in which those two differ, has `2` as its effect monoid of
scalars.

The two morphisms are `k ↦ (k = 1)` and `b ↦ if b then 1 else 0`; the
effect-algebra structure of `2 = Bool` is the Boolean one of 178III.3, so
`0 = ⊥`, `1 = ⊤`, `⋁ = ⊔`, `⊙ = ⊓` and `a ⊥ b` means `a ⊓ b = ⊥`.  That `1`
is not orthogonal to itself on either side is the zero–one axiom together
with `0 ≠ 1`; scalar multiplication is composition, so `0 ⊙ a = 0` and
`a ⊙ 0 = 0` are `FinPAC.comp_zero` and `FinPAC.zero_comp`. -/
theorem scalarsAreTwo_of_forall (hex : ∀ k : Scal D, k = 0 ∨ k = 1)
    (hne : (0 : Scal D) ≠ 1) : ScalarsAreTwo D := by
  classical
  obtain ⟨φf, hφ0, hφ1⟩ : ∃ f : Scal D → Bool, f 0 = false ∧ f 1 = true := by
    refine ⟨fun k => if k = 1 then true else false, ?_, ?_⟩
    · simp [hne]
    · simp
  obtain ⟨ψf, hψ0, hψ1⟩ : ∃ g : Bool → Scal D, g false = 0 ∧ g true = 1 :=
    ⟨fun b => cond b 1 0, rfl, rfl⟩
  have hbne : ¬ ((true : Bool) = 0) := fun hh => Bool.noConfusion hh
  have hbcases : ∀ b : Bool, b = false ∨ b = true := by
    intro b; cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hnp : ¬ Perp (1 : Scal D) (1 : Scal D) := fun hh =>
    hne (EffectAlgebra.eq_zero_of_perp_one hh).symm
  have hnpb : ¬ Perp (true : Bool) (true : Bool) := fun hh =>
    hbne (EffectAlgebra.eq_zero_of_perp_one hh)
  have hzm : ∀ a : Scal D, (0 : Scal D) * a = 0 := fun a =>
    show a ≫ (0 : Scal D) = 0 from FinPAC.comp_zero a
  have hmz : ∀ a : Scal D, a * (0 : Scal D) = 0 := fun a =>
    show (0 : Scal D) ≫ a = 0 from FinPAC.zero_comp a
  have hbzm : ∀ b : Bool, (false : Bool) * b = false := by
    intro b; cases b <;> rfl
  have hbmz : ∀ b : Bool, b * (false : Bool) = false := by
    intro b; cases b <;> rfl
  have hbtt : (true : Bool) * true = true := rfl
  -- orthogonality and partial sums in `Bool`, with `false` in place of `0`
  have hpfl : ∀ x : Bool, Perp (false : Bool) x := fun x => PCM.zero_perp x
  have hpfr : ∀ x : Bool, Perp x (false : Bool) := fun x => PCM.perp_zero x
  have hzol : ∀ x : Bool, ovee (false : Bool) x (hpfl x) = x := fun x =>
    PCM.zero_ovee x
  have hzor : ∀ x : Bool, ovee x (false : Bool) (hpfr x) = x := fun x =>
    PCM.ovee_zero x (hpfr x)
  -- the two morphisms, field by field
  have φperp : ∀ {a b : Scal D}, Perp a b → Perp (φf a) (φf b) := by
    intro a b hab
    rcases hex a with rfl | rfl
    · rw [hφ0]; exact hpfl _
    · rcases hex b with rfl | rfl
      · rw [hφ0]; exact hpfr _
      · exact absurd hab hnp
  have φovee : ∀ {a b : Scal D} (h : Perp a b),
      φf (ovee a b h) = ovee (φf a) (φf b) (φperp h) := by
    intro a b hab
    rcases hex a with rfl | rfl
    · rw [congrArg φf (PCM.zero_ovee (M := Scal D) b)]
      symm
      exact (PCM.ovee_congr hφ0 rfl (φperp hab) (hpfl (φf b))).trans (hzol (φf b))
    · rcases hex b with rfl | rfl
      · rw [congrArg φf (PCM.ovee_zero (1 : Scal D) hab)]
        symm
        exact (PCM.ovee_congr rfl hφ0 (φperp hab) (hpfr (φf 1))).trans
          (hzor (φf 1))
      · exact absurd hab hnp
  have φmul : ∀ a b : Scal D, φf (a * b) = φf a * φf b := by
    intro a b
    rcases hex a with rfl | rfl
    · rw [hzm, hφ0, hbzm]
    · rcases hex b with rfl | rfl
      · rw [hmz, hφ0, hφ1, hbmz]
      · rw [EffectMonoid.one_mul, hφ1, hbtt]
  have ψperp : ∀ {a b : Bool}, Perp a b → Perp (ψf a) (ψf b) := by
    intro a b hab
    rcases hbcases a with rfl | rfl
    · rw [hψ0]; exact PCM.zero_perp _
    · rcases hbcases b with rfl | rfl
      · rw [hψ0]; exact PCM.perp_zero _
      · exact absurd hab hnpb
  have ψovee : ∀ {a b : Bool} (h : Perp a b),
      ψf (ovee a b h) = ovee (ψf a) (ψf b) (ψperp h) := by
    intro a b hab
    rcases hbcases a with rfl | rfl
    · rw [congrArg ψf (hzol b)]
      symm
      exact (PCM.ovee_congr hψ0 rfl (ψperp hab) (PCM.zero_perp (ψf b))).trans
        (PCM.zero_ovee (ψf b))
    · rcases hbcases b with rfl | rfl
      · rw [congrArg ψf (hzor true)]
        symm
        exact (PCM.ovee_congr rfl hψ0 (ψperp hab) (PCM.perp_zero (ψf true))).trans
          (PCM.ovee_zero (ψf true) (PCM.perp_zero (ψf true)))
      · exact absurd hab hnpb
  have ψmul : ∀ a b : Bool, ψf (a * b) = ψf a * ψf b := by
    intro a b
    rcases hbcases a with rfl | rfl
    · rw [hbzm, hψ0, hzm]
    · rcases hbcases b with rfl | rfl
      · rw [hbmz, hψ0, hψ1, hmz]
      · rw [hbtt, hψ1, EffectMonoid.one_mul]
  refine ⟨⟨⟨⟨φf, φperp, φovee⟩, hφ1⟩, φmul⟩, ⟨⟨⟨ψf, ψperp, ψovee⟩, hψ1⟩, ψmul⟩,
    ?_, ?_⟩
  · intro k
    rcases hex k with rfl | rfl
    · show ψf (φf 0) = 0
      rw [hφ0, hψ0]
    · show ψf (φf 1) = 1
      rw [hφ1, hψ1]
  · intro b
    rcases hbcases b with rfl | rfl
    · show φf (ψf false) = false
      rw [hψ0, hφ0]
    · show φf (ψf true) = true
      rw [hψ1, hφ1]

end ScalarsTwo

/-! ## Predicates and scalars from a two-point presentation of `⊤ + ⊤` -/

section ParPred

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasTerminal C]
variable {S : C} {i₁ i₂ : (⊤_ C) ⟶ S}

/-- The comparison isomorphism `⊤ + ⊤ ≅ S` attached to a colimit cofan
`i₁, i₂ : ⊤ ⟶ S`. -/
noncomputable def parGamma (hS : IsColimit (BinaryCofan.mk i₁ i₂)) :
    ((⊤_ C) ⨿ (⊤_ C)) ≅ S :=
  IsColimit.coconePointUniqueUpToIso (coprodIsCoprod (⊤_ C) (⊤_ C)) hS

theorem parGamma_inl (hS : IsColimit (BinaryCofan.mk i₁ i₂)) :
    (coprod.inl : (⊤_ C) ⟶ _) ≫ (parGamma hS).hom = i₁ :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod (⊤_ C) (⊤_ C)) hS
    (Discrete.mk WalkingPair.left)

theorem parGamma_inr (hS : IsColimit (BinaryCofan.mk i₁ i₂)) :
    (coprod.inr : (⊤_ C) ⟶ _) ≫ (parGamma hS).hom = i₂ :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod (⊤_ C) (⊤_ C)) hS
    (Discrete.mk WalkingPair.right)

section ParSwap

variable [EffectusTotalForm C]

/-- The orthosupplement `[κ₂,κ₁]` of `Par C`, transported to `S`. -/
theorem parSwapTop_parGamma (hS : IsColimit (BinaryCofan.mk i₁ i₂)) (sw : S ⟶ S)
    (h₁ : i₁ ≫ sw = i₂) (h₂ : i₂ ≫ sw = i₁) :
    (parSwapTop : (⊤_ C) ⨿ (⊤_ C) ⟶ _) ≫ (parGamma hS).hom
      = (parGamma hS).hom ≫ sw := by
  refine coprod.hom_ext ?_ ?_
  · rw [parSwapTop_eq, ← Category.assoc, coprod.inl_desc, parGamma_inr,
      ← Category.assoc, parGamma_inl, h₁]
  · rw [parSwapTop_eq, ← Category.assoc, coprod.inr_desc, parGamma_inl,
      ← Category.assoc, parGamma_inr, h₂]

end ParSwap

section ParPredEffectus

variable [EffectusTotalForm C] [HasFiniteCoproducts (Par C)]

/-- **190IV.3** (eff.tex:2168, Examples), the shared half: a two-point
presentation `i₁, i₂ : ⊤ ⟶ S` of `⊤ + ⊤` computes the **predicates** of
`Par C`, since `Pred X = (X ⇸ 1)` is `C(X, ⊤ + ⊤)`. -/
noncomputable def parPredEquiv (hS : IsColimit (BinaryCofan.mk i₁ i₂)) (X : C) :
    Pred (Par.of X) ≃ (X ⟶ S) where
  toFun p := pval p ≫ (parGamma hS).hom
  invFun q := show Pred (Par.of X) from
    (q ≫ (parGamma hS).inv : X ⟶ (⊤_ C) ⨿ (⊤_ C))
  left_inv p := by
    refine pval_inj ?_
    show (pval p ≫ (parGamma hS).hom) ≫ (parGamma hS).inv = pval p
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv q := by
    show (q ≫ (parGamma hS).inv) ≫ (parGamma hS).hom = q
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem parPredEquiv_symm_apply (hS : IsColimit (BinaryCofan.mk i₁ i₂)) (X : C)
    (q : X ⟶ S) :
    pval ((parPredEquiv hS X).symm q) = q ≫ (parGamma hS).inv := rfl

/-- Under `parPredEquiv` the truth predicate `1` is the constant `i₁`. -/
theorem parPredEquiv_truth (hS : IsColimit (BinaryCofan.mk i₁ i₂)) (X : C) :
    parPredEquiv hS X (truth (Par.of X)) = terminal.from X ≫ i₁ := by
  show (terminal.from X ≫ coprod.inl) ≫ (parGamma hS).hom = _
  rw [Category.assoc, parGamma_inl]

/-- Under `parPredEquiv` the zero predicate `0` is the constant `i₂`. -/
theorem parPredEquiv_zero (hS : IsColimit (BinaryCofan.mk i₁ i₂)) (X : C) :
    parPredEquiv hS X (0 : Pred (Par.of X)) = terminal.from X ≫ i₂ := by
  have h : pval (0 : Pred (Par.of X)) = terminal.from X ≫ coprod.inr := by
    rw [par_zero_eq' (Par.of X) (Par.of (⊤_ C)), pval_zero]
    rfl
  show pval (0 : Pred (Par.of X)) ≫ (parGamma hS).hom = _
  rw [h, Category.assoc, parGamma_inr]

/-- Under `parPredEquiv` the orthosupplement `p^⊥` is `sw ∘ p`, for the
involution `sw` of `S` swapping the two points. -/
theorem parPredEquiv_orth (hS : IsColimit (BinaryCofan.mk i₁ i₂)) (sw : S ⟶ S)
    (h₁ : i₁ ≫ sw = i₂) (h₂ : i₂ ≫ sw = i₁) (X : C) (p : Pred (Par.of X)) :
    parPredEquiv hS X (orth p) = parPredEquiv hS X p ≫ sw := by
  show pval (parOrth p) ≫ (parGamma hS).hom = (pval p ≫ (parGamma hS).hom) ≫ sw
  rw [pval_parOrth, Category.assoc, parSwapTop_parGamma hS sw h₁ h₂,
    ← Category.assoc]

/-- The scalars of `Par C` are `C(⊤, ⊤ + ⊤)`, with `1 = κ₁`. -/
theorem pval_scal_one :
    pval (1 : Scal (Par C)) = (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C)) := by
  have h : (1 : Scal (Par C)) = 𝟙 (Par.of (⊤_ C)) := truth_effObj_eq_id
  rw [h]
  rfl

/-- The scalars of `Par C` are `C(⊤, ⊤ + ⊤)`, with `0 = κ₂`. -/
theorem pval_scal_zero :
    pval (0 : Scal (Par C)) = (coprod.inr : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C)) := by
  rw [par_zero_eq' (Par.of (⊤_ C)) (Par.of (⊤_ C)), pval_zero, par_terminal_self,
    Category.id_comp]

/-- **190IV.3** (eff.tex:2168, Examples), the shared half: if `⊤ + ⊤` is
presented by a cofan `i₁, i₂ : ⊤ ⟶ S` whose two legs are distinct and are
the **only** maps `⊤ ⟶ S`, then the scalars of `Par C` are the two-element
effect monoid `2`.

(That hypothesis is exactly "the final object is connected"; extensivity
alone does not give it — see the file header.) -/
theorem par_scalarsAreTwo_of_cofan (hS : IsColimit (BinaryCofan.mk i₁ i₂))
    (hne : i₁ ≠ i₂) (hex : ∀ k : (⊤_ C) ⟶ S, k = i₁ ∨ k = i₂) :
    ScalarsAreTwo (Par C) := by
  refine scalarsAreTwo_of_forall ?_ ?_
  · intro k
    rcases hex (pval k ≫ (parGamma hS).hom) with hk | hk
    · right
      refine pval_inj ?_
      rw [pval_scal_one]
      refine (cancel_mono (parGamma hS).hom).mp ?_
      rw [hk, parGamma_inl]
    · left
      refine pval_inj ?_
      rw [pval_scal_zero]
      refine (cancel_mono (parGamma hS).hom).mp ?_
      rw [hk, parGamma_inr]
  · intro hz
    refine hne ?_
    have h1 : (coprod.inl : (⊤_ C) ⟶ (⊤_ C) ⨿ (⊤_ C)) = coprod.inr :=
      ((pval_scal_one (C := C)).symm.trans (congrArg pval hz.symm)).trans
        (pval_scal_zero (C := C))
    calc i₁ = (coprod.inl : (⊤_ C) ⟶ _) ≫ (parGamma hS).hom := (parGamma_inl hS).symm
      _ = (coprod.inr : (⊤_ C) ⟶ _) ≫ (parGamma hS).hom := by rw [h1]
      _ = i₂ := parGamma_inr hS

end ParPredEffectus

end ParPred

/-! ## 190IV.3(a): the effectus `SET` -/

section SetCase

local instance instEffectusTotalFormType : EffectusTotalForm (Type u) :=
  extensive_effectus_set

local instance instHasFiniteCoproductsParType :
    HasFiniteCoproducts (Par (Type u)) := parHasFiniteCoproducts

/-- The final object of `SET` has exactly one element. -/
noncomputable local instance instUniqueTerminalType : Unique (⊤_ (Type u)) :=
  Types.isTerminalEquivUnique _ terminalIsTerminal

/-- The two-element set `1 + 1` of `SET`, concretely. -/
private abbrev setTwo : Type u := (⊤_ (Type u)) ⊕ (⊤_ (Type u))

private abbrev setI₁ : (⊤_ (Type u)) ⟶ setTwo.{u} :=
  ↾(Sum.inl : (⊤_ (Type u)) → setTwo.{u})

private abbrev setI₂ : (⊤_ (Type u)) ⟶ setTwo.{u} :=
  ↾(Sum.inr : (⊤_ (Type u)) → setTwo.{u})

private abbrev setSwap : setTwo.{u} ⟶ setTwo.{u} :=
  ↾(Sum.swap : setTwo.{u} → setTwo.{u})

private abbrev setElim {X : Type u} (q : X ⟶ setTwo.{u}) :
    (X ⊕ (⊤_ (Type u))) ⟶ setTwo.{u} :=
  ↾(Sum.elim (fun x => q x) (fun t => Sum.inr t))

/-- `⊤ + ⊤` in `SET` is the two-element set `1 ⊕ 1`. -/
private noncomputable def set_top_cofan :
    IsColimit (BinaryCofan.mk setI₁.{u} setI₂.{u}) :=
  Types.binaryCoproductColimit _ _

private theorem set_inl_ne_inr : setI₁.{u} ≠ setI₂.{u} := by
  intro h
  have h2 : (Sum.inl (default : ⊤_ (Type u)) : setTwo.{u})
      = Sum.inr (default : ⊤_ (Type u)) :=
    congrArg (fun f : (⊤_ (Type u)) ⟶ setTwo.{u} => f (default : ⊤_ (Type u))) h
  simp at h2

private theorem set_top_hom_cases (k : (⊤_ (Type u)) ⟶ setTwo.{u}) :
    k = setI₁.{u} ∨ k = setI₂.{u} := by
  rcases hk : k (default : ⊤_ (Type u)) with a | a
  · left
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    have hx : x = (default : ⊤_ (Type u)) := Subsingleton.elim _ _
    subst hx
    rw [hk]
    exact congrArg Sum.inl (Subsingleton.elim a (default : ⊤_ (Type u)))
  · right
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    have hx : x = (default : ⊤_ (Type u)) := Subsingleton.elim _ _
    subst hx
    rw [hk]
    exact congrArg Sum.inr (Subsingleton.elim a (default : ⊤_ (Type u)))

/-- **190IV.3** (eff.tex:2168, Examples) for `SET`: the scalars of `SET` are
the two-element effect monoid `2`.  (`Scal = Set(1, 1 + 1)`, and `1 + 1` has
exactly the two points `κ₁ ≠ κ₂`.) -/
theorem set_scalars_two : ScalarsAreTwo (Par (Type u)) :=
  par_scalarsAreTwo_of_cofan set_top_cofan set_inl_ne_inr set_top_hom_cases

/-- The two-element set is `Bool`. -/
private noncomputable def setTwoEquivBool : setTwo.{u} ≃ Bool where
  toFun := Sum.isLeft
  invFun b := cond b (Sum.inl default) (Sum.inr default)
  left_inv s := by
    cases s with
    | inl a => exact congrArg Sum.inl (Subsingleton.elim _ _)
    | inr a => exact congrArg Sum.inr (Subsingleton.elim _ _)
  right_inv b := by cases b <;> rfl

/-- Maps `X ⟶ 1 + 1` are the subsets of `X`. -/
private noncomputable def setSumEquiv (X : Type u) :
    (X ⟶ setTwo.{u}) ≃ Set X :=
  TypeCat.homEquiv.trans (Equiv.arrowCongr (Equiv.refl X)
    (setTwoEquivBool.{u}.trans Equiv.propEquivBool.symm))

/-- **190IV.3(a)** (eff.tex:2173, Examples), first half: in `SET` **the
predicates on a set `X` correspond to the subsets `U ⊆ X`**.

The correspondence is pinned by the three lemmas below: `1` is `X` itself,
`0` is `∅`, and `p^⊥` is the complement. -/
noncomputable def set_pred_subset (X : Type u) : Pred (Par.of X) ≃ Set X :=
  (parPredEquiv set_top_cofan.{u} X).trans (setSumEquiv X)

private theorem set_pred_subset_apply (X : Type u) (p : Pred (Par.of X))
    (x : X) :
    x ∈ set_pred_subset X p ↔ ((parPredEquiv set_top_cofan.{u} X p) x).isLeft = true :=
  Iff.rfl

/-- **190IV.3(a)**: the truth predicate is the whole set. -/
theorem set_pred_subset_truth (X : Type u) :
    set_pred_subset X (truth (Par.of X)) = Set.univ := by
  ext x
  rw [set_pred_subset_apply, parPredEquiv_truth]
  exact ⟨fun _ => trivial, fun _ => rfl⟩

/-- **190IV.3(a)**: the zero predicate is the empty set. -/
theorem set_pred_subset_zero (X : Type u) :
    set_pred_subset X (0 : Pred (Par.of X)) = (∅ : Set X) := by
  ext x
  rw [set_pred_subset_apply, parPredEquiv_zero]
  exact ⟨fun hh => Bool.noConfusion hh, fun hh => False.elim hh⟩

/-- **190IV.3(a)**: the orthosupplement is the complement. -/
theorem set_pred_subset_orth (X : Type u) (p : Pred (Par.of X)) :
    set_pred_subset X (orth p) = (set_pred_subset X p)ᶜ := by
  ext x
  show ((parPredEquiv set_top_cofan.{u} X (orth p)) x).isLeft = true
      ↔ ¬ (((parPredEquiv set_top_cofan.{u} X p) x).isLeft = true)
  rw [parPredEquiv_orth set_top_cofan.{u} setSwap.{u} rfl rfl X p]
  show (setSwap.{u} ((parPredEquiv set_top_cofan.{u} X p) x)).isLeft = true
      ↔ ¬ (((parPredEquiv set_top_cofan.{u} X p) x).isLeft = true)
  rcases hv : (parPredEquiv set_top_cofan.{u} X p) x with a | a
  · exact ⟨fun hh => Bool.noConfusion hh, fun hh => absurd rfl hh⟩
  · exact ⟨fun _ hh => Bool.noConfusion hh, fun _ => rfl⟩

/-- **190IV.3(a)** (eff.tex:2175, Examples), second half: in `SET` **the
states of `X` correspond to the elements `x ∈ X`**.  (`parStatEquiv` makes a
state a point `1 ⟶ X`, and a point of `SET` is an element.) -/
noncomputable def set_stat_elem (X : Type u) : Stat (Par.of X) ≃ X :=
  (parStatEquiv X).trans
    (TypeCat.homEquiv.trans
      { toFun := fun g => g default
        invFun := fun x => fun _ => x
        left_inv := fun g => funext fun _ => congrArg g (Subsingleton.elim _ _)
        right_inv := fun _ => rfl })

/-- **190IV.3(a)** (eff.tex:2173, Examples): `SET` has **separating
predicates**.

Every subset of `X` is a predicate, so the maps `[p, κ₂] : X + 1 ⟶ 1 + 1`
separate the points of `X + 1`: two distinct points of `X` are separated by
a singleton, and a point of `X` from `κ₂` by the truth predicate. -/
theorem set_separating_predicates : SeparatingPredicates (Par (Type u)) := by
  classical
  intro Y X f g h
  refine pval_inj ?_
  have key : ∀ q : X.base ⟶ setTwo.{u},
      coprod.desc (q ≫ (parGamma set_top_cofan.{u}).inv)
          (coprod.inr : (⊤_ (Type u)) ⟶ (⊤_ (Type u)) ⨿ (⊤_ (Type u)))
          ≫ (parGamma set_top_cofan.{u}).hom
        = (Types.binaryCoproductIso X.base (⊤_ (Type u))).hom ≫ setElim q := by
    intro q
    refine coprod.hom_ext ?_ ?_
    · simp only [← Category.assoc, coprod.inl_desc,
        Types.binaryCoproductIso_inl_comp_hom]
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl
    · simp only [← Category.assoc, coprod.inr_desc,
        Types.binaryCoproductIso_inr_comp_hom]
      rw [parGamma_inr]
      rfl
  have hpt : ∀ (q : X.base ⟶ setTwo.{u}) (y : Y.base),
      setElim q ((Types.binaryCoproductIso X.base (⊤_ (Type u))).hom (pval f y))
        = setElim q
            ((Types.binaryCoproductIso X.base (⊤_ (Type u))).hom (pval g y)) := by
    intro q y
    have hq : pval f ≫ coprod.desc (q ≫ (parGamma set_top_cofan.{u}).inv)
          (coprod.inr : (⊤_ (Type u)) ⟶ (⊤_ (Type u)) ⨿ (⊤_ (Type u)))
        = pval g ≫ coprod.desc (q ≫ (parGamma set_top_cofan.{u}).inv)
          (coprod.inr : (⊤_ (Type u)) ⟶ (⊤_ (Type u)) ⨿ (⊤_ (Type u))) :=
      congrArg pval (h ((parPredEquiv set_top_cofan.{u} X.base).symm q))
    have h2 := congrArg (fun m => m ≫ (parGamma set_top_cofan.{u}).hom) hq
    simp only [Category.assoc, key q] at h2
    exact congrArg (fun m => m y) h2
  refine (cancel_mono (Types.binaryCoproductIso X.base (⊤_ (Type u))).hom).mp ?_
  refine ConcreteCategory.hom_ext _ _ (fun y => ?_)
  show (Types.binaryCoproductIso X.base (⊤_ (Type u))).hom (pval f y)
      = (Types.binaryCoproductIso X.base (⊤_ (Type u))).hom (pval g y)
  obtain ⟨A, hA⟩ :
      ∃ A, (Types.binaryCoproductIso X.base (⊤_ (Type u))).hom (pval f y) = A :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ :
      ∃ B, (Types.binaryCoproductIso X.base (⊤_ (Type u))).hom (pval g y) = B :=
    ⟨_, rfl⟩
  have hpt' : ∀ q : X.base ⟶ setTwo.{u}, setElim q A = setElim q B := by
    intro q
    rw [← hA, ← hB]
    exact hpt q y
  rw [hA, hB]
  clear hA hB
  cases A with
  | inl a =>
      cases B with
      | inl b =>
          by_cases hab : a = b
          · rw [hab]
          · exfalso
            have hh : (if a = a then (Sum.inl default : setTwo.{u})
                  else Sum.inr default)
                = (if b = a then (Sum.inl default : setTwo.{u})
                  else Sum.inr default) :=
              hpt' (↾(fun x => if x = a then (Sum.inl default : setTwo.{u})
                else Sum.inr default))
            simp [Ne.symm hab] at hh
      | inr b =>
          exfalso
          have hh : (Sum.inl (default : ⊤_ (Type u)) : setTwo.{u}) = Sum.inr b :=
            hpt' (↾(fun _ => (Sum.inl default : setTwo.{u})))
          simp at hh
  | inr a =>
      cases B with
      | inl b =>
          exfalso
          have hh : (Sum.inr a : setTwo.{u}) = Sum.inl (default : ⊤_ (Type u)) :=
            hpt' (↾(fun _ => (Sum.inl default : setTwo.{u})))
          simp at hh
      | inr b =>
          rw [Subsingleton.elim a b]

/-- **190IV.3(a)** (eff.tex:2175, Examples): `SET` has **separating
states**.  The states of `X` are its elements, and elements are jointly epic
in `SET`. -/
theorem set_separating_states : SeparatingStates (Par (Type u)) := by
  intro X Y f g h
  refine pval_inj ?_
  refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
  have hst : IsTotal (Par.hat (↾(fun _ => x) : (⊤_ (Type u)) ⟶ X.base) :
      Par.of (⊤_ (Type u)) ⟶ Par.of X.base) :=
    (par_isTotal_iff_hat _).mpr ⟨_, rfl⟩
  have h2 := h ⟨Par.hat (↾(fun _ => x) : (⊤_ (Type u)) ⟶ X.base), hst⟩
  have h3 : (↾(fun _ => x) : (⊤_ (Type u)) ⟶ X.base) ≫ pval f
      = (↾(fun _ => x) : (⊤_ (Type u)) ⟶ X.base) ≫ pval g := by
    rw [← par_hat_comp, ← par_hat_comp]
    exact congrArg pval h2
  exact congrArg (fun m => m (default : ⊤_ (Type u))) h3

end SetCase

/-! ## 190IV.3(b): the effectus `CRngᵒᵖ` -/

section CommRingCase

local instance instEffectusTotalFormCommRing :
    EffectusTotalForm CommRingCat.{u}ᵒᵖ := extensive_effectus_commRing

local instance instHasFiniteCoproductsParCommRing :
    HasFiniteCoproducts (Par CommRingCat.{u}ᵒᵖ) := parHasFiniteCoproducts

/-- The initial commutative ring: the unop of the final object of `CRngᵒᵖ`. -/
private noncomputable abbrev crngI : CommRingCat.{u} := (⊤_ CommRingCat.{u}ᵒᵖ).unop

/-- The unique ring map out of the initial commutative ring. -/
private noncomputable def crngIto (R : CommRingCat.{u}) : crngI.{u} ⟶ R :=
  (terminal.from (op R)).unop

private theorem crngI_hom_unique {R : CommRingCat.{u}} (f g : crngI.{u} ⟶ R) :
    f = g :=
  Quiver.Hom.op_inj (terminalIsTerminal.hom_ext (C := CommRingCat.{u}ᵒᵖ) f.op g.op)

private noncomputable def crngIsInitial : IsInitial crngI.{u} :=
  IsInitial.ofUniqueHom crngIto (fun R f => crngI_hom_unique f (crngIto R))

/-- The initial commutative ring is `ℤ`. -/
private noncomputable def crngIsoZ : crngI.{u} ≅ CommRingCat.of (ULift.{u} ℤ) :=
  crngIsInitial.uniqueUpToIso CommRingCat.isInitial

private theorem crngIsoZ_back (x : crngI.{u}) :
    crngIsoZ.{u}.inv.hom (crngIsoZ.{u}.hom.hom x) = x :=
  congrArg (fun m : crngI.{u} ⟶ crngI.{u} => m.hom x) crngIsoZ.{u}.hom_inv_id

private theorem crngI_one_ne_zero : (1 : crngI.{u}) ≠ 0 := by
  intro h
  have h2 : (1 : ULift.{u} ℤ) = 0 := by
    rw [← map_one crngIsoZ.{u}.hom.hom, h, map_zero]
  exact one_ne_zero (congrArg ULift.down h2)

private theorem crngI_idem (e : crngI.{u}) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have hφ : IsIdempotentElem (crngIsoZ.{u}.hom.hom e) := by
    show crngIsoZ.{u}.hom.hom e * crngIsoZ.{u}.hom.hom e = crngIsoZ.{u}.hom.hom e
    rw [← map_mul, he]
  have hd : IsIdempotentElem (crngIsoZ.{u}.hom.hom e).down := congrArg ULift.down hφ
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hd with h | h
  · left
    have h0 : crngIsoZ.{u}.hom.hom e = 0 := ULift.down_injective h
    rw [← crngIsoZ_back e, h0, map_zero]
  · right
    have h1 : crngIsoZ.{u}.hom.hom e = 1 := ULift.down_injective h
    rw [← crngIsoZ_back e, h1, map_one]

/-- The ring `ℤ × ℤ`, whose opposite presents `⊤ + ⊤` in `CRngᵒᵖ`. -/
private noncomputable abbrev crngII : CommRingCat.{u} :=
  CommRingCat.of (crngI.{u} × crngI.{u})

private noncomputable abbrev crngJ₁ :
    (⊤_ CommRingCat.{u}ᵒᵖ) ⟶ op crngII.{u} :=
  (CommRingCat.ofHom (RingHom.fst crngI.{u} crngI.{u})).op

private noncomputable abbrev crngJ₂ :
    (⊤_ CommRingCat.{u}ᵒᵖ) ⟶ op crngII.{u} :=
  (CommRingCat.ofHom (RingHom.snd crngI.{u} crngI.{u})).op

/-- `⊤ + ⊤` in `CRngᵒᵖ` is the product ring `ℤ × ℤ`. -/
private noncomputable def crngCofan :
    IsColimit (BinaryCofan.mk crngJ₁.{u} crngJ₂.{u}) :=
  BinaryCofan.IsColimit.mk _
    (fun {_} u v => (CommRingCat.ofHom (RingHom.prod u.unop.hom v.unop.hom)).op)
    (fun {_} _ _ => by apply Quiver.Hom.unop_inj; ext _; rfl)
    (fun {_} _ _ => by apply Quiver.Hom.unop_inj; ext _; rfl)
    (fun {W} _ _ m h₁ h₂ => by
      obtain ⟨m', rfl⟩ : ∃ m' : op crngII.{u} ⟶ W, m' = m := ⟨m, rfl⟩
      apply Quiver.Hom.unop_inj
      ext x
      · exact congrArg (fun k : (⊤_ CommRingCat.{u}ᵒᵖ) ⟶ W => k.unop x) h₁
      · exact congrArg (fun k : (⊤_ CommRingCat.{u}ᵒᵖ) ⟶ W => k.unop x) h₂)

/-- The unique map `ℤ ⟶ ℤ × ℤ` is the diagonal. -/
private theorem crngIto_prod_apply (a : crngI.{u}) :
    (crngIto crngII.{u}).hom a = (a, a) := by
  have h₁ : CommRingCat.ofHom
      ((RingHom.fst crngI.{u} crngI.{u}).comp (crngIto crngII.{u}).hom)
      = CommRingCat.ofHom (RingHom.id crngI.{u}) := crngI_hom_unique _ _
  have h₂ : CommRingCat.ofHom
      ((RingHom.snd crngI.{u} crngI.{u}).comp (crngIto crngII.{u}).hom)
      = CommRingCat.ofHom (RingHom.id crngI.{u}) := crngI_hom_unique _ _
  refine Prod.ext ?_ ?_
  · exact congrArg (fun m : crngI.{u} ⟶ crngI.{u} => m.hom a) h₁
  · exact congrArg (fun m : crngI.{u} ⟶ crngI.{u} => m.hom a) h₂

/-- The ring map `ℤ × ℤ ⟶ R` attached to an idempotent `e` of `R`:
`(a, b) ↦ κ(a)·e + κ(b)·(1-e)`. -/
private noncomputable def crngHomOfIdem (R : CommRingCat.{u}) (e : R)
    (he : IsIdempotentElem e) : crngII.{u} ⟶ R :=
  CommRingCat.ofHom
    { toFun := fun p => (crngIto R).hom p.1 * e + (crngIto R).hom p.2 * (1 - e)
      map_zero' := by
        show (crngIto R).hom 0 * e + (crngIto R).hom 0 * (1 - e) = 0
        rw [map_zero, zero_mul, zero_mul, add_zero]
      map_one' := by
        show (crngIto R).hom 1 * e + (crngIto R).hom 1 * (1 - e) = 1
        rw [map_one, one_mul, one_mul]
        abel
      map_add' := by
        rintro ⟨a, b⟩ ⟨a', b'⟩
        show (crngIto R).hom (a + a') * e + (crngIto R).hom (b + b') * (1 - e)
            = ((crngIto R).hom a * e + (crngIto R).hom b * (1 - e))
              + ((crngIto R).hom a' * e + (crngIto R).hom b' * (1 - e))
        rw [map_add, map_add, add_mul, add_mul]
        abel
      map_mul' := by
        have hee : e * e = e := he
        have hef : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
        have hff : (1 - e) * (1 - e) = 1 - e := by
          rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
        have key : ∀ x y z w : R,
            (x * e + y * (1 - e)) * (z * e + w * (1 - e))
              = x * z * e + y * w * (1 - e) := by
          intro x y z w
          linear_combination (x * z) * hee + (x * w + y * z) * hef + (y * w) * hff
        rintro ⟨a, b⟩ ⟨a', b'⟩
        show (crngIto R).hom (a * a') * e + (crngIto R).hom (b * b') * (1 - e)
            = ((crngIto R).hom a * e + (crngIto R).hom b * (1 - e))
              * ((crngIto R).hom a' * e + (crngIto R).hom b' * (1 - e))
        rw [key, map_mul, map_mul] }

/-- **190IV.3(b)** (eff.tex:2177, Examples), the correspondence itself: ring
maps `ℤ × ℤ ⟶ R` are the **idempotents** of `R`, by `φ ↦ φ(1,0)`. -/
private noncomputable def crngHomIdemEquiv (R : CommRingCat.{u}) :
    (crngII.{u} ⟶ R) ≃ {e : R // IsIdempotentElem e} where
  toFun φ := ⟨φ.hom ((1 : crngI.{u}), (0 : crngI.{u})), by
    have hsq : ((1 : crngI.{u}), (0 : crngI.{u})) * (1, 0) = (1, 0) := by
      refine Prod.ext ?_ ?_ <;> simp
    show φ.hom (1, 0) * φ.hom (1, 0) = φ.hom (1, 0)
    rw [← map_mul, hsq]⟩
  invFun e := crngHomOfIdem R e.1 e.2
  left_inv φ := by
    have hfac : ∀ a : crngI.{u}, (crngIto R).hom a = φ.hom (a, a) := by
      intro a
      have h := crngI_hom_unique (crngIto crngII.{u} ≫ φ) (crngIto R)
      have h2 := congrArg (fun m : crngI.{u} ⟶ R => m.hom a) h
      rw [← h2]
      show φ.hom ((crngIto crngII.{u}).hom a) = _
      rw [crngIto_prod_apply]
    apply CommRingCat.hom_ext
    ext p
    obtain ⟨a, b⟩ := p
    show (crngIto R).hom a * φ.hom (1, 0)
        + (crngIto R).hom b * (1 - φ.hom (1, 0)) = φ.hom (a, b)
    have e1 : (crngIto R).hom a * φ.hom (1, 0) = φ.hom (a, 0) := by
      rw [hfac a, ← map_mul]
      congr 1
      refine Prod.ext ?_ ?_ <;> simp
    have hsum : φ.hom (1, 0) + φ.hom (0, 1) = 1 := by
      rw [← map_add,
        show ((1 : crngI.{u}), (0 : crngI.{u})) + (0, 1)
            = (1 : crngI.{u} × crngI.{u}) from Prod.ext (by simp) (by simp)]
      exact map_one _
    have e2 : (1 : R) - φ.hom (1, 0) = φ.hom (0, 1) := by
      rw [← hsum]; abel
    have e3 : (crngIto R).hom b * φ.hom (0, 1) = φ.hom (0, b) := by
      rw [hfac b, ← map_mul]
      congr 1
      refine Prod.ext ?_ ?_ <;> simp
    rw [e1, e2, e3, ← map_add]
    congr 1
    refine Prod.ext ?_ ?_ <;> simp
  right_inv e := by
    apply Subtype.ext
    show (crngIto R).hom 1 * e.1 + (crngIto R).hom 0 * (1 - e.1) = e.1
    rw [map_one, map_zero, one_mul, zero_mul, add_zero]

private theorem crngHomIdem_compl {R : CommRingCat.{u}} (ψ : crngII.{u} ⟶ R) :
    ψ.hom ((0 : crngI.{u}), (1 : crngI.{u}))
      = 1 - ψ.hom ((1 : crngI.{u}), (0 : crngI.{u})) := by
  have hsum : ψ.hom ((1 : crngI.{u}), (0 : crngI.{u})) + ψ.hom (0, 1) = 1 := by
    rw [← map_add,
      show ((1 : crngI.{u}), (0 : crngI.{u})) + (0, 1)
          = (1 : crngI.{u} × crngI.{u}) from Prod.ext (by simp) (by simp)]
    exact map_one _
  rw [← hsum]; abel

private theorem crng_j_ne : crngJ₁.{u} ≠ crngJ₂.{u} := by
  intro h
  have h1 : CommRingCat.ofHom (RingHom.fst crngI.{u} crngI.{u})
      = CommRingCat.ofHom (RingHom.snd crngI.{u} crngI.{u}) :=
    congrArg Quiver.Hom.unop h
  exact crngI_one_ne_zero.{u}
    (congrArg (fun m : crngII.{u} ⟶ crngI.{u} =>
      m.hom ((1 : crngI.{u}), (0 : crngI.{u}))) h1)

private theorem crng_top_hom_cases (k : (⊤_ CommRingCat.{u}ᵒᵖ) ⟶ op crngII.{u}) :
    k = crngJ₁.{u} ∨ k = crngJ₂.{u} := by
  rcases crngI_idem _ ((crngHomIdemEquiv crngI.{u} k.unop).2) with h | h
  · right
    refine Quiver.Hom.unop_inj
      ((crngHomIdemEquiv crngI.{u}).injective (Subtype.ext ?_))
    rw [h]
    rfl
  · left
    refine Quiver.Hom.unop_inj
      ((crngHomIdemEquiv crngI.{u}).injective (Subtype.ext ?_))
    rw [h]
    rfl

/-- **190IV.3** (eff.tex:2168, Examples) for `CRngᵒᵖ`: the scalars of
`CRngᵒᵖ` are the two-element effect monoid `2`.  (`Scal` is the set of ring
maps `ℤ × ℤ → ℤ`, i.e. the idempotents of `ℤ`, i.e. `{0, 1}`.) -/
theorem crng_scalars_two : ScalarsAreTwo (Par CommRingCat.{u}ᵒᵖ) :=
  par_scalarsAreTwo_of_cofan crngCofan crng_j_ne crng_top_hom_cases

/-- Passing to the opposite category. -/
private noncomputable def crngOpEquiv (R : CommRingCat.{u}) :
    ((op R : CommRingCat.{u}ᵒᵖ) ⟶ op crngII.{u}) ≃ (crngII.{u} ⟶ R) where
  toFun f := f.unop
  invFun g := g.op
  left_inv _ := rfl
  right_inv _ := rfl

/-- **190IV.3(b)** (eff.tex:2177, Examples), first half: in `CRngᵒᵖ` **the
predicates on `R` correspond to the idempotents of `R`**.

The correspondence is pinned by the three lemmas below: `1` is the
idempotent `1`, `0` is `0`, and `p^⊥` is `1 - p`. -/
noncomputable def crng_pred_idem (R : CommRingCat.{u}) :
    Pred (Par.of (op R)) ≃ {e : R // IsIdempotentElem e} :=
  ((parPredEquiv crngCofan.{u} (op R)).trans (crngOpEquiv R)).trans
    (crngHomIdemEquiv R)

private theorem crng_pred_idem_val (R : CommRingCat.{u})
    (p : Pred (Par.of (op R))) :
    ((crng_pred_idem R p).1 : R)
      = (parPredEquiv crngCofan.{u} (op R) p).unop.hom
          ((1 : crngI.{u}), (0 : crngI.{u})) := rfl

/-- **190IV.3(b)**: the truth predicate is the idempotent `1`. -/
theorem crng_pred_idem_truth (R : CommRingCat.{u}) :
    ((crng_pred_idem R (truth (Par.of (op R)))).1 : R) = 1 := by
  rw [crng_pred_idem_val, parPredEquiv_truth]
  show (crngIto R).hom ((RingHom.fst crngI.{u} crngI.{u}) (1, 0)) = 1
  exact map_one _

/-- **190IV.3(b)**: the zero predicate is the idempotent `0`. -/
theorem crng_pred_idem_zero (R : CommRingCat.{u}) :
    ((crng_pred_idem R (0 : Pred (Par.of (op R)))).1 : R) = 0 := by
  rw [crng_pred_idem_val, parPredEquiv_zero]
  show (crngIto R).hom ((RingHom.snd crngI.{u} crngI.{u}) (1, 0)) = 0
  exact map_zero _

/-- The swap of `ℤ × ℤ`, i.e. the orthosupplement of `Par (CRngᵒᵖ)`. -/
private noncomputable abbrev crngSwap : (op crngII.{u}) ⟶ op crngII.{u} :=
  (CommRingCat.ofHom (RingHom.prod (RingHom.snd crngI.{u} crngI.{u})
    (RingHom.fst crngI.{u} crngI.{u}))).op

/-- **190IV.3(b)**: the orthosupplement is `1 - p`. -/
theorem crng_pred_idem_orth (R : CommRingCat.{u}) (p : Pred (Par.of (op R))) :
    ((crng_pred_idem R (orth p)).1 : R) = 1 - ((crng_pred_idem R p).1 : R) := by
  rw [crng_pred_idem_val, crng_pred_idem_val,
    parPredEquiv_orth crngCofan.{u} crngSwap.{u} rfl rfl (op R) p,
    ← crngHomIdem_compl (parPredEquiv crngCofan.{u} (op R) p).unop]
  rfl

/-- **190IV.3(b)** (eff.tex:2179, Examples), second half: in `CRngᵒᵖ` **the
states of `R` correspond to the unit-preserving homomorphisms `R → ℤ`**.
(`parStatEquiv` makes a state a point `⊤ ⟶ Rᵒᵖ` of `CRngᵒᵖ`, i.e. a ring map
`R → ℤ`, since `ℤ` is the initial commutative ring.) -/
noncomputable def crng_stat_hom (R : CommRingCat.{u}) :
    Stat (Par.of (op R)) ≃ (R →+* ULift.{u} ℤ) :=
  (parStatEquiv (op R)).trans
    { toFun := fun f => (f.unop ≫ crngIsoZ.{u}.hom).hom
      invFun := fun g => (CommRingCat.ofHom g ≫ crngIsoZ.{u}.inv).op
      left_inv := fun f => by
        refine Quiver.Hom.unop_inj ?_
        show CommRingCat.ofHom (f.unop ≫ crngIsoZ.{u}.hom).hom
            ≫ crngIsoZ.{u}.inv = f.unop
        rw [CommRingCat.ofHom_hom, Category.assoc, crngIsoZ.{u}.hom_inv_id,
          Category.comp_id]
      right_inv := fun g => by
        show ((CommRingCat.ofHom g ≫ crngIsoZ.{u}.inv) ≫ crngIsoZ.{u}.hom).hom = g
        rw [Category.assoc, crngIsoZ.{u}.inv_hom_id, Category.comp_id,
          CommRingCat.hom_ofHom] }

/-! ### 190IV.3(b): neither predicates nor states separate -/

/-- `ℤ[X]`, as an object of `CRng`. -/
private noncomputable abbrev crngPoly : CommRingCat.{u} :=
  CommRingCat.of (ULift.{u} (Polynomial ℤ))

/-- The endomorphism `X ↦ 0` of `ℤ[X]`. -/
private noncomputable def crngEv0 : crngPoly.{u} ⟶ crngPoly.{u} :=
  CommRingCat.ofHom (RingHom.ulift.{u, u}
    ((Polynomial.C (R := ℤ)).comp (Polynomial.evalRingHom (0 : ℤ))))

private theorem crngEv0_ne_id : crngEv0.{u} ≠ 𝟙 crngPoly.{u} := by
  intro h
  have h1 := congrArg
    (fun m : crngPoly.{u} ⟶ crngPoly.{u} => (m.hom (ULift.up Polynomial.X)).down) h
  simp only [crngEv0, CommRingCat.hom_ofHom, RingHom.down_ulift_apply,
    CommRingCat.hom_id, RingHom.id_apply] at h1
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_evalRingHom,
    Polynomial.eval_X, map_zero] at h1
  exact Polynomial.X_ne_zero h1.symm

/-- Every ring map `ℤ × ℤ ⟶ ℤ[X]` is fixed by `X ↦ 0`: its idempotent is `0`
or `1` (`ℤ[X]` is a domain), and both are fixed. -/
private theorem crng_ev0_fixes (ψ : crngII.{u} ⟶ crngPoly.{u}) :
    ψ ≫ crngEv0.{u} = ψ := by
  refine (crngHomIdemEquiv crngPoly.{u}).injective (Subtype.ext ?_)
  show crngEv0.{u}.hom (ψ.hom ((1 : crngI.{u}), (0 : crngI.{u})))
      = ψ.hom ((1 : crngI.{u}), (0 : crngI.{u}))
  have he : IsIdempotentElem (ψ.hom ((1 : crngI.{u}), (0 : crngI.{u}))) :=
    (crngHomIdemEquiv crngPoly.{u} ψ).2
  have hedown : IsIdempotentElem
      (ψ.hom ((1 : crngI.{u}), (0 : crngI.{u}))).down := congrArg ULift.down he
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hedown with h | h
  · have h0 : ψ.hom ((1 : crngI.{u}), (0 : crngI.{u})) = 0 := ULift.down_injective h
    rw [h0, map_zero]
  · have h1 : ψ.hom ((1 : crngI.{u}), (0 : crngI.{u})) = 1 := ULift.down_injective h
    rw [h1, map_one]

/-- **190IV.3(b)** (eff.tex:2177, Examples): `CRngᵒᵖ` does **not** have
separating predicates.  On `ℤ[X]` there are only the two predicates `0` and
`1` — the idempotents of a domain — and both are fixed by the two distinct
endomorphisms `id` and `X ↦ 0`. -/
theorem crng_no_separating_predicates :
    ¬ SeparatingPredicates (Par CommRingCat.{u}ᵒᵖ) := by
  intro hsep
  refine crngEv0_ne_id.{u} ?_
  refine Quiver.Hom.op_inj ?_
  refine par_hat_inj (Y := op crngPoly.{u}) ?_
  refine hsep (Par.hat crngEv0.{u}.op) (Par.hat (𝟙 (op crngPoly.{u}))) ?_
  intro p
  refine pval_inj ?_
  rw [par_hat_comp, par_hat_comp, Category.id_comp]
  refine (cancel_mono (parGamma crngCofan.{u}).hom).mp ?_
  rw [Category.assoc]
  show crngEv0.{u}.op ≫ (parPredEquiv crngCofan.{u} (op crngPoly.{u}) p)
      = parPredEquiv crngCofan.{u} (op crngPoly.{u}) p
  refine Quiver.Hom.unop_inj ?_
  exact crng_ev0_fixes _

/-- `ℤ₂`, as an object of `CRng`. -/
private noncomputable abbrev crngZmodTwo : CommRingCat.{u} :=
  CommRingCat.of (ULift.{u} (ZMod 2))

private theorem crng_stat_empty :
    IsEmpty (Stat (Par.of (op crngZmodTwo.{u}))) := by
  have hE : IsEmpty (crngZmodTwo.{u} →+* ULift.{u} ℤ) := by
    refine ⟨fun g => ?_⟩
    exact (exc_rng_eff_no_hom).elim
      ((((ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)).toRingHom.comp g).comp
        ((ULift.ringEquiv : ULift.{u} (ZMod 2) ≃+* ZMod 2)).symm.toRingHom)
  exact Function.isEmpty (crng_stat_hom crngZmodTwo.{u})

/-- **190IV.3(b)** (eff.tex:2179, Examples): `CRngᵒᵖ` does **not** have
separating states.  `ℤ₂` has no states at all — there is no unit-preserving
ring homomorphism `ℤ₂ → ℤ` — while `1 ≠ 0` as predicates on it. -/
theorem crng_no_separating_states :
    ¬ SeparatingStates (Par CommRingCat.{u}ᵒᵖ) := by
  intro hsep
  have hemp := crng_stat_empty.{u}
  have h : truth (Par.of (op crngZmodTwo.{u}))
      = (0 : Pred (Par.of (op crngZmodTwo.{u}))) :=
    hsep (truth (Par.of (op crngZmodTwo.{u}))) 0 (fun ω => isEmptyElim ω)
  have h1 := congrArg (fun q => ((crng_pred_idem crngZmodTwo.{u} q).1 :
    crngZmodTwo.{u})) h
  rw [crng_pred_idem_truth, crng_pred_idem_zero] at h1
  exact absurd (congrArg ULift.down h1) (by decide)

end CommRingCase

/-! ## 190IV.3(c): the effectus `CH` -/

section CompHausCase

open TopologicalSpace

/-- The `letI` of `extensive_effectus_compHaus`: instance synthesis for
`HasFiniteCoproducts CompHaus.{u}` gets stuck on `u =?= max ?v ?w`, because
Mathlib's `CompHausLike` instance is stated in two universes. -/
local instance instHasFiniteCoproductsCompHaus :
    HasFiniteCoproducts CompHaus.{u} := FinitaryExtensive.hasFiniteCoproducts

local instance instEffectusTotalFormCompHaus :
    EffectusTotalForm CompHaus.{u} := extensive_effectus_compHaus

local instance instHasFiniteCoproductsParCompHaus :
    HasFiniteCoproducts (Par CompHaus.{u}) := parHasFiniteCoproducts

/-- The final object of `CH` is a one-point space. -/
private noncomputable def chTopIso :
    (⊤_ CompHaus.{u}) ≅ CompHaus.of PUnit.{u + 1} :=
  terminalIsTerminal.uniqueUpToIso CompHausLike.isTerminalPUnit

noncomputable local instance instUniqueTerminalCompHaus :
    Unique (⊤_ CompHaus.{u}) where
  default := chTopIso.{u}.inv PUnit.unit
  uniq a := by
    have h : chTopIso.{u}.inv (chTopIso.{u}.hom a) = a :=
      congrArg (fun m : (⊤_ CompHaus.{u}) ⟶ (⊤_ CompHaus.{u}) => m a)
        chTopIso.{u}.hom_inv_id
    rw [← h, Subsingleton.elim (chTopIso.{u}.hom a) PUnit.unit]

/-- The two-point space `1 + 1` of `CH`. -/
private noncomputable abbrev chTwo : CompHaus.{u} :=
  CompHaus.of ((⊤_ CompHaus.{u}) ⊕ (⊤_ CompHaus.{u}))

private noncomputable abbrev chI₁ : (⊤_ CompHaus.{u}) ⟶ chTwo.{u} :=
  ConcreteCategory.ofHom ⟨Sum.inl, continuous_inl⟩

private noncomputable abbrev chI₂ : (⊤_ CompHaus.{u}) ⟶ chTwo.{u} :=
  ConcreteCategory.ofHom ⟨Sum.inr, continuous_inr⟩

/-- `⊤ + ⊤` in `CH` is the two-point discrete space. -/
private noncomputable def chCofan : IsColimit (BinaryCofan.mk chI₁.{u} chI₂.{u}) :=
  BinaryCofan.IsColimit.mk _
    (fun {_} u v => ConcreteCategory.ofHom
      ⟨Sum.elim (fun t => u t) (fun t => v t),
        Continuous.sumElim (ConcreteCategory.hom u).continuous
          (ConcreteCategory.hom v).continuous⟩)
    (fun {_} _ _ => ConcreteCategory.hom_ext _ _ (fun _ => rfl))
    (fun {_} _ _ => ConcreteCategory.hom_ext _ _ (fun _ => rfl))
    (fun {W} _ _ m h₁ h₂ => by
      refine ConcreteCategory.hom_ext _ _ (fun s => ?_)
      cases s with
      | inl t => exact congrArg (fun k : (⊤_ CompHaus.{u}) ⟶ W => k t) h₁
      | inr t => exact congrArg (fun k : (⊤_ CompHaus.{u}) ⟶ W => k t) h₂)

private theorem ch_i_ne : chI₁.{u} ≠ chI₂.{u} := by
  intro h
  have h2 : (Sum.inl (default : ⊤_ CompHaus.{u}) : chTwo.{u})
      = Sum.inr (default : ⊤_ CompHaus.{u}) :=
    congrArg (fun f : (⊤_ CompHaus.{u}) ⟶ chTwo.{u} =>
      f (default : ⊤_ CompHaus.{u})) h
  simp at h2

private theorem ch_top_hom_cases (k : (⊤_ CompHaus.{u}) ⟶ chTwo.{u}) :
    k = chI₁.{u} ∨ k = chI₂.{u} := by
  rcases hk : k (default : ⊤_ CompHaus.{u}) with a | a
  · left
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    have hx : x = (default : ⊤_ CompHaus.{u}) := Subsingleton.elim _ _
    subst hx
    rw [hk]
    exact congrArg Sum.inl (Subsingleton.elim a (default : ⊤_ CompHaus.{u}))
  · right
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    have hx : x = (default : ⊤_ CompHaus.{u}) := Subsingleton.elim _ _
    subst hx
    rw [hk]
    exact congrArg Sum.inr (Subsingleton.elim a (default : ⊤_ CompHaus.{u}))

/-- **190IV.3** (eff.tex:2168, Examples) for `bCH`: the scalars of `CH` are
the two-element effect monoid `2`.  (`Scal = CH(1, 1 + 1)`, and a one-point
space has exactly the two maps into a two-point space.) -/
theorem ch_scalars_two : ScalarsAreTwo (Par CompHaus.{u}) :=
  par_scalarsAreTwo_of_cofan chCofan ch_i_ne ch_top_hom_cases

section ChClopen

open Classical

/-- The map `X ⟶ 1 + 1` attached to a clopen subset `U ⊆ X`: it is locally
constant, hence continuous. -/
private noncomputable def chOfClopen {X : CompHaus.{u}} (U : Clopens X) :
    X ⟶ chTwo.{u} :=
  ConcreteCategory.ofHom
    ⟨fun x => if x ∈ U then (Sum.inl default : chTwo.{u}) else Sum.inr default, by
      refine IsLocallyConstant.continuous ?_
      refine (IsLocallyConstant.iff_exists_open _).mpr (fun x => ?_)
      by_cases hx : x ∈ U
      · refine ⟨(U : Set X), U.isOpen, hx, fun y hy => ?_⟩
        have hy' : y ∈ U := hy
        simp [hx, hy']
      · refine ⟨(U : Set X)ᶜ, U.isClopen.compl.isOpen, hx, fun y hy => ?_⟩
        have hy' : y ∉ U := hy
        simp [hx, hy']⟩

private theorem chOfClopen_apply {X : CompHaus.{u}} (U : Clopens X) (x : X) :
    chOfClopen U x
      = if x ∈ U then (Sum.inl default : chTwo.{u}) else Sum.inr default := rfl

/-- Continuous maps `X ⟶ 1 + 1` are the clopen subsets of `X`: the preimage
of the left summand is clopen, and conversely. -/
private noncomputable def chClopensEquiv (X : CompHaus.{u}) :
    (X ⟶ chTwo.{u}) ≃ Clopens X where
  toFun q := ⟨⇑q ⁻¹' Set.range (Sum.inl : (⊤_ CompHaus.{u}) → chTwo.{u}),
    isClopen_range_inl.preimage (ConcreteCategory.hom q).continuous⟩
  invFun U := chOfClopen U
  left_inv q := by
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    rw [chOfClopen_apply]
    rcases hq : (q x : chTwo.{u}) with a | a
    · simp [hq, Subsingleton.elim (default : ⊤_ CompHaus.{u}) a]
    · simp [hq, Subsingleton.elim (default : ⊤_ CompHaus.{u}) a]
  right_inv U := by
    refine SetLike.ext (fun x => ?_)
    show chOfClopen U x ∈ Set.range (Sum.inl : (⊤_ CompHaus.{u}) → chTwo.{u})
        ↔ x ∈ U
    rw [chOfClopen_apply]
    by_cases hx : x ∈ U
    · simp [hx]
    · simp [hx]

end ChClopen

/-- **190IV.3(c)** (eff.tex:2182, Examples), first half: in `bCH` **the
predicates on `X` correspond to the clopen subsets `U ⊆ X`**.

The correspondence is pinned by the two lemmas below: `1` is `X` itself and
`0` is `∅`. -/
noncomputable def ch_pred_clopens (X : CompHaus.{u}) :
    Pred (Par.of X) ≃ Clopens X :=
  (parPredEquiv chCofan.{u} X).trans (chClopensEquiv X)

/-- **190IV.3(c)**: the truth predicate is the whole space. -/
theorem ch_pred_clopens_truth (X : CompHaus.{u}) :
    ((ch_pred_clopens X (truth (Par.of X)) : Clopens X) : Set X) = Set.univ := by
  show ⇑(parPredEquiv chCofan.{u} X (truth (Par.of X)))
      ⁻¹' Set.range (Sum.inl : (⊤_ CompHaus.{u}) → chTwo.{u}) = Set.univ
  rw [parPredEquiv_truth]
  ext x
  exact ⟨fun _ => trivial, fun _ => ⟨terminal.from X x, rfl⟩⟩

/-- **190IV.3(c)**: the zero predicate is the empty subset. -/
theorem ch_pred_clopens_zero (X : CompHaus.{u}) :
    ((ch_pred_clopens X (0 : Pred (Par.of X)) : Clopens X) : Set X) = ∅ := by
  show ⇑(parPredEquiv chCofan.{u} X (0 : Pred (Par.of X)))
      ⁻¹' Set.range (Sum.inl : (⊤_ CompHaus.{u}) → chTwo.{u}) = ∅
  rw [parPredEquiv_zero]
  ext x
  simp

/-- **190IV.3(c)** (eff.tex:2184, Examples), second half: in `bCH` **the
states of `X` correspond to its points `x ∈ X`**. -/
noncomputable def ch_stat_point (X : CompHaus.{u}) : Stat (Par.of X) ≃ X :=
  (parStatEquiv X).trans
    { toFun := fun f => f (default : ⊤_ CompHaus.{u})
      invFun := fun p => ConcreteCategory.ofHom ⟨fun _ => p, continuous_const⟩
      left_inv := fun f => ConcreteCategory.hom_ext _ _ (fun t => by
        show f (default : ⊤_ CompHaus.{u}) = f t
        rw [Subsingleton.elim (default : ⊤_ CompHaus.{u}) t])
      right_inv := fun _ => rfl }

/-- **190IV.3(c)** (eff.tex:2184, Examples): `bCH` has **separating
states**.  The states of `X` are its points, and points are jointly epic in
`CH`. -/
theorem ch_separating_states : SeparatingStates (Par CompHaus.{u}) := by
  intro X Y f g h
  refine pval_inj ?_
  refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
  obtain ⟨w, hw⟩ : ∃ w : (⊤_ CompHaus.{u}) ⟶ X.base,
      w (default : ⊤_ CompHaus.{u}) = x :=
    ⟨ConcreteCategory.ofHom ⟨fun _ => x, continuous_const⟩, rfl⟩
  have hst : IsTotal (Par.hat w : Par.of (⊤_ CompHaus.{u}) ⟶ Par.of X.base) :=
    (par_isTotal_iff_hat _).mpr ⟨_, rfl⟩
  have h2 := h ⟨Par.hat w, hst⟩
  have h3 : w ≫ pval f = w ≫ pval g := by
    rw [← par_hat_comp, ← par_hat_comp]
    exact congrArg pval h2
  have h4 : pval f (w (default : ⊤_ CompHaus.{u}))
      = pval g (w (default : ⊤_ CompHaus.{u})) :=
    congrArg (fun m : (⊤_ CompHaus.{u}) ⟶ _ =>
      m (default : ⊤_ CompHaus.{u})) h3
  rw [hw] at h4
  exact h4

/-! ### 190IV.3(c): the predicates do not separate -/

/-- The unit interval, as a compact Hausdorff space in `Type u`. -/
private noncomputable abbrev chIcc : CompHaus.{u} := CompHaus.of (ULift.{u} I)

private theorem chIcc_preconnected : PreconnectedSpace (ULift.{u} I) := by
  constructor
  have h : (Set.univ : Set (ULift.{u} I)) = ULift.up '' (Set.univ : Set I) := by
    ext x
    exact ⟨fun _ => ⟨x.down, trivial, rfl⟩, fun _ => trivial⟩
  rw [h]
  exact isPreconnected_univ.image _ continuous_uliftUp.continuousOn

local instance instPreconnectedChIcc :
    PreconnectedSpace (chIcc.{u} : Type u) := chIcc_preconnected.{u}

private theorem chIcc_zero_ne_one :
    (ULift.up (0 : I) : ULift.{u} I) ≠ ULift.up (1 : I) := by
  intro h
  have h2 : ((0 : I) : ℝ) = ((1 : I) : ℝ) :=
    congrArg Subtype.val (congrArg ULift.down h)
  simp at h2

/-- On a connected space every predicate is constant: the clopen subset it
names is `∅` or the whole space. -/
private theorem ch_pred_const (q : chIcc.{u} ⟶ chTwo.{u}) (x y : chIcc.{u}) :
    q x = q y := by
  have hclopen : IsClopen (⇑q ⁻¹'
      Set.range (Sum.inl : (⊤_ CompHaus.{u}) → chTwo.{u})) :=
    isClopen_range_inl.preimage (ConcreteCategory.hom q).continuous
  rcases isClopen_iff.mp hclopen with h | h
  · have hx : q x ∉ Set.range (Sum.inl : (⊤_ CompHaus.{u}) → chTwo.{u}) :=
      Set.eq_empty_iff_forall_notMem.mp h x
    have hy : q y ∉ Set.range (Sum.inl : (⊤_ CompHaus.{u}) → chTwo.{u}) :=
      Set.eq_empty_iff_forall_notMem.mp h y
    rcases hqx : (q x : chTwo.{u}) with a | a
    · exact absurd ⟨a, rfl⟩ (hqx ▸ hx)
    · rcases hqy : (q y : chTwo.{u}) with b | b
      · exact absurd ⟨b, rfl⟩ (hqy ▸ hy)
      · exact congrArg Sum.inr (Subsingleton.elim a b)
  · have hx : q x ∈ Set.range (Sum.inl : (⊤_ CompHaus.{u}) → chTwo.{u}) :=
      Set.eq_univ_iff_forall.mp h x
    have hy : q y ∈ Set.range (Sum.inl : (⊤_ CompHaus.{u}) → chTwo.{u}) :=
      Set.eq_univ_iff_forall.mp h y
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    rw [← ha, ← hb, Subsingleton.elim a b]

/-- **190IV.3(c)** (eff.tex:2182, Examples): `bCH` does **not** have
separating predicates.

The witness is the unit interval `[0,1]`, which is connected, so its only
clopen subsets — hence its only predicates — are `∅` and `[0,1]`; both are
fixed by the two distinct endomaps `id` and the constant map at `0`. -/
theorem ch_no_separating_predicates :
    ¬ SeparatingPredicates (Par CompHaus.{u}) := by
  intro hsep
  obtain ⟨c, hc⟩ : ∃ c : chIcc.{u} ⟶ chIcc.{u},
      ∀ z : chIcc.{u}, c z = ULift.up (0 : I) :=
    ⟨ConcreteCategory.ofHom ⟨fun _ => ULift.up (0 : I), continuous_const⟩,
      fun _ => rfl⟩
  have hne : c ≠ 𝟙 chIcc.{u} := by
    intro hh
    refine chIcc_zero_ne_one.{u} ?_
    rw [← hc (ULift.up (1 : I))]
    exact congrArg (fun m : chIcc.{u} ⟶ chIcc.{u} => m (ULift.up (1 : I))) hh
  refine hne ?_
  refine par_hat_inj (Y := chIcc.{u}) ?_
  refine hsep (Par.hat c) (Par.hat (𝟙 chIcc.{u})) ?_
  intro p
  refine pval_inj ?_
  rw [par_hat_comp, par_hat_comp, Category.id_comp]
  refine (cancel_mono (parGamma chCofan.{u}).hom).mp ?_
  rw [Category.assoc]
  show c ≫ (parPredEquiv chCofan.{u} chIcc.{u} p)
      = parPredEquiv chCofan.{u} chIcc.{u} p
  refine ConcreteCategory.hom_ext _ _ (fun z => ?_)
  exact ch_pred_const (parPredEquiv chCofan.{u} chIcc.{u} p) (c z) z

end CompHausCase

end Theses.B.Eff
