/-
Theses/B/Eff/ExtensiveExamples.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
2143–2187: the point 190IV.3 and its three sub-items — the predicates,
states and scalars of the three *extensive* examples of an effectus,
`SET`, `CRngᵒᵖ` and `bCH`, whose effectus structure is 189aII.3
(`extensive_effectus_set`, `_commRing`, `_compHaus` in `B/Eff/Effectus`) —
and, at eff.tex:4460, the `SET` clause of **206III**: `SET` is a
⋄-effectus (`diamond_effectus_set`).  That is why this module imports
`B/Eff/DiamondAmp` rather than only `B/Eff/StatesPredicates`.

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
* **206III** for `SET` (an Examples point, no printed proof, so the
  argument is ours) is built on a second concrete handle, `parSetHom`: a
  partial map `X ⇸ Y` of `SET` read as a function `X → Option Y`, with
  transport lemmas for `⊙`, `id`, `1`, `0` and `(–)^⊥`.  Quotients are
  partial identities onto complements, comprehensions are total inclusions,
  images are set-theoretic images, and *every* predicate is sharp
  (`set_isSharp_all`), which makes the fourth axiom free.
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
  `effectus_vn_real_separating` in `B/Eff/VNExamples`;
* the `EJAᵒᵖ` clause of 206III, which has no category in the tree; its
  `vNᵒᵖ` and `CvNᵒᵖ` clauses are `diamond_effectus_vn` and
  `diamond_effectus_cvn` in `B/Eff/VNExamples`.
-/
import Theses.B.Eff.DiamondAmp

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

/-! ### 206III: the partial maps of `SET` as `X → Option Y` -/

/-- The comparison isomorphism `A + B ≅ A ⊕ B` of `SET`: Mathlib's
`Types.binaryCoproductIso`, under the name used below. -/
private noncomputable abbrev setGam (A B : Type u) : (A ⨿ B : Type u) ≅ (A ⊕ B) :=
  Types.binaryCoproductIso A B

/-- `γ ∘ κ₁ = inl`. -/
private theorem setGam_inl {A B : Type u} (a : A) :
    (setGam A B).hom ((coprod.inl : A ⟶ A ⨿ B) a) = Sum.inl a :=
  congrArg (fun m : A ⟶ (A ⊕ B) => m a) (Types.binaryCoproductIso_inl_comp_hom A B)

/-- `γ ∘ κ₂ = inr`. -/
private theorem setGam_inr {A B : Type u} (b : B) :
    (setGam A B).hom ((coprod.inr : B ⟶ A ⨿ B) b) = Sum.inr b :=
  congrArg (fun m : B ⟶ (A ⊕ B) => m b) (Types.binaryCoproductIso_inr_comp_hom A B)

/-- Every element of a binary coproduct of `SET` lies in one of the two
summands (the elementwise form of `Types.binaryCoproductIso`). -/
private theorem set_coprod_cases {A B : Type u} (v : (A ⨿ B : Type u)) :
    (∃ a, v = (coprod.inl : A ⟶ A ⨿ B) a) ∨ (∃ b, v = (coprod.inr : B ⟶ A ⨿ B) b) := by
  have e : ∀ z : (A ⨿ B : Type u), (setGam A B).inv ((setGam A B).hom z) = z := fun z =>
    congrArg (fun m : (A ⨿ B : Type u) ⟶ (A ⨿ B : Type u) => m z) (setGam A B).hom_inv_id
  have hinj : ∀ {v w : (A ⨿ B : Type u)},
      (setGam A B).hom v = (setGam A B).hom w → v = w := by
    intro v w h
    rw [← e v, ← e w, h]
  rcases hv : (setGam A B).hom v with a | b
  · exact Or.inl ⟨a, hinj (by rw [hv, setGam_inl])⟩
  · exact Or.inr ⟨b, hinj (by rw [hv, setGam_inr])⟩

/-- `Y + 1` of `SET`, read as `Option Y`: `κ₁ y ↦ some y`, `κ₂ ⋆ ↦ none`. -/
private noncomputable def setOpt {Y : Type u} (v : (Y ⨿ (⊤_ (Type u)) : Type u)) : Option Y :=
  Sum.elim some (fun _ => none) ((setGam Y (⊤_ (Type u))).hom v)

/-- `κ₁ y` is `some y`. -/
private theorem setOpt_inl {Y : Type u} (y : Y) :
    setOpt ((coprod.inl : Y ⟶ Y ⨿ (⊤_ (Type u))) y) = some y := by
  show Sum.elim some (fun _ => none) ((setGam Y (⊤_ (Type u))).hom _) = _
  rw [setGam_inl]
  rfl

/-- `κ₂ ⋆` is `none`. -/
private theorem setOpt_inr {Y : Type u} (t : (⊤_ (Type u))) :
    setOpt ((coprod.inr : (⊤_ (Type u)) ⟶ Y ⨿ (⊤_ (Type u))) t) = none := by
  show Sum.elim some (fun _ => none) ((setGam Y (⊤_ (Type u))).hom _) = _
  rw [setGam_inr]
  rfl

/-- The inverse of `setOpt`: `Option Y → Y + 1`. -/
private noncomputable def setInj {Y : Type u} (o : Option Y) :
    (Y ⨿ (⊤_ (Type u)) : Type u) :=
  o.elim ((coprod.inr : (⊤_ (Type u)) ⟶ Y ⨿ (⊤_ (Type u))) default)
    (fun y => (coprod.inl : Y ⟶ Y ⨿ (⊤_ (Type u))) y)

/-- `setOpt` undoes `setInj`. -/
private theorem setOpt_setInj {Y : Type u} (o : Option Y) : setOpt (setInj o) = o := by
  cases o with
  | none => exact setOpt_inr _
  | some y => exact setOpt_inl y

/-- `setInj` undoes `setOpt`. -/
private theorem setInj_setOpt {Y : Type u} (v : (Y ⨿ (⊤_ (Type u)) : Type u)) :
    setInj (setOpt v) = v := by
  rcases set_coprod_cases v with ⟨y, rfl⟩ | ⟨t, rfl⟩
  · rw [setOpt_inl]; rfl
  · rw [setOpt_inr]
    exact congrArg (fun s => (coprod.inr : (⊤_ (Type u)) ⟶ Y ⨿ (⊤_ (Type u))) s)
      (Subsingleton.elim _ _)

/-- **206III** (eff.tex:4460, Examples), the concrete handle for `SET`: a
partial map `f : X ⇸ Y` of `SET` — that is, a map `X ⟶ Y + 1` — read as the
partial function `X → Option Y` it is.

The abstract coproduct `Y + 1` is the only obstacle to computing with
`Par (Type u)` by hand; `parSetHom` and the transport lemmas below
(`parSetHom_comp`, `_id`, `_hat`, `_zero`, `parSetHom_truth_isSome`,
`parSetHom_orth_isSome`) remove it once and for all, and everything the
⋄-effectus axioms need is then ordinary reasoning about `Option`. -/
noncomputable def parSetHom {X Y : Par (Type u)} (f : X ⟶ Y) : X.base → Option Y.base :=
  fun x => setOpt (pval f x)

/-- **206III** (eff.tex:4460, Examples): `parSetHom` is a bijection —
the partial maps `X ⇸ Y` of `SET` *are* the functions `X → Option Y`. -/
noncomputable def parSetHomEquiv (X Y : Par (Type u)) :
    (X ⟶ Y) ≃ (X.base → Option Y.base) where
  toFun := parSetHom
  invFun g := show X ⟶ Y from
    (↾(fun x => setInj (g x)) : X.base ⟶ Y.base ⨿ (⊤_ (Type u)))
  left_inv f := by
    refine pval_inj ?_
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact setInj_setOpt (pval f x)
  right_inv g := funext fun x => setOpt_setInj (g x)

/-- The partial map named by a function `X → Option Y` has that function as
its `parSetHom`. -/
theorem parSetHom_symm_apply (X Y : Par (Type u)) (g : X.base → Option Y.base)
    (x : X.base) : parSetHom ((parSetHomEquiv X Y).symm g) x = g x :=
  setOpt_setInj (g x)

/-- A partial map of `SET` is determined by its values. -/
theorem parSetHom_injective {X Y : Par (Type u)} {f g : X ⟶ Y}
    (h : ∀ x, parSetHom f x = parSetHom g x) : f = g :=
  (parSetHomEquiv X Y).injective (funext h)

/-- Composition in `Par SET` is Kleisli composition of partial
functions. -/
theorem parSetHom_comp {X Y Z : Par (Type u)} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.base) :
    parSetHom (f ≫ g : X ⟶ Z) x = (parSetHom f x).bind (parSetHom g) := by
  have hv : parSetHom (f ≫ g : X ⟶ Z) x
      = setOpt ((coprod.desc (pval g)
          (coprod.inr : (⊤_ (Type u)) ⟶ Z.base ⨿ (⊤_ (Type u)))) (pval f x)) := rfl
  have hf : parSetHom f x = setOpt (pval f x) := rfl
  rw [hv, hf]
  rcases set_coprod_cases (pval f x) with ⟨y, hy⟩ | ⟨t, ht⟩
  · rw [hy, setOpt_inl]
    have h2 : setOpt ((coprod.desc (pval g)
        (coprod.inr : (⊤_ (Type u)) ⟶ Z.base ⨿ (⊤_ (Type u))))
          ((coprod.inl : Y.base ⟶ Y.base ⨿ (⊤_ (Type u))) y))
        = setOpt (((coprod.inl : Y.base ⟶ Y.base ⨿ (⊤_ (Type u))) ≫ coprod.desc (pval g)
          (coprod.inr : (⊤_ (Type u)) ⟶ Z.base ⨿ (⊤_ (Type u)))) y) := rfl
    rw [h2, coprod.inl_desc]
    rfl
  · rw [ht, setOpt_inr]
    have h2 : setOpt ((coprod.desc (pval g)
        (coprod.inr : (⊤_ (Type u)) ⟶ Z.base ⨿ (⊤_ (Type u))))
          ((coprod.inr : (⊤_ (Type u)) ⟶ Y.base ⨿ (⊤_ (Type u))) t))
        = setOpt (((coprod.inr : (⊤_ (Type u)) ⟶ Y.base ⨿ (⊤_ (Type u))) ≫ coprod.desc (pval g)
          (coprod.inr : (⊤_ (Type u)) ⟶ Z.base ⨿ (⊤_ (Type u)))) t) := rfl
    rw [h2, coprod.inr_desc]
    exact setOpt_inr t

/-- Composition, in the form used below: where `f` is defined at `x`, with
value `y`, the composite `g ⊙ f` takes the value of `g` at `y`. -/
theorem parSetHom_comp_of_some {X Y Z : Par (Type u)} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.base)
    (y : Y.base) (h : parSetHom f x = some y) :
    parSetHom (f ≫ g : X ⟶ Z) x = parSetHom g y := by
  rw [parSetHom_comp f g x, h]
  rfl

/-- Composition, in the form used below: where `f` is undefined, so is
`g ⊙ f`. -/
theorem parSetHom_comp_of_none {X Y Z : Par (Type u)} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.base)
    (h : parSetHom f x = none) : parSetHom (f ≫ g : X ⟶ Z) x = none := by
  rw [parSetHom_comp f g x, h]
  rfl

/-- The Kleisli embedding `f̂` of a total map is the everywhere-defined
partial function. -/
theorem parSetHom_hat {A B : Type u} (w : A ⟶ B) (a : A) :
    parSetHom (Par.hat w : Par.of A ⟶ Par.of B) a = some (w a) :=
  setOpt_inl (w a)

/-- The identity of `Par SET` is the everywhere-defined identity. -/
theorem parSetHom_id {X : Par (Type u)} (x : X.base) :
    parSetHom (𝟙 X) x = some x := setOpt_inl x

/-- The zero map of `Par SET` is the nowhere-defined partial function. -/
theorem parSetHom_zero {X Y : Par (Type u)} (x : X.base) :
    parSetHom (0 : X ⟶ Y) x = none := setOpt_inr _

/-- The truth predicate is everywhere defined. -/
theorem parSetHom_truth_isSome {X : Par (Type u)} (x : X.base) :
    (parSetHom (truth X) x).isSome = true := by
  have h : parSetHom (truth X) x
      = setOpt ((coprod.inl : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u))
        (terminal.from X.base x)) := rfl
  rw [h, setOpt_inl]
  rfl

/-- `1 ∘ f` is defined exactly where `f` is: it is the *domain* of `f`, read
as a predicate. -/
theorem parSetHom_comp_truth_isSome {X Y : Par (Type u)} (f : X ⟶ Y) (x : X.base) :
    (parSetHom (f ≫ truth Y : X ⟶ effObj (Par (Type u))) x).isSome
      = (parSetHom f x).isSome := by
  cases hf : parSetHom f x with
  | none => rw [parSetHom_comp_of_none f (truth Y) x hf]; rfl
  | some y => rw [parSetHom_comp_of_some f (truth Y) x y hf, parSetHom_truth_isSome]; rfl

/-- The orthosupplement's `[κ₂,κ₁] : 1 + 1 ⟶ 1 + 1` swaps `κ₁` to `κ₂`. -/
private theorem set_swapTop_inl (t : (⊤_ (Type u))) :
    (parSwapTop : ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u) ⟶
        ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u))
        ((coprod.inl : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) t)
      = (coprod.inr : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) t := by
  have h : (coprod.inl : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) ≫
      (parSwapTop : ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u) ⟶
        ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) = coprod.inr := by
    rw [parSwapTop_eq, coprod.inl_desc]
  exact congrArg
    (fun m : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u) => m t) h

/-- The orthosupplement's `[κ₂,κ₁] : 1 + 1 ⟶ 1 + 1` swaps `κ₂` to `κ₁`. -/
private theorem set_swapTop_inr (t : (⊤_ (Type u))) :
    (parSwapTop : ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u) ⟶
        ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u))
        ((coprod.inr : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) t)
      = (coprod.inl : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) t := by
  have h : (coprod.inr : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) ≫
      (parSwapTop : ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u) ⟶
        ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) = coprod.inl := by
    rw [parSwapTop_eq, coprod.inr_desc]
  exact congrArg
    (fun m : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u) => m t) h

/-- **190IV.3(a)**, in the `Option` form: `p^⊥` is defined exactly where `p`
is not — the complement of `set_pred_subset_orth`, stated on domains. -/
theorem parSetHom_orth_isSome {X : Par (Type u)} (p : Pred X) (x : X.base) :
    (parSetHom (orth p) x).isSome = !(parSetHom p x).isSome := by
  have key : ∀ v : ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u),
      (setOpt ((parSwapTop : ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u) ⟶
          ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) v)).isSome = !(setOpt v).isSome := by
    intro v
    rcases set_coprod_cases v with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [set_swapTop_inl, setOpt_inr, setOpt_inl]
      rfl
    · rw [set_swapTop_inr, setOpt_inl, setOpt_inr]
      rfl
  exact key (pval p x)

/-- The effect object of `Par SET` is the final set, so it has at most one
element. -/
private theorem set_effObj_elim (a b : (effObj (Par (Type u))).base) : a = b :=
  Subsingleton.elim (α := (⊤_ (Type u))) a b

/-- Two predicates of `SET` with the same domain are equal: a predicate
takes values in the final set, so only its domain carries information.  This
is the extensionality principle every argument below ends with. -/
theorem set_pred_ext {X : Par (Type u)} {p q : Pred X}
    (h : ∀ x, (parSetHom p x).isSome = (parSetHom q x).isSome) : p = q := by
  refine parSetHom_injective (fun x => ?_)
  have hx := h x
  cases hp : parSetHom p x with
  | none =>
      cases hq : parSetHom q x with
      | none => rfl
      | some b => rw [hp, hq] at hx; simp at hx
  | some a =>
      cases hq : parSetHom q x with
      | none => rw [hp, hq] at hx; simp at hx
      | some b => exact congrArg some (set_effObj_elim a b)

/-! ### 206III: the algebraic order on the predicates of `SET` -/

/-- The codiagonal `∇ = [id, id]` is everywhere defined. -/
private theorem parSetHom_nabla {A : Type u} (v : (A ⨿ A : Type u)) :
    (parSetHom (parNabla A) v).isSome = true := by
  have h : parSetHom (parNabla A) v
      = parSetHom (Par.hat (coprod.desc (𝟙 A) (𝟙 A)) : Par.of (A ⨿ A) ⟶ Par.of A) v := rfl
  rw [h, parSetHom_hat]
  rfl

/-- The partial projector `▷₁ = [id, 0]` is defined on the left summand. -/
private theorem parSetHom_pproj₁_inl {A B : Type u} (a : A) :
    parSetHom (Par.pproj₁ A B) ((coprod.inl : A ⟶ A ⨿ B) a) = some a := by
  have h : parSetHom (Par.pproj₁ A B) ((coprod.inl : A ⟶ A ⨿ B) a)
      = setOpt (((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc
          (coprod.inl : A ⟶ A ⨿ (⊤_ (Type u)))
          (terminal.from B ≫ (coprod.inr : (⊤_ (Type u)) ⟶ A ⨿ (⊤_ (Type u))))) a) := rfl
  rw [h, coprod.inl_desc]
  exact setOpt_inl a

/-- The partial projector `▷₁ = [id, 0]` is undefined on the right
summand. -/
private theorem parSetHom_pproj₁_inr {A B : Type u} (b : B) :
    parSetHom (Par.pproj₁ A B) ((coprod.inr : B ⟶ A ⨿ B) b) = none := by
  have h : parSetHom (Par.pproj₁ A B) ((coprod.inr : B ⟶ A ⨿ B) b)
      = setOpt (((coprod.inr : B ⟶ A ⨿ B) ≫ coprod.desc
          (coprod.inl : A ⟶ A ⨿ (⊤_ (Type u)))
          (terminal.from B ≫ (coprod.inr : (⊤_ (Type u)) ⟶ A ⨿ (⊤_ (Type u))))) b) := rfl
  rw [h, coprod.inr_desc]
  exact setOpt_inr _

/-- **206III** for `SET`, first half of the order: if `p ≤ q` in the
algebraic order of the hom-PCM, then `q` is defined wherever `p` is.

The bound `b` witnessing `p ⊥ c` has `p = ▷₁ ⊙ b`, so `b` is defined
wherever `p` is; and `q = p ⋁ c = ∇ ⊙ b`, which is defined wherever `b`
is. -/
theorem set_le_isSome {X Y : Par (Type u)} {p q : X ⟶ Y} (h : p ≼ q) {x : X.base}
    (hx : (parSetHom p x).isSome = true) : (parSetHom q x).isSome = true := by
  obtain ⟨c, hperp, hovee⟩ := h
  obtain ⟨b, hb₁, hb₂⟩ := id hperp
  have hq : q = b ≫ parNabla Y.base := by
    rw [← hovee]; exact parOvee_eq hperp ⟨hb₁, hb₂⟩
  have hbx : ∃ v, parSetHom b x = some v := by
    cases hbv : parSetHom b x with
    | none =>
        rw [← hb₁, parSetHom_comp_of_none b (Par.pproj₁ Y.base Y.base) x hbv] at hx
        simp at hx
    | some v => exact ⟨v, rfl⟩
  obtain ⟨v, hv⟩ := hbx
  rw [hq, parSetHom_comp_of_some b (parNabla Y.base) x v hv]
  exact parSetHom_nabla v

/-- The bound witnessing `p ⊥ (q − p)` for predicates `p ≤ q` of `SET`: it
sends `x` into the left summand on the domain of `p`, into the right summand
on the rest of the domain of `q`, and is undefined elsewhere. -/
private noncomputable def setBound {X : Par (Type u)} (p q : Pred X) (x : X.base) :
    Option (((⊤_ (Type u)) ⨿ (⊤_ (Type u))) : Type u) :=
  cond (parSetHom p x).isSome
    (some ((coprod.inl : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) default))
    (cond (parSetHom q x).isSome
      (some ((coprod.inr : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) default))
      none)

/-- `setBound` on the domain of `p`. -/
private theorem setBound_pos {X : Par (Type u)} (p q : Pred X) {x : X.base}
    (hp : (parSetHom p x).isSome = true) :
    setBound p q x
      = some ((coprod.inl : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u))
        default) := by
  have e : setBound p q x = cond (parSetHom p x).isSome
      (some ((coprod.inl : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) default))
      (cond (parSetHom q x).isSome
        (some ((coprod.inr : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) default))
        none) := rfl
  rw [e, hp]
  rfl

/-- `setBound` on the domain of `q` minus that of `p`. -/
private theorem setBound_mid {X : Par (Type u)} (p q : Pred X) {x : X.base}
    (hp : (parSetHom p x).isSome = false) (hq : (parSetHom q x).isSome = true) :
    setBound p q x
      = some ((coprod.inr : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u))
        default) := by
  have e : setBound p q x = cond (parSetHom p x).isSome
      (some ((coprod.inl : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) default))
      (cond (parSetHom q x).isSome
        (some ((coprod.inr : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) default))
        none) := rfl
  rw [e, hp, hq]
  rfl

/-- `setBound` off the domain of `q`. -/
private theorem setBound_neg {X : Par (Type u)} (p q : Pred X) {x : X.base}
    (hp : (parSetHom p x).isSome = false) (hq : (parSetHom q x).isSome = false) :
    setBound p q x = none := by
  have e : setBound p q x = cond (parSetHom p x).isSome
      (some ((coprod.inl : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) default))
      (cond (parSetHom q x).isSome
        (some ((coprod.inr : (⊤_ (Type u)) ⟶ ((⊤_ (Type u)) ⨿ (⊤_ (Type u)) : Type u)) default))
        none) := rfl
  rw [e, hp, hq]
  rfl

/-- **206III** for `SET`, second half of the order: a predicate `p` is below
`q` as soon as `q` is defined wherever `p` is.  Together with
`set_le_isSome` this says that the algebraic order on `Pred (Par.of X)` is
inclusion of subsets, as 190IV.3(a) would have it. -/
theorem set_le_of_isSome {X : Par (Type u)} {p q : Pred X}
    (h : ∀ x, (parSetHom p x).isSome = true → (parSetHom q x).isSome = true) : p ≼ q := by
  obtain ⟨b, hb⟩ : ∃ b : X ⟶ Par.of (((⊤_ (Type u)) ⨿ (⊤_ (Type u))) : Type u),
      ∀ x, parSetHom b x = setBound p q x :=
    ⟨(parSetHomEquiv _ _).symm _, fun x => parSetHom_symm_apply _ _ _ x⟩
  have hb₁ : b ≫ Par.pproj₁ (⊤_ (Type u)) (⊤_ (Type u)) = p := by
    refine set_pred_ext (fun x => ?_)
    cases hp : (parSetHom p x).isSome with
    | true =>
        rw [parSetHom_comp_of_some b (Par.pproj₁ (⊤_ (Type u)) (⊤_ (Type u))) x _
          ((hb x).trans (setBound_pos p q hp)), parSetHom_pproj₁_inl]
        rfl
    | false =>
        cases hq : (parSetHom q x).isSome with
        | true =>
            rw [parSetHom_comp_of_some b (Par.pproj₁ (⊤_ (Type u)) (⊤_ (Type u))) x _
              ((hb x).trans (setBound_mid p q hp hq)), parSetHom_pproj₁_inr]
            rfl
        | false =>
            rw [parSetHom_comp_of_none b (Par.pproj₁ (⊤_ (Type u)) (⊤_ (Type u))) x
              ((hb x).trans (setBound_neg p q hp hq))]
            rfl
  refine ⟨b ≫ Par.pproj₂ (⊤_ (Type u)) (⊤_ (Type u)), ⟨b, hb₁, rfl⟩, ?_⟩
  have hov : ovee p (b ≫ Par.pproj₂ (⊤_ (Type u)) (⊤_ (Type u)))
      (⟨b, hb₁, rfl⟩ : Perp p (b ≫ Par.pproj₂ (⊤_ (Type u)) (⊤_ (Type u))))
      = b ≫ parNabla (⊤_ (Type u)) := parOvee_eq _ ⟨hb₁, rfl⟩
  rw [hov]
  refine set_pred_ext (fun x => ?_)
  cases hp : (parSetHom p x).isSome with
  | true =>
      rw [parSetHom_comp_of_some b (parNabla (⊤_ (Type u))) x _
        ((hb x).trans (setBound_pos p q hp)), h x hp]
      exact parSetHom_nabla _
  | false =>
      cases hq : (parSetHom q x).isSome with
      | true =>
          rw [parSetHom_comp_of_some b (parNabla (⊤_ (Type u))) x _
            ((hb x).trans (setBound_mid p q hp hq))]
          exact parSetHom_nabla _
      | false =>
          rw [parSetHom_comp_of_none b (parNabla (⊤_ (Type u))) x
            ((hb x).trans (setBound_neg p q hp hq))]
          rfl

/-! ### 206III: quotients, comprehension, images and sharpness in `SET` -/

/-- The partial identity `X ⇸ {x | S x = false}`, defined exactly off
`S` — the quotient map of a predicate. -/
private def setRestrict {A : Type u} (S : A → Bool) (a : A) :
    Option {x : A // S x = false} :=
  if h : S a = false then some ⟨a, h⟩ else none

/-- `setRestrict` off `S`. -/
private theorem setRestrict_pos {A : Type u} (S : A → Bool) {a : A} (h : S a = false) :
    setRestrict S a = some ⟨a, h⟩ := by
  unfold setRestrict
  split
  · rfl
  · next h' => exact absurd h h'

/-- `setRestrict` on `S`. -/
private theorem setRestrict_neg {A : Type u} (S : A → Bool) {a : A} (h : S a = true) :
    setRestrict S a = none := by
  unfold setRestrict
  split
  · next h' => rw [h] at h'; simp at h'
  · rfl

/-- The partial identity `X ⇸ {x | S x = true}`, defined exactly on `S`
(used to corestrict a map that already lands in `S`). -/
private def setCorestrict {A : Type u} (S : A → Bool) (a : A) :
    Option {x : A // S x = true} :=
  if h : S a = true then some ⟨a, h⟩ else none

/-- `setCorestrict` on `S`. -/
private theorem setCorestrict_pos {A : Type u} (S : A → Bool) {a : A} (h : S a = true) :
    setCorestrict S a = some ⟨a, h⟩ := by
  unfold setCorestrict
  split
  · rfl
  · next h' => exact absurd h h'

/-- A `Bool` that is not `false` is `true`. -/
private theorem set_isSome_eq_true {b : Bool} (h : ¬ b = false) : b = true := by
  cases hb : b with
  | false => exact absurd hb h
  | true => rfl

/-- **206III** (eff.tex:4460, Examples) for `SET`: `SET` **has quotients**.

The point prints no proof, so this is our own.  For a predicate `p` with
domain `U ⊆ X` the quotient is the partial identity `ξ_p : X ⇸ Uᶜ` defined
exactly off `U`.  Then `1 ∘ ξ_p` is the predicate `Uᶜ = p^⊥` on the nose, so
the inequality `1 ∘ ξ_p ≤ p^⊥` of 197II holds reflexively; and a partial map
`f : X ⇸ Y` with `1 ∘ f ≤ p^⊥` is undefined on `U`, hence factors through
`ξ_p` by the unique `f'` with `f'(x) = f(x)`. -/
theorem set_hasQuotients : HasQuotients (Par (Type u)) where
  quot {X} p := by
    obtain ⟨ξ, hξ⟩ : ∃ ξ : X ⟶ Par.of {x : X.base // (parSetHom p x).isSome = false},
        ∀ x, parSetHom ξ x = setRestrict (fun x => (parSetHom p x).isSome) x :=
      ⟨(parSetHomEquiv _ _).symm _, fun x => parSetHom_symm_apply _ _ _ x⟩
    refine ⟨Par.of {x : X.base // (parSetHom p x).isSome = false}, ξ, ?_, ?_⟩
    · have he : (ξ ≫ truth (Par.of {x : X.base // (parSetHom p x).isSome = false}) :
          X ⟶ effObj (Par (Type u))) = orth p := by
        refine set_pred_ext (fun x => ?_)
        rw [parSetHom_comp_truth_isSome ξ x, hξ x, parSetHom_orth_isSome]
        by_cases hp : (parSetHom p x).isSome = false
        · rw [setRestrict_pos (fun x => (parSetHom p x).isSome) hp]
          show (true : Bool) = !(parSetHom p x).isSome
          rw [hp]
          rfl
        · rw [setRestrict_neg (fun x => (parSetHom p x).isSome) (set_isSome_eq_true hp)]
          show (false : Bool) = !(parSetHom p x).isSome
          rw [set_isSome_eq_true hp]
          rfl
      rw [he]
      exact pcm_preorder_refl _
    · intro Y f hf
      have hdom : ∀ x, (parSetHom f x).isSome = true → (parSetHom p x).isSome = false := by
        intro x hx
        have h1 : (parSetHom (f ≫ truth Y : X ⟶ effObj (Par (Type u))) x).isSome = true := by
          rw [parSetHom_comp_truth_isSome f x]; exact hx
        have h2 := set_le_isSome hf h1
        rw [parSetHom_orth_isSome] at h2
        cases hc : (parSetHom p x).isSome with
        | false => rfl
        | true => rw [hc] at h2; simp at h2
      obtain ⟨f', hf'⟩ : ∃ f' : Par.of {x : X.base // (parSetHom p x).isSome = false} ⟶ Y,
          ∀ w, parSetHom f' w = parSetHom f w.1 :=
        ⟨(parSetHomEquiv _ _).symm _, fun w => parSetHom_symm_apply _ _ _ w⟩
      refine ⟨f', ?_, ?_⟩
      · refine parSetHom_injective (fun x => ?_)
        by_cases hp : (parSetHom p x).isSome = false
        · rw [parSetHom_comp_of_some ξ f' x ⟨x, hp⟩
            ((hξ x).trans (setRestrict_pos (fun x => (parSetHom p x).isSome) hp)), hf']
        · rw [parSetHom_comp_of_none ξ f' x ((hξ x).trans
            (setRestrict_neg (fun x => (parSetHom p x).isSome) (set_isSome_eq_true hp)))]
          cases hfx : parSetHom f x with
          | none => rfl
          | some y =>
              have hcon := hdom x (by rw [hfx]; rfl)
              exact absurd hcon hp
      · intro g hg
        refine parSetHom_injective (fun w => ?_)
        rw [hf' w]
        have h1 : parSetHom (ξ ≫ g : X ⟶ Y) w.1 = parSetHom f w.1 := by rw [hg]
        rw [parSetHom_comp_of_some ξ g w.1 w
          ((hξ w.1).trans (setRestrict_pos (fun x => (parSetHom p x).isSome) w.2))] at h1
        exact h1

/-- **206III** (eff.tex:4460, Examples) for `SET`: `SET` **has
comprehension**.

Again our own proof.  For a predicate `p` with domain `U ⊆ X` the
comprehension is the total inclusion `π_p : U ⇸ X`; `p ∘ π_p = 1 ∘ π_p`
because `p` is defined everywhere on `U`.  A map `g : Z ⇸ X` with
`p ∘ g = 1 ∘ g` lands in `U` wherever it is defined, so it corestricts to
`U`, uniquely because `π_p` is injective. -/
theorem set_hasComprehension : HasComprehension (Par (Type u)) where
  compr {X} p := by
    obtain ⟨π, hπ⟩ : ∃ π : Par.of {x : X.base // (parSetHom p x).isSome = true} ⟶ X,
        ∀ w, parSetHom π w = some w.1 :=
      ⟨Par.hat (↾(Subtype.val)), fun w => parSetHom_hat _ w⟩
    refine ⟨Par.of {x : X.base // (parSetHom p x).isSome = true}, π, ?_, ?_⟩
    · refine set_pred_ext (fun w => ?_)
      rw [parSetHom_comp_of_some π p w w.1 (hπ w), parSetHom_comp_truth_isSome π w, hπ w]
      exact w.2
    · intro Z g hg
      have hdom : ∀ (z : Z.base) (y : X.base), parSetHom g z = some y →
          (parSetHom p y).isSome = true := by
        intro z y hz
        have h1 : (parSetHom (g ≫ p : Z ⟶ effObj (Par (Type u))) z).isSome
            = (parSetHom (g ≫ truth X : Z ⟶ effObj (Par (Type u))) z).isSome := by rw [hg]
        rw [parSetHom_comp_of_some g p z y hz, parSetHom_comp_truth_isSome g z, hz] at h1
        exact h1
      obtain ⟨g', hg'⟩ : ∃ g' : Z ⟶ Par.of {x : X.base // (parSetHom p x).isSome = true},
          ∀ z, parSetHom g' z
            = (parSetHom g z).bind (setCorestrict (fun x => (parSetHom p x).isSome)) :=
        ⟨(parSetHomEquiv _ _).symm _, fun z => parSetHom_symm_apply _ _ _ z⟩
      refine ⟨g', ?_, ?_⟩
      · refine parSetHom_injective (fun z => ?_)
        cases hz : parSetHom g z with
        | none =>
            rw [parSetHom_comp_of_none g' π z (by rw [hg' z, hz]; rfl)]
        | some y =>
            rw [parSetHom_comp_of_some g' π z ⟨y, hdom z y hz⟩
              (by rw [hg' z, hz]
                  exact setCorestrict_pos (fun x => (parSetHom p x).isSome) (hdom z y hz)),
              hπ]
      · intro k hk
        refine parSetHom_injective (fun z => ?_)
        rw [hg' z]
        have h1 : parSetHom (k ≫ π : Z ⟶ X) z = parSetHom g z := by rw [hk]
        cases hkz : parSetHom k z with
        | none =>
            rw [parSetHom_comp_of_none k π z hkz] at h1
            rw [← h1]
            rfl
        | some w =>
            rw [parSetHom_comp_of_some k π z w hkz, hπ w] at h1
            rw [← h1]
            exact (setCorestrict_pos (fun x => (parSetHom p x).isSome) w.2).symm

/-- The predicate of `SET` whose domain is a given (not necessarily
decidable) subset. -/
private noncomputable def setPredOf {Y : Par (Type u)} (S : Y.base → Prop) : Pred Y :=
  (parSetHomEquiv Y (Par.of (⊤_ (Type u)))).symm
    (fun y => @ite (Option (⊤_ (Type u))) (S y) (Classical.propDecidable (S y))
      (some default) none)

/-- `setPredOf S` has domain `S`. -/
private theorem setPredOf_isSome {Y : Par (Type u)} (S : Y.base → Prop) (y : Y.base) :
    (parSetHom (setPredOf S) y).isSome = true ↔ S y := by
  have h : parSetHom (setPredOf S) y
      = @ite (Option (⊤_ (Type u))) (S y) (Classical.propDecidable (S y))
        (some default) none :=
    parSetHom_symm_apply Y (Par.of (⊤_ (Type u))) _ y
  rw [h]
  by_cases hs : S y <;> simp [hs]

/-- **206III** (eff.tex:4460, Examples) for `SET`: `SET` **has images**.

Our own proof: the image of `f : X ⇸ Y` is the set-theoretic image
`{y | ∃ x, f(x) = y}` of the domain of definition of `f`.  It satisfies
`im ∘ f = 1 ∘ f` by construction, and it is the least such predicate because
any `q` with `q ∘ f = 1 ∘ f` is defined at every `f(x)`. -/
theorem set_hasImages : HasImages (Par (Type u)) where
  im {X Y} f := by
    refine ⟨setPredOf (fun y => ∃ x, parSetHom f x = some y), ?_, ?_⟩
    · refine set_pred_ext (fun x => ?_)
      cases hf : parSetHom f x with
      | none =>
          rw [parSetHom_comp_of_none f (setPredOf _) x hf,
            parSetHom_comp_truth_isSome f x, hf]
          rfl
      | some y =>
          rw [parSetHom_comp_of_some f (setPredOf _) x y hf,
            parSetHom_comp_truth_isSome f x, hf,
            (setPredOf_isSome (fun y => ∃ x, parSetHom f x = some y) y).mpr ⟨x, hf⟩]
          rfl
    · intro q hq
      refine set_le_of_isSome (fun y hy => ?_)
      obtain ⟨x, hx⟩ := (setPredOf_isSome _ y).mp hy
      have h1 : (parSetHom (f ≫ q : X ⟶ effObj (Par (Type u))) x).isSome
          = (parSetHom (f ≫ truth Y : X ⟶ effObj (Par (Type u))) x).isSome := by rw [hq]
      rw [parSetHom_comp_of_some f q x y hx, parSetHom_comp_truth_isSome f x, hx] at h1
      exact h1

/-- **206III** (eff.tex:4460, Examples) for `SET`: **every** predicate of
`SET` is sharp.

A predicate with domain `U ⊆ X` is the image of the total inclusion
`U ⇸ X`: that inclusion is everywhere defined on `U`, and any predicate `q`
with `q ∘ ι = 1 ∘ ι` is defined on all of `U`.  In particular the last axiom
of a ⋄-effectus, "`s^⊥` is sharp for sharp `s`", is free here. -/
theorem set_isSharp_all {X : Par (Type u)} (p : Pred X) : IsSharp p := by
  obtain ⟨π, hπ⟩ : ∃ π : Par.of {x : X.base // (parSetHom p x).isSome = true} ⟶ X,
      ∀ w, parSetHom π w = some w.1 :=
    ⟨Par.hat (↾(Subtype.val)), fun w => parSetHom_hat _ w⟩
  refine ⟨Par.of {x : X.base // (parSetHom p x).isSome = true}, π, ?_, ?_⟩
  · refine set_pred_ext (fun w => ?_)
    rw [parSetHom_comp_of_some π p w w.1 (hπ w), parSetHom_comp_truth_isSome π w, hπ w]
    exact w.2
  · intro q hq
    refine set_le_of_isSome (fun x hx => ?_)
    have h1 : (parSetHom (π ≫ q :
          Par.of {x : X.base // (parSetHom p x).isSome = true} ⟶ effObj (Par (Type u)))
          ⟨x, hx⟩).isSome
        = (parSetHom (π ≫ truth X :
          Par.of {x : X.base // (parSetHom p x).isSome = true} ⟶ effObj (Par (Type u)))
          ⟨x, hx⟩).isSome := by rw [hq]
    rw [parSetHom_comp_of_some π q ⟨x, hx⟩ x (hπ ⟨x, hx⟩),
      parSetHom_comp_truth_isSome π ⟨x, hx⟩, hπ ⟨x, hx⟩] at h1
    exact h1

/-- **206III** (eff.tex:4460, Examples), the `SET` clause: **`SET` is a
⋄-effectus**.

The point states it without proof, so the argument is ours; it is assembled
from `set_hasQuotients`, `set_hasComprehension` and `set_hasImages`, with
the fourth axiom supplied by `set_isSharp_all` — in `SET` every predicate is
sharp, so orthocomplements of sharp predicates trivially are.

The three quotient/comprehension/image constructions are the expected ones
for partial functions: for a predicate with domain `U ⊆ X` the quotient is
the partial identity onto `Uᶜ`, the comprehension is the total inclusion of
`U`, and the image of `f` is the set-theoretic image of its domain of
definition.  All of it is carried out through `parSetHom`, which presents a
partial map `X ⇸ Y` of `SET` as a function `X → Option Y`.

The sibling clauses `vNᵒᵖ` and `CvNᵒᵖ` of the same Examples are
`diamond_effectus_vn` and `diamond_effectus_cvn` in
`Theses/B/Eff/VNExamples.lean`; `EJAᵒᵖ` has no category in the tree. -/
theorem diamond_effectus_set : DiamondEffectus (Par (Type u)) :=
  { set_hasQuotients, set_hasComprehension, set_hasImages with
    orth_sharp := fun _ => set_isSharp_all _ }

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
