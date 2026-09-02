/-
Theses/B/Eff/Dagger.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
5254–7118: †-categories and †-effectuses (parsecs 214–215), consequences of
the †-effectus axioms (216), the dagger of a pure map in a †'-effectus
(217), pristine maps (218), functoriality of the dagger and the equivalence
theorem (219–220), and dilations in an effectus (221–223).

Design:
* `DaggerCat D` is the structure of a †-category on a category `D`
  (identity-on-objects is built into the type); `DaggerEffectus C` bundles
  a dagger on `Pure C` with the three axioms of 215I over an &-effectus.
* `DaggerPrimeEffectus C` is the Prop-class of †'-effectuses (215V:
  &-effectuses satisfying the three axioms of the theorem 215III).
* The dagger of a pure map in a †'-effectus (217II) is formalized by the
  relation `IsDaggerOf f g` (via the standard form 212III, with the
  isomorphism packaged as an `Iso`), with `pureDagger` obtained by unique
  choice from `pureDagger_existsUnique`.  That fixes `f†` for the *chosen*
  `π_s` and `ζ_s`; that the value is independent of that choice — the
  actual content of 217I — is the separate
  `pureDagger_indep_of_choice`.
* 214II (`Hilb` is a †-category with the adjoint as †) is `HilbObj` and
  its `DaggerCat` instance below; Mathlib has no category of Hilbert
  spaces, so the objects are bundled here.
* Not separately formalized: the examples 215II/215VIa–VII
  (the concrete description of the dagger on `vN`), the Setting 219II with
  its internal lemmas 219III, 219V, 219VII, 219IX, 219X and 219XIII
  (proof infrastructure for 219XVI, represented here by the standalone
  219XI, 219XIV and 219XVI — 219XIV *is* formalized, as
  `pureDagger_compr_asrt_zeta`, in a form that avoids the Setting), the
  quantum-gate discussion 222I–222IV, the
  commutant computation 223III (`Inv ϱ = [0,1]_{ϱ(𝒜)□}`, which needs the
  commutant apparatus of thesis A), and 221IIIa (`CvNᵒᵖ` has no dilations;
  `CvNᵒᵖ` is not formalized).
-/
import Theses.B.Eff.DiamondAmp

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits

namespace Theses.B.Eff

universe u v

/-! ## †-categories (parsec 214) -/

/-- **214I** (`dagger-effectus`, eff.tex:5240, Definition): a **†-category**
is a category with an involutive identity-on-objects functor
`(–)† : C → Cᵒᵖ`: `(f ∘ g)† = g† ∘ f†`, `id† = id`, `f†† = f` (and
`X† = X`, built into the type here). -/
class DaggerCat (D : Type u) [Category.{v} D] where
  /-- The dagger `f†` of a morphism. -/
  dag : ∀ {X Y : D}, (X ⟶ Y) → (Y ⟶ X)
  dag_comp : ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z),
    dag (f ≫ g) = dag g ≫ dag f
  dag_id : ∀ X : D, dag (𝟙 X) = 𝟙 X
  dag_dag : ∀ {X Y : D} (f : X ⟶ Y), dag (dag f) = f

section DaggerCat

variable {D : Type u} [Category.{v} D] [DaggerCat D]

/-- **214I.1** (`dagger-effectus`, eff.tex:5260, Definition): an endomap of
a †-category is **†-self-adjoint** when `f† = f`. -/
def DaggerCat.SelfAdjoint {X : D} (f : X ⟶ X) : Prop := dag f = f

/-- **214I.2** (`dagger-effectus`, eff.tex:5264, Definition): an endomap is
**†-positive** when `f = g† ∘ g` for some map `g`. -/
def DaggerCat.IsPositive {X : D} (f : X ⟶ X) : Prop :=
  ∃ (Y : D) (g : X ⟶ Y), f = g ≫ dag g

/-- **214I.3** (`dagger-effectus`, eff.tex:5268, Definition): an isomorphism
`α` is **†-unitary** when `α⁻¹ = α†`. -/
def DaggerCat.Unitary {X Y : D} (α : X ≅ Y) : Prop := α.inv = dag α.hom

end DaggerCat

/-! ### `Hilb` is a †-category (214II) -/

section Hilb

/-- An object of **`Hilb`**, the category of complex Hilbert spaces
(**214II**, eff.tex:5274, Example).  Bundled, because Mathlib has no
category of Hilbert spaces. -/
structure HilbObj : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [nacg : NormedAddCommGroup carrier]
  [ips : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]

attribute [instance] HilbObj.nacg HilbObj.ips HilbObj.complete

/-- **214II**: `Hilb` — Hilbert spaces with **bounded linear maps**. -/
instance : Category.{u, u + 1} HilbObj where
  Hom X Y := X.carrier →L[ℂ] Y.carrier
  id X := ContinuousLinearMap.id ℂ X.carrier
  comp f g := g.comp f

@[simp] theorem hilb_comp {X Y Z : HilbObj} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = g.comp f := rfl

@[simp] theorem hilb_id (X : HilbObj) :
    𝟙 X = ContinuousLinearMap.id ℂ X.carrier := rfl

/-- **214II** (eff.tex:5274, Example): **`Hilb` is a †-category with the
familiar adjoint as †.**  The three laws are Mathlib's
`ContinuousLinearMap.adjoint_comp`, `adjoint_id` and `adjoint_adjoint`;
identity-on-objects is built into `DaggerCat.dag`, whose type already
returns a map `Y ⟶ X`. -/
noncomputable instance : DaggerCat HilbObj where
  dag {X Y} f := ContinuousLinearMap.adjoint (𝕜 := ℂ) f
  dag_comp {X Y Z} f g := ContinuousLinearMap.adjoint_comp (𝕜 := ℂ) g f
  dag_id X := ContinuousLinearMap.adjoint_id (𝕜 := ℂ)
  dag_dag {X Y} f := ContinuousLinearMap.adjoint_adjoint (𝕜 := ℂ) f

end Hilb

/-! ## †-effectuses (parsec 215) -/

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

section DaggerEffectus

variable (C) [AndThenEffectus C]

/-- The image `im f` of any map is sharp (it is an image; used throughout
parsecs 215–223). -/
theorem isSharp_imPred {X Y : C} (f : X ⟶ Y) : IsSharp (imPred f) :=
  ⟨_, _, isImage_imPred f⟩

/-- Comprehensions are pure (an immediate consequence of 197V.3 and 201II;
used to regard `π_s` as a morphism of `Pure C`). -/
theorem isPure_comprehension {W X : C} {p : Pred X} {π : W ⟶ X}
    (h : IsComprehension p π) : IsPure π :=
  ⟨W, 𝟙 W, π, 0, p, quotient_basics_3 _, h, (Category.id_comp _).symm⟩

/-- Isomorphisms are faithful: `im α = im id = 1` by 202V. -/
theorem faithfulMap_of_isIso {X Y : C} (θ : X ⟶ Y) [IsIso θ] : FaithfulMap θ := by
  have h := (im_ineq (𝟙 Y) θ).2 θ inferInstance
  rw [Category.comp_id, imPred_id] at h
  have h4 := isImage_imPred θ
  rwa [h] at h4

/-- **215I** (eff.tex:5282, Definition): a **†-effectus** is an &-effectus
`C` such that

1. `Pure C` is a †-category with `asrt_p† = asrt_p` and `f` ⋄-adjoint to
   `f†`;
2. every †-positive map has a unique †-positive square root; and
3. ⋄-positive maps are †-positive. -/
class DaggerEffectus where
  /-- The †-category structure on `Pure C` (215I.1). -/
  daggerCat : DaggerCat (PureCat C)
  dag_asrt : ∀ {X : C} (p : Pred X),
    daggerCat.dag (X := PureCat.of X) (Y := PureCat.of X)
      ⟨asrt p, (asrt_spec p).1.1⟩ = ⟨asrt p, (asrt_spec p).1.1⟩
  dag_diamond_adjoint : ∀ {X Y : PureCat C} (f : X ⟶ Y),
    DiamondAdjoint f.1 (daggerCat.dag f).1
  sqrt_existsUnique : ∀ {X : PureCat C} (f : X ⟶ X),
    @DaggerCat.IsPositive _ _ daggerCat _ f →
      ∃! g : X ⟶ X, @DaggerCat.IsPositive _ _ daggerCat _ g ∧ g ≫ g = f
  diamond_pos_dagger_pos : ∀ {X : C} (f : X ⟶ X) (hf : DiamondPositive f),
    @DaggerCat.IsPositive _ _ daggerCat (PureCat.of X) ⟨f, hf.1⟩

/-- **215III** (`dagger-theorem`, eff.tex:5310, Theorem) and **215V**
(eff.tex:5331): a **†'-effectus** is an &-effectus such that

1. every predicate has a unique square root (`q & q = p`);
2. `asrt²_{p & q} = asrt_p ∘ asrt²_q ∘ asrt_p`; and
3. quotients for sharp predicates are sharp maps. -/
class DaggerPrimeEffectus : Prop where
  sqrt_existsUnique : ∀ {X : C} (p : Pred X), ∃! q : Pred X, andThen q q = p
  asrt_sq : ∀ {X : C} (p q : Pred X),
    asrt (andThen p q) ≫ asrt (andThen p q) =
      asrt p ≫ asrt q ≫ asrt q ≫ asrt p
  quot_sharp : ∀ {X W : C} {s : Pred X} (_ : IsSharp s) {ξ : X ⟶ W},
    IsQuotient s ξ → SharpMap ξ

-- **215III** (`dagger-theorem`, eff.tex:5310, Theorem), `dagger_theorem`:
-- an &-effectus is a †-effectus iff it is a †'-effectus.  It is stated and
-- proved after 220II (`dagger_thm_sufficiency`), which is one of its two
-- halves; the other is 216XI (`dagger_thm_necessity`).

-- **215VI** (`vn-is-dagger-category`, eff.tex:5338, Corollary),
-- `vn_is_dagger_category`: the &-effectus `vNᵒᵖ` is a †-effectus.  Moved to
-- `Theses/B/Eff/VNExamples.lean` (author ruling 2026-08-17): it needs
-- thesis A's von Neumann theory, and this file must keep importing only
-- `Theses.Common`.

end DaggerEffectus

/-! ## Consequences of the †-effectus axioms (parsec 216) -/

section DaggerConsequences

variable [AndThenEffectus C] {X Y : C}

/-- **216I** (`diamond-is-dagger-positive`, eff.tex:5423, Lemma): in a
†-effectus, a (pure endo)map is †-positive iff it is ⋄-positive. -/
theorem diamond_is_dagger_positive (d : DaggerEffectus C) (f : X ⟶ X)
    (hf : IsPure f) :
    @DaggerCat.IsPositive _ _ d.daggerCat (PureCat.of X) ⟨f, hf⟩ ↔
      DiamondPositive f := by
  constructor
  · intro hpos
    -- axiom 2: `f = g ∘ g` for a (unique) †-positive `g`
    obtain ⟨g, ⟨hgpos, hgg⟩, -⟩ := d.sqrt_existsUnique _ hpos
    -- `g = k† ∘ k` is ⋄-self-adjoint, since `k` is ⋄-adjoint to `k†`
    obtain ⟨W, k, hk⟩ := hgpos
    have h1 : DiamondAdjoint k.1 (d.daggerCat.dag k).1 := d.dag_diamond_adjoint k
    have h2 : DiamondAdjoint (d.daggerCat.dag k).1 k.1 := by
      have h := d.dag_diamond_adjoint (d.daggerCat.dag k)
      rwa [d.daggerCat.dag_dag] at h
    have hsa : DiamondSelfAdjoint g.1 := by
      have hg1 : g.1 = k.1 ≫ (d.daggerCat.dag k).1 := congrArg Subtype.val hk
      show diaPull g.1 = diaPush g.1
      rw [hg1]
      funext t
      rw [diaPull_comp, diaPush_comp, h1, h2]
    exact ⟨hf, g.1, hsa, (congrArg Subtype.val hgg).symm⟩
  · intro hdp
    exact d.diamond_pos_dagger_pos f hdp

/-- **216III** (`dagger-eff-square-root`, eff.tex:5447, Lemma): in a
†-effectus every predicate has a unique square root: a unique `q` with
`q & q = p`. -/
theorem dagger_eff_square_root (d : DaggerEffectus C) (p : Pred X) :
    ∃! q : Pred X, andThen q q = p := by
  -- `asrt_p` is ⋄-positive, hence †-positive (axiom 3); take its †-positive
  -- square root `f` (axiom 2)
  have hdp : DiamondPositive (asrt p) := (asrt_spec p).1
  obtain ⟨f, ⟨hfpos, hff⟩, hu⟩ :=
    d.sqrt_existsUnique (X := PureCat.of X) ⟨asrt p, hdp.1⟩
      (d.diamond_pos_dagger_pos (asrt p) hdp)
  have hfdp : DiamondPositive f.1 := (diamond_is_dagger_positive d f.1 f.2).mp hfpos
  -- so `f = asrt_{1∘f}`, and `q = 1 ∘ f` is a square root of `p`
  have hfq : f.1 = asrt (f.1 ≫ truth X) := asrt_unique _ _ hfdp rfl
  have hff' : f.1 ≫ f.1 = asrt p := congrArg Subtype.val hff
  refine ⟨f.1 ≫ truth X, ?_, ?_⟩
  · show asrt (f.1 ≫ truth X) ≫ (f.1 ≫ truth X) = p
    rw [← hfq, ← Category.assoc, hff', (asrt_spec p).2]
  · intro r hr
    -- `asrt_r ∘ asrt_r = asrt_{r & r} = asrt_p` and `asrt_r` is †-positive
    have heq : (⟨asrt r, (asrt_spec r).1.1⟩ :
        (PureCat.of X : PureCat C) ⟶ PureCat.of X) = f :=
      hu _ ⟨d.diamond_pos_dagger_pos (asrt r) (asrt_spec r).1,
        Subtype.ext (show asrt r ≫ asrt r = asrt p by
          rw [andthen_square_rule, hr])⟩
    rw [← congrArg Subtype.val heq]
    exact ((asrt_spec r).2).symm

/-- **216V** (`asrt-iso`, eff.tex:5490, Proposition): in an &-effectus with
square roots (e.g. a †- or †'-effectus), `asrt_p ∘ α = α ∘ asrt_{p ∘ α}`
for every isomorphism `α` and predicate `p`. -/
theorem asrt_iso (hsqrt : ∀ {Z : C} (p : Pred Z), ∃ q, andThen q q = p)
    (α : X ⟶ Y) [IsIso α] (p : Pred Y) :
    α ≫ asrt p = asrt (α ≫ p) ≫ α := by
  obtain ⟨q, hq⟩ := hsqrt p
  -- `α⁻¹ ∘ asrt_q ∘ α` is ⋄-self-adjoint by 209IV
  have hA : diaPull α = diaPush (inv α) := (iso_diamond_adjoint_2 α).2.2
  have hB : diaPull (inv α) = diaPush α := by
    have h := (iso_diamond_adjoint_2 (inv α)).2.2
    rwa [IsIso.inv_inv] at h
  have hqsa : diaPull (asrt q) = diaPush (asrt q) :=
    diamond_squares_2 (asrt_spec q).1
  have hsa : DiamondSelfAdjoint (α ≫ asrt q ≫ inv α) := by
    show diaPull _ = diaPush _
    funext t
    rw [diaPull_comp, diaPull_comp, diaPush_comp, diaPush_comp, hA, hqsa, hB]
  have hpure : IsPure (α ≫ asrt q ≫ inv α) :=
    upm_closed_pure (isPure_of_isQuotient (quotient_basics_3 α))
      (upm_closed_pure (asrt_spec q).1.1
        (isPure_of_isQuotient (quotient_basics_3 (inv α))))
  have hff : (α ≫ asrt q ≫ inv α) ≫ (α ≫ asrt q ≫ inv α) =
      α ≫ asrt p ≫ inv α := by
    simp only [Category.assoc]
    rw [← Category.assoc (inv α) α (asrt q ≫ inv α), IsIso.inv_hom_id,
      Category.id_comp, ← Category.assoc (asrt q) (asrt q) (inv α),
      andthen_square_rule, hq]
  have hpos : DiamondPositive (α ≫ asrt p ≫ inv α) := by
    refine ⟨?_, _, hsa, hff.symm⟩
    rw [← hff]; exact upm_closed_pure hpure hpure
  have htruth : (α ≫ asrt p ≫ inv α) ≫ truth X = α ≫ p := by
    simp only [Category.assoc]
    rw [iso_isTotal (inv α), (asrt_spec p).2]
  have key : α ≫ asrt p ≫ inv α = asrt (α ≫ p) :=
    asrt_unique _ _ hpos htruth
  calc α ≫ asrt p = (α ≫ asrt p ≫ inv α) ≫ α := by
        simp only [Category.assoc]; rw [IsIso.inv_hom_id, Category.comp_id]
    _ = asrt (α ≫ p) ≫ α := by rw [key]

/-- **216VII** (`dagger-of-zeta`, eff.tex:5520, Proposition): in a
†-effectus `ζ_s† = π_s` (for the corresponding pair of 211IX). -/
theorem dagger_of_zeta (d : DaggerEffectus C) {s : Pred X} (hs : IsSharp s) :
    d.daggerCat.dag (X := PureCat.of X) (Y := PureCat.of (comprObj s))
        ⟨zetaMap s hs, isPure_of_isQuotient (zetaMap_spec s hs).1⟩ =
      ⟨comprMap s, isPure_comprehension C (isComprehension_comprMap s)⟩ := by
  -- work with abstract names `Zm`, `Pim` for `ζ_s` and `π_s` as maps of `Pure C`
  have main : ∀ (Zm : (PureCat.of X : PureCat C) ⟶ PureCat.of (comprObj s))
      (Pim : (PureCat.of (comprObj s) : PureCat C) ⟶ PureCat.of X),
      Zm.1 = zetaMap s hs → Pim.1 = comprMap s → d.daggerCat.dag Zm = Pim := by
    intro Zm Pim hZm hPim
    obtain ⟨hζq, hπζ, hζπ⟩ := zetaMap_spec s hs
    -- `1 ∘ ζ_s = s`
    have hζtruth : zetaMap s hs ≫ truth (comprObj s) = s := by
      rw [quotient_basics_5 hζq, eabasics_orth_orth]
    -- `IM ζ_s† = ⌈1 ∘ ζ_s⌉ = s`, so `ζ_s† = π_s ∘ g` for a unique `g`
    have hadjZ : DiamondAdjoint (d.daggerCat.dag Zm).1 Zm.1 := by
      have h := d.dag_diamond_adjoint (d.daggerCat.dag Zm)
      rwa [d.daggerCat.dag_dag] at h
    have himZ : imPred (d.daggerCat.dag Zm).1 = s := by
      have h := exc_diamond_adj_2 hadjZ
      rwa [hZm, hζtruth, ceil_of_isSharp hs] at h
    obtain ⟨g, hg, -⟩ := (isComprehension_comprMap s).2 (d.daggerCat.dag Zm).1
      (by
        have him := (isImage_imPred (d.daggerCat.dag Zm).1).1
        rwa [himZ] at him)
    -- `⌈1 ∘ π_s†⌉ = IM π_s = s`, so `π_s† = h' ∘ ζ_s` by the quotient property
    have hceilPi : ceilPred ((d.daggerCat.dag Pim).1 ≫ truth (comprObj s)) = s := by
      have h := exc_diamond_adj_2 (d.dag_diamond_adjoint Pim)
      rw [hPim, (img_of_compr s).2 s hs] at h
      exact h.symm
    obtain ⟨h', hh', -⟩ := hζq.2 (d.daggerCat.dag Pim).1 (by
      rw [eabasics_orth_orth]
      have hle := le_ceil ((d.daggerCat.dag Pim).1 ≫ truth (comprObj s))
      rwa [hceilPi] at hle)
    -- `id = id† = (ζ_s ∘ π_s)† = π_s† ∘ ζ_s†`, i.e. `g ∘ h' = id`
    have hdagid : d.daggerCat.dag Zm ≫ d.daggerCat.dag Pim = 𝟙 _ := by
      rw [← d.daggerCat.dag_comp,
        show Pim ≫ Zm = 𝟙 (PureCat.of (comprObj s)) from
          Subtype.ext (by
            show Pim.1 ≫ Zm.1 = 𝟙 (comprObj s)
            rw [hPim, hZm, hπζ]),
        d.daggerCat.dag_id]
    have hgh : g ≫ h' = 𝟙 (comprObj s) := by
      have e : (d.daggerCat.dag Zm).1 ≫ (d.daggerCat.dag Pim).1 = 𝟙 (comprObj s) :=
        congrArg Subtype.val hdagid
      rw [← hg, ← hh'] at e
      simp only [Category.assoc] at e
      rwa [← Category.assoc (comprMap s) (zetaMap s hs) h', hπζ,
        Category.id_comp] at e
    -- `1 = 1 ∘ h' ∘ g ≤ 1 ∘ g`, so `g` is total
    have hgtot : IsTotal g := by
      have h2 := comp_le_comp g (pred_le_truth (h' ≫ truth (comprObj s)))
      rw [← Category.assoc, hgh, Category.id_comp] at h2
      exact eabasics_le_antisymm (pred_le_truth _) h2
    -- `ζ_s† ∘ ζ_s` is †-positive, hence ⋄-positive, with `1 ∘ (–) = s`
    have hpos : DiamondPositive (Zm.1 ≫ (d.daggerCat.dag Zm).1) :=
      (diamond_is_dagger_positive d _ (Zm ≫ d.daggerCat.dag Zm).2).mp
        ⟨_, Zm, rfl⟩
    have htruthzz : (Zm.1 ≫ (d.daggerCat.dag Zm).1) ≫ truth X = s := by
      rw [hZm, ← hg]
      simp only [Category.assoc]
      rw [compr_total (isComprehension_comprMap s), hgtot]
      exact hζtruth
    have hasrt : Zm.1 ≫ (d.daggerCat.dag Zm).1 = asrt s :=
      asrt_unique s _ hpos htruthzz
    -- `ζ_s† ∘ ζ_s = asrt_s = π_s ∘ ζ_s`, and `ζ_s` is epic
    haveI : Epi (zetaMap s hs) := quotient_basics_6 hζq
    refine Subtype.ext ?_
    rw [hPim]
    refine (cancel_epi (zetaMap s hs)).mp ?_
    rw [hζπ, ← hZm]
    exact hasrt
  exact main _ _ rfl rfl

/-- **216VII** (`dagger-of-zeta`, eff.tex:5520, Proposition), dually: in a
†-effectus `π_s† = ζ_s††† = ζ_s`. -/
theorem dagger_of_compr (d : DaggerEffectus C) {s : Pred X} (hs : IsSharp s) :
    d.daggerCat.dag (X := PureCat.of (comprObj s)) (Y := PureCat.of X)
        ⟨comprMap s, isPure_comprehension C (isComprehension_comprMap s)⟩ =
      ⟨zetaMap s hs, isPure_of_isQuotient (zetaMap_spec s hs).1⟩ := by
  rw [← dagger_of_zeta d hs, d.daggerCat.dag_dag]

/-- **216IX** (`dagger-of-iso`, eff.tex:5558, Corollary), first half: in a
†-effectus `π_s` is ⋄-adjoint to `ζ_s`. -/
theorem dagger_of_iso_adjoint (d : DaggerEffectus C) {s : Pred X}
    (hs : IsSharp s) : DiamondAdjoint (comprMap s) (zetaMap s hs) := by
  -- `π_s† = ζ_s†† = ζ_s` by 216VII, and `π_s` is ⋄-adjoint to `π_s†`
  have h := d.dag_diamond_adjoint (X := PureCat.of (comprObj s)) (Y := PureCat.of X)
    ⟨comprMap s, isPure_comprehension C (isComprehension_comprMap s)⟩
  rw [dagger_of_compr d hs] at h
  exact h

/-- **216IX** (`dagger-of-iso`, eff.tex:5558, Corollary), second half: in a
†-effectus `α† = α⁻¹` for every isomorphism `α` of `Pure C`. -/
theorem dagger_of_iso (d : DaggerEffectus C) {P Q : PureCat C} (α : P ≅ Q) :
    d.daggerCat.dag α.hom = α.inv := by
  -- `α†` is again an isomorphism (with inverse `(α⁻¹)†`), hence total
  have h1 : d.daggerCat.dag α.inv ≫ d.daggerCat.dag α.hom = 𝟙 P := by
    rw [← d.daggerCat.dag_comp, α.hom_inv_id, d.daggerCat.dag_id]
  have h2 : d.daggerCat.dag α.hom ≫ d.daggerCat.dag α.inv = 𝟙 Q := by
    rw [← d.daggerCat.dag_comp, α.inv_hom_id, d.daggerCat.dag_id]
  haveI : IsIso (d.daggerCat.dag α.hom).1 :=
    ⟨(d.daggerCat.dag α.inv).1, congrArg Subtype.val h2, congrArg Subtype.val h1⟩
  haveI : IsIso α.hom.1 :=
    ⟨α.inv.1, congrArg Subtype.val α.hom_inv_id, congrArg Subtype.val α.inv_hom_id⟩
  -- `α† ∘ α` is †-positive, hence ⋄-positive, and total, so it is the identity
  have hpos : DiamondPositive ((d.daggerCat.dag α.hom).1 ≫ α.hom.1) :=
    (diamond_is_dagger_positive d _ (d.daggerCat.dag α.hom ≫ α.hom).2).mp
      ⟨_, d.daggerCat.dag α.hom, by rw [d.daggerCat.dag_dag]; rfl⟩
  have htruth : ((d.daggerCat.dag α.hom).1 ≫ α.hom.1) ≫ truth Q.base =
      truth Q.base := by
    rw [Category.assoc, show α.hom.1 ≫ truth Q.base = truth P.base from
      iso_isTotal α.hom.1]
    exact iso_isTotal (d.daggerCat.dag α.hom).1
  have key : d.daggerCat.dag α.hom ≫ α.hom = 𝟙 Q :=
    Subtype.ext ((asrt_unique (truth Q.base) _ hpos htruth).trans
      (asrt_unique (truth Q.base) (𝟙 Q.base) (diamondPositive_id _)
        (Category.id_comp _)).symm)
  calc d.daggerCat.dag α.hom = d.daggerCat.dag α.hom ≫ α.hom ≫ α.inv := by
        rw [α.hom_inv_id, Category.comp_id]
    _ = α.inv := by rw [← Category.assoc, key, Category.id_comp]

/-- **216X** (`zeta-through-asrt`, eff.tex:5564, Exercise): in an
&-effectus with square roots where `π_s` is ⋄-adjoint to `ζ_s` (e.g. a
†-effectus), `asrt_p ∘ ζ_s = ζ_s ∘ asrt_{p ∘ ζ_s}`. -/
theorem zeta_through_asrt
    (hsqrt : ∀ {Z : C} (p : Pred Z), ∃ q, andThen q q = p)
    {s : Pred X} (hs : IsSharp s)
    (hadj : DiamondAdjoint (comprMap s) (zetaMap s hs))
    (p : Pred (comprObj s)) :
    zetaMap s hs ≫ asrt p = asrt (zetaMap s hs ≫ p) ≫ zetaMap s hs := by
  obtain ⟨q, hq⟩ := hsqrt p
  obtain ⟨-, hπζ, hζπ⟩ := zetaMap_spec s hs
  -- `f = π_s ∘ asrt_q ∘ ζ_s` is pure and ⋄-self-adjoint
  have hfpure : IsPure (zetaMap s hs ≫ asrt q ≫ comprMap s) :=
    upm_closed_pure (isPure_of_isQuotient (zetaMap_spec s hs).1)
      (upm_closed_pure (asrt_spec q).1.1
        (isPure_comprehension C (isComprehension_comprMap s)))
  have hadj' : diaPush (comprMap s) = diaPull (zetaMap s hs) :=
    (exc_diamond_adj_1 _ _).mp hadj
  have hqsa : diaPull (asrt q) = diaPush (asrt q) :=
    diamond_squares_2 (asrt_spec q).1
  have hsa : DiamondSelfAdjoint (zetaMap s hs ≫ asrt q ≫ comprMap s) := by
    show diaPull _ = diaPush _
    funext t
    rw [diaPull_comp, diaPull_comp, diaPush_comp, diaPush_comp, hadj, hqsa,
      ← hadj']
  -- `f ∘ f = π_s ∘ asrt_{q & q} ∘ ζ_s = π_s ∘ asrt_p ∘ ζ_s`
  have hff : (zetaMap s hs ≫ asrt q ≫ comprMap s) ≫
      (zetaMap s hs ≫ asrt q ≫ comprMap s) =
      zetaMap s hs ≫ asrt p ≫ comprMap s := by
    simp only [Category.assoc]
    rw [← Category.assoc (comprMap s) (zetaMap s hs) (asrt q ≫ comprMap s),
      hπζ, Category.id_comp,
      ← Category.assoc (asrt q) (asrt q) (comprMap s), andthen_square_rule, hq]
  -- hence `π_s ∘ asrt_p ∘ ζ_s` is ⋄-positive, with `1 ∘ – = p ∘ ζ_s`
  have hpos : DiamondPositive (zetaMap s hs ≫ asrt p ≫ comprMap s) := by
    refine ⟨?_, _, hsa, hff.symm⟩
    rw [← hff]; exact upm_closed_pure hfpure hfpure
  have htruth : (zetaMap s hs ≫ asrt p ≫ comprMap s) ≫ truth X =
      zetaMap s hs ≫ p := by
    simp only [Category.assoc]
    rw [compr_total (isComprehension_comprMap s), (asrt_spec p).2]
  have key : zetaMap s hs ≫ asrt p ≫ comprMap s = asrt (zetaMap s hs ≫ p) :=
    asrt_unique _ _ hpos htruth
  calc zetaMap s hs ≫ asrt p
      = (zetaMap s hs ≫ asrt p ≫ comprMap s) ≫ zetaMap s hs := by
        simp only [Category.assoc]; rw [hπζ, Category.comp_id]
    _ = asrt (zetaMap s hs ≫ p) ≫ zetaMap s hs := by rw [key]

/-- Helper: the standard form of 212III for a pure map, stated for
*representatives* `c`, `i` of `⌈1 ∘ f⌉` and `im f` (the analogue of
`isDaggerOf_of_eq`, which it avoids transporting along). -/
theorem standard_form_of_eq {f : X ⟶ Y} (hf : IsPure f) {c : Pred X}
    {i : Pred Y} (hcs : IsSharp c) (his : IsSharp i)
    (hc : ceilPred (f ≫ truth Y) = c) (hi : imPred f = i) :
    ∃ β : comprObj c ≅ comprObj i,
      f = asrt (f ≫ truth Y) ≫ zetaMap c hcs ≫ β.hom ≫ comprMap i := by
  subst hc; subst hi
  obtain ⟨g, ⟨-, hg⟩, -⟩ := standard_form_map f
  haveI : IsIso g := standard_form_map_pure hf g hg
  exact ⟨asIso g, hg⟩

/-- **216XIII** (`pqqp-from-dagger`, eff.tex:5578, Ax. 2): in an &-effectus
`asrt_q ∘ asrt_p = π_{⌈q&p⌉} ∘ α ∘ ζ_{⌈p&q⌉} ∘ asrt_{p&q}` for some
isomorphism `α`; indeed `1 ∘ asrt_q ∘ asrt_p = p & q` and
`im (asrt_q ∘ asrt_p) = ⌈q & p⌉`, as `asrt_q ∘ asrt_p` and
`asrt_p ∘ asrt_q` are ⋄-adjoint. -/
theorem asrt_comp_standard_form (p q : Pred X) :
    ∃ α : comprObj (ceilPred (andThen p q)) ≅ comprObj (ceilPred (andThen q p)),
      asrt p ≫ asrt q =
        asrt (andThen p q) ≫
          zetaMap (ceilPred (andThen p q)) (isSharp_ceil _) ≫ α.hom ≫
          comprMap (ceilPred (andThen q p)) := by
  have hpsa : diaPull (asrt p) = diaPush (asrt p) :=
    diamond_squares_2 (asrt_spec p).1
  have hqsa : diaPull (asrt q) = diaPush (asrt q) :=
    diamond_squares_2 (asrt_spec q).1
  have h1 : (asrt p ≫ asrt q) ≫ truth X = andThen p q := by
    rw [Category.assoc, (asrt_spec q).2]; rfl
  -- `asrt_q ∘ asrt_p` is ⋄-adjoint to `asrt_p ∘ asrt_q`
  have hadj : DiamondAdjoint (asrt p ≫ asrt q) (asrt q ≫ asrt p) := by
    show diaPull _ = diaPush _
    funext s
    rw [diaPull_comp, diaPush_comp, hpsa, hqsa]
  have h2 : imPred (asrt p ≫ asrt q) = ceilPred (andThen q p) := by
    have h := exc_diamond_adj_2 hadj
    rwa [Category.assoc, (asrt_spec p).2] at h
  obtain ⟨β, hβ⟩ := standard_form_of_eq
    (upm_closed_pure (asrt_spec p).1.1 (asrt_spec q).1.1)
    (isSharp_ceil _) (isSharp_ceil _) (by rw [h1]) h2
  rw [h1] at hβ
  exact ⟨β, hβ⟩

/-- **216XIV** (`dagger-thm-necessity`, eff.tex:5630, Ax. 3): in a †-effectus
`t ∘ ζ_s` is sharp for sharp `s` and `t`.

The proof is eff.tex:5630's own, which shows that `t ∘ ζ_s` **is** the image
of `π_s ∘ π_t` — hence sharp.  (a) `t ∘ ζ_s ∘ π_s ∘ π_t = 1 ∘ π_s ∘ π_t`.
(b) For sharp `p` with `p ∘ π_s ∘ π_t = 1 ∘ π_s ∘ π_t`: `p ∘ π_s ≥ IM π_t = t`,
so `pᵖ ∘ π_s ≤ tᵖ` and `⌈pᵖ ∘ π_s⌉ ≤ tᵖ`; as `π_s` is ⋄-adjoint to `ζ_s`
(216IX.1 `dagger_of_iso_adjoint`), `⌈pᵖ ∘ π_s⌉ = im (ζ_s ∘ π_{pᵖ})`, so
`ζ_s ∘ π_{pᵖ}` kills `t` and therefore `t ∘ ζ_s ≤ ⌈t ∘ ζ_s⌉ ≤ p`.  Clause (b)
at the sharp predicate `im (π_s ∘ π_t)` is the half that needs (b) at all. -/
theorem sharpMap_zetaMap (d : DaggerEffectus C) {s : Pred X} (hs : IsSharp s) :
    SharpMap (zetaMap s hs) := by
  intro t ht
  obtain ⟨-, hπζ, -⟩ := zetaMap_spec s hs
  have hπtot : IsTotal (comprMap s) := compr_total (isComprehension_comprMap s)
  -- 216IX.1: `π_s` is ⋄-adjoint to `ζ_s`
  have hadj : DiamondAdjoint (comprMap s) (zetaMap s hs) :=
    dagger_of_iso_adjoint d hs
  -- (a) `t ∘ ζ_s ∘ π_s ∘ π_t = 1 ∘ π_s ∘ π_t`
  have ha : (comprMap t ≫ comprMap s) ≫ zetaMap s hs ≫ t
      = (comprMap t ≫ comprMap s) ≫ truth X := by
    calc (comprMap t ≫ comprMap s) ≫ zetaMap s hs ≫ t
        = comprMap t ≫ t := by
          rw [Category.assoc, ← Category.assoc (comprMap s) (zetaMap s hs) t,
            hπζ, Category.id_comp]
      _ = comprMap t ≫ truth (comprObj s) := (isComprehension_comprMap t).1
      _ = (comprMap t ≫ comprMap s) ≫ truth X := by
          rw [Category.assoc, hπtot]
  -- (b) every sharp `p` with `p ∘ π_s ∘ π_t = 1 ∘ π_s ∘ π_t` has `t ∘ ζ_s ≤ p`
  have hb : ∀ p : Pred X, IsSharp p →
      (comprMap t ≫ comprMap s) ≫ p = (comprMap t ≫ comprMap s) ≫ truth X →
      zetaMap s hs ≫ t ≼ p := by
    intro p hp hp1
    -- `p ∘ π_s ≥ IM π_t = t`
    have h1 : comprMap t ≫ comprMap s ≫ p
        = comprMap t ≫ truth (comprObj s) := by
      rw [← Category.assoc, hp1, Category.assoc, hπtot]
    have h2 : t ≼ comprMap s ≫ p := by
      have h := (isImage_imPred (comprMap t)).2 _ h1
      rwa [(img_of_compr t).2 t ht] at h
    -- so `pᵖ ∘ π_s ≤ tᵖ`, and `⌈pᵖ ∘ π_s⌉ ≤ tᵖ` as `tᵖ` is sharp
    have h3 : comprMap s ≫ orth p ≼ orth t := by
      rw [total_comp_orth hπtot]
      exact eabasics_le_iff_orth_le.mp h2
    have h4 : ceilPred (comprMap s ≫ orth p) ≼ orth t :=
      (ceil_le_iff_of_isSharp (DiamondEffectus.orth_sharp ht)).mpr h3
    -- 216IX.1 at `pᵖ`: `⌈pᵖ ∘ π_s⌉ = im (ζ_s ∘ π_{pᵖ})`
    have h5 : ceilPred (comprMap s ≫ orth p)
        = imPred (comprMap (orth p) ≫ zetaMap s hs) :=
      congrArg Subtype.val
        (congrFun hadj ⟨orth p, DiamondEffectus.orth_sharp hp⟩)
    -- hence `t ∘ ζ_s ∘ π_{pᵖ} = 0`, i.e. `t ∘ ζ_s ≤ ⌈t ∘ ζ_s⌉ ≤ p`
    have h6 : comprMap (orth p) ≫ zetaMap s hs ≫ t = 0 := by
      rw [← Category.assoc]
      exact (im_le_orth_iff _ t).mp (by rw [← h5]; exact h4)
    exact (le_iff_compr_orth_comp_eq_zero hp _).mpr h6
  -- so `t ∘ ζ_s` is the image of `π_s ∘ π_t`, and images are sharp
  have heq : zetaMap s hs ≫ t = imPred (comprMap t ≫ comprMap s) :=
    eabasics_le_antisymm
      (hb _ (isSharp_imPred C _) (isImage_imPred (comprMap t ≫ comprMap s)).1)
      ((isImage_imPred (comprMap t ≫ comprMap s)).2 _ ha)
  rw [heq]
  exact isSharp_imPred C _

/-- **216XI** (`dagger-thm-necessity`, eff.tex:5573, Theorem): a †-effectus
is a †'-effectus. -/
theorem dagger_thm_necessity (d : DaggerEffectus C) :
    DaggerPrimeEffectus C := by
  refine ⟨?_, ?_, ?_⟩
  · -- Ax. 1 is 216III
    intro Z p
    exact dagger_eff_square_root d p
  · -- Ax. 2 (`pqqp-from-dagger`): apply the dagger to the standard form of
    -- `asrt_q ∘ asrt_p`, and combine the two forms
    intro Z p q
    obtain ⟨α, hα⟩ := asrt_comp_standard_form p q
    have hAl : d.daggerCat.dag
        (X := PureCat.of (comprObj (ceilPred (andThen p q))))
        (Y := PureCat.of (comprObj (ceilPred (andThen q p))))
        ⟨α.hom, isPure_of_isQuotient (quotient_basics_3 α.hom)⟩ =
        ⟨α.inv, isPure_of_isQuotient (quotient_basics_3 α.inv)⟩ := by
      have h := dagger_of_iso d
        (P := PureCat.of (comprObj (ceilPred (andThen p q))))
        (Q := PureCat.of (comprObj (ceilPred (andThen q p))))
        ⟨⟨α.hom, isPure_of_isQuotient (quotient_basics_3 α.hom)⟩,
          ⟨α.inv, isPure_of_isQuotient (quotient_basics_3 α.inv)⟩,
          Subtype.ext α.hom_inv_id, Subtype.ext α.inv_hom_id⟩
      exact h
    have hα2 : asrt q ≫ asrt p =
        ((zetaMap (ceilPred (andThen q p)) (isSharp_ceil _) ≫ α.inv) ≫
          comprMap (ceilPred (andThen p q))) ≫ asrt (andThen p q) := by
      -- name the five factors as maps of `Pure C`
      obtain ⟨Ap, hAp⟩ : ∃ f : (PureCat.of Z : PureCat C) ⟶ PureCat.of Z,
        f = ⟨asrt p, (asrt_spec p).1.1⟩ := ⟨_, rfl⟩
      obtain ⟨Aq, hAq⟩ : ∃ f : (PureCat.of Z : PureCat C) ⟶ PureCat.of Z,
        f = ⟨asrt q, (asrt_spec q).1.1⟩ := ⟨_, rfl⟩
      obtain ⟨A, hA⟩ : ∃ f : (PureCat.of Z : PureCat C) ⟶ PureCat.of Z,
        f = ⟨asrt (andThen p q), (asrt_spec (andThen p q)).1.1⟩ := ⟨_, rfl⟩
      obtain ⟨Zc, hZc⟩ : ∃ f : (PureCat.of Z : PureCat C) ⟶
          PureCat.of (comprObj (ceilPred (andThen p q))),
        f = ⟨zetaMap (ceilPred (andThen p q)) (isSharp_ceil _),
          isPure_of_isQuotient
            (zetaMap_spec (ceilPred (andThen p q)) (isSharp_ceil _)).1⟩ :=
        ⟨_, rfl⟩
      obtain ⟨Al, hAlv⟩ : ∃ f : (PureCat.of (comprObj (ceilPred (andThen p q))) :
          PureCat C) ⟶ PureCat.of (comprObj (ceilPred (andThen q p))),
        f = ⟨α.hom, isPure_of_isQuotient (quotient_basics_3 α.hom)⟩ := ⟨_, rfl⟩
      obtain ⟨Pe, hPe⟩ : ∃ f : (PureCat.of (comprObj (ceilPred (andThen q p))) :
          PureCat C) ⟶ PureCat.of Z,
        f = ⟨comprMap (ceilPred (andThen q p)),
          isPure_comprehension C (isComprehension_comprMap _)⟩ := ⟨_, rfl⟩
      have hE : Ap ≫ Aq = A ≫ Zc ≫ Al ≫ Pe := by
        refine Subtype.ext ?_
        rw [hAp, hAq, hA, hZc, hAlv, hPe]
        exact hα
      have hdAp : d.daggerCat.dag Ap = Ap := by rw [hAp]; exact d.dag_asrt p
      have hdAq : d.daggerCat.dag Aq = Aq := by rw [hAq]; exact d.dag_asrt q
      have hdA : d.daggerCat.dag A = A := by
        rw [hA]; exact d.dag_asrt (andThen p q)
      have hdZc : d.daggerCat.dag Zc =
          ⟨comprMap (ceilPred (andThen p q)),
            isPure_comprehension C (isComprehension_comprMap _)⟩ := by
        rw [hZc]; exact dagger_of_zeta d (isSharp_ceil (andThen p q))
      have hdAl : d.daggerCat.dag Al =
          ⟨α.inv, isPure_of_isQuotient (quotient_basics_3 α.inv)⟩ := by
        rw [hAlv]; exact hAl
      have hdPe : d.daggerCat.dag Pe =
          ⟨zetaMap (ceilPred (andThen q p)) (isSharp_ceil _),
            isPure_of_isQuotient
              (zetaMap_spec (ceilPred (andThen q p)) (isSharp_ceil _)).1⟩ := by
        rw [hPe]; exact dagger_of_compr d (isSharp_ceil (andThen q p))
      have hD := congrArg d.daggerCat.dag hE
      rw [d.daggerCat.dag_comp, d.daggerCat.dag_comp, d.daggerCat.dag_comp,
        d.daggerCat.dag_comp, hdAp, hdAq, hdA, hdZc, hdAl, hdPe] at hD
      have hfin := congrArg Subtype.val hD
      rw [hAp, hAq, hA] at hfin
      exact hfin
    have habs : asrt (andThen p q) ≫ asrt (ceilPred (andThen p q)) =
        asrt (andThen p q) :=
      (asrt_absorp_rule (asrt (andThen p q)) (isSharp_ceil (andThen p q))
        (isSharp_one Z)).1.mp (by rw [imPred_asrt]; exact pcm_preorder_refl _)
    rw [← Category.assoc, hα, hα2]
    simp only [Category.assoc]
    rw [← Category.assoc (comprMap (ceilPred (andThen q p)))
        (zetaMap (ceilPred (andThen q p)) (isSharp_ceil _)) _,
      (zetaMap_spec (ceilPred (andThen q p)) (isSharp_ceil _)).2.1,
      Category.id_comp, ← Category.assoc α.hom α.inv _, α.hom_inv_id,
      Category.id_comp,
      ← Category.assoc (zetaMap (ceilPred (andThen p q)) (isSharp_ceil _))
        (comprMap (ceilPred (andThen p q))) _,
      (zetaMap_spec (ceilPred (andThen p q)) (isSharp_ceil _)).2.2,
      ← Category.assoc, habs]
  · -- Ax. 3: a quotient for a sharp `s` differs from `ζ_{sᵖ}` by an iso
    intro Z W s hs ξ hξ
    have hos : IsSharp (orth s) := DiamondEffectus.orth_sharp hs
    have hzq : IsQuotient s (zetaMap (orth s) hos) := by
      have h := (zetaMap_spec (orth s) hos).1
      rwa [eabasics_orth_orth] at h
    obtain ⟨θ, hθ, hθc, -⟩ := quotient_basics_2 hξ hzq
    haveI := hθ
    intro t ht
    have h1 : ξ ≫ t = zetaMap (orth s) hos ≫ (θ ≫ t) := by
      rw [← Category.assoc, hθc]
    rw [h1]
    exact sharpMap_zetaMap d hos (θ ≫ t) ⟨_, _, isImage_compr_comp_inv θ ht⟩

end DaggerConsequences

/-! ## The dagger of a pure map in a †'-effectus (parsec 217) -/

section PureDagger

variable [AndThenEffectus C] {X Y Z : C}

/-- **217II** (`dagger-definition2`, eff.tex:5721, Definition), as a
relation: `g` is *the* dagger of `f`,
`g = f† = asrt_{1∘f} ∘ π_{⌈1∘f⌉} ∘ α⁻¹ ∘ ζ_{im f}`, where `α` is the
unique isomorphism putting `f` in the standard form of 212III. -/
def IsDaggerOf (f : X ⟶ Y) (g : Y ⟶ X) : Prop :=
  ∃ α : comprObj (ceilPred (f ≫ truth Y)) ≅ comprObj (imPred f),
    f = asrt (f ≫ truth Y) ≫
        zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ α.hom ≫
        comprMap (imPred f) ∧
    g = zetaMap (imPred f) (isSharp_imPred C f) ≫ α.inv ≫
        comprMap (ceilPred (f ≫ truth Y)) ≫ asrt (f ≫ truth Y)

/-- **217II** (`dagger-definition2`, eff.tex:5721): in a †'-effectus every
pure map has a unique dagger in the sense of `IsDaggerOf`, so that
`pureDagger` below is well defined *for the chosen* `π_s` and `ζ_s`.  That
the value does not depend on that choice — the actual content of 217I — is
`pureDagger_indep_of_choice` below. -/
theorem pureDagger_existsUnique [DaggerPrimeEffectus C] (f : X ⟶ Y)
    (hf : IsPure f) : ∃! g : Y ⟶ X, IsDaggerOf f g := by
  obtain ⟨g₀, ⟨-, hg₀⟩, hu⟩ := standard_form_map f
  haveI hiso : IsIso g₀ := standard_form_map_pure hf g₀ hg₀
  refine ⟨zetaMap (imPred f) (isSharp_imPred C f) ≫ inv g₀ ≫
      comprMap (ceilPred (f ≫ truth Y)) ≫ asrt (f ≫ truth Y),
    ⟨asIso g₀, hg₀, rfl⟩, ?_⟩
  rintro g₁ ⟨α, hα, hgeq⟩
  -- `α.hom` also puts `f` in standard form, so `α.hom = g₀` by 212III
  have hαg : α.hom = g₀ :=
    hu α.hom ⟨⟨iso_isTotal α.hom, faithfulMap_of_isIso C α.hom⟩, hα⟩
  have hinv : α.inv = inv g₀ := by
    refine (cancel_mono g₀).mp ?_
    rw [IsIso.inv_hom_id, ← hαg, α.inv_hom_id]
  rw [hgeq, hinv]

/-- **217II** (`dagger-definition2`, eff.tex:5721, Definition): the dagger
`f†` of a pure map `f` in a †'-effectus. -/
noncomputable def pureDagger [DaggerPrimeEffectus C] (f : X ⟶ Y)
    (hf : IsPure f) : Y ⟶ X :=
  (pureDagger_existsUnique f hf).exists.choose

/-- The defining property of `pureDagger` (217II). -/
theorem isDaggerOf_pureDagger [DaggerPrimeEffectus C] (f : X ⟶ Y)
    (hf : IsPure f) : IsDaggerOf f (pureDagger f hf) :=
  (pureDagger_existsUnique f hf).exists.choose_spec

/-- **217I** (eff.tex:5653–5720, which carries no label of its own; the
Definition it justifies is **217II**, `dagger-definition2`, eff.tex:5721):
the formula
`f† = asrt_{1∘f} ∘ π_{⌈1∘f⌉} ∘ α⁻¹ ∘ ζ_{im f}` is **independent of the
choice** of comprehension `π'` for `im f` and quotient `ζ'` for
`⌈1∘f⌉ᵖ` — which is what justifies declaring it a definition.

Precisely, in the notation of 211IX: let `π' : W ⟶ Y` be *any* comprehension
for `im f` with corresponding quotient `ζπ'` (`π' ∘ ζπ' = id` and
`ζπ' ∘ π' = asrt_{im f}` — written here in diagrammatic order), let
`ζ' : X ⟶ V` be *any* quotient for `⌈1∘f⌉ᵖ` with corresponding
comprehension `πζ'`, and let `α' : V ≅ W` be an isomorphism with
`f = π' ∘ α' ∘ ζ' ∘ asrt_{1∘f}`.  Then
`asrt_{1∘f} ∘ πζ' ∘ α'⁻¹ ∘ ζπ' = f†`.

The proof is the thesis's β/γ computation: `π' = π_{im f} ∘ β` and
`ζ' = γ ∘ ζ_{⌈1∘f⌉}` for isomorphisms `β`, `γ` (197V.2/199VII.2), whence
`ζπ' = β⁻¹ ∘ ζ_{im f}` and `πζ' = π_{⌈1∘f⌉} ∘ γ⁻¹` (by monicity of `π'` and
epicity of `ζ'`), and `β ∘ α' ∘ γ` puts `f` in the standard form 212III, so
the `γ⁻¹ γ` and `β β⁻¹` of the thesis's display cancel. -/
theorem pureDagger_indep_of_choice [DaggerPrimeEffectus C] {f : X ⟶ Y}
    (hf : IsPure f) {V W : C}
    {π' : W ⟶ Y} (hπ' : IsComprehension (imPred f) π')
    {ζπ' : Y ⟶ W}
    (hcorrπ' : π' ≫ ζπ' = 𝟙 W ∧ ζπ' ≫ π' = asrt (imPred f))
    {ζ' : X ⟶ V} (hζ' : IsQuotient (orth (ceilPred (f ≫ truth Y))) ζ')
    {πζ' : V ⟶ X}
    (hcorrζ' : πζ' ≫ ζ' = 𝟙 V ∧
      ζ' ≫ πζ' = asrt (ceilPred (f ≫ truth Y)))
    (α' : V ≅ W)
    (hform : f = asrt (f ≫ truth Y) ≫ ζ' ≫ α'.hom ≫ π') :
    ζπ' ≫ α'.inv ≫ πζ' ≫ asrt (f ≫ truth Y) = pureDagger f hf := by
  obtain ⟨-, hπζim, hζπim⟩ := zetaMap_spec (imPred f) (isSharp_imPred C f)
  obtain ⟨hqζc, hπζc, hζπc⟩ :=
    zetaMap_spec (ceilPred (f ≫ truth Y)) (isSharp_ceil _)
  -- `β : W ≅ {Y | im f}` with `π' = β ∘ π_{im f}`
  obtain ⟨β, hβiso, hβ, -⟩ :=
    compr_basics_2 hπ' (isComprehension_comprMap (imPred f))
  haveI := hβiso
  -- `γ : {X | ⌈1∘f⌉} ≅ V` with `ζ' = ζ_{⌈1∘f⌉} ∘ γ`
  obtain ⟨γ, hγiso, hγ, -⟩ := quotient_basics_2 hζ' hqζc
  haveI := hγiso
  -- the corresponding quotient of `π'` is `ζ_{im f} ∘ β⁻¹`, as `π'` is monic
  haveI : Mono π' := compr_basics_5 hπ'
  have hζπ' : ζπ' = zetaMap (imPred f) (isSharp_imPred C f) ≫ inv β := by
    refine (cancel_mono π').mp ?_
    rw [hcorrπ'.2, ← hβ]
    simp only [Category.assoc]
    rw [← Category.assoc (inv β) β, IsIso.inv_hom_id, Category.id_comp, hζπim]
  -- the corresponding comprehension of `ζ'` is `π_{⌈1∘f⌉} ∘ γ⁻¹`, as `ζ'` is epic
  haveI : Epi ζ' := quotient_basics_6 hζ'
  have hπζ' : πζ' = inv γ ≫ comprMap (ceilPred (f ≫ truth Y)) := by
    refine (cancel_epi ζ').mp ?_
    rw [hcorrζ'.2, ← hγ]
    simp only [Category.assoc]
    rw [← Category.assoc γ (inv γ), IsIso.hom_inv_id, Category.id_comp, hζπc]
  -- `α = γ ∘ α' ∘ β` is the standard-form isomorphism of 212III for `f`
  refine (pureDagger_existsUnique f hf).unique ⟨asIso γ ≪≫ α' ≪≫ asIso β, ?_, ?_⟩
    (isDaggerOf_pureDagger f hf)
  · -- `f = asrt ∘ ζ ∘ (γ α' β) ∘ π_{im f}`, from `hform` by `hγ` and `hβ`
    simp only [Iso.trans_hom, asIso_hom]
    conv_lhs => rw [hform]
    rw [← hγ, ← hβ]
    simp only [Category.assoc]
  · -- and the two formulas for the dagger agree, the `γ⁻¹γ`/`ββ⁻¹` cancelling
    simp only [Iso.trans_inv, asIso_inv]
    rw [hζπ', hπζ']
    simp only [Category.assoc]

/-- Helper (216VII + 216IX): in a †-effectus the given dagger on `Pure C` is
*the* dagger of 217II — applying `(–)†` to the standard form 212III of a pure
map `f` yields the standard form of `f†`, by `dagger_of_zeta`,
`dagger_of_compr` and `dagger_of_iso`. -/
theorem isDaggerOf_dag (d : DaggerEffectus C) {P Q : PureCat C} (f : P ⟶ Q) :
    IsDaggerOf f.1 (d.daggerCat.dag f).1 := by
  obtain ⟨g, ⟨-, hg⟩, -⟩ := standard_form_map f.1
  haveI : IsIso g := standard_form_map_pure f.2 g hg
  refine ⟨asIso g, hg, ?_⟩
  -- name the four factors of the standard form as maps of `Pure C`
  obtain ⟨A, hA⟩ : ∃ h : P ⟶ P,
    h = ⟨asrt (f.1 ≫ truth Q.base), (asrt_spec _).1.1⟩ := ⟨_, rfl⟩
  obtain ⟨Zc, hZc⟩ : ∃ h : P ⟶ PureCat.of (comprObj (ceilPred (f.1 ≫ truth Q.base))),
    h = ⟨zetaMap (ceilPred (f.1 ≫ truth Q.base)) (isSharp_ceil _),
      isPure_of_isQuotient
        (zetaMap_spec (ceilPred (f.1 ≫ truth Q.base)) (isSharp_ceil _)).1⟩ :=
    ⟨_, rfl⟩
  obtain ⟨Al, hAl⟩ : ∃ h : (PureCat.of (comprObj (ceilPred (f.1 ≫ truth Q.base))) :
      PureCat C) ⟶ PureCat.of (comprObj (imPred f.1)),
    h = ⟨g, isPure_of_isQuotient (quotient_basics_3 g)⟩ := ⟨_, rfl⟩
  obtain ⟨Pi, hPi⟩ : ∃ h : (PureCat.of (comprObj (imPred f.1)) : PureCat C) ⟶ Q,
    h = ⟨comprMap (imPred f.1),
      isPure_comprehension C (isComprehension_comprMap _)⟩ := ⟨_, rfl⟩
  have hE : f = A ≫ Zc ≫ Al ≫ Pi := by
    refine Subtype.ext ?_
    rw [hA, hZc, hAl, hPi]
    exact hg
  have hdA : d.daggerCat.dag A = A := by
    rw [hA]; exact d.dag_asrt (f.1 ≫ truth Q.base)
  have hdZc : d.daggerCat.dag Zc =
      ⟨comprMap (ceilPred (f.1 ≫ truth Q.base)),
        isPure_comprehension C (isComprehension_comprMap _)⟩ := by
    rw [hZc]; exact dagger_of_zeta d (isSharp_ceil (f.1 ≫ truth Q.base))
  have hdPi : d.daggerCat.dag Pi =
      ⟨zetaMap (imPred f.1) (isSharp_imPred C f.1),
        isPure_of_isQuotient
          (zetaMap_spec (imPred f.1) (isSharp_imPred C f.1)).1⟩ := by
    rw [hPi]; exact dagger_of_compr d (isSharp_imPred C f.1)
  have hdAl : d.daggerCat.dag Al =
      ⟨inv g, isPure_of_isQuotient (quotient_basics_3 (inv g))⟩ := by
    rw [hAl]
    have h := dagger_of_iso d
      (P := PureCat.of (comprObj (ceilPred (f.1 ≫ truth Q.base))))
      (Q := PureCat.of (comprObj (imPred f.1)))
      ⟨⟨g, isPure_of_isQuotient (quotient_basics_3 g)⟩,
        ⟨inv g, isPure_of_isQuotient (quotient_basics_3 (inv g))⟩,
        Subtype.ext (IsIso.hom_inv_id g), Subtype.ext (IsIso.inv_hom_id g)⟩
    exact h
  have hD := congrArg d.daggerCat.dag hE
  rw [d.daggerCat.dag_comp, d.daggerCat.dag_comp, d.daggerCat.dag_comp,
    hdA, hdZc, hdAl, hdPi] at hD
  simp only [Category.assoc] at hD
  rw [hA] at hD
  have hfin := congrArg Subtype.val hD
  simp only [asIso_inv]
  exact hfin

/-- Helper (216VII + 216IX): in a †-effectus the given dagger on `Pure C`
agrees with `pureDagger` (217II). -/
theorem dag_eq_pureDagger (d : DaggerEffectus C) {P Q : PureCat C} (f : P ⟶ Q) :
    letI := dagger_thm_necessity d
    (d.daggerCat.dag f).1 = pureDagger f.1 f.2 := by
  letI := dagger_thm_necessity d
  exact (pureDagger_existsUnique f.1 f.2).unique (isDaggerOf_dag d f)
    (isDaggerOf_pureDagger f.1 f.2)

/-- Helper (211II): `asrt_1 = id`, since `id` is ⋄-positive and total.
(This is the author's "`asrt_1 = id`" of the solution to 217III.) -/
theorem asrt_one (W : C) : asrt (1 : Pred W) = 𝟙 W :=
  (asrt_unique _ (𝟙 W) (diamondPositive_id W) (Category.id_comp _)).symm

/-- Helper for 217III: to verify `IsDaggerOf f g` it suffices to exhibit the
standard-form isomorphism between comprehensions of *representatives* `c`,
`i` of `⌈1 ∘ f⌉` and `im f`. -/
theorem isDaggerOf_of_eq {f : X ⟶ Y} {g : Y ⟶ X} {c : Pred X} {i : Pred Y}
    (hcs : IsSharp c) (his : IsSharp i)
    (hc : ceilPred (f ≫ truth Y) = c) (hi : imPred f = i)
    (β : comprObj c ≅ comprObj i)
    (h1 : f = asrt (f ≫ truth Y) ≫ zetaMap c hcs ≫ β.hom ≫ comprMap i)
    (h2 : g = zetaMap i his ≫ β.inv ≫ comprMap c ≫ asrt (f ≫ truth Y)) :
    IsDaggerOf f g := by
  subst hc; subst hi; exact ⟨β, h1, h2⟩

/-- **217III** (`dagger-prime-basics`, eff.tex:5735, Exercise):
`asrt_p† = asrt_p`. -/
theorem dagger_prime_basics_asrt [DaggerPrimeEffectus C] (p : Pred X) :
    IsDaggerOf (asrt p) (asrt p) := by
  have h1 : asrt p ≫ truth X = p := (asrt_spec p).2
  -- `asrt_p = asrt_p ∘ asrt_{⌈p⌉} = π_{⌈p⌉} ∘ id ∘ ζ_{⌈p⌉} ∘ asrt_p`
  have habs1 : asrt p ≫ asrt (ceilPred p) = asrt p :=
    (asrt_absorp_rule (asrt p) (isSharp_ceil p) (isSharp_ceil p)).1.mp
      (by rw [imPred_asrt p]; exact pcm_preorder_refl _)
  have habs2 : asrt (ceilPred p) ≫ asrt p = asrt p :=
    (asrt_absorp_rule (asrt p) (isSharp_ceil p) (isSharp_ceil p)).2.mp
      (by rw [h1]; exact le_ceilPred p)
  have hζπ := (zetaMap_spec (ceilPred p) (isSharp_ceil p)).2.2
  refine isDaggerOf_of_eq (isSharp_ceil p) (isSharp_ceil p) (by rw [h1])
    (imPred_asrt p) (Iso.refl _) ?_ ?_
  · rw [h1, Iso.refl_hom, Category.id_comp, hζπ, habs1]
  · rw [h1, Iso.refl_inv, Category.id_comp, ← Category.assoc, hζπ, habs2]

/-- **217III** (`dagger-prime-basics`, eff.tex:5735, Exercise):
`π_s† = ζ_s` for a corresponding pair. -/
theorem dagger_prime_basics_pi [DaggerPrimeEffectus C] {s : Pred X}
    (hs : IsSharp s) : IsDaggerOf (comprMap s) (zetaMap s hs) := by
  -- `π_s = π_s ∘ id ∘ ζ_1 ∘ asrt_1`, using `ζ_1 = π_1⁻¹` and `asrt_1 = id`
  have := isIso_comprMap_one (comprObj s)
  have htot : comprMap s ≫ truth X = truth (comprObj s) :=
    compr_total (isComprehension_comprMap s)
  have hone : asrt (comprMap s ≫ truth X) = 𝟙 (comprObj s) := by
    rw [htot]; exact asrt_one (comprObj s)
  have hζπ := (zetaMap_spec (1 : Pred (comprObj s)) (isSharp_one _)).2.2
  rw [asrt_one] at hζπ
  refine isDaggerOf_of_eq (isSharp_one (comprObj s)) hs
    (by rw [htot]; exact ceil_of_isSharp (isSharp_one (comprObj s)))
    ((img_of_compr s).2 s hs) (asIso (comprMap (1 : Pred (comprObj s)))) ?_ ?_
  · rw [hone, Category.id_comp, asIso_hom, ← Category.assoc, hζπ,
      Category.id_comp]
  · rw [hone, Category.comp_id, asIso_inv, IsIso.inv_hom_id, Category.comp_id]

/-- **217III** (`dagger-prime-basics`, eff.tex:5735, Exercise):
`ζ_s† = π_s`. -/
theorem dagger_prime_basics_zeta [DaggerPrimeEffectus C] {s : Pred X}
    (hs : IsSharp s) : IsDaggerOf (zetaMap s hs) (comprMap s) := by
  -- `ζ_s = π_1 ∘ id ∘ ζ_s ∘ asrt_1`
  have := isIso_comprMap_one (comprObj s)
  obtain ⟨hq, hπζ, hζπ⟩ := zetaMap_spec s hs
  have hζ1 : zetaMap s hs ≫ truth (comprObj s) = s := by
    rw [quotient_basics_5 hq, eabasics_orth_orth]
  have him : imPred (zetaMap s hs) = (1 : Pred (comprObj s)) := by
    refine eabasics_le_antisymm (pred_le_truth _) ?_
    have h := (im_ineq (zetaMap s hs) (comprMap s)).1
    rwa [hπζ, imPred_id] at h
  have habs1 : asrt s ≫ zetaMap s hs = zetaMap s hs :=
    (asrt_absorp_rule (zetaMap s hs) (isSharp_one _) hs).2.mp
      (by rw [hζ1]; exact pcm_preorder_refl _)
  have habs2 : comprMap s ≫ asrt s = comprMap s :=
    (asrt_absorp_rule (comprMap s) hs (isSharp_one (comprObj s))).1.mp
      (by rw [(img_of_compr s).2 s hs]; exact pcm_preorder_refl _)
  have hζπ1 := (zetaMap_spec (1 : Pred (comprObj s)) (isSharp_one _)).2.2
  rw [asrt_one] at hζπ1
  refine isDaggerOf_of_eq hs (isSharp_one (comprObj s))
    (by rw [hζ1]; exact ceil_of_isSharp hs) him
    (asIso (comprMap (1 : Pred (comprObj s)))).symm ?_ ?_
  · rw [hζ1, Iso.symm_hom, asIso_inv, IsIso.inv_hom_id, Category.comp_id,
      habs1]
  · rw [hζ1, Iso.symm_inv, asIso_hom, ← Category.assoc, hζπ1,
      Category.id_comp, habs2]

/-- **217III** (`dagger-prime-basics`, eff.tex:5735, Exercise):
`α† = α⁻¹` for an isomorphism `α`. -/
theorem dagger_prime_basics_iso [DaggerPrimeEffectus C] (α : X ≅ Y) :
    IsDaggerOf α.hom α.inv := by
  -- `asrt_1 = id` (the author's "`ζ_1 = π_1 = asrt_1 = id`", first part)
  have hasrt_one : ∀ Z : C, asrt (1 : Pred Z) = 𝟙 Z := fun Z =>
    (asrt_unique _ (𝟙 Z) (diamondPositive_id Z) (Category.id_comp _)).symm
  -- `α` is total and faithful, so `1 ∘ α = 1`, `⌈1 ∘ α⌉ = 1` and `im α = 1`
  have htot : α.hom ≫ truth Y = truth X := iso_isTotal α.hom
  have hceil : ceilPred (α.hom ≫ truth Y) = (1 : Pred X) := by
    rw [htot]; exact ceil_of_isSharp (isSharp_one X)
  have him : imPred α.hom = (1 : Pred Y) :=
    (cancel_epi α.hom).mp (isImage_imPred α.hom).1
  have hone : asrt (α.hom ≫ truth Y) = 𝟙 X := by rw [htot]; exact hasrt_one X
  have hasrtc : asrt (ceilPred (α.hom ≫ truth Y)) = 𝟙 X := by
    rw [hceil]; exact hasrt_one X
  have hasrti : asrt (imPred α.hom) = 𝟙 Y := by rw [him]; exact hasrt_one Y
  -- hence `π_{⌈1∘α⌉}` and `π_{im α}` are isomorphisms, inverse to `ζ`
  obtain ⟨-, hπζc, hζπc⟩ :=
    zetaMap_spec (ceilPred (α.hom ≫ truth Y)) (isSharp_ceil _)
  obtain ⟨-, hπζi, hζπi⟩ := zetaMap_spec (imPred α.hom) (isSharp_imPred C α.hom)
  rw [hasrtc] at hζπc
  rw [hasrti] at hζπi
  set ζc := zetaMap (ceilPred (α.hom ≫ truth Y)) (isSharp_ceil _) with hζcdef
  set πc := comprMap (ceilPred (α.hom ≫ truth Y)) with hπcdef
  set ζi := zetaMap (imPred α.hom) (isSharp_imPred C α.hom) with hζidef
  set πi := comprMap (imPred α.hom) with hπidef
  -- the standard-form isomorphism is then just `α` conjugated by those
  refine ⟨{ hom := πc ≫ α.hom ≫ ζi
            inv := πi ≫ α.inv ≫ ζc
            hom_inv_id := ?_
            inv_hom_id := ?_ }, ?_, ?_⟩
  · calc (πc ≫ α.hom ≫ ζi) ≫ (πi ≫ α.inv ≫ ζc)
        = πc ≫ α.hom ≫ (ζi ≫ πi) ≫ α.inv ≫ ζc := by
          simp only [Category.assoc]
      _ = πc ≫ ζc := by rw [hζπi, Category.id_comp, α.hom_inv_id_assoc]
      _ = _ := hπζc
  · calc (πi ≫ α.inv ≫ ζc) ≫ (πc ≫ α.hom ≫ ζi)
        = πi ≫ α.inv ≫ (ζc ≫ πc) ≫ α.hom ≫ ζi := by
          simp only [Category.assoc]
      _ = πi ≫ ζi := by rw [hζπc, Category.id_comp, α.inv_hom_id_assoc]
      _ = _ := hπζi
  · calc α.hom = (ζc ≫ πc) ≫ α.hom ≫ (ζi ≫ πi) := by
          rw [hζπc, hζπi, Category.id_comp, Category.comp_id]
      _ = 𝟙 X ≫ ζc ≫ (πc ≫ α.hom ≫ ζi) ≫ πi := by
          simp only [Category.id_comp, Category.assoc]
      _ = _ := by rw [hone]
  · calc α.inv = (ζi ≫ πi) ≫ α.inv ≫ (ζc ≫ πc) := by
          rw [hζπc, hζπi, Category.id_comp, Category.comp_id]
      _ = ζi ≫ (πi ≫ α.inv ≫ ζc) ≫ πc ≫ 𝟙 X := by
          simp only [Category.comp_id, Category.assoc]
      _ = _ := by rw [hone]

/-- Helper: the quotient of a sharp predicate transports along an equality
of predicates (used to pass between `ζ_{⌈1∘h⌉}` and `ζ_{1∘h}` for sharp
`1 ∘ h`). -/
theorem zetaMap_eqToHom {s t : Pred X} (hs : IsSharp s) (ht : IsSharp t)
    (e : s = t) :
    zetaMap s hs ≫ eqToHom (congrArg comprObj e) = zetaMap t ht := by
  subst e; simp

/-- Helper: the comprehension of a predicate transports along an equality of
predicates. -/
theorem zetaMap_eqToHom_assoc {s t : Pred X} (hs : IsSharp s) (ht : IsSharp t)
    (e : s = t) {W : C} (f : comprObj t ⟶ W) :
    zetaMap s hs ≫ eqToHom (congrArg comprObj e) ≫ f = zetaMap t ht ≫ f := by
  subst e; simp

/-- Helper: the comprehension of a predicate transports along an equality of
predicates. -/
theorem eqToHom_comprMap {s t : Pred X} (e : s = t) :
    eqToHom (congrArg comprObj e) ≫ comprMap t = comprMap s := by
  subst e; simp

@[inherit_doc eqToHom_comprMap]
theorem eqToHom_comprMap_assoc {s t : Pred X} (e : s = t) {W : C} (f : X ⟶ W) :
    eqToHom (congrArg comprObj e) ≫ comprMap t ≫ f = comprMap s ≫ f := by
  subst e; simp

/-! ## Pristine maps (parsec 218) -/

/-- **218II** (`quotcompr-diamond-adjoint`, eff.tex:5757, Lemma): in a
†'-effectus, `π_s` is ⋄-adjoint to `ζ_s`. -/
theorem quotcompr_diamond_adjoint [DaggerPrimeEffectus C] {s : Pred X}
    (hs : IsSharp s) : DiamondAdjoint (comprMap s) (zetaMap s hs) := by
  obtain ⟨hquot, hπζ, hζπ⟩ := zetaMap_spec s hs
  have hπtot : IsTotal (comprMap s) := compr_total (isComprehension_comprMap s)
  have hζsharp : SharpMap (zetaMap s hs) :=
    DaggerPrimeEffectus.quot_sharp (DiamondEffectus.orth_sharp hs) hquot
  have hasa : diaPull (asrt s) = diaPush (asrt s) :=
    diamond_squares_2 (asrt_spec s).1
  -- the ⋄-self-adjointness of `asrt_s`, in elementary form
  have hswap : ∀ w r : Pred X, IsSharp w → IsSharp r →
      (asrt s ≫ w) ≼ orth r → (asrt s ≫ r) ≼ orth w := by
    intro w r hw hr h
    have hadj := diamond_adjunction (asrt s) ⟨w, hw⟩ ⟨r, hr⟩
    rw [← hasa] at hadj
    have h1 : ceilPred (asrt s ≫ w) ≼ orth r :=
      (ceil_le_iff_of_isSharp (DiamondEffectus.orth_sharp hr)).mpr h
    exact (ceil_le_iff_of_isSharp (DiamondEffectus.orth_sharp hw)).mp
      (hadj.mp h1)
  -- the Galois form of the statement, as in the thesis
  have galois : ∀ (t : Pred (comprObj s)) (u : Pred X), IsSharp t → IsSharp u →
      ((zetaMap s hs ≫ t) ≼ orth u ↔ (comprMap s ≫ u) ≼ orth t) := by
    intro t u ht hu
    constructor
    · -- `t = t ∘ ζ_s ∘ π_s ≤ u^⊥ ∘ π_s = (u ∘ π_s)^⊥`
      intro h
      have h1 : t ≼ (comprMap s ≫ orth u) := by
        have h2 := comp_le_comp (comprMap s) h
        rwa [← Category.assoc, hπζ, Category.id_comp] at h2
      rw [total_comp_orth hπtot] at h1
      exact le_orth_comm.mp h1
    · intro h
      have hvs : IsSharp (zetaMap s hs ≫ orth t) :=
        hζsharp _ (DiamondEffectus.orth_sharp ht)
      -- `u ∘ asrt_s = u ∘ π_s ∘ ζ_s ≤ t^⊥ ∘ ζ_s`
      have h1 : (asrt s ≫ u) ≼ orth (orth (zetaMap s hs ≫ orth t)) := by
        rw [eabasics_orth_orth, ← hζπ, Category.assoc]
        exact comp_le_comp _ h
      -- hence `(t^⊥ ∘ ζ_s)^⊥ ∘ asrt_s ≤ u^⊥`
      have h2 : (asrt s ≫ orth (zetaMap s hs ≫ orth t)) ≼ orth u :=
        hswap u (orth (zetaMap s hs ≫ orth t)) hu
          (DiamondEffectus.orth_sharp hvs) h1
      -- and `t ∘ ζ_s = (t^⊥ ∘ ζ_s ∘ π_s)^⊥ ∘ ζ_s = (t^⊥ ∘ ζ_s)^⊥ ∘ asrt_s`
      have h3 : zetaMap s hs ≫ t = asrt s ≫ orth (zetaMap s hs ≫ orth t) := by
        rw [← hζπ, Category.assoc, total_comp_orth hπtot, ← Category.assoc,
          hπζ, Category.id_comp, eabasics_orth_orth]
      rw [h3]; exact h2
  -- uniqueness of adjoints: `π_s^⋄(u)` and `(ζ_s)_⋄(u)` have the same
  -- sharp upper bounds, hence are equal
  funext u
  have key : ∀ t : SPred (comprObj s),
      ((diaPush (zetaMap s hs) u).1 ≼ orth t.1 ↔
        (diaPull (comprMap s) u).1 ≼ orth t.1) := by
    intro t
    rw [(diamond_adjunction (zetaMap s hs) t u).symm]
    show ceilPred (zetaMap s hs ≫ t.1) ≼ orth u.1 ↔
      ceilPred (comprMap s ≫ u.1) ≼ orth t.1
    rw [ceil_le_iff_of_isSharp (DiamondEffectus.orth_sharp u.2),
      ceil_le_iff_of_isSharp (DiamondEffectus.orth_sharp t.2)]
    exact galois t.1 u.1 t.2 u.2
  have hA := key (diaPull (comprMap s) u).orth
  have hB := key (diaPush (zetaMap s hs) u).orth
  rw [spred_orth_val, eabasics_orth_orth] at hA hB
  exact Subtype.ext (eabasics_le_antisymm (hB.mp (pcm_preorder_refl _))
    (hA.mpr (pcm_preorder_refl _)))

/-- **218IV** (`dfn-pristine`, eff.tex:5788, Definition): a map `f` in an
&-effectus is **pristine** when it is pure and `1 ∘ f` is sharp.
(Pristine maps are not closed under composition, 218V.) -/
def Pristine (f : X ⟶ Y) : Prop :=
  IsPure f ∧ IsSharp (f ≫ truth Y)

/-- **218VI** (`standard-form-pristine`, eff.tex:5808, Exercise): every
pristine map is of the form `h = π_{im h} ∘ α ∘ ζ_{1∘h}` for an
isomorphism `α`. -/
theorem standard_form_pristine {h : X ⟶ Y} (hp : Pristine h) :
    ∃ α : comprObj (h ≫ truth Y) ≅ comprObj (imPred h),
      h = zetaMap (h ≫ truth Y) hp.2 ≫ α.hom ≫ comprMap (imPred h) := by
  obtain ⟨g, ⟨-, hg⟩, -⟩ := standard_form_map h
  have hiso : IsIso g := standard_form_map_pure hp.1 g hg
  have hc : ceilPred (h ≫ truth Y) = h ≫ truth Y := ceil_of_isSharp hp.2
  -- `1 ∘ h` is sharp, so `ζ_{⌈1∘h⌉} ∘ asrt_{1∘h} = ζ_{1∘h}`
  have hz1 : zetaMap (ceilPred (h ≫ truth Y)) (isSharp_ceil _) ≫
      truth (comprObj (ceilPred (h ≫ truth Y))) = h ≫ truth Y := by
    rw [quotient_basics_5
        (zetaMap_spec (ceilPred (h ≫ truth Y)) (isSharp_ceil _)).1,
      eabasics_orth_orth, hc]
  have habs : asrt (h ≫ truth Y) ≫
      zetaMap (ceilPred (h ≫ truth Y)) (isSharp_ceil _) =
        zetaMap (ceilPred (h ≫ truth Y)) (isSharp_ceil _) :=
    (asrt_absorp_rule _ (isSharp_one _) hp.2).2.mp
      (by rw [hz1]; exact pcm_preorder_refl _)
  refine ⟨eqToIso (congrArg comprObj hc.symm) ≪≫ asIso g, ?_⟩
  rw [Iso.trans_hom, eqToIso.hom, asIso_hom]
  calc h = asrt (h ≫ truth Y) ≫
          zetaMap (ceilPred (h ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
          comprMap (imPred h) := hg
    _ = (asrt (h ≫ truth Y) ≫
          zetaMap (ceilPred (h ≫ truth Y)) (isSharp_ceil _)) ≫ g ≫
          comprMap (imPred h) := by simp only [Category.assoc]
    _ = zetaMap (ceilPred (h ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
          comprMap (imPred h) := by rw [habs]
    _ = (zetaMap (h ≫ truth Y) hp.2 ≫
          eqToHom (congrArg comprObj hc.symm)) ≫ g ≫ comprMap (imPred h) := by
          rw [zetaMap_eqToHom hp.2 (isSharp_ceil _) hc.symm]
    _ = _ := by simp only [Category.assoc]

/-- Helper for 218VII (the first computation of eff.tex:5850): in a
†'-effectus `asrt_p ∘ π_s = π_s ∘ asrt_{p ∘ π_s}` for sharp `s` and
`p ≤ s`. (The mirror image of 216X.) -/
theorem compr_through_asrt [DaggerPrimeEffectus C] {s : Pred Y}
    (hs : IsSharp s) {p : Pred Y} (hle : p ≼ s) :
    comprMap s ≫ asrt p = asrt (comprMap s ≫ p) ≫ comprMap s := by
  obtain ⟨-, hπζ, hζπ⟩ := zetaMap_spec s hs
  -- `im asrt_p = ⌈p⌉ ≤ s`, so `asrt_p ∘ asrt_s = asrt_p`
  have ha : asrt p ≫ asrt s = asrt p := by
    refine (asrt_absorp_rule (asrt p) hs hs).1.mp ?_
    rw [imPred_asrt]
    have h := ceil_mono hle
    rwa [ceil_of_isSharp hs] at h
  -- `1 ∘ p = p ≤ s`, so `p ∘ asrt_s = p`
  have hb : asrt s ≫ p = p := by
    refine (asrt_absorp_rule p (isSharp_one (effObj C)) hs).2.mp ?_
    rw [truth_effObj_eq_id, Category.comp_id]
    exact hle
  -- 216X at the predicate `p ∘ π_s`
  have hz := zeta_through_asrt
    (fun p => (DaggerPrimeEffectus.sqrt_existsUnique p).exists) hs
    (quotcompr_diamond_adjoint hs) (comprMap s ≫ p)
  rw [← Category.assoc, hζπ, hb] at hz
  calc comprMap s ≫ asrt p
      = comprMap s ≫ asrt p ≫ asrt s := by rw [ha]
    _ = comprMap s ≫ asrt p ≫ zetaMap s hs ≫ comprMap s := by rw [hζπ]
    _ = comprMap s ≫ (zetaMap s hs ≫ asrt (comprMap s ≫ p)) ≫ comprMap s := by
        rw [hz]; simp only [Category.assoc]
    _ = (comprMap s ≫ zetaMap s hs) ≫ asrt (comprMap s ≫ p) ≫ comprMap s := by
        simp only [Category.assoc]
    _ = asrt (comprMap s ≫ p) ≫ comprMap s := by
        rw [hπζ, Category.id_comp]

/-- **218VII** (`pristine-asrt`, eff.tex:5815, Proposition): in a
†'-effectus, for a pristine `h` and predicate `p ≤ im h`:
`asrt_p ∘ h = h ∘ asrt_{p ∘ h}`. -/
theorem pristine_asrt [DaggerPrimeEffectus C] {h : X ⟶ Y} (hp : Pristine h)
    {p : Pred Y} (hle : p ≼ imPred h) :
    h ≫ asrt p = asrt (h ≫ p) ≫ h := by
  have hsqrt : ∀ {Z : C} (p : Pred Z), ∃ q, andThen q q = p := fun p =>
    (DaggerPrimeEffectus.sqrt_existsUnique p).exists
  obtain ⟨α, hform⟩ := standard_form_pristine hp
  -- `asrt_p ∘ π_s = π_s ∘ asrt_{p ∘ π_s}`
  have hπ := compr_through_asrt (isSharp_imPred C h) hle
  -- `asrt_q ∘ α = α ∘ asrt_{q ∘ α}` and `asrt_r ∘ ζ_t = ζ_t ∘ asrt_{r ∘ ζ_t}`
  have hα := asrt_iso hsqrt α.hom (comprMap (imPred h) ≫ p)
  have hζ := zeta_through_asrt hsqrt hp.2
    (quotcompr_diamond_adjoint hp.2)
    (α.hom ≫ comprMap (imPred h) ≫ p)
  calc h ≫ asrt p
      = zetaMap (h ≫ truth Y) hp.2 ≫ α.hom ≫ comprMap (imPred h) ≫ asrt p := by
        conv_lhs => rw [hform]
        simp only [Category.assoc]
    _ = zetaMap (h ≫ truth Y) hp.2 ≫ α.hom ≫
          asrt (comprMap (imPred h) ≫ p) ≫ comprMap (imPred h) := by rw [hπ]
    _ = zetaMap (h ≫ truth Y) hp.2 ≫
          asrt (α.hom ≫ comprMap (imPred h) ≫ p) ≫
            α.hom ≫ comprMap (imPred h) := by
        rw [← Category.assoc α.hom, hα]; simp only [Category.assoc]
    _ = asrt (zetaMap (h ≫ truth Y) hp.2 ≫ α.hom ≫ comprMap (imPred h) ≫ p) ≫
          zetaMap (h ≫ truth Y) hp.2 ≫ α.hom ≫ comprMap (imPred h) := by
        rw [← Category.assoc (zetaMap (h ≫ truth Y) hp.2), hζ]
        simp only [Category.assoc]
    _ = asrt (h ≫ p) ≫ h := by
        conv_rhs => rw [hform]
        simp only [Category.assoc]

/-- **218IX.1** (`asrt-pristine-reverse`, eff.tex:5864, Exercise): if
`h = π_{im h} ∘ α ∘ ζ_{1∘h}` is pristine, then
`h† = π_{1∘h} ∘ α⁻¹ ∘ ζ_{im h}`. -/
theorem asrt_pristine_reverse_1 [DaggerPrimeEffectus C] {h : X ⟶ Y}
    (hp : Pristine h)
    (α : comprObj (h ≫ truth Y) ≅ comprObj (imPred h))
    (hform : h = zetaMap (h ≫ truth Y) hp.2 ≫ α.hom ≫ comprMap (imPred h)) :
    pureDagger h hp.1 =
      zetaMap (imPred h) (isSharp_imPred C h) ≫ α.inv ≫
        comprMap (h ≫ truth Y) := by
  refine (pureDagger_existsUnique h hp.1).unique (isDaggerOf_pureDagger h hp.1) ?_
  -- `1 ∘ h` is sharp, so `ζ_{⌈1∘h⌉} ∘ asrt_{1∘h} = ζ_{1∘h}` and
  -- `asrt_{1∘h} ∘ π_{⌈1∘h⌉} = π_{1∘h}` (both by `asrt-absorp-rule`)
  have hz1 : zetaMap (h ≫ truth Y) hp.2 ≫ truth (comprObj (h ≫ truth Y)) =
      h ≫ truth Y := by
    rw [quotient_basics_5 (zetaMap_spec (h ≫ truth Y) hp.2).1,
      eabasics_orth_orth]
  have habs1 : asrt (h ≫ truth Y) ≫ zetaMap (h ≫ truth Y) hp.2 =
      zetaMap (h ≫ truth Y) hp.2 :=
    (asrt_absorp_rule _ (isSharp_one _) hp.2).2.mp
      (by rw [hz1]; exact pcm_preorder_refl _)
  have habs2 : comprMap (h ≫ truth Y) ≫ asrt (h ≫ truth Y) =
      comprMap (h ≫ truth Y) :=
    (asrt_absorp_rule _ hp.2 (isSharp_one _)).1.mp
      (by rw [(img_of_compr (h ≫ truth Y)).2 _ hp.2]; exact pcm_preorder_refl _)
  refine isDaggerOf_of_eq hp.2 (isSharp_imPred C h) (ceil_of_isSharp hp.2) rfl
    α ?_ ?_
  · rw [← Category.assoc, habs1]; exact hform
  · rw [habs2]

/-- The dagger of a pure map is pure (needed to state 218IX.2 and 218XII;
implicit in 217II). -/
theorem isPure_pureDagger [DaggerPrimeEffectus C] {f : X ⟶ Y}
    (hf : IsPure f) : IsPure (pureDagger f hf) := by
  obtain ⟨α, -, hg⟩ := isDaggerOf_pureDagger f hf
  rw [hg]
  exact upm_closed_pure (isPure_of_isQuotient (zetaMap_spec _ _).1)
    (upm_closed_pure (isPure_of_isQuotient (quotient_basics_3 α.inv))
      (upm_closed_pure (isPure_comprehension C (isComprehension_comprMap _))
        (asrt_spec _).1.1))

/-- Helper (218IX.2, "note that by the previous point"): `1 ∘ h† = im h` for
a pristine map `h`. -/
theorem pristine_dagger_truth [DaggerPrimeEffectus C] {h : X ⟶ Y}
    (hp : Pristine h) : pureDagger h hp.1 ≫ truth X = imPred h := by
  obtain ⟨α, hform⟩ := standard_form_pristine hp
  rw [asrt_pristine_reverse_1 hp α hform, Category.assoc, Category.assoc,
    compr_total (isComprehension_comprMap (h ≫ truth Y)),
    iso_isTotal α.inv,
    quotient_basics_5 (zetaMap_spec (imPred h) (isSharp_imPred C h)).1,
    eabasics_orth_orth]

/-- Helper (218IX.2, "note that by the previous point"): `im h† = 1 ∘ h` for
a pristine map `h`. -/
theorem pristine_dagger_imPred [DaggerPrimeEffectus C] {h : X ⟶ Y}
    (hp : Pristine h) : imPred (pureDagger h hp.1) = h ≫ truth Y := by
  obtain ⟨α, hform⟩ := standard_form_pristine hp
  have hepi : Epi (zetaMap (imPred h) (isSharp_imPred C h)) :=
    quotient_basics_6 (zetaMap_spec (imPred h) (isSharp_imPred C h)).1
  rw [asrt_pristine_reverse_1 hp α hform, imPred_comp_of_epi,
    (im_ineq (comprMap (h ≫ truth Y)) α.inv).2 α.inv inferInstance,
    (img_of_compr (h ≫ truth Y)).2 _ hp.2]

/-- **218IX.2** (`asrt-pristine-reverse`, eff.tex:5864, Exercise):
`h†† = h` for pristine `h`. -/
theorem asrt_pristine_reverse_2 [DaggerPrimeEffectus C] {h : X ⟶ Y}
    (hp : Pristine h) :
    pureDagger (pureDagger h hp.1) (isPure_pureDagger hp.1) = h := by
  obtain ⟨α, hform⟩ := standard_form_pristine hp
  have e1 : pureDagger h hp.1 ≫ truth X = imPred h := pristine_dagger_truth hp
  have e2 : imPred (pureDagger h hp.1) = h ≫ truth Y := pristine_dagger_imPred hp
  -- `h†` is pristine, with `1 ∘ h† = im h` and `im h† = 1 ∘ h`
  have hp' : Pristine (pureDagger h hp.1) :=
    ⟨isPure_pureDagger hp.1, by rw [e1]; exact isSharp_imPred C h⟩
  -- so its standard-form isomorphism is `α⁻¹` (up to the transports)
  refine (asrt_pristine_reverse_1 hp'
    (eqToIso (congrArg comprObj e1) ≪≫ α.symm ≪≫
      eqToIso (congrArg comprObj e2.symm)) ?_).trans ?_
  · simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
    rw [zetaMap_eqToHom_assoc hp'.2 (isSharp_imPred C h) e1,
      eqToHom_comprMap e2.symm]
    exact asrt_pristine_reverse_1 hp α hform
  · simp only [Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Category.assoc]
    rw [zetaMap_eqToHom_assoc _ hp.2 e2, eqToHom_comprMap e1.symm]
    exact hform.symm

/-- **218IX.3** (`asrt-pristine-reverse`, eff.tex:5864, Exercise):
`h† ∘ h = asrt_{1∘h}` for pristine `h`. -/
theorem asrt_pristine_reverse_3 [DaggerPrimeEffectus C] {h : X ⟶ Y}
    (hp : Pristine h) :
    h ≫ pureDagger h hp.1 = asrt (h ≫ truth Y) := by
  obtain ⟨α, hform⟩ := standard_form_pristine hp
  calc h ≫ pureDagger h hp.1
      = (zetaMap (h ≫ truth Y) hp.2 ≫ α.hom ≫ comprMap (imPred h)) ≫
        (zetaMap (imPred h) (isSharp_imPred C h) ≫ α.inv ≫
          comprMap (h ≫ truth Y)) := by
        rw [← hform, ← asrt_pristine_reverse_1 hp α hform]
    _ = zetaMap (h ≫ truth Y) hp.2 ≫ α.hom ≫
        (comprMap (imPred h) ≫ zetaMap (imPred h) (isSharp_imPred C h)) ≫
        α.inv ≫ comprMap (h ≫ truth Y) := by simp only [Category.assoc]
    _ = zetaMap (h ≫ truth Y) hp.2 ≫ comprMap (h ≫ truth Y) := by
        rw [(zetaMap_spec (imPred h) (isSharp_imPred C h)).2.1,
          Category.id_comp, α.hom_inv_id_assoc]
    _ = asrt (h ≫ truth Y) := (zetaMap_spec (h ≫ truth Y) hp.2).2.2

/-- **218IX.4** (`asrt-pristine-reverse`, eff.tex:5864, Exercise):
`p ∘ h† ≤ im h` for any predicate `p` and pristine `h`. -/
theorem asrt_pristine_reverse_4 [DaggerPrimeEffectus C] {h : X ⟶ Y}
    (hp : Pristine h) (p : Pred X) :
    (pureDagger h hp.1 ≫ p) ≼ imPred h := by
  have h1 := comp_le_comp (pureDagger h hp.1) (pred_le_truth p)
  rwa [pristine_dagger_truth hp] at h1

/-- **218IX.5** (`asrt-pristine-reverse`, eff.tex:5864, Exercise): if
`p ≤ 1 ∘ h` then `asrt_{p ∘ h†} ∘ h = h ∘ asrt_p` for pristine `h`. -/
theorem asrt_pristine_reverse_5 [DaggerPrimeEffectus C] {h : X ⟶ Y}
    (hp : Pristine h) {p : Pred X} (hle : p ≼ (h ≫ truth Y)) :
    h ≫ asrt (pureDagger h hp.1 ≫ p) = asrt p ≫ h := by
  -- `p ≤ 1 ∘ h` gives `p ∘ asrt_{1∘h} = p` by `asrt-absorp-rule`
  have hb : asrt (h ≫ truth Y) ≫ p = p :=
    (asrt_absorp_rule p (isSharp_one (effObj C)) hp.2).2.mp
      (by rw [truth_effObj_eq_id, Category.comp_id]; exact hle)
  -- 218VII at the predicate `p ∘ h†`, which is below `im h` by 218IX.4
  have h1 := pristine_asrt hp (asrt_pristine_reverse_4 hp p)
  rwa [← Category.assoc, asrt_pristine_reverse_3 hp, hb] at h1

/-- **218X** (`prist-asrt-decomp`, eff.tex:5881, Proposition), first half:
in a †'-effectus every pure map `f` decomposes uniquely as
`f = h ∘ asrt_{1∘f}` with `h` pristine and `1 ∘ h = ⌈1 ∘ f⌉`. -/
theorem imPred_of_prist_asrt [DaggerPrimeEffectus C] {f h : X ⟶ Y}
    (hh : Pristine h) (h1 : h ≫ truth Y = ceilPred (f ≫ truth Y))
    (hd : f = asrt (f ≫ truth Y) ≫ h) : imPred h = imPred f := by
  obtain ⟨α, hform⟩ := standard_form_pristine hh
  -- `ζ_{⌈1∘f⌉} ∘ asrt_{1∘f}` is a quotient (212I), hence epi
  have hfac : asrt (f ≫ truth Y) ≫ zetaMap (h ≫ truth Y) hh.2 =
      (asrt (f ≫ truth Y) ≫
        zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _)) ≫
        eqToHom (congrArg comprObj h1.symm) := by
    rw [Category.assoc, zetaMap_eqToHom (isSharp_ceil _) hh.2 h1.symm]
  have hepi0 : Epi (asrt (f ≫ truth Y) ≫
      zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _)) :=
    quotient_basics_6 (zeta_asrt_quot (f ≫ truth Y))
  have hepi : Epi (asrt (f ≫ truth Y) ≫ zetaMap (h ≫ truth Y) hh.2) := by
    rw [hfac]; exact epi_comp _ _
  have hfe : f = (asrt (f ≫ truth Y) ≫ zetaMap (h ≫ truth Y) hh.2) ≫
      α.hom ≫ comprMap (imPred h) := by
    rw [Category.assoc]
    exact hd.trans (congrArg _ hform)
  rw [hfe, imPred_comp_of_epi,
    (im_ineq (comprMap (imPred h)) α.hom).2 α.hom inferInstance,
    (img_of_compr (imPred h)).2 _ (isSharp_imPred C h)]

/-- **218X** (`prist-asrt-decomp`, eff.tex:5881, Proposition), first half:
in a †'-effectus every pure map `f` decomposes uniquely as
`f = h ∘ asrt_{1∘f}` with `h` pristine and `1 ∘ h = ⌈1 ∘ f⌉`. -/
theorem prist_asrt_decomp [DaggerPrimeEffectus C] {f : X ⟶ Y}
    (hf : IsPure f) :
    ∃! h : X ⟶ Y, Pristine h ∧ h ≫ truth Y = ceilPred (f ≫ truth Y) ∧
      f = asrt (f ≫ truth Y) ≫ h := by
  obtain ⟨g, ⟨-, hg⟩, hu⟩ := standard_form_map f
  have hiso : IsIso g := standard_form_map_pure hf g hg
  -- `h = π_{im f} ∘ α ∘ ζ_{⌈1∘f⌉}` is the pristine part
  have htr : (zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
      comprMap (imPred f)) ≫ truth Y = ceilPred (f ≫ truth Y) := by
    rw [Category.assoc, Category.assoc,
      compr_total (isComprehension_comprMap (imPred f)), iso_isTotal g,
      quotient_basics_5
        (zetaMap_spec (ceilPred (f ≫ truth Y)) (isSharp_ceil _)).1,
      eabasics_orth_orth]
  refine ⟨zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
      comprMap (imPred f),
    ⟨⟨upm_closed_pure (isPure_of_isQuotient (zetaMap_spec _ _).1)
        (upm_closed_pure (isPure_of_isQuotient (quotient_basics_3 g))
          (isPure_comprehension C (isComprehension_comprMap _))),
      by rw [htr]; exact isSharp_ceil _⟩, htr, hg⟩,
    ?_⟩
  rintro h' ⟨hp', h1', hd'⟩
  have him : imPred h' = imPred f := imPred_of_prist_asrt hp' h1' hd'
  obtain ⟨α, hform⟩ := standard_form_pristine hp'
  -- the transported `α` also puts `f` in standard form, so it *is* `g`
  set g' : comprObj (ceilPred (f ≫ truth Y)) ⟶ comprObj (imPred f) :=
    eqToHom (congrArg comprObj h1'.symm) ≫ α.hom ≫
      eqToHom (congrArg comprObj him) with hg'def
  have hg'iso : IsIso g' := by rw [hg'def]; infer_instance
  have key : asrt (f ≫ truth Y) ≫
      zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g' ≫
        comprMap (imPred f) = f := by
    rw [hg'def]
    simp only [Category.assoc]
    rw [zetaMap_eqToHom_assoc (isSharp_ceil _) hp'.2 h1'.symm,
      eqToHom_comprMap him]
    exact (hd'.trans (congrArg _ hform)).symm
  have hgg : g' = g :=
    hu g' ⟨⟨iso_isTotal g', faithfulMap_of_isIso C g'⟩, key.symm⟩
  rw [← hgg, hg'def]
  simp only [Category.assoc]
  rw [zetaMap_eqToHom_assoc (isSharp_ceil _) hp'.2 h1'.symm,
    eqToHom_comprMap him]
  exact hform

/-- **218X** (`prist-asrt-decomp`, eff.tex:5881, Proposition), second half:
for the pristine part `h` of a pure `f`, we have
`f† = asrt_{1∘f} ∘ h†`. -/
theorem prist_asrt_decomp_dagger [DaggerPrimeEffectus C] {f : X ⟶ Y}
    (hf : IsPure f) {h : X ⟶ Y} (hh : Pristine h)
    (h1 : h ≫ truth Y = ceilPred (f ≫ truth Y))
    (hd : f = asrt (f ≫ truth Y) ≫ h) :
    pureDagger f hf = pureDagger h hh.1 ≫ asrt (f ≫ truth Y) := by
  have him : imPred h = imPred f := imPred_of_prist_asrt hh h1 hd
  obtain ⟨α, hform⟩ := standard_form_pristine hh
  refine (pureDagger_existsUnique f hf).unique (isDaggerOf_pureDagger f hf) ?_
  rw [asrt_pristine_reverse_1 hh α hform]
  refine isDaggerOf_of_eq (isSharp_ceil _) (isSharp_imPred C f) rfl rfl
    (eqToIso (congrArg comprObj h1.symm) ≪≫ α ≪≫
      eqToIso (congrArg comprObj him)) ?_ ?_
  · simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
    rw [zetaMap_eqToHom_assoc (isSharp_ceil _) hh.2 h1.symm,
      eqToHom_comprMap him]
    exact hd.trans (congrArg _ hform)
  · simp only [Iso.trans_inv, eqToIso.inv, Category.assoc]
    rw [zetaMap_eqToHom_assoc (isSharp_imPred C f) (isSharp_imPred C h) him.symm,
      eqToHom_comprMap_assoc h1]

/-- **218XII** (`dagger-idempotent`, eff.tex:5929, Proposition): in a
†'-effectus, `f†† = f` for every pure `f`. -/
theorem dagger_idempotent [DaggerPrimeEffectus C] {f : X ⟶ Y}
    (hf : IsPure f) :
    pureDagger (pureDagger f hf) (isPure_pureDagger hf) = f := by
  -- `f = h ∘ asrt_{1∘f}` with `h` pristine and `1 ∘ h = ⌈1∘f⌉` (218X)
  obtain ⟨h, ⟨hh, h1, hd⟩, -⟩ := prist_asrt_decomp hf
  have hdag : pureDagger f hf = pureDagger h hh.1 ≫ asrt (f ≫ truth Y) :=
    prist_asrt_decomp_dagger hf hh h1 hd
  -- `h†` is pristine, with `1 ∘ h† = im h` and `im h† = 1 ∘ h`
  have e1 : pureDagger h hh.1 ≫ truth X = imPred h := pristine_dagger_truth hh
  have e2 : imPred (pureDagger h hh.1) = h ≫ truth Y := pristine_dagger_imPred hh
  have hh' : Pristine (pureDagger h hh.1) :=
    ⟨isPure_pureDagger hh.1, by rw [e1]; exact isSharp_imPred C h⟩
  -- `1 ∘ f† = (1∘f) ∘ h†`
  have htr : pureDagger f hf ≫ truth X =
      pureDagger h hh.1 ≫ f ≫ truth Y := by
    rw [hdag, Category.assoc, (asrt_spec (f ≫ truth Y)).2]
  -- `⌈1 ∘ f†⌉ = ⌈im h† ∘ h†⌉ = ⌈1 ∘ h†⌉ = 1 ∘ h†`, so `h†` is the pristine
  -- part of `f†`
  have hceil : pureDagger h hh.1 ≫ truth X =
      ceilPred (pureDagger f hf ≫ truth X) := by
    have key : ceilPred (pureDagger h hh.1 ≫ f ≫ truth Y) = imPred h := by
      set k := pureDagger h hh.1 with hk
      rw [← ceiling_within_ceiling (f ≫ truth Y) k, ← h1, ← e2,
        (isImage_imPred k).1, e1]
      exact ceil_of_isSharp (isSharp_imPred C h)
    rw [htr, key, e1]
  -- `f† = asrt_{1∘f} ∘ h† = h† ∘ asrt_{1∘f†}` by 218VII
  have hd' : pureDagger f hf =
      asrt (pureDagger f hf ≫ truth X) ≫ pureDagger h hh.1 := by
    have hle : (f ≫ truth Y) ≼ imPred (pureDagger h hh.1) := by
      rw [e2, h1]; exact le_ceil _
    rw [htr]
    exact hdag.trans (pristine_asrt hh' hle)
  -- hence `f†† = h†† ∘ asrt_{1∘f†} = h ∘ asrt_{(1∘f)∘h†}`
  have hddag := prist_asrt_decomp_dagger (isPure_pureDagger hf) hh' hceil hd'
  rw [hddag, asrt_pristine_reverse_2 hh, htr]
  -- and `asrt_{(1∘f)∘h†} ∘ h = h ∘ asrt_{1∘f} = f` by 218IX.5
  rw [asrt_pristine_reverse_5 hh (by rw [h1]; exact le_ceil _)]
  exact hd.symm

/-! ## Functoriality of the dagger (parsecs 219–220) -/

/-- Helper (`asrt-absorp-rule`, 211XV): `p ∘ asrt_{⌈p⌉} = p`. -/
theorem asrt_ceil_comp (p : Pred X) : asrt (ceilPred p) ≫ p = p :=
  (asrt_absorp_rule p (isSharp_one (effObj C)) (isSharp_ceil p)).2.mp
    (by rw [truth_effObj_eq_id, Category.comp_id]; exact le_ceil p)

/-- Helper for 219XI (the thesis's `p̄ = p ∘ π_{⌈p⌉}`): `p̄ ∘ ζ_{⌈p⌉} = p`. -/
theorem zeta_comp_bar (p : Pred X) :
    zetaMap (ceilPred p) (isSharp_ceil p) ≫ comprMap (ceilPred p) ≫ p = p := by
  rw [← Category.assoc, (zetaMap_spec (ceilPred p) (isSharp_ceil p)).2.2]
  exact asrt_ceil_comp p

/-- Helper for 219XI: `asrt_p̄ ∘ ζ_{⌈p⌉} = ζ_{⌈p⌉} ∘ asrt_p` (216X at `p̄`). -/
theorem zeta_asrt_bar [DaggerPrimeEffectus C] (p : Pred X) :
    zetaMap (ceilPred p) (isSharp_ceil p) ≫ asrt (comprMap (ceilPred p) ≫ p) =
      asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p) := by
  have h := zeta_through_asrt
    (fun p => (DaggerPrimeEffectus.sqrt_existsUnique p).exists)
    (isSharp_ceil p) (quotcompr_diamond_adjoint (isSharp_ceil p))
    (comprMap (ceilPred p) ≫ p)
  rwa [zeta_comp_bar p] at h

/-- Helper for 219XI (the computation before
`dagger-seqprod-inversion`, eff.tex:6338): `⌈p̄⌉ = 1`. -/
theorem ceil_bar [DaggerPrimeEffectus C] (p : Pred X) :
    ceilPred (comprMap (ceilPred p) ≫ p) =
      (1 : Pred (comprObj (ceilPred p))) := by
  have hq : IsQuotient (orth (ceilPred p))
      (zetaMap (ceilPred p) (isSharp_ceil p)) :=
    (zetaMap_spec (ceilPred p) (isSharp_ceil p)).1
  have hsharp : SharpMap (zetaMap (ceilPred p) (isSharp_ceil p)) :=
    DaggerPrimeEffectus.quot_sharp
      (DiamondEffectus.orth_sharp (isSharp_ceil p)) hq
  have h := (sharp_ceil _).mp hsharp (comprMap (ceilPred p) ≫ p)
  rw [zeta_comp_bar p] at h
  have h1 : zetaMap (ceilPred p) (isSharp_ceil p) ≫
      truth (comprObj (ceilPred p)) = ceilPred p := by
    rw [quotient_basics_5 hq, eabasics_orth_orth]
  haveI : Epi (zetaMap (ceilPred p) (isSharp_ceil p)) := quotient_basics_6 hq
  refine (cancel_epi (zetaMap (ceilPred p) (isSharp_ceil p))).mp ?_
  rw [← h]
  exact h1.symm

/-- Helper for 219XI ("`asrt_p̄` is a quotient and therefore an epi",
eff.tex:6345): `asrt_p̄` is epic. -/
theorem epi_asrt_bar [DaggerPrimeEffectus C] (p : Pred X) :
    Epi (asrt (comprMap (ceilPred p) ≫ p)) := by
  have him : imPred (asrt (comprMap (ceilPred p) ≫ p)) = 1 := by
    rw [imPred_asrt]; exact ceil_bar p
  have hfaith : FaithfulMap (asrt (comprMap (ceilPred p) ≫ p)) := by
    have h := isImage_imPred (asrt (comprMap (ceilPred p) ≫ p))
    rwa [him] at h
  obtain ⟨r, hr⟩ := standard_form_map_quot (asrt_spec _).1.1 hfaith
  exact quotient_basics_6 hr

/-- Helper for 219XI (the computation of eff.tex:6293–6390, from the second
axiom of a †'-effectus down to `dagger-seqprod-inversion`): if
`asrt²_{ab} = (π_{⌈ba⌉} ∘ μ ∘ ζ_{⌈ab⌉} ∘ asrt_{ab}) ∘
(π_{⌈ab⌉} ∘ ν ∘ ζ_{⌈ba⌉} ∘ asrt_{ba})`, then `ν ∘ μ = id` and
`ab̄ = b̄a ∘ μ` (writing `p̄ = p ∘ π_{⌈p⌉}`). -/
theorem asrt_mu_inv [DaggerPrimeEffectus C] {ab ba : Pred X}
    (μ : comprObj (ceilPred ab) ≅ comprObj (ceilPred ba))
    (ν : comprObj (ceilPred ba) ≅ comprObj (ceilPred ab))
    (hsq : asrt ab ≫ asrt ab =
      (asrt ab ≫ zetaMap (ceilPred ab) (isSharp_ceil ab) ≫ μ.hom ≫
          comprMap (ceilPred ba)) ≫
        (asrt ba ≫ zetaMap (ceilPred ba) (isSharp_ceil ba) ≫ ν.hom ≫
          comprMap (ceilPred ab))) :
    μ.hom ≫ ν.hom = 𝟙 (comprObj (ceilPred ab)) ∧
      comprMap (ceilPred ab) ≫ ab =
        μ.hom ≫ comprMap (ceilPred ba) ≫ ba := by
  have hsqrt : ∀ {Z : C} (p : Pred Z), ∃ q, andThen q q = p := fun p =>
    (DaggerPrimeEffectus.sqrt_existsUnique p).exists
  obtain ⟨hqab, hπζab, hζπab⟩ := zetaMap_spec (ceilPred ab) (isSharp_ceil ab)
  obtain ⟨-, hπζba, -⟩ := zetaMap_spec (ceilPred ba) (isSharp_ceil ba)
  haveI : Epi (zetaMap (ceilPred ab) (isSharp_ceil ab)) :=
    quotient_basics_6 hqab
  haveI : Mono (comprMap (ceilPred ab)) :=
    compr_basics_5 (isComprehension_comprMap _)
  haveI : Epi (asrt (comprMap (ceilPred ab) ≫ ab)) := epi_asrt_bar ab
  -- `asrt_{ab̄} ∘ ζ_{⌈ab⌉} = ζ_{⌈ab⌉} ∘ asrt_{ab}` (216X) and
  -- `asrt_{ba} ∘ π_{⌈ba⌉} = π_{⌈ba⌉} ∘ asrt_{b̄a}` (218VII)
  have e1 : zetaMap (ceilPred ab) (isSharp_ceil ab) ≫
      asrt (comprMap (ceilPred ab) ≫ ab) =
        asrt ab ≫ zetaMap (ceilPred ab) (isSharp_ceil ab) := zeta_asrt_bar ab
  have e2 : comprMap (ceilPred ba) ≫ asrt ba =
      asrt (comprMap (ceilPred ba) ≫ ba) ≫ comprMap (ceilPred ba) :=
    compr_through_asrt (isSharp_ceil ba) (le_ceil ba)
  have e1a : ∀ {W : C} (f : comprObj (ceilPred ab) ⟶ W),
      zetaMap (ceilPred ab) (isSharp_ceil ab) ≫
        asrt (comprMap (ceilPred ab) ≫ ab) ≫ f =
      asrt ab ≫ zetaMap (ceilPred ab) (isSharp_ceil ab) ≫ f := by
    intro W f; rw [← Category.assoc, e1, Category.assoc]
  have e2a : ∀ {W : C} (f : X ⟶ W),
      comprMap (ceilPred ba) ≫ asrt ba ≫ f =
      asrt (comprMap (ceilPred ba) ≫ ba) ≫ comprMap (ceilPred ba) ≫ f := by
    intro W f; rw [← Category.assoc, e2, Category.assoc]
  have eabs : asrt ab ≫ asrt (ceilPred ab) = asrt ab :=
    (asrt_absorp_rule (asrt ab) (isSharp_ceil ab) (isSharp_ceil ab)).1.mp
      (by rw [imPred_asrt]; exact pcm_preorder_refl _)
  -- the left-hand side, conjugated by `ζ_{⌈ab⌉}` and `π_{⌈ab⌉}`
  have hL : zetaMap (ceilPred ab) (isSharp_ceil ab) ≫
      (asrt (comprMap (ceilPred ab) ≫ ab) ≫
        asrt (comprMap (ceilPred ab) ≫ ab)) ≫ comprMap (ceilPred ab) =
      asrt ab ≫ asrt ab := by
    simp only [Category.assoc]
    rw [e1a, e1a, hζπab, eabs]
  -- the right-hand side, likewise
  have hR : zetaMap (ceilPred ab) (isSharp_ceil ab) ≫
      (asrt (comprMap (ceilPred ab) ≫ ab) ≫ μ.hom ≫
        asrt (comprMap (ceilPred ba) ≫ ba) ≫ ν.hom) ≫
        comprMap (ceilPred ab) =
      (asrt ab ≫ zetaMap (ceilPred ab) (isSharp_ceil ab) ≫ μ.hom ≫
          comprMap (ceilPred ba)) ≫
        (asrt ba ≫ zetaMap (ceilPred ba) (isSharp_ceil ba) ≫ ν.hom ≫
          comprMap (ceilPred ab)) := by
    simp only [Category.assoc]
    rw [e1a, e2a, ← Category.assoc (comprMap (ceilPred ba))
      (zetaMap (ceilPred ba) (isSharp_ceil ba)), hπζba, Category.id_comp]
  -- so `asrt²_{ab̄} = ν ∘ asrt_{b̄a} ∘ μ ∘ asrt_{ab̄}` (`dagger-second-axiom-
  -- intermediate`), and `asrt_{ab̄}` is epic
  have hE1 : asrt (comprMap (ceilPred ab) ≫ ab) ≫
      asrt (comprMap (ceilPred ab) ≫ ab) =
      asrt (comprMap (ceilPred ab) ≫ ab) ≫ μ.hom ≫
        asrt (comprMap (ceilPred ba) ≫ ba) ≫ ν.hom := by
    refine (cancel_mono (comprMap (ceilPred ab))).mp ?_
    refine (cancel_epi (zetaMap (ceilPred ab) (isSharp_ceil ab))).mp ?_
    rw [hL, hR, hsq]
  have hE2 : asrt (comprMap (ceilPred ab) ≫ ab) =
      μ.hom ≫ asrt (comprMap (ceilPred ba) ≫ ba) ≫ ν.hom :=
    (cancel_epi (asrt (comprMap (ceilPred ab) ≫ ab))).mp hE1
  -- `ab̄ = 1 ∘ asrt_{ab̄} = 1 ∘ ν ∘ asrt_{b̄a} ∘ μ = b̄a ∘ μ`
  have hE3 : comprMap (ceilPred ab) ≫ ab =
      μ.hom ≫ comprMap (ceilPred ba) ≫ ba := by
    have h := congrArg (fun f => f ≫ truth (comprObj (ceilPred ab)))
      hE2
    simp only [Category.assoc] at h
    rw [(asrt_spec (comprMap (ceilPred ab) ≫ ab)).2, iso_isTotal ν.hom,
      (asrt_spec (comprMap (ceilPred ba) ≫ ba)).2] at h
    exact h
  refine ⟨?_, hE3⟩
  -- `ν ∘ μ ∘ asrt_{ab̄} = ν ∘ asrt_{b̄a} ∘ μ = asrt_{ab̄}`, and `asrt_{ab̄}` is epic
  have hE4 : μ.hom ≫ asrt (comprMap (ceilPred ba) ≫ ba) =
      asrt (comprMap (ceilPred ab) ≫ ab) ≫ μ.hom := by
    rw [hE3]
    exact asrt_iso hsqrt μ.hom (comprMap (ceilPred ba) ≫ ba)
  refine (cancel_epi (asrt (comprMap (ceilPred ab) ≫ ab))).mp ?_
  rw [Category.comp_id]
  conv_lhs => rw [← Category.assoc, ← hE4, Category.assoc]
  exact hE2.symm

/-- **219XI** (`dagger-iso-mu`, eff.tex:6249, Proposition): in a
†'-effectus, if `ν` is the unique isomorphism with
`asrt_a ∘ asrt_b = π_{⌈a&b⌉} ∘ ν ∘ ζ_{⌈b&a⌉} ∘ asrt_{b&a}`, then
`asrt_b ∘ asrt_a = asrt_{b&a} ∘ π_{⌈b&a⌉} ∘ ν⁻¹ ∘ ζ_{⌈a&b⌉}`. -/
theorem dagger_iso_mu [DaggerPrimeEffectus C] (a b : Pred X)
    (ν : comprObj (ceilPred (andThen b a)) ≅ comprObj (ceilPred (andThen a b)))
    (hν : asrt b ≫ asrt a =
      asrt (andThen b a) ≫
        zetaMap (ceilPred (andThen b a)) (isSharp_ceil _) ≫ ν.hom ≫
        comprMap (ceilPred (andThen a b))) :
    asrt a ≫ asrt b =
      zetaMap (ceilPred (andThen a b)) (isSharp_ceil _) ≫ ν.inv ≫
        comprMap (ceilPred (andThen b a)) ≫ asrt (andThen b a) := by
  -- `μ` is the iso for the reversed product (`pqqp-from-dagger`)
  obtain ⟨μ, hμ⟩ := asrt_comp_standard_form a b
  obtain ⟨hqab, hπζab, hζπab⟩ :=
    zetaMap_spec (ceilPred (andThen a b)) (isSharp_ceil (andThen a b))
  obtain ⟨hqba, -, hζπba⟩ :=
    zetaMap_spec (ceilPred (andThen b a)) (isSharp_ceil (andThen b a))
  haveI : Epi (zetaMap (ceilPred (andThen a b)) (isSharp_ceil (andThen a b))) :=
    quotient_basics_6 hqab
  have hZ1 : zetaMap (ceilPred (andThen a b)) (isSharp_ceil (andThen a b)) ≫
      truth (comprObj (ceilPred (andThen a b))) = ceilPred (andThen a b) := by
    rw [quotient_basics_5 hqab, eabasics_orth_orth]
  -- the second axiom of a †'-effectus, in the two standard forms
  have hsq : asrt (andThen a b) ≫ asrt (andThen a b) =
      (asrt (andThen a b) ≫
          zetaMap (ceilPred (andThen a b)) (isSharp_ceil (andThen a b)) ≫
          μ.hom ≫ comprMap (ceilPred (andThen b a))) ≫
        (asrt (andThen b a) ≫
          zetaMap (ceilPred (andThen b a)) (isSharp_ceil (andThen b a)) ≫
          ν.hom ≫ comprMap (ceilPred (andThen a b))) := by
    rw [← hμ, ← hν, DaggerPrimeEffectus.asrt_sq a b]
    simp only [Category.assoc]
  obtain ⟨hone, hbar⟩ := asrt_mu_inv μ ν hsq
  -- hence `μ = ν⁻¹`
  have hμν : μ.hom = ν.inv := by
    rw [← Category.comp_id μ.hom, ← ν.hom_inv_id, ← Category.assoc, hone,
      Category.id_comp]
  rw [hμν] at hμ hbar
  -- `l = π_{⌈ba⌉} ∘ ν⁻¹ ∘ ζ_{⌈ab⌉}` is pristine, with `1 ∘ l = ⌈ab⌉` and
  -- `im l = ⌈ba⌉`
  have hltruth : (zetaMap (ceilPred (andThen a b)) (isSharp_ceil _) ≫ ν.inv ≫
      comprMap (ceilPred (andThen b a))) ≫ truth X = ceilPred (andThen a b) := by
    simp only [Category.assoc]
    rw [compr_total (isComprehension_comprMap (ceilPred (andThen b a))),
      iso_isTotal ν.inv, hZ1]
  have hlpure : IsPure (zetaMap (ceilPred (andThen a b)) (isSharp_ceil _) ≫
      ν.inv ≫ comprMap (ceilPred (andThen b a))) :=
    upm_closed_pure (isPure_of_isQuotient hqab)
      (upm_closed_pure (isPure_of_isQuotient (quotient_basics_3 ν.inv))
        (isPure_comprehension C (isComprehension_comprMap _)))
  have hlim : imPred (zetaMap (ceilPred (andThen a b)) (isSharp_ceil _) ≫
      ν.inv ≫ comprMap (ceilPred (andThen b a))) = ceilPred (andThen b a) := by
    rw [imPred_comp_of_epi,
      (im_ineq (comprMap (ceilPred (andThen b a))) ν.inv).2 ν.inv inferInstance,
      (img_of_compr (ceilPred (andThen b a))).2 _ (isSharp_ceil _)]
  have hpris : Pristine (zetaMap (ceilPred (andThen a b)) (isSharp_ceil _) ≫
      ν.inv ≫ comprMap (ceilPred (andThen b a))) :=
    ⟨hlpure, by rw [hltruth]; exact isSharp_ceil _⟩
  -- `asrt_{⌈ab⌉} ∘ ζ_{⌈ab⌉} = ζ_{⌈ab⌉}`, so `l` is already in standard form
  have eabsZ : asrt (ceilPred (andThen a b)) ≫
      zetaMap (ceilPred (andThen a b)) (isSharp_ceil (andThen a b)) =
      zetaMap (ceilPred (andThen a b)) (isSharp_ceil (andThen a b)) :=
    (asrt_absorp_rule _ (isSharp_one _) (isSharp_ceil (andThen a b))).2.mp
      (by rw [hZ1]; exact pcm_preorder_refl _)
  -- so `l† = π_{⌈ab⌉} ∘ ν ∘ ζ_{⌈ba⌉}` (218IX.1, via 217II)
  have hdag : pureDagger _ hpris.1 =
      zetaMap (ceilPred (andThen b a)) (isSharp_ceil (andThen b a)) ≫ ν.hom ≫
        comprMap (ceilPred (andThen a b)) ≫ asrt (ceilPred (andThen a b)) := by
    refine (pureDagger_existsUnique _ hpris.1).unique
      (isDaggerOf_pureDagger _ hpris.1) ?_
    refine isDaggerOf_of_eq (isSharp_ceil (andThen a b))
      (isSharp_ceil (andThen b a))
      (by rw [hltruth]; exact ceil_of_isSharp (isSharp_ceil _))
      hlim ν.symm ?_ ?_
    · rw [hltruth, Iso.symm_hom,
        ← Category.assoc (asrt (ceilPred (andThen a b))), eabsZ]
    · rw [hltruth, Iso.symm_inv]
  -- `(a&b) ∘ l† = b&a` (using `dagger-seqprod-inversion` and `μ = ν⁻¹`)
  have hdagab : pureDagger _ hpris.1 ≫ andThen a b = andThen b a := by
    rw [hdag]
    simp only [Category.assoc]
    rw [asrt_ceil_comp, hbar, ← Category.assoc ν.hom ν.inv, ν.hom_inv_id,
      Category.id_comp, ← Category.assoc, hζπba, asrt_ceil_comp]
  -- 218IX.5 at `l` and `a&b ≤ ⌈a&b⌉ = 1 ∘ l`
  have hpr5 := asrt_pristine_reverse_5 hpris
    (p := andThen a b) (by rw [hltruth]; exact le_ceil _)
  rw [hdagab] at hpr5
  calc asrt a ≫ asrt b
      = asrt (andThen a b) ≫
        zetaMap (ceilPred (andThen a b)) (isSharp_ceil _) ≫ ν.inv ≫
          comprMap (ceilPred (andThen b a)) := hμ
    _ = (zetaMap (ceilPred (andThen a b)) (isSharp_ceil _) ≫ ν.inv ≫
          comprMap (ceilPred (andThen b a))) ≫ asrt (andThen b a) := hpr5.symm
    _ = _ := by simp only [Category.assoc]

/-- Helper: `pureDagger` respects equality of its argument (`IsPure` being a
`Prop`, the purity proofs need not be transported). -/
theorem pureDagger_congr [DaggerPrimeEffectus C] {f g : X ⟶ Y} (hf : IsPure f)
    (hg : IsPure g) (h : f = g) : pureDagger f hf = pureDagger g hg := by
  subst h; rfl

/-- Helper: `f† = g` as soon as `g` is *a* dagger of `f` (217I). -/
theorem pureDagger_eq [DaggerPrimeEffectus C] {f : X ⟶ Y} (hf : IsPure f)
    {g : Y ⟶ X} (h : IsDaggerOf f g) : pureDagger f hf = g :=
  (pureDagger_existsUnique f hf).unique (isDaggerOf_pureDagger f hf) h

/-- Helper: `im (θ ∘ f) = im f ∘ θ⁻¹` for an isomorphism `θ`. -/
theorem imPred_comp_iso (f : X ⟶ Y) (θ : Y ⟶ Z) [IsIso θ] :
    imPred (f ≫ θ) = inv θ ≫ imPred f := by
  refine imPred_eq _ ⟨?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc θ, IsIso.hom_inv_id, Category.id_comp,
      (isImage_imPred f).1, Category.assoc, iso_isTotal θ]
  · intro q hq
    have h : f ≫ (θ ≫ q) = f ≫ truth Y := by
      rw [← Category.assoc, hq, Category.assoc, iso_isTotal θ]
    have h2 := comp_le_comp (inv θ) ((isImage_imPred f).2 _ h)
    rwa [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at h2

/-- Helper for the daggered squares (used in 219XIV): if `m = π_J ∘ δ` for an
isomorphism `δ` and `m ∘ z = asrt_J`, then `δ ∘ z = ζ_J` — a map into a
comprehension for `J` composing with it to `asrt_J` *is* the corresponding
quotient, comprehensions being monic.  (This is the mirror image of the
uniqueness step of the published solution to **219IX**, `bsols.tex:3286`, which
instead checks `z ∘ π_J = id` on a map already known to be a quotient.) -/
theorem zetaMap_eq_of_compr {J : Pred Y} (hJ : IsSharp J) {A : C}
    (δ : A ≅ comprObj J) {m : A ⟶ Y} (hm : δ.hom ≫ comprMap J = m)
    {z : Y ⟶ A} (hz : z ≫ m = asrt J) : z ≫ δ.hom = zetaMap J hJ := by
  have : Mono (comprMap J) := compr_basics_5 (isComprehension_comprMap J)
  refine (cancel_mono (comprMap J)).mp ?_
  rw [Category.assoc, hm, hz, (zetaMap_spec J hJ).2.2]

/-- Helper, dual to `zetaMap_eq_of_compr` (used in 219XIV): if `z = β ∘ ζ_J` for
an isomorphism `β` and `c ∘ z = asrt_J`, then `β⁻¹ ∘ π_J = c`, quotients being
epic.  (This is the mirror image of the uniqueness step of **219VII**,
eff.tex:6186, which instead checks `ζ_J ∘ c = id` on a map already known to be a
comprehension.) -/
theorem comprMap_eq_of_zeta {J : Pred Y} (hJ : IsSharp J) {B : C}
    (β : comprObj J ≅ B) {z : Y ⟶ B} (hz : zetaMap J hJ ≫ β.hom = z)
    {c : B ⟶ Y} (hc : z ≫ c = asrt J) : β.inv ≫ comprMap J = c := by
  have : Epi (zetaMap J hJ) := quotient_basics_6 (zetaMap_spec J hJ).1
  have : Epi z := by rw [← hz]; exact epi_comp _ _
  refine (cancel_epi z).mp ?_
  rw [← hz, Category.assoc, ← Category.assoc β.hom, β.hom_inv_id,
    Category.id_comp, (zetaMap_spec J hJ).2.2, hz]
  exact hc.symm

/-- Helper: `im (π_i ∘ π_j) = j ∘ ζ_i` for sharp `i` on `Y` and sharp `j` on
`{Y|i}` — the pushforward of `j` along `π_i`.  (`≥` is the universal property of
the image; `≤` uses `j ≤ im (π_i ∘ π_j) ∘ π_i` and `asrt_i ∘ im (π_i ∘ π_j) =
im (π_i ∘ π_j)`.) -/
theorem imPred_compr_compr {i : Pred Y} (hi : IsSharp i)
    {j : Pred (comprObj i)} (hj : IsSharp j) :
    imPred (comprMap j ≫ comprMap i) = zetaMap i hi ≫ j := by
  obtain ⟨-, hπζ, hζπ⟩ := zetaMap_spec i hi
  set I := imPred (comprMap j ≫ comprMap i) with hI
  have hIle : I ≼ i := by
    have h := (im_ineq (comprMap i) (comprMap j)).1
    rwa [(img_of_compr i).2 i hi] at h
  refine eabasics_le_antisymm ?_ ?_
  · -- `im` is least: `(π_i ∘ π_j) ∘ (j ∘ ζ_i) = (π_i ∘ π_j) ∘ 1`
    refine (isImage_imPred _).2 _ ?_
    rw [Category.assoc, ← Category.assoc (comprMap i) (zetaMap i hi) j, hπζ,
      Category.id_comp, (isComprehension_comprMap j).1, Category.assoc,
      compr_total (isComprehension_comprMap i)]
  · -- `j ≤ π_i ∘ I` since `π_j ∘ (π_i ∘ I) = π_j ∘ 1`, so `j ∘ ζ_i ≤ I ∘ asrt_i = I`
    have hj1 : j ≼ (comprMap i ≫ I) := by
      have h : comprMap j ≫ (comprMap i ≫ I) = comprMap j ≫ truth (comprObj i) := by
        rw [← Category.assoc, (isImage_imPred (comprMap j ≫ comprMap i)).1,
          Category.assoc, compr_total (isComprehension_comprMap i)]
      have h2 := (isImage_imPred (comprMap j)).2 _ h
      rwa [(img_of_compr j).2 j hj] at h2
    have h2 := comp_le_comp (zetaMap i hi) hj1
    rw [← Category.assoc, hζπ] at h2
    have h3 : asrt i ≫ I = I := by
      have := ((asrt_absorp_rule I (isSharp_one (effObj C)) hi).2).mp
        (by rw [truth_effObj_eq_id, Category.comp_id]; exact hIle)
      exact this
    rwa [h3] at h2

/-- Helper: in a †'-effectus every predicate has a square root (the first
axiom, in the form `zeta_through_asrt` and `asrt_iso` want it). -/
theorem exists_sqrt_pred [DaggerPrimeEffectus C] {W : C} (p : Pred W) :
    ∃ q, andThen q q = p := (DaggerPrimeEffectus.sqrt_existsUnique p).exists

/-- Helper (216X at `ζ_i`): `asrt_{j ∘ ζ_i} = π_i ∘ asrt_j ∘ ζ_i`. -/
theorem asrt_zeta_compr [DaggerPrimeEffectus C] {i : Pred Y} (hi : IsSharp i)
    (j : Pred (comprObj i)) :
    zetaMap i hi ≫ asrt j ≫ comprMap i = asrt (zetaMap i hi ≫ j) := by
  obtain ⟨hq, hπζ, hζπ⟩ := zetaMap_spec i hi
  have hz := zeta_through_asrt (fun p => exists_sqrt_pred p) hi
    (quotcompr_diamond_adjoint hi) j
  have hJle : (zetaMap i hi ≫ j) ≼ i := by
    have h := comp_le_comp (zetaMap i hi) (pred_le_truth j)
    rwa [quotient_basics_5 hq, eabasics_orth_orth] at h
  have habs : asrt (zetaMap i hi ≫ j) ≫ asrt i = asrt (zetaMap i hi ≫ j) :=
    (asrt_absorp_rule _ hi hi).1.mp
      (by rw [imPred_asrt]; exact (ceil_le_iff_of_isSharp hi).mpr hJle)
  calc zetaMap i hi ≫ asrt j ≫ comprMap i
      = (zetaMap i hi ≫ asrt j) ≫ comprMap i := by rw [Category.assoc]
    _ = (asrt (zetaMap i hi ≫ j) ≫ zetaMap i hi) ≫ comprMap i := by rw [hz]
    _ = asrt (zetaMap i hi ≫ j) ≫ asrt i := by rw [Category.assoc, hζπ]
    _ = asrt (zetaMap i hi ≫ j) := habs

/-- **219XI** (`dagger-iso-mu`, eff.tex:6249, Proposition), restated as the
functoriality of the dagger on assert maps: `(asrt_b ∘ asrt_a)† =
asrt_a ∘ asrt_b`.  (216XI.Ax2 puts `asrt_b ∘ asrt_a` in standard form; 219XI
identifies the resulting formula for the dagger with `asrt_a ∘ asrt_b`.) -/
theorem pureDagger_asrt_comp [DaggerPrimeEffectus C] (a b : Pred X) :
    pureDagger (asrt a ≫ asrt b)
        (upm_closed_pure (asrt_spec a).1.1 (asrt_spec b).1.1) =
      asrt b ≫ asrt a := by
  have htruth : (asrt a ≫ asrt b) ≫ truth X = andThen a b := by
    rw [Category.assoc, (asrt_spec b).2]; rfl
  have hadj : DiamondAdjoint (asrt a ≫ asrt b) (asrt b ≫ asrt a) := by
    have hpsa : diaPull (asrt a) = diaPush (asrt a) :=
      diamond_squares_2 (asrt_spec a).1
    have hqsa : diaPull (asrt b) = diaPush (asrt b) :=
      diamond_squares_2 (asrt_spec b).1
    change diaPull _ = diaPush _
    funext s
    rw [diaPull_comp, diaPush_comp, hpsa, hqsa]
  have him : imPred (asrt a ≫ asrt b) = ceilPred (andThen b a) := by
    have h := exc_diamond_adj_2 hadj
    rwa [Category.assoc, (asrt_spec a).2] at h
  obtain ⟨ν, hν⟩ := asrt_comp_standard_form a b
  refine pureDagger_eq _ (isDaggerOf_of_eq (isSharp_ceil (andThen a b))
    (isSharp_ceil (andThen b a)) (by rw [htruth]) him ν ?_ ?_)
  · rw [htruth]; exact hν
  · rw [htruth]; exact dagger_iso_mu b a ν hν

/-- The map `ζ_e ∘ asrt_p ∘ π_t` of 219XIV is pure. -/
theorem isPure_compr_asrt_zeta [DaggerPrimeEffectus C] {t e : Pred Y} (he : IsSharp e)
    (p : Pred Y) : IsPure (comprMap t ≫ asrt p ≫ zetaMap e he) :=
  upm_closed_pure (isPure_comprehension C (isComprehension_comprMap t))
    (upm_closed_pure (asrt_spec p).1.1
      (isPure_of_isQuotient (zetaMap_spec e he).1))

/-- **219XIV** (`dagger-iso-chi2`, eff.tex:6412, Lemma), in the general form
that avoids the Setting 219II: for sharp `t`, `e` and a predicate `p` with
`⌈p⌉ ≤ e`,
`(ζ_e ∘ asrt_p ∘ π_t)† = ζ_t ∘ asrt_p ∘ π_e`.
(The thesis states this for `e = ⌈p⌉`, and only for the `χ` of its Setting; the
proof is the thesis's: put `asrt_p ∘ asrt_t` in standard form using the standard
form `χ` of `ζ_e ∘ asrt_p ∘ π_t` together with the two auxiliary isomorphisms
`α₂`, `β₂` and their daggered versions, then apply 219XI.) -/
theorem pureDagger_compr_asrt_zeta [DaggerPrimeEffectus C] {t e : Pred Y} (ht : IsSharp t)
    (he : IsSharp e) {p : Pred Y} (hpe : ceilPred p ≼ e) :
    pureDagger (comprMap t ≫ asrt p ≫ zetaMap e he) (isPure_compr_asrt_zeta he p) =
    comprMap e ≫ asrt p ≫ zetaMap t ht := by
  obtain ⟨hqt, hπζt, hζπt⟩ := zetaMap_spec t ht
  obtain ⟨hqe, hπζe, hζπe⟩ := zetaMap_spec e he
  have hpure := isPure_compr_asrt_zeta (t := t) he p
  have hZe : zetaMap e he ≫ truth (comprObj e) = e := by
    rw [quotient_basics_5 hqe, eabasics_orth_orth]
  have hZt : zetaMap t ht ≫ truth (comprObj t) = t := by
    rw [quotient_basics_5 hqt, eabasics_orth_orth]
  have habs : asrt p ≫ asrt e = asrt p :=
    (asrt_absorp_rule (asrt p) he he).1.mp (by rw [imPred_asrt]; exact hpe)
  have hpe' : asrt p ≫ e = p := by
    refine eabasics_le_antisymm ?_ ?_
    · have h := comp_le_comp (asrt p) (pred_le_truth e)
      rwa [(asrt_spec p).2] at h
    · have h := comp_le_comp (asrt p) hpe
      rwa [asrt_comp_ceil] at h
  -- the truth and image of `A`
  set u := comprMap t ≫ p with hu
  have hA1 : (comprMap t ≫ asrt p ≫ zetaMap e he) ≫ truth (comprObj e) = u := by
    simp only [Category.assoc]
    rw [hZe, hpe']
  set v := imPred (comprMap t ≫ asrt p ≫ zetaMap e he) with hv
  have hvs : IsSharp v := isSharp_imPred C _
  obtain ⟨χ, hχ⟩ := standard_form_of_eq hpure (isSharp_ceil u) hvs (by rw [hA1]) rfl
  have hdag : pureDagger (comprMap t ≫ asrt p ≫ zetaMap e he) hpure =
      zetaMap v hvs ≫ χ.inv ≫ comprMap (ceilPred u) ≫ asrt u :=
    pureDagger_eq hpure (isDaggerOf_of_eq (isSharp_ceil u) hvs (by rw [hA1]) rfl
      χ hχ (by rw [hA1]))
  rw [hA1] at hχ
  set tp := andThen t p with htp
  set pt := andThen p t with hpt
  -- (1) `⌈u⌉ ∘ ζ_t = ⌈t & p⌉`
  have hzt_sharp : SharpMap (zetaMap t ht) :=
    DaggerPrimeEffectus.quot_sharp (DiamondEffectus.orth_sharp ht) hqt
  have hzu : zetaMap t ht ≫ u = tp := by
    rw [hu, ← Category.assoc, hζπt, htp]
    rfl
  have hceil_u : zetaMap t ht ≫ ceilPred u = ceilPred tp := by
    rw [← (sharp_ceil _).mp hzt_sharp u, hzu]
  have htple : ceilPred tp ≼ t := by
    have h1 : tp ≼ t := by
      have h := comp_le_comp (asrt t) (pred_le_truth p)
      rwa [(asrt_spec t).2] at h
    have h2 := ceilPred_mono h1
    rwa [ceil_of_isSharp ht] at h2
  -- (2) the isomorphism `β₂`
  have hqcomp : IsQuotient (orth (ceilPred tp))
      (zetaMap t ht ≫ zetaMap (ceilPred u) (isSharp_ceil u)) := by
    have h := quotients_composition hqt
      (zetaMap_spec (ceilPred u) (isSharp_ceil u)).1
    rwa [hceil_u] at h
  obtain ⟨β₂, hβiso, hβ, -⟩ :=
    quotient_basics_2 hqcomp (zetaMap_spec (ceilPred tp) (isSharp_ceil tp)).1
  have := hβiso
  -- (3) the daggered version of `β₂`
  have hβdag : (inv β₂) ≫ comprMap (ceilPred tp) =
      comprMap (ceilPred u) ≫ comprMap t := by
    have h := comprMap_eq_of_zeta (isSharp_ceil tp) (asIso β₂) hβ
      (c := comprMap (ceilPred u) ≫ comprMap t) ?_
    · rw [asIso_inv] at h; exact h
    have hz := zeta_through_asrt (fun q => exists_sqrt_pred q) ht
      (quotcompr_diamond_adjoint ht) (ceilPred u)
    have habs2 : asrt (ceilPred tp) ≫ asrt t = asrt (ceilPred tp) :=
      (asrt_absorp_rule (asrt (ceilPred tp)) ht ht).1.mp
        (by rw [imPred_asrt, ceil_of_isSharp (isSharp_ceil tp)]; exact htple)
    calc (zetaMap t ht ≫ zetaMap (ceilPred u) (isSharp_ceil u)) ≫
          comprMap (ceilPred u) ≫ comprMap t
        = zetaMap t ht ≫ (zetaMap (ceilPred u) (isSharp_ceil u) ≫
            comprMap (ceilPred u)) ≫ comprMap t := by simp only [Category.assoc]
      _ = (zetaMap t ht ≫ asrt (ceilPred u)) ≫ comprMap t := by
          rw [(zetaMap_spec (ceilPred u) (isSharp_ceil u)).2.2]
          simp only [Category.assoc]
      _ = asrt (ceilPred tp) ≫ zetaMap t ht ≫ comprMap t := by
          rw [hz, hceil_u]; simp only [Category.assoc]
      _ = asrt (ceilPred tp) := by rw [hζπt, habs2]
  -- (4) the isomorphism `α₂`
  have himA : imPred (comprMap t ≫ asrt p) = ceilPred pt :=
    (congrArg Subtype.val
      (congrFun (diamond_squares_2 (asrt_spec p).1) ⟨t, ht⟩)).symm
  have hAπe : (comprMap t ≫ asrt p ≫ zetaMap e he) ≫ comprMap e =
      comprMap t ≫ asrt p := by
    simp only [Category.assoc]; rw [hζπe, habs]
  have hepiA : Epi (asrt u ≫ zetaMap (ceilPred u) (isSharp_ceil u) ≫ χ.hom) := by
    have h : Epi (asrt u ≫ zetaMap (ceilPred u) (isSharp_ceil u)) :=
      quotient_basics_6 (zeta_asrt_quot u)
    rw [← Category.assoc]; exact epi_comp _ _
  have himPv : imPred (comprMap v ≫ comprMap e) = ceilPred pt := by
    have he1 : (comprMap t ≫ asrt p ≫ zetaMap e he) ≫ comprMap e =
        (asrt u ≫ zetaMap (ceilPred u) (isSharp_ceil u) ≫ χ.hom) ≫
          (comprMap v ≫ comprMap e) := by
      conv_lhs => rw [hχ]
      simp only [Category.assoc]
    rw [← imPred_comp_of_epi (asrt u ≫ zetaMap (ceilPred u) (isSharp_ceil u) ≫
      χ.hom) (comprMap v ≫ comprMap e), ← he1, hAπe, himA]
  obtain ⟨r₂, hr₂⟩ := upm_closed_compr (isComprehension_comprMap v)
    (isComprehension_comprMap e)
  have hcompr₂ : IsComprehension (ceilPred pt) (comprMap v ≫ comprMap e) := by
    have h := isComprehension_imPred hr₂
    rwa [himPv] at h
  obtain ⟨α₂, hαiso, hα, -⟩ :=
    compr_basics_2 hcompr₂ (isComprehension_comprMap (ceilPred pt))
  have := hαiso
  -- (5) the daggered version of `α₂`
  have hzev : zetaMap e he ≫ v = ceilPred pt := by
    rw [← imPred_compr_compr he hvs, himPv]
  have hαdag : (zetaMap e he ≫ zetaMap v hvs) ≫ α₂ =
      zetaMap (ceilPred pt) (isSharp_ceil pt) := by
    refine zetaMap_eq_of_compr (isSharp_ceil pt) (asIso α₂) hα ?_
    rw [Category.assoc, ← Category.assoc (zetaMap v hvs),
      (zetaMap_spec v hvs).2.2, asrt_zeta_compr he v, hzev]
  -- (6) the isomorphism `ν` of 219XI
  have hzu2 : zetaMap t ht ≫ asrt u = asrt tp ≫ zetaMap t ht := by
    have h := zeta_through_asrt (fun q => exists_sqrt_pred q) ht
      (quotcompr_diamond_adjoint ht) u
    rwa [hzu] at h
  have hν : asrt t ≫ asrt p = asrt tp ≫ zetaMap (ceilPred tp) (isSharp_ceil tp) ≫
      (asIso β₂ ≪≫ χ ≪≫ asIso α₂).hom ≫ comprMap (ceilPred pt) := by
    calc asrt t ≫ asrt p
        = (zetaMap t ht ≫ comprMap t) ≫ (asrt p ≫ zetaMap e he ≫ comprMap e) := by
          rw [hζπt, hζπe, habs]
      _ = zetaMap t ht ≫ (comprMap t ≫ asrt p ≫ zetaMap e he) ≫ comprMap e := by
          simp only [Category.assoc]
      _ = zetaMap t ht ≫ (asrt u ≫ zetaMap (ceilPred u) (isSharp_ceil u) ≫
            χ.hom ≫ comprMap v) ≫ comprMap e := by rw [hχ]
      _ = (zetaMap t ht ≫ asrt u) ≫ zetaMap (ceilPred u) (isSharp_ceil u) ≫
            χ.hom ≫ comprMap v ≫ comprMap e := by simp only [Category.assoc]
      _ = asrt tp ≫ (zetaMap t ht ≫ zetaMap (ceilPred u) (isSharp_ceil u)) ≫
            χ.hom ≫ (comprMap v ≫ comprMap e) := by
          rw [hzu2]; simp only [Category.assoc]
      _ = asrt tp ≫ (zetaMap (ceilPred tp) (isSharp_ceil tp) ≫ β₂) ≫ χ.hom ≫
            (α₂ ≫ comprMap (ceilPred pt)) := by rw [hβ, hα]
      _ = _ := by simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  have hmu := dagger_iso_mu p t (asIso β₂ ≪≫ χ ≪≫ asIso α₂) hν
  -- (7) the final computation
  have habsζ : asrt t ≫ zetaMap t ht = zetaMap t ht :=
    (asrt_absorp_rule (zetaMap t ht) (isSharp_one _) ht).2.mp
      (by rw [hZt]; exact pcm_preorder_refl _)
  have hfront : comprMap e ≫ zetaMap (ceilPred pt) (isSharp_ceil pt) ≫ inv α₂ =
      zetaMap v hvs := by
    rw [← hαdag]
    simp only [Category.assoc]
    rw [IsIso.hom_inv_id, Category.comp_id, ← Category.assoc, hπζe,
      Category.id_comp]
  have htail : comprMap t ≫ asrt tp ≫ zetaMap t ht = asrt u := by
    rw [← hzu2, ← Category.assoc, hπζt, Category.id_comp]
  rw [hdag]
  symm
  calc comprMap e ≫ asrt p ≫ zetaMap t ht
      = comprMap e ≫ (asrt p ≫ asrt t) ≫ zetaMap t ht := by
        rw [Category.assoc, habsζ]
    _ = comprMap e ≫ (zetaMap (ceilPred pt) (isSharp_ceil pt) ≫
          (asIso β₂ ≪≫ χ ≪≫ asIso α₂).inv ≫ comprMap (ceilPred tp) ≫ asrt tp) ≫
          zetaMap t ht := by rw [hmu]
    _ = (comprMap e ≫ zetaMap (ceilPred pt) (isSharp_ceil pt) ≫ inv α₂) ≫ χ.inv ≫
          (inv β₂ ≫ comprMap (ceilPred tp)) ≫ asrt tp ≫ zetaMap t ht := by
        simp only [Iso.trans_inv, asIso_inv, Category.assoc]
    _ = zetaMap v hvs ≫ χ.inv ≫ (comprMap (ceilPred u) ≫ comprMap t) ≫
          asrt tp ≫ zetaMap t ht := by rw [hfront, hβdag]
    _ = zetaMap v hvs ≫ χ.inv ≫ comprMap (ceilPred u) ≫
          (comprMap t ≫ asrt tp ≫ zetaMap t ht) := by simp only [Category.assoc]
    _ = zetaMap v hvs ≫ χ.inv ≫ comprMap (ceilPred u) ≫ asrt u := by rw [htail]

/-- Helper: the truth `1 ∘ M` of a map given in the standard form 212III. -/
theorem standard_form_truth {M : X ⟶ Y} {c : Pred X} {i : Pred Y}
    (Θ : comprObj (ceilPred c) ≅ comprObj i)
    (hM : M = asrt c ≫ zetaMap (ceilPred c) (isSharp_ceil c) ≫ Θ.hom ≫ comprMap i) :
    M ≫ truth Y = c := by
  rw [hM]
  simp only [Category.assoc]
  rw [compr_total (isComprehension_comprMap i), iso_isTotal Θ.hom,
    quotient_basics_5 (zetaMap_spec (ceilPred c) (isSharp_ceil c)).1,
    eabasics_orth_orth, asrt_comp_ceil]

/-- Helper: the image `im M` of a map given in the standard form 212III. -/
theorem standard_form_imPred {M : X ⟶ Y} {c : Pred X} {i : Pred Y} (hi : IsSharp i)
    (Θ : comprObj (ceilPred c) ≅ comprObj i)
    (hM : M = asrt c ≫ zetaMap (ceilPred c) (isSharp_ceil c) ≫ Θ.hom ≫ comprMap i) :
    imPred M = i := by
  have hepi : Epi (asrt c ≫ zetaMap (ceilPred c) (isSharp_ceil c) ≫ Θ.hom) := by
    have h : Epi (asrt c ≫ zetaMap (ceilPred c) (isSharp_ceil c)) :=
      quotient_basics_6 (zeta_asrt_quot c)
    rw [← Category.assoc]; exact epi_comp _ _
  have he : M = (asrt c ≫ zetaMap (ceilPred c) (isSharp_ceil c) ≫ Θ.hom) ≫ comprMap i := by
    rw [hM]; simp only [Category.assoc]
  rw [he, imPred_comp_of_epi, (img_of_compr i).2 i hi]

/-! ### The Setting 219II (parsec 219) -/

/-- Helper for `dagger_iso_chi` (the image computation of eff.tex:5989):
`IM (ζ_{⌈p⌉} ∘ asrt_p ∘ π_t) = ⌈t ∘ asrt_p ∘ π_{⌈p⌉}⌉`, by 218II. -/
theorem dagger_setting_im_chi [DaggerPrimeEffectus C] {t : Pred Y} (ht : IsSharp t)
    (p : Pred Y) :
    imPred (comprMap t ≫ asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p)) =
      ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t) := by
  have hpsa : diaPull (asrt p) = diaPush (asrt p) :=
    diamond_squares_2 (asrt_spec p).1
  have hadj : diaPull (comprMap (ceilPred p)) =
      diaPush (zetaMap (ceilPred p) (isSharp_ceil p)) :=
    quotcompr_diamond_adjoint (isSharp_ceil p)
  have key : diaPush (asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p)) ⟨t, ht⟩ =
      diaPull (comprMap (ceilPred p)) (diaPull (asrt p) ⟨t, ht⟩) := by
    rw [diaPush_comp (asrt p) (zetaMap (ceilPred p) (isSharp_ceil p)) ⟨t, ht⟩, ← hadj, ← hpsa]
  have h1 := congrArg Subtype.val key
  refine h1.trans ?_
  show ceilPred (comprMap (ceilPred p) ≫ ceilPred (asrt p ≫ t)) = _
  rw [ceiling_within_ceiling]

/-- Helper for `dagger_iso_chi` (the truth computation of eff.tex:5987):
`1 ∘ ζ_{⌈p⌉} ∘ asrt_p ∘ π_t = p ∘ π_t`, by `asrt-absorp-rule`. -/
theorem dagger_setting_truth_chi [DaggerPrimeEffectus C] (t p : Pred Y) :
    (comprMap t ≫ asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p)) ≫
      truth (comprObj (ceilPred p)) = comprMap t ≫ p := by
  simp only [Category.assoc]
  rw [quotient_basics_5 (zetaMap_spec (ceilPred p) (isSharp_ceil p)).1,
    eabasics_orth_orth, asrt_comp_ceil]

/-- **219II** (`dagger-setting`, eff.tex:5993, eq. `dagger-iso-chi`): in the
Setting 219II there is a (unique) isomorphism `χ` with
`ζ_{⌈p⌉} ∘ asrt_p ∘ π_t = π_{⌈t ∘ asrt_p ∘ π_{⌈p⌉}⌉} ∘ χ ∘ ζ_{⌈p ∘ π_t⌉} ∘
asrt_{p ∘ π_t}`.  (The truth of `ζ_{⌈p⌉} ∘ asrt_p ∘ π_t` is `p ∘ π_t` by
`asrt-absorp-rule`, its image is `⌈t ∘ asrt_p ∘ π_{⌈p⌉}⌉` by 218II.) -/
theorem dagger_iso_chi [DaggerPrimeEffectus C] {t : Pred Y} (ht : IsSharp t)
    (p : Pred Y) :
    ∃ χ : comprObj (ceilPred (comprMap t ≫ p)) ≅
        comprObj (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)),
      comprMap t ≫ asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p) =
        asrt (comprMap t ≫ p) ≫
          zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _) ≫ χ.hom ≫
          comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) := by
  obtain ⟨χ, hχ⟩ := standard_form_of_eq (isPure_compr_asrt_zeta (isSharp_ceil p) p)
    (isSharp_ceil (comprMap t ≫ p)) (isSharp_ceil _)
    (by rw [dagger_setting_truth_chi]) (dagger_setting_im_chi ht p)
  rw [dagger_setting_truth_chi] at hχ
  exact ⟨χ, hχ⟩

/-- **219II** (`dagger-setting`, eff.tex:6017, eq. `dagger-iso-omega`): in the
Setting 219II there is a (unique) isomorphism `ω` with
`asrt_{p ∘ k} ∘ asrt_q = π_{⌈p ∘ k⌉} ∘ ω ∘ ζ_{⌈p ∘ g⌉} ∘ asrt_{p ∘ g}`.
(Its truth is `p ∘ g`; its image is `⌈p ∘ k⌉` because `p ∘ k ≤ ⌈q⌉`.) -/
theorem dagger_iso_omega [DaggerPrimeEffectus C] {g : X ⟶ Y} {q : Pred X} {k : X ⟶ Y}
    (hgk : g = asrt q ≫ k) (hk : k ≫ truth Y = ceilPred q) (p : Pred Y) :
    ∃ ω : comprObj (ceilPred (g ≫ p)) ≅ comprObj (ceilPred (k ≫ p)),
      asrt q ≫ asrt (k ≫ p) =
        asrt (g ≫ p) ≫ zetaMap (ceilPred (g ≫ p)) (isSharp_ceil _) ≫ ω.hom ≫
          comprMap (ceilPred (k ≫ p)) := by
  have hpure : IsPure (asrt q ≫ asrt (k ≫ p)) :=
    upm_closed_pure (asrt_spec q).1.1 (asrt_spec _).1.1
  have htruth : (asrt q ≫ asrt (k ≫ p)) ≫ truth X = g ≫ p := by
    rw [hgk]; simp only [Category.assoc]; rw [(asrt_spec (k ≫ p)).2]
  obtain ⟨ν, hν⟩ := asrt_comp_standard_form q (k ≫ p)
  have him0 : imPred (asrt q ≫ asrt (k ≫ p)) = ceilPred (andThen (k ≫ p) q) :=
    standard_form_imPred (isSharp_ceil _) ν hν
  have hle : ceilPred (k ≫ p) ≼ ceilPred q := by
    have h1 : (k ≫ p) ≼ ceilPred q := by
      have h := comp_le_comp k (pred_le_truth p)
      rwa [hk] at h
    have h2 := ceilPred_mono h1
    rwa [ceil_of_isSharp (isSharp_ceil q)] at h2
  have hqq : asrt (k ≫ p) ≫ ceilPred q = asrt (k ≫ p) ≫ truth X := by
    refine eabasics_le_antisymm (comp_le_comp _ (pred_le_truth _)) ?_
    rw [← (isImage_imPred (asrt (k ≫ p))).1]
    exact comp_le_comp _ (by rw [imPred_asrt]; exact hle)
  have him : imPred (asrt q ≫ asrt (k ≫ p)) = ceilPred (k ≫ p) := by
    rw [him0]
    show ceilPred (asrt (k ≫ p) ≫ q) = _
    rw [← ceiling_within_ceiling q (asrt (k ≫ p)), hqq, (asrt_spec (k ≫ p)).2]
  obtain ⟨ω, hω⟩ := standard_form_of_eq hpure (isSharp_ceil _) (isSharp_ceil _)
    (by rw [htruth]) him
  rw [htruth] at hω
  exact ⟨ω, hω⟩

/-- **219II** (`dagger-setting`, eff.tex:6035, eq. `dagger-iso-beta`): in the
Setting 219II there is an isomorphism `β` with
`ζ_{⌈p ∘ π_t⌉} ∘ ψ ∘ ζ_{⌈q⌉} = β ∘ ζ_{⌈p ∘ k⌉}` — quotients are closed under
composition (199IX) and `⌈p ∘ π_t⌉ ∘ ψ ∘ ζ_{⌈q⌉} = ⌈p ∘ k⌉` by 210II. -/
theorem dagger_iso_beta [DaggerPrimeEffectus C] {q : Pred X} {t : Pred Y}
    (ψ : comprObj (ceilPred q) ≅ comprObj t) {k : X ⟶ Y}
    (hk : k = zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫ comprMap t) (p : Pred Y) :
    ∃ β : comprObj (ceilPred (k ≫ p)) ≅ comprObj (ceilPred (comprMap t ≫ p)),
      zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫
          zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _) =
        zetaMap (ceilPred (k ≫ p)) (isSharp_ceil _) ≫ β.hom := by
  have hmq : IsQuotient (orth (ceilPred q))
      (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) :=
    quotient_basics_1 (zetaMap_spec (ceilPred q) (isSharp_ceil q)).1 ψ.hom
  have hmsharp : SharpMap (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) :=
    DaggerPrimeEffectus.quot_sharp (DiamondEffectus.orth_sharp (isSharp_ceil q)) hmq
  have hmu : (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) ≫
      ceilPred (comprMap t ≫ p) = ceilPred (k ≫ p) := by
    rw [← (sharp_ceil _).mp hmsharp (comprMap t ≫ p)]
    refine congrArg ceilPred ?_
    rw [hk]; simp only [Category.assoc]
  have hcomp : IsQuotient (orth (ceilPred (k ≫ p)))
      ((zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) ≫
        zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _)) := by
    have h := quotients_composition hmq
      (zetaMap_spec (ceilPred (comprMap t ≫ p)) (isSharp_ceil _)).1
    rwa [hmu] at h
  obtain ⟨β, hβiso, hβ, -⟩ := quotient_basics_2 hcomp
    (zetaMap_spec (ceilPred (k ≫ p)) (isSharp_ceil _)).1
  have := hβiso
  refine ⟨asIso β, ?_⟩
  rw [asIso_hom, hβ]
  simp only [Category.assoc]

/-- Helper: `ζ_s ∘ φ⁻¹` is a sharp map. -/
theorem sharpMap_zeta_comp_iso [DaggerPrimeEffectus C] {s : Pred Z} (hs : IsSharp s)
    {W : C} (θ : comprObj s ⟶ W) [IsIso θ] : SharpMap (zetaMap s hs ≫ θ) := by
  have hzs : SharpMap (zetaMap s hs) :=
    DaggerPrimeEffectus.quot_sharp (DiamondEffectus.orth_sharp hs) (zetaMap_spec s hs).1
  intro r hr
  rw [Category.assoc]
  exact hzs _ ⟨_, _, isImage_compr_comp_inv θ hr⟩

/-- **219II** (`dagger-setting`, eff.tex:6066, eq. `dagger-iso-alpha`): in the
Setting 219II there is a (unique) isomorphism `α` with
`π_s ∘ φ ∘ π_{⌈t ∘ asrt_p ∘ π_{⌈p⌉}⌉} = π_{⌈t ∘ f†⌉} ∘ α`.  (By 211XI the
left-hand side is a comprehension; its image is
`⌈t ∘ asrt_p ∘ π_{⌈p⌉} ∘ φ⁻¹ ∘ ζ_s⌉ = ⌈t ∘ f†⌉` by 210II and, where the point
cites 218II for the value `im (π_i ∘ π_j) = j ∘ ζ_i`, by `imPred_compr_compr`,
which proves that same value from the universal property of the image.) -/
theorem dagger_iso_alpha [DaggerPrimeEffectus C] {s : Pred Z} (hs : IsSharp s)
    {p : Pred Y} (φ : comprObj (ceilPred p) ≅ comprObj s) (t : Pred Y) {d : Z ⟶ Y}
    (hd : d = zetaMap s hs ≫ φ.inv ≫ comprMap (ceilPred p) ≫ asrt p) :
    ∃ α : comprObj (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≅
        comprObj (ceilPred (d ≫ t)),
      comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≫ φ.hom ≫ comprMap s =
        α.hom ≫ comprMap (ceilPred (d ≫ t)) := by
  have hcomb : SharpMap (zetaMap s hs ≫ φ.inv) := sharpMap_zeta_comp_iso hs φ.inv
  have hkey : zetaMap s hs ≫ φ.inv ≫
      ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t) = ceilPred (d ≫ t) := by
    rw [hd, show (zetaMap s hs ≫ φ.inv ≫ comprMap (ceilPred p) ≫ asrt p) ≫ t =
        (zetaMap s hs ≫ φ.inv) ≫ (comprMap (ceilPred p) ≫ asrt p ≫ t) from by
      simp only [Category.assoc],
      (sharp_ceil _).mp hcomb (comprMap (ceilPred p) ≫ asrt p ≫ t)]
    simp only [Category.assoc]
  have hinv : inv φ.hom = φ.inv := by simp
  have hjs : IsSharp (φ.inv ≫ ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) := by
    have h := isSharp_imPred C
      (comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≫ φ.hom)
    rwa [imPred_comp_iso, hinv,
      (img_of_compr (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t))).2 _
        (isSharp_ceil _)] at h
  have hc1 : IsComprehension (φ.inv ≫ ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t))
      (comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≫ φ.hom) := by
    have h := isComprehension_comp_iso
      (isComprehension_comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t))) φ.hom
    rwa [hinv] at h
  obtain ⟨δ, hδiso, hδ, -⟩ := compr_basics_2 hc1
    (isComprehension_comprMap (φ.inv ≫ ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)))
  have := hδiso
  have him : imPred (comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≫
      φ.hom ≫ comprMap s) = ceilPred (d ≫ t) := by
    have he : comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≫
        φ.hom ≫ comprMap s =
        δ ≫ comprMap (φ.inv ≫ ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≫
          comprMap s := by
      conv_lhs => rw [← Category.assoc, ← hδ]
      simp only [Category.assoc]
    rw [he, imPred_comp_of_epi, imPred_compr_compr hs hjs, hkey]
  obtain ⟨r, hr⟩ := upm_closed_compr hc1 (isComprehension_comprMap s)
  have hcompr : IsComprehension (ceilPred (d ≫ t))
      (comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≫
        φ.hom ≫ comprMap s) := by
    have h := isComprehension_imPred hr
    simp only [Category.assoc] at h
    rwa [him] at h
  obtain ⟨α, hαiso, hα, -⟩ := compr_basics_2 hcompr
    (isComprehension_comprMap (ceilPred (d ≫ t)))
  have := hαiso
  exact ⟨asIso α, by rw [asIso_hom, hα]⟩

/-- Helper: `1 ∘ k = ⌈q⌉` for the `k` of the Setting 219II. -/
theorem dagger_setting_k_truth [DaggerPrimeEffectus C] {q : Pred X} {t : Pred Y}
    (ψ : comprObj (ceilPred q) ≅ comprObj t) {k : X ⟶ Y}
    (hk : k = zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫ comprMap t) :
    k ≫ truth Y = ceilPred q := by
  rw [hk]
  simp only [Category.assoc]
  rw [compr_total (isComprehension_comprMap t), iso_isTotal ψ.hom,
    quotient_basics_5 (zetaMap_spec (ceilPred q) (isSharp_ceil q)).1,
    eabasics_orth_orth]

/-- Helper: `ψ ∘ ζ_{⌈q⌉}` is pristine. -/
theorem dagger_setting_pristine [DaggerPrimeEffectus C] {q : Pred X} {t : Pred Y}
    (ψ : comprObj (ceilPred q) ≅ comprObj t) :
    Pristine (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) := by
  have hmq : IsQuotient (orth (ceilPred q))
      (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) :=
    quotient_basics_1 (zetaMap_spec (ceilPred q) (isSharp_ceil q)).1 ψ.hom
  refine ⟨upm_closed_pure (isPure_of_isQuotient
    (zetaMap_spec (ceilPred q) (isSharp_ceil q)).1)
    (isPure_of_isQuotient (quotient_basics_3 ψ.hom)), ?_⟩
  rw [quotient_basics_5 hmq, eabasics_orth_orth]
  exact isSharp_ceil q

/-- **219II** (the `pristine-asrt` square of the diagram of 219IV, eff.tex:6094):
`asrt_{p ∘ π_t} ∘ ψ ∘ ζ_{⌈q⌉} = ψ ∘ ζ_{⌈q⌉} ∘ asrt_{p ∘ k}`. -/
theorem dagger_setting_pristine_asrt [DaggerPrimeEffectus C] {q : Pred X} {t : Pred Y}
    (ψ : comprObj (ceilPred q) ≅ comprObj t) {k : X ⟶ Y}
    (hk : k = zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫ comprMap t) (p : Pred Y) :
    (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) ≫ asrt (comprMap t ≫ p) =
      asrt (k ≫ p) ≫ (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) := by
  have hmq : IsQuotient (orth (ceilPred q))
      (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) :=
    quotient_basics_1 (zetaMap_spec (ceilPred q) (isSharp_ceil q)).1 ψ.hom
  have hepi : Epi (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) :=
    quotient_basics_6 hmq
  have him1 : imPred (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) =
      truth (comprObj t) := (cancel_epi _).mp (isImage_imPred _).1
  have hkp : (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) ≫ (comprMap t ≫ p) =
      k ≫ p := by rw [hk]; simp only [Category.assoc]
  have hpri := pristine_asrt (dagger_setting_pristine ψ) (p := comprMap t ≫ p)
    (by rw [him1]; exact pred_le_truth _)
  rwa [hkp] at hpri

/-- Helper (the image computation of `dagger-iso-omega`, eff.tex:6019): if
`⌈a⌉ ≤ ⌈b⌉` then `⌈a & b⌉ = ⌈a⌉`. -/
theorem ceil_andThen_of_le [DaggerPrimeEffectus C] {a b : Pred X}
    (hle : ceilPred a ≼ ceilPred b) : ceilPred (andThen a b) = ceilPred a := by
  have hbb : asrt a ≫ ceilPred b = asrt a ≫ truth X := by
    refine eabasics_le_antisymm (comp_le_comp _ (pred_le_truth _)) ?_
    rw [← (isImage_imPred (asrt a)).1]
    exact comp_le_comp _ (by rw [imPred_asrt]; exact hle)
  show ceilPred (asrt a ≫ b) = _
  rw [← ceiling_within_ceiling b (asrt a), hbb, (asrt_spec a).2]

/-- Helper: `⌈p ∘ k⌉ ≤ ⌈q⌉` in the Setting 219II. -/
theorem dagger_setting_ceil_le [DaggerPrimeEffectus C] {q : Pred X} {k : X ⟶ Y}
    (hk : k ≫ truth Y = ceilPred q) (p : Pred Y) :
    ceilPred (k ≫ p) ≼ ceilPred q := by
  have h1 : (k ≫ p) ≼ ceilPred q := by
    have h := comp_le_comp k (pred_le_truth p)
    rwa [hk] at h
  have h2 := ceilPred_mono h1
  rwa [ceil_of_isSharp (isSharp_ceil q)] at h2

/-- Helper: `dagger_iso_mu` (219XI) transported along equalities of the two
ceilings involved. -/
theorem dagger_iso_mu_of_eq [DaggerPrimeEffectus C] (a b : Pred X)
    {e₁ e₂ : Pred X} (he₁ : IsSharp e₁) (he₂ : IsSharp e₂)
    (h₁ : ceilPred (andThen a b) = e₁) (h₂ : ceilPred (andThen b a) = e₂)
    (ν : comprObj e₂ ≅ comprObj e₁)
    (hν : asrt b ≫ asrt a =
      asrt (andThen b a) ≫ zetaMap e₂ he₂ ≫ ν.hom ≫ comprMap e₁) :
    asrt a ≫ asrt b =
      zetaMap e₁ he₁ ≫ ν.inv ≫ comprMap e₂ ≫ asrt (andThen b a) := by
  subst h₁; subst h₂; exact dagger_iso_mu a b ν hν

/-- **219III** (eff.tex:6072, Lemma): in the Setting 219II,
`f ∘ g = π_{⌈t ∘ f†⌉} ∘ α ∘ χ ∘ β ∘ ω ∘ ζ_{⌈p ∘ g⌉} ∘ asrt_{p ∘ g}`. -/
theorem dagger_of_fg_form [DaggerPrimeEffectus C]
    {g : X ⟶ Y} {f : Y ⟶ Z} {p : Pred Y} {q : Pred X} {s : Pred Z} {t : Pred Y}
    (φ : comprObj (ceilPred p) ≅ comprObj s) (ψ : comprObj (ceilPred q) ≅ comprObj t)
    (hφ : f = asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p) ≫ φ.hom ≫ comprMap s)
    (hψ : g = asrt q ≫ zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫ comprMap t)
    {k : X ⟶ Y}
    (hk : k = zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫ comprMap t)
    {d : Z ⟶ Y}
    {ω : comprObj (ceilPred (g ≫ p)) ≅ comprObj (ceilPred (k ≫ p))}
    (hω : asrt q ≫ asrt (k ≫ p) =
      asrt (g ≫ p) ≫ zetaMap (ceilPred (g ≫ p)) (isSharp_ceil _) ≫ ω.hom ≫
        comprMap (ceilPred (k ≫ p)))
    {β : comprObj (ceilPred (k ≫ p)) ≅ comprObj (ceilPred (comprMap t ≫ p))}
    (hβ : zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫
        zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _) =
      zetaMap (ceilPred (k ≫ p)) (isSharp_ceil _) ≫ β.hom)
    {χ : comprObj (ceilPred (comprMap t ≫ p)) ≅
      comprObj (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t))}
    (hχ : comprMap t ≫ asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p) =
      asrt (comprMap t ≫ p) ≫
        zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _) ≫ χ.hom ≫
        comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)))
    {α : comprObj (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≅
      comprObj (ceilPred (d ≫ t))}
    (hα : comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≫ φ.hom ≫
        comprMap s = α.hom ≫ comprMap (ceilPred (d ≫ t))) :
    g ≫ f = asrt (g ≫ p) ≫ zetaMap (ceilPred (g ≫ p)) (isSharp_ceil _) ≫
      ω.hom ≫ β.hom ≫ χ.hom ≫ α.hom ≫ comprMap (ceilPred (d ≫ t)) := by
  -- the "pristine-asrt" square of the diagram
  have hpri := dagger_setting_pristine_asrt ψ hk p
  have hpriM : ∀ {W : C} (M : comprObj t ⟶ W),
      zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫ asrt (comprMap t ≫ p) ≫ M =
        asrt (k ≫ p) ≫ zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫ M := by
    intro W M
    have h := congrArg (fun x => x ≫ M) hpri
    simpa only [Category.assoc] using h
  have hχM : ∀ {W : C} (M : comprObj (ceilPred p) ⟶ W),
      comprMap t ≫ asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p) ≫ M =
        asrt (comprMap t ≫ p) ≫
          zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _) ≫ χ.hom ≫
          comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≫ M := by
    intro W M
    have h := congrArg (fun x => x ≫ M) hχ
    simpa only [Category.assoc] using h
  have hβM : ∀ {W : C} (M : comprObj (ceilPred (comprMap t ≫ p)) ⟶ W),
      zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫
          zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _) ≫ M =
        zetaMap (ceilPred (k ≫ p)) (isSharp_ceil _) ≫ β.hom ≫ M := by
    intro W M
    have h := congrArg (fun x => x ≫ M) hβ
    simpa only [Category.assoc] using h
  have hωM : ∀ {W : C} (M : X ⟶ W),
      asrt q ≫ asrt (k ≫ p) ≫ M =
        asrt (g ≫ p) ≫ zetaMap (ceilPred (g ≫ p)) (isSharp_ceil _) ≫ ω.hom ≫
          comprMap (ceilPred (k ≫ p)) ≫ M := by
    intro W M
    have h := congrArg (fun x => x ≫ M) hω
    simpa only [Category.assoc] using h
  have hπζc : ∀ {W : C} (M : comprObj (ceilPred (k ≫ p)) ⟶ W),
      comprMap (ceilPred (k ≫ p)) ≫
        zetaMap (ceilPred (k ≫ p)) (isSharp_ceil _) ≫ M = M := by
    intro W M
    rw [← Category.assoc, (zetaMap_spec (ceilPred (k ≫ p)) (isSharp_ceil _)).2.1,
      Category.id_comp]
  conv_lhs => rw [hψ, hφ]
  simp only [Category.assoc]
  rw [hχM, hpriM, hβM, hα, hωM, hπζc]

/-- Helper: `⌈p ∘ π_t⌉ ∘ ψ ∘ ζ_{⌈q⌉} = ⌈p ∘ k⌉`. -/
theorem dagger_setting_ceil_pk [DaggerPrimeEffectus C] {q : Pred X} {t : Pred Y}
    (ψ : comprObj (ceilPred q) ≅ comprObj t) {k : X ⟶ Y}
    (hk : k = zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫ comprMap t) (p : Pred Y) :
    (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) ≫ ceilPred (comprMap t ≫ p) =
      ceilPred (k ≫ p) := by
  have hmq : IsQuotient (orth (ceilPred q))
      (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) :=
    quotient_basics_1 (zetaMap_spec (ceilPred q) (isSharp_ceil q)).1 ψ.hom
  have hmsharp : SharpMap (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) :=
    DaggerPrimeEffectus.quot_sharp (DiamondEffectus.orth_sharp (isSharp_ceil q)) hmq
  rw [← (sharp_ceil _).mp hmsharp (comprMap t ≫ p)]
  refine congrArg ceilPred ?_
  rw [hk]; simp only [Category.assoc]

/-- **219VII** (`dagger-iso-beta2`, eff.tex:6186, Lemma): the daggered version
of `dagger-iso-beta`, `π_{⌈p ∘ k⌉} ∘ β⁻¹ = π_{⌈q⌉} ∘ ψ⁻¹ ∘ π_{⌈p ∘ π_t⌉}`. -/
theorem dagger_iso_beta2 [DaggerPrimeEffectus C] {q : Pred X} {t : Pred Y}
    (ψ : comprObj (ceilPred q) ≅ comprObj t) {k : X ⟶ Y}
    (hk : k = zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫ comprMap t) (p : Pred Y)
    {β : comprObj (ceilPred (k ≫ p)) ≅ comprObj (ceilPred (comprMap t ≫ p))}
    (hβ : zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫
        zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _) =
      zetaMap (ceilPred (k ≫ p)) (isSharp_ceil _) ≫ β.hom) :
    β.inv ≫ comprMap (ceilPred (k ≫ p)) =
      comprMap (ceilPred (comprMap t ≫ p)) ≫ ψ.inv ≫ comprMap (ceilPred q) := by
  -- `π_{⌈p ∘ π_t⌉} ∘ ψ⁻¹` is a comprehension, for the sharp `⌈p ∘ π_t⌉ ∘ ψ`
  have hinv : inv ψ.inv = ψ.hom := by simp
  have hc1 : IsComprehension (ψ.hom ≫ ceilPred (comprMap t ≫ p))
      (comprMap (ceilPred (comprMap t ≫ p)) ≫ ψ.inv) := by
    have h := isComprehension_comp_iso
      (isComprehension_comprMap (ceilPred (comprMap t ≫ p))) ψ.inv
    rwa [hinv] at h
  have hjs : IsSharp (ψ.hom ≫ ceilPred (comprMap t ≫ p)) := by
    have h := isSharp_imPred C (comprMap (ceilPred (comprMap t ≫ p)) ≫ ψ.inv)
    rwa [imPred_comp_iso, hinv,
      (img_of_compr (ceilPred (comprMap t ≫ p))).2 _ (isSharp_ceil _)] at h
  obtain ⟨δ, hδiso, hδ, -⟩ := compr_basics_2 hc1
    (isComprehension_comprMap (ψ.hom ≫ ceilPred (comprMap t ≫ p)))
  have := hδiso
  -- the point's first `align*`: its image is `⌈p ∘ π_t⌉ ∘ ψ ∘ ζ_{⌈q⌉} = ⌈p ∘ k⌉`
  have him : imPred ((comprMap (ceilPred (comprMap t ≫ p)) ≫ ψ.inv) ≫
      comprMap (ceilPred q)) = ceilPred (k ≫ p) := by
    have he : (comprMap (ceilPred (comprMap t ≫ p)) ≫ ψ.inv) ≫ comprMap (ceilPred q) =
        δ ≫ comprMap (ψ.hom ≫ ceilPred (comprMap t ≫ p)) ≫ comprMap (ceilPred q) := by
      rw [← Category.assoc, hδ]
    rw [he, imPred_comp_of_epi, imPred_compr_compr (isSharp_ceil q) hjs,
      ← Category.assoc]
    exact dagger_setting_ceil_pk ψ hk p
  -- so, by `upm-closed`, it is a comprehension for `⌈p ∘ k⌉`
  obtain ⟨r, hr⟩ := upm_closed_compr hc1 (isComprehension_comprMap (ceilPred q))
  have hM : IsComprehension (ceilPred (k ≫ p))
      ((comprMap (ceilPred (comprMap t ≫ p)) ≫ ψ.inv) ≫ comprMap (ceilPred q)) := by
    have h := isComprehension_imPred hr
    rwa [him] at h
  obtain ⟨θ, -, hθ, -⟩ := compr_basics_2 hM
    (isComprehension_comprMap (ceilPred (k ≫ p)))
  -- and the comparison iso is `β⁻¹`, as `π_{⌈p∘k⌉} ∘ ζ_{⌈p∘k⌉} = id` and
  -- `dagger-iso-beta` collapse the pairing
  have hθβ : θ = β.inv := by
    have hz : zetaMap (ceilPred (k ≫ p)) (isSharp_ceil _) =
        (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫
          zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _)) ≫ β.inv := by
      rw [hβ, Category.assoc, β.hom_inv_id, Category.comp_id]
    have h1 : θ = ((comprMap (ceilPred (comprMap t ≫ p)) ≫ ψ.inv) ≫
        comprMap (ceilPred q)) ≫ zetaMap (ceilPred (k ≫ p)) (isSharp_ceil _) := by
      rw [← hθ, Category.assoc,
        (zetaMap_spec (ceilPred (k ≫ p)) (isSharp_ceil _)).2.1, Category.comp_id]
    rw [h1, hz]
    simp only [Category.assoc]
    rw [← Category.assoc (comprMap (ceilPred q)) (zetaMap (ceilPred q) (isSharp_ceil q)),
      (zetaMap_spec (ceilPred q) (isSharp_ceil q)).2.1, Category.id_comp,
      ← Category.assoc ψ.inv ψ.hom, ψ.inv_hom_id, Category.id_comp,
      ← Category.assoc (comprMap (ceilPred (comprMap t ≫ p)))
        (zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _)),
      (zetaMap_spec (ceilPred (comprMap t ≫ p)) (isSharp_ceil _)).2.1,
      Category.id_comp]
  rw [← hθβ, hθ]
  exact Category.assoc _ _ _

/-- **219IX** (`dagger-iso-alpha2`, eff.tex:6228, Exercise): the daggered
version of `dagger-iso-alpha`,
`α⁻¹ ∘ ζ_{⌈t ∘ f†⌉} = ζ_{⌈t ∘ asrt_p ∘ π_{⌈p⌉}⌉} ∘ φ⁻¹ ∘ ζ_s`. -/
theorem dagger_iso_alpha2 [DaggerPrimeEffectus C] {s : Pred Z} (hs : IsSharp s)
    {p : Pred Y} (φ : comprObj (ceilPred p) ≅ comprObj s) (t : Pred Y) {d : Z ⟶ Y}
    (hd : d = zetaMap s hs ≫ φ.inv ≫ comprMap (ceilPred p) ≫ asrt p)
    {α : comprObj (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≅
      comprObj (ceilPred (d ≫ t))}
    (hα : comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≫ φ.hom ≫
        comprMap s = α.hom ≫ comprMap (ceilPred (d ≫ t))) :
    zetaMap (ceilPred (d ≫ t)) (isSharp_ceil _) ≫ α.inv =
      zetaMap s hs ≫ φ.inv ≫
        zetaMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) (isSharp_ceil _) := by
  have hcomb : SharpMap (zetaMap s hs ≫ φ.inv) := sharpMap_zeta_comp_iso hs φ.inv
  -- the solution's first `align*`: `1 ∘ N = ⌈t ∘ f†⌉` for
  -- `N ≡ α ∘ ζ_{⌈t∘asrt_p∘π_{⌈p⌉}⌉} ∘ φ⁻¹ ∘ ζ_s`
  have hkey : (zetaMap s hs ≫ φ.inv) ≫
      ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t) = ceilPred (d ≫ t) := by
    rw [hd, show (zetaMap s hs ≫ φ.inv ≫ comprMap (ceilPred p) ≫ asrt p) ≫ t =
        (zetaMap s hs ≫ φ.inv) ≫ (comprMap (ceilPred p) ≫ asrt p ≫ t) from by
      simp only [Category.assoc],
      (sharp_ceil _).mp hcomb (comprMap (ceilPred p) ≫ asrt p ≫ t)]
  -- so `N` is a quotient for `⌈t ∘ f†⌉ᵖ`, quotients being closed under composition
  have hquot := quotients_composition
    (quotient_basics_1 (zetaMap_spec s hs).1 φ.inv)
    (quotient_basics_1 (zetaMap_spec (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t))
      (isSharp_ceil _)).1 α.hom)
  rw [hkey] at hquot
  -- the solution's second `align*`: `N ∘ π_{⌈t ∘ f†⌉} = id`, by `dagger-iso-alpha`
  have hπN : comprMap (ceilPred (d ≫ t)) ≫ ((zetaMap s hs ≫ φ.inv) ≫
      (zetaMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) (isSharp_ceil _) ≫
        α.hom)) = 𝟙 (comprObj (ceilPred (d ≫ t))) := by
    have hπ : comprMap (ceilPred (d ≫ t)) =
        α.inv ≫ comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≫ φ.hom ≫
          comprMap s := by
      rw [hα, ← Category.assoc, α.inv_hom_id, Category.id_comp]
    rw [hπ]
    simp only [Category.assoc]
    rw [← Category.assoc (comprMap s) (zetaMap s hs), (zetaMap_spec s hs).2.1,
      Category.id_comp, ← Category.assoc φ.hom φ.inv, φ.hom_inv_id, Category.id_comp,
      ← Category.assoc (comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)))
        (zetaMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) (isSharp_ceil _)),
      (zetaMap_spec (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t))
        (isSharp_ceil _)).2.1, Category.id_comp, α.inv_hom_id]
  -- thus `N` is *the* quotient paired with `π_{⌈t ∘ f†⌉}`, i.e. `N = ζ_{⌈t ∘ f†⌉}`
  obtain ⟨θ, -, hθ, -⟩ := quotient_basics_2 hquot
    (zetaMap_spec (ceilPred (d ≫ t)) (isSharp_ceil _)).1
  have hθid : θ = 𝟙 (comprObj (ceilPred (d ≫ t))) := by
    rw [← hπN, ← hθ, ← Category.assoc,
      (zetaMap_spec (ceilPred (d ≫ t)) (isSharp_ceil _)).2.1, Category.id_comp]
  rw [hθid, Category.comp_id] at hθ
  rw [hθ]
  simp only [Category.assoc]
  rw [α.hom_inv_id, Category.comp_id]

/-- **219X** (`dagger-iso-zeta2`, eff.tex:6239, Exercise): the daggered version
of the `pristine-asrt` square,
`π_{⌈q⌉} ∘ ψ⁻¹ ∘ asrt_{p ∘ π_t} = asrt_{p ∘ k} ∘ π_{⌈q⌉} ∘ ψ⁻¹`. -/
theorem dagger_iso_zeta2 [DaggerPrimeEffectus C] {q : Pred X} {t : Pred Y}
    (ψ : comprObj (ceilPred q) ≅ comprObj t) {k : X ⟶ Y}
    (hk : k = zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫ comprMap t) (p : Pred Y) :
    asrt (comprMap t ≫ p) ≫ ψ.inv ≫ comprMap (ceilPred q) =
      ψ.inv ≫ comprMap (ceilPred q) ≫ asrt (k ≫ p) := by
  -- `m ≡ π_{⌈q⌉} ∘ ψ⁻¹` is total, pristine, and has image `⌈q⌉`
  have hmtot : (ψ.inv ≫ comprMap (ceilPred q)) ≫ truth X = truth (comprObj t) := by
    rw [Category.assoc, compr_total (isComprehension_comprMap (ceilPred q))]
    exact iso_isTotal ψ.inv
  have hmpri : Pristine (ψ.inv ≫ comprMap (ceilPred q)) :=
    ⟨upm_closed_pure (isPure_of_isQuotient (quotient_basics_3 ψ.inv))
        (isPure_comprehension C (isComprehension_comprMap (ceilPred q))),
      by rw [hmtot]; exact isSharp_one (comprObj t)⟩
  have hmim : imPred (ψ.inv ≫ comprMap (ceilPred q)) = ceilPred q := by
    rw [imPred_comp_of_epi, (img_of_compr (ceilPred q)).2 _ (isSharp_ceil q)]
  -- `m = π_{⌈q⌉} ∘ ψ⁻¹ ∘ ζ_1 ∘ asrt_1` is its standard form, so `m† = ψ ∘ ζ_{⌈q⌉}`
  have := isIso_comprMap_one (comprObj t)
  have hone : asrt ((ψ.inv ≫ comprMap (ceilPred q)) ≫ truth X) = 𝟙 (comprObj t) := by
    rw [hmtot]; exact asrt_one (comprObj t)
  have hζπ1 := (zetaMap_spec (1 : Pred (comprObj t)) (isSharp_one _)).2.2
  rw [asrt_one] at hζπ1
  have hdag : pureDagger (ψ.inv ≫ comprMap (ceilPred q)) hmpri.1 =
      zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom := by
    refine pureDagger_eq hmpri.1 (isDaggerOf_of_eq (isSharp_one (comprObj t))
      (isSharp_ceil q) (by rw [hmtot]; exact ceil_of_isSharp (isSharp_one (comprObj t)))
      hmim (asIso (comprMap (1 : Pred (comprObj t))) ≪≫ ψ.symm) ?_ ?_)
    · rw [hone, Category.id_comp, Iso.trans_hom, asIso_hom, Iso.symm_hom]
      simp only [Category.assoc]
      rw [← Category.assoc (zetaMap (1 : Pred (comprObj t)) (isSharp_one _)),
        hζπ1, Category.id_comp]
    · rw [hone, Iso.trans_inv, Iso.symm_inv, asIso_inv]
      simp only [Category.assoc]
      rw [Category.comp_id, IsIso.inv_hom_id, Category.comp_id]
  -- `p ∘ π_t ≤ 1 = 1 ∘ m`, so clause 5 of 218IX applies to `m`
  have hle : (comprMap t ≫ p) ≼ ((ψ.inv ≫ comprMap (ceilPred q)) ≫ truth X) := by
    rw [hmtot]; exact pred_le_truth _
  have hkp : (zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom) ≫ (comprMap t ≫ p) =
      k ≫ p := by rw [hk]; simp only [Category.assoc]
  have h5 := asrt_pristine_reverse_5 hmpri hle
  rw [hdag, hkp] at h5
  rw [← h5]
  exact Category.assoc _ _ _

/-- **219XIII** (`dagger-iso-omega2`, eff.tex:6397, Corollary): the daggered
version of `dagger-iso-omega`,
`asrt_q ∘ asrt_{p ∘ k} = asrt_{p ∘ g} ∘ π_{⌈p ∘ g⌉} ∘ ω⁻¹ ∘ ζ_{⌈p ∘ k⌉}`. -/
theorem dagger_iso_omega2 [DaggerPrimeEffectus C] {g : X ⟶ Y} {q : Pred X} {k : X ⟶ Y}
    (hgk : g = asrt q ≫ k) (hk : k ≫ truth Y = ceilPred q) (p : Pred Y)
    {ω : comprObj (ceilPred (g ≫ p)) ≅ comprObj (ceilPred (k ≫ p))}
    (hω : asrt q ≫ asrt (k ≫ p) =
      asrt (g ≫ p) ≫ zetaMap (ceilPred (g ≫ p)) (isSharp_ceil _) ≫ ω.hom ≫
        comprMap (ceilPred (k ≫ p))) :
    asrt (k ≫ p) ≫ asrt q =
      zetaMap (ceilPred (k ≫ p)) (isSharp_ceil _) ≫ ω.inv ≫
        comprMap (ceilPred (g ≫ p)) ≫ asrt (g ≫ p) := by
  have hgp : andThen q (k ≫ p) = g ≫ p := by
    show asrt q ≫ (k ≫ p) = g ≫ p
    rw [hgk]; simp only [Category.assoc]
  have h₁ : ceilPred (andThen (k ≫ p) q) = ceilPred (k ≫ p) :=
    ceil_andThen_of_le (dagger_setting_ceil_le hk p)
  have h₂ : ceilPred (andThen q (k ≫ p)) = ceilPred (g ≫ p) := by rw [hgp]
  have hν : asrt q ≫ asrt (k ≫ p) =
      asrt (andThen q (k ≫ p)) ≫ zetaMap (ceilPred (g ≫ p)) (isSharp_ceil _) ≫
        ω.hom ≫ comprMap (ceilPred (k ≫ p)) := by rw [hgp]; exact hω
  have h := dagger_iso_mu_of_eq (k ≫ p) q (isSharp_ceil (k ≫ p))
    (isSharp_ceil (g ≫ p)) h₁ h₂ ω hν
  rwa [hgp] at h

/-- **219XIV** (`dagger-iso-chi2`, eff.tex:6412, Lemma): the daggered version of
`dagger-iso-chi`,
`ζ_t ∘ asrt_p ∘ π_{⌈p⌉} = asrt_{p ∘ π_t} ∘ π_{⌈p ∘ π_t⌉} ∘ χ⁻¹ ∘
ζ_{⌈t ∘ asrt_p ∘ π_{⌈p⌉}⌉}` — the specialisation of the general
`pureDagger_compr_asrt_zeta` to the Setting 219II. -/
theorem dagger_iso_chi2 [DaggerPrimeEffectus C] {t : Pred Y} (ht : IsSharp t) (p : Pred Y)
    {χ : comprObj (ceilPred (comprMap t ≫ p)) ≅
      comprObj (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t))}
    (hχ : comprMap t ≫ asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p) =
      asrt (comprMap t ≫ p) ≫
        zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _) ≫ χ.hom ≫
        comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t))) :
    comprMap (ceilPred p) ≫ asrt p ≫ zetaMap t ht =
      zetaMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) (isSharp_ceil _) ≫
        χ.inv ≫ comprMap (ceilPred (comprMap t ≫ p)) ≫ asrt (comprMap t ≫ p) := by
  have hA := pureDagger_compr_asrt_zeta ht (isSharp_ceil p)
    (p := p) (pcm_preorder_refl _)
  rw [← hA]
  refine pureDagger_eq (isPure_compr_asrt_zeta (isSharp_ceil p) p)
    (isDaggerOf_of_eq (isSharp_ceil (comprMap t ≫ p)) (isSharp_ceil _)
      (by rw [dagger_setting_truth_chi]) (dagger_setting_im_chi ht p) χ ?_ ?_)
  · rw [dagger_setting_truth_chi]; exact hχ
  · rw [dagger_setting_truth_chi]

/-- **219V** (`dagger-of-fg`, eff.tex:6165, Corollary): in the Setting 219II,
`(f ∘ g)† = asrt_{p ∘ g} ∘ π_{⌈p ∘ g⌉} ∘ ω⁻¹ ∘ β⁻¹ ∘ χ⁻¹ ∘ α⁻¹ ∘
ζ_{⌈t ∘ f†⌉}`. -/
theorem dagger_of_fg [DaggerPrimeEffectus C]
    {g : X ⟶ Y} {f : Y ⟶ Z} (hgf : IsPure (g ≫ f))
    {p : Pred Y} {q : Pred X} {s : Pred Z} {t : Pred Y}
    (φ : comprObj (ceilPred p) ≅ comprObj s) (ψ : comprObj (ceilPred q) ≅ comprObj t)
    (hφ : f = asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p) ≫ φ.hom ≫ comprMap s)
    (hψ : g = asrt q ≫ zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫ comprMap t)
    {k : X ⟶ Y}
    (hk : k = zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫ comprMap t)
    {d : Z ⟶ Y}
    {ω : comprObj (ceilPred (g ≫ p)) ≅ comprObj (ceilPred (k ≫ p))}
    (hω : asrt q ≫ asrt (k ≫ p) =
      asrt (g ≫ p) ≫ zetaMap (ceilPred (g ≫ p)) (isSharp_ceil _) ≫ ω.hom ≫
        comprMap (ceilPred (k ≫ p)))
    {β : comprObj (ceilPred (k ≫ p)) ≅ comprObj (ceilPred (comprMap t ≫ p))}
    (hβ : zetaMap (ceilPred q) (isSharp_ceil q) ≫ ψ.hom ≫
        zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _) =
      zetaMap (ceilPred (k ≫ p)) (isSharp_ceil _) ≫ β.hom)
    {χ : comprObj (ceilPred (comprMap t ≫ p)) ≅
      comprObj (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t))}
    (hχ : comprMap t ≫ asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p) =
      asrt (comprMap t ≫ p) ≫
        zetaMap (ceilPred (comprMap t ≫ p)) (isSharp_ceil _) ≫ χ.hom ≫
        comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)))
    {α : comprObj (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≅
      comprObj (ceilPred (d ≫ t))}
    (hα : comprMap (ceilPred (comprMap (ceilPred p) ≫ asrt p ≫ t)) ≫ φ.hom ≫
        comprMap s = α.hom ≫ comprMap (ceilPred (d ≫ t))) :
    pureDagger (g ≫ f) hgf =
      zetaMap (ceilPred (d ≫ t)) (isSharp_ceil _) ≫ α.inv ≫ χ.inv ≫ β.inv ≫ ω.inv ≫
        comprMap (ceilPred (g ≫ p)) ≫ asrt (g ≫ p) := by
  have hform := dagger_of_fg_form φ ψ hφ hψ hk hω hβ hχ hα
  have hform' : g ≫ f = asrt (g ≫ p) ≫
      zetaMap (ceilPred (g ≫ p)) (isSharp_ceil _) ≫ (ω ≪≫ β ≪≫ χ ≪≫ α).hom ≫
      comprMap (ceilPred (d ≫ t)) := by
    rw [hform]; simp only [Iso.trans_hom, Category.assoc]
  have htruth : (g ≫ f) ≫ truth Z = g ≫ p :=
    standard_form_truth (ω ≪≫ β ≪≫ χ ≪≫ α) hform'
  have him : imPred (g ≫ f) = ceilPred (d ≫ t) :=
    standard_form_imPred (isSharp_ceil _) (ω ≪≫ β ≪≫ χ ≪≫ α) hform'
  refine pureDagger_eq hgf (isDaggerOf_of_eq (isSharp_ceil (g ≫ p))
    (isSharp_ceil (d ≫ t)) (by rw [htruth]) him (ω ≪≫ β ≪≫ χ ≪≫ α) ?_ ?_)
  · rw [htruth]; exact hform'
  · rw [htruth]; simp only [Iso.trans_inv, Category.assoc]

/-- **219XVI** (`dagger-is-functor`, eff.tex:6535, Proposition): in a
†'-effectus, `(f ∘ g)† = g† ∘ f†` for pure `f, g`.  The proof is the thesis's:
set up the Setting 219II, form its four isomorphisms `χ`, `ω`, `β`, `α`, and
run the six-step chain of eff.tex:6580 on `g† ∘ f†`, using the daggered
squares 219VII, 219IX, 219X, 219XIII and 219XIV and closing with 219V. -/
theorem dagger_is_functor [DaggerPrimeEffectus C] {g : X ⟶ Y} {f : Y ⟶ Z}
    (hg : IsPure g) (hf : IsPure f) :
    pureDagger (g ≫ f) (upm_closed_pure hg hf) =
      pureDagger f hf ≫ pureDagger g hg := by
  -- Setting 219II
  obtain ⟨φ, hφ⟩ := standard_form_of_eq hf (isSharp_ceil (f ≫ truth Z))
    (isSharp_imPred C f) rfl rfl
  obtain ⟨ψ, hψ⟩ := standard_form_of_eq hg (isSharp_ceil (g ≫ truth Y))
    (isSharp_imPred C g) rfl rfl
  obtain ⟨k, hk⟩ : ∃ k : X ⟶ Y, k =
      zetaMap (ceilPred (g ≫ truth Y)) (isSharp_ceil _) ≫ ψ.hom ≫
        comprMap (imPred g) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Z ⟶ Y, d =
      zetaMap (imPred f) (isSharp_imPred C f) ≫ φ.inv ≫
        comprMap (ceilPred (f ≫ truth Z)) ≫ asrt (f ≫ truth Z) := ⟨_, rfl⟩
  have hgk : g = asrt (g ≫ truth Y) ≫ k := by rw [hk]; exact hψ
  have hktruth : k ≫ truth Y = ceilPred (g ≫ truth Y) := dagger_setting_k_truth ψ hk
  have hdf : pureDagger f hf = d := pureDagger_eq hf ⟨φ, hφ, hd⟩
  have hdg : pureDagger g hg = zetaMap (imPred g) (isSharp_imPred C g) ≫ ψ.inv ≫
      comprMap (ceilPred (g ≫ truth Y)) ≫ asrt (g ≫ truth Y) :=
    pureDagger_eq hg ⟨ψ, hψ, rfl⟩
  -- the four isomorphisms of 219II
  obtain ⟨χ, hχ⟩ := dagger_iso_chi (isSharp_imPred C g) (f ≫ truth Z)
  obtain ⟨ω, hω⟩ := dagger_iso_omega hgk hktruth (f ≫ truth Z)
  obtain ⟨β, hβ⟩ := dagger_iso_beta ψ hk (f ≫ truth Z)
  obtain ⟨α, hα⟩ := dagger_iso_alpha (isSharp_imPred C f) φ (imPred g) hd
  -- 219V and the daggered versions 219VII, 219IX, 219X, 219XIII, 219XV
  have hV := dagger_of_fg (upm_closed_pure hg hf) φ ψ hφ hψ hk hω hβ hχ hα
  have hchi2 := dagger_iso_chi2 (isSharp_imPred C g) (f ≫ truth Z) hχ
  have hzeta2 := dagger_iso_zeta2 ψ hk (f ≫ truth Z)
  have hbeta2 := dagger_iso_beta2 ψ hk (f ≫ truth Z) hβ
  have halpha2 := dagger_iso_alpha2 (isSharp_imPred C f) φ (imPred g) hd hα
  have homega2 := dagger_iso_omega2 hgk hktruth (f ≫ truth Z) hω
  -- the six-step chain of eff.tex:6580
  have hchi2M : ∀ {W : C} (M : comprObj (imPred g) ⟶ W),
      comprMap (ceilPred (f ≫ truth Z)) ≫ asrt (f ≫ truth Z) ≫
          zetaMap (imPred g) (isSharp_imPred C g) ≫ M =
        zetaMap (ceilPred (comprMap (ceilPred (f ≫ truth Z)) ≫ asrt (f ≫ truth Z) ≫
            imPred g)) (isSharp_ceil _) ≫ χ.inv ≫
          comprMap (ceilPred (comprMap (imPred g) ≫ f ≫ truth Z)) ≫
          asrt (comprMap (imPred g) ≫ f ≫ truth Z) ≫ M := by
    intro W M
    have h := congrArg (fun x => x ≫ M) hchi2
    simpa only [Category.assoc] using h
  have hzeta2M : ∀ {W : C} (M : X ⟶ W),
      asrt (comprMap (imPred g) ≫ f ≫ truth Z) ≫ ψ.inv ≫
          comprMap (ceilPred (g ≫ truth Y)) ≫ M =
        ψ.inv ≫ comprMap (ceilPred (g ≫ truth Y)) ≫
          asrt (k ≫ f ≫ truth Z) ≫ M := by
    intro W M
    have h := congrArg (fun x => x ≫ M) hzeta2
    simpa only [Category.assoc] using h
  have hbeta2M : ∀ {W : C} (M : X ⟶ W),
      comprMap (ceilPred (comprMap (imPred g) ≫ f ≫ truth Z)) ≫ ψ.inv ≫
          comprMap (ceilPred (g ≫ truth Y)) ≫ M =
        β.inv ≫ comprMap (ceilPred (k ≫ f ≫ truth Z)) ≫ M := by
    intro W M
    have h := congrArg (fun x => x ≫ M) hbeta2.symm
    simpa only [Category.assoc] using h
  have hπζ : ∀ {W : C} (M : comprObj (ceilPred (k ≫ f ≫ truth Z)) ⟶ W),
      comprMap (ceilPred (k ≫ f ≫ truth Z)) ≫
        zetaMap (ceilPred (k ≫ f ≫ truth Z)) (isSharp_ceil _) ≫ M = M := by
    intro W M
    rw [← Category.assoc (comprMap (ceilPred (k ≫ f ≫ truth Z)))
        (zetaMap (ceilPred (k ≫ f ≫ truth Z)) (isSharp_ceil _)) M,
      (zetaMap_spec (ceilPred (k ≫ f ≫ truth Z)) (isSharp_ceil _)).2.1,
      Category.id_comp]
  have halpha2M : ∀ {W : C} (M : comprObj (ceilPred (comprMap (ceilPred (f ≫ truth Z)) ≫
        asrt (f ≫ truth Z) ≫ imPred g)) ⟶ W),
      zetaMap (imPred f) (isSharp_imPred C f) ≫ φ.inv ≫
          zetaMap (ceilPred (comprMap (ceilPred (f ≫ truth Z)) ≫ asrt (f ≫ truth Z) ≫
            imPred g)) (isSharp_ceil _) ≫ M =
        zetaMap (ceilPred (d ≫ imPred g)) (isSharp_ceil _) ≫ α.inv ≫ M := by
    intro W M
    have h := congrArg (fun x => x ≫ M) halpha2.symm
    simpa only [Category.assoc] using h
  rw [hV, hdf, hdg]
  conv_rhs => rw [hd]
  simp only [Category.assoc]
  rw [hchi2M, hzeta2M, hbeta2M, homega2, hπζ, halpha2M]

/-- **220II** (`dagger-thm-sufficiency`, eff.tex:6665), Ax. 1: a pure map is
⋄-adjoint to its dagger.  (Apply `(–)^⋄` to the standard form 212III of `f`,
using 218II for `π/ζ` and 209IV for the isomorphism.) -/
theorem pureDagger_diamond_adjoint [DaggerPrimeEffectus C] {f : X ⟶ Y}
    (hf : IsPure f) : DiamondAdjoint f (pureDagger f hf) := by
  obtain ⟨φ, hform⟩ :=
    standard_form_of_eq hf (isSharp_ceil _) (isSharp_imPred C f) rfl rfl
  have hdag : pureDagger f hf = zetaMap (imPred f) (isSharp_imPred C f) ≫
      φ.inv ≫ comprMap (ceilPred (f ≫ truth Y)) ≫ asrt (f ≫ truth Y) :=
    pureDagger_eq hf ⟨φ, hform, rfl⟩
  have e1 : diaPull (comprMap (imPred f)) =
      diaPush (zetaMap (imPred f) (isSharp_imPred C f)) :=
    quotcompr_diamond_adjoint _
  have e2 : diaPull φ.hom = diaPush φ.inv := by
    have h := (iso_diamond_adjoint_2 φ.hom).2.2
    have hinv : inv φ.hom = φ.inv := by simp
    rw [hinv] at h
    exact h
  have e3 : diaPull (zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _)) =
      diaPush (comprMap (ceilPred (f ≫ truth Y))) :=
    ((exc_diamond_adj_1 _ _).mp (quotcompr_diamond_adjoint (isSharp_ceil _))).symm
  have e4 : diaPull (asrt (f ≫ truth Y)) = diaPush (asrt (f ≫ truth Y)) :=
    diamond_squares_2 (asrt_spec _).1
  change diaPull f = diaPush (pureDagger f hf)
  rw [hdag]
  conv_lhs => rw [hform]
  funext s
  simp only [diaPull_comp, diaPush_comp, e1, e2, e3, e4]

/-- **220II**, Ax. 2 (first half): `f† ∘ f = asrt_{1∘f} ∘ asrt_{1∘f}` for pure
`f`; in particular †-positive maps are ⋄-positive. -/
theorem pureDagger_comp_self [DaggerPrimeEffectus C] {f : X ⟶ Y}
    (hf : IsPure f) : f ≫ pureDagger f hf =
      asrt (f ≫ truth Y) ≫ asrt (f ≫ truth Y) := by
  obtain ⟨φ, hform⟩ :=
    standard_form_of_eq hf (isSharp_ceil _) (isSharp_imPred C f) rfl rfl
  have hdag : pureDagger f hf = zetaMap (imPred f) (isSharp_imPred C f) ≫
      φ.inv ≫ comprMap (ceilPred (f ≫ truth Y)) ≫ asrt (f ≫ truth Y) :=
    pureDagger_eq hf ⟨φ, hform, rfl⟩
  have habs : asrt (ceilPred (f ≫ truth Y)) ≫ asrt (f ≫ truth Y) =
      asrt (f ≫ truth Y) :=
    (asrt_absorp_rule (asrt (f ≫ truth Y)) (isSharp_one X)
      (isSharp_ceil _)).2.mp
      (by rw [(asrt_spec (f ≫ truth Y)).2]; exact le_ceil _)
  calc f ≫ pureDagger f hf
      = (asrt (f ≫ truth Y) ≫ zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫
          φ.hom ≫ comprMap (imPred f)) ≫
        (zetaMap (imPred f) (isSharp_imPred C f) ≫ φ.inv ≫
          comprMap (ceilPred (f ≫ truth Y)) ≫ asrt (f ≫ truth Y)) := by
        rw [hdag, ← hform]
    _ = asrt (f ≫ truth Y) ≫ asrt (f ≫ truth Y) := by
        simp only [Category.assoc]
        rw [← Category.assoc (comprMap (imPred f))
            (zetaMap (imPred f) (isSharp_imPred C f)),
          (zetaMap_spec (imPred f) (isSharp_imPred C f)).2.1, Category.id_comp,
          ← Category.assoc φ.hom φ.inv, φ.hom_inv_id, Category.id_comp,
          ← Category.assoc (zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _)),
          (zetaMap_spec (ceilPred (f ≫ truth Y)) (isSharp_ceil _)).2.2, habs]

/-- The †-category structure on `Pure C` of a †'-effectus (220II, Ax. 1). -/
noncomputable def pureDaggerCat [DaggerPrimeEffectus C] :
    DaggerCat (PureCat C) where
  dag f := ⟨pureDagger f.1 f.2, isPure_pureDagger f.2⟩
  dag_comp f g := Subtype.ext (dagger_is_functor f.2 g.2)
  dag_id P := Subtype.ext
    (pureDagger_eq (isPure_of_isQuotient (quotient_basics_3 (𝟙 P.base)))
      (dagger_prime_basics_iso (Iso.refl P.base)))
  dag_dag f := Subtype.ext (dagger_idempotent f.2)

/-- The dagger of `pureDaggerCat` is `pureDagger` (definitional). -/
theorem pureDaggerCat_dag [DaggerPrimeEffectus C] {P Q : PureCat C} (f : P ⟶ Q) :
    (@DaggerCat.dag _ _ pureDaggerCat P Q f).1 = pureDagger f.1 f.2 := rfl

/-- Composition in `Pure C` is composition in `C` (definitional). -/
theorem pureCat_comp_val {P Q R : PureCat C}
    (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).1 = f.1 ≫ g.1 := rfl

/-- The †-effectus structure that a †'-effectus carries (220II): its
†-category is `pureDaggerCat`, hence its dagger *is* `pureDagger`, the
dagger of 217II.  The three axioms are verified as in the Theorem's own
proof. -/
noncomputable def pureDaggerEffectus [DaggerPrimeEffectus C] :
    DaggerEffectus C := by
  refine
    { daggerCat := pureDaggerCat
      dag_asrt := fun p => Subtype.ext ?_
      dag_diamond_adjoint := fun f => ?_
      sqrt_existsUnique := ?_
      diamond_pos_dagger_pos := ?_ }
  · rw [pureDaggerCat_dag]
    exact pureDagger_eq _ (dagger_prime_basics_asrt p)
  · rw [pureDaggerCat_dag]
    exact pureDagger_diamond_adjoint f.2
  · -- Ax. 2
    rintro P F ⟨Q, g, hg⟩
    have hF : F.1 = asrt (g.1 ≫ truth Q.base) ≫ asrt (g.1 ≫ truth Q.base) := by
      rw [congrArg Subtype.val hg, pureCat_comp_val, pureDaggerCat_dag]
      exact pureDagger_comp_self g.2
    have hF1 : F.1 ≫ truth P.base =
        andThen (g.1 ≫ truth Q.base) (g.1 ≫ truth Q.base) := by
      rw [hF, Category.assoc, (asrt_spec _).2]; rfl
    obtain ⟨q, hq⟩ := (DaggerPrimeEffectus.sqrt_existsUnique
      (g.1 ≫ truth Q.base)).exists
    refine ⟨⟨asrt (g.1 ≫ truth Q.base), (asrt_spec _).1.1⟩,
      ⟨⟨PureCat.of P.base, ⟨asrt q, (asrt_spec q).1.1⟩, Subtype.ext ?_⟩,
        Subtype.ext hF.symm⟩, ?_⟩
    · rw [pureCat_comp_val, pureDaggerCat_dag]
      change asrt (g.1 ≫ truth Q.base) = asrt q ≫ pureDagger (asrt q) _
      rw [pureDagger_eq (asrt_spec q).1.1 (dagger_prime_basics_asrt q),
        andthen_square_rule, hq]
    · rintro G' ⟨⟨R, k, hk⟩, hGG⟩
      have hG' : G'.1 = asrt (andThen (k.1 ≫ truth R.base)
          (k.1 ≫ truth R.base)) := by
        rw [congrArg Subtype.val hk, pureCat_comp_val, pureDaggerCat_dag,
          pureDagger_comp_self k.2, andthen_square_rule]
      refine Subtype.ext ?_
      have hsq : andThen (andThen (k.1 ≫ truth R.base) (k.1 ≫ truth R.base))
          (andThen (k.1 ≫ truth R.base) (k.1 ≫ truth R.base)) =
          F.1 ≫ truth P.base := by
        rw [← congrArg (fun z => z ≫ truth P.base) (congrArg Subtype.val hGG),
          pureCat_comp_val, hG', Category.assoc, (asrt_spec _).2]
        rfl
      have huniq := (DaggerPrimeEffectus.sqrt_existsUnique
        (F.1 ≫ truth P.base)).unique hsq (by rw [← hF1])
      rw [hG', huniq]
  · -- Ax. 3
    intro W f hf
    obtain ⟨q, hq⟩ := (DaggerPrimeEffectus.sqrt_existsUnique
      (f ≫ truth W)).exists
    refine ⟨PureCat.of W, ⟨asrt q, (asrt_spec q).1.1⟩, Subtype.ext ?_⟩
    rw [pureCat_comp_val, pureDaggerCat_dag]
    change f = asrt q ≫ pureDagger (asrt q) _
    rw [pureDagger_eq (asrt_spec q).1.1 (dagger_prime_basics_asrt q),
      andthen_square_rule, hq]
    exact asrt_unique _ f hf rfl

/-- **220II** (`dagger-thm-sufficiency`, eff.tex:6665, Theorem): a
†'-effectus is a †-effectus **with † as defined in 217II** — the dagger of
the resulting †-effectus is `pureDagger`, on the nose.  (The identification
is definitional: the witness `pureDaggerEffectus` has `pureDaggerCat` as its
†-category, whose `dag` is `pureDagger`.) -/
theorem dagger_thm_sufficiency' [DaggerPrimeEffectus C] :
    ∃ d : DaggerEffectus C, ∀ (P Q : PureCat C) (f : P ⟶ Q),
      (d.daggerCat.dag f).1 = pureDagger f.1 f.2 :=
  ⟨pureDaggerEffectus, fun _ _ _ => rfl⟩

/-- **220II** (`dagger-thm-sufficiency`, eff.tex:6665, Theorem), the bare
existence half.  The full statement, with the identification of the dagger
with that of 217II, is `dagger_thm_sufficiency'`. -/
theorem dagger_thm_sufficiency [DaggerPrimeEffectus C] :
    Nonempty (DaggerEffectus C) :=
  ⟨pureDaggerEffectus⟩

section DaggerTheorem

variable (C)

/-- **215III** (`dagger-theorem`, eff.tex:5310, Theorem): an &-effectus is
a †-effectus if and only if it is a †'-effectus (necessity is 216XI,
sufficiency 220II).  (Stated at its numbering slot in parsec 215; proved here,
where 220II is available.)  220II's "with † as defined in 217II" cannot be
carried into this biimplication — `pureDagger` presupposes
`[DaggerPrimeEffectus C]`, which is the right-hand side — so it is stated
separately as `dagger_thm_sufficiency'`, and `dag_eq_pureDagger` gives the
converse identification for an arbitrary †-effectus. -/
theorem dagger_theorem :
    Nonempty (DaggerEffectus C) ↔ DaggerPrimeEffectus C := by
  constructor
  · rintro ⟨d⟩
    exact dagger_thm_necessity d
  · intro h
    exact dagger_thm_sufficiency

end DaggerTheorem

end PureDagger

/-! ## Coproducts of quotients and of comprehensions

Six helpers used by 221IV.7 (and 221IV.5), proved in a plain effectus: the
coproduct `ξ₁ + ξ₂` of two quotients is a quotient and the coproduct
`π₁ + π₂` of two comprehensions is a comprehension, so `h₁ + h₂` is pure as
soon as `h₁` and `h₂` are — **without** the &-effectus that closure of pure
maps under composition (211XI) would need.  The Proposition asserts the
purity and its proof passes over it in silence (ERRATA, `221IV.5/.6/.7`). -/

section CoprodQuotCompr

/-- Helper: `[p, q]ᵖ = [pᵖ, qᵖ]`. -/
theorem orth_coprod_desc {X Y : C} (p : Pred X) (q : Pred Y) :
    orth (coprod.desc p q) = coprod.desc (orth p) (orth q) := by
  have hp := EffectAlgebra.perp_orth p
  have hq := EffectAlgebra.perp_orth q
  have hperp : Perp (coprod.desc p q) (coprod.desc (orth p) (orth q)) :=
    (cotupl_pcm_1 _ _ _ _).2 ⟨hp, hq⟩
  refine (EffectAlgebra.orth_unique hperp ?_).symm
  rw [cotupl_pcm_2 hperp hp hq, EffectAlgebra.ovee_orth p, EffectAlgebra.ovee_orth q]
  exact cotupl_pcm_one X Y

/-- Helper: `[a₁,a₂] ≼ [b₁,b₂]` as soon as `a₁ ≼ b₁` and `a₂ ≼ b₂`. -/
theorem coprod_desc_le {X Y : C} {a₁ b₁ : Pred X} {a₂ b₂ : Pred Y}
    (h₁ : a₁ ≼ b₁) (h₂ : a₂ ≼ b₂) :
    (coprod.desc a₁ a₂ : Pred (X ⨿ Y)) ≼ coprod.desc b₁ b₂ := by
  obtain ⟨c₁, hc₁, e₁⟩ := h₁
  obtain ⟨c₂, hc₂, e₂⟩ := h₂
  have hperp : Perp (coprod.desc a₁ a₂) (coprod.desc c₁ c₂) :=
    (cotupl_pcm_1 _ _ _ _).2 ⟨hc₁, hc₂⟩
  exact ⟨coprod.desc c₁ c₂, hperp, by rw [cotupl_pcm_2 hperp hc₁ hc₂, e₁, e₂]⟩

/-- Helper: `▷₁ ∘ (π₁ + π₂) = π₁ ∘ ▷₁` (the partial projections are natural
for `+`). -/
theorem coprod_map_pproj₁ {W₁ W₂ X₁ X₂ : C} (k : W₁ ⟶ X₁) (l : W₂ ⟶ X₂) :
    coprod.map k l ≫ pproj₁ X₁ X₂ = pproj₁ W₁ W₂ ≫ k := by
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, coprod.inl_map, Category.assoc, pproj₁,
      coprod.inl_desc, Category.comp_id, ← Category.assoc, pproj₁,
      coprod.inl_desc, Category.id_comp]
  · rw [← Category.assoc, coprod.inr_map, Category.assoc, pproj₁,
      coprod.inr_desc, FinPAC.comp_zero, ← Category.assoc, pproj₁,
      coprod.inr_desc, FinPAC.zero_comp]

theorem coprod_map_pproj₂ {W₁ W₂ X₁ X₂ : C} (k : W₁ ⟶ X₁) (l : W₂ ⟶ X₂) :
    coprod.map k l ≫ pproj₂ X₁ X₂ = pproj₂ W₁ W₂ ≫ l := by
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, coprod.inl_map, Category.assoc, pproj₂,
      coprod.inl_desc, FinPAC.comp_zero, ← Category.assoc, pproj₂,
      coprod.inl_desc, FinPAC.zero_comp]
  · rw [← Category.assoc, coprod.inr_map, Category.assoc, pproj₂,
      coprod.inr_desc, Category.comp_id, ← Category.assoc, pproj₂,
      coprod.inr_desc, Category.id_comp]

/-- Helper: every map into a coproduct is the pairing of its partial
projections (181VII). -/
theorem eq_effPair {X Y Z : C} (u : Z ⟶ X ⨿ Y) :
    u = effPair (u ≫ pproj₁ X Y) (u ≫ pproj₂ X Y) (coprod_prod_converse u) :=
  (coprod_prod (coprod_prod_converse u)).unique ⟨rfl, rfl⟩ (effPair_spec _ _ _)

/-- Helper: the coproduct `ξ₁ + ξ₂` of two quotients is a quotient
for `[p₁, p₂]`. -/
theorem isQuotient_coprod_map {X₁ X₂ Q₁ Q₂ : C} {p₁ : Pred X₁} {p₂ : Pred X₂}
    {ξ₁ : X₁ ⟶ Q₁} {ξ₂ : X₂ ⟶ Q₂} (h₁ : IsQuotient p₁ ξ₁)
    (h₂ : IsQuotient p₂ ξ₂) :
    IsQuotient (coprod.desc p₁ p₂) (coprod.map ξ₁ ξ₂) := by
  have hone : coprod.map ξ₁ ξ₂ ≫ truth (Q₁ ⨿ Q₂)
      = coprod.desc (ξ₁ ≫ truth Q₁) (ξ₂ ≫ truth Q₂) := by
    rw [← cotupl_pcm_one Q₁ Q₂, coprod.map_desc]
  refine ⟨?_, ?_⟩
  · rw [orth_coprod_desc, hone]
    exact coprod_desc_le h₁.1 h₂.1
  · intro V f hf
    rw [orth_coprod_desc] at hf
    have hf₁ : ((coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ≫ f) ≫ truth V ≼ orth p₁ := by
      have := comp_le_comp (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) hf
      rwa [← Category.assoc, coprod.inl_desc] at this
    have hf₂ : ((coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ≫ f) ≫ truth V ≼ orth p₂ := by
      have := comp_le_comp (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) hf
      rwa [← Category.assoc, coprod.inr_desc] at this
    obtain ⟨f₁, hf₁', hu₁⟩ := h₁.2 _ hf₁
    obtain ⟨f₂, hf₂', hu₂⟩ := h₂.2 _ hf₂
    refine ⟨coprod.desc f₁ f₂, ?_, ?_⟩
    · show coprod.map ξ₁ ξ₂ ≫ coprod.desc f₁ f₂ = f
      rw [coprod.map_desc, hf₁', hf₂', ← coprod.desc_comp, coprod.desc_inl_inr,
        Category.id_comp]
    · intro g hg
      refine coprod.hom_ext ?_ ?_
      · rw [coprod.inl_desc]
        refine hu₁ _ ?_
        show ξ₁ ≫ _ = _
        rw [← Category.assoc, ← coprod.inl_map ξ₁ ξ₂, Category.assoc, hg]
      · rw [coprod.inr_desc]
        refine hu₂ _ ?_
        show ξ₂ ≫ _ = _
        rw [← Category.assoc, ← coprod.inr_map ξ₁ ξ₂, Category.assoc, hg]

/-- Helper: the coproduct `π₁ + π₂` of two comprehensions is a comprehension
for `[q₁, q₂]`. -/
theorem isComprehension_coprod_map [HasQuotients C] {W₁ W₂ X₁ X₂ : C}
    {q₁ : Pred X₁} {q₂ : Pred X₂} {π₁ : W₁ ⟶ X₁} {π₂ : W₂ ⟶ X₂}
    (h₁ : IsComprehension q₁ π₁) (h₂ : IsComprehension q₂ π₂) :
    IsComprehension (coprod.desc q₁ q₂) (coprod.map π₁ π₂) := by
  have ht₁ : IsTotal π₁ := compr_total h₁
  have ht₂ : IsTotal π₂ := compr_total h₂
  refine ⟨?_, ?_⟩
  · rw [coprod.map_desc, ← cotupl_pcm_one X₁ X₂, coprod.map_desc, h₁.1, h₂.1]
  · intro Z g hg
    set g₁ := g ≫ pproj₁ X₁ X₂ with hg₁d
    set g₂ := g ≫ pproj₂ X₁ X₂ with hg₂d
    have hperp : Perp (g₁ ≫ truth X₁) (g₂ ≫ truth X₂) := coprod_prod_converse g
    have hgp : g = effPair g₁ g₂ hperp := eq_effPair g
    obtain ⟨hp1, e1⟩ := eff_prod_rules_1 g₁ g₂ hperp q₁ q₂
    have e2 := eff_prod_rules_2 g₁ g₂ hperp
    have hsum : ovee (g₁ ≫ q₁) (g₂ ≫ q₂) hp1
        = ovee (g₁ ≫ truth X₁) (g₂ ≫ truth X₂) hperp := by
      rw [← e1, ← e2, ← hgp]; exact hg
    obtain ⟨eq1, eq2⟩ := eq_of_ovee_eq_of_le hp1 hperp
      (comp_le_comp g₁ (pred_le_truth q₁)) (comp_le_comp g₂ (pred_le_truth q₂))
      hsum
    obtain ⟨g₁', hg₁', hu₁⟩ := h₁.2 g₁ eq1
    obtain ⟨g₂', hg₂', hu₂⟩ := h₂.2 g₂ eq2
    have hperp' : Perp (g₁' ≫ truth W₁) (g₂' ≫ truth W₂) := by
      have a1 : g₁' ≫ truth W₁ = g₁ ≫ truth X₁ := by
        rw [← ht₁, ← Category.assoc, hg₁']
      have a2 : g₂' ≫ truth W₂ = g₂ ≫ truth X₂ := by
        rw [← ht₂, ← Category.assoc, hg₂']
      rw [a1, a2]; exact hperp
    refine ⟨effPair g₁' g₂' hperp', ?_, ?_⟩
    · show effPair g₁' g₂' hperp' ≫ coprod.map π₁ π₂ = g
      refine (coprod_prod hperp).unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩
      · rw [Category.assoc, coprod_map_pproj₁, ← Category.assoc,
          (effPair_spec g₁' g₂' hperp').1, hg₁']
      · rw [Category.assoc, coprod_map_pproj₂, ← Category.assoc,
          (effPair_spec g₁' g₂' hperp').2, hg₂']
    · intro k hk
      replace hk : k ≫ coprod.map π₁ π₂ = g := hk
      have k1 : k ≫ pproj₁ W₁ W₂ = g₁' := by
        refine hu₁ _ ?_
        show (k ≫ pproj₁ W₁ W₂) ≫ π₁ = g₁
        rw [Category.assoc, ← coprod_map_pproj₁ π₁ π₂, ← Category.assoc, hk]
      have k2 : k ≫ pproj₂ W₁ W₂ = g₂' := by
        refine hu₂ _ ?_
        show (k ≫ pproj₂ W₁ W₂) ≫ π₂ = g₂
        rw [Category.assoc, ← coprod_map_pproj₂ π₁ π₂, ← Category.assoc, hk]
      exact (coprod_prod hperp').unique ⟨k1, k2⟩ (effPair_spec g₁' g₂' hperp')

end CoprodQuotCompr

/-! ## Dilations (parsecs 221–223) -/

section Dilations

variable [DiamondEffectus C] {X Y P : C}

/-- **221II** (`dfn-eff-dilations`, eff.tex:6786, Definition): a
**dilation** of a map `f : X ⟶ Y` is a triple `(P, ϱ, h)` of a sharp total
map `ϱ : P ⟶ Y` and a pure map `h : X ⟶ P` with `ϱ ∘ h = f`, universal
among such factorizations: for every `(P', ϱ', h')` with `ϱ'` total sharp
and `f = ϱ' ∘ h'` there is a unique `σ : P ⟶ P'` with `σ ∘ h = h'` and
`ϱ' ∘ σ = ϱ`. -/
def IsDilation (f : X ⟶ Y) (ϱ : P ⟶ Y) (h : X ⟶ P) : Prop :=
  SharpMap ϱ ∧ IsTotal ϱ ∧ IsPure h ∧ h ≫ ϱ = f ∧
    ∀ ⦃P' : C⦄ (ϱ' : P' ⟶ Y) (h' : X ⟶ P'),
      SharpMap ϱ' → IsTotal ϱ' → h' ≫ ϱ' = f →
        ∃! σ : P ⟶ P', h ≫ σ = h' ∧ σ ≫ ϱ' = ϱ

/-- **221II** (`dfn-eff-dilations`, eff.tex:6802, Definition): an effectus
**has dilations** when every map has a dilation. -/
class HasDilations (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
    [DiamondEffectus C] : Prop where
  dil : ∀ {X Y : C} (f : X ⟶ Y),
    ∃ (P : C) (ϱ : P ⟶ Y) (h : X ⟶ P), IsDilation f ϱ h

/-- **221IV.1** (`dils-abstract-basics`, eff.tex:6820, Proposition): any
two dilations of `f` are related by a unique isomorphism. -/
theorem dils_abstract_basics_1 {P₂ : C} {f : X ⟶ Y} {ϱ₁ : P ⟶ Y}
    {h₁ : X ⟶ P} {ϱ₂ : P₂ ⟶ Y} {h₂ : X ⟶ P₂}
    (d₁ : IsDilation f ϱ₁ h₁) (d₂ : IsDilation f ϱ₂ h₂) :
    ∃ α : P ⟶ P₂, IsIso α ∧ h₁ ≫ α = h₂ ∧ α ≫ ϱ₂ = ϱ₁ ∧
      ∀ α' : P ⟶ P₂, h₁ ≫ α' = h₂ → α' ≫ ϱ₂ = ϱ₁ → α' = α := by
  obtain ⟨hs₁, ht₁, hp₁, hfac₁, huniv₁⟩ := d₁
  obtain ⟨hs₂, ht₂, hp₂, hfac₂, huniv₂⟩ := d₂
  obtain ⟨σ₁, ⟨hσ₁h, hσ₁ϱ⟩, huσ₁⟩ := huniv₁ ϱ₂ h₂ hs₂ ht₂ hfac₂
  obtain ⟨σ₂, ⟨hσ₂h, hσ₂ϱ⟩, -⟩ := huniv₂ ϱ₁ h₁ hs₁ ht₁ hfac₁
  -- `σ₁ ≫ σ₂` and `𝟙 P` both mediate `(P, ϱ₁, h₁)` to itself, hence agree.
  obtain ⟨τ, -, huτ⟩ := huniv₁ ϱ₁ h₁ hs₁ ht₁ hfac₁
  have e1 : σ₁ ≫ σ₂ = 𝟙 P :=
    (huτ (σ₁ ≫ σ₂) ⟨by rw [← Category.assoc, hσ₁h, hσ₂h],
        by rw [Category.assoc, hσ₂ϱ, hσ₁ϱ]⟩).trans
      (huτ (𝟙 P) ⟨Category.comp_id _, Category.id_comp _⟩).symm
  obtain ⟨τ', -, huτ'⟩ := huniv₂ ϱ₂ h₂ hs₂ ht₂ hfac₂
  have e2 : σ₂ ≫ σ₁ = 𝟙 P₂ :=
    (huτ' (σ₂ ≫ σ₁) ⟨by rw [← Category.assoc, hσ₂h, hσ₁h],
        by rw [Category.assoc, hσ₁ϱ, hσ₂ϱ]⟩).trans
      (huτ' (𝟙 P₂) ⟨Category.comp_id _, Category.id_comp _⟩).symm
  exact ⟨σ₁, ⟨σ₂, e1, e2⟩, hσ₁h, hσ₁ϱ, fun α' hα'h hα'ϱ => huσ₁ α' ⟨hα'h, hα'ϱ⟩⟩

/-- Helper: a composite of sharp maps is sharp. -/
theorem sharpMap_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : SharpMap f)
    (hg : SharpMap g) : SharpMap (f ≫ g) := by
  intro s hs
  rw [Category.assoc]
  exact hf _ (hg s hs)

theorem isTotal_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsTotal f)
    (hg : IsTotal g) : IsTotal (f ≫ g) := by
  show (f ≫ g) ≫ truth Z = truth X
  rw [Category.assoc, show g ≫ truth Z = truth Y from hg,
    show f ≫ truth Y = truth X from hf]

/-- Helper (221IV.2): isomorphisms are sharp maps (`α ∘ s` is the image of
`π_s ∘ α⁻¹`, cf. `isImage_compr_comp_inv`). -/
theorem sharpMap_of_isIso {X Y : C} (θ : X ⟶ Y) [IsIso θ] : SharpMap θ :=
  fun s hs => ⟨_, _, isImage_compr_comp_inv θ hs⟩

/-- Helper (221IV.2): postcomposing a pure map with an isomorphism is
again pure (by `isComprehension_comp_iso`; note that closure of pure maps
under composition, 211XI, is only available in an &-effectus). -/
theorem isPure_comp_iso {X Y Z : C} {f : X ⟶ Y} (hf : IsPure f) (θ : Y ⟶ Z)
    [IsIso θ] : IsPure (f ≫ θ) := by
  obtain ⟨Q, ξ, π, p, q, hξ, hπ, rfl⟩ := hf
  exact ⟨Q, ξ, π ≫ θ, p, inv θ ≫ q, hξ, isComprehension_comp_iso hπ θ,
    Category.assoc _ _ _⟩

/-- **221IV.2** (`dils-abstract-basics`, eff.tex:6820, Proposition):
dilations transport along isomorphisms:
`(P', ϱ ∘ α⁻¹, α ∘ h)` is a dilation of `f` when `(P, ϱ, h)` is. -/
theorem dils_abstract_basics_2 {P' : C} {f : X ⟶ Y} {ϱ : P ⟶ Y}
    {h : X ⟶ P} (d : IsDilation f ϱ h) (α : P ≅ P') :
    IsDilation f (α.inv ≫ ϱ) (h ≫ α.hom) := by
  obtain ⟨hs, ht, hp, hfac, huniv⟩ := d
  refine ⟨sharpMap_comp (sharpMap_of_isIso α.inv) hs,
    isTotal_comp (iso_isTotal α.inv) ht,
    isPure_comp_iso hp α.hom,
    by rw [Category.assoc, ← Category.assoc α.hom, α.hom_inv_id,
      Category.id_comp, hfac], ?_⟩
  intro P'' ϱ'' h'' hs'' ht'' hfac''
  obtain ⟨σ, ⟨hσ1, hσ2⟩, hσu⟩ := huniv ϱ'' h'' hs'' ht'' hfac''
  refine ⟨α.inv ≫ σ, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, ← Category.assoc α.hom, α.hom_inv_id,
      Category.id_comp, hσ1]
  · rw [Category.assoc, hσ2]
  · rintro σ' ⟨hσ'1, hσ'2⟩
    have h1 : α.hom ≫ σ' = σ := by
      refine hσu (α.hom ≫ σ') ⟨by rw [← Category.assoc, hσ'1], ?_⟩
      rw [Category.assoc, hσ'2, ← Category.assoc, α.hom_inv_id,
        Category.id_comp]
    rw [← h1, ← Category.assoc, α.inv_hom_id, Category.id_comp]

/-- Helper (221IV.3/.4): the identity is pure — it is the first component
of `diamondPositive_id`, so the Proposition needs no purity hypothesis. -/
theorem isPure_id (X : C) : IsPure (𝟙 X) := (diamondPositive_id X).1

/-- **221IV.3** (`dils-abstract-basics`, eff.tex:6820, Proposition):
`(X, ϱ, id)` is the dilation of a sharp total map `ϱ`. -/
theorem dils_abstract_basics_3 {ϱ : X ⟶ Y} (hs : SharpMap ϱ)
    (ht : IsTotal ϱ) :
    IsDilation ϱ ϱ (𝟙 X) := by
  refine ⟨hs, ht, isPure_id X, Category.id_comp _, ?_⟩
  intro P' ϱ' h' _ _ hfac
  refine ⟨h', ⟨Category.id_comp _, hfac⟩, ?_⟩
  rintro σ ⟨hσ, -⟩
  rw [← hσ, Category.id_comp]

/-- **221IV.4** (`dils-abstract-basics`, eff.tex:6820, Proposition): if
`(P, ϱ, h)` is a dilation (of some map), then `(P, id, h)` is a dilation
of `h`. -/
theorem dils_abstract_basics_4 {f : X ⟶ Y} {ϱ : P ⟶ Y} {h : X ⟶ P}
    (d : IsDilation f ϱ h) :
    IsDilation h (𝟙 P) h := by
  obtain ⟨hsϱ, htϱ, hph, hfac, huniv⟩ := d
  refine ⟨sharpMap_of_isIso (𝟙 P), iso_isTotal (𝟙 P), hph, Category.comp_id _, ?_⟩
  intro P' ϱ' h' hsϱ' htϱ' hfac'
  -- `(P', ϱ' ≫ ϱ, h')` is a factorization of `f`
  have hfac'' : h' ≫ (ϱ' ≫ ϱ) = f := by
    rw [← Category.assoc, hfac', hfac]
  obtain ⟨σ, ⟨hσ1, hσ2⟩, hσu⟩ :=
    huniv (ϱ' ≫ ϱ) h' (sharpMap_comp hsϱ' hsϱ) (isTotal_comp htϱ' htϱ) hfac''
  -- `σ ≫ ϱ'` mediates `(P, ϱ, h)` with itself, hence is the identity
  obtain ⟨τ, -, hτu⟩ := huniv ϱ h hsϱ htϱ hfac
  have hid' : σ ≫ ϱ' = 𝟙 P := by
    rw [hτu (σ ≫ ϱ') ⟨by rw [← Category.assoc, hσ1, hfac'],
      by rw [Category.assoc]; exact hσ2⟩,
      hτu (𝟙 P) ⟨Category.comp_id _, Category.id_comp _⟩]
  refine ⟨σ, ⟨hσ1, hid'⟩, ?_⟩
  rintro σ' ⟨hσ'1, hσ'2⟩
  refine hσu σ' ⟨hσ'1, ?_⟩
  rw [← Category.assoc, hσ'2, Category.id_comp]

/-- **221IV.5** (`dils-abstract-basics`, eff.tex:6820, Proposition): for a
quotient `ξ : X ⟶ Q` and `f : Q ⟶ Y` with dilation `(P, ϱ, h)`, the triple
`(P, ϱ, h ∘ ξ)` is a dilation of `f ∘ ξ`.

Purity of `h ∘ ξ`, which the Proposition asserts and its proof passes over
in silence (ERRATA, `221IV.5/.6/.7`), is **not** a hypothesis: it is
discharged here from purity of `h` alone.  Writing `h = ξ' ∘ π` with `ξ'` a
quotient and `π` a comprehension, `h ∘ ξ = π ∘ (ξ' ∘ ξ)`, and `ξ' ∘ ξ` is a
quotient by **197IX** (`quotients_composition`) — so no appeal to 211XI, and
no &-effectus, is needed. -/
theorem dils_abstract_basics_5 {Q : C} {p : Pred X} {ξ : X ⟶ Q}
    (hξ : IsQuotient p ξ) {f : Q ⟶ Y} {ϱ : P ⟶ Y} {h : Q ⟶ P}
    (d : IsDilation f ϱ h) :
    IsDilation (ξ ≫ f) ϱ (ξ ≫ h) := by
  obtain ⟨hsϱ, htϱ, hph, hfac, huniv⟩ := d
  haveI : Epi ξ := quotient_basics_6 hξ
  -- purity of `ξ ≫ h`: quotients compose (197IX)
  have hpure : IsPure (ξ ≫ h) := by
    obtain ⟨Q', ξ', π, p', q', hξ', hπ, he⟩ := hph
    have hq : IsQuotient (orth (orth p)) ξ := by rwa [eabasics_orth_orth]
    have hq' : IsQuotient (orth (orth p')) ξ' := by rwa [eabasics_orth_orth]
    exact ⟨Q', ξ ≫ ξ', π, _, q', quotients_composition hq hq', hπ,
      by rw [he, Category.assoc]⟩
  refine ⟨hsϱ, htϱ, hpure, by rw [Category.assoc, hfac], ?_⟩
  intro P' ϱ' h' hsϱ' htϱ' hfac'
  -- `h'` factors through the quotient `ξ`
  have ht' : ϱ' ≫ truth Y = truth P' := htϱ'
  have hle : (h' ≫ truth P') ≼ orth p := by
    rw [← quotient_basics_5 hξ]
    have e : h' ≫ truth P' = ξ ≫ (f ≫ truth Y) := by
      rw [← ht', ← Category.assoc, hfac', Category.assoc]
    rw [e]
    exact comp_le_comp ξ (pred_le_truth _)
  obtain ⟨h'', hh'', -⟩ := hξ.2 h' hle
  have hfacQ : h'' ≫ ϱ' = f := by
    apply (cancel_epi ξ).mp
    rw [← Category.assoc, hh'', hfac']
  obtain ⟨σ, ⟨hσ1, hσ2⟩, hσu⟩ := huniv ϱ' h'' hsϱ' htϱ' hfacQ
  refine ⟨σ, ⟨by rw [Category.assoc, hσ1, hh''], hσ2⟩, ?_⟩
  rintro σ' ⟨hσ'1, hσ'2⟩
  refine hσu σ' ⟨?_, hσ'2⟩
  apply (cancel_epi ξ).mp
  rw [← Category.assoc, hσ'1, hh'']

/-- **221IV.6** (`dils-abstract-basics`, eff.tex:6820, Proposition):
conversely, if `(P, ϱ, h)` is a dilation of `f ∘ ξ` for a quotient `ξ`,
then `(P, ϱ, h'')` is a dilation of `f`, where `h''` is the unique map
with `h'' ∘ ξ = h`. -/
theorem dils_abstract_basics_6 {Q : C} {p : Pred X} {ξ : X ⟶ Q}
    (hξ : IsQuotient p ξ) {f : Q ⟶ Y} {ϱ : P ⟶ Y} {h : X ⟶ P}
    (d : IsDilation (ξ ≫ f) ϱ h) :
    ∃ h'' : Q ⟶ P, ξ ≫ h'' = h ∧ IsDilation f ϱ h'' := by
  obtain ⟨hsϱ, htϱ, hph, hfac, huniv⟩ := d
  haveI : Epi ξ := quotient_basics_6 hξ
  -- `h` factors through the quotient `ξ`
  have ht : ϱ ≫ truth Y = truth P := htϱ
  have hle : (h ≫ truth P) ≼ orth p := by
    rw [← quotient_basics_5 hξ]
    have e : h ≫ truth P = ξ ≫ (f ≫ truth Y) := by
      rw [← ht, ← Category.assoc, hfac, Category.assoc]
    rw [e]
    exact comp_le_comp ξ (pred_le_truth _)
  obtain ⟨h'', hh'', -⟩ := hξ.2 h hle
  have hfacQ : h'' ≫ ϱ = f := by
    apply (cancel_epi ξ).mp
    rw [← Category.assoc, hh'', hfac]
  refine ⟨h'', hh'', hsϱ, htϱ, ?_, hfacQ, ?_⟩
  · -- purity of `h''`: pure maps divide on the left by quotients, applied to
    -- `ξ ≫ h'' = h` (the thesis leaves this step implicit, eff.tex:6906)
    exact isPure_of_isQuotient_comp hξ (by rw [hh'']; exact hph)
  · intro P' ϱ' h' hsϱ' htϱ' hfac'
    have hfac'' : (ξ ≫ h') ≫ ϱ' = ξ ≫ f := by
      rw [Category.assoc, hfac']
    obtain ⟨σ, ⟨hσ1, hσ2⟩, hσu⟩ := huniv ϱ' (ξ ≫ h') hsϱ' htϱ' hfac''
    refine ⟨σ, ⟨?_, hσ2⟩, ?_⟩
    · apply (cancel_epi ξ).mp
      rw [← Category.assoc, hh'', hσ1]
    · rintro σ' ⟨hσ'1, hσ'2⟩
      refine hσu σ' ⟨?_, hσ'2⟩
      rw [← hh'', Category.assoc, hσ'1]

/-- **221IV.7** (`dils-abstract-basics`, eff.tex:6820, Proposition):
dilations are closed under coproducts:
`(P₁ + P₂, [ϱ₁, ϱ₂], h₁ + h₂)` dilates `[f₁, f₂]`.

The Proposition *asserts* that `[ϱ₁, ϱ₂]` is sharp and `h₁ + h₂` pure; here
they are hypotheses, because the section only assumes a ⋄-effectus, in which
the Proposition asserts all three side conditions of the new triple and its
proof addresses none of them (ERRATA, `221IV.5/.6/.7`), so all three are
discharged here: sharpness of `[ϱ₁, ϱ₂]` from `img_tupling_sharp` (203XIV,
`[s,t]` is sharp iff `s` and `t` are), purity of `h₁ + h₂` from
`isQuotient_coprod_map` and `isComprehension_coprod_map` above, and totality
of `[ϱ₁, ϱ₂]` from 181IV (`cotupl_pcm_one`).  No appeal to 211XI, hence no
&-effectus, is needed. -/
theorem dils_abstract_basics_7 {X₁ X₂ P₁ P₂ : C}
    {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y} {ϱ₁ : P₁ ⟶ Y} {ϱ₂ : P₂ ⟶ Y}
    {h₁ : X₁ ⟶ P₁} {h₂ : X₂ ⟶ P₂}
    (d₁ : IsDilation f₁ ϱ₁ h₁) (d₂ : IsDilation f₂ ϱ₂ h₂) :
    IsDilation (coprod.desc f₁ f₂) (coprod.desc ϱ₁ ϱ₂)
      (coprod.map h₁ h₂) := by
  obtain ⟨hs₁, ht₁, hp₁, hfac₁, huniv₁⟩ := d₁
  obtain ⟨hs₂, ht₂, hp₂, hfac₂, huniv₂⟩ := d₂
  -- `[ϱ₁, ϱ₂] ∘ 1 = [ϱ₁ ∘ 1, ϱ₂ ∘ 1] = [1, 1] = 1` (181IV)
  have htcop : IsTotal (coprod.desc ϱ₁ ϱ₂) := by
    show coprod.desc ϱ₁ ϱ₂ ≫ truth Y = truth (P₁ ⨿ P₂)
    rw [← cotupl_pcm_one P₁ P₂, ← show ϱ₁ ≫ truth Y = truth P₁ from ht₁,
      ← show ϱ₂ ≫ truth Y = truth P₂ from ht₂]
    exact coprod.desc_comp _ _ _
  -- `[ϱ₁, ϱ₂] ∘ s = [ϱ₁ ∘ s, ϱ₂ ∘ s]` is sharp by 203XIV
  have hscop : SharpMap (coprod.desc ϱ₁ ϱ₂) := by
    intro s hs
    rw [coprod.desc_comp]
    exact (img_tupling_sharp _ _).mpr ⟨hs₁ s hs, hs₂ s hs⟩
  -- `h₁ + h₂ = (ξ₁ + ξ₂) ; (π₁ + π₂)` is a quotient followed by a
  -- comprehension
  have hpcop : IsPure (coprod.map h₁ h₂) := by
    obtain ⟨Q₁, ξ₁, π₁, r₁, s₁, hξ₁, hπ₁, e₁⟩ := hp₁
    obtain ⟨Q₂, ξ₂, π₂, r₂, s₂, hξ₂, hπ₂, e₂⟩ := hp₂
    refine ⟨Q₁ ⨿ Q₂, coprod.map ξ₁ ξ₂, coprod.map π₁ π₂, _, _,
      isQuotient_coprod_map hξ₁ hξ₂, isComprehension_coprod_map hπ₁ hπ₂, ?_⟩
    rw [e₁, e₂, coprod.map_map]
  refine ⟨hscop, htcop, hpcop, ?_, ?_⟩
  · rw [coprod.map_desc, hfac₁, hfac₂]
  · intro P' ϱ' h' hsϱ' htϱ' hfac'
    have e₁ : (coprod.inl ≫ h') ≫ ϱ' = f₁ := by
      rw [Category.assoc, hfac', coprod.inl_desc]
    have e₂ : (coprod.inr ≫ h') ≫ ϱ' = f₂ := by
      rw [Category.assoc, hfac', coprod.inr_desc]
    obtain ⟨σ₁, ⟨hσ₁1, hσ₁2⟩, hσ₁u⟩ :=
      huniv₁ ϱ' (coprod.inl ≫ h') hsϱ' htϱ' e₁
    obtain ⟨σ₂, ⟨hσ₂1, hσ₂2⟩, hσ₂u⟩ :=
      huniv₂ ϱ' (coprod.inr ≫ h') hsϱ' htϱ' e₂
    refine ⟨coprod.desc σ₁ σ₂, ⟨?_, ?_⟩, ?_⟩
    · refine coprod.hom_ext ?_ ?_
      · rw [← Category.assoc, coprod.inl_map, Category.assoc, coprod.inl_desc,
          hσ₁1]
      · rw [← Category.assoc, coprod.inr_map, Category.assoc, coprod.inr_desc,
          hσ₂1]
    · refine coprod.hom_ext ?_ ?_
      · rw [← Category.assoc, coprod.inl_desc, hσ₁2, coprod.inl_desc]
      · rw [← Category.assoc, coprod.inr_desc, hσ₂2, coprod.inr_desc]
    · rintro σ' ⟨hσ'1, hσ'2⟩
      have k₁ : coprod.inl ≫ σ' = σ₁ := by
        refine hσ₁u _ ⟨?_, ?_⟩
        · rw [← Category.assoc, ← coprod.inl_map h₁ h₂, Category.assoc, hσ'1]
        · rw [Category.assoc, hσ'2, coprod.inl_desc]
      have k₂ : coprod.inr ≫ σ' = σ₂ := by
        refine hσ₂u _ ⟨?_, ?_⟩
        · rw [← Category.assoc, ← coprod.inr_map h₁ h₂, Category.assoc, hσ'1]
        · rw [Category.assoc, hσ'2, coprod.inr_desc]
      refine coprod.hom_ext ?_ ?_
      · rw [coprod.inl_desc, k₁]
      · rw [coprod.inr_desc, k₂]

-- **221III** (eff.tex:6805, Example), `vn_has_dilations`: the effectus
-- `vNᵒᵖ` has dilations (Paschke dilations).  Moved to
-- `Theses/B/Eff/VNExamples.lean` (author ruling 2026-08-17): it needs the
-- Paschke development of `B/Dils`, and this file must keep importing only
-- `Theses.Common`.

end Dilations

section SideEffects

variable [AndThenEffectus C] {X Y P : C}

/-- The claim implicit in 223II that `asrt_p ⊥ asrt_{pᵖ}` (so that their
sum `sef_p` exists). -/
theorem asrt_perp_asrt_orth (p : Pred X) :
    Perp (asrt p) (asrt (orth p)) := by
  -- summability criterion of an effectus in partial form: `1∘f ⊥ 1∘g ⟹ f ⊥ g`
  refine EffectusPartialForm.perp_of_one_perp ?_
  show Perp (asrt p ≫ truth X) (asrt (orth p) ≫ truth X)
  rw [(asrt_spec p).2, (asrt_spec (orth p)).2]
  exact EffectAlgebra.perp_orth p

/-- **223II** (`sefp`, eff.tex:7038, Definition): the **side-effect**
`sef_p = asrt_p ⋁ asrt_{pᵖ}` of measuring the predicate `p`. -/
noncomputable def sef (p : Pred X) : X ⟶ X :=
  ovee (asrt p) (asrt (orth p)) (asrt_perp_asrt_orth p)

/-- **223II** (`sefp`, eff.tex:7044, Definition): the set
`Inv f = {p : f ∘ sef_p = f}` of predicates whose measurement does not
disturb `f`. -/
def InvSet (f : X ⟶ Y) : Set (Pred X) :=
  { p : Pred X | sef p ≫ f = f }

/-- **223V** (eff.tex:7076, Definition): the down-set
`↓f = {g : g ≤ f}` of a map in an &-effectus. -/
def belowSet (f : X ⟶ Y) : Set (X ⟶ Y) := { g : X ⟶ Y | g ≼ f }

/-- **223V** (eff.tex:7076, Definition): a dilation `(P, ϱ, h)` of `f` has
**the order correspondence** when there is an order isomorphism
`Θ : ↓f → Inv ϱ` with `g = ϱ ∘ asrt_{Θ(g)} ∘ h` for every `g ≤ f`. -/
def DilationOrderCorrespondence (f : X ⟶ Y) (ϱ : P ⟶ Y) (h : X ⟶ P) :
    Prop :=
  ∃ Θ : belowSet f ≃ InvSet ϱ,
    (∀ g₁ g₂ : belowSet f, g₁.1 ≼ g₂.1 ↔ (Θ g₁).1 ≼ (Θ g₂).1) ∧
    ∀ g : belowSet f, g.1 = h ≫ asrt (Θ g).1 ≫ ϱ

-- **223VI** (eff.tex:7095, Example), `vn_dilation_order_correspondence`:
-- every dilation in `vNᵒᵖ` has the order correspondence.  Moved to
-- `Theses/B/Eff/VNExamples.lean` (author ruling 2026-08-17): it needs the
-- Paschke correspondence of `B/Dils`, and this file must keep importing
-- only `Theses.Common`.

end SideEffects

end Theses.B.Eff
