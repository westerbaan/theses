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
  choice from `pureDagger_existsUnique` (= the well-definedness argument
  of 217I).
* Not separately formalized: the examples 214II (`Hilb`), 215II/215VIa–VII
  (the concrete description of the dagger on `vN`), the Setting 219II with
  its internal lemmas 219III, 219V, 219VII, 219IX, 219X, 219XIII, 219XIV
  (proof infrastructure for 219XVI, represented here by the standalone
  219XI and 219XVI), the quantum-gate discussion 222I–222IV, the
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

/-- **214I** (`dagger-effectus`, eff.tex:5257, Definition): a **†-category**
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

/-- **214I.1** (`dagger-effectus`, eff.tex:5277, Definition): an endomap of
a †-category is **†-self-adjoint** when `f† = f`. -/
def DaggerCat.SelfAdjoint {X : D} (f : X ⟶ X) : Prop := dag f = f

/-- **214I.2** (`dagger-effectus`, eff.tex:5281, Definition): an endomap is
**†-positive** when `f = g† ∘ g` for some map `g`. -/
def DaggerCat.IsPositive {X : D} (f : X ⟶ X) : Prop :=
  ∃ (Y : D) (g : X ⟶ Y), f = g ≫ dag g

/-- **214I.3** (`dagger-effectus`, eff.tex:5285, Definition): an isomorphism
`α` is **†-unitary** when `α⁻¹ = α†`. -/
def DaggerCat.Unitary {X Y : D} (α : X ≅ Y) : Prop := α.inv = dag α.hom

end DaggerCat

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

/-- **215I** (eff.tex:5299, Definition): a **†-effectus** is an &-effectus
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

/-- **215III** (`dagger-theorem`, eff.tex:5327, Theorem) and **215V**
(eff.tex:5348): a **†'-effectus** is an &-effectus such that

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

/-- **215III** (`dagger-theorem`, eff.tex:5327, Theorem): an &-effectus is
a †-effectus if and only if it is a †'-effectus (necessity is 216XI,
sufficiency 220II). -/
theorem dagger_theorem :
    Nonempty (DaggerEffectus C) ↔ DaggerPrimeEffectus C := sorry

/-- **215VI** (`vn-is-dagger-category`, eff.tex:5355, Corollary): the
&-effectus `vNᵒᵖ` is a †-effectus. -/
theorem vn_is_dagger_category (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    ∀ hA : AndThenEffectus WStarCPSU.{u}ᵒᵖ,
      letI := hA
      Nonempty (DaggerEffectus WStarCPSU.{u}ᵒᵖ) := sorry

end DaggerEffectus

/-! ## Consequences of the †-effectus axioms (parsec 216) -/

section DaggerConsequences

variable [AndThenEffectus C] {X Y : C}

/-- **216I** (`diamond-is-dagger-positive`, eff.tex:5440, Lemma): in a
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

/-- **216III** (`dagger-eff-square-root`, eff.tex:5464, Lemma): in a
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

/-- **216V** (`asrt-iso`, eff.tex:5507, Proposition): in an &-effectus with
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

/-- **216VII** (`dagger-of-zeta`, eff.tex:5537, Proposition): in a
†-effectus `ζ_s† = π_s` (for the corresponding pair of 211IX). -/
theorem dagger_of_zeta (d : DaggerEffectus C) {s : Pred X} (hs : IsSharp s) :
    d.daggerCat.dag (X := PureCat.of X) (Y := PureCat.of (comprObj s))
        ⟨zetaMap s hs, isPure_of_isQuotient (zetaMap_spec s hs).1⟩ =
      ⟨comprMap s, isPure_comprehension C (isComprehension_comprMap s)⟩ :=
  sorry

/-- **216IX** (`dagger-of-iso`, eff.tex:5575, Corollary), first half: in a
†-effectus `π_s` is ⋄-adjoint to `ζ_s`. -/
theorem dagger_of_iso_adjoint (d : DaggerEffectus C) {s : Pred X}
    (hs : IsSharp s) : DiamondAdjoint (comprMap s) (zetaMap s hs) := sorry

/-- **216IX** (`dagger-of-iso`, eff.tex:5575, Corollary), second half: in a
†-effectus `α† = α⁻¹` for every isomorphism `α` of `Pure C`. -/
theorem dagger_of_iso (d : DaggerEffectus C) {P Q : PureCat C} (α : P ≅ Q) :
    d.daggerCat.dag α.hom = α.inv := sorry

/-- **216X** (`zeta-through-asrt`, eff.tex:5581, Exercise): in an
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

/-- **216XI** (`dagger-thm-necessity`, eff.tex:5590, Theorem): a †-effectus
is a †'-effectus. -/
theorem dagger_thm_necessity (d : DaggerEffectus C) :
    DaggerPrimeEffectus C := sorry

end DaggerConsequences

/-! ## The dagger of a pure map in a †'-effectus (parsec 217) -/

section PureDagger

variable [AndThenEffectus C] {X Y Z : C}

/-- **217II** (`dagger-definition2`, eff.tex:5738, Definition), as a
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

/-- **217I–II** (`dagger-definition2`, eff.tex:5670–5738): in a
†'-effectus every pure map has a unique dagger in the sense of
`IsDaggerOf` (well-definedness is the argument of 217I). -/
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

/-- **217II** (`dagger-definition2`, eff.tex:5738, Definition): the dagger
`f†` of a pure map `f` in a †'-effectus. -/
noncomputable def pureDagger [DaggerPrimeEffectus C] (f : X ⟶ Y)
    (hf : IsPure f) : Y ⟶ X :=
  (pureDagger_existsUnique f hf).exists.choose

/-- The defining property of `pureDagger` (217II). -/
theorem isDaggerOf_pureDagger [DaggerPrimeEffectus C] (f : X ⟶ Y)
    (hf : IsPure f) : IsDaggerOf f (pureDagger f hf) :=
  (pureDagger_existsUnique f hf).exists.choose_spec

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

/-- **217III** (`dagger-prime-basics`, eff.tex:5752, Exercise):
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

/-- **217III** (`dagger-prime-basics`, eff.tex:5752, Exercise):
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

/-- **217III** (`dagger-prime-basics`, eff.tex:5752, Exercise):
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

/-- **217III** (`dagger-prime-basics`, eff.tex:5752, Exercise):
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

/-- **218II** (`quotcompr-diamond-adjoint`, eff.tex:5774, Lemma): in a
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

/-- **218IV** (`dfn-pristine`, eff.tex:5805, Definition): a map `f` in an
&-effectus is **pristine** when it is pure and `1 ∘ f` is sharp.
(Pristine maps are not closed under composition, 218V.) -/
def Pristine (f : X ⟶ Y) : Prop :=
  IsPure f ∧ IsSharp (f ≫ truth Y)

/-- **218VI** (`standard-form-pristine`, eff.tex:5825, Exercise): every
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

/-- Helper for 218VII (the first computation of eff.tex:5854): in a
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

/-- **218VII** (`pristine-asrt`, eff.tex:5832, Proposition): in a
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

/-- **218IX.1** (`asrt-pristine-reverse`, eff.tex:5881, Exercise): if
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

/-- **218IX.2** (`asrt-pristine-reverse`, eff.tex:5881, Exercise):
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

/-- **218IX.3** (`asrt-pristine-reverse`, eff.tex:5881, Exercise):
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

/-- **218IX.4** (`asrt-pristine-reverse`, eff.tex:5881, Exercise):
`p ∘ h† ≤ im h` for any predicate `p` and pristine `h`. -/
theorem asrt_pristine_reverse_4 [DaggerPrimeEffectus C] {h : X ⟶ Y}
    (hp : Pristine h) (p : Pred X) :
    (pureDagger h hp.1 ≫ p) ≼ imPred h := by
  have h1 := comp_le_comp (pureDagger h hp.1) (pred_le_truth p)
  rwa [pristine_dagger_truth hp] at h1

/-- **218IX.5** (`asrt-pristine-reverse`, eff.tex:5881, Exercise): if
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

/-- **218X** (`prist-asrt-decomp`, eff.tex:5898, Proposition), first half:
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

/-- **218X** (`prist-asrt-decomp`, eff.tex:5898, Proposition), first half:
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

/-- **218X** (`prist-asrt-decomp`, eff.tex:5898, Proposition), second half:
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

/-- **218XII** (`dagger-idempotent`, eff.tex:5946, Proposition): in a
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

/-- **219XI** (`dagger-iso-mu`, eff.tex:6266, Proposition): in a
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
        comprMap (ceilPred (andThen b a)) ≫ asrt (andThen b a) := sorry

/-- **219XVI** (`dagger-is-functor`, eff.tex:6552, Proposition): in a
†'-effectus, `(f ∘ g)† = g† ∘ f†` for pure `f, g`. -/
theorem dagger_is_functor [DaggerPrimeEffectus C] {g : X ⟶ Y} {f : Y ⟶ Z}
    (hg : IsPure g) (hf : IsPure f) :
    pureDagger (g ≫ f) (upm_closed_pure hg hf) =
      pureDagger f hf ≫ pureDagger g hg := sorry

/-- **220II** (`dagger-thm-sufficiency`, eff.tex:6682, Theorem): a
†'-effectus is a †-effectus, with the dagger of 217II. -/
theorem dagger_thm_sufficiency [DaggerPrimeEffectus C] :
    Nonempty (DaggerEffectus C) := sorry

end PureDagger

/-! ## Dilations (parsecs 221–223) -/

section Dilations

variable [DiamondEffectus C] {X Y P : C}

/-- **221II** (`dfn-eff-dilations`, eff.tex:6803, Definition): a
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

/-- **221II** (`dfn-eff-dilations`, eff.tex:6819, Definition): an effectus
**has dilations** when every map has a dilation. -/
class HasDilations (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
    [DiamondEffectus C] : Prop where
  dil : ∀ {X Y : C} (f : X ⟶ Y),
    ∃ (P : C) (ϱ : P ⟶ Y) (h : X ⟶ P), IsDilation f ϱ h

/-- **221IV.1** (`dils-abstract-basics`, eff.tex:6837, Proposition): any
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

/-- **221IV.2** (`dils-abstract-basics`, eff.tex:6837, Proposition):
dilations transport along isomorphisms:
`(P', ϱ ∘ α⁻¹, α ∘ h)` is a dilation of `f` when `(P, ϱ, h)` is. -/
theorem dils_abstract_basics_2 {P' : C} {f : X ⟶ Y} {ϱ : P ⟶ Y}
    {h : X ⟶ P} (d : IsDilation f ϱ h) (α : P ≅ P') :
    IsDilation f (α.inv ≫ ϱ) (h ≫ α.hom) := sorry

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

/-- **221IV.3** (`dils-abstract-basics`, eff.tex:6837, Proposition):
`(X, ϱ, id)` is the dilation of a sharp total map `ϱ`. -/
theorem dils_abstract_basics_3 {ϱ : X ⟶ Y} (hs : SharpMap ϱ)
    (ht : IsTotal ϱ) (hp : IsPure (𝟙 X)) :
    IsDilation ϱ ϱ (𝟙 X) := by
  refine ⟨hs, ht, hp, Category.id_comp _, ?_⟩
  intro P' ϱ' h' _ _ hfac
  refine ⟨h', ⟨Category.id_comp _, hfac⟩, ?_⟩
  rintro σ ⟨hσ, -⟩
  rw [← hσ, Category.id_comp]

/-- **221IV.4** (`dils-abstract-basics`, eff.tex:6837, Proposition): if
`(P, ϱ, h)` is a dilation (of some map), then `(P, id, h)` is a dilation
of `h`. -/
theorem dils_abstract_basics_4 {f : X ⟶ Y} {ϱ : P ⟶ Y} {h : X ⟶ P}
    (d : IsDilation f ϱ h) (hid : SharpMap (𝟙 P) ∧ IsTotal (𝟙 P)) :
    IsDilation h (𝟙 P) h := by
  obtain ⟨hsϱ, htϱ, hph, hfac, huniv⟩ := d
  refine ⟨hid.1, hid.2, hph, Category.comp_id _, ?_⟩
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

/-- **221IV.5** (`dils-abstract-basics`, eff.tex:6837, Proposition): for a
quotient `ξ : X ⟶ Q` and `f : Q ⟶ Y` with dilation `(P, ϱ, h)`, the triple
`(P, ϱ, h ∘ ξ)` is a dilation of `f ∘ ξ`. -/
theorem dils_abstract_basics_5 {Q : C} {p : Pred X} {ξ : X ⟶ Q}
    (hξ : IsQuotient p ξ) {f : Q ⟶ Y} {ϱ : P ⟶ Y} {h : Q ⟶ P}
    (d : IsDilation f ϱ h) (hpure : IsPure (ξ ≫ h)) :
    IsDilation (ξ ≫ f) ϱ (ξ ≫ h) := by
  obtain ⟨hsϱ, htϱ, hph, hfac, huniv⟩ := d
  haveI : Epi ξ := quotient_basics_6 hξ
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

/-- **221IV.6** (`dils-abstract-basics`, eff.tex:6837, Proposition):
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
  · -- purity of `h''`: it is the total-part of the pure map `h`… we reuse
    -- purity of `h` via the factorization `h = ξ ≫ h''`
    sorry
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

/-- **221IV.7** (`dils-abstract-basics`, eff.tex:6837, Proposition):
dilations are closed under coproducts:
`(P₁ + P₂, [ϱ₁, ϱ₂], h₁ + h₂)` dilates `[f₁, f₂]`. -/
theorem dils_abstract_basics_7 {X₁ X₂ P₁ P₂ : C}
    {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y} {ϱ₁ : P₁ ⟶ Y} {ϱ₂ : P₂ ⟶ Y}
    {h₁ : X₁ ⟶ P₁} {h₂ : X₂ ⟶ P₂}
    (d₁ : IsDilation f₁ ϱ₁ h₁) (d₂ : IsDilation f₂ ϱ₂ h₂)
    (hcop : SharpMap (coprod.desc ϱ₁ ϱ₂) ∧ IsTotal (coprod.desc ϱ₁ ϱ₂) ∧
      IsPure (coprod.map h₁ h₂)) :
    IsDilation (coprod.desc f₁ f₂) (coprod.desc ϱ₁ ϱ₂)
      (coprod.map h₁ h₂) := by
  obtain ⟨hs₁, ht₁, hp₁, hfac₁, huniv₁⟩ := d₁
  obtain ⟨hs₂, ht₂, hp₂, hfac₂, huniv₂⟩ := d₂
  refine ⟨hcop.1, hcop.2.1, hcop.2.2, ?_, ?_⟩
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

/-- **221III** (eff.tex:6822, Example): the effectus `vNᵒᵖ` has dilations
(Paschke dilations; the full subcategory `CvNᵒᵖ` does not, 221IIIa — not
formalized here). -/
theorem vn_has_dilations (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    ∀ hD : DiamondEffectus WStarCPSU.{u}ᵒᵖ,
      letI := hD
      HasDilations WStarCPSU.{u}ᵒᵖ := sorry

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

/-- **223II** (`sefp`, eff.tex:7055, Definition): the **side-effect**
`sef_p = asrt_p ⋁ asrt_{pᵖ}` of measuring the predicate `p`. -/
noncomputable def sef (p : Pred X) : X ⟶ X :=
  ovee (asrt p) (asrt (orth p)) (asrt_perp_asrt_orth p)

/-- **223II** (`sefp`, eff.tex:7061, Definition): the set
`Inv f = {p : f ∘ sef_p = f}` of predicates whose measurement does not
disturb `f`. -/
def InvSet (f : X ⟶ Y) : Set (Pred X) :=
  { p : Pred X | sef p ≫ f = f }

/-- **223V** (eff.tex:7093, Definition): the down-set
`↓f = {g : g ≤ f}` of a map in an &-effectus. -/
def belowSet (f : X ⟶ Y) : Set (X ⟶ Y) := { g : X ⟶ Y | g ≼ f }

/-- **223V** (eff.tex:7093, Definition): a dilation `(P, ϱ, h)` of `f` has
**the order correspondence** when there is an order isomorphism
`Θ : ↓f → Inv ϱ` with `g = ϱ ∘ asrt_{Θ(g)} ∘ h` for every `g ≤ f`. -/
def DilationOrderCorrespondence (f : X ⟶ Y) (ϱ : P ⟶ Y) (h : X ⟶ P) :
    Prop :=
  ∃ Θ : belowSet f ≃ InvSet ϱ,
    (∀ g₁ g₂ : belowSet f, g₁.1 ≼ g₂.1 ↔ (Θ g₁).1 ≼ (Θ g₂).1) ∧
    ∀ g : belowSet f, g.1 = h ≫ asrt (Θ g).1 ≫ ϱ

/-- **223VI** (eff.tex:7112, Example): every dilation in `vNᵒᵖ` has the
order correspondence (by the Paschke correspondence of the dils
chapter). -/
theorem vn_dilation_order_correspondence
    (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    ∀ hA : AndThenEffectus WStarCPSU.{u}ᵒᵖ,
      letI := hA
      ∀ {X Y P : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) (ϱ : P ⟶ Y) (h : X ⟶ P),
        IsDilation f ϱ h → DilationOrderCorrespondence f ϱ h := sorry

end SideEffects

end Theses.B.Eff
