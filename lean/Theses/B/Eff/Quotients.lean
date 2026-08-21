/-
Theses/B/Eff/Quotients.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
3663–4407: effectuses with quotients (parsecs 197–198), effectuses with
comprehension (199), kernels (200), pure maps (201), images and faithful
maps (202), sharp predicates, floor and ceiling (203–204), and cokernels
(205).

Design:
* `IsQuotient p ξ` / `IsComprehension p π` are the universal properties of
  197II / 199II; `HasQuotients C` / `HasComprehension C` / `HasImages C`
  are Prop-classes asserting existence, with chosen witnesses `quotMap p`
  (`ξ_p`), `comprMap p` (`π_p`) and `imPred f` (`im f`) obtained by choice.
* Kernels/cokernels (200II) are defined with respect to the zero maps of
  the PCM-enrichment (an effectus in partial form has a zero object, so
  these agree with the usual categorical notions).
* Not separately formalized: the concrete examples 197IV/199V/202IV
  (quotients = filters and comprehensions = corners in `vNᵒᵖ`, `EJA`,
  `OUS`, `OUG`), the remark 198IV on the chain of adjunctions
  `Q ⊣ 0 ⊣ U ⊣ 1 ⊣ K` (its constituents are 198II/198III/199VI), the
  purity discussion 201III–201V, and the sharpness example 203III.
-/
import Theses.B.Eff.StatesPredicates

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits

namespace Theses.B.Eff

universe u v

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-! ### Helper lemmas used throughout -/

/-- `0` is below every map (for the algebraic order of the hom-PCM). -/
theorem zero_le_hom {X Y : C} (f : X ⟶ Y) : (0 : X ⟶ Y) ≼ f :=
  ⟨f, PCM.zero_perp f, PCM.zero_ovee f⟩

/-- Every predicate is below the truth predicate. -/
theorem pred_le_truth {X : C} (p : Pred X) : p ≼ truth X :=
  ⟨orth p, EffectAlgebra.perp_orth p, EffectAlgebra.ovee_orth p⟩

/-- Precomposition is monotone for the algebraic order. -/
theorem comp_le_comp {W X Y : C} (f : W ⟶ X) {a b : X ⟶ Y} (h : a ≼ b) :
    (f ≫ a) ≼ (f ≫ b) := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨h', e⟩ := FinPAC.ovee_comp hc f
  exact ⟨f ≫ c, h', e.symm⟩

/-- The truth predicate on the initial object is `0` (the initial object of
an effectus in partial form is a zero object). -/
theorem truth_initial : truth (⊥_ C) = 0 := initial.hom_ext _ _

/-- Every map into the initial object is `0`. -/
theorem eq_zero_of_hom_to_initial {Z : C} (f : Z ⟶ ⊥_ C) : f = 0 := by
  have h : f ≫ truth (⊥_ C) = 0 := by rw [truth_initial, FinPAC.comp_zero]
  exact EffectusPartialForm.eq_zero_of_one_zero h

/-- Every predicate is below `(f ∘ 1ᵖ)ᵖ` — the condition for a map into an
object carrying the predicate `1` in `∫ Pred_□`. -/
theorem le_orth_comp_orth_one {W X : C} (f : W ⟶ X) (r : Pred W) :
    r ≼ orth (f ≫ orth (1 : Pred X)) := by
  have h0 : f ≫ orth (1 : Pred X) = 0 := by
    rw [eabasics_orth_one]; exact FinPAC.comp_zero _
  rw [h0, eabasics_orth_zero]
  exact pred_le_truth _

/-- Isomorphisms are total. -/
theorem iso_isTotal {X Y : C} (θ : X ⟶ Y) [IsIso θ] : IsTotal θ := by
  have key : ∀ {A B : C} (f : A ⟶ B), IsIso f → truth A ≼ (f ≫ truth B) := by
    intro A B f hf
    have := hf
    have h2 : (f ≫ (inv f ≫ truth A)) ≼ (f ≫ truth B) :=
      comp_le_comp f (pred_le_truth _)
    rwa [← Category.assoc, IsIso.hom_inv_id, Category.id_comp] at h2
  have h1 := key θ inferInstance
  have h2 := key (inv θ) inferInstance
  have h3 : (θ ≫ truth Y) ≼ (θ ≫ inv θ ≫ truth X) := comp_le_comp θ h2
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp] at h3
  exact eabasics_le_antisymm h3 h1

/-- `pᵖ ∘ f = 0` iff `p ∘ f = 1 ∘ f`. -/
theorem comp_orth_eq_zero_iff {W X : C} (f : W ⟶ X) (p : Pred X) :
    f ≫ orth p = 0 ↔ f ≫ p = f ≫ truth X := by
  have ovcongr : ∀ {a b a' b' : W ⟶ effObj C}, a = a' → b = b' →
      ∀ (h : Perp a b) (h' : Perp a' b'), ovee a b h = ovee a' b' h' := by
    intro a b a' b' ha hb h h'
    subst ha; subst hb; rfl
  have ovzero : ∀ (a : W ⟶ effObj C) (h : Perp a 0), ovee a 0 h = a := by
    intro a h; rw [PCM.ovee_comm]; exact PCM.zero_ovee a
  obtain ⟨h', e⟩ := FinPAC.ovee_comp (EffectAlgebra.perp_orth p) f
  have hone : ovee p (orth p) (EffectAlgebra.perp_orth p) = truth X :=
    EffectAlgebra.ovee_orth p
  have e1 : f ≫ truth X = ovee (f ≫ p) (f ≫ orth p) h' := by
    rw [← hone]; exact e
  constructor
  · intro hz
    have h0 : Perp (f ≫ p) (0 : W ⟶ effObj C) := PCM.perp_comm (PCM.zero_perp _)
    have h2 : ovee (f ≫ p) (f ≫ orth p) h' = f ≫ p :=
      (ovcongr rfl hz h' h0).trans (ovzero _ h0)
    exact (e1.trans h2).symm
  · intro hp
    have hpq : Perp (f ≫ truth X) (f ≫ orth p) := by rw [← hp]; exact h'
    have e2 : ovee (f ≫ truth X) (f ≫ orth p) hpq = f ≫ truth X :=
      (ovcongr hp.symm rfl hpq h').trans e1.symm
    have e3 : ovee (f ≫ orth p) (f ≫ truth X) (PCM.perp_comm hpq)
        = ovee (0 : W ⟶ effObj C) (f ≫ truth X) (PCM.zero_perp _) := by
      rw [PCM.zero_ovee, ← PCM.ovee_comm]; exact e2
    exact eabasics_cancellation (PCM.perp_comm hpq) (PCM.zero_perp _) e3

/-- A total map commutes with orthocomplementation of predicates:
`pᵖ ∘ f = (p ∘ f)ᵖ` when `f` is total. -/
theorem total_comp_orth {W X : C} {f : W ⟶ X} (hf : IsTotal f) (p : Pred X) :
    f ≫ orth p = orth (f ≫ p) := by
  obtain ⟨h', e⟩ := FinPAC.ovee_comp (EffectAlgebra.perp_orth p) f
  refine EffectAlgebra.orth_unique h' ?_
  rw [← e, EffectAlgebra.ovee_orth]
  exact hf

/-! ## Effectuses with quotients (parsec 197) -/

/-- **197II** (`dfn-quotient`, eff.tex:3653, Definition): a map
`ξ : X ⟶ X/p` is a **quotient** for a predicate `p` on `X` when
`1 ∘ ξ ≤ pᵖ` and, universally, every `f : X ⟶ Y` with `1 ∘ f ≤ pᵖ` factors
as `f = f' ∘ ξ` for a unique `f'`. -/
def IsQuotient {X Q : C} (p : Pred X) (ξ : X ⟶ Q) : Prop :=
  (ξ ≫ truth Q) ≼ orth p ∧
    ∀ ⦃Y : C⦄ (f : X ⟶ Y), (f ≫ truth Y) ≼ orth p →
      ∃! f' : Q ⟶ Y, ξ ≫ f' = f

/-- **197II** (`dfn-quotient`, eff.tex:3655, Definition): an **effectus with
quotients**: every predicate has a quotient. -/
class HasQuotients (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop where
  quot : ∀ {X : C} (p : Pred X), ∃ (Q : C) (ξ : X ⟶ Q), IsQuotient p ξ

/-- **197III** (`quot-not`, eff.tex:3678, Notation): the codomain `X/p` of a
chosen quotient for `p`. -/
noncomputable def quotObj [HasQuotients C] {X : C} (p : Pred X) : C :=
  (HasQuotients.quot p).choose

/-- **197III** (`quot-not`, eff.tex:3678, Notation): a chosen quotient
`ξ_p : X ⟶ X/p` for `p`. -/
noncomputable def quotMap [HasQuotients C] {X : C} (p : Pred X) :
    X ⟶ quotObj p :=
  (HasQuotients.quot p).choose_spec.choose

/-- The chosen `ξ_p` is a quotient for `p` (197III). -/
theorem isQuotient_quotMap [HasQuotients C] {X : C} (p : Pred X) :
    IsQuotient p (quotMap p) :=
  (HasQuotients.quot p).choose_spec.choose_spec

section QuotientBasics

variable {X Q Q' Z : C}

/-- **197V.1** (`quotient-basics`, eff.tex:3712, Exercise): postcomposing a
quotient for `p` with an isomorphism yields a quotient for `p`. -/
theorem quotient_basics_1 {p : Pred X} {ξ : X ⟶ Q} (h : IsQuotient p ξ)
    (θ : Q ⟶ Z) [IsIso θ] : IsQuotient p (ξ ≫ θ) := by
  have ht : θ ≫ truth Z = truth Q := iso_isTotal θ
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, ht]; exact h.1
  · intro Y f hf
    obtain ⟨f', hf', huniq⟩ := h.2 f hf
    refine ⟨inv θ ≫ f', ?_, ?_⟩
    · show (ξ ≫ θ) ≫ (inv θ ≫ f') = f
      rw [Category.assoc, ← Category.assoc θ, IsIso.hom_inv_id, Category.id_comp]
      exact hf'
    · intro g hg
      replace hg : (ξ ≫ θ) ≫ g = f := hg
      have hgf : ξ ≫ (θ ≫ g) = f := by rw [← Category.assoc]; exact hg
      have hg' := huniq _ hgf
      rw [← hg', ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- **197V.2** (`quotient-basics`, eff.tex:3720, Exercise): any two
quotients for `p` differ by a unique isomorphism. -/
theorem quotient_basics_2 {p : Pred X} {ξ₁ : X ⟶ Q} {ξ₂ : X ⟶ Q'}
    (h₁ : IsQuotient p ξ₁) (h₂ : IsQuotient p ξ₂) :
    ∃ θ : Q' ⟶ Q, IsIso θ ∧ ξ₂ ≫ θ = ξ₁ ∧
      ∀ θ' : Q' ⟶ Q, ξ₂ ≫ θ' = ξ₁ → θ' = θ := by
  obtain ⟨θ, hθ, huθ⟩ := h₂.2 ξ₁ h₁.1
  obtain ⟨θ', hθ', huθ'⟩ := h₁.2 ξ₂ h₂.1
  refine ⟨θ, ⟨⟨θ', ?_, ?_⟩⟩, hθ, huθ⟩
  · obtain ⟨u, -, huu⟩ := h₂.2 ξ₂ h₂.1
    rw [huu (θ ≫ θ') (show ξ₂ ≫ (θ ≫ θ') = ξ₂ by rw [← Category.assoc, hθ, hθ']),
      huu (𝟙 Q') (Category.comp_id _)]
  · obtain ⟨u, -, huu⟩ := h₁.2 ξ₁ h₁.1
    rw [huu (θ' ≫ θ) (show ξ₁ ≫ (θ' ≫ θ) = ξ₁ by rw [← Category.assoc, hθ', hθ]),
      huu (𝟙 Q) (Category.comp_id _)]

/-- **197V.3** (`quotient-basics`, eff.tex:3724, Exercise): isomorphisms are
quotients for `0`. -/
theorem quotient_basics_3 (f : X ⟶ Q) [IsIso f] :
    IsQuotient (0 : Pred X) f := by
  -- bsols.tex:2643: `id` is a quotient for `0` — every `f` is the unique map
  -- with `f' ∘ id = f` — and then so is every isomorphism, by the first point.
  have hid : IsQuotient (0 : Pred X) (𝟙 X) := by
    refine ⟨?_, ?_⟩
    · rw [Category.id_comp, eabasics_orth_zero]; exact pred_le_truth _
    · intro Y g _
      exact ⟨g, Category.id_comp g, fun g' hg' => (Category.id_comp g').symm.trans hg'⟩
  have h := quotient_basics_1 hid f
  rwa [Category.id_comp] at h

/-- **197V.4** (`quotient-basics`, eff.tex:3725, Exercise): maps into the
zero object are quotients for `1`. -/
theorem quotient_basics_4 (f : X ⟶ (⊥_ C)) :
    IsQuotient (1 : Pred X) f := by
  refine ⟨?_, ?_⟩
  · rw [eabasics_orth_one, truth_initial, FinPAC.comp_zero]
    exact pcm_preorder_refl _
  · intro Y g hg
    rw [eabasics_orth_one] at hg
    have hg0 : g = 0 := EffectusPartialForm.eq_zero_of_one_zero (eq_zero_of_le_zero hg)
    refine ⟨0, ?_, ?_⟩
    · show f ≫ (0 : (⊥_ C) ⟶ Y) = g
      rw [FinPAC.comp_zero, hg0]
    · intro g' _
      exact initial.hom_ext g' 0

/-- **197V.5** (`quotient-basics`, eff.tex:3726, Exercise): if `ξ` is a
quotient for `p`, then `1 ∘ ξ = pᵖ`. -/
theorem quotient_basics_5 {p : Pred X} {ξ : X ⟶ Q} (h : IsQuotient p ξ) :
    ξ ≫ truth Q = orth p := by
  -- `1 = id_I` (181XIII, `one-m-is-id`); proved inline to keep this file
  -- independent of the helper in `StatesPredicates`.
  have hid : truth (effObj C) = 𝟙 (effObj C) := by
    have hperp : Perp (𝟙 (effObj C)) (orth (𝟙 (effObj C))) := EffectAlgebra.perp_orth _
    obtain ⟨h', -⟩ := FinPAC.comp_ovee hperp (truth (effObj C))
    rw [Category.id_comp] at h'
    have hz : orth (𝟙 (effObj C)) ≫ truth (effObj C) = 0 :=
      EffectAlgebra.eq_zero_of_perp_one (PCM.perp_comm h')
    have he0 : orth (𝟙 (effObj C)) = 0 := EffectusPartialForm.eq_zero_of_one_zero hz
    have h2 := eabasics_orth_orth (𝟙 (effObj C))
    rw [he0, eabasics_orth_zero] at h2
    exact h2
  have hpp : ((orth p : X ⟶ effObj C) ≫ truth (effObj C)) ≼ orth p := by
    rw [hid, Category.comp_id]
    exact pcm_preorder_refl _
  obtain ⟨f, hf, -⟩ := h.2 (orth p) hpp
  have hle : (ξ ≫ f) ≼ (ξ ≫ truth Q) := comp_le_comp ξ (pred_le_truth f)
  rw [hf] at hle
  exact eabasics_le_antisymm h.1 hle

/-- **197V.6** (`quotient-basics`, eff.tex:3728, Exercise): quotients are
epic. -/
theorem quotient_basics_6 {p : Pred X} {ξ : X ⟶ Q} (h : IsQuotient p ξ) :
    Epi ξ := by
  constructor
  intro Y a b hab
  have hf : ((ξ ≫ a) ≫ truth Y) ≼ orth p := by
    rw [Category.assoc]
    exact pcm_preorder_trans (comp_le_comp ξ (pred_le_truth (a ≫ truth Y))) h.1
  obtain ⟨u, -, huu⟩ := h.2 (ξ ≫ a) hf
  rw [huu a rfl, huu b hab.symm]

/-- **197VII** (`quotient-total`, eff.tex:3738, Proposition): if
`ξ : X ⟶ X/pᵖ` is a quotient for `pᵖ`, then every `f : X ⟶ Z` with
`1 ∘ f = p` factors as `f = g ∘ ξ` for a unique *total* `g`.  (So every map
factors as a total map after a quotient.) -/
theorem quotient_total {p : Pred X} {ξ : X ⟶ Q} (hξ : IsQuotient (orth p) ξ)
    (f : X ⟶ Z) (hf : f ≫ truth Z = p) :
    ∃! g : Q ⟶ Z, IsTotal g ∧ ξ ≫ g = f := by
  have hle : (f ≫ truth Z) ≼ orth (orth p) := by
    rw [eabasics_orth_orth, hf]; exact pcm_preorder_refl _
  obtain ⟨g, hg, huniq⟩ := hξ.2 f hle
  have : Epi ξ := quotient_basics_6 hξ
  refine ⟨g, ⟨?_, hg⟩, fun g' hg' => huniq g' hg'.2⟩
  have : ξ ≫ (g ≫ truth Z) = ξ ≫ truth Q := by
    rw [← Category.assoc, hg, hf, quotient_basics_5 hξ, eabasics_orth_orth]
  exact (cancel_epi ξ).mp this

/-- **197IX** (`quotients-composition`, eff.tex:3755, Proposition): in an
effectus with quotients, quotients are closed under composition: if `ξ₁` is
a quotient for `pᵖ` and `ξ₂` a quotient for `qᵖ`, then `ξ₂ ∘ ξ₁` is a
quotient for `(q ∘ ξ₁)ᵖ`. -/
theorem quotients_composition [HasQuotients C] {Y : C} {p : Pred X}
    {q : Pred Y} {ξ₁ : X ⟶ Y} {ξ₂ : Y ⟶ Z}
    (h₁ : IsQuotient (orth p) ξ₁) (h₂ : IsQuotient (orth q) ξ₂) :
    IsQuotient (orth (ξ₁ ≫ q)) (ξ₁ ≫ ξ₂) := by
  have hε₁ : ξ₁ ≫ truth Y = p := by rw [quotient_basics_5 h₁, eabasics_orth_orth]
  have hε₂ : ξ₂ ≫ truth Z = q := by rw [quotient_basics_5 h₂, eabasics_orth_orth]
  have hcomp : (ξ₁ ≫ ξ₂) ≫ truth Z = ξ₁ ≫ q := by rw [Category.assoc, hε₂]
  obtain ⟨QQ, ξ, hξ⟩ := HasQuotients.quot (orth (ξ₁ ≫ q))
  have hεξ : ξ ≫ truth QQ = ξ₁ ≫ q := by
    rw [quotient_basics_5 hξ, eabasics_orth_orth]
  have hepi₁ : Epi ξ₁ := quotient_basics_6 h₁
  have hepi₂ : Epi ξ₂ := quotient_basics_6 h₂
  have hle : (ξ ≫ truth QQ) ≼ orth (orth p) := by
    rw [hεξ, eabasics_orth_orth, ← hε₁]
    exact comp_le_comp ξ₁ (pred_le_truth q)
  obtain ⟨u, hu, -⟩ := h₁.2 ξ hle
  have hut : u ≫ truth QQ = q := by
    refine (cancel_epi ξ₁).mp ?_
    rw [← Category.assoc, hu, hεξ]
  obtain ⟨v, hv, -⟩ := quotient_total h₂ u hut
  have hcond : ((ξ₁ ≫ ξ₂) ≫ truth Z) ≼ orth (orth (ξ₁ ≫ q)) := by
    rw [hcomp, eabasics_orth_orth]; exact pcm_preorder_refl _
  obtain ⟨g, hg, -⟩ := hξ.2 (ξ₁ ≫ ξ₂) hcond
  have hgv : g ≫ v = 𝟙 QQ := by
    have hcond' : (ξ ≫ truth QQ) ≼ orth (orth (ξ₁ ≫ q)) := by
      rw [hεξ, eabasics_orth_orth]; exact pcm_preorder_refl _
    obtain ⟨w, -, hwu⟩ := hξ.2 ξ hcond'
    have e1 : ξ ≫ (g ≫ v) = ξ := by
      rw [← Category.assoc, hg, Category.assoc, hv.2, hu]
    rw [hwu (g ≫ v) e1, hwu (𝟙 QQ) (Category.comp_id _)]
  have hvg : v ≫ g = 𝟙 Z := by
    have hepi : Epi (ξ₁ ≫ ξ₂) := epi_comp _ _
    refine (cancel_epi (ξ₁ ≫ ξ₂)).mp ?_
    rw [Category.comp_id, Category.assoc, ← Category.assoc ξ₂, hv.2,
      ← Category.assoc, hu, hg]
  have hiso : IsIso g := ⟨⟨v, hgv, hvg⟩⟩
  have hq := quotient_basics_1 hξ g
  rwa [hg] at hq

/-- **197XI** (`quot-fact-system`, eff.tex:3797, Exercise): (quotient, total)
is an orthogonal factorization system: if `t ∘ ξ = t' ∘ ξ'` with `ξ, ξ'`
quotients (for `p`, `p'`) and `t, t'` total, then there is a unique
isomorphism `θ` with `ξ' = θ ∘ ξ` and `t = t' ∘ θ`. -/
theorem quot_fact_system {p : Pred X} {p' : Pred X} {ξ : X ⟶ Q}
    {ξ' : X ⟶ Q'} {t : Q ⟶ Z} {t' : Q' ⟶ Z}
    (hξ : IsQuotient p ξ) (hξ' : IsQuotient p' ξ')
    (ht : IsTotal t) (ht' : IsTotal t') (hcomm : ξ ≫ t = ξ' ≫ t') :
    ∃ θ : Q ⟶ Q', IsIso θ ∧ ξ ≫ θ = ξ' ∧ θ ≫ t' = t ∧
      ∀ θ' : Q ⟶ Q', ξ ≫ θ' = ξ' → θ' = θ := by
  have hpp : orth p = orth p' := by
    rw [← quotient_basics_5 hξ, ← quotient_basics_5 hξ', ← ht, ← ht',
      ← Category.assoc, ← Category.assoc, hcomm]
  have hp : p = p' := by
    rw [← eabasics_orth_orth p, hpp, eabasics_orth_orth]
  subst hp
  obtain ⟨θ, hiso, hθ, huniq⟩ := quotient_basics_2 hξ' hξ
  have hepi : Epi ξ := quotient_basics_6 hξ
  refine ⟨θ, hiso, hθ, ?_, huniq⟩
  refine (cancel_epi ξ).mp ?_
  rw [← Category.assoc, hθ, hcomm]

end QuotientBasics

/-! ## The Grothendieck-style category `∫ Pred_□` (parsec 198) -/

/-- **198II** (`dfn-eff-grothendieck`, eff.tex:3821, Definition): the
category `∫ Pred_□` of an effectus `C`: objects are pairs `(X, p)` of an
object with a predicate; a morphism `(X,p) → (Y,q)` is a map `f : X ⟶ Y`
of `C` with `p ≤ (qᵖ ∘ f)ᵖ`. -/
structure PredSquare (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] :
    Type (max u v) where
  obj : C
  pred : Pred obj

/-- The category structure of `∫ Pred_□` (198II; identities and compositions
are checked to satisfy the predicate inequality). -/
instance : Category.{v} (PredSquare C) where
  Hom P R := { f : P.obj ⟶ R.obj // P.pred ≼ orth (f ≫ orth R.pred) }
  id P := ⟨𝟙 P.obj, by
    rw [Category.id_comp, eabasics_orth_orth]
    exact pcm_preorder_refl _⟩
  comp := fun {P R S} f g => ⟨f.1 ≫ g.1, by
    have h1 : (g.1 ≫ orth S.pred) ≼ orth R.pred :=
      eabasics_perp_iff_le_orth.mp
        (PCM.perp_comm (eabasics_perp_iff_le_orth.mpr g.2))
    have h3 := eabasics_le_iff_orth_le.mp (comp_le_comp f.1 h1)
    rw [Category.assoc]
    exact pcm_preorder_trans f.2 h3⟩
  id_comp _ := Subtype.ext (by simp)
  comp_id _ := Subtype.ext (by simp)
  assoc _ _ _ := Subtype.ext (by simp)

/-- **198II** (`dfn-eff-grothendieck`, eff.tex:3835, Definition): the
forgetful functor `U : ∫ Pred_□ → C`. -/
def predSquareForget (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] :
    PredSquare C ⥤ C where
  obj P := P.obj
  map f := f.1

/-- **198II** (`dfn-eff-grothendieck`, eff.tex:3839, Definition): the
functor `0 : C → ∫ Pred_□`, `X ↦ (X, 0)`. -/
def predSquareZero (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] :
    C ⥤ PredSquare C where
  obj X := ⟨X, 0⟩
  map f := ⟨f, zero_le_hom _⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

/-- **198II** (`dfn-eff-grothendieck`, eff.tex:3839, Definition): the
functor `1 : C → ∫ Pred_□`, `X ↦ (X, 1)`. -/
def predSquareOne (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] :
    C ⥤ PredSquare C where
  obj X := ⟨X, 1⟩
  map f := ⟨f, le_orth_comp_orth_one _ _⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

/-- **198II** (`dfn-eff-grothendieck`, eff.tex:3838, Definition): the
adjunction `0 ⊣ U`. -/
theorem predSquare_zero_adj :
    Nonempty (predSquareZero C ⊣ predSquareForget C) :=
  ⟨Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => f.1
          invFun := fun f => ⟨f, zero_le_hom _⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl } }⟩

/-- **198II** (`dfn-eff-grothendieck`, eff.tex:3838, Definition): the
adjunction `U ⊣ 1`. -/
theorem predSquare_one_adj :
    Nonempty (predSquareForget C ⊣ predSquareOne C) :=
  ⟨Adjunction.mkOfHomEquiv
    { homEquiv := fun P X =>
        { toFun := fun f => ⟨f, le_orth_comp_orth_one _ _⟩
          invFun := fun f => f.1
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl } }⟩

/-- **198III** (`exc-quot-adjoint`, eff.tex:3845, Exercise\*): an effectus
has quotients if and only if the functor `0 : C → ∫ Pred_□` has a left
adjoint `Q`. -/
theorem exc_quot_adjoint :
    HasQuotients C ↔
      ∃ Q : PredSquare C ⥤ C, Nonempty (Q ⊣ predSquareZero C) := by
  -- A map `f : X ⟶ Y` is a map `(X,p) ⟶ (Y,0)` in `∫ Pred_□` exactly when
  -- `1 ∘ f ≤ pᵖ`, i.e. exactly under the hypothesis of the universal
  -- property of a quotient of `p`.
  have key : ∀ (P : PredSquare C) (Y : C) (f : P.obj ⟶ Y),
      (P.pred ≼ orth (f ≫ orth ((predSquareZero C).obj Y).pred)) ↔
        (f ≫ truth Y) ≼ orth P.pred := by
    intro P Y f
    change (P.pred ≼ orth (f ≫ orth (0 : Pred Y))) ↔ _
    rw [eabasics_orth_zero]
    change (P.pred ≼ orth (f ≫ truth Y)) ↔ _
    rw [← eabasics_perp_iff_le_orth, ← eabasics_perp_iff_le_orth]
    exact ⟨PCM.perp_comm, PCM.perp_comm⟩
  constructor
  · -- Quotients give a left adjoint: `ξ_p` is the unit component at `(X,p)`.
    intro _
    have hiff : ∀ (P : PredSquare C) (Y : C) (f : P ⟶ (predSquareZero C).obj Y),
        (f.1 ≫ truth Y) ≼ orth P.pred := fun P Y f => (key P Y f.1).mp f.2
    have hto : ∀ (P : PredSquare C) (Y : C) (g : quotObj P.pred ⟶ Y),
        P.pred ≼ orth ((quotMap P.pred ≫ g) ≫
          orth ((predSquareZero C).obj Y).pred) := by
      intro P Y g
      refine (key P Y _).mpr ?_
      have h1 : (quotMap P.pred ≫ (g ≫ truth Y)) ≼
          (quotMap P.pred ≫ truth (quotObj P.pred)) :=
        comp_le_comp _ (pred_le_truth _)
      rw [← Category.assoc] at h1
      exact pcm_preorder_trans h1 (isQuotient_quotMap P.pred).1
    let e : ∀ (P : PredSquare C) (Y : C),
        (quotObj P.pred ⟶ Y) ≃ (P ⟶ (predSquareZero C).obj Y) := fun P Y =>
      { toFun := fun g => ⟨quotMap P.pred ≫ g, hto P Y g⟩
        invFun := fun f =>
          ((isQuotient_quotMap P.pred).2 f.1 (hiff P Y f)).choose
        left_inv := fun g =>
          (((isQuotient_quotMap P.pred).2 (quotMap P.pred ≫ g)
            (hiff P Y ⟨quotMap P.pred ≫ g, hto P Y g⟩)).choose_spec.2 g rfl).symm
        right_inv := fun f =>
          Subtype.ext
            ((isQuotient_quotMap P.pred).2 f.1 (hiff P Y f)).choose_spec.1 }
    have he : ∀ (P : PredSquare C) (Y Y' : C) (g : Y ⟶ Y')
        (h : quotObj P.pred ⟶ Y),
        e P Y' (h ≫ g) = e P Y h ≫ (predSquareZero C).map g := fun P Y Y' g h =>
      Subtype.ext (Category.assoc _ _ _).symm
    exact ⟨Adjunction.leftAdjointOfEquiv e he,
      ⟨Adjunction.adjunctionOfEquivLeft e he⟩⟩
  · -- Conversely, the unit component of `Q ⊣ 0` at `(X,p)` is a quotient.
    rintro ⟨Q, ⟨adj⟩⟩
    refine ⟨fun {X} p => ⟨Q.obj ⟨X, p⟩, (adj.unit.app ⟨X, p⟩).1, ?_, ?_⟩⟩
    · exact (key ⟨X, p⟩ _ _).mp (adj.unit.app ⟨X, p⟩).2
    · intro Y f hf
      refine ⟨(adj.homEquiv ⟨X, p⟩ Y).symm ⟨f, (key ⟨X, p⟩ Y f).mpr hf⟩, ?_, ?_⟩
      · have := (adj.homEquiv ⟨X, p⟩ Y).apply_symm_apply
          ⟨f, (key ⟨X, p⟩ Y f).mpr hf⟩
        exact congrArg Subtype.val
          ((Adjunction.homEquiv_unit adj _ _ _).symm.trans this)
      · intro g hg
        refine (adj.homEquiv ⟨X, p⟩ Y).injective ?_
        rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
        exact Subtype.ext hg

/-! ## Effectuses with comprehension (parsec 199) -/

/-- **199II** (`dfn-comprehension`, eff.tex:3895, Definition): a map
`π : {X|p} ⟶ X` is a **comprehension** for a predicate `p` on `X` when
`p ∘ π = 1 ∘ π` and, universally, every `g : Z ⟶ X` with `p ∘ g = 1 ∘ g`
factors as `g = π ∘ g'` for a unique `g'`.  (Comprehensions are *not*
assumed total; cf. 199III and 202VIII.) -/
def IsComprehension {W X : C} (p : Pred X) (π : W ⟶ X) : Prop :=
  π ≫ p = π ≫ truth X ∧
    ∀ ⦃Z : C⦄ (g : Z ⟶ X), g ≫ p = g ≫ truth X →
      ∃! g' : Z ⟶ W, g' ≫ π = g

/-- **199II** (`dfn-comprehension`, eff.tex:3897, Definition): an effectus
**has comprehension** when every predicate has a comprehension. -/
class HasComprehension (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop where
  compr : ∀ {X : C} (p : Pred X), ∃ (W : C) (π : W ⟶ X), IsComprehension p π

/-- **199IV** (`compr-not`, eff.tex:3928, Notation): the domain `{X|p}` of a
chosen comprehension for `p`. -/
noncomputable def comprObj [HasComprehension C] {X : C} (p : Pred X) : C :=
  (HasComprehension.compr p).choose

/-- **199IV** (`compr-not`, eff.tex:3928, Notation): a chosen comprehension
`π_p : {X|p} ⟶ X` for `p`. -/
noncomputable def comprMap [HasComprehension C] {X : C} (p : Pred X) :
    comprObj p ⟶ X :=
  (HasComprehension.compr p).choose_spec.choose

/-- The chosen `π_p` is a comprehension for `p` (199IV). -/
theorem isComprehension_comprMap [HasComprehension C] {X : C} (p : Pred X) :
    IsComprehension p (comprMap p) :=
  (HasComprehension.compr p).choose_spec.choose_spec

/-- **199VI** (`compr-grothendieck`, eff.tex:3960, Exercise\*): an effectus
has comprehension if and only if the functor `1 : C → ∫ Pred_□` has a right
adjoint `K`. -/
theorem compr_grothendieck :
    HasComprehension C ↔
      ∃ K : PredSquare C ⥤ C, Nonempty (predSquareOne C ⊣ K) := by
  -- A map `f : X ⟶ Y` is a map `(X,1) ⟶ (Y,q)` in `∫ Pred_□` exactly when
  -- `q ∘ f = 1 ∘ f`, i.e. exactly under the hypothesis of the universal
  -- property of a comprehension of `q`.
  have key : ∀ (P : PredSquare C) (X : C) (f : X ⟶ P.obj),
      (((predSquareOne C).obj X).pred ≼ orth (f ≫ orth P.pred)) ↔
        f ≫ P.pred = f ≫ truth P.obj := by
    intro P X f
    rw [← comp_orth_eq_zero_iff]
    change ((1 : Pred X) ≼ orth (f ≫ orth P.pred)) ↔ _
    constructor
    · intro h
      have h1 : orth (f ≫ orth P.pred) = (1 : Pred X) :=
        eabasics_le_antisymm (pred_le_truth _) h
      have h2 := congrArg orth h1
      rwa [eabasics_orth_orth, eabasics_orth_one] at h2
    · intro h
      rw [h, eabasics_orth_zero]
      exact pcm_preorder_refl _
  constructor
  · -- Comprehensions give a right adjoint: `π_p` is the counit component.
    intro _
    have hiff : ∀ (P : PredSquare C) (X : C)
        (f : (predSquareOne C).obj X ⟶ P),
        f.1 ≫ P.pred = f.1 ≫ truth P.obj := fun P X f => (key P X f.1).mp f.2
    have hfrom : ∀ (P : PredSquare C) (X : C) (g : X ⟶ comprObj P.pred),
        ((predSquareOne C).obj X).pred ≼
          orth ((g ≫ comprMap P.pred) ≫ orth P.pred) := by
      intro P X g
      refine (key P X _).mpr ?_
      have h : g ≫ (comprMap P.pred ≫ P.pred)
          = g ≫ (comprMap P.pred ≫ truth P.obj) :=
        congrArg (fun x => g ≫ x) (isComprehension_comprMap P.pred).1
      exact ((Category.assoc g (comprMap P.pred) P.pred).trans h).trans
        (Category.assoc g (comprMap P.pred) (truth P.obj)).symm
    let e : ∀ (X : C) (P : PredSquare C),
        ((predSquareOne C).obj X ⟶ P) ≃ (X ⟶ comprObj P.pred) := fun X P =>
      { toFun := fun f =>
          ((isComprehension_comprMap P.pred).2 f.1 (hiff P X f)).choose
        invFun := fun g => ⟨g ≫ comprMap P.pred, hfrom P X g⟩
        left_inv := fun f =>
          Subtype.ext
            ((isComprehension_comprMap P.pred).2 f.1 (hiff P X f)).choose_spec.1
        right_inv := fun g =>
          (((isComprehension_comprMap P.pred).2 (g ≫ comprMap P.pred)
            (hiff P X ⟨g ≫ comprMap P.pred, hfrom P X g⟩)).choose_spec.2
              g rfl).symm }
    have he : ∀ (X' X : C) (P : PredSquare C) (f : X' ⟶ X)
        (g : (predSquareOne C).obj X ⟶ P),
        e X' P ((predSquareOne C).map f ≫ g) = f ≫ e X P g := by
      intro X' X P f g
      have h1 : (e X P g) ≫ comprMap P.pred = g.1 :=
        ((isComprehension_comprMap P.pred).2 g.1 (hiff P X g)).choose_spec.1
      refine (((isComprehension_comprMap P.pred).2
        ((predSquareOne C).map f ≫ g).1
        (hiff P X' ((predSquareOne C).map f ≫ g))).choose_spec.2
        (f ≫ e X P g) ?_).symm
      calc (f ≫ e X P g) ≫ comprMap P.pred
          = f ≫ ((e X P g) ≫ comprMap P.pred) := Category.assoc _ _ _
        _ = f ≫ g.1 := congrArg (fun x => f ≫ x) h1
    exact ⟨Adjunction.rightAdjointOfEquiv e he,
      ⟨Adjunction.adjunctionOfEquivRight e he⟩⟩
  · -- Conversely, the counit component of `1 ⊣ K` at `(X,p)` is a
    -- comprehension.
    rintro ⟨K, ⟨adj⟩⟩
    refine ⟨fun {X} p => ⟨K.obj ⟨X, p⟩, (adj.counit.app ⟨X, p⟩).1, ?_, ?_⟩⟩
    · exact (key ⟨X, p⟩ _ _).mp (adj.counit.app ⟨X, p⟩).2
    · intro Z g hg
      refine ⟨adj.homEquiv Z ⟨X, p⟩ ⟨g, (key ⟨X, p⟩ Z g).mpr hg⟩, ?_, ?_⟩
      · have h := (adj.homEquiv Z ⟨X, p⟩).symm_apply_apply
          ⟨g, (key ⟨X, p⟩ Z g).mpr hg⟩
        exact congrArg Subtype.val
          ((Adjunction.homEquiv_counit adj _ _ _).symm.trans h)
      · intro h hh
        refine (adj.homEquiv Z ⟨X, p⟩).symm.injective ?_
        rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
        exact Subtype.ext hh

section ComprBasics

variable {W W' X Z : C}

/-- **199VII.1** (`compr-basics`, eff.tex:3966, Exercise): precomposing a
comprehension for `p` with an isomorphism yields a comprehension for
`p`. -/
theorem compr_basics_1 {p : Pred X} {π : W ⟶ X} (h : IsComprehension p π)
    (θ : W' ⟶ W) [IsIso θ] : IsComprehension p (θ ≫ π) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, Category.assoc, h.1]
  · intro Z g hg
    obtain ⟨g', hg', huniq⟩ := h.2 g hg
    refine ⟨g' ≫ inv θ, ?_, ?_⟩
    · show (g' ≫ inv θ) ≫ (θ ≫ π) = g
      rw [Category.assoc, ← Category.assoc (inv θ), IsIso.inv_hom_id, Category.id_comp]
      exact hg'
    · intro k hk
      replace hk : k ≫ (θ ≫ π) = g := hk
      have hk' : (k ≫ θ) ≫ π = g := by rw [Category.assoc]; exact hk
      rw [← huniq _ hk', Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Helper (the mirror image of `compr_basics_1`, used in 221IV.2):
postcomposing a comprehension for `p` with an isomorphism `θ` yields a
comprehension for `p ∘ θ⁻¹`. -/
theorem isComprehension_comp_iso {p : Pred X} {π : W ⟶ X}
    (h : IsComprehension p π) (θ : X ⟶ Z) [IsIso θ] :
    IsComprehension (inv θ ≫ p) (π ≫ θ) := by
  have hθ : IsTotal θ := iso_isTotal θ
  have hθ' : IsTotal (inv θ) := iso_isTotal (inv θ)
  refine ⟨?_, ?_⟩
  · calc (π ≫ θ) ≫ (inv θ ≫ p)
        = (π ≫ (θ ≫ inv θ)) ≫ p := by simp only [Category.assoc]
      _ = π ≫ truth X := by
          rw [IsIso.hom_inv_id, Category.comp_id]; exact h.1
      _ = (π ≫ θ) ≫ truth Z := by
          rw [Category.assoc, show θ ≫ truth Z = truth X from hθ]
  · intro V g hg
    have hg' : (g ≫ inv θ) ≫ p = (g ≫ inv θ) ≫ truth X := by
      rw [Category.assoc, Category.assoc,
        show inv θ ≫ truth X = truth Z from hθ']
      exact hg
    obtain ⟨g', hg'eq, huniq⟩ := h.2 (g ≫ inv θ) hg'
    refine ⟨g', ?_, ?_⟩
    · show g' ≫ (π ≫ θ) = g
      rw [← Category.assoc, hg'eq, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id]
    · intro k hk
      replace hk : k ≫ (π ≫ θ) = g := hk
      refine huniq k ?_
      show k ≫ π = g ≫ inv θ
      rw [← hk, Category.assoc, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]

/-- **199VII.2** (`compr-basics`, eff.tex:3974, Exercise): any two
comprehensions for `p` differ by a unique isomorphism. -/
theorem compr_basics_2 {p : Pred X} {π₁ : W ⟶ X} {π₂ : W' ⟶ X}
    (h₁ : IsComprehension p π₁) (h₂ : IsComprehension p π₂) :
    ∃ θ : W ⟶ W', IsIso θ ∧ θ ≫ π₂ = π₁ ∧
      ∀ θ' : W ⟶ W', θ' ≫ π₂ = π₁ → θ' = θ := by
  obtain ⟨θ, hθ, huθ⟩ := h₂.2 π₁ h₁.1
  obtain ⟨θ', hθ', huθ'⟩ := h₁.2 π₂ h₂.1
  refine ⟨θ, ⟨⟨θ', ?_, ?_⟩⟩, hθ, huθ⟩
  · obtain ⟨u, -, huu⟩ := h₁.2 π₁ h₁.1
    rw [huu (θ ≫ θ') (show (θ ≫ θ') ≫ π₁ = π₁ by rw [Category.assoc, hθ', hθ]),
      huu (𝟙 W) (Category.id_comp _)]
  · obtain ⟨u, -, huu⟩ := h₂.2 π₂ h₂.1
    rw [huu (θ' ≫ θ) (show (θ' ≫ θ) ≫ π₂ = π₂ by rw [Category.assoc, hθ, hθ']),
      huu (𝟙 W') (Category.id_comp _)]

/-- **199VII.3** (`compr-basics`, eff.tex:3978, Exercise): isomorphisms are
comprehensions for `1`. -/
theorem compr_basics_3 (f : W ⟶ X) [IsIso f] :
    IsComprehension (1 : Pred X) f := by
  -- bsols.tex:2801: `id` is a comprehension for `1` — every `f` is the unique
  -- map with `f ∘ id = f` — and then so is every isomorphism, by the first
  -- point.
  have hid : IsComprehension (1 : Pred X) (𝟙 X) := by
    refine ⟨rfl, ?_⟩
    intro Z g _
    exact ⟨g, Category.comp_id g, fun k hk => (Category.comp_id k).symm.trans hk⟩
  have h := compr_basics_1 hid f
  rwa [Category.comp_id] at h

/-- **199VII.4** (`compr-basics`, eff.tex:3979, Exercise): the zero map out
of the zero object is a comprehension for `0`.

*The running text is still wrong here.*  As printed the part reads "Zero
maps are comprehensions (for `0`)", and that is **false** for any non-initial
domain: the universal property applied to `g = 0 : Z ⟶ W` forces the
factorisation through `π : W ⟶ X` to be unique, so `W ⟶ W` is a singleton
for every `W`, and (with `id` and `0` both in it) `W ≅ 0`.  `berr.tex`'s
erratum `compr-basics` says exactly this — "Not every zero map is a
comprehension; only those from `0`" — but, unlike its twin for 197V.4
(`quotient-basics`, whose correction *has* been absorbed: the running text
now reads "Maps into `0` are quotients (for 1)"), it has **not** been carried
into eff.tex.  The corrected form is what is stated here. -/
theorem compr_basics_4 (X : C) :
    IsComprehension (0 : Pred X) (0 : (⊥_ C) ⟶ X) := by
  refine ⟨?_, ?_⟩
  · rw [FinPAC.comp_zero, FinPAC.zero_comp]
  · intro Z g hg
    rw [FinPAC.comp_zero] at hg
    have hg0 : g = 0 := EffectusPartialForm.eq_zero_of_one_zero hg.symm
    refine ⟨0, ?_, ?_⟩
    · show (0 : Z ⟶ (⊥_ C)) ≫ (0 : (⊥_ C) ⟶ X) = g
      rw [FinPAC.comp_zero, hg0]
    · intro k _
      exact eq_zero_of_hom_to_initial k

/-- **199VII.5** (`compr-basics`, eff.tex:3980, Exercise): comprehensions
are monic. -/
theorem compr_basics_5 {p : Pred X} {π : W ⟶ X} (h : IsComprehension p π) :
    Mono π := by
  constructor
  intro Z a b hab
  have hg : (a ≫ π) ≫ p = (a ≫ π) ≫ truth X := by
    rw [Category.assoc, Category.assoc, h.1]
  obtain ⟨u, -, huu⟩ := h.2 (a ≫ π) hg
  rw [huu a rfl, huu b hab.symm]

/-- **199VII.6** (`compr-basics`, eff.tex:3981, Exercise): `pᵖ ∘ π = 0` for
a comprehension `π` for `p`. -/
theorem compr_basics_6 {p : Pred X} {π : W ⟶ X} (h : IsComprehension p π) :
    π ≫ orth p = 0 := (comp_orth_eq_zero_iff π p).mpr h.1

end ComprBasics

/-! ## Kernels and cokernels (parsec 200) -/

/-- **200II** (eff.tex:3990, Definition): a **kernel** of `f : X ⟶ Y` is an
equalizer of `f` with the zero map: `k` with `f ∘ k = 0` such that every
`g` with `f ∘ g = 0` factors uniquely through `k`.  (Zero maps are those of
the PCM-enrichment; an effectus in partial form has a zero object.) -/
def IsKernel {W X Y : C} (f : X ⟶ Y) (k : W ⟶ X) : Prop :=
  k ≫ f = 0 ∧
    ∀ ⦃Z : C⦄ (g : Z ⟶ X), g ≫ f = 0 → ∃! g' : Z ⟶ W, g' ≫ k = g

/-- **200II** (eff.tex:4000, Definition): a **cokernel** of `f : X ⟶ Y` is
a kernel of `f` in `Cᵒᵖ`. -/
def IsCokernel {X Y W : C} (f : X ⟶ Y) (c : Y ⟶ W) : Prop :=
  f ≫ c = 0 ∧
    ∀ ⦃Z : C⦄ (g : Y ⟶ Z), f ≫ g = 0 → ∃! g' : W ⟶ Z, c ≫ g' = g

/-- **200III** (`effectus-kernels`, eff.tex:4005, Proposition), *second*
sentence: a comprehension `π` for `(1 ∘ f)ᵖ` is a kernel of `f`.  The
Proposition's headline — an effectus with comprehension has **all** kernels —
is `effectus_has_all_kernels` below, which is this statement applied to the
chosen comprehension. -/
theorem effectus_kernels {W X Y : C} (f : X ⟶ Y) {π : W ⟶ X}
    (hπ : IsComprehension (orth (f ≫ truth Y)) π) : IsKernel f π := by
  have h1 : π ≫ f = 0 := by
    have h2 := (comp_orth_eq_zero_iff π (orth (f ≫ truth Y))).mpr hπ.1
    rw [eabasics_orth_orth, ← Category.assoc] at h2
    exact EffectusPartialForm.eq_zero_of_one_zero h2
  refine ⟨h1, ?_⟩
  intro Z g hg
  refine hπ.2 g ?_
  rw [← comp_orth_eq_zero_iff, eabasics_orth_orth, ← Category.assoc, hg,
    FinPAC.zero_comp]

/-- **200III** (`effectus-kernels`, eff.tex:4005, Proposition), headline
sentence: a category *has all kernels* when every map has a kernel.  (Named
`HasAllKernels` rather than `HasKernels` to avoid a clash with Mathlib's
`CategoryTheory.Limits.HasKernels`, which is stated for its own notion of
kernel in a category with zero morphisms.) -/
class HasAllKernels (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop where
  ker : ∀ {X Y : C} (f : X ⟶ Y), ∃ (W : C) (k : W ⟶ X), IsKernel f k

/-- **200III** (`effectus-kernels`, eff.tex:4005, Proposition), the
Proposition's *first* sentence: **an effectus with comprehension has all
kernels**.  (Until the audit repair only the second sentence,
`effectus_kernels`, was stated, and it did not even take
`[HasComprehension C]`.)

The thesis's proof is exactly this: *the* kernel of `f` "is given by a
comprehension `π_{(1 ∘ f)ᵖ}`", so the existence half is the chosen
comprehension `π_{(1 ∘ f)ᵖ}` fed to `effectus_kernels`. -/
instance effectus_has_all_kernels [HasComprehension C] : HasAllKernels C where
  ker {_ Y} f :=
    ⟨comprObj (orth (f ≫ truth Y)), comprMap (orth (f ≫ truth Y)),
      effectus_kernels f (isComprehension_comprMap _)⟩

/-- **200III**, in the explicit form the Proposition states it: in an
effectus with comprehension, a chosen comprehension `π_{(1 ∘ f)ᵖ}` *is* a
kernel of `f`. -/
theorem isKernel_comprMap [HasComprehension C] {X Y : C} (f : X ⟶ Y) :
    IsKernel f (comprMap (orth (f ≫ truth Y))) :=
  effectus_kernels f (isComprehension_comprMap _)

/-- **200V** (`compr-is-kernel`, eff.tex:4020, Exercise): in an effectus, a
map is a comprehension for `p` if and only if it is a kernel of `pᵖ`. -/
theorem compr_is_kernel {W X : C} (p : Pred X) (f : W ⟶ X) :
    IsComprehension p f ↔ IsKernel (orth p) f := by
  constructor
  · intro h
    exact ⟨(comp_orth_eq_zero_iff f p).mpr h.1,
      fun Z g hg => h.2 g ((comp_orth_eq_zero_iff g p).mp hg)⟩
  · intro h
    exact ⟨(comp_orth_eq_zero_iff f p).mp h.1,
      fun Z g hg => h.2 g ((comp_orth_eq_zero_iff g p).mpr hg)⟩

/-! ## Pure maps (parsec 201) -/

/-- **201II** (eff.tex:4031, Definition): a map in an effectus is **pure**
if it is a comprehension after a quotient. -/
def IsPure {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ (Q : C) (ξ : X ⟶ Q) (π : Q ⟶ Y) (p : Pred X) (q : Pred Y),
    IsQuotient p ξ ∧ IsComprehension q π ∧ f = ξ ≫ π

/-! ## Images and faithful maps (parsec 202) -/

/-- **202I.1** (eff.tex:4080, Definition): a predicate `im` on `Y` is *the*
**image** of `f : X ⟶ Y` when it is the least predicate with
`im ∘ f = 1 ∘ f`. -/
def IsImage {X Y : C} (f : X ⟶ Y) (im : Pred Y) : Prop :=
  f ≫ im = f ≫ truth Y ∧
    ∀ p : Pred Y, f ≫ p = f ≫ truth Y → im ≼ p

/-- **202I.1** (eff.tex:4084, Definition): an effectus **has images** when
every map has an image. -/
class HasImages (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop where
  im : ∀ {X Y : C} (f : X ⟶ Y), ∃ p : Pred Y, IsImage f p

/-- **202II** (eff.tex:4105, Notation): the image `im f` of a map `f` in an
effectus with images (`im f ∘ g` is read as `im (f ∘ g)`; the thesis's
`im^⊥ f` is `orth (imPred f)`). -/
noncomputable def imPred [HasImages C] {X Y : C} (f : X ⟶ Y) : Pred Y :=
  (HasImages.im f).choose

/-- The defining property of `imPred` (202I). -/
theorem isImage_imPred [HasImages C] {X Y : C} (f : X ⟶ Y) :
    IsImage f (imPred f) :=
  (HasImages.im f).choose_spec

/-- **202I.2** (eff.tex:4097, Definition): a map `f : X ⟶ Y` is
**faithful** if `im f = 1`; equivalently, `p ∘ f = 0` implies `p = 0` for
every predicate `p` on `Y`. -/
def FaithfulMap {X Y : C} (f : X ⟶ Y) : Prop :=
  IsImage f (1 : Pred Y)

/-- **202I.2** (eff.tex:4100, Definition): the equivalent characterization
of faithfulness: `p ∘ f = 0` implies `p = 0`. -/
theorem faithfulMap_iff {X Y : C} (f : X ⟶ Y) :
    FaithfulMap f ↔ ∀ p : Pred Y, f ≫ p = 0 → p = 0 := by
  constructor
  · rintro ⟨-, hmin⟩ p hp
    have h1 : f ≫ orth p = f ≫ truth Y := by
      refine (comp_orth_eq_zero_iff f (orth p)).mp ?_
      rw [eabasics_orth_orth]; exact hp
    have h2 : orth p = 1 :=
      eabasics_le_antisymm (pred_le_truth _) (hmin (orth p) h1)
    rw [← eabasics_orth_orth p, h2, eabasics_orth_one]
  · intro hf
    refine ⟨rfl, ?_⟩
    intro p hp
    have h1 : f ≫ orth p = 0 := (comp_orth_eq_zero_iff f p).mpr hp
    have hp1 : p = 1 := by
      rw [← eabasics_orth_orth p, hf (orth p) h1, eabasics_orth_zero]
    rw [hp1]
    exact pcm_preorder_refl _

/-- **202V** (`im-ineq`, eff.tex:4130, Exercise): `im (f ∘ g) ≤ im f`, with
equality when `g` is an isomorphism. -/
theorem im_ineq [HasImages C] {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ X) :
    imPred (g ≫ f) ≼ imPred f ∧
      (∀ (α : Z ⟶ X), IsIso α → imPred (α ≫ f) = imPred f) := by
  have key : ∀ {W V : C} (u : W ⟶ V) (h : V ⟶ Y), imPred (u ≫ h) ≼ imPred h := by
    intro W V u h
    refine (isImage_imPred (u ≫ h)).2 (imPred h) ?_
    rw [Category.assoc, (isImage_imPred h).1, ← Category.assoc]
  refine ⟨key g f, ?_⟩
  intro α hα
  have := hα
  have h3 := key (inv α) (α ≫ f)
  rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at h3
  exact eabasics_le_antisymm (key α f) h3

/-- **202VI** (`exc-quot-faithful`, eff.tex:4135, Exercise): quotients are
faithful. -/
theorem exc_quot_faithful {X Q : C} {p : Pred X} {ξ : X ⟶ Q}
    (h : IsQuotient p ξ) : FaithfulMap ξ := by
  have : Epi ξ := quotient_basics_6 h
  refine (faithfulMap_iff ξ).mpr ?_
  intro q hq
  have h2 : ξ ≫ q = ξ ≫ 0 := by rw [hq, FinPAC.comp_zero]
  exact (cancel_epi ξ).mp h2

/-- **202VIII** (`compr-total`, eff.tex:4145, Lemma): in an effectus with
quotients, comprehensions are total. -/
theorem compr_total [HasQuotients C] {W X : C} {p : Pred X} {π : W ⟶ X}
    (h : IsComprehension p π) : IsTotal π := by
  obtain ⟨QQ, ξ, hξ⟩ := HasQuotients.quot (orth (π ≫ truth X))
  obtain ⟨πt, hπt, -⟩ := quotient_total hξ π rfl
  have hepi : Epi ξ := quotient_basics_6 hξ
  have hmono : Mono π := compr_basics_5 h
  have h1 : πt ≫ p = πt ≫ truth X := by
    refine (cancel_epi ξ).mp ?_
    rw [← Category.assoc, ← Category.assoc, hπt.2, h.1]
  obtain ⟨f, hf, -⟩ := h.2 πt h1
  have h2 : ξ ≫ f = 𝟙 W := by
    refine (cancel_mono π).mp ?_
    rw [Category.assoc, hf, hπt.2, Category.id_comp]
  have h3 : truth W ≼ (π ≫ truth X) := by
    have h4 : (ξ ≫ (f ≫ truth W)) ≼ (ξ ≫ truth QQ) :=
      comp_le_comp ξ (pred_le_truth _)
    rw [← Category.assoc, h2, Category.id_comp, quotient_basics_5 hξ,
      eabasics_orth_orth] at h4
    exact h4
  exact eabasics_le_antisymm (pred_le_truth _) h3


/-- Helper (quotients cancel on the left; needed for 221IV.6, eff.tex:6906):
if `ξ` and `ξ ≫ η` are quotients, then so is `η` — namely a quotient for
`(1 ∘ η)ᵖ`. -/
theorem isQuotient_of_comp_left {X Q R : C} {p₀ p : Pred X}
    {ξ : X ⟶ Q} {η : Q ⟶ R} (hξ : IsQuotient p₀ ξ)
    (hcomp : IsQuotient p (ξ ≫ η)) :
    IsQuotient (orth (η ≫ truth R)) η := by
  haveI : Epi ξ := quotient_basics_6 hξ
  refine ⟨?_, ?_⟩
  · rw [eabasics_orth_orth]
    exact pcm_preorder_refl _
  · intro Y f hf
    rw [eabasics_orth_orth] at hf
    -- `1 ∘ (ξ ≫ f) ≤ 1 ∘ (ξ ≫ η) ≤ pᵖ`
    have hle : ((ξ ≫ f) ≫ truth Y) ≼ orth p := by
      refine pcm_preorder_trans ?_ hcomp.1
      rw [Category.assoc, Category.assoc]
      exact comp_le_comp ξ hf
    obtain ⟨f', hf', hu⟩ := hcomp.2 (ξ ≫ f) hle
    refine ⟨f', ?_, ?_⟩
    · refine (cancel_epi ξ).mp ?_
      rw [← Category.assoc]
      exact hf'
    · intro g hg
      exact hu g (show (ξ ≫ η) ≫ g = ξ ≫ f by rw [Category.assoc, hg])

/-- Helper (comprehensions cancel on the right; the dual of
`isQuotient_of_comp_left`): if `π` and `κ ≫ π` are comprehensions — say `π`
for `r` and `κ ≫ π` for `q` — then `κ` is a comprehension for `π ≫ q`. -/
theorem isComprehension_of_comp_right [HasQuotients C] {W Z X : C}
    {r q : Pred X} {κ : W ⟶ Z} {π : Z ⟶ X} (hπ : IsComprehension r π)
    (hcomp : IsComprehension q (κ ≫ π)) : IsComprehension (π ≫ q) κ := by
  have hπt : IsTotal π := compr_total hπ
  haveI : Mono π := compr_basics_5 hπ
  haveI : Mono (κ ≫ π) := compr_basics_5 hcomp
  haveI : Mono κ := mono_of_mono κ π
  refine ⟨?_, ?_⟩
  · rw [← Category.assoc, hcomp.1, Category.assoc, hπt]
  · intro V g hg
    have hg' : (g ≫ π) ≫ q = (g ≫ π) ≫ truth X := by
      rw [Category.assoc, Category.assoc, hπt]
      exact hg
    obtain ⟨h, hh, hu⟩ := hcomp.2 (g ≫ π) hg'
    refine ⟨h, ?_, ?_⟩
    · refine (cancel_mono π).mp ?_
      rw [Category.assoc]
      exact hh
    · intro k hk
      exact hu k (show k ≫ κ ≫ π = g ≫ π by rw [← Category.assoc, hk])

/-- Helper (**pure maps divide on the left by quotients**): if `ξ` is a
quotient and `ξ ≫ g` is pure, then `g` is pure.  The thesis uses this
tacitly in the proof of 221IV.6 (eff.tex:6906), where it asserts that the
factor `h''` of the pure map `h = h'' ∘ ξ` is again pure. -/
theorem isPure_of_isQuotient_comp [HasQuotients C] {X Q Y : C} {p₀ : Pred X}
    {ξ : X ⟶ Q} (hξ : IsQuotient p₀ ξ) {g : Q ⟶ Y}
    (hpure : IsPure (ξ ≫ g)) : IsPure g := by
  haveI : Epi ξ := quotient_basics_6 hξ
  obtain ⟨Q', ξ', π, p, q, hξ', hπ, he⟩ := hpure
  have hπt : IsTotal π := compr_total hπ
  -- `1 ∘ ξ' = 1 ∘ ξ ∘ g ≤ 1 ∘ ξ ≤ p₀ᵖ`, so `ξ'` factors through `ξ`
  have hle : (ξ' ≫ truth Q') ≼ orth p₀ := by
    have e : ξ' ≫ truth Q' = ξ ≫ (g ≫ truth Y) := by
      rw [← Category.assoc, he, Category.assoc, hπt]
    rw [e]
    exact pcm_preorder_trans (comp_le_comp ξ (pred_le_truth _)) hξ.1
  obtain ⟨η, hη, -⟩ := hξ.2 ξ' hle
  have hgη : η ≫ π = g := by
    refine (cancel_epi ξ).mp ?_
    rw [← Category.assoc, hη, ← he]
  exact ⟨Q', η, π, orth (η ≫ truth Q'), q,
    isQuotient_of_comp_left hξ (by rw [hη]; exact hξ'), hπ, hgη.symm⟩

/-- Helper (**pure maps divide on the right by comprehensions**): if `π` is
a comprehension and `f ≫ π` is pure, then `f` is pure.  (The dual of
`isPure_of_isQuotient_comp`; the same gap arises in the proof of 224III.) -/
theorem isPure_of_comp_isComprehension [HasQuotients C] {X Z Y : C}
    {r : Pred Y} {f : X ⟶ Z} {π : Z ⟶ Y} (hπ : IsComprehension r π)
    (hpure : IsPure (f ≫ π)) : IsPure f := by
  have hπt : IsTotal π := compr_total hπ
  haveI : Mono π := compr_basics_5 hπ
  obtain ⟨Q, ξ, π', p, q, hξ, hπ', he⟩ := hpure
  haveI : Epi ξ := quotient_basics_6 hξ
  -- `π'` satisfies the defining equation of the comprehension `π`
  have hπ'r : π' ≫ r = π' ≫ truth Y := by
    refine (cancel_epi ξ).mp ?_
    rw [← Category.assoc, ← Category.assoc, ← he, Category.assoc, hπ.1,
      ← Category.assoc]
  obtain ⟨κ, hκ, -⟩ := hπ.2 π' hπ'r
  have hfκ : ξ ≫ κ = f := by
    refine (cancel_mono π).mp ?_
    rw [Category.assoc, hκ, ← he]
  exact ⟨Q, ξ, κ, p, π ≫ q, hξ,
    isComprehension_of_comp_right hπ (by rw [hκ]; exact hπ'), hfκ.symm⟩

/-! ## Sharp predicates, floor and ceiling (parsecs 203–204) -/

/-- **203I.1** (eff.tex:4168, Definition): a predicate is (image) **sharp**
if it is the image of some map.  (`SPred X` is the set of sharp predicates
on `X`.) -/
def IsSharp {X : C} (p : Pred X) : Prop :=
  ∃ (Y : C) (f : Y ⟶ X), IsImage f p

/-- **203I.1** (eff.tex:4174, Definition): the set `SPred X` of sharp
predicates on `X`. -/
def SPred (X : C) : Type v := { p : Pred X // IsSharp p }

/-- **203I.2** (eff.tex:4177, Definition): the **floor**
`⌊p⌋ = im π_p` of a predicate (comprehensions for the same predicate have
the same image by 202V). -/
noncomputable def floorPred [HasComprehension C] [HasImages C] {X : C}
    (p : Pred X) : Pred X :=
  imPred (comprMap p)

/-- **203I.2** (eff.tex:4181, Definition): the **ceiling**
`⌈p⌉ = ⌊pᵖ⌋ᵖ` of a predicate. -/
noncomputable def ceilPred [HasComprehension C] [HasImages C] {X : C}
    (p : Pred X) : Pred X :=
  orth (floorPred (orth p))

section FloorBasics

variable [HasComprehension C] [HasImages C] {X Y : C}

/-- **203IV.1** (`floor-basics`, eff.tex:4200, Lemma): `⌊p⌋ ≤ p`. -/
theorem floor_basics_1 (p : Pred X) : floorPred p ≼ p :=
  (isImage_imPred (comprMap p)).2 p (isComprehension_comprMap p).1

/-- **203IV.2** (`floor-basics`, eff.tex:4200, Lemma):
`π_p = π_{⌊p⌋} ∘ α` for some isomorphism `α` (indeed `π_p` is also a
comprehension for `⌊p⌋`). -/
theorem floor_basics_2 (p : Pred X) :
    ∃ α : comprObj p ⟶ comprObj (floorPred p),
      IsIso α ∧ α ≫ comprMap (floorPred p) = comprMap p := by
  have hc : IsComprehension (floorPred p) (comprMap p) := by
    refine ⟨(isImage_imPred (comprMap p)).1, ?_⟩
    intro Z g hg
    refine (isComprehension_comprMap p).2 g ?_
    refine eabasics_le_antisymm (comp_le_comp g (pred_le_truth p)) ?_
    rw [← hg]
    exact comp_le_comp g (floor_basics_1 p)
  obtain ⟨θ, hiso, hθ, -⟩ :=
    compr_basics_2 hc (isComprehension_comprMap (floorPred p))
  exact ⟨θ, hiso, hθ⟩

/-- **203IV.3** (`floor-basics`, eff.tex:4200, Lemma): `⌊⌊p⌋⌋ = ⌊p⌋`. -/
theorem floor_basics_3 (p : Pred X) :
    floorPred (floorPred p) = floorPred p := by
  obtain ⟨α, hiso, hα⟩ := floor_basics_2 p
  have h := (im_ineq (comprMap (floorPred p)) α).2 α hiso
  rw [hα] at h
  exact h.symm

/-- **203IV.4** (`floor-basics`, eff.tex:4200, Lemma): `p ≤ q` implies
`⌊p⌋ ≤ ⌊q⌋`. -/
theorem floor_basics_4 {p q : Pred X} (h : p ≼ q) :
    floorPred p ≼ floorPred q := by
  have hcm : comprMap p ≫ q = comprMap p ≫ truth X := by
    refine eabasics_le_antisymm (comp_le_comp _ (pred_le_truth q)) ?_
    rw [← (isComprehension_comprMap p).1]
    exact comp_le_comp _ h
  obtain ⟨g, hg, -⟩ := (isComprehension_comprMap q).2 (comprMap p) hcm
  have h2 := (im_ineq (comprMap q) g).1
  rw [hg] at h2
  exact h2

/-- Helper (203IV, "Ad 6"): `⌊1⌋ = 1`, because the identity is a
comprehension for `1` (199VII.3) and `im id = 1`. -/
theorem floorPred_one : floorPred (1 : Pred X) = 1 := by
  obtain ⟨θ, hθ, hcomm, -⟩ :=
    compr_basics_2 (isComprehension_comprMap (1 : Pred X)) (compr_basics_3 (𝟙 X))
  have h1 : imPred (θ ≫ 𝟙 X) = imPred (𝟙 X) := (im_ineq (𝟙 X) θ).2 θ hθ
  have h2 : imPred (𝟙 X) = (1 : Pred X) := by
    have h := (isImage_imPred (𝟙 X)).1
    rw [Category.id_comp, Category.id_comp] at h
    exact h
  show imPred (comprMap (1 : Pred X)) = 1
  rw [← hcomm, h1, h2]

/-- Helper (203IV, "Ad 6"): `⌈0⌉ = 0`. -/
theorem ceilPred_zero : ceilPred (0 : Pred X) = 0 := by
  show orth (floorPred (orth (0 : Pred X))) = 0
  rw [eabasics_orth_zero, floorPred_one, eabasics_orth_one]

/-- Helper (203IV): `p ≤ ⌈p⌉`, dual to `⌊pᵖ⌋ ≤ pᵖ`. -/
theorem le_ceilPred (p : Pred X) : p ≼ ceilPred p := by
  have h := eabasics_le_iff_orth_le.mp (floor_basics_1 (orth p))
  rw [eabasics_orth_orth] at h
  exact h

/-- Helper (203IV): the ceiling is monotone, dual to `floor_basics_4`. -/
theorem ceilPred_mono {p q : Pred X} (h : p ≼ q) : ceilPred p ≼ ceilPred q := by
  have h2 := eabasics_le_iff_orth_le.mp
    (floor_basics_4 (eabasics_le_iff_orth_le.mp h))
  exact h2

/-- **203IV.5** (`floor-basics`, eff.tex:4200, Lemma):
`⌈p⌉ ∘ f ≤ ⌈p ∘ f⌉`. -/
theorem floor_basics_5 (p : Pred X) (f : Y ⟶ X) :
    (f ≫ ceilPred p) ≼ ceilPred (f ≫ p) := by
  -- `(p ∘ f) ∘ π = 0` for the comprehension `π = π_{(p ∘ f)ᵖ}`
  have h0 : comprMap (orth (f ≫ p)) ≫ (f ≫ p) = 0 := by
    have h := compr_basics_6 (isComprehension_comprMap (orth (f ≫ p)))
    rwa [eabasics_orth_orth] at h
  -- hence `f ∘ π` factors through `π_{pᵖ}`
  have hfac : (comprMap (orth (f ≫ p)) ≫ f) ≫ orth p
      = (comprMap (orth (f ≫ p)) ≫ f) ≫ truth X := by
    refine (comp_orth_eq_zero_iff _ (orth p)).mp ?_
    rw [eabasics_orth_orth, Category.assoc]
    exact h0
  obtain ⟨k, hk, -⟩ := (isComprehension_comprMap (orth p)).2 _ hfac
  -- `⌈p⌉ ∘ π_{pᵖ} = 0`, as `π_{pᵖ} = π_{⌊pᵖ⌋} ∘ α` and `⌈p⌉ = ⌊pᵖ⌋ᵖ`
  have hcompr0 : comprMap (orth p) ≫ ceilPred p = 0 := by
    obtain ⟨α, -, hα⟩ := floor_basics_2 (orth p)
    have h1 : comprMap (floorPred (orth p)) ≫ ceilPred p = 0 :=
      compr_basics_6 (isComprehension_comprMap (floorPred (orth p)))
    rw [← hα, Category.assoc, h1, FinPAC.comp_zero]
  have hz : comprMap (orth (f ≫ p)) ≫ (f ≫ ceilPred p) = 0 := by
    rw [← Category.assoc, ← hk, Category.assoc, hcompr0, FinPAC.comp_zero]
  -- so `⌈p⌉ ∘ f ≤ im^⊥ π = ⌈p ∘ f⌉`
  have him : imPred (comprMap (orth (f ≫ p))) ≼ orth (f ≫ ceilPred p) := by
    refine (isImage_imPred _).2 _ ?_
    refine (comp_orth_eq_zero_iff _ (orth (f ≫ ceilPred p))).mp ?_
    rw [eabasics_orth_orth]
    exact hz
  have h2 := eabasics_le_iff_orth_le.mp him
  rw [eabasics_orth_orth] at h2
  exact h2

/-- **203IV.6** (`floor-basics`, eff.tex:4200, Lemma): `⌈p⌉ ∘ f = 0` iff
`p ∘ f = 0`. -/
theorem floor_basics_6 (p : Pred X) (f : Y ⟶ X) :
    f ≫ ceilPred p = 0 ↔ f ≫ p = 0 := by
  constructor
  · intro h
    have hle : (f ≫ p) ≼ (f ≫ ceilPred p) := comp_le_comp f (le_ceilPred p)
    rw [h] at hle
    exact eq_zero_of_le_zero hle
  · intro h
    have h5 := floor_basics_5 p f
    rw [h, ceilPred_zero] at h5
    exact eq_zero_of_le_zero h5

/-- **203XII** (`img-of-compr`, eff.tex:4284, Exercise): `p` is sharp iff
`⌊p⌋ = p`; consequently `im π_s = s` for sharp `s`. -/
theorem img_of_compr (p : Pred X) :
    (IsSharp p ↔ floorPred p = p) ∧
      (∀ s : Pred X, IsSharp s → imPred (comprMap s) = s) := by
  have key : ∀ r : Pred X, IsSharp r → floorPred r = r := by
    rintro r ⟨Y, f, hf⟩
    have hr : r = imPred f :=
      eabasics_le_antisymm (hf.2 (imPred f) (isImage_imPred f).1)
        ((isImage_imPred f).2 r hf.1)
    obtain ⟨g, hg, -⟩ := (isComprehension_comprMap r).2 f hf.1
    have h2 := (im_ineq (comprMap r) g).1
    rw [hg, ← hr] at h2
    exact eabasics_le_antisymm (floor_basics_1 r) h2
  refine ⟨⟨key p, ?_⟩, fun s hs => key s hs⟩
  intro hfp
  have h3 := isImage_imPred (comprMap p)
  rw [show imPred (comprMap p) = p from hfp] at h3
  exact ⟨_, _, h3⟩

/-- **203XIII** (`ceiling-within-ceiling`, eff.tex:4289, Exercise):
`⌈⌈p⌉ ∘ f⌉ = ⌈p ∘ f⌉`. -/
theorem ceiling_within_ceiling (p : Pred X) (f : Y ⟶ X) :
    ceilPred (f ≫ ceilPred p) = ceilPred (f ≫ p) := by
  -- `⌈·⌉` is monotone and idempotent, and `⌈p⌉ ∘ f ≤ ⌈p ∘ f⌉` (203IV.5)
  have hidem : ∀ q : Pred Y, ceilPred (ceilPred q) = ceilPred q := by
    intro q
    show orth (floorPred (orth (orth (floorPred (orth q)))))
      = orth (floorPred (orth q))
    rw [eabasics_orth_orth, floor_basics_3]
  refine eabasics_le_antisymm ?_ ?_
  · have h := ceilPred_mono (floor_basics_5 p f)
    rw [hidem] at h
    exact h
  · exact ceilPred_mono (comp_le_comp f (le_ceilPred p))

end FloorBasics

/-- Helper: `⋁` depends only on its two element arguments. -/
theorem ovee_eq_of_eq {E : Type*} [PCM E] {a b a' b' : E} (ha : a = a')
    (hb : b = b') (h : Perp a b) (h' : Perp a' b') :
    ovee a b h = ovee a' b' h' := by
  subst ha; subst hb; rfl

/-- Helper (used for 203XIV): in an effect algebra, `a ⋁ b = A ⋁ B` together
with `a ≤ A` and `b ≤ B` forces `a = A` and `b = B`.  (This is the
"cancellation" step of the solution `img-tupling`, bsols.tex:2892.) -/
theorem eq_of_ovee_eq_of_le {E : Type*} [EffectAlgebra E] {a b A B : E}
    (hab : Perp a b) (hAB : Perp A B) (haA : a ≼ A) (hbB : b ≼ B)
    (heq : ovee a b hab = ovee A B hAB) : a = A ∧ b = B := by
  -- `a ⋁ B ≤ A ⋁ B = a ⋁ b`, so `B ⋁ c = b` for some `c`, whence `B ≤ b`
  obtain ⟨haB, hle⟩ := eabasics_le_perp_compat haA hAB
  rw [← heq] at hle
  obtain ⟨c, hc, hcc⟩ := hle
  have hBc : Perp B c := PCM.perp_of_ovee_perp haB hc
  have haBc : Perp a (ovee B c hBc) := PCM.perp_ovee_of_ovee_perp haB hc
  have hassoc : ovee a (ovee B c hBc) haBc = ovee a b hab := by
    rw [← PCM.ovee_assoc haB hc]; exact hcc
  have e2 : ovee (ovee B c hBc) a (PCM.perp_comm haBc)
      = ovee b a (PCM.perp_comm hab) := by
    rw [← PCM.ovee_comm haBc, ← PCM.ovee_comm hab]
    exact hassoc
  have hBb : ovee B c hBc = b :=
    eabasics_cancellation (PCM.perp_comm haBc) (PCM.perp_comm hab) e2
  have hbeq : b = B := eabasics_le_antisymm hbB ⟨c, hBc, hBb⟩
  subst hbeq
  exact ⟨eabasics_cancellation hab hAB heq, rfl⟩

/-- **203XIV** (`img-tupling`, eff.tex:4295, Exercise), first half: in an
effectus with images, `im ⟨f, g⟩ = [im f, im g]`. -/
theorem img_tupling [HasImages C] {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) :
    imPred (effPair f g h) = coprod.desc (imPred f) (imPred g) := by
  -- every predicate on `X + Y` is a cotuple
  have hdesc : ∀ q : Pred (X ⨿ Y),
      coprod.desc (coprod.inl ≫ q) (coprod.inr ≫ q) = q := by
    intro q
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc]
    · rw [coprod.inr_desc]
  -- `[im f, im g] ∘ ⟨f,g⟩ = (im f ∘ f) ⋁ (im g ∘ g) = 1 ∘ ⟨f,g⟩`
  have hA : effPair f g h ≫ coprod.desc (imPred f) (imPred g)
      = effPair f g h ≫ truth (X ⨿ Y) := by
    obtain ⟨hp, e⟩ := eff_prod_rules_1 f g h (imPred f) (imPred g)
    rw [e, eff_prod_rules_2 f g h]
    exact ovee_eq_of_eq (isImage_imPred f).1 (isImage_imPred g).1 hp h
  have hle : imPred (effPair f g h) ≼ coprod.desc (imPred f) (imPred g) :=
    (isImage_imPred (effPair f g h)).2 _ hA
  -- write `im ⟨f,g⟩ = [p₁, p₂]`; the defining equation and cancellation give
  -- `p₁ ∘ f = 1 ∘ f` and `p₂ ∘ g = 1 ∘ g`, so `im f ≤ p₁` and `im g ≤ p₂`
  obtain ⟨hp, e⟩ := eff_prod_rules_1 f g h
    (coprod.inl ≫ imPred (effPair f g h)) (coprod.inr ≫ imPred (effPair f g h))
  rw [hdesc (imPred (effPair f g h)), (isImage_imPred (effPair f g h)).1,
    eff_prod_rules_2 f g h] at e
  obtain ⟨e₁, e₂⟩ := eq_of_ovee_eq_of_le hp h
    (comp_le_comp f (pred_le_truth _)) (comp_le_comp g (pred_le_truth _)) e.symm
  have hf : imPred f ≼ (coprod.inl ≫ imPred (effPair f g h)) :=
    (isImage_imPred f).2 _ e₁
  have hg : imPred g ≼ (coprod.inr ≫ imPred (effPair f g h)) :=
    (isImage_imPred g).2 _ e₂
  -- the reverse inequalities come from `hle` by precomposing with `κ₁`, `κ₂`
  have hf' : (coprod.inl ≫ imPred (effPair f g h)) ≼ imPred f := by
    have h1 := comp_le_comp (coprod.inl : X ⟶ X ⨿ Y) hle
    rwa [coprod.inl_desc] at h1
  have hg' : (coprod.inr ≫ imPred (effPair f g h)) ≼ imPred g := by
    have h1 := comp_le_comp (coprod.inr : Y ⟶ X ⨿ Y) hle
    rwa [coprod.inr_desc] at h1
  rw [← hdesc (imPred (effPair f g h)), eabasics_le_antisymm hf' hf,
    eabasics_le_antisymm hg' hg]

/-- **203XIV** (`img-tupling`, eff.tex:4295, Exercise), second half: a
predicate `[p, q]` is sharp iff `p` and `q` are sharp. -/
theorem img_tupling_sharp [HasImages C] {X Y : C} (p : Pred X) (q : Pred Y) :
    IsSharp (coprod.desc p q : X ⨿ Y ⟶ effObj C) ↔ IsSharp p ∧ IsSharp q := by
  -- images are unique, so `IsImage u r` forces `r = im u`
  have huniq : ∀ {A B : C} (u : A ⟶ B) (r : Pred B), IsImage u r → r = imPred u :=
    fun u r hr => eabasics_le_antisymm (hr.2 _ (isImage_imPred u).1)
      ((isImage_imPred u).2 _ hr.1)
  -- every map into a coproduct is the pairing of its partial projections
  have hpair : ∀ {Z : C} (u : Z ⟶ X ⨿ Y),
      u = effPair (u ≫ pproj₁ X Y) (u ≫ pproj₂ X Y) (coprod_prod_converse u) :=
    fun u => (coprod_prod (coprod_prod_converse u)).unique ⟨rfl, rfl⟩
      (effPair_spec _ _ _)
  constructor
  · rintro ⟨W, u, hu⟩
    have hdesc : coprod.desc p q = imPred u := huniq u _ hu
    rw [hpair u, img_tupling] at hdesc
    have h1 : p = imPred (u ≫ pproj₁ X Y) := by
      have hc : (coprod.inl : X ⟶ X ⨿ Y) ≫ coprod.desc p q
          = (coprod.inl : X ⟶ X ⨿ Y) ≫ coprod.desc (imPred (u ≫ pproj₁ X Y))
              (imPred (u ≫ pproj₂ X Y)) := by rw [hdesc]
      rwa [coprod.inl_desc, coprod.inl_desc] at hc
    have h2 : q = imPred (u ≫ pproj₂ X Y) := by
      have hc : (coprod.inr : Y ⟶ X ⨿ Y) ≫ coprod.desc p q
          = (coprod.inr : Y ⟶ X ⨿ Y) ≫ coprod.desc (imPred (u ≫ pproj₁ X Y))
              (imPred (u ≫ pproj₂ X Y)) := by rw [hdesc]
      rwa [coprod.inr_desc, coprod.inr_desc] at hc
    exact ⟨⟨_, _, by rw [h1]; exact isImage_imPred _⟩,
      ⟨_, _, by rw [h2]; exact isImage_imPred _⟩⟩
  · rintro ⟨⟨W, f, hf⟩, ⟨V, g, hg⟩⟩
    have hfp : p = imPred f := huniq f p hf
    have hgq : q = imPred g := huniq g q hg
    have inl_p1 : ∀ A B : C, (coprod.inl : A ⟶ A ⨿ B) ≫ pproj₁ A B = 𝟙 A :=
      fun A B => coprod.inl_desc _ _
    have inr_p1 : ∀ A B : C, (coprod.inr : B ⟶ A ⨿ B) ≫ pproj₁ A B = 0 :=
      fun A B => coprod.inr_desc _ _
    have inl_p2 : ∀ A B : C, (coprod.inl : A ⟶ A ⨿ B) ≫ pproj₂ A B = 0 :=
      fun A B => coprod.inl_desc _ _
    have inr_p2 : ∀ A B : C, (coprod.inr : B ⟶ A ⨿ B) ≫ pproj₂ A B = 𝟙 B :=
      fun A B => coprod.inr_desc _ _
    -- `f + g = ⟨▷₁ ; f, ▷₂ ; g⟩`, so its image is `[im f, im g]` by 203XIV.1
    have him0 : imPred (coprod.map f g)
        = coprod.desc (imPred (coprod.map f g ≫ pproj₁ X Y))
            (imPred (coprod.map f g ≫ pproj₂ X Y)) := by
      conv_lhs => rw [hpair (coprod.map f g)]
      rw [img_tupling]
    have e1 : coprod.map f g ≫ pproj₁ X Y = pproj₁ W V ≫ f := by
      refine coprod.hom_ext ?_ ?_
      · rw [← Category.assoc, coprod.inl_map, Category.assoc, inl_p1 X Y,
          Category.comp_id, ← Category.assoc, inl_p1 W V, Category.id_comp]
      · rw [← Category.assoc, coprod.inr_map, Category.assoc, inr_p1 X Y,
          FinPAC.comp_zero, ← Category.assoc, inr_p1 W V, FinPAC.zero_comp]
    have e2 : coprod.map f g ≫ pproj₂ X Y = pproj₂ W V ≫ g := by
      refine coprod.hom_ext ?_ ?_
      · rw [← Category.assoc, coprod.inl_map, Category.assoc, inl_p2 X Y,
          FinPAC.comp_zero, ← Category.assoc, inl_p2 W V, FinPAC.zero_comp]
      · rw [← Category.assoc, coprod.inr_map, Category.assoc, inr_p2 X Y,
          Category.comp_id, ← Category.assoc, inr_p2 W V, Category.id_comp]
    -- `im (▷₁ ; f) = im f`, as `κ₁ ; ▷₁ = id`
    have hf1 : imPred (pproj₁ W V ≫ f) = imPred f := by
      refine eabasics_le_antisymm (im_ineq f (pproj₁ W V)).1 ?_
      have h3 := (im_ineq (pproj₁ W V ≫ f) (coprod.inl : W ⟶ W ⨿ V)).1
      rw [← Category.assoc, inl_p1 W V, Category.id_comp] at h3
      exact h3
    have hg1 : imPred (pproj₂ W V ≫ g) = imPred g := by
      refine eabasics_le_antisymm (im_ineq g (pproj₂ W V)).1 ?_
      have h3 := (im_ineq (pproj₂ W V ≫ g) (coprod.inr : V ⟶ W ⨿ V)).1
      rw [← Category.assoc, inr_p2 W V, Category.id_comp] at h3
      exact h3
    have him : imPred (coprod.map f g) = coprod.desc (imPred f) (imPred g) := by
      rw [him0, e1, e2, hf1, hg1]
    exact ⟨_, coprod.map f g, by rw [hfp, hgq, ← him]; exact isImage_imPred _⟩

/-- **204I** (`compr-is-full`, eff.tex:4304, Lemma): for sharp predicates
`s, t` on the same object, `s ≤ t` iff `π_s` factors through `π_t`. -/
theorem compr_is_full [HasComprehension C] [HasImages C] {X : C}
    {s t : Pred X} (hs : IsSharp s) (ht : IsSharp t) :
    s ≼ t ↔ ∃ h : comprObj s ⟶ comprObj t, h ≫ comprMap t = comprMap s := by
  constructor
  · intro hst
    have hcm : comprMap s ≫ t = comprMap s ≫ truth X := by
      refine eabasics_le_antisymm (comp_le_comp _ (pred_le_truth t)) ?_
      rw [← (isComprehension_comprMap s).1]
      exact comp_le_comp _ hst
    obtain ⟨g, hg, -⟩ := (isComprehension_comprMap t).2 (comprMap s) hcm
    exact ⟨g, hg⟩
  · rintro ⟨h, hh⟩
    have h2 := (im_ineq (comprMap t) h).1
    rw [hh] at h2
    rw [← (img_of_compr s).2 s hs, ← (img_of_compr t).2 t ht]
    exact h2

/-- **204III** (eff.tex:4330, Lemma): in an effectus with images,
`im [f, g] = im f ∨ im g` (a supremum among all predicates). -/
theorem im_cotuple_sup [HasImages C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PCM.IsSup (imPred f) (imPred g) (imPred (coprod.desc f g)) := by
  have hkey : ∀ {W : C} (u : W ⟶ Z) (q : Pred Z), imPred u ≼ q →
      u ≫ q = u ≫ truth Z := by
    intro W u q hq
    refine eabasics_le_antisymm (comp_le_comp u (pred_le_truth q)) ?_
    have h1 := comp_le_comp u hq
    rwa [(isImage_imPred u).1] at h1
  have hd := (isImage_imPred (coprod.desc f g)).1
  refine ⟨?_, ?_, ?_⟩
  · refine (isImage_imPred f).2 _ ?_
    have h2 := congrArg (fun t => coprod.inl ≫ t) hd
    simp only [← Category.assoc, coprod.inl_desc] at h2
    exact h2
  · refine (isImage_imPred g).2 _ ?_
    have h2 := congrArg (fun t => coprod.inr ≫ t) hd
    simp only [← Category.assoc, coprod.inr_desc] at h2
    exact h2
  · intro c hcf hcg
    refine (isImage_imPred (coprod.desc f g)).2 c ?_
    apply coprod.hom_ext
    · rw [← Category.assoc, ← Category.assoc, coprod.inl_desc]
      exact hkey f c hcf
    · rw [← Category.assoc, ← Category.assoc, coprod.inr_desc]
      exact hkey g c hcg

/-- **204V** (`lattice-compr`, eff.tex:4353, Corollary): in an effectus
with comprehension and images, sharp predicates `s, t` have a supremum
`s ∨ t = im [π_s, π_t]` among all predicates, which is itself sharp. -/
theorem lattice_compr [HasComprehension C] [HasImages C] {X : C}
    {s t : Pred X} (hs : IsSharp s) (ht : IsSharp t) :
    PCM.IsSup s t (imPred (coprod.desc (comprMap s) (comprMap t))) ∧
      IsSharp (imPred (coprod.desc (comprMap s) (comprMap t))) := by
  refine ⟨?_, ⟨_, _, isImage_imPred (coprod.desc (comprMap s) (comprMap t))⟩⟩
  have h := im_cotuple_sup (comprMap s) (comprMap t)
  rw [(img_of_compr s).2 s hs, (img_of_compr t).2 t ht] at h
  exact h

/-! ## Cokernels (parsec 205) -/

/-- **205II** (`effectus-cokernels`, eff.tex:4369, Proposition), *second*
sentence: a quotient `ξ` for `im f` is a cokernel of `f`.  The Proposition's
headline — an effectus with quotients and images has **all** cokernels — is
`effectus_has_all_cokernels` below, which is this statement applied to the
chosen quotient `ξ_{im f}`. -/
theorem effectus_cokernels [HasImages C] {X Y Q : C} (f : X ⟶ Y)
    {ξ : Y ⟶ Q} (hξ : IsQuotient (imPred f) ξ) : IsCokernel f ξ := by
  have him : f ≫ orth (imPred f) = 0 :=
    (comp_orth_eq_zero_iff f (imPred f)).mpr (isImage_imPred f).1
  have h1 : f ≫ ξ = 0 := by
    have h2 : ((f ≫ ξ) ≫ truth Q) ≼ (f ≫ orth (imPred f)) := by
      rw [Category.assoc]
      exact comp_le_comp f hξ.1
    rw [him] at h2
    exact EffectusPartialForm.eq_zero_of_one_zero (eq_zero_of_le_zero h2)
  refine ⟨h1, ?_⟩
  intro Z g hg
  refine hξ.2 g ?_
  have hmin : imPred f ≼ orth (g ≫ truth Z) := by
    refine (isImage_imPred f).2 _ ?_
    rw [← comp_orth_eq_zero_iff, eabasics_orth_orth, ← Category.assoc, hg,
      FinPAC.zero_comp]
  exact eabasics_perp_iff_le_orth.mp
    (PCM.perp_comm (eabasics_perp_iff_le_orth.mpr hmin))

/-- **205II** (`effectus-cokernels`, eff.tex:4369, Proposition), headline
sentence: a category *has all cokernels* when every map has a cokernel.
(Named `HasAllCokernels` rather than `HasCokernels` to avoid a clash with
Mathlib's `CategoryTheory.Limits.HasCokernels`.) -/
class HasAllCokernels (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop where
  cok : ∀ {X Y : C} (f : X ⟶ Y), ∃ (W : C) (c : Y ⟶ W), IsCokernel f c

/-- **205II** (`effectus-cokernels`, eff.tex:4369, Proposition), the
Proposition's *first* sentence: **an effectus with quotients and images has
all cokernels**.  (Until the audit repair only the second sentence,
`effectus_cokernels`, was stated, and it assumed only `[HasImages C]`, so
the existence half — which is what needs `[HasQuotients C]` — was nowhere.)

The thesis's proof is exactly this: "a cokernel of a map `f` is given by a
quotient `ξ_{IM f}` of `IM f`", so the existence half is the chosen quotient
`ξ_{im f}` fed to `effectus_cokernels`. -/
instance effectus_has_all_cokernels [HasQuotients C] [HasImages C] :
    HasAllCokernels C where
  cok {_ _} f :=
    ⟨quotObj (imPred f), quotMap (imPred f),
      effectus_cokernels f (isQuotient_quotMap _)⟩

/-- **205II**, in the explicit form the Proposition states it: in an effectus
with quotients and images, a chosen quotient `ξ_{im f}` *is* a cokernel
of `f`. -/
theorem isCokernel_quotMap [HasQuotients C] [HasImages C] {X Y : C} (f : X ⟶ Y) :
    IsCokernel f (quotMap (imPred f)) :=
  effectus_cokernels f (isQuotient_quotMap _)

/-- **205IV** (`exc-cokernels`, eff.tex:4383, Exercise): in an effectus
with comprehension and images, a map `f` is a quotient for a sharp
predicate `s` iff `f` is a cokernel of a comprehension `π_s` for `s`. -/
theorem exc_cokernels [HasComprehension C] [HasImages C] {X Z : C}
    {s : Pred X} (hs : IsSharp s) (f : X ⟶ Z) :
    IsQuotient s f ↔ IsCokernel (comprMap s) f := by
  -- the two universal properties have the same side condition:
  -- `g ∘ π_s = 0` iff `1 ∘ g ≤ sᵖ` (using `im π_s = s` for sharp `s`)
  have him : imPred (comprMap s) = s := (img_of_compr s).2 s hs
  have key : ∀ {Y : C} (g : X ⟶ Y),
      comprMap s ≫ g = 0 ↔ (g ≫ truth Y) ≼ orth s := by
    intro Y g
    constructor
    · intro hg
      have h1 : comprMap s ≫ (g ≫ truth Y) = 0 := by
        rw [← Category.assoc, hg, FinPAC.zero_comp]
      have h2 : imPred (comprMap s) ≼ orth (g ≫ truth Y) := by
        refine (isImage_imPred (comprMap s)).2 _ ?_
        rw [← comp_orth_eq_zero_iff, eabasics_orth_orth]
        exact h1
      rw [him] at h2
      exact eabasics_perp_iff_le_orth.mp
        (PCM.perp_comm (eabasics_perp_iff_le_orth.mpr h2))
    · intro hg
      have h1 : (comprMap s ≫ (g ≫ truth Y)) ≼ (comprMap s ≫ orth s) :=
        comp_le_comp _ hg
      rw [compr_basics_6 (isComprehension_comprMap s)] at h1
      have h2 : comprMap s ≫ (g ≫ truth Y) = 0 := eq_zero_of_le_zero h1
      rw [← Category.assoc] at h2
      exact EffectusPartialForm.eq_zero_of_one_zero h2
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(key f).mpr h1, ?_⟩
    intro Y g hg
    exact h2 g ((key g).mp hg)
  · rintro ⟨h1, h2⟩
    refine ⟨(key f).mp h1, ?_⟩
    intro Y g hg
    exact h2 g ((key g).mpr hg)

end Theses.B.Eff
