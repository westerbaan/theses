/-
Theses/B/Eff/DiamondAmp.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
4408–5253: ⋄-effectuses (parsecs 206–210) and &-effectuses ("andthen
effectuses", parsecs 211–213).

Design:
* `DiamondEffectus C` is a Prop-class extending `HasQuotients`,
  `HasComprehension` and `HasImages` with the axiom that orthocomplements
  of sharp predicates are sharp.  The maps `f^⋄, f_⋄, f^□, f_□` between the
  sets `SPred` of sharp predicates are `diaPull`, `diaPush`, `boxPull`,
  `boxPush`.
* `AndThenEffectus C` ("&-effectus") adds the unique existence of
  ⋄-positive `asrt_p` maps and purity of quotient-after-comprehension;
  `asrt`, `andThen p q = q ∘ asrt_p` and the corresponding quotient `ζ_s`
  of a chosen comprehension `π_s` are obtained by (unique) choice.
* Not separately formalized: the examples 206III/210III/211IV beyond
  `vNᵒᵖ` (`CvNᵒᵖ`, `EJAᵒᵖ`, `Set`; sharp maps = nmiu-maps), the remarks
  211III/211IIIa on `assert` and polar decomposition, and 208VII (the
  functor to `OMLatGal`, whose data is exactly 207VI + 207III).
-/
import Theses.B.Eff.Quotients

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits

namespace Theses.B.Eff

universe u v

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-! ## ⋄-effectuses (parsec 206) -/

/-- **206II** (`diamond-basics`, eff.tex:4430, Definition): a
**⋄-effectus** is an effectus with quotients, comprehension and images such
that `sᵖ` is sharp for every sharp predicate `s`. -/
class DiamondEffectus (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop
    extends HasQuotients C, HasComprehension C, HasImages C where
  orth_sharp : ∀ {X : C} {s : Pred X}, IsSharp s → IsSharp (orth s)

section Diamond

variable [DiamondEffectus C] {X Y Z : C}

/-- The floor `⌊p⌋ = im π_p` of a predicate is sharp (it is an image; used
implicitly throughout parsecs 206–208). -/
theorem isSharp_floor (p : Pred X) : IsSharp (floorPred p) :=
  ⟨_, _, isImage_imPred _⟩

/-- In a ⋄-effectus ceilings are sharp: `⌈p⌉ = ⌊pᵖ⌋ᵖ` is the
orthocomplement of a sharp predicate (used in 206II to define `f^⋄`, and in
the proof of 207VI). -/
theorem isSharp_ceil (p : Pred X) : IsSharp (ceilPred p) :=
  DiamondEffectus.orth_sharp (isSharp_floor _)

/-- The orthocomplement within the sharp predicates (206II). -/
def SPred.orth (s : SPred X) : SPred X :=
  ⟨EffectAlgebra.orth s.1, DiamondEffectus.orth_sharp s.2⟩

/-- **206II** (`diamond-basics`, eff.tex:4444, Definition): the restriction
`f^⋄ : SPred Y → SPred X` of `f : X ⟶ Y` to sharp predicates,
`f^⋄(s) = ⌈s ∘ f⌉`. -/
noncomputable def diaPull (f : X ⟶ Y) (s : SPred Y) : SPred X :=
  ⟨ceilPred (f ≫ s.1), isSharp_ceil _⟩

/-- **206II** (`diamond-basics`, eff.tex:4449, Definition): the map
`f_⋄ : SPred X → SPred Y` of `f : X ⟶ Y`, `f_⋄(s) = im (f ∘ π_s)`. -/
noncomputable def diaPush (f : X ⟶ Y) (s : SPred X) : SPred Y :=
  ⟨imPred (comprMap s.1 ≫ f), _, _, isImage_imPred _⟩

/-- **206II** (`diamond-basics`, eff.tex:4473, Definition):
`f^□(s) = f^⋄(sᵖ)ᵖ`. -/
noncomputable def boxPull (f : X ⟶ Y) (s : SPred Y) : SPred X :=
  (diaPull f s.orth).orth

/-- **206II** (`diamond-basics`, eff.tex:4474, Definition):
`f_□(s) = f_⋄(sᵖ)ᵖ`. -/
noncomputable def boxPush (f : X ⟶ Y) (s : SPred X) : SPred Y :=
  (diaPush f s.orth).orth

/-- **206II.1** (`diamond-basics`, eff.tex:4453, Definition): maps
`f : X ⟶ Y` and `g : Y ⟶ X` are **⋄-adjoint** when `f^⋄ = g_⋄`. -/
def DiamondAdjoint (f : X ⟶ Y) (g : Y ⟶ X) : Prop :=
  diaPull f = diaPush g

/-- **206II.2** (`diamond-basics`, eff.tex:4458, Definition): an endomap is
**⋄-self-adjoint** when it is ⋄-adjoint to itself. -/
def DiamondSelfAdjoint (f : X ⟶ X) : Prop := DiamondAdjoint f f

/-- **206II.3** (`diamond-basics`, eff.tex:4462, Definition): maps
`f, g : X ⟶ Y` are **⋄-equivalent** when `f^⋄ = g^⋄` (equivalently
`f_⋄ = g_⋄`, 207VIIa). -/
def DiamondEquivalent (f g : X ⟶ Y) : Prop := diaPull f = diaPull g

/-- **206II.4** (`diamond-basics`, eff.tex:4468, Definition): a pure endomap
`f` is **⋄-positive** when `f = g ∘ g` for some ⋄-self-adjoint `g`. -/
def DiamondPositive (f : X ⟶ X) : Prop :=
  IsPure f ∧ ∃ g : X ⟶ X, DiamondSelfAdjoint g ∧ f = g ≫ g

end Diamond

/-- **206III** (eff.tex:4477, Examples): `vNᵒᵖ` is a ⋄-effectus (as are
`CvNᵒᵖ`, `EJAᵒᵖ` and `Set`, not formalized here). -/
theorem diamond_effectus_vn (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    DiamondEffectus WStarCPSU.{u}ᵒᵖ := sorry

/-! ## Basic properties of `(–)^⋄`, `(–)_⋄`, `(–)^□` (parsecs 207–208) -/

/-- Helper: `a ≤ bᵖ` iff `b ≤ aᵖ` in an effect algebra. -/
theorem le_orth_comm {E : Type*} [EffectAlgebra E] {a b : E} :
    a ≼ orth b ↔ b ≼ orth a := by
  rw [← eabasics_perp_iff_le_orth, ← eabasics_perp_iff_le_orth]
  exact ⟨PCM.perp_comm, PCM.perp_comm⟩

section DiamondBasics

variable [DiamondEffectus C] {X Y Z : C}

/-! ### Helper lemmas (images, ceilings and the sharp orthocomplement) -/

/-- The image of a map is unique. -/
theorem imPred_eq {X Y : C} (f : X ⟶ Y) {p : Pred Y} (h : IsImage f p) :
    imPred f = p :=
  eabasics_le_antisymm ((isImage_imPred f).2 p h.1) (h.2 _ (isImage_imPred f).1)

/-- `im f ≤ pᵖ` iff `p ∘ f = 0`. -/
theorem im_le_orth_iff {X Y : C} (g : X ⟶ Y) (p : Pred Y) :
    imPred g ≼ orth p ↔ g ≫ p = 0 := by
  have key : g ≫ p = 0 ↔ g ≫ orth p = g ≫ truth Y := by
    have h := comp_orth_eq_zero_iff g (orth p)
    rwa [eabasics_orth_orth] at h
  constructor
  · intro h
    rw [key]
    refine eabasics_le_antisymm (comp_le_comp g (pred_le_truth _)) ?_
    rw [← (isImage_imPred g).1]
    exact comp_le_comp g h
  · intro h
    exact (isImage_imPred g).2 _ (key.mp h)


/-- The image of the zero map is `0`. -/
theorem imPred_zero {W X : C} : imPred (0 : W ⟶ X) = 0 :=
  imPred_eq _ ⟨by rw [FinPAC.zero_comp, FinPAC.zero_comp], fun p _ => zero_le_hom p⟩

/-- `0` is sharp. -/
theorem dia_isSharp_zero (X : C) : IsSharp (0 : Pred X) :=
  ⟨X, 0, by rw [FinPAC.zero_comp, FinPAC.zero_comp], fun p _ => zero_le_hom p⟩

/-- `1` is sharp. -/
theorem isSharp_one (X : C) : IsSharp (1 : Pred X) :=
  ⟨X, 𝟙 X, rfl, by
    intro p hp
    rw [Category.id_comp, Category.id_comp] at hp
    rw [hp]
    exact pred_le_truth _⟩

/-- A comprehension for `1` is an isomorphism. -/
theorem isIso_comprMap_one (X : C) : IsIso (comprMap (1 : Pred X)) := by
  obtain ⟨θ, hθ, he, -⟩ := compr_basics_2 (isComprehension_comprMap (1 : Pred X))
    (compr_basics_3 (𝟙 X))
  rw [Category.comp_id] at he
  rw [← he]; exact hθ

/-- The sharp predicate `1`. -/
noncomputable def sOne (X : C) : SPred X := ⟨1, isSharp_one X⟩

/-- The sharp predicate `0`. -/
noncomputable def sZero (X : C) : SPred X := ⟨0, dia_isSharp_zero X⟩

@[simp] theorem sOne_val (X : C) : (sOne X).1 = (1 : Pred X) := rfl

@[simp] theorem sZero_val (X : C) : (sZero X).1 = (0 : Pred X) := rfl

/-- Ceilings are monotone (203IV.4). -/
theorem ceil_mono {X : C} {p q : Pred X} (h : p ≼ q) : ceilPred p ≼ ceilPred q :=
  eabasics_le_iff_orth_le.mp (floor_basics_4 (eabasics_le_iff_orth_le.mp h))

/-- `p ≤ ⌈p⌉` (203IV.1, dualized). -/
theorem le_ceil {X : C} (p : Pred X) : p ≼ ceilPred p := by
  have h := eabasics_le_iff_orth_le.mp (floor_basics_1 (orth p))
  rwa [eabasics_orth_orth] at h

/-- The ceiling of a sharp predicate is itself (203XII). -/
theorem ceil_of_isSharp {X : C} {s : Pred X} (hs : IsSharp s) : ceilPred s = s := by
  have h := (img_of_compr (orth s)).1.mp (DiamondEffectus.orth_sharp hs)
  show orth (floorPred (orth s)) = s
  rw [h, eabasics_orth_orth]

/-- The value of the sharp orthocomplement. -/
theorem spred_orth_val (s : SPred X) : (SPred.orth s).1 = orth s.1 := rfl

/-- The sharp orthocomplement is involutive. -/
theorem spred_orth_orth (s : SPred X) : s.orth.orth = s :=
  Subtype.ext (eabasics_orth_orth s.1)

/-- The supremum of two sharp predicates within the poset `SPred` (helper
for 207V, 208XII). -/
def SPred.IsSup (s t j : SPred X) : Prop :=
  s.1 ≼ j.1 ∧ t.1 ≼ j.1 ∧ ∀ r : SPred X, s.1 ≼ r.1 → t.1 ≼ r.1 → j.1 ≼ r.1

/-- The infimum of two sharp predicates within the poset `SPred` (helper
for 207V, 208IX). -/
def SPred.IsInf (s t m : SPred X) : Prop :=
  m.1 ≼ s.1 ∧ m.1 ≼ t.1 ∧ ∀ r : SPred X, r.1 ≼ s.1 → r.1 ≼ t.1 → r.1 ≼ m.1

/-- **207II** (`exc-diam-order-pres`, eff.tex:4487, Exercise): `f^⋄` and
`f^□` are order preserving. -/
theorem exc_diam_order_pres (f : X ⟶ Y) {s t : SPred Y} (h : s.1 ≼ t.1) :
    (diaPull f s).1 ≼ (diaPull f t).1 ∧
      (boxPull f s).1 ≼ (boxPull f t).1 := by
  refine ⟨ceil_mono (comp_le_comp f h), ?_⟩
  have h2 : orth t.1 ≼ orth s.1 := eabasics_le_iff_orth_le.mp h
  have h3 : ceilPred (f ≫ orth t.1) ≼ ceilPred (f ≫ orth s.1) :=
    ceil_mono (comp_le_comp f h2)
  exact eabasics_le_iff_orth_le.mp h3

/-- **207III** (`diamond-adjunction`, eff.tex:4491, Proposition): for
`f : X ⟶ Y` and sharp `s, t` we have `f^⋄(s) ≤ tᵖ` iff `f_⋄(t) ≤ sᵖ`. -/
theorem diamond_adjunction (f : X ⟶ Y) (s : SPred Y) (t : SPred X) :
    (diaPull f s).1 ≼ orth t.1 ↔ (diaPush f t).1 ≼ orth s.1 := by
  have ht : imPred (comprMap t.1) = t.1 := (img_of_compr t.1).2 t.1 t.2
  have e0 : ∀ q : Pred X, (q ≼ orth t.1 ↔ comprMap t.1 ≫ q = 0) := by
    intro q
    rw [le_orth_comm]
    conv_lhs => rw [← ht]
    exact im_le_orth_iff _ _
  show ceilPred (f ≫ s.1) ≼ orth t.1 ↔ imPred (comprMap t.1 ≫ f) ≼ orth s.1
  rw [e0, floor_basics_6, im_le_orth_iff, Category.assoc]

/-- **207III** (`diamond-adjunction`, eff.tex:4499, Proposition),
reformulated: `f_⋄` is the left order-adjoint of `f^□`:
`f_⋄(s) ≤ t ⟺ s ≤ f^□(t)`. -/
theorem diamond_adjunction' (f : X ⟶ Y) (s : SPred X) (t : SPred Y) :
    (diaPush f s).1 ≼ t.1 ↔ s.1 ≼ (boxPull f t).1 := by
  have h := diamond_adjunction f t.orth s
  rw [spred_orth_val, eabasics_orth_orth] at h
  rw [← h]
  exact le_orth_comm

/-- Unit of the order adjunction `f_⋄ ⊣ f^□` (207III). -/
theorem le_boxPull_diaPush (f : X ⟶ Y) (s : SPred X) :
    s.1 ≼ (boxPull f (diaPush f s)).1 :=
  (diamond_adjunction' f s (diaPush f s)).mp (pcm_preorder_refl _)

/-- Counit of the order adjunction `f_⋄ ⊣ f^□` (207III). -/
theorem diaPush_boxPull_le (f : X ⟶ Y) (t : SPred Y) :
    (diaPush f (boxPull f t)).1 ≼ t.1 :=
  (diamond_adjunction' f (boxPull f t) t).mpr (pcm_preorder_refl _)

/-- `f^□(sᵖ) = f^⋄(s)ᵖ`. -/
theorem boxPull_orth (f : X ⟶ Y) (s : SPred Y) :
    boxPull f s.orth = (diaPull f s).orth := by
  show (diaPull f s.orth.orth).orth = (diaPull f s).orth
  rw [spred_orth_orth]

/-- `f^□(s)ᵖ = f^⋄(sᵖ)`. -/
theorem orth_boxPull (f : X ⟶ Y) (s : SPred Y) :
    (boxPull f s).orth = diaPull f s.orth :=
  spred_orth_orth _

/-- **207V.1** (`order-adj-basics`, eff.tex:4527, Exercise): `f_⋄` is order
preserving. -/
theorem order_adj_basics_1 (f : X ⟶ Y) {s t : SPred X} (h : s.1 ≼ t.1) :
    (diaPush f s).1 ≼ (diaPush f t).1 :=
  (diamond_adjunction' f s (diaPush f t)).mpr
    (pcm_preorder_trans h (le_boxPull_diaPush f t))

/-- Orthocomplementation turns suprema of sharp predicates into infima. -/
theorem spred_isSup_orth {s t j : SPred X} (h : SPred.IsSup s t j) :
    SPred.IsInf s.orth t.orth j.orth := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨eabasics_le_iff_orth_le.mp h1, eabasics_le_iff_orth_le.mp h2, ?_⟩
  intro r hr1 hr2
  replace hr1 : r.1 ≼ orth s.1 := hr1
  replace hr2 : r.1 ≼ orth t.1 := hr2
  exact le_orth_comm.mp (h3 r.orth (le_orth_comm.mp hr1) (le_orth_comm.mp hr2))

/-- Orthocomplementation turns infima of sharp predicates into suprema. -/
theorem spred_isInf_orth {s t m : SPred X} (h : SPred.IsInf s t m) :
    SPred.IsSup s.orth t.orth m.orth := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨eabasics_le_iff_orth_le.mp h1, eabasics_le_iff_orth_le.mp h2, ?_⟩
  intro r hr1 hr2
  replace hr1 : orth s.1 ≼ r.1 := hr1
  replace hr2 : orth t.1 ≼ r.1 := hr2
  have k1 : orth r.1 ≼ s.1 :=
    eabasics_le_iff_orth_le.mpr (by rwa [eabasics_orth_orth])
  have k2 : orth r.1 ≼ t.1 :=
    eabasics_le_iff_orth_le.mpr (by rwa [eabasics_orth_orth])
  have k3 := eabasics_le_iff_orth_le.mp (h3 r.orth k1 k2)
  rwa [spred_orth_val, eabasics_orth_orth] at k3

/-- **207V.2** (`order-adj-basics`, eff.tex:4527, Exercise): `f_⋄` preserves
(binary) suprema. -/
theorem order_adj_basics_2 (f : X ⟶ Y) {s t j : SPred X}
    (h : SPred.IsSup s t j) :
    SPred.IsSup (diaPush f s) (diaPush f t) (diaPush f j) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨order_adj_basics_1 f h1, order_adj_basics_1 f h2, ?_⟩
  intro r hr1 hr2
  exact (diamond_adjunction' f j r).mpr
    (h3 (boxPull f r) ((diamond_adjunction' f s r).mp hr1)
      ((diamond_adjunction' f t r).mp hr2))

/-- **207V.3** (`order-adj-basics`, eff.tex:4527, Exercise): `f^□` preserves
(binary) infima. -/
theorem order_adj_basics_3 (f : X ⟶ Y) {s t m : SPred Y}
    (h : SPred.IsInf s t m) :
    SPred.IsInf (boxPull f s) (boxPull f t) (boxPull f m) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(exc_diam_order_pres f h1).2, (exc_diam_order_pres f h2).2, ?_⟩
  intro r hr1 hr2
  exact (diamond_adjunction' f r m).mp
    (h3 (diaPush f r) ((diamond_adjunction' f r s).mpr hr1)
      ((diamond_adjunction' f r t).mpr hr2))

/-- **207V.4** (`order-adj-basics`, eff.tex:4527, Exercise): `f^⋄` preserves
(binary) suprema. -/
theorem order_adj_basics_4 (f : X ⟶ Y) {s t j : SPred Y}
    (h : SPred.IsSup s t j) :
    SPred.IsSup (diaPull f s) (diaPull f t) (diaPull f j) := by
  have h3 := order_adj_basics_3 f (spred_isSup_orth h)
  rw [boxPull_orth, boxPull_orth, boxPull_orth] at h3
  have h4 := spred_isInf_orth h3
  rwa [spred_orth_orth, spred_orth_orth, spred_orth_orth] at h4

/-- **207V.5** (`order-adj-basics`, eff.tex:4527, Exercise):
`f_⋄ ∘ f^□ ∘ f_⋄ = f_⋄`. -/
theorem order_adj_basics_5 (f : X ⟶ Y) (s : SPred X) :
    diaPush f (boxPull f (diaPush f s)) = diaPush f s :=
  Subtype.ext (eabasics_le_antisymm (diaPush_boxPull_le f (diaPush f s))
    (order_adj_basics_1 f (le_boxPull_diaPush f s)))

/-- **207V.6** (`order-adj-basics`, eff.tex:4527, Exercise):
`f^□ ∘ f_⋄ ∘ f^□ = f^□`. -/
theorem order_adj_basics_6 (f : X ⟶ Y) (t : SPred Y) :
    boxPull f (diaPush f (boxPull f t)) = boxPull f t :=
  Subtype.ext (eabasics_le_antisymm (exc_diam_order_pres f (diaPush_boxPull_le f t)).2
    (le_boxPull_diaPush f (boxPull f t)))

theorem diaPull_id (s : SPred X) : diaPull (𝟙 X) s = s := by
  apply Subtype.ext
  show ceilPred (𝟙 X ≫ s.1) = s.1
  rw [Category.id_comp]
  exact ceil_of_isSharp s.2

theorem diaPull_comp (g : X ⟶ Y) (f : Y ⟶ Z) (s : SPred Z) :
    diaPull (g ≫ f) s = diaPull g (diaPull f s) := by
  apply Subtype.ext
  show ceilPred ((g ≫ f) ≫ s.1) = ceilPred (g ≫ ceilPred (f ≫ s.1))
  rw [ceiling_within_ceiling, Category.assoc]

/-- **207VI.1–2** (`diamond-functor`, eff.tex:4543, Lemma): `(–)^⋄` is
functorial: `(id)^⋄ = id` and `(f ∘ g)^⋄ = g^⋄ ∘ f^⋄`. -/
theorem diamond_functor_pull :
    (∀ s : SPred X, diaPull (𝟙 X) s = s) ∧
      ∀ (g : X ⟶ Y) (f : Y ⟶ Z) (s : SPred Z),
        diaPull (g ≫ f) s = diaPull g (diaPull f s) :=
  ⟨diaPull_id, diaPull_comp⟩

theorem boxPull_id (s : SPred X) : boxPull (𝟙 X) s = s := by
  show (diaPull (𝟙 X) s.orth).orth = s
  rw [diaPull_id, spred_orth_orth]

theorem boxPull_comp (g : X ⟶ Y) (f : Y ⟶ Z) (s : SPred Z) :
    boxPull (g ≫ f) s = boxPull g (boxPull f s) := by
  show (diaPull (g ≫ f) s.orth).orth = (diaPull g (boxPull f s).orth).orth
  rw [diaPull_comp, orth_boxPull]

/-- **207VI.3–4** (`diamond-functor`, eff.tex:4543, Lemma): `(–)^□` is
functorial. -/
theorem diamond_functor_box :
    (∀ s : SPred X, boxPull (𝟙 X) s = s) ∧
      ∀ (g : X ⟶ Y) (f : Y ⟶ Z) (s : SPred Z),
        boxPull (g ≫ f) s = boxPull g (boxPull f s) :=
  ⟨boxPull_id, boxPull_comp⟩

theorem diaPush_id (s : SPred X) : diaPush (𝟙 X) s = s := by
  apply Subtype.ext
  show imPred (comprMap s.1 ≫ 𝟙 X) = s.1
  rw [Category.comp_id]
  exact (img_of_compr s.1).2 s.1 s.2

theorem diaPush_comp (g : X ⟶ Y) (f : Y ⟶ Z) (s : SPred X) :
    diaPush (g ≫ f) s = diaPush f (diaPush g s) := by
  apply Subtype.ext
  refine eabasics_le_antisymm ?_ ?_
  · refine (diamond_adjunction' (g ≫ f) s (diaPush f (diaPush g s))).mpr ?_
    rw [boxPull_comp]
    exact (diamond_adjunction' g s _).mp (le_boxPull_diaPush f (diaPush g s))
  · refine (diamond_adjunction' f (diaPush g s) _).mpr ?_
    refine (diamond_adjunction' g s _).mpr ?_
    rw [← boxPull_comp]
    exact le_boxPull_diaPush (g ≫ f) s

/-- **207VI.5–6** (`diamond-functor`, eff.tex:4543, Lemma): `(–)_⋄` is
functorial: `(id)_⋄ = id` and `(f ∘ g)_⋄ = f_⋄ ∘ g_⋄`. -/
theorem diamond_functor_push :
    (∀ s : SPred X, diaPush (𝟙 X) s = s) ∧
      ∀ (g : X ⟶ Y) (f : Y ⟶ Z) (s : SPred X),
        diaPush (g ≫ f) s = diaPush f (diaPush g s) :=
  ⟨diaPush_id, diaPush_comp⟩

/-- **207VIIa** (`diamond-equiv-equiv`, eff.tex:4594, Exercise):
`f^⋄ = g^⋄` iff `f_⋄ = g_⋄`. -/
theorem diamond_equiv_equiv (f g : X ⟶ Y) :
    diaPull f = diaPull g ↔ diaPush f = diaPush g := by
  have pusheq : ∀ f g : X ⟶ Y, (∀ s : SPred Y, boxPull f s = boxPull g s) →
      diaPush f = diaPush g := by
    intro f g h
    funext t
    apply Subtype.ext
    refine eabasics_le_antisymm ?_ ?_
    · refine (diamond_adjunction' f t (diaPush g t)).mpr ?_
      rw [h]; exact le_boxPull_diaPush g t
    · refine (diamond_adjunction' g t (diaPush f t)).mpr ?_
      rw [← h]; exact le_boxPull_diaPush f t
  constructor
  · intro h
    refine pusheq f g fun s => ?_
    show (diaPull f s.orth).orth = (diaPull g s.orth).orth
    rw [h]
  · intro h
    have hbox : ∀ s : SPred Y, boxPull f s = boxPull g s := by
      intro s
      apply Subtype.ext
      refine eabasics_le_antisymm ?_ ?_
      · refine (diamond_adjunction' g (boxPull f s) s).mp ?_
        rw [← h]; exact diaPush_boxPull_le f s
      · refine (diamond_adjunction' f (boxPull g s) s).mp ?_
        rw [h]; exact diaPush_boxPull_le g s
    have e : ∀ k : X ⟶ Y, ∀ s : SPred Y, diaPull k s = (boxPull k s.orth).orth := by
      intro k s
      rw [boxPull_orth, spred_orth_orth]
    funext s
    rw [e f s, e g s, hbox s.orth]

/-- **208I** (`image-sharp-is-order-sharp`, eff.tex:4601, Lemma): in a
⋄-effectus sharp predicates are **order sharp**: `p ≤ s` and `p ≤ sᵖ` imply
`p = 0`. -/
theorem image_sharp_is_order_sharp {p s : Pred X} (hs : IsSharp s)
    (h₁ : p ≼ s) (h₂ : p ≼ orth s) : p = 0 := by
  have hcs : IsSharp (ceilPred p) := isSharp_ceil p
  have hc1 : ceilPred p ≼ s := by
    have h := ceil_mono h₁; rwa [ceil_of_isSharp hs] at h
  have hc2 : ceilPred p ≼ orth s := by
    have h := ceil_mono h₂
    rwa [ceil_of_isSharp (DiamondEffectus.orth_sharp hs)] at h
  obtain ⟨h, hh⟩ := (compr_is_full hcs hs).mp hc1
  have e3 : comprMap (ceilPred p) ≫ orth s = 0 := by
    rw [← hh, Category.assoc, compr_basics_6 (isComprehension_comprMap s),
      FinPAC.comp_zero]
  have hz : comprMap (ceilPred p) ≫ truth X = 0 := by
    rw [← (isComprehension_comprMap (ceilPred p)).1]
    refine eq_zero_of_le_zero ?_
    rw [← e3]
    exact comp_le_comp _ hc2
  have hzero : comprMap (ceilPred p) = 0 :=
    EffectusPartialForm.eq_zero_of_one_zero hz
  have hc0 : ceilPred p = 0 := by
    have h := (img_of_compr (ceilPred p)).2 (ceilPred p) hcs
    rw [hzero, imPred_zero] at h
    exact h.symm
  exact eq_zero_of_le_zero (by rw [← hc0]; exact le_ceil p)

/-- Suprema for the algebraic order are unique. -/
theorem pcm_sup_unique {E : Type*} [EffectAlgebra E] {a b j j' : E}
    (h : PCM.IsSup a b j) (h' : PCM.IsSup a b j') : j = j' :=
  eabasics_le_antisymm (h.2.2 j' h'.1 h'.2.1) (h'.2.2 j h.1 h.2.1)

/-- Orthogonal sharp predicates have infimum `0` (208III, "Ortholattice"). -/
theorem isInf_zero_of_perp {X : C} {s t : Pred X} (hs : IsSharp s)
    (h : Perp s t) : PCM.IsInf s t 0 := by
  refine ⟨zero_le_hom _, zero_le_hom _, ?_⟩
  intro r hrs hrt
  have hts : t ≼ orth s := eabasics_perp_iff_le_orth.mp (PCM.perp_comm h)
  have hr0 : r = 0 :=
    image_sharp_is_order_sharp hs hrs (pcm_preorder_trans hrt hts)
  rw [hr0]
  exact pcm_preorder_refl 0

/-- Sharp predicates are closed under `⋁` (208III, "Sub-EA"): for orthogonal
sharp `s, t` the sum `s ⋁ t` is the supremum `s ∨ t`, which is sharp. -/
theorem isSharp_ovee {X : C} {s t : Pred X} (hs : IsSharp s) (ht : IsSharp t)
    (h : Perp s t) : IsSharp (ovee s t h) := by
  obtain ⟨j, hmj, hsup, he⟩ := ea_modularity_prop h (isInf_zero_of_perp hs h)
  have hj : ovee s t h = j := by rw [he, PCM.zero_ovee]
  obtain ⟨hsup', hsharp'⟩ := lattice_compr hs ht
  rw [hj, pcm_sup_unique hsup hsup']
  exact hsharp'

/-- **208III** (`diamond-oml`, eff.tex:4625, Proposition (Cho)), first half:
in a ⋄-effectus the sharp predicates form a sub-effect algebra of
`Pred X`. -/
theorem diamond_oml_subEA (X : C) :
    ∃ D : SubEffectAlgebra (Pred X),
      D.carrier = { p : Pred X | IsSharp p } :=
  ⟨⟨{ p : Pred X | IsSharp p }, dia_isSharp_zero X, isSharp_one X,
    fun h ha hb => isSharp_ovee ha hb h,
    fun ha => DiamondEffectus.orth_sharp ha⟩, rfl⟩

/-- **208III** (`diamond-oml`, eff.tex:4625, Proposition (Cho)), second
half: `SPred X` is an orthomodular lattice (for the order inherited from
`Pred X`, with orthocomplement `sᵖ`). -/
theorem diamond_oml (X : C) :
    ∃ oml : OrthomodularLattice (SPred X), ∀ s t : SPred X,
      (letI := oml
       (s ≤ t ↔ s.1 ≼ t.1) ∧ sᶜ = s.orth) := sorry

end DiamondBasics

/-- The category `OMLatGal` of orthomodular lattices with Galois
connections between them (Jacobs; needed for 208VII). -/
structure OMLatGalCat : Type (u + 1) where
  carrier : Type u
  [str : OrthomodularLattice carrier]

attribute [instance] OMLatGalCat.str

/-- A Galois connection between orthomodular lattices — the morphisms of
`OMLatGal` (208VII). -/
structure GaloisPair (A B : Type u) [OrthomodularLattice A]
    [OrthomodularLattice B] where
  push : A → B
  pull : B → A
  adj : ∀ (a : A) (b : B), push a ≤ b ↔ a ≤ pull b

instance : Category.{u} OMLatGalCat.{u} where
  Hom A B := GaloisPair A.carrier B.carrier
  id _ := ⟨_root_.id, _root_.id, fun _ _ => Iff.rfl⟩
  comp f g := ⟨g.push ∘ f.push, f.pull ∘ g.pull,
    fun _ _ => (g.adj _ _).trans (f.adj _ _)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- **208VII** (eff.tex:4661, Corollary): in a ⋄-effectus the assignment
`X ↦ SPred X`, `f ↦ (f_⋄, f^□)` yields a functor to `OMLatGal`, the
category of orthomodular lattices with Galois connections (Jacobs). -/
theorem diamond_omlatgal_functor [DiamondEffectus C] :
    ∃ F : C ⥤ OMLatGalCat.{v},
      ∀ X : C, (F.obj X).carrier = SPred X := sorry

section DiamondBasics2

variable [DiamondEffectus C] {X Y Z : C}

theorem diaPush_one_val (f : X ⟶ Y) :
    (diaPush f (sOne X)).1 = imPred f :=
  (im_ineq f (comprMap (1 : Pred X))).2 _ (isIso_comprMap_one X)

/-- **208IX** (`spred-infimum`, eff.tex:4676, Lemma): for sharp `s, t` the
infimum is `s ∧ t = (π_s)_⋄ ((π_s)^□ (t))`. -/
theorem spred_infimum {X : C} (s t : SPred X) :
    SPred.IsInf s t
      (diaPush (comprMap s.1) (boxPull (comprMap s.1) t)) := by
  have hims : imPred (comprMap s.1) = s.1 := (img_of_compr s.1).2 s.1 s.2
  refine ⟨?_, diaPush_boxPull_le _ t, ?_⟩
  · have h := order_adj_basics_1 (comprMap s.1)
      (show (boxPull (comprMap s.1) t).1 ≼ (sOne (comprObj s.1)).1
        from pred_le_truth _)
    rwa [diaPush_one_val, hims] at h
  · intro r hrs hrt
    obtain ⟨h, hh⟩ := (compr_is_full r.2 s.2).mp hrs
    have hr0 : diaPush (comprMap s.1)
        (diaPush h (sOne (comprObj r.1))) = r := by
      rw [← diaPush_comp]
      apply Subtype.ext
      rw [diaPush_one_val, hh]
      exact (img_of_compr r.1).2 r.1 r.2
    have hr : (diaPush (comprMap s.1)
        (diaPush h (sOne (comprObj r.1)))).1 = r.1 :=
      congrArg Subtype.val hr0
    have h1 : (diaPush h (sOne (comprObj r.1))).1 ≼
        (boxPull (comprMap s.1) r).1 := by
      have hu := le_boxPull_diaPush (comprMap s.1)
        (diaPush h (sOne (comprObj r.1)))
      rwa [hr0] at hu
    have h3 := order_adj_basics_1 (comprMap s.1)
      (pcm_preorder_trans h1 (exc_diam_order_pres (comprMap s.1) hrt).2)
    rwa [hr] at h3

theorem boxPull_zero_of_isQuotient {X Q : C} {q : Pred X} (hq : IsSharp q)
    {ξ : X ⟶ Q} (hξ : IsQuotient q ξ) :
    (boxPull ξ (sZero Q)).1 = q := by
  show orth (ceilPred (ξ ≫ orth (0 : Pred Q))) = q
  have h0 : orth (0 : Pred Q) = truth Q := eabasics_orth_zero
  rw [h0, show ξ ≫ truth Q = orth q from quotient_basics_5 hξ,
    ceil_of_isSharp (DiamondEffectus.orth_sharp hq), eabasics_orth_orth]

/-- **208XII** (`spred-sup`, eff.tex:4709, Exercise): for sharp `s, t` and a
quotient `ξ` for `s`, we have `(ξ^□ ∘ ξ_⋄)(t) = s ∨ t`. -/
theorem spred_sup {X : C} (s t : SPred X) :
    SPred.IsSup s t
      (boxPull (quotMap s.1) (diaPush (quotMap s.1) t)) := by
  have hq : IsQuotient s.1 (quotMap s.1) := isQuotient_quotMap s.1
  refine ⟨?_, le_boxPull_diaPush (quotMap s.1) t, ?_⟩
  · have h := (exc_diam_order_pres (quotMap s.1)
      (show (sZero (quotObj s.1)).1 ≼ (diaPush (quotMap s.1) t).1
        from zero_le_hom _)).2
    rwa [boxPull_zero_of_isQuotient s.2 hq] at h
  · intro r hsr htr
    have hqr : IsQuotient r.1 (quotMap r.1) := isQuotient_quotMap r.1
    have hle : ((quotMap r.1) ≫ truth (quotObj r.1)) ≼ orth s.1 := by
      rw [quotient_basics_5 hqr]
      exact eabasics_le_iff_orth_le.mp hsr
    obtain ⟨h', hh', -⟩ := hq.2 (quotMap r.1) hle
    have hr0 : boxPull (quotMap s.1)
        (boxPull h' (sZero (quotObj r.1))) = r := by
      rw [← boxPull_comp, hh']
      apply Subtype.ext
      exact boxPull_zero_of_isQuotient r.2 hqr
    have hr : (boxPull (quotMap s.1)
        (boxPull h' (sZero (quotObj r.1)))).1 = r.1 :=
      congrArg Subtype.val hr0
    have h1 : (diaPush (quotMap s.1) r).1 ≼
        (boxPull h' (sZero (quotObj r.1))).1 :=
      (diamond_adjunction' (quotMap s.1) r _).mpr
        (by rw [hr]; exact pcm_preorder_refl _)
    have h2 := pcm_preorder_trans (order_adj_basics_1 (quotMap s.1) htr) h1
    have h3 := (exc_diam_order_pres (quotMap s.1) h2).2
    rwa [hr] at h3

/-! ### ⋄-adjointness (parsec 209) -/

/-- **209II.1** (`exc-diamond-adj`, eff.tex:4722, Exercise): `f^⋄ = g_⋄` iff
`f_⋄ = g^⋄`. -/
theorem exc_diamond_adj_1 (f : X ⟶ Y) (g : Y ⟶ X) :
    DiamondAdjoint f g ↔ diaPush f = diaPull g := by
  have key : ∀ {A B : C} (f : A ⟶ B) (g : B ⟶ A), diaPull f = diaPush g →
      diaPush f = diaPull g := by
    intro A B f g h
    have step : ∀ (a : SPred A) (b : SPred B),
        ((diaPush f a).1 ≼ b.1 ↔ (diaPull g a).1 ≼ b.1) := by
      intro a b
      have e1 := diamond_adjunction' f a b
      have e2 : a.1 ≼ (boxPull f b).1 ↔ (diaPull f b.orth).1 ≼ orth a.1 :=
        le_orth_comm
      have e3 : ((diaPull f b.orth).1 ≼ orth a.1) ↔
          (diaPush g b.orth).1 ≼ orth a.1 := by rw [h]
      have e4 := diamond_adjunction' g b.orth a.orth
      have e5 : (b.orth).1 ≼ (boxPull g a.orth).1 ↔ (diaPull g a).1 ≼ b.1 := by
        rw [boxPull_orth]
        exact eabasics_le_iff_orth_le.symm
      exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
    funext a
    apply Subtype.ext
    exact eabasics_le_antisymm ((step a (diaPull g a)).mpr (pcm_preorder_refl _))
      ((step a (diaPush f a)).mp (pcm_preorder_refl _))
  exact ⟨fun h => key f g h, fun h => (key g f h.symm).symm⟩

/-- **209II.2** (`exc-diamond-adj`, eff.tex:4722, Exercise): if `f` and `g`
are ⋄-adjoint, then `im f = ⌈1 ∘ g⌉`. -/
theorem exc_diamond_adj_2 {f : X ⟶ Y} {g : Y ⟶ X}
    (h : DiamondAdjoint f g) :
    imPred f = ceilPred (g ≫ truth X) := by
  have h' : diaPush f = diaPull g := (exc_diamond_adj_1 f g).mp h
  have h1 : imPred (comprMap (1 : Pred X) ≫ f) = ceilPred (g ≫ (1 : Pred X)) :=
    congrArg Subtype.val (congrFun h' ⟨1, isSharp_one X⟩)
  rw [(im_ineq f (comprMap (1 : Pred X))).2 _ (isIso_comprMap_one X)] at h1
  exact h1

/-- **209III.1** (`diamond-squares`, eff.tex:4735, Exercise): if `f` is
⋄-self-adjoint, then so is `f ∘ f`. -/
theorem diamond_squares_1 {f : X ⟶ X} (h : DiamondSelfAdjoint f) :
    DiamondSelfAdjoint (f ≫ f) := by
  have h' : diaPull f = diaPush f := h
  show diaPull (f ≫ f) = diaPush (f ≫ f)
  funext s
  rw [diaPull_comp, diaPush_comp, h']

/-- **209III.2** (`diamond-squares`, eff.tex:4735, Exercise): ⋄-positive
maps are ⋄-self-adjoint. -/
theorem diamond_squares_2 {f : X ⟶ X} (h : DiamondPositive f) :
    DiamondSelfAdjoint f := by
  obtain ⟨-, g, hg, rfl⟩ := h
  exact diamond_squares_1 hg

/-- **209III.3** (`diamond-squares`, eff.tex:4735, Exercise): if `f` is
⋄-positive and `f ∘ f` is pure, then `f ∘ f` is ⋄-positive. -/
theorem diamond_squares_3 {f : X ⟶ X} (h : DiamondPositive f)
    (hp : IsPure (f ≫ f)) : DiamondPositive (f ≫ f) :=
  ⟨hp, f, diamond_squares_2 h, rfl⟩

theorem isImage_compr_comp_inv (α : X ⟶ Y) [IsIso α] {s : Pred Y}
    (hs : IsSharp s) : IsImage (comprMap s ≫ inv α) (α ≫ s) := by
  have him : IsImage (comprMap s) s := by
    have h : imPred (comprMap s) = s := (img_of_compr s).2 s hs
    have h2 := isImage_imPred (comprMap s)
    rwa [h] at h2
  have htot : inv α ≫ truth X = truth Y := iso_isTotal (inv α)
  constructor
  · calc (comprMap s ≫ inv α) ≫ (α ≫ s)
        = comprMap s ≫ ((inv α ≫ α) ≫ s) := by simp only [Category.assoc]
      _ = comprMap s ≫ s := by rw [IsIso.inv_hom_id, Category.id_comp]
      _ = comprMap s ≫ truth Y := (isComprehension_comprMap s).1
      _ = (comprMap s ≫ inv α) ≫ truth X := by rw [Category.assoc, htot]
  · intro p hp
    have hp' : comprMap s ≫ (inv α ≫ p) = comprMap s ≫ truth Y := by
      rw [← Category.assoc, hp, Category.assoc, htot]
    have h3 : (α ≫ s) ≼ (α ≫ (inv α ≫ p)) :=
      comp_le_comp α (him.2 (inv α ≫ p) hp')
    rwa [← Category.assoc, IsIso.hom_inv_id, Category.id_comp] at h3

/-- **209IV.1** (`iso-diamond-adjoint`, eff.tex:4750, Lemma): for an
isomorphism `α`, the predicate `s ∘ α` is sharp for sharp `s`. -/
theorem iso_diamond_adjoint_1 (α : X ⟶ Y) [IsIso α] {s : Pred Y}
    (hs : IsSharp s) : IsSharp (α ≫ s) :=
  ⟨comprObj s, comprMap s ≫ inv α, isImage_compr_comp_inv α hs⟩

/-- **209IV.2** (`iso-diamond-adjoint`, eff.tex:4750, Lemma): for an
isomorphism `α`, `α^⋄(s) = s ∘ α` and `α_⋄(s) = s ∘ α⁻¹`; in particular `α`
and `α⁻¹` are ⋄-adjoint. -/
theorem iso_diamond_adjoint_2 (α : X ⟶ Y) [IsIso α] :
    (∀ s : SPred Y, (diaPull α s).1 = α ≫ s.1) ∧
      (∀ s : SPred X, (diaPush α s).1 = inv α ≫ s.1) ∧
      DiamondAdjoint α (inv α) := by
  have hpull : ∀ s : SPred Y, (diaPull α s).1 = α ≫ s.1 := fun s =>
    ceil_of_isSharp (iso_diamond_adjoint_1 α s.2)
  have hpush : ∀ s : SPred X, (diaPush α s).1 = inv α ≫ s.1 := by
    intro s
    have h := isImage_compr_comp_inv (inv α) s.2
    rw [IsIso.inv_inv] at h
    exact imPred_eq _ h
  refine ⟨hpull, hpush, ?_⟩
  funext s
  apply Subtype.ext
  show (diaPull α s).1 = (diaPush (inv α) s).1
  rw [hpull s]
  exact (imPred_eq _ (isImage_compr_comp_inv α s.2)).symm

/-! ### Sharp maps (parsec 210) -/

/-- **210I** (`sharp-map`, eff.tex:4779, Definition): a map `f` in a
⋄-effectus is **sharp** when `s ∘ f` is sharp for every sharp `s`. -/
def SharpMap (f : X ⟶ Y) : Prop :=
  ∀ s : Pred Y, IsSharp s → IsSharp (f ≫ s)

/-- **210II** (`sharp-ceil`, eff.tex:4784, Exercise): `f` is sharp iff
`⌈p ∘ f⌉ = ⌈p⌉ ∘ f` for every predicate `p`. -/
theorem sharp_ceil (f : X ⟶ Y) :
    SharpMap f ↔ ∀ p : Pred Y, ceilPred (f ≫ p) = f ≫ ceilPred p := by
  constructor
  · intro hf p
    rw [← ceiling_within_ceiling p f]
    exact ceil_of_isSharp (hf _ (isSharp_ceil p))
  · intro h s hs
    have hs' := h s
    rw [ceil_of_isSharp hs] at hs'
    rw [← hs']
    exact isSharp_ceil _

end DiamondBasics2

/-! ## &-effectuses (parsec 211) -/

/-- **211II** (eff.tex:4809, Definition): an **&-effectus** ("andthen
effectus") is a ⋄-effectus such that

1. for each predicate `p` on `X` there is a unique ⋄-positive map
   `asrt_p : X ⟶ X` with `1 ∘ asrt_p = p`; and
2. for every quotient `ξ` and comprehension `π`, the composite `ξ ∘ π` is
   pure. -/
class AndThenEffectus (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop
    extends DiamondEffectus C where
  existsUnique_asrt : ∀ {X : C} (p : Pred X),
    ∃! f : X ⟶ X, DiamondPositive f ∧ f ≫ truth X = p
  quot_after_compr_pure : ∀ {X Y Z : C} {p q : Pred Y}
    (π : X ⟶ Y) (ξ : Y ⟶ Z),
    IsComprehension p π → IsQuotient q ξ → IsPure (π ≫ ξ)

section AndThen

variable [AndThenEffectus C] {X Y Z : C}

/-- **211II** (eff.tex:4818, Definition): the **assert map**
`asrt_p : X ⟶ X` of a predicate `p` — the unique ⋄-positive map with
`1 ∘ asrt_p = p`. -/
noncomputable def asrt (p : Pred X) : X ⟶ X :=
  (AndThenEffectus.existsUnique_asrt p).exists.choose

/-- The defining property of `asrt` (211II). -/
theorem asrt_spec (p : Pred X) :
    DiamondPositive (asrt p) ∧ asrt p ≫ truth X = p :=
  (AndThenEffectus.existsUnique_asrt p).exists.choose_spec

/-- Uniqueness of the assert map (211II). -/
theorem asrt_unique (p : Pred X) (f : X ⟶ X) (hf : DiamondPositive f)
    (h1 : f ≫ truth X = p) : f = asrt p :=
  (AndThenEffectus.existsUnique_asrt p).unique ⟨hf, h1⟩ (asrt_spec p)

/-- **211II** (eff.tex:4830, Definition): the sequential conjunction
`p & q = q ∘ asrt_p` ("`p` andthen `q`"); `p² = p & p`. -/
noncomputable def andThen (p q : Pred X) : Pred X := asrt p ≫ q

/-- **211IV** (`vn-is-andthen-eff`, eff.tex:4876, Examples): `vNᵒᵖ` is an
&-effectus, with `asrt_a(b) = √a b √a` (as are `CvNᵒᵖ` and `EJAᵒᵖ`, not
formalized here; these are the only known examples). -/
theorem vn_is_andthen_eff (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    AndThenEffectus WStarCPSU.{u}ᵒᵖ := sorry

/-- **211V** (`sharp-prop`, eff.tex:4889, Proposition): for a predicate `p`
in an &-effectus the following are equivalent: (1) `p` is sharp;
(2) `p & p = p`; (3) `asrt_p ∘ asrt_p = asrt_p`. -/
theorem sharp_prop (p : Pred X) :
    (IsSharp p ↔ andThen p p = p) ∧
      (IsSharp p ↔ asrt p ≫ asrt p = asrt p) := sorry

/-- **211VII** (`prop-corr-zeta-pi`, eff.tex:4951, Proposition), first
part: for sharp `s` there are a comprehension `π_s` for `s` and a quotient
`ζ_s` for `sᵖ` with `ζ_s ∘ π_s = id` and `π_s ∘ ζ_s = asrt_s`. -/
theorem prop_corr_zeta_pi {s : Pred X} (hs : IsSharp s) :
    ∃ (W : C) (π : W ⟶ X) (ζ : X ⟶ W),
      IsComprehension s π ∧ IsQuotient (orth s) ζ ∧
        π ≫ ζ = 𝟙 W ∧ ζ ≫ π = asrt s := sorry

/-- **211VII** (`prop-corr-zeta-pi`, eff.tex:4960, Proposition), second
part (with the uniqueness of 211IX): for *every* comprehension `π` for a
sharp `s` there is a unique quotient `ζ` for `sᵖ` with `ζ ∘ π = id` and
`π ∘ ζ = asrt_s`. -/
theorem prop_corr_zeta_pi_compr {s : Pred X} (hs : IsSharp s) {W : C}
    {π : W ⟶ X} (hπ : IsComprehension s π) :
    ∃! ζ : X ⟶ W,
      IsQuotient (orth s) ζ ∧ π ≫ ζ = 𝟙 W ∧ ζ ≫ π = asrt s := sorry

/-- **211VII** (`prop-corr-zeta-pi`, eff.tex:4963, Proposition), third
part: conversely, for every quotient `ζ` for `sᵖ` (`s` sharp) there is a
comprehension `π` for `s` with `ζ ∘ π = id` and `π ∘ ζ = asrt_s`. -/
theorem prop_corr_zeta_pi_quot {s : Pred X} (hs : IsSharp s) {W : C}
    {ζ : X ⟶ W} (hζ : IsQuotient (orth s) ζ) :
    ∃ π : W ⟶ X,
      IsComprehension s π ∧ π ≫ ζ = 𝟙 W ∧ ζ ≫ π = asrt s := sorry

/-- **211IX** (`zeta-s-convention`, eff.tex:5002, Notation): the
**corresponding quotient** `ζ_s : X ⟶ {X|s}` of the chosen comprehension
`π_s` for a sharp predicate `s`: the unique quotient for `sᵖ` with
`ζ_s ∘ π_s = id` and `π_s ∘ ζ_s = asrt_s`.  (Beware, 211X:
`ξ_{sᵖ} = ζ_s`.) -/
noncomputable def zetaMap (s : Pred X) (hs : IsSharp s) : X ⟶ comprObj s :=
  (prop_corr_zeta_pi_compr hs (isComprehension_comprMap s)).exists.choose

/-- The defining property of `ζ_s` (211IX). -/
theorem zetaMap_spec (s : Pred X) (hs : IsSharp s) :
    IsQuotient (orth s) (zetaMap s hs) ∧
      comprMap s ≫ zetaMap s hs = 𝟙 (comprObj s) ∧
      zetaMap s hs ≫ comprMap s = asrt s :=
  (prop_corr_zeta_pi_compr hs (isComprehension_comprMap s)).exists.choose_spec

/-- **211XI** (`upm-closed`, eff.tex:5020, Proposition), first half: in an
&-effectus comprehensions are closed under composition. -/
theorem upm_closed_compr {p : Pred Y} {q : Pred Z} {π₁ : X ⟶ Y}
    {π₂ : Y ⟶ Z} (h₁ : IsComprehension p π₁) (h₂ : IsComprehension q π₂) :
    ∃ r : Pred Z, IsComprehension r (π₁ ≫ π₂) := sorry

/-- **211XI** (`upm-closed`, eff.tex:5020, Proposition), second half: in an
&-effectus pure maps are closed under composition. -/
theorem upm_closed_pure {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsPure f) (hg : IsPure g) : IsPure (f ≫ g) := sorry

/-- **211XIV** (`andthen-square-rule`, eff.tex:5075, Exercise):
`asrt_p ∘ asrt_p = asrt_{p & p}`. -/
theorem andthen_square_rule (p : Pred X) :
    asrt p ≫ asrt p = asrt (andThen p p) := by
  refine asrt_unique _ _ ?_ ?_
  · exact diamond_squares_3 (asrt_spec p).1
      (upm_closed_pure (asrt_spec p).1.1 (asrt_spec p).1.1)
  · rw [Category.assoc, (asrt_spec p).2]
    rfl

/-- **211XV** (`asrt-absorp-rule`, eff.tex:5079, Exercise): for sharp `s`
(on the codomain) and `t` (on the domain): `im f ≤ s ⟺ asrt_s ∘ f = f` and
`1 ∘ f ≤ t ⟺ f ∘ asrt_t = f`. -/
theorem asrt_absorp_rule (f : X ⟶ Y) {s : Pred Y} {t : Pred X}
    (hs : IsSharp s) (ht : IsSharp t) :
    (imPred f ≼ s ↔ f ≫ asrt s = f) ∧
      ((f ≫ truth Y) ≼ t ↔ asrt t ≫ f = f) := by
  obtain ⟨-, hπζs, hζπs⟩ := zetaMap_spec s hs
  obtain ⟨hqζt, hπζt, hζπt⟩ := zetaMap_spec t ht
  constructor
  · constructor
    · intro him
      have he : f ≫ s = f ≫ truth Y :=
        eabasics_le_antisymm (comp_le_comp f (pred_le_truth _))
          (by rw [← (isImage_imPred f).1]; exact comp_le_comp f him)
      obtain ⟨g, hg, -⟩ := (isComprehension_comprMap s).2 f he
      calc f ≫ asrt s
          = (g ≫ comprMap s) ≫ (zetaMap s hs ≫ comprMap s) := by rw [hg, hζπs]
        _ = g ≫ (comprMap s ≫ zetaMap s hs) ≫ comprMap s := by
              simp only [Category.assoc]
        _ = g ≫ comprMap s := by rw [hπζs, Category.id_comp]
        _ = f := hg
    · intro habs
      refine (isImage_imPred f).2 s ?_
      conv_rhs => rw [← habs]
      rw [Category.assoc, (asrt_spec s).2]
  · constructor
    · intro hle
      have h1 : (f ≫ truth Y) ≼ orth (orth t) := by rwa [eabasics_orth_orth]
      obtain ⟨g, hg, -⟩ := hqζt.2 f h1
      calc asrt t ≫ f
          = (zetaMap t ht ≫ comprMap t) ≫ (zetaMap t ht ≫ g) := by rw [hζπt, hg]
        _ = zetaMap t ht ≫ (comprMap t ≫ zetaMap t ht) ≫ g := by
              simp only [Category.assoc]
        _ = zetaMap t ht ≫ g := by rw [hπζt, Category.id_comp]
        _ = f := hg
    · intro habs
      have h := comp_le_comp (asrt t) (pred_le_truth (f ≫ truth Y))
      rw [(asrt_spec t).2, ← Category.assoc, habs] at h
      exact h

end AndThen

/-- **211XVI** (eff.tex:5088, Definition): the subcategory `Pure C` of pure
maps of an &-effectus (objects wrapped; closure under composition is
211XI). -/
structure PureCat (C : Type u) : Type u where
  of ::
  base : C

/-- The category structure of `Pure C` (211XVI; identities are pure by
`quotient_basics_3`/`compr_basics_3`, and pure maps compose by
`upm_closed_pure`, cf. 211XI). -/
instance PureCat.category [AndThenEffectus C] : Category.{v} (PureCat C) where
  Hom X Y := { f : X.base ⟶ Y.base // IsPure f }
  id X := ⟨𝟙 X.base, X.base, 𝟙 X.base, 𝟙 X.base, 0, 1,
    quotient_basics_3 _, compr_basics_3 _, (Category.id_comp _).symm⟩
  comp f g := ⟨f.1 ≫ g.1, upm_closed_pure f.2 g.2⟩
  id_comp _ := Subtype.ext (by simp)
  comp_id _ := Subtype.ext (by simp)
  assoc _ _ _ := Subtype.ext (by simp)

section AndThenMore

variable [AndThenEffectus C] {X Y : C}

/-- **212I** (`zeta-asrt-quot`, eff.tex:5097, Lemma): in an &-effectus,
`ζ_{⌈p⌉} ∘ asrt_p` is a quotient for `pᵖ`. -/
theorem zeta_asrt_quot (p : Pred X) :
    IsQuotient (orth p)
      (asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p)) := sorry

/-- **212III** (`standard-form-map`, eff.tex:5119, Proposition): every map
`f` in an &-effectus factors as
`f = π_{im f} ∘ g ∘ ζ_{⌈1∘f⌉} ∘ asrt_{1∘f}` for a unique total and faithful
`g`. -/
theorem standard_form_map (f : X ⟶ Y) :
    ∃! g : comprObj (ceilPred (f ≫ truth Y)) ⟶ comprObj (imPred f),
      (IsTotal g ∧ FaithfulMap g) ∧
        f = asrt (f ≫ truth Y) ≫
          zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
          comprMap (imPred f) := sorry

/-- **212III.1** (`standard-form-map`, eff.tex:5128, Proposition): if `f`
is pure, the total faithful part `g` of its standard form is an
isomorphism. -/
theorem standard_form_map_pure {f : X ⟶ Y} (hf : IsPure f)
    (g : comprObj (ceilPred (f ≫ truth Y)) ⟶ comprObj (imPred f))
    (hg : f = asrt (f ≫ truth Y) ≫
      zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
      comprMap (imPred f)) : IsIso g := sorry

/-- **212III.2** (`standard-form-map`, eff.tex:5128, Proposition): a pure
faithful map (`im f = 1`) is a quotient. -/
theorem standard_form_map_quot {f : X ⟶ Y} (hf : IsPure f)
    (him : FaithfulMap f) : ∃ p : Pred X, IsQuotient p f := sorry

/-- **212III.3** (`standard-form-map`, eff.tex:5128, Proposition): a pure
total map is a comprehension. -/
theorem standard_form_map_compr {f : X ⟶ Y} (hf : IsPure f)
    (ht : IsTotal f) : ∃ q : Pred Y, IsComprehension q f := sorry

end AndThenMore

/-- **213I** (`andthen-effect-divisoid`, eff.tex:5184, Proposition): if `C`
is an &-effectus, then `(Scal C)ᵒᵖ` (scalars with reversed multiplication)
is an effect divisoid. -/
theorem andthen_effect_divisoid [AndThenEffectus C] :
    Nonempty (EffectDivisoid (Scal C)ᵐᵒᵖ) := sorry

section AndThenSharp

variable [AndThenEffectus C] {X Y Z : C}

/-- **213III** (`perp-sharp-is-orth`, eff.tex:5224, Lemma): in an
&-effectus, if `s ⊥ t` for sharp `s, t` then `s & t = 0 = t & s`. -/
theorem perp_sharp_is_orth {s t : Pred X} (hs : IsSharp s) (ht : IsSharp t)
    (h : Perp s t) : andThen s t = 0 ∧ andThen t s = 0 := by
  have key : ∀ {a : Pred X}, IsSharp a → asrt a ≫ orth a = 0 := by
    intro a ha
    have hss : asrt a ≫ a = a := (sharp_prop a).1.mp ha
    have hone : asrt a ≫ (1 : Pred X) = a := (asrt_spec a).2
    obtain ⟨h', e⟩ := FinPAC.ovee_comp (EffectAlgebra.perp_orth a) (asrt a)
    rw [EffectAlgebra.ovee_orth a, hone] at e
    have hperp : Perp a (asrt a ≫ orth a) := by
      have h'' := h'
      rwa [hss] at h''
    have hcong : ∀ {x y : Pred X} (hx : x = y) (hp : Perp x (asrt a ≫ orth a))
        (hq : Perp y (asrt a ≫ orth a)),
        ovee x (asrt a ≫ orth a) hp = ovee y (asrt a ≫ orth a) hq := by
      intro x y hx hp hq; subst hx; rfl
    have e2 : a = ovee a (asrt a ≫ orth a) hperp :=
      e.trans (hcong hss h' hperp)
    have ecomm : ovee (asrt a ≫ orth a) a (PCM.perp_comm hperp)
        = ovee (0 : Pred X) a (PCM.zero_perp a) := by
      rw [PCM.zero_ovee, ← PCM.ovee_comm]
      exact e2.symm
    exact eabasics_cancellation (PCM.perp_comm hperp) (PCM.zero_perp a) ecomm
  constructor
  · have hle := comp_le_comp (asrt s)
      (eabasics_perp_iff_le_orth.mp (PCM.perp_comm h))
    rw [key hs] at hle
    exact eq_zero_of_le_zero hle
  · have hle := comp_le_comp (asrt t) (eabasics_perp_iff_le_orth.mp h)
    rw [key ht] at hle
    exact eq_zero_of_le_zero hle

/-- **213V** (`simple-andthen-absorption`, eff.tex:5239, Exercise): for
sharp `s` and any predicate `p`: `p ≤ s ⟺ s & p = p`. -/
theorem simple_andthen_absorption {s p : Pred X} (hs : IsSharp s) :
    p ≼ s ↔ andThen s p = p := by
  have h := (asrt_absorp_rule p (isSharp_one (effObj C)) hs).2
  rwa [truth_effObj_eq_id, Category.comp_id] at h

/-- **213VI** (`exc-prod-sharp-maps`, eff.tex:5246, Exercise): a pairing
`⟨f, g⟩` is a sharp map iff both `f` and `g` are sharp maps. -/
theorem exc_prod_sharp_maps (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) :
    SharpMap (effPair f g h) ↔ SharpMap f ∧ SharpMap g := sorry

end AndThenSharp

end Theses.B.Eff
