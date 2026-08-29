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
* 208VII (the functor `X ↦ SPred X`, `f ↦ (f_⋄, f^□)` into `OMLatGal`) *is*
  formalized, as `diamond_omlatgal_functor`, on the category `OMLatGalCat`
  of orthomodular lattices and Galois pairs defined below; its data is
  207VI + 207III, as the Corollary says.
* Not separately formalized: the examples 206III/210III/211IV beyond
  `vNᵒᵖ` (`CvNᵒᵖ`, `EJAᵒᵖ`, `Set`; sharp maps = nmiu-maps) and the remarks
  211III/211IIIa on `assert` and polar decomposition.
-/
import Theses.B.Eff.Quotients

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits

namespace Theses.B.Eff

universe u v

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-! ## ⋄-effectuses (parsec 206) -/

/-- **206II** (`diamond-basics`, eff.tex:4413, Definition): a
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

/-- **206II** (`diamond-basics`, eff.tex:4427, Definition): the restriction
`f^⋄ : SPred Y → SPred X` of `f : X ⟶ Y` to sharp predicates,
`f^⋄(s) = ⌈s ∘ f⌉`. -/
noncomputable def diaPull (f : X ⟶ Y) (s : SPred Y) : SPred X :=
  ⟨ceilPred (f ≫ s.1), isSharp_ceil _⟩

/-- **206II** (`diamond-basics`, eff.tex:4432, Definition): the map
`f_⋄ : SPred X → SPred Y` of `f : X ⟶ Y`, `f_⋄(s) = im (f ∘ π_s)`. -/
noncomputable def diaPush (f : X ⟶ Y) (s : SPred X) : SPred Y :=
  ⟨imPred (comprMap s.1 ≫ f), _, _, isImage_imPred _⟩

/-- **206II** (`diamond-basics`, eff.tex:4456, Definition):
`f^□(s) = f^⋄(sᵖ)ᵖ`. -/
noncomputable def boxPull (f : X ⟶ Y) (s : SPred Y) : SPred X :=
  (diaPull f s.orth).orth

/-- **206II** (`diamond-basics`, eff.tex:4457, Definition):
`f_□(s) = f_⋄(sᵖ)ᵖ`. -/
noncomputable def boxPush (f : X ⟶ Y) (s : SPred X) : SPred Y :=
  (diaPush f s.orth).orth

/-- **206II.1** (`diamond-basics`, eff.tex:4436, Definition): maps
`f : X ⟶ Y` and `g : Y ⟶ X` are **⋄-adjoint** when `f^⋄ = g_⋄`. -/
def DiamondAdjoint (f : X ⟶ Y) (g : Y ⟶ X) : Prop :=
  diaPull f = diaPush g

/-- **206II.2** (`diamond-basics`, eff.tex:4441, Definition): an endomap is
**⋄-self-adjoint** when it is ⋄-adjoint to itself. -/
def DiamondSelfAdjoint (f : X ⟶ X) : Prop := DiamondAdjoint f f

/-- **206II.3** (`diamond-basics`, eff.tex:4445, Definition): maps
`f, g : X ⟶ Y` are **⋄-equivalent** when `f^⋄ = g^⋄` (equivalently
`f_⋄ = g_⋄`, 207VIIa). -/
def DiamondEquivalent (f g : X ⟶ Y) : Prop := diaPull f = diaPull g

/-- **206II.4** (`diamond-basics`, eff.tex:4451, Definition): a pure endomap
`f` is **⋄-positive** when `f = g ∘ g` for some ⋄-self-adjoint `g`. -/
def DiamondPositive (f : X ⟶ X) : Prop :=
  IsPure f ∧ ∃ g : X ⟶ X, DiamondSelfAdjoint g ∧ f = g ≫ g

end Diamond

-- **206III** (eff.tex:4460, Examples), `diamond_effectus_vn`: `vNᵒᵖ` is a
-- ⋄-effectus.  Moved to `Theses/B/Eff/VNExamples.lean` (author ruling
-- 2026-08-17): it needs thesis A's von Neumann theory, and this file must
-- keep importing only `Theses.Common`.

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

/-- The ceiling is the least sharp predicate above `p`: for sharp `q`,
`⌈p⌉ ≤ q` iff `p ≤ q`. -/
theorem ceil_le_iff_of_isSharp {X : C} {p q : Pred X} (hq : IsSharp q) :
    ceilPred p ≼ q ↔ p ≼ q := by
  refine ⟨fun h => pcm_preorder_trans (le_ceil p) h, fun h => ?_⟩
  have h2 := ceil_mono h
  rwa [ceil_of_isSharp hq] at h2

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

/-- `j` is the supremum of an **arbitrary** set `D ⊆ SPred X` of sharp
predicates within the poset `SPred` — the form in which the solution to
207V (`bsols.tex`:2966) states and proves the preservation clauses 2 and 4. -/
def SPred.IsSupSet (D : Set (SPred X)) (j : SPred X) : Prop :=
  (∀ d ∈ D, d.1 ≼ j.1) ∧ ∀ r : SPred X, (∀ d ∈ D, d.1 ≼ r.1) → j.1 ≼ r.1

/-- `m` is the infimum of an **arbitrary** set `D ⊆ SPred X` of sharp
predicates (`bsols.tex`:2966, clause 3). -/
def SPred.IsInfSet (D : Set (SPred X)) (m : SPred X) : Prop :=
  (∀ d ∈ D, m.1 ≼ d.1) ∧ ∀ r : SPred X, (∀ d ∈ D, r.1 ≼ d.1) → r.1 ≼ m.1

/-- The binary supremum of `SPred.IsSup` is the supremum of the two-element
set `{s, t}`. -/
theorem SPred.isSup_iff_isSupSet {s t j : SPred X} :
    SPred.IsSup s t j ↔ SPred.IsSupSet {s, t} j := by
  simp only [SPred.IsSup, SPred.IsSupSet, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, fun r hr => h3 r (hr s (Or.inl rfl)) (hr t (Or.inr rfl))⟩
    rintro d (rfl | rfl)
    exacts [h1, h2]
  · rintro ⟨hub, hlub⟩
    refine ⟨hub s (Or.inl rfl), hub t (Or.inr rfl), fun r h1 h2 => hlub r ?_⟩
    rintro d (rfl | rfl)
    exacts [h1, h2]

/-- The binary infimum of `SPred.IsInf` is the infimum of the two-element
set `{s, t}`. -/
theorem SPred.isInf_iff_isInfSet {s t m : SPred X} :
    SPred.IsInf s t m ↔ SPred.IsInfSet {s, t} m := by
  simp only [SPred.IsInf, SPred.IsInfSet, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, fun r hr => h3 r (hr s (Or.inl rfl)) (hr t (Or.inr rfl))⟩
    rintro d (rfl | rfl)
    exacts [h1, h2]
  · rintro ⟨hlb, hglb⟩
    refine ⟨hlb s (Or.inl rfl), hlb t (Or.inr rfl), fun r h1 h2 => hglb r ?_⟩
    rintro d (rfl | rfl)
    exacts [h1, h2]

/-- **207II** (`exc-diam-order-pres`, eff.tex:4470, Exercise): `f^⋄` and
`f^□` are order preserving. -/
theorem exc_diam_order_pres (f : X ⟶ Y) {s t : SPred Y} (h : s.1 ≼ t.1) :
    (diaPull f s).1 ≼ (diaPull f t).1 ∧
      (boxPull f s).1 ≼ (boxPull f t).1 := by
  refine ⟨ceil_mono (comp_le_comp f h), ?_⟩
  have h2 : orth t.1 ≼ orth s.1 := eabasics_le_iff_orth_le.mp h
  have h3 : ceilPred (f ≫ orth t.1) ≼ ceilPred (f ≫ orth s.1) :=
    ceil_mono (comp_le_comp f h2)
  exact eabasics_le_iff_orth_le.mp h3

/-- **207III** (`diamond-adjunction`, eff.tex:4474, Proposition): for
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

/-- **207III** (`diamond-adjunction`, eff.tex:4482, Proposition),
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

/-- **207V.1** (`order-adj-basics`, eff.tex:4510, Exercise): `f_⋄` is order
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

/-- Orthocomplementation turns the supremum of an arbitrary set of sharp
predicates into the infimum of the orthocomplemented set — the step
`(⋁D)ᵖ = ⋀_{d ∈ D} dᵖ` of `bsols.tex`:2966, clause 4. -/
theorem spred_isSupSet_orth {D : Set (SPred X)} {j : SPred X}
    (h : SPred.IsSupSet D j) :
    SPred.IsInfSet (SPred.orth '' D) j.orth := by
  obtain ⟨hub, hlub⟩ := h
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact eabasics_le_iff_orth_le.mp (hub d hd)
  · intro r hr
    refine le_orth_comm.mp (hlub r.orth ?_)
    intro d hd
    exact le_orth_comm.mp (hr _ ⟨d, hd, rfl⟩)

/-- Orthocomplementation turns the infimum of an arbitrary set of sharp
predicates into a supremum (`bsols.tex`:2966, clause 4). -/
theorem spred_isInfSet_orth {D : Set (SPred X)} {m : SPred X}
    (h : SPred.IsInfSet D m) :
    SPred.IsSupSet (SPred.orth '' D) m.orth := by
  obtain ⟨hlb, hglb⟩ := h
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact eabasics_le_iff_orth_le.mp (hlb d hd)
  · intro r hr
    have key : ∀ d ∈ D, (r.orth).1 ≼ d.1 := by
      intro d hd
      have hd' : orth d.1 ≼ r.1 := hr _ ⟨d, hd, rfl⟩
      have h1 := eabasics_le_iff_orth_le.mp hd'
      rwa [eabasics_orth_orth] at h1
    have h2' : orth r.1 ≼ m.1 := hglb r.orth key
    have h2 := eabasics_le_iff_orth_le.mp h2'
    show orth m.1 ≼ r.1
    rwa [eabasics_orth_orth] at h2

/-- Double orthocomplementation is the identity on sets of sharp
predicates. -/
theorem spred_orth_image_orth (D : Set (SPred X)) :
    SPred.orth '' (SPred.orth '' D) = D := by
  rw [Set.image_image]
  simp only [spred_orth_orth]
  exact Set.image_id' D

/-- **207V.2** (`order-adj-basics`, eff.tex:4510, Exercise): `f_⋄` preserves
suprema.  As at `bsols.tex`:2966, for an **arbitrary** set `D ⊆ SPred X`
with a supremum `j`, the map `f_⋄(j)` is the supremum of `f_⋄(D)`.  (The
binary case is `order_adj_basics_2` below.) -/
theorem order_adj_basics_2' (f : X ⟶ Y) {D : Set (SPred X)} {j : SPred X}
    (h : SPred.IsSupSet D j) :
    SPred.IsSupSet (diaPush f '' D) (diaPush f j) := by
  obtain ⟨hub, hlub⟩ := h
  constructor
  · -- `d ≤ j` gives `f_⋄(d) ≤ f_⋄(j)` by 207V.1
    rintro _ ⟨d, hd, rfl⟩
    exact order_adj_basics_1 f (hub d hd)
  · -- if `f_⋄(d) ≤ x` for all `d ∈ D` then `d ≤ f^□(x)`, so `j ≤ f^□(x)`
    intro x hx
    exact (diamond_adjunction' f j x).mpr
      (hlub (boxPull f x)
        (fun d hd => (diamond_adjunction' f d x).mp (hx _ ⟨d, hd, rfl⟩)))

/-- **207V.3** (`order-adj-basics`, eff.tex:4510, Exercise): `f^□` preserves
infima, for an **arbitrary** set `D ⊆ SPred Y` with an infimum
(`bsols.tex`:2966).  (The binary case is `order_adj_basics_3` below.) -/
theorem order_adj_basics_3' (f : X ⟶ Y) {D : Set (SPred Y)} {m : SPred Y}
    (h : SPred.IsInfSet D m) :
    SPred.IsInfSet (boxPull f '' D) (boxPull f m) := by
  obtain ⟨hlb, hglb⟩ := h
  constructor
  · -- `inf D ≤ d` gives `f^□(inf D) ≤ f^□(d)` by 207II
    rintro _ ⟨d, hd, rfl⟩
    exact (exc_diam_order_pres f (hlb d hd)).2
  · -- if `x ≤ f^□(d)` for all `d ∈ D` then `f_⋄(x) ≤ d`, so `f_⋄(x) ≤ inf D`
    intro x hx
    exact (diamond_adjunction' f x m).mp
      (hglb (diaPush f x)
        (fun d hd => (diamond_adjunction' f x d).mpr (hx _ ⟨d, hd, rfl⟩)))

/-- **207V.4** (`order-adj-basics`, eff.tex:4510, Exercise): `f^⋄` preserves
suprema, for an **arbitrary** set `D ⊆ SPred Y` with a supremum.  The proof
is `bsols.tex`:2966's derivation from clause 3 by orthocomplementation:
`f^⋄(⋁D) = f^□((⋁D)ᵖ)ᵖ = (⋀_{d} f^□(dᵖ))ᵖ = ⋁_d f^□(dᵖ)ᵖ = ⋁_d f^⋄(d)`.
(The binary case is `order_adj_basics_4` below.) -/
theorem order_adj_basics_4' (f : X ⟶ Y) {D : Set (SPred Y)} {j : SPred Y}
    (h : SPred.IsSupSet D j) :
    SPred.IsSupSet (diaPull f '' D) (diaPull f j) := by
  -- `(⋁D)ᵖ = ⋀_{d ∈ D} dᵖ`, and `f^□` preserves that infimum
  have h1 := order_adj_basics_3' f (spred_isSupSet_orth h)
  have e1 : boxPull f '' (SPred.orth '' D) = SPred.orth '' (diaPull f '' D) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr (fun s _ => boxPull_orth f s)
  rw [e1, boxPull_orth] at h1
  -- orthocomplement back
  have h2 := spred_isInfSet_orth h1
  rwa [spred_orth_image_orth, spred_orth_orth] at h2

/-- **207V.2** (`order-adj-basics`, eff.tex:4510, Exercise), binary case:
`f_⋄` preserves binary suprema.  (`bsols.tex`:2966's argument, specialised
to `D = {s, t}` through `order_adj_basics_2'`.) -/
theorem order_adj_basics_2 (f : X ⟶ Y) {s t j : SPred X}
    (h : SPred.IsSup s t j) :
    SPred.IsSup (diaPush f s) (diaPush f t) (diaPush f j) := by
  have hg := order_adj_basics_2' f (SPred.isSup_iff_isSupSet.mp h)
  rw [Set.image_pair] at hg
  exact SPred.isSup_iff_isSupSet.mpr hg

/-- **207V.3** (`order-adj-basics`, eff.tex:4510, Exercise), binary case:
`f^□` preserves binary infima. -/
theorem order_adj_basics_3 (f : X ⟶ Y) {s t m : SPred Y}
    (h : SPred.IsInf s t m) :
    SPred.IsInf (boxPull f s) (boxPull f t) (boxPull f m) := by
  have hg := order_adj_basics_3' f (SPred.isInf_iff_isInfSet.mp h)
  rw [Set.image_pair] at hg
  exact SPred.isInf_iff_isInfSet.mpr hg

/-- **207V.4** (`order-adj-basics`, eff.tex:4510, Exercise), binary case:
`f^⋄` preserves binary suprema. -/
theorem order_adj_basics_4 (f : X ⟶ Y) {s t j : SPred Y}
    (h : SPred.IsSup s t j) :
    SPred.IsSup (diaPull f s) (diaPull f t) (diaPull f j) := by
  have hg := order_adj_basics_4' f (SPred.isSup_iff_isSupSet.mp h)
  rw [Set.image_pair] at hg
  exact SPred.isSup_iff_isSupSet.mpr hg

/-- **207V.5** (`order-adj-basics`, eff.tex:4510, Exercise):
`f_⋄ ∘ f^□ ∘ f_⋄ = f_⋄`. -/
theorem order_adj_basics_5 (f : X ⟶ Y) (s : SPred X) :
    diaPush f (boxPull f (diaPush f s)) = diaPush f s :=
  Subtype.ext (eabasics_le_antisymm (diaPush_boxPull_le f (diaPush f s))
    (order_adj_basics_1 f (le_boxPull_diaPush f s)))

/-- **207V.6** (`order-adj-basics`, eff.tex:4510, Exercise):
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

/-- **207VI.1–2** (`diamond-functor`, eff.tex:4526, Lemma): `(–)^⋄` is
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

/-- **207VI.3–4** (`diamond-functor`, eff.tex:4526, Lemma): `(–)^□` is
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

/-- **207VI.5–6** (`diamond-functor`, eff.tex:4526, Lemma): `(–)_⋄` is
functorial: `(id)_⋄ = id` and `(f ∘ g)_⋄ = f_⋄ ∘ g_⋄`. -/
theorem diamond_functor_push :
    (∀ s : SPred X, diaPush (𝟙 X) s = s) ∧
      ∀ (g : X ⟶ Y) (f : Y ⟶ Z) (s : SPred X),
        diaPush (g ≫ f) s = diaPush f (diaPush g s) :=
  ⟨diaPush_id, diaPush_comp⟩

/-- **207VIIa** (`diamond-equiv-equiv`, eff.tex:4577, Exercise):
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

/-- **208I** (`image-sharp-is-order-sharp`, eff.tex:4584, Lemma): in a
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

/-- Helper: for a *sharp* `j`, a predicate `p` is below `j` exactly when `p`
vanishes on the comprehension for `jᵖ` (`im π_{jᵖ} = jᵖ`, 203IX + 202IV). -/
theorem le_iff_compr_orth_comp_eq_zero {X : C} {j : Pred X} (hj : IsSharp j)
    (p : Pred X) : p ≼ j ↔ comprMap (orth j) ≫ p = 0 := by
  constructor
  · intro hpj
    have h0 : comprMap (orth j) ≫ j = 0 := by
      have h := compr_basics_6 (isComprehension_comprMap (orth j))
      rwa [eabasics_orth_orth] at h
    have h1 := comp_le_comp (comprMap (orth j)) hpj
    rw [h0] at h1
    exact eq_zero_of_le_zero h1
  · intro h0
    have h1 : imPred (comprMap (orth j)) ≼ orth p := (im_le_orth_iff _ p).mpr h0
    rw [(img_of_compr (orth j)).2 _ (DiamondEffectus.orth_sharp hj)] at h1
    exact eabasics_le_iff_orth_le.mpr h1

/-- Helper: the predicates below a *sharp* `j` are closed under `⋁` — the
"partial sum" version of `le_sup`, and the step a general effect algebra
does not have.

Scaffolding of the route 208III used to take before 2026-08-22, kept as the
record of it: with `isSharp_ovee` and `diamond_oml` both back on eff.tex's
argument (177Ia and 177VI respectively) nothing appeals to it any more. -/
theorem ovee_le_of_le {X : C} {j : Pred X} (hj : IsSharp j) {s t : Pred X}
    (h : Perp s t) (hs : s ≼ j) (ht : t ≼ j) : ovee s t h ≼ j := by
  refine (le_iff_compr_orth_comp_eq_zero hj _).mpr ?_
  obtain ⟨h', e⟩ := FinPAC.ovee_comp h (comprMap (orth j))
  rw [e, PCM.ovee_congr ((le_iff_compr_orth_comp_eq_zero hj s).mp hs)
    ((le_iff_compr_orth_comp_eq_zero hj t).mp ht) h' (PCM.zero_perp 0),
    PCM.zero_ovee]

/-- Sharp predicates are closed under `⋁` (208III, "Sub-EA"): for orthogonal
sharp `s, t` the sum `s ⋁ t` is the supremum `s ∨ t`, which is sharp.

**This is now the thesis's own route.**  208III derives it from
`ea-modularity-prop` (177Ia): the join `s ∨ t = im [π_s, π_t]` exists by
204V (`lattice_compr`), orthogonal sharp predicates have `s ∧ t = 0`
(`isInf_zero_of_perp`), and 177Ia then gives `s ⋁ t = (s ∧ t) ⋁ (s ∨ t)
= s ∨ t` — that last step is `msc_cor16_1`, the master's thesis's Corollary
16.1, which `EffectAlgebras.lean` proves in the direction eff.tex now
prints (supremum hypothesised, infimum concluded).

Until 2026-08-21 this proof avoided modularity altogether, because 177Ia's
*first* printing hypothesised the infimum and concluded the supremum and in
that direction it is false (`WrightTriangle.not_ea_modularity_prop`);
eff.tex was corrected on 2026-08-14 and `ea_modularity_prop` now states the
corrected Proposition, so the detour is no longer needed.  (The avoided
argument, for the record: `s ∨ t ≤ s ⋁ t` since `s ⋁ t` is an upper bound,
and `s ⋁ t ≤ s ∨ t` since `s` and `t` both vanish on `π_{(s∨t)ᵖ}` — the
second half is `ovee_le_of_le`, which is still in the file but is no
longer appealed to anywhere.  The gap was recorded as **B4** in
`QUESTIONS.md`; it was settled on 2026-08-14 by the machine-checked
counterexample `WrightTriangle.not_ea_modularity_prop`, leaving only how to
amend the printed Proposition, and the entry was deleted on 2026-08-16 once
eff.tex had been corrected — commit f277d72.) -/
theorem isSharp_ovee {X : C} {s t : Pred X} (hs : IsSharp s) (ht : IsSharp t)
    (h : Perp s t) : IsSharp (ovee s t h) := by
  -- 204V: the join `s ∨ t` exists among all predicates, and is sharp
  obtain ⟨hsup, hjsharp⟩ := lattice_compr hs ht
  -- 177Ia at `s ∧ t = 0`: `s ⋁ t = s ∨ t`
  rw [← msc_cor16_1 h (isInf_zero_of_perp hs h) hsup]
  exact hjsharp

/-- **208III** (`diamond-oml`, eff.tex:4608, Proposition (Cho)), first half:
in a ⋄-effectus the sharp predicates form a sub-effect algebra of
`Pred X`. -/
theorem diamond_oml_subEA (X : C) :
    ∃ D : SubEffectAlgebra (Pred X),
      D.carrier = { p : Pred X | IsSharp p } :=
  ⟨⟨{ p : Pred X | IsSharp p }, dia_isSharp_zero X, isSharp_one X,
    fun h ha hb => isSharp_ovee ha hb h,
    fun ha => DiamondEffectus.orth_sharp ha⟩, rfl⟩

/-- Helper for 208III's "Sub-EA" step, in the form 177VI needs: the
*difference* of two sharp predicates is sharp.  If `s ⋁ d = t` with `s, t`
sharp, then `d = (s ⋁ tᵖ)ᵖ` is sharp too, so the algebraic order that
`SPred X` carries as a sub-effect algebra of `Pred X` is the order it
inherits as a subset. -/
theorem isSharp_of_ovee_eq {X : C} {s t d : Pred X} (hs : IsSharp s)
    (ht : IsSharp t) (hd : Perp s d) (he : ovee s d hd = t) : IsSharp d := by
  -- `d ⋁ tᵖ = sᵖ` (the computation of 175V.6), hence `s ⊥ tᵖ` and
  -- `(s ⋁ tᵖ) ⋁ d = s ⋁ (tᵖ ⋁ d) = s ⋁ sᵖ = 1`
  have hp : Perp (ovee s d hd) (orth (ovee s d hd)) := EffectAlgebra.perp_orth _
  have h1 : Perp d (orth (ovee s d hd)) := PCM.perp_of_ovee_perp hd hp
  have h2 : ovee d (orth (ovee s d hd)) h1 = orth s :=
    EffectAlgebra.orth_unique (PCM.perp_ovee_of_ovee_perp hd hp) (by
      rw [← PCM.ovee_assoc hd hp]; exact EffectAlgebra.ovee_orth _)
  subst he
  have hod : Perp (orth (ovee s d hd)) d := PCM.perp_comm h1
  have hinner : ovee (orth (ovee s d hd)) d hod = orth s :=
    (PCM.ovee_comm h1).symm.trans h2
  have hB : Perp s (ovee (orth (ovee s d hd)) d hod) := by
    rw [hinner]; exact EffectAlgebra.perp_orth s
  obtain ⟨hso, h', eq⟩ := PCM.assoc_left hod hB
  have eq1 : ovee (ovee s (orth (ovee s d hd)) hso) d h' = 1 := by
    rw [eq, PCM.ovee_congr rfl hinner hB (EffectAlgebra.perp_orth s)]
    exact EffectAlgebra.ovee_orth s
  rw [EffectAlgebra.orth_unique h' eq1]
  exact DiamondEffectus.orth_sharp (isSharp_ovee hs (DiamondEffectus.orth_sharp ht) hso)

/-- The effect algebra `SPred X` carries as a sub-effect algebra of `Pred X`
(`diamond_oml_subEA`): the structure 208III's proof means by "`SPred X` is a
sub-effect algebra of `Pred X`", spelled out so that 177VI
(`orth_ea_is_orthomodular`) can be applied to it.  Kept a `def` rather than
an `instance` so that `Perp`/`ovee` on `SPred X` are not silently
reinterpreted elsewhere in this file. -/
noncomputable def spredEffectAlgebra (X : C) : EffectAlgebra (SPred X) where
  zero := sZero X
  one := sOne X
  Perp s t := Perp s.1 t.1
  ovee s t h := ⟨ovee s.1 t.1 h, isSharp_ovee s.2 t.2 h⟩
  orth := SPred.orth
  perp_comm h := PCM.perp_comm h
  ovee_comm h := Subtype.ext (PCM.ovee_comm h)
  perp_of_ovee_perp hab h := PCM.perp_of_ovee_perp hab h
  perp_ovee_of_ovee_perp hab h := PCM.perp_ovee_of_ovee_perp hab h
  ovee_assoc hab h := Subtype.ext (PCM.ovee_assoc hab h)
  zero_perp s := PCM.zero_perp s.1
  zero_ovee s := Subtype.ext (PCM.zero_ovee s.1)
  perp_orth s := EffectAlgebra.perp_orth s.1
  ovee_orth s := Subtype.ext (EffectAlgebra.ovee_orth s.1)
  orth_unique h he := Subtype.ext (EffectAlgebra.orth_unique h (congrArg Subtype.val he))
  eq_zero_of_perp_one h := Subtype.ext (EffectAlgebra.eq_zero_of_perp_one h)

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

section DiamondOML

variable [DiamondEffectus C] {X Y Z : C}

/-- **208III** (`diamond-oml`, eff.tex:4608, Proposition (Cho)), second
half: `SPred X` is an orthomodular lattice (for the order inherited from
`Pred X`, with orthocomplement `sᵖ`).

This is eff.tex's own proof.  Point 50 ("Ortholattice"): the join is the one
204V (`lattice_compr`) already provides among *all* predicates,
`s ∨ t = im [π_s, π_t]`, which is sharp and hence also the join in
`SPred X`; the meet is `(sᵖ ∨ tᵖ)ᵖ`, because `(·)ᵖ` is an order
anti-automorphism of both posets (`spred_isSup_orth`); and `s ∧ sᵖ = 0`
because sharp predicates are order sharp (208I,
`image_sharp_is_order_sharp`), whence also `s ∨ sᵖ = 1`.  Point 40 then
appeals to 177VI: an effect algebra that is an ortholattice is orthomodular
(`orth_ea_is_orthomodular`), and `SPred X` is an effect algebra because it
is a sub-effect algebra of `Pred X` — the first half, `diamond_oml_subEA`,
here in the usable form `spredEffectAlgebra`. -/
theorem diamond_oml (X : C) :
    ∃ oml : OrthomodularLattice (SPred X), ∀ s t : SPred X,
      (letI := oml
       (s ≤ t ↔ s.1 ≼ t.1) ∧ sᶜ = s.orth) := by
  letI po : PartialOrder (SPred X) :=
    { le := fun s t => s.1 ≼ t.1
      le_refl := fun _ => pcm_preorder_refl _
      le_trans := fun _ _ _ h₁ h₂ => pcm_preorder_trans h₁ h₂
      le_antisymm := fun _ _ h₁ h₂ => Subtype.ext (eabasics_le_antisymm h₁ h₂) }
  -- 204V: `s ∨ t = im [π_s, π_t]` is a supremum among *all* predicates and is
  -- itself sharp, so it is the supremum of `s` and `t` in `SPred X` as well
  let J : SPred X → SPred X → SPred X := fun s t =>
    ⟨imPred (coprod.desc (comprMap s.1) (comprMap t.1)), (lattice_compr s.2 t.2).2⟩
  have hJ : ∀ s t : SPred X, SPred.IsSup s t (J s t) := fun s t =>
    ⟨(lattice_compr s.2 t.2).1.1, (lattice_compr s.2 t.2).1.2.1,
      fun r h₁ h₂ => (lattice_compr s.2 t.2).1.2.2 r.1 h₁ h₂⟩
  -- as `(·)ᵖ` is an order anti-automorphism, `(sᵖ ∨ tᵖ)ᵖ` is the infimum
  have hM : ∀ s t : SPred X, SPred.IsInf s t (J s.orth t.orth).orth := by
    intro s t
    have h := spred_isSup_orth (hJ s.orth t.orth)
    rwa [spred_orth_orth, spred_orth_orth] at h
  letI lat : Lattice (SPred X) :=
    { po with
      sup := J
      inf := fun s t => (J s.orth t.orth).orth
      le_sup_left := fun s t => (hJ s t).1
      le_sup_right := fun s t => (hJ s t).2.1
      sup_le := fun s t r h₁ h₂ => (hJ s t).2.2 r h₁ h₂
      inf_le_left := fun s t => (hM s t).1
      inf_le_right := fun s t => (hM s t).2.1
      le_inf := fun r s t h₁ h₂ => (hM s t).2.2 r h₁ h₂ }
  letI bo : BoundedOrder (SPred X) :=
    { top := sOne X
      bot := sZero X
      le_top := fun s => pred_le_truth s.1
      bot_le := fun s => zero_le_hom s.1 }
  letI cpl : Compl (SPred X) := ⟨SPred.orth⟩
  -- `a ∧ aᵖ = 0`, since sharp predicates are order sharp (208I)
  have hinf : ∀ a : SPred X, a ⊓ aᶜ = ⊥ := fun a =>
    Subtype.ext (image_sharp_is_order_sharp a.2 (hM a a.orth).1 (hM a a.orth).2.1)
  -- and consequently `a ∨ aᵖ = 1`
  have hsup : ∀ a : SPred X, a ⊔ aᶜ = ⊤ := by
    intro a
    have h : SPred.IsInf a.orth a (J a a.orth).orth := by
      have h0 := spred_isSup_orth (hJ a a.orth)
      rwa [spred_orth_orth] at h0
    have h0 : orth (J a a.orth).1 = 0 :=
      image_sharp_is_order_sharp a.2 h.2.1 h.1
    refine Subtype.ext ?_
    show (J a a.orth).1 = (1 : Pred X)
    have h1 := congrArg orth h0
    rwa [eabasics_orth_orth, eabasics_orth_zero] at h1
  letI ol : Ortholattice (SPred X) :=
    { lat, bo, cpl with
      inf_compl := hinf
      sup_compl := hsup
      compl_antitone := fun h => eabasics_le_iff_orth_le.mp h
      compl_compl := spred_orth_orth }
  -- `SPred X` is a sub-effect algebra of `Pred X` (the first half), and the
  -- algebraic order of that effect algebra is the inherited order, because a
  -- difference of sharp predicates is sharp
  letI ea : EffectAlgebra (SPred X) := spredEffectAlgebra X
  have hle : ∀ a b : SPred X, a ≤ b ↔ a ≼ b := by
    intro a b
    constructor
    · rintro ⟨d, hd, he⟩
      exact ⟨⟨d, isSharp_of_ovee_eq a.2 b.2 hd he⟩, hd, Subtype.ext he⟩
    · rintro ⟨d, hd, he⟩
      exact ⟨d.1, hd, congrArg Subtype.val he⟩
  -- 177VI: an effect algebra that is an ortholattice is orthomodular
  exact ⟨{ ol with
    orthomodular := orth_ea_is_orthomodular (SPred X) hle (fun _ => rfl) },
    fun s t => ⟨Iff.rfl, rfl⟩⟩

/-- **208VII** (eff.tex:4644, Corollary): in a ⋄-effectus the assignment
`X ↦ SPred X`, `f ↦ (f_⋄, f^□)` yields a functor to `OMLatGal`, the
category of orthomodular lattices with Galois connections (Jacobs).  Both
halves of the assignment are pinned: the object part on the nose, the
morphism part up to the transport of the object part (`HEq`, as the
carrier of `F.obj X` is only propositionally `SPred X`). -/
theorem diamond_omlatgal_functor :
    ∃ F : C ⥤ OMLatGalCat.{v},
      (∀ X : C, (F.obj X).carrier = SPred X) ∧
      ∀ (X Y : C) (f : X ⟶ Y),
        HEq (F.map f).push (diaPush f) ∧ HEq (F.map f).pull (boxPull f) := by
  classical
  -- choose the orthomodular structure of 208III on every `SPred X`
  have hex : ∀ X : C, ∃ oml : OrthomodularLattice (SPred X), ∀ s t : SPred X,
      (letI := oml
       (s ≤ t ↔ s.1 ≼ t.1) ∧ sᶜ = s.orth) := fun X => diamond_oml X
  choose oml homl using hex
  -- Galois pairs are determined by their two maps (the adjunction is a `Prop`)
  have gext : ∀ {A B : Type v} [OrthomodularLattice A] [OrthomodularLattice B]
      (u v : GaloisPair A B), u.push = v.push → u.pull = v.pull → u = v := by
    intro A B _ _ u v
    obtain ⟨p, q, -⟩ := u
    obtain ⟨p', q', -⟩ := v
    intro hp hq
    have hp' : p = p' := hp
    have hq' : q = q' := hq
    subst hp'
    subst hq'
    rfl
  refine ⟨{ obj := fun X => { carrier := SPred X, str := oml X }
            map := fun {X Y} f => ⟨diaPush f, boxPull f, fun a b => ?_⟩
            map_id := fun X => gext _ _ (funext diaPush_id) (funext boxPull_id)
            map_comp := fun f g => gext _ _ (funext fun s => diaPush_comp f g s)
              (funext fun t => boxPull_comp f g t) },
    fun X => rfl, fun X Y f => ⟨HEq.rfl, HEq.rfl⟩⟩
  -- the adjunction `f_⋄ ⊣ f^□` of 207III, transported along `homl`
  exact ((homl Y (diaPush f a) b).1).trans
    ((diamond_adjunction' f a b).trans ((homl X a (boxPull f b)).1).symm)

end DiamondOML

section DiamondBasics2

variable [DiamondEffectus C] {X Y Z : C}

theorem diaPush_one_val (f : X ⟶ Y) :
    (diaPush f (sOne X)).1 = imPred f :=
  (im_ineq f (comprMap (1 : Pred X))).2 _ (isIso_comprMap_one X)

/-- **208IX** (`spred-infimum`, eff.tex:4659, Lemma): for sharp `s, t` the
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

/-- **208XII** (`spred-sup`, eff.tex:4692, Exercise): for sharp `s, t` and a
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

/-- **209II.1** (`exc-diamond-adj`, eff.tex:4705, Exercise): `f^⋄ = g_⋄` iff
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

/-- **209II.2** (`exc-diamond-adj`, eff.tex:4705, Exercise): if `f` and `g`
are ⋄-adjoint, then `im f = ⌈1 ∘ g⌉`. -/
theorem exc_diamond_adj_2 {f : X ⟶ Y} {g : Y ⟶ X}
    (h : DiamondAdjoint f g) :
    imPred f = ceilPred (g ≫ truth X) := by
  have h' : diaPush f = diaPull g := (exc_diamond_adj_1 f g).mp h
  have h1 : imPred (comprMap (1 : Pred X) ≫ f) = ceilPred (g ≫ (1 : Pred X)) :=
    congrArg Subtype.val (congrFun h' ⟨1, isSharp_one X⟩)
  rw [(im_ineq f (comprMap (1 : Pred X))).2 _ (isIso_comprMap_one X)] at h1
  exact h1

/-- **209III.1** (`diamond-squares`, eff.tex:4718, Exercise): if `f` is
⋄-self-adjoint, then so is `f ∘ f`. -/
theorem diamond_squares_1 {f : X ⟶ X} (h : DiamondSelfAdjoint f) :
    DiamondSelfAdjoint (f ≫ f) := by
  have h' : diaPull f = diaPush f := h
  show diaPull (f ≫ f) = diaPush (f ≫ f)
  funext s
  rw [diaPull_comp, diaPush_comp, h']

/-- **209III.2** (`diamond-squares`, eff.tex:4718, Exercise): ⋄-positive
maps are ⋄-self-adjoint. -/
theorem diamond_squares_2 {f : X ⟶ X} (h : DiamondPositive f) :
    DiamondSelfAdjoint f := by
  obtain ⟨-, g, hg, rfl⟩ := h
  exact diamond_squares_1 hg

/-- **209III.3** (`diamond-squares`, eff.tex:4718, Exercise): if `f` is
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

/-- **209IV.1** (`iso-diamond-adjoint`, eff.tex:4733, Lemma): for an
isomorphism `α`, the predicate `s ∘ α` is sharp for sharp `s`. -/
theorem iso_diamond_adjoint_1 (α : X ⟶ Y) [IsIso α] {s : Pred Y}
    (hs : IsSharp s) : IsSharp (α ≫ s) :=
  ⟨comprObj s, comprMap s ≫ inv α, isImage_compr_comp_inv α hs⟩

/-- **209IV.2** (`iso-diamond-adjoint`, eff.tex:4733, Lemma): for an
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

/-- **210I** (`sharp-map`, eff.tex:4762, Definition): a map `f` in a
⋄-effectus is **sharp** when `s ∘ f` is sharp for every sharp `s`. -/
def SharpMap (f : X ⟶ Y) : Prop :=
  ∀ s : Pred Y, IsSharp s → IsSharp (f ≫ s)

/-- **210II** (`sharp-ceil`, eff.tex:4767, Exercise): `f` is sharp iff
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

/-! ### Helper lemmas for parsecs 211–212 -/

/-- Helper (implicit in 203IV.2, `floor_basics_2`): a comprehension for `p`
is also a comprehension for its own image `im π = ⌊p⌋`. -/
theorem isComprehension_imPred {W : C} {p : Pred X} {π : W ⟶ X}
    (h : IsComprehension p π) : IsComprehension (imPred π) π := by
  refine ⟨(isImage_imPred π).1, ?_⟩
  intro V g hg
  refine h.2 g ?_
  refine eabasics_le_antisymm (comp_le_comp g (pred_le_truth p)) ?_
  rw [← hg]
  exact comp_le_comp g ((isImage_imPred π).2 p h.1)

/-- Helper: precomposition with an epimorphism does not change the image
(the inequality `im (f ∘ ξ) ≤ im f` is 202V). -/
theorem imPred_comp_of_epi {W : C} (ξ : W ⟶ X) [Epi ξ] (f : X ⟶ Y) :
    imPred (ξ ≫ f) = imPred f := by
  refine eabasics_le_antisymm (im_ineq f ξ).1 ?_
  refine (isImage_imPred f).2 _ ?_
  refine (cancel_epi ξ).mp ?_
  rw [← Category.assoc, ← Category.assoc]
  exact (isImage_imPred (ξ ≫ f)).1

/-- Helper: a total quotient is an isomorphism (it is a quotient for `0`,
by 197V.5, and so differs from `id` by an iso, 197V.2/197V.3). -/
theorem isIso_of_isQuotient_isTotal {Q : C} {p : Pred X} {ξ : X ⟶ Q}
    (h : IsQuotient p ξ) (ht : IsTotal ξ) : IsIso ξ := by
  have hp : p = 0 := by
    have h5 := quotient_basics_5 h
    rw [ht] at h5
    have : orth p = 1 := h5.symm
    rw [← eabasics_orth_orth p, this, eabasics_orth_one]
  subst hp
  obtain ⟨θ, hθ, hcomm, -⟩ :=
    quotient_basics_2 (quotient_basics_3 (𝟙 X)) h
  haveI := hθ
  refine ⟨⟨θ, hcomm, ?_⟩⟩
  refine (cancel_mono θ).mp ?_
  rw [Category.assoc, hcomm, Category.comp_id, Category.id_comp]

/-- Helper: the identity is ⋄-positive (`id = id ∘ id` and `id^⋄ = id_⋄`). -/
theorem diamondPositive_id (X : C) : DiamondPositive (𝟙 X) := by
  refine ⟨⟨X, 𝟙 X, 𝟙 X, 0, 1, quotient_basics_3 _, compr_basics_3 _,
    (Category.id_comp _).symm⟩, 𝟙 X, ?_, (Category.id_comp _).symm⟩
  show diaPull (𝟙 X) = diaPush (𝟙 X)
  funext s
  rw [diaPull_id, diaPush_id]

/-- Helper: a comprehension with image `1` is an isomorphism (by the
previous helper it is a comprehension for `1`; cf. `isIso_comprMap_one`). -/
theorem isIso_of_isComprehension_faithful {W : C} {p : Pred X}
    {π : W ⟶ X} (h : IsComprehension p π) (him : imPred π = (1 : Pred X)) :
    IsIso π := by
  have h1 : IsComprehension (1 : Pred X) π := him ▸ isComprehension_imPred h
  obtain ⟨θ, hθ, hcomm, -⟩ := compr_basics_2 h1 (compr_basics_3 (𝟙 X))
  rw [Category.comp_id] at hcomm
  rw [← hcomm]; exact hθ

end DiamondBasics2

/-! ## &-effectuses (parsec 211) -/

/-- **211II** (eff.tex:4792, Definition): an **&-effectus** ("andthen
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

/-- **211II** (eff.tex:4801, Definition): the **assert map**
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

/-- Helper (first line of the proof of 211V): `im asrt_p = ⌈1 ∘ asrt_p⌉ = ⌈p⌉`,
because ⋄-positive maps are ⋄-self-adjoint. -/
theorem imPred_asrt (p : Pred X) : imPred (asrt p) = ceilPred p := by
  have h := exc_diamond_adj_2 (diamond_squares_2 (asrt_spec p).1)
  rwa [(asrt_spec p).2] at h

/-- Helper (used repeatedly in 211V–212I): `⌈p⌉ ∘ asrt_p = 1 ∘ asrt_p = p`. -/
theorem asrt_comp_ceil (p : Pred X) : asrt p ≫ ceilPred p = p := by
  have h := (isImage_imPred (asrt p)).1
  rw [imPred_asrt p, (asrt_spec p).2] at h
  exact h

/-- Helper: `im id = 1`. -/
theorem imPred_id (X : C) : imPred (𝟙 X) = (1 : Pred X) := by
  have h := (isImage_imPred (𝟙 X)).1
  rw [Category.id_comp, Category.id_comp] at h
  exact h

/-- Helper: quotients are pure (201II, taking the comprehension to be `id`). -/
theorem isPure_of_isQuotient {Q : C} {q : Pred X} {ξ : X ⟶ Q}
    (h : IsQuotient q ξ) : IsPure ξ :=
  ⟨Q, ξ, 𝟙 Q, q, 1, h, compr_basics_3 (𝟙 Q), (Category.comp_id _).symm⟩

/-- **211II** (eff.tex:4813, Definition): the sequential conjunction
`p & q = q ∘ asrt_p` ("`p` andthen `q`"); `p² = p & p`. -/
noncomputable def andThen (p q : Pred X) : Pred X := asrt p ≫ q

-- **211IV** (`vn-is-andthen-eff`, eff.tex:4859, Examples),
-- `vn_is_andthen_eff`: `vNᵒᵖ` is an &-effectus, with `asrt_a(b) = √a b √a`.
-- Moved to `Theses/B/Eff/VNExamples.lean` (author ruling 2026-08-17): it
-- needs thesis A's von Neumann theory, and this file must keep importing
-- only `Theses.Common`.

/-- **211V** (`sharp-prop`, eff.tex:4872, Proposition): for a predicate `p`
in an &-effectus the following are equivalent: (1) `p` is sharp;
(2) `p & p = p`; (3) `asrt_p ∘ asrt_p = asrt_p`. -/
theorem sharp_prop (p : Pred X) :
    (IsSharp p ↔ andThen p p = p) ∧
      (IsSharp p ↔ asrt p ≫ asrt p = asrt p) := by
  -- `asrt_p` is ⋄-positive, hence ⋄-self-adjoint, so `im asrt_p = ⌈1 ∘ asrt_p⌉ = ⌈p⌉`
  have hsa : DiamondSelfAdjoint (asrt p) := diamond_squares_2 (asrt_spec p).1
  have him : imPred (asrt p) = ceilPred p := imPred_asrt p
  -- (1) ⟹ (2): if `p` is sharp then `im asrt_p = p`, so `p & p = 1 ∘ asrt_p = p`
  have h12 : IsSharp p → andThen p p = p := by
    intro hp
    have himp : imPred (asrt p) = p := by rw [him, ceil_of_isSharp hp]
    have h := (isImage_imPred (asrt p)).1
    rw [himp, (asrt_spec p).2] at h
    exact h
  -- (2) ⟹ (1)
  have h21 : andThen p p = p → IsSharp p := by
    intro hpp
    replace hpp : asrt p ≫ p = p := hpp
    -- `⌈p⌉ ∘ asrt_p = 1 ∘ asrt_p = p`
    have hcp : asrt p ≫ ceilPred p = p := by
      have h := (isImage_imPred (asrt p)).1
      rw [him, (asrt_spec p).2] at h
      exact h
    -- write `⌈p⌉ = p ⋁ d` with `d = ⌈p⌉ ⊖ p`
    obtain ⟨d, hd, hsum⟩ := le_ceil p
    -- `p & d = 0`
    have hd0 : asrt p ≫ d = 0 := by
      obtain ⟨hp', hovee⟩ := FinPAC.ovee_comp hd (asrt p)
      have hkey : ovee (asrt p ≫ p) (asrt p ≫ d) hp' = asrt p ≫ p := by
        rw [← hovee, hsum, hcp, hpp]
      refine (eabasics_cancellation (c := asrt p ≫ p) (PCM.perp_comm hp')
        (PCM.zero_perp _) ?_)
      rw [PCM.zero_ovee, ← PCM.ovee_comm]
      exact hkey
    -- hence `d ≤ im^⊥ asrt_p = ⌈p⌉ᵖ`, while also `d ≤ ⌈p⌉`
    have hdle : d ≼ orth (ceilPred p) := by
      have h := (im_le_orth_iff (asrt p) d).mpr hd0
      rw [him] at h
      exact le_orth_comm.mp h
    have hd2 : d ≼ ceilPred p :=
      ⟨p, PCM.perp_comm hd, by rw [← PCM.ovee_comm]; exact hsum⟩
    have hdz : d = 0 := image_sharp_is_order_sharp (isSharp_ceil p) hd2 hdle
    -- so `⌈p⌉ = p ⋁ 0 = p`, and `⌈p⌉` is sharp
    subst hdz
    rw [PCM.ovee_zero] at hsum
    rw [hsum]
    exact isSharp_ceil p
  -- (3) ⟹ (2)
  have h32 : asrt p ≫ asrt p = asrt p → andThen p p = p := by
    intro h
    show asrt p ≫ p = p
    calc asrt p ≫ p = asrt p ≫ (asrt p ≫ truth X) := by rw [(asrt_spec p).2]
      _ = (asrt p ≫ asrt p) ≫ truth X := (Category.assoc _ _ _).symm
      _ = asrt p ≫ truth X := by rw [h]
      _ = p := (asrt_spec p).2
  -- (1) ⟹ (3): the main argument
  have h13 : IsSharp p → asrt p ≫ asrt p = asrt p := by
    intro hp
    have hpp : asrt p ≫ p = p := h12 hp
    -- `asrt_p = π ∘ ξ` with `ξ` a quotient and `π` a comprehension
    obtain ⟨Q, ξ, π, p₀, q₀, hξ, hπ, hasrt⟩ := (asrt_spec p).1.1
    haveI hepi : Epi ξ := quotient_basics_6 hξ
    have hπt : IsTotal π := compr_total hπ
    have hξ1 : ξ ≫ truth Q = p := by
      have h := (asrt_spec p).2
      rw [hasrt, Category.assoc, hπt] at h
      exact h
    -- `ξ ∘ π` is pure by the &-effectus axiom: `ξ ∘ π = π' ∘ ξ'`
    obtain ⟨W, ξ', π', p₁, q₁, hξ', hπ', hcomp⟩ :=
      AndThenEffectus.quot_after_compr_pure π ξ hπ hξ
    have hπ't : IsTotal π' := compr_total hπ'
    -- `1 ∘ ξ' = 1`, so `ξ'` is an iso
    have hξ'tot : IsTotal ξ' := by
      refine (cancel_epi ξ).mp ?_
      calc ξ ≫ (ξ' ≫ truth W)
          = ξ ≫ ξ' ≫ (π' ≫ truth Q) := by rw [hπ't]
        _ = ξ ≫ (ξ' ≫ π') ≫ truth Q := by simp only [Category.assoc]
        _ = ξ ≫ (π ≫ ξ) ≫ truth Q := by rw [hcomp]
        _ = (ξ ≫ π) ≫ (ξ ≫ truth Q) := by simp only [Category.assoc]
        _ = asrt p ≫ p := by rw [← hasrt, hξ1]
        _ = p := hpp
        _ = ξ ≫ truth Q := hξ1.symm
    haveI hiso' : IsIso ξ' := isIso_of_isQuotient_isTotal hξ' hξ'tot
    -- `im π = im asrt_p = ⌈p⌉ = p`
    have himπ : imPred π = p := by
      have h1 : imPred (ξ ≫ π) = imPred π := imPred_comp_of_epi ξ π
      rw [← hasrt] at h1
      rw [← h1, him, ceil_of_isSharp hp]
    -- `(im π') ∘ ξ = 1 ∘ ξ`, so `im π' = 1` and `π'` is an iso
    have himπ' : imPred π' = (1 : Pred Q) := by
      have key : π ≫ (ξ ≫ imPred π') = π ≫ truth X := by
        calc π ≫ (ξ ≫ imPred π')
            = (ξ' ≫ π') ≫ imPred π' := by rw [← Category.assoc, hcomp]
          _ = ξ' ≫ (π' ≫ truth Q) := by
                rw [Category.assoc, (isImage_imPred π').1]
          _ = truth Q := by rw [hπ't]; exact hξ'tot
          _ = π ≫ truth X := hπt.symm
      have hge : imPred π ≼ ξ ≫ imPred π' := (isImage_imPred π).2 _ key
      rw [himπ] at hge
      have hle : (ξ ≫ imPred π') ≼ p := by
        rw [← hξ1]; exact comp_le_comp ξ (pred_le_truth _)
      have heq : ξ ≫ imPred π' = ξ ≫ truth Q := by
        rw [hξ1]; exact eabasics_le_antisymm hle hge
      have hz : ξ ≫ orth (imPred π') = 0 :=
        (comp_orth_eq_zero_iff ξ (imPred π')).mpr heq
      have h0 : orth (imPred π') = 0 :=
        (faithfulMap_iff ξ).mp (exc_quot_faithful hξ) _ hz
      rw [← eabasics_orth_orth (imPred π'), h0, eabasics_orth_zero]
    haveI hisoπ' : IsIso π' := isIso_of_isComprehension_faithful hπ' himπ'
    -- `asrt_p ∘ asrt_p = (π ∘ π') ∘ (ξ' ∘ ξ)` is pure, hence ⋄-positive
    have hpure : IsPure (asrt p ≫ asrt p) := by
      refine ⟨W, ξ ≫ ξ', π' ≫ π, p₀, q₀, quotient_basics_1 hξ ξ',
        compr_basics_1 hπ π', ?_⟩
      rw [hasrt]
      calc (ξ ≫ π) ≫ (ξ ≫ π)
          = ξ ≫ (π ≫ ξ) ≫ π := by simp only [Category.assoc]
        _ = ξ ≫ (ξ' ≫ π') ≫ π := by rw [hcomp]
        _ = (ξ ≫ ξ') ≫ (π' ≫ π) := by simp only [Category.assoc]
    have hpos : DiamondPositive (asrt p ≫ asrt p) :=
      diamond_squares_3 (asrt_spec p).1 hpure
    refine asrt_unique p _ hpos ?_
    rw [Category.assoc, (asrt_spec p).2]
    exact hpp
  exact ⟨⟨h12, h21⟩, ⟨h13, fun h => h21 (h32 h)⟩⟩

/-- **211VII** (`prop-corr-zeta-pi`, eff.tex:4934, Proposition), first
part: for sharp `s` there are a comprehension `π_s` for `s` and a quotient
`ζ_s` for `sᵖ` with `ζ_s ∘ π_s = id` and `π_s ∘ ζ_s = asrt_s`. -/
theorem prop_corr_zeta_pi {s : Pred X} (hs : IsSharp s) :
    ∃ (W : C) (π : W ⟶ X) (ζ : X ⟶ W),
      IsComprehension s π ∧ IsQuotient (orth s) ζ ∧
        π ≫ ζ = 𝟙 W ∧ ζ ≫ π = asrt s := by
  -- ⋄-positive maps are pure: `asrt_s = π ∘ ξ`
  obtain ⟨Q, ξ, π, p₀, q₀, hξ, hπ, hasrt⟩ := (asrt_spec s).1.1
  haveI hepi : Epi ξ := quotient_basics_6 hξ
  haveI hmono : Mono π := compr_basics_5 hπ
  have hπt : IsTotal π := compr_total hπ
  have hidem : asrt s ≫ asrt s = asrt s := (sharp_prop s).2.mp hs
  -- `ξ ∘ π = id`, because `π ∘ ξ = asrt_s = asrt_s ∘ asrt_s = π ∘ ξ ∘ π ∘ ξ`
  have hπξ : π ≫ ξ = 𝟙 Q := by
    refine (cancel_mono π).mp ?_
    refine (cancel_epi ξ).mp ?_
    calc ξ ≫ ((π ≫ ξ) ≫ π) = (ξ ≫ π) ≫ (ξ ≫ π) := by simp only [Category.assoc]
      _ = ξ ≫ π := by rw [← hasrt, hidem]
      _ = ξ ≫ (𝟙 Q ≫ π) := by rw [Category.id_comp]
  -- `1 ∘ ξ = 1 ∘ asrt_s = s`, so `ξ` is a quotient for `sᵖ`
  have hξ1 : ξ ≫ truth Q = s := by
    have h := (asrt_spec s).2
    rw [hasrt, Category.assoc, hπt] at h
    exact h
  have hp₀ : p₀ = orth s := by
    have h := quotient_basics_5 hξ
    rw [hξ1] at h
    rw [← eabasics_orth_orth p₀, ← h]
  -- `im π = (asrt_s)_⋄(im π) = (asrt_s)^⋄(im π) = ⌈1 ∘ ξ⌉ = s`
  have hsharpim : IsSharp (imPred π) := ⟨_, _, isImage_imPred π⟩
  have hπasrt : π ≫ asrt s = π := by
    rw [hasrt, ← Category.assoc, hπξ, Category.id_comp]
  obtain ⟨θ, hθ, hθc, -⟩ :=
    compr_basics_2 (isComprehension_imPred hπ)
      (isComprehension_comprMap (imPred π))
  haveI := hθ
  have e1 : imPred (comprMap (imPred π) ≫ asrt s) = imPred π := by
    have h := imPred_comp_of_epi θ (comprMap (imPred π) ≫ asrt s)
    rw [← Category.assoc, hθc, hπasrt] at h
    exact h.symm
  have e2 : asrt s ≫ imPred π = s := by
    calc asrt s ≫ imPred π = ξ ≫ (π ≫ imPred π) := by
          rw [hasrt, Category.assoc]
      _ = ξ ≫ (π ≫ truth X) := by rw [(isImage_imPred π).1]
      _ = ξ ≫ truth Q := by rw [hπt]
      _ = s := hξ1
  have himπ : imPred π = s := by
    have hsa : DiamondSelfAdjoint (asrt s) := diamond_squares_2 (asrt_spec s).1
    have h : (diaPull (asrt s) ⟨imPred π, hsharpim⟩).1
        = (diaPush (asrt s) ⟨imPred π, hsharpim⟩).1 :=
      congrArg Subtype.val (congrFun hsa ⟨imPred π, hsharpim⟩)
    show imPred π = s
    have hl : (diaPull (asrt s) ⟨imPred π, hsharpim⟩).1 = s := by
      show ceilPred (asrt s ≫ imPred π) = s
      rw [e2, ceil_of_isSharp hs]
    have hr : (diaPush (asrt s) ⟨imPred π, hsharpim⟩).1 = imPred π := e1
    rw [hl, hr] at h
    exact h.symm
  exact ⟨Q, π, ξ, himπ ▸ isComprehension_imPred hπ, hp₀ ▸ hξ, hπξ, hasrt.symm⟩

/-- **211VII** (`prop-corr-zeta-pi`, eff.tex:4943, Proposition), second
part (with the uniqueness of 211IX): for *every* comprehension `π` for a
sharp `s` there is a unique quotient `ζ` for `sᵖ` with `ζ ∘ π = id` and
`π ∘ ζ = asrt_s`. -/
theorem prop_corr_zeta_pi_compr {s : Pred X} (hs : IsSharp s) {W : C}
    {π : W ⟶ X} (hπ : IsComprehension s π) :
    ∃! ζ : X ⟶ W,
      IsQuotient (orth s) ζ ∧ π ≫ ζ = 𝟙 W ∧ ζ ≫ π = asrt s := by
  obtain ⟨W₀, π₀, ζ₀, hπ₀, hζ₀, h1, h2⟩ := prop_corr_zeta_pi hs
  obtain ⟨θ, hθ, hθc, -⟩ := compr_basics_2 hπ hπ₀
  haveI := hθ
  haveI hmono : Mono π := compr_basics_5 hπ
  have hA : π ≫ (ζ₀ ≫ inv θ) = 𝟙 W := by
    have e : π ≫ (ζ₀ ≫ inv θ) = θ ≫ ((π₀ ≫ ζ₀) ≫ inv θ) := by
      rw [← hθc]; simp only [Category.assoc]
    rw [e, h1, Category.id_comp, IsIso.hom_inv_id]
  have hB : (ζ₀ ≫ inv θ) ≫ π = asrt s := by
    have e : (ζ₀ ≫ inv θ) ≫ π = (ζ₀ ≫ (inv θ ≫ θ)) ≫ π₀ := by
      rw [← hθc]; simp only [Category.assoc]
    rw [e, IsIso.inv_hom_id, Category.comp_id, h2]
  refine ⟨ζ₀ ≫ inv θ, ⟨quotient_basics_1 hζ₀ (inv θ), hA, hB⟩, ?_⟩
  rintro ζ' ⟨-, -, hζ'⟩
  exact (cancel_mono π).mp (by rw [hζ', hB])

/-- **211VII** (`prop-corr-zeta-pi`, eff.tex:4946, Proposition), third
part: conversely, for every quotient `ζ` for `sᵖ` (`s` sharp) there is a
comprehension `π` for `s` with `ζ ∘ π = id` and `π ∘ ζ = asrt_s`. -/
theorem prop_corr_zeta_pi_quot {s : Pred X} (hs : IsSharp s) {W : C}
    {ζ : X ⟶ W} (hζ : IsQuotient (orth s) ζ) :
    ∃ π : W ⟶ X,
      IsComprehension s π ∧ π ≫ ζ = 𝟙 W ∧ ζ ≫ π = asrt s := by
  obtain ⟨W₀, π₀, ζ₀, hπ₀, hζ₀, h1, h2⟩ := prop_corr_zeta_pi hs
  obtain ⟨θ, hθ, hθc, -⟩ := quotient_basics_2 hζ₀ hζ
  haveI := hθ
  -- `hθc : ζ ≫ θ = ζ₀`, so `ζ = ζ₀ ∘ θ⁻¹`
  have hζeq : ζ₀ ≫ inv θ = ζ := by
    rw [← hθc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine ⟨θ ≫ π₀, compr_basics_1 hπ₀ θ, ?_, ?_⟩
  · have e : (θ ≫ π₀) ≫ ζ = θ ≫ ((π₀ ≫ ζ₀) ≫ inv θ) := by
      rw [← hζeq]; simp only [Category.assoc]
    rw [e, h1, Category.id_comp, IsIso.hom_inv_id]
  · have e : ζ ≫ (θ ≫ π₀) = (ζ₀ ≫ (inv θ ≫ θ)) ≫ π₀ := by
      rw [← hζeq]; simp only [Category.assoc]
    rw [e, IsIso.inv_hom_id, Category.comp_id, h2]

/-- **211IX** (`zeta-s-convention`, eff.tex:4985, Notation): the
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

/-- **211XI** (`upm-closed`, eff.tex:5003, Proposition), first half: in an
&-effectus comprehensions are closed under composition. -/
theorem upm_closed_compr {p : Pred Y} {q : Pred Z} {π₁ : X ⟶ Y}
    {π₂ : Y ⟶ Z} (h₁ : IsComprehension p π₁) (h₂ : IsComprehension q π₂) :
    ∃ r : Pred Z, IsComprehension r (π₁ ≫ π₂) := by
  -- `π₂ ∘ π₁` is a comprehension for `im (π₂ ∘ π₁)`; write `s = im π₁`,
  -- `t = im π₂`
  refine ⟨imPred (π₁ ≫ π₂), (isImage_imPred (π₁ ≫ π₂)).1, ?_⟩
  intro V f hf
  have hs : IsComprehension (imPred π₁) π₁ := isComprehension_imPred h₁
  have ht : IsComprehension (imPred π₂) π₂ := isComprehension_imPred h₂
  have htsharp : IsSharp (imPred π₂) := ⟨_, _, isImage_imPred π₂⟩
  have hπ₂t : IsTotal π₂ := compr_total h₂
  haveI : Mono π₁ := compr_basics_5 h₁
  haveI : Mono π₂ := compr_basics_5 h₂
  haveI hmono : Mono (π₁ ≫ π₂) := mono_comp _ _
  -- the corresponding quotient `ζ₂` of `π₂`, with `ζ₂ ∘ π₂ = id`
  obtain ⟨ζ₂, ⟨-, hπζ₂, -⟩, -⟩ := prop_corr_zeta_pi_compr htsharp ht
  -- `im (π₂ ∘ π₁) ≤ im π₂`, so `f` factors as `f = π₂ ∘ g₂`
  have hrt : imPred (π₁ ≫ π₂) ≼ imPred π₂ := (im_ineq π₂ π₁).1
  have hft : f ≫ imPred π₂ = f ≫ truth Z := by
    refine eabasics_le_antisymm (comp_le_comp f (pred_le_truth _)) ?_
    rw [← hf]
    exact comp_le_comp f hrt
  obtain ⟨g₂, hg₂, -⟩ := ht.2 f hft
  -- `s ∘ ζ₂ ≥ im (π₂ ∘ π₁)`
  have hkey : imPred (π₁ ≫ π₂) ≼ ζ₂ ≫ imPred π₁ := by
    refine (isImage_imPred (π₁ ≫ π₂)).2 _ ?_
    have e : (π₁ ≫ π₂) ≫ (ζ₂ ≫ imPred π₁) = (π₁ ≫ (π₂ ≫ ζ₂)) ≫ imPred π₁ := by
      simp only [Category.assoc]
    rw [e, hπζ₂, Category.comp_id, (isImage_imPred π₁).1, Category.assoc, hπ₂t]
  -- hence `s ∘ g₂ = 1 ∘ g₂`, so `g₂` factors through `π₁`
  have hg₂s : g₂ ≫ imPred π₁ = g₂ ≫ truth Y := by
    refine eabasics_le_antisymm (comp_le_comp g₂ (pred_le_truth _)) ?_
    have e1 : g₂ ≫ imPred π₁ = f ≫ (ζ₂ ≫ imPred π₁) := by
      rw [← hg₂]
      have e : (g₂ ≫ π₂) ≫ (ζ₂ ≫ imPred π₁)
          = (g₂ ≫ (π₂ ≫ ζ₂)) ≫ imPred π₁ := by simp only [Category.assoc]
      rw [e, hπζ₂, Category.comp_id]
    have e2 : g₂ ≫ truth Y = f ≫ imPred (π₁ ≫ π₂) := by
      rw [hf, ← hg₂, Category.assoc, hπ₂t]
    rw [e1, e2]
    exact comp_le_comp f hkey
  obtain ⟨g₁, hg₁, -⟩ := hs.2 g₂ hg₂s
  refine ⟨g₁, ?_, ?_⟩
  · show g₁ ≫ (π₁ ≫ π₂) = f
    rw [← Category.assoc, hg₁, hg₂]
  · intro g' hg'
    replace hg' : g' ≫ (π₁ ≫ π₂) = f := hg'
    refine (cancel_mono (π₁ ≫ π₂)).mp ?_
    rw [hg', ← Category.assoc, hg₁, hg₂]

/-- **211XI** (`upm-closed`, eff.tex:5003, Proposition), second half: in an
&-effectus pure maps are closed under composition. -/
theorem upm_closed_pure {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsPure f) (hg : IsPure g) : IsPure (f ≫ g) := by
  -- `f = π₁ ∘ ξ₁` and `g = π₂ ∘ ξ₂`
  obtain ⟨Q₁, ξ₁, π₁, p₁, q₁, hξ₁, hπ₁, rfl⟩ := hf
  obtain ⟨Q₂, ξ₂, π₂, p₂, q₂, hξ₂, hπ₂, rfl⟩ := hg
  -- `ξ₂ ∘ π₁` is pure by the &-effectus axiom: `ξ₂ ∘ π₁ = π' ∘ ξ'`
  obtain ⟨W, ξ', π', p', q', hξ', hπ', hcomp⟩ :=
    AndThenEffectus.quot_after_compr_pure π₁ ξ₂ hπ₁ hξ₂
  -- `π₂ ∘ π'` is a comprehension (211XI, first half) and `ξ' ∘ ξ₁` a quotient
  -- (197IX)
  obtain ⟨r, hr⟩ := upm_closed_compr hπ' hπ₂
  have hq₁ : IsQuotient (orth (orth p₁)) ξ₁ := by rwa [eabasics_orth_orth]
  have hq' : IsQuotient (orth (orth p')) ξ' := by rwa [eabasics_orth_orth]
  refine ⟨W, ξ₁ ≫ ξ', π' ≫ π₂, _, r, quotients_composition hq₁ hq', hr, ?_⟩
  calc (ξ₁ ≫ π₁) ≫ (ξ₂ ≫ π₂) = ξ₁ ≫ ((π₁ ≫ ξ₂) ≫ π₂) := by
        simp only [Category.assoc]
    _ = ξ₁ ≫ ((ξ' ≫ π') ≫ π₂) := by rw [hcomp]
    _ = (ξ₁ ≫ ξ') ≫ (π' ≫ π₂) := by simp only [Category.assoc]

/-- **211XIV** (`andthen-square-rule`, eff.tex:5058, Exercise):
`asrt_p ∘ asrt_p = asrt_{p & p}`. -/
theorem andthen_square_rule (p : Pred X) :
    asrt p ≫ asrt p = asrt (andThen p p) := by
  refine asrt_unique _ _ ?_ ?_
  · exact diamond_squares_3 (asrt_spec p).1
      (upm_closed_pure (asrt_spec p).1.1 (asrt_spec p).1.1)
  · rw [Category.assoc, (asrt_spec p).2]
    rfl

/-- **211XV** (`asrt-absorp-rule`, eff.tex:5062, Exercise): for sharp `s`
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

/-- **211XVI** (eff.tex:5071, Definition): the subcategory `Pure C` of pure
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

/-- **212I** (`zeta-asrt-quot`, eff.tex:5080, Lemma): in an &-effectus,
`ζ_{⌈p⌉} ∘ asrt_p` is a quotient for `pᵖ`. -/
theorem zeta_asrt_quot (p : Pred X) :
    IsQuotient (orth p)
      (asrt p ≫ zetaMap (ceilPred p) (isSharp_ceil p)) := by
  obtain ⟨hqζ, hπζ, hζπ⟩ := zetaMap_spec (ceilPred p) (isSharp_ceil p)
  set ζ := zetaMap (ceilPred p) (isSharp_ceil p) with hζdef
  -- `1 ∘ ζ_{⌈p⌉} ∘ asrt_p = ⌈p⌉ ∘ asrt_p = p`
  have hζ1 : ζ ≫ truth (comprObj (ceilPred p)) = ceilPred p := by
    rw [quotient_basics_5 hqζ, eabasics_orth_orth]
  have htot : (asrt p ≫ ζ) ≫ truth (comprObj (ceilPred p)) = p := by
    rw [Category.assoc, hζ1]
    exact asrt_comp_ceil p
  -- `im (ζ_{⌈p⌉} ∘ asrt_p) = (ζ_{⌈p⌉})_⋄(⌈p⌉) = im (ζ_{⌈p⌉} ∘ π_{⌈p⌉}) = im id = 1`
  have himone : imPred (asrt p ≫ ζ) = (1 : Pred (comprObj (ceilPred p))) := by
    obtain ⟨Q, ξ, π, p₀, q₀, hξ, hπ, hasrt⟩ := (asrt_spec p).1.1
    haveI : Epi ξ := quotient_basics_6 hξ
    have himπ : imPred π = ceilPred p := by
      rw [← imPred_comp_of_epi ξ π, ← hasrt, imPred_asrt]
    obtain ⟨θ, hθ, hθc, -⟩ :=
      compr_basics_2 (himπ ▸ isComprehension_imPred hπ)
        (isComprehension_comprMap (ceilPred p))
    haveI := hθ
    have e : asrt p ≫ ζ = ξ ≫ (θ ≫ (comprMap (ceilPred p) ≫ ζ)) := by
      rw [← Category.assoc θ, hθc, hasrt, Category.assoc]
    rw [e, imPred_comp_of_epi ξ, imPred_comp_of_epi θ, hπζ, imPred_id]
  -- `ζ_{⌈p⌉} ∘ asrt_p` is pure (211XI), say `= π' ∘ ξ'`, and `im π' = 1`
  obtain ⟨W', ξ', π', p', q', hξ', hπ', he⟩ :=
    upm_closed_pure (asrt_spec p).1.1 (isPure_of_isQuotient hqζ)
  have himπ' : imPred π' = (1 : Pred (comprObj (ceilPred p))) := by
    have h1 : imPred (ξ' ≫ π') ≼ imPred π' := (im_ineq π' ξ').1
    rw [← he, himone] at h1
    exact eabasics_le_antisymm (pred_le_truth _) h1
  haveI : IsIso π' := isIso_of_isComprehension_faithful hπ' himπ'
  -- so `ζ_{⌈p⌉} ∘ asrt_p` is a quotient, and for `pᵖ` by the computation above
  have hq : IsQuotient p' (asrt p ≫ ζ) := by
    rw [he]; exact quotient_basics_1 hξ' π'
  have hp' : p' = orth p := by
    have h := quotient_basics_5 hq
    rw [htot] at h
    rw [← eabasics_orth_orth p', ← h]
  rwa [hp'] at hq

/-- **212III** (`standard-form-map`, eff.tex:5102, Proposition): every map
`f` in an &-effectus factors as
`f = π_{im f} ∘ g ∘ ζ_{⌈1∘f⌉} ∘ asrt_{1∘f}` for a unique total and faithful
`g`. -/
theorem standard_form_map (f : X ⟶ Y) :
    ∃! g : comprObj (ceilPred (f ≫ truth Y)) ⟶ comprObj (imPred f),
      (IsTotal g ∧ FaithfulMap g) ∧
        f = asrt (f ≫ truth Y) ≫
          zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
          comprMap (imPred f) := by
  have hsim : IsSharp (imPred f) := ⟨_, _, isImage_imPred f⟩
  obtain ⟨-, hπζ, -⟩ := zetaMap_spec (imPred f) hsim
  -- `f = π_{im f} ∘ g'` by the universal property of `π_{im f}`
  obtain ⟨g', hg', -⟩ :=
    (isComprehension_comprMap (imPred f)).2 f (isImage_imPred f).1
  -- `g'` is faithful
  have hfaith : FaithfulMap g' := by
    refine (faithfulMap_iff g').mpr ?_
    intro q hq
    have h0 : f ≫ (zetaMap (imPred f) hsim ≫ q) = 0 := by
      have e : (g' ≫ comprMap (imPred f)) ≫ (zetaMap (imPred f) hsim ≫ q) = 0 := by
        have e2 : (g' ≫ comprMap (imPred f)) ≫ (zetaMap (imPred f) hsim ≫ q)
            = (g' ≫ (comprMap (imPred f) ≫ zetaMap (imPred f) hsim)) ≫ q := by
          simp only [Category.assoc]
        rw [e2, hπζ, Category.comp_id, hq]
      rw [hg'] at e
      exact e
    have h1 : (zetaMap (imPred f) hsim ≫ q) ≼ orth (imPred f) :=
      le_orth_comm.mp ((im_le_orth_iff f _).mpr h0)
    have h2 : q ≼ comprMap (imPred f) ≫ orth (imPred f) := by
      have h := comp_le_comp (comprMap (imPred f)) h1
      rw [← Category.assoc, hπζ, Category.id_comp] at h
      exact h
    rw [compr_basics_6 (isComprehension_comprMap (imPred f))] at h2
    exact eq_zero_of_le_zero h2
  -- `1 ∘ g' = 1 ∘ f`
  have hg'1 : g' ≫ truth (comprObj (imPred f)) = f ≫ truth Y := by
    conv_rhs => rw [← hg']
    rw [Category.assoc, compr_total (isComprehension_comprMap (imPred f))]
  -- factor `g'` through the quotient `ζ_{⌈1∘f⌉} ∘ asrt_{1∘f}` (212I)
  obtain ⟨g, ⟨hgt, hgeq⟩, hgu⟩ :=
    quotient_total (zeta_asrt_quot (f ≫ truth Y)) g' hg'1
  have heqg : f = asrt (f ≫ truth Y) ≫
      zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
      comprMap (imPred f) := by
    have e : asrt (f ≫ truth Y) ≫
        zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
        comprMap (imPred f)
        = ((asrt (f ≫ truth Y) ≫
            zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _)) ≫ g) ≫
          comprMap (imPred f) := by simp only [Category.assoc]
    rw [e, hgeq, hg']
  -- `1 = im g' = im (g ∘ ζ ∘ asrt) ≤ im g`, so `g` is faithful too
  have hfg : FaithfulMap g := by
    have h1 : imPred g' = (1 : Pred (comprObj (imPred f))) := imPred_eq g' hfaith
    have h2 : imPred g' ≼ imPred g := by
      rw [← hgeq]; exact (im_ineq g _).1
    rw [h1] at h2
    have h3 : imPred g = (1 : Pred (comprObj (imPred f))) :=
      eabasics_le_antisymm (pred_le_truth _) h2
    have h4 := isImage_imPred g
    rwa [h3] at h4
  refine ⟨g, ⟨⟨hgt, hfg⟩, heqg⟩, ?_⟩
  -- uniqueness: comprehensions are monic and quotients epic
  rintro g₁ ⟨-, heq₁⟩
  haveI : Epi (asrt (f ≫ truth Y) ≫
      zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _)) :=
    quotient_basics_6 (zeta_asrt_quot (f ≫ truth Y))
  haveI : Mono (comprMap (imPred f)) :=
    compr_basics_5 (isComprehension_comprMap (imPred f))
  refine (cancel_mono (comprMap (imPred f))).mp ?_
  refine (cancel_epi (asrt (f ≫ truth Y) ≫
    zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _))).mp ?_
  simp only [Category.assoc]
  rw [← heq₁]
  exact heqg

/-- **212III.1** (`standard-form-map`, eff.tex:5111, Proposition): if `f`
is pure, the total faithful part `g` of its standard form is an
isomorphism. -/
theorem standard_form_map_pure {f : X ⟶ Y} (hf : IsPure f)
    (g : comprObj (ceilPred (f ≫ truth Y)) ⟶ comprObj (imPred f))
    (hg : f = asrt (f ≫ truth Y) ≫
      zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
      comprMap (imPred f)) : IsIso g := by
  obtain ⟨Q, ξ, π, p₀, q₀, hξ, hπ, hfeq⟩ := hf
  haveI : Epi ξ := quotient_basics_6 hξ
  have hπt : IsTotal π := compr_total hπ
  -- `1 ∘ π = 1` and `im ξ = 1`, so `im π = im f` and `1 ∘ ξ = 1 ∘ f`
  have himπ : imPred π = imPred f := by rw [hfeq, imPred_comp_of_epi]
  obtain ⟨α, hα, hαc, -⟩ :=
    compr_basics_2 (himπ ▸ isComprehension_imPred hπ)
      (isComprehension_comprMap (imPred f))
  haveI := hα
  have hξ1 : ξ ≫ truth Q = f ≫ truth Y := by rw [hfeq, Category.assoc, hπt]
  have hξq : IsQuotient (orth (f ≫ truth Y)) ξ := by
    have h := quotient_basics_5 hξ
    rw [hξ1] at h
    have hp : p₀ = orth (f ≫ truth Y) := by rw [← eabasics_orth_orth p₀, ← h]
    rwa [hp] at hξ
  obtain ⟨β, hβ, hβc, -⟩ :=
    quotient_basics_2 hξq (zeta_asrt_quot (f ≫ truth Y))
  haveI := hβ
  -- by uniqueness of the standard form, `g = β ∘ α`
  have key : g = β ≫ α := by
    haveI : Mono (comprMap (imPred f)) :=
      compr_basics_5 (isComprehension_comprMap (imPred f))
    haveI : Epi (asrt (f ≫ truth Y) ≫
        zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _)) :=
      quotient_basics_6 (zeta_asrt_quot (f ≫ truth Y))
    refine (cancel_mono (comprMap (imPred f))).mp ?_
    refine (cancel_epi (asrt (f ≫ truth Y) ≫
      zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _))).mp ?_
    simp only [Category.assoc]
    rw [← hg]
    calc f = ξ ≫ π := hfeq
      _ = ((asrt (f ≫ truth Y) ≫
            zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _)) ≫ β) ≫
          (α ≫ comprMap (imPred f)) := by rw [hβc, hαc]
      _ = _ := by simp only [Category.assoc]
  rw [key]
  infer_instance

/-- **212III.2** (`standard-form-map`, eff.tex:5111, Proposition): a pure
faithful map (`im f = 1`) is a quotient. -/
theorem standard_form_map_quot {f : X ⟶ Y} (hf : IsPure f)
    (him : FaithfulMap f) : ∃ p : Pred X, IsQuotient p f := by
  obtain ⟨g, ⟨-, hg⟩, -⟩ := standard_form_map f
  haveI : IsIso g := standard_form_map_pure hf g hg
  -- `im f = 1`, so `π_{im f}` is an isomorphism too
  haveI : IsIso (comprMap (imPred f)) := by
    refine isIso_of_isComprehension_faithful
      (isComprehension_comprMap (imPred f)) ?_
    rw [(img_of_compr (imPred f)).2 _ ⟨_, _, isImage_imPred f⟩]
    exact imPred_eq f him
  have e : asrt (f ≫ truth Y) ≫
      zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
      comprMap (imPred f)
      = (asrt (f ≫ truth Y) ≫
          zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _)) ≫
        (g ≫ comprMap (imPred f)) := by simp only [Category.assoc]
  have hq := quotient_basics_1 (zeta_asrt_quot (f ≫ truth Y))
    (g ≫ comprMap (imPred f))
  rw [← e, ← hg] at hq
  exact ⟨_, hq⟩

/-- **212III.3** (`standard-form-map`, eff.tex:5111, Proposition): a pure
total map is a comprehension. -/
theorem standard_form_map_compr {f : X ⟶ Y} (hf : IsPure f)
    (ht : IsTotal f) : ∃ q : Pred Y, IsComprehension q f := by
  obtain ⟨g, ⟨-, hg⟩, -⟩ := standard_form_map f
  haveI : IsIso g := standard_form_map_pure hf g hg
  -- `1 ∘ f = 1`, so `asrt_{1∘f} = id` and `ζ_{⌈1∘f⌉}` is an isomorphism
  have hone : asrt (f ≫ truth Y) = 𝟙 X := by
    refine (asrt_unique (f ≫ truth Y) (𝟙 X) (diamondPositive_id X) ?_).symm
    rw [Category.id_comp]
    exact ht.symm
  have hceil : ceilPred (f ≫ truth Y) = (1 : Pred X) := by
    rw [ht]; exact ceil_of_isSharp (isSharp_one X)
  haveI : IsIso (zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _)) := by
    refine isIso_of_isQuotient_isTotal
      (zetaMap_spec (ceilPred (f ≫ truth Y)) (isSharp_ceil _)).1 ?_
    show zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫
      truth (comprObj (ceilPred (f ≫ truth Y))) = truth X
    rw [quotient_basics_5
        (zetaMap_spec (ceilPred (f ≫ truth Y)) (isSharp_ceil _)).1,
      eabasics_orth_orth, hceil]
    rfl
  have e : asrt (f ≫ truth Y) ≫
      zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g ≫
      comprMap (imPred f)
      = (zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g) ≫
        comprMap (imPred f) := by
    rw [hone, Category.id_comp]; simp only [Category.assoc]
  have hc := compr_basics_1 (isComprehension_comprMap (imPred f))
    (zetaMap (ceilPred (f ≫ truth Y)) (isSharp_ceil _) ≫ g)
  rw [← e, ← hg] at hc
  exact ⟨_, hc⟩

end AndThenMore

section AndThenDivisoid

variable [AndThenEffectus C]

/-- Helper for 213I: for a *scalar* `μ`, `asrt_μ = μ` (as `1 = id` on the
effect object, 181XIII). -/
private theorem scal_asrt_eq (m : Scal C) : asrt m = m := by
  have h := (asrt_spec m).2
  rwa [truth_effObj_eq_id, Category.comp_id] at h

/-- Helper for 213I: `ζ_{⌈μ⌉}`. -/
private noncomputable def scalZeta (m : Scal C) :
    effObj C ⟶ comprObj (ceilPred m) :=
  zetaMap (ceilPred m) (isSharp_ceil m)

/-- Helper for 213I (212I with `asrt_μ = μ`): `ζ_{⌈μ⌉} ∘ μ` is a quotient
for `μᵖ`. -/
private theorem scalQuot (m : Scal C) : IsQuotient (orth m) (m ≫ scalZeta m) := by
  have h := zeta_asrt_quot m
  rwa [scal_asrt_eq m] at h

/-- Helper for 213I: `1 ∘ ζ_{⌈μ⌉} = ⌈μ⌉`. -/
private theorem scalZeta_truth (m : Scal C) :
    scalZeta m ≫ truth (comprObj (ceilPred m)) = ceilPred m := by
  rw [scalZeta, quotient_basics_5 (zetaMap_spec (ceilPred m) (isSharp_ceil m)).1,
    eabasics_orth_orth]

/-- Helper for 213I: for `λ ≼ μ` there is a unique `λ'` with
`λ' ∘ ζ_{⌈μ⌉} ∘ μ = λ`. -/
private theorem scal_factor {l m : Scal C} (h : l ≼ m) :
    ∃! l' : comprObj (ceilPred m) ⟶ effObj C, (m ≫ scalZeta m) ≫ l' = l := by
  refine (scalQuot m).2 l ?_
  rw [truth_effObj_eq_id, Category.comp_id, eabasics_orth_orth]
  exact h

open Classical in
/-- Helper for 213I: the division `λ/μ ≡ λ' ∘ ζ_{⌈μ⌉}` of scalars. -/
private noncomputable def scalDiv (l m : Scal C) : Scal C :=
  if h : l ≼ m then scalZeta m ≫ (scal_factor h).exists.choose else 0

private theorem scalDiv_spec {l m : Scal C} (h : l ≼ m) :
    m ≫ scalDiv l m = l := by
  classical
  rw [scalDiv, dif_pos h, ← Category.assoc]
  exact (scal_factor h).exists.choose_spec

private theorem scalDiv_self (m : Scal C) : scalDiv m m = ceilPred m := by
  classical
  have hrefl : m ≼ m := pcm_preorder_refl m
  have huniq := (scal_factor hrefl).unique
    ((scal_factor hrefl).exists.choose_spec)
    (show (m ≫ scalZeta m) ≫ truth (comprObj (ceilPred m)) = m by
      rw [quotient_basics_5 (scalQuot m), eabasics_orth_orth])
  rw [scalDiv, dif_pos hrefl, huniq, scalZeta_truth]

private theorem scalDiv_le {l m : Scal C} (h : l ≼ m) :
    scalDiv l m ≼ scalDiv m m := by
  classical
  have hle : scalZeta m ≫ (scal_factor h).exists.choose
      ≼ scalZeta m ≫ truth (comprObj (ceilPred m)) :=
    comp_le_comp _ (pred_le_truth _)
  rw [scalZeta_truth m] at hle
  rw [scalDiv, dif_pos h, scalDiv_self]
  exact hle

private theorem scalDiv_unique {a b c : Scal C} (hab : a ≼ b)
    (hc : c ≼ ceilPred b) (habc : b ≫ c = a) : c = scalDiv a b := by
  classical
  -- `c` factors through the quotient `ζ_{⌈b⌉}` as `c = c' ∘ ζ_{⌈b⌉}`
  obtain ⟨c', hc', -⟩ := (zetaMap_spec (ceilPred b) (isSharp_ceil b)).1.2 c
    (by rw [truth_effObj_eq_id, Category.comp_id, eabasics_orth_orth]; exact hc)
  have hkey : (b ≫ scalZeta b) ≫ c' = a := by
    rw [Category.assoc]
    show b ≫ (scalZeta b ≫ c') = a
    rw [scalZeta, hc']
    exact habc
  have := (scal_factor hab).unique hkey ((scal_factor hab).exists.choose_spec)
  rw [scalDiv, dif_pos hab, ← this, ← hc', scalZeta]

/-- **213I** (`andthen-effect-divisoid`, eff.tex:5167, Proposition): if `C`
is an &-effectus, then `(Scal C)ᵒᵖ` (scalars with reversed multiplication)
is an effect divisoid. -/
theorem andthen_effect_divisoid :
    Nonempty (EffectDivisoid (Scal C)ᵐᵒᵖ) := by
  classical
  refine ⟨{ div := fun a b => MulOpposite.op (scalDiv a.unop b.unop)
            div_le := ?_
            mul_div := ?_
            div_unique := ?_
            le_div_self := ?_
            div_div_self := ?_ }⟩
  · intro a b h
    exact op_le_iff.mpr (scalDiv_le (op_le_iff.mp h))
  · intro a b h
    show MulOpposite.op (b.unop ≫ scalDiv a.unop b.unop) = a
    exact congrArg MulOpposite.op (scalDiv_spec (op_le_iff.mp h))
  · intro a b c hab hc habc
    have h1 : b.unop ≫ c.unop = a.unop := congrArg MulOpposite.unop habc
    have h2 : c.unop ≼ ceilPred b.unop := by
      have := op_le_iff.mp
        (show MulOpposite.op c.unop ≼ MulOpposite.op (scalDiv b.unop b.unop) from hc)
      rwa [scalDiv_self] at this
    show c = MulOpposite.op (scalDiv a.unop b.unop)
    exact MulOpposite.unop_injective (scalDiv_unique (op_le_iff.mp hab) h2 h1)
  · intro a
    refine op_le_iff.mpr ?_
    rw [scalDiv_self]
    exact le_ceil a.unop
  · intro a
    show MulOpposite.op (scalDiv (scalDiv a.unop a.unop) (scalDiv a.unop a.unop))
      = MulOpposite.op (scalDiv a.unop a.unop)
    rw [scalDiv_self, scalDiv_self, ceil_of_isSharp (isSharp_ceil a.unop)]

end AndThenDivisoid

section AndThenSharp

variable [AndThenEffectus C] {X Y Z : C}

/-- **213III** (`perp-sharp-is-orth`, eff.tex:5207, Lemma): in an
&-effectus, if `s ⊥ t` for sharp `s, t` then `s & t = 0 = t & s`.

The proof is eff.tex:5209's.  Write `r ≡ (a ⋁ b)ᵖ`, so that
`1 = a ⋁ b ⋁ r`; then, as `a & a = a`,
`a = a & 1 = (a & a) ⋁ (a & b) ⋁ (a & r) = a ⋁ ((a & b) ⋁ (a & r))`,
whence `a & b ≤ (a & b) ⋁ (a & r) = 0`. -/
theorem perp_sharp_is_orth {s t : Pred X} (hs : IsSharp s) (ht : IsSharp t)
    (h : Perp s t) : andThen s t = 0 ∧ andThen t s = 0 := by
  have main : ∀ {a b : Pred X}, IsSharp a → Perp a b → andThen a b = 0 := by
    intro a b ha hab
    -- `r ≡ (a ⋁ b)ᵖ`, so that `1 = (a ⋁ b) ⋁ r`
    have hpr : Perp (ovee a b hab) (orth (ovee a b hab)) :=
      EffectAlgebra.perp_orth _
    have h1 : ovee (ovee a b hab) (orth (ovee a b hab)) hpr = 1 :=
      EffectAlgebra.ovee_orth _
    have hone : asrt a ≫ (1 : Pred X) = a := (asrt_spec a).2
    have hss : asrt a ≫ a = a := (sharp_prop a).1.mp ha
    -- `a & (a ⋁ b) = (a & a) ⋁ (a & b) = a ⋁ (a & b)`
    obtain ⟨hq1, e1⟩ := FinPAC.ovee_comp hab (asrt a)
    have hq1' : Perp a (asrt a ≫ b) := by
      have h' := hq1; rwa [hss] at h'
    have e1' : asrt a ≫ ovee a b hab = ovee a (asrt a ≫ b) hq1' :=
      e1.trans (PCM.ovee_congr hss rfl _ _)
    -- `a = a & 1 = (a & (a ⋁ b)) ⋁ (a & r)`
    obtain ⟨hq2, e2⟩ := FinPAC.ovee_comp hpr (asrt a)
    rw [h1, hone] at e2
    have hq2' : Perp (ovee a (asrt a ≫ b) hq1')
        (asrt a ≫ orth (ovee a b hab)) := by
      rw [← e1']; exact hq2
    have e3 : a = ovee (ovee a (asrt a ≫ b) hq1')
        (asrt a ≫ orth (ovee a b hab)) hq2' :=
      e2.trans (PCM.ovee_congr e1' rfl _ _)
    -- regroup: `a = a ⋁ ((a & b) ⋁ (a & r))`
    have hw : Perp (asrt a ≫ b) (asrt a ≫ orth (ovee a b hab)) :=
      PCM.perp_of_ovee_perp hq1' hq2'
    have haw : Perp a (ovee (asrt a ≫ b) (asrt a ≫ orth (ovee a b hab)) hw) :=
      PCM.perp_ovee_of_ovee_perp hq1' hq2'
    have e4 : a =
        ovee a (ovee (asrt a ≫ b) (asrt a ≫ orth (ovee a b hab)) hw) haw :=
      e3.trans (PCM.ovee_assoc hq1' hq2')
    -- so `(a & b) ⋁ (a & r) = 0` by cancellation, and `a & b = 0`
    have e5 : ovee (ovee (asrt a ≫ b) (asrt a ≫ orth (ovee a b hab)) hw) a
          (PCM.perp_comm haw)
        = ovee (0 : Pred X) a (PCM.zero_perp a) := by
      rw [PCM.zero_ovee, ← PCM.ovee_comm]
      exact e4.symm
    have hw0 : ovee (asrt a ≫ b) (asrt a ≫ orth (ovee a b hab)) hw = 0 :=
      eabasics_cancellation (PCM.perp_comm haw) (PCM.zero_perp a) e5
    exact (eabasics_positivity hw hw0).1
  exact ⟨main hs h, main ht (PCM.perp_comm h)⟩

/-- **213V** (`simple-andthen-absorption`, eff.tex:5222, Exercise): for
sharp `s` and any predicate `p`: `p ≤ s ⟺ s & p = p`. -/
theorem simple_andthen_absorption {s p : Pred X} (hs : IsSharp s) :
    p ≼ s ↔ andThen s p = p := by
  have h := (asrt_absorp_rule p (isSharp_one (effObj C)) hs).2
  rwa [truth_effObj_eq_id, Category.comp_id] at h

/-- **213VI** (`exc-prod-sharp-maps`, eff.tex:5229, Exercise): a pairing
`⟨f, g⟩` is a sharp map iff both `f` and `g` are sharp maps. -/
theorem exc_prod_sharp_maps (f : Z ⟶ X) (g : Z ⟶ Y)
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) :
    SharpMap (effPair f g h) ↔ SharpMap f ∧ SharpMap g := by
  constructor
  · -- `[s,0]` is sharp (203XIV) and `[s,0] ∘ ⟨f,g⟩ = (s ∘ f) ⋁ 0 = s ∘ f`
    intro hfg
    constructor
    · intro s hs
      obtain ⟨hp, he⟩ := eff_prod_rules_1 f g h s (0 : Pred Y)
      have hsh := hfg _ ((img_tupling_sharp s 0).mpr ⟨hs, dia_isSharp_zero Y⟩)
      rw [he, PCM.ovee_congr rfl (FinPAC.comp_zero g) hp (PCM.perp_zero (f ≫ s)),
        PCM.ovee_zero] at hsh
      exact hsh
    · intro t ht
      obtain ⟨hp, he⟩ := eff_prod_rules_1 f g h (0 : Pred X) t
      have hsh := hfg _ ((img_tupling_sharp 0 t).mpr ⟨dia_isSharp_zero X, ht⟩)
      rw [he, PCM.ovee_congr (FinPAC.comp_zero f) rfl hp (PCM.zero_perp (g ≫ t)),
        PCM.zero_ovee] at hsh
      exact hsh
  · -- conversely, every sharp predicate on `X + Y` is a cotuple `[s,t]` of
    -- sharp predicates (203XIV), and `[s,t] ∘ ⟨f,g⟩ = (s ∘ f) ⋁ (t ∘ g)` is
    -- sharp by 208III
    rintro ⟨hf, hg⟩ u hu
    have hdesc : coprod.desc ((coprod.inl : X ⟶ X ⨿ Y) ≫ u)
        ((coprod.inr : Y ⟶ X ⨿ Y) ≫ u) = u :=
      coprod.hom_ext (by rw [coprod.inl_desc]) (by rw [coprod.inr_desc])
    obtain ⟨hs, ht⟩ := (img_tupling_sharp _ _).mp (by rw [hdesc]; exact hu)
    obtain ⟨hp, he⟩ := eff_prod_rules_1 f g h ((coprod.inl : X ⟶ X ⨿ Y) ≫ u)
      ((coprod.inr : Y ⟶ X ⨿ Y) ≫ u)
    rw [← hdesc, he]
    exact isSharp_ovee (hf _ hs) (hg _ ht) hp

end AndThenSharp

end Theses.B.Eff
