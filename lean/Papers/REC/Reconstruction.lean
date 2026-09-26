/-
Papers/REC/Reconstruction.lean

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707 (2021): §5 "The reconstruction" — points
REC 100–121 of `../papers/REC-points.csv` (Definition 100 of a sequential
effectus, Theorems 102 and 103, Remark 104, and the lemmas of §5.1–§5.4).

One file: a new file cannot import another new file this session, so the
supporting material (floors in a normal SEA, the norm of REC 41, linear maps out
of the Gudder–Pulmannová space, a spectral theorem for normal SEAs) sits here too.

Design:
* **Sequential effectus** (REC 100) is the class `SequentialEffectus` over the
  tree's effectus in partial form.  The dagger is a function on all maps whose
  laws are asked for pure maps only; axiom 4 is the relational form
  `DiamondAdjointRel` (REC 70 defines ⋄-adjointness only once images exist);
  axiom 6 is a normal REC-SEA structure on each `Pred(A)` with product
  `q ∘ asrt_p`.
* **Cited results are named hypotheses**, never axioms:
  - `WeteringStateOrderLemma C` — van de Wetering 2018, Prop. 46 (REC 119);
  - `AlfsenShultzResolventCriterion` — Alfsen–Shultz, *State spaces*, (1.82)
    (REC 120): a bounded operator whose resolvents `1 ± λD` are positive for
    small `λ` is an order derivation;
  - `AlfsenShultzJordanFromDerivations` — Alfsen–Shultz, *Geometry*, 9.48/9.43
    (REC 121), stated for a Banach, directed-complete order unit space with a
    norm-dense set of spectral combinations of a family of idempotents whose
    compressions differ by order derivations; no spectral duality, no dual space.
  `AlfsenShultzOrderDerivationCriterion` (REC 118) is stated, unused.
* **REC 120 by the repaired route** (review-rec120, ERRATA): the proof takes a
  *total* state `ω := π_q ∘ σ` for a state `σ` of `{A|q}` and applies REC 119
  as printed; the scalars are `[0,1]` on the convex part (see next point), so
  all inequalities are real.
* **Scalars are irreducible.**  In an effectus with filters and comprehensions
  that is separated by *states*, the only idempotent scalars are `0` and `1`
  (`idem_scalar_trivial`).  So a sequential effectus has irreducible scalars
  (`scal_irreducible_of_states`): `{0}`, `{0,1}` or `[0,1]` (REC 36,
  `rec36_holds_rc`).  Consequences: **Remark 104 is false** (`rec104_false`:
  `Pred(I) ≅ [0,1]_{C(X)}` only for `|X| ≤ 1`); the splitting in Theorem 102
  always has a trivial factor (`rec102_trivial_factor`); the hypothesis of
  Theorem 103 holds automatically.  Theorems 102 and 103 are proved as printed
  (with the named hypotheses above).
* **The convex part.**  §5.4 assumes "without loss of generality" convex
  scalars; here `CPt σs A` is the convex part `s⊥ · Pred(A)` inside `C` itself
  (REC 93), with its order unit space `VA σs A` (REC 42), compressions `Uop`
  and derivations `Dop`.
* **Compressibility** (REC 112) is stated with the internal states of the
  effectus (`stateLin`), the form in which §5 uses it.
-/
import Papers.REC.Decompose
import Papers.REC.Scalars
import Papers.OAP.OUS
import Papers.SEA.Basic

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Idempotents
open CategoryTheory.Limits hiding HasImages
open Theses.B.Eff
open scoped unitInterval NNReal

namespace Papers.REC

universe u v w

/-! ## Floors and ceilings in a normal SEA (used by REC 105, 106) -/

section SEAFloor

open Papers.SEA
open scoped Papers.SEA

/-- A REC-SEA (REC 56) that is normal is a normal SEA in the sense of
`Papers.SEA` (SEA 15): the same axioms, with SEA's `seq_comm_seq` the first
half of REC's axiom e). -/
@[reducible] def normalSEAOf {E : Type u} [EffectAlgebra E] [s : SEA E] (h : IsNormalSEA E) :
    NormalSEA E :=
  { SEA.toTree (E := E) with
    seq_comm_seq := fun ha hb => s.comm_seq ha hb
    directedComplete := fun S hS => by
      obtain ⟨x, hx1, hx2⟩ := h.1 S hS.2
      exact ⟨x, hx1, hx2⟩
    seq_sup := fun a S x hS hx => (h.2 S x hS.2 hx a).1
    comm_sup := fun a S x hS hx hc => (h.2 S x hS.2 hx a).2 hc }

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

/-- The powers `a⁰ = 1`, `aⁿ⁺¹ = a ⊙ aⁿ`. -/
def seaPow (a : E) : ℕ → E
  | 0 => 1
  | n + 1 => a ⊙ seaPow a n

theorem comm_seaPow {a c : E} (h : Commutes c a) : ∀ n, Commutes c (seaPow a n)
  | 0 => by show c ⊙ (1 : E) = (1 : E) ⊙ c; rw [seq_one, one_seq]
  | n + 1 => Commutes.seq h (comm_seaPow h n)

theorem seaPow_succ_le (a : E) (n : ℕ) : seaPow a (n + 1) ≼ seaPow a n := by
  show a ⊙ seaPow a n ≼ seaPow a n
  rw [comm_seaPow (commutes_refl a) n]
  exact seq_le_left _ _

theorem seaPow_absorb {a c : E} (hc : Commutes c a) (h : c ⊙ a = c) : ∀ n, c ⊙ seaPow a n = c
  | 0 => seq_one c
  | n + 1 => by
    show c ⊙ (a ⊙ seaPow a n) = c
    rw [hc.assoc, h, seaPow_absorb hc h n]

theorem le_seaPow {a c : E} (hc : Commutes c a) (h : c ⊙ a = c) (n : ℕ) : c ≼ seaPow a n := by
  have e := seaPow_absorb hc h n
  rw [comm_seaPow hc n] at e
  rw [← e]; exact seq_le_left _ _

/-- The **floor** `⌊a⌋ := ⋀ₙ aⁿ` (the infimum of the decreasing powers). -/
noncomputable def sflr (a : E) : E :=
  (exists_inf_of_antitone NormalSEA.directedComplete (seaPow_succ_le a)).choose

theorem sflr_isInf (a : E) : EIsInf (Set.range (seaPow a)) (sflr a) :=
  (exists_inf_of_antitone NormalSEA.directedComplete (seaPow_succ_le a)).choose_spec

theorem sflr_le_pow (a : E) (n : ℕ) : sflr a ≼ seaPow a n := (sflr_isInf a).1 _ ⟨n, rfl⟩

theorem sflr_le (a : E) : sflr a ≼ a := by
  have := sflr_le_pow a 1
  rwa [show seaPow a 1 = a ⊙ 1 from rfl, seq_one] at this

theorem orth_pow_directed (a : E) : EDirected (orth '' Set.range (seaPow a)) := by
  refine ⟨⟨orth (seaPow a 0), _, ⟨0, rfl⟩, rfl⟩, ?_⟩
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩ _ ⟨_, ⟨m, rfl⟩, rfl⟩
  have mono : ∀ n m, n ≤ m → seaPow a m ≼ seaPow a n := by
    intro n m hnm
    induction hnm with
    | refl => exact le_refl' _
    | step _ ih => exact le_trans' (seaPow_succ_le a _) ih
  exact ⟨orth (seaPow a (max n m)), ⟨_, ⟨_, rfl⟩, rfl⟩,
    orth_le_orth (mono _ _ (le_max_left _ _)), orth_le_orth (mono _ _ (le_max_right _ _))⟩

theorem orth_sflr_isSup (a : E) : EIsSup (orth '' Set.range (seaPow a)) (orth (sflr a)) :=
  eIsSup_orth_of_eIsInf (sflr_isInf a)

/-- `a` commutes with `⌊a⌋` (S6: `a` commutes with every `(aⁿ)⊥`, so with their
supremum `⌊a⌋⊥`). -/
theorem sflr_comm (a : E) : Commutes a (sflr a) := by
  refine Commutes.of_orth_r ?_
  refine NormalSEA.comm_sup a (orth_pow_directed a) (orth_sflr_isSup a) ?_
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  exact (comm_seaPow (commutes_refl a) n).orth_r

/-- `x ≼ b ⊖ f` iff `f ⊥ x` with `f ⋁ x ≼ b`. -/
theorem le_ominus_iff {b f x : E} (hf : f ≼ b) :
    x ≼ ominus b f hf ↔ ∃ h : Perp f x, ovee f x h ≼ b := by
  obtain ⟨h0, e0⟩ := ovee_ominus hf
  constructor
  · intro hx
    obtain ⟨h1, hle⟩ := ovee_le_ovee_right hx h0
    exact ⟨h1, e0 ▸ hle⟩
  · rintro ⟨h, hle⟩
    exact le_of_ovee_le_ovee h h0 (e0.symm ▸ hle)

/-- `a ⊙ ⌊a⌋ = ⌊a⌋`. -/
theorem seq_sflr (a : E) : a ⊙ sflr a = sflr a := by
  set f := sflr a with hf
  have hc : Commutes a f := sflr_comm a
  refine le_antisymm' ?_ ?_
  · rw [hc]; exact seq_le_left _ _
  · have hfa : f ≼ a := sflr_le a
    obtain ⟨h1, e1⟩ := seq_split a f
    -- `a ⊙ f⊥ ≼ a ⊖ f`
    have hsup := NormalSEA.seq_sup a (orth_pow_directed a) (orth_sflr_isSup a)
    have hd : a ⊙ orth f ≼ ominus a f hfa := by
      refine hsup.2 _ ?_
      rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      rw [le_ominus_iff hfa]
      obtain ⟨h2, e2⟩ := seq_split a (seaPow a n)
      have hfn : f ≼ a ⊙ seaPow a n := sflr_le_pow a (n + 1)
      obtain ⟨h3, hle⟩ := eabasics_le_perp_compat hfn h2
      rw [e2] at hle
      exact ⟨h3, hle⟩
    obtain ⟨h4, hle4⟩ := (le_ominus_iff hfa).1 hd
    -- `f ⋁ a⊙f⊥ ≼ a = a⊙f ⋁ a⊙f⊥`
    have h4' : Perp (a ⊙ orth f) f := PCM.perp_comm h4
    have h1' : Perp (a ⊙ orth f) (a ⊙ f) := PCM.perp_comm h1
    refine le_of_ovee_le_ovee h4' h1' ?_
    rw [← PCM.ovee_comm h4, ← PCM.ovee_comm h1, e1]
    exact hle4

/-- `⌊a⌋` is idempotent. -/
theorem sflr_idem (a : E) : Papers.SEA.IsIdempotent (sflr a) := by
  set f := sflr a with hf
  have hc : Commutes f a := (sflr_comm a).symm
  have hfa : f ⊙ a = f := by rw [hc, seq_sflr]
  have hsup := NormalSEA.seq_sup f (orth_pow_directed a) (orth_sflr_isSup a)
  rw [isIdempotent_iff]
  refine eq_zero_of_le_zero (hsup.2 0 ?_)
  rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
  rw [seq_eq_self_iff.1 (seaPow_absorb hc hfa n)]
  exact le_refl' _

/-- Anything commuting with `a` and absorbing it lies below `⌊a⌋`. -/
theorem le_sflr_of_absorb {a c : E} (hc : Commutes c a) (h : c ⊙ a = c) : c ≼ sflr a :=
  (sflr_isInf a).2 _ (by rintro _ ⟨n, rfl⟩; exact le_seaPow hc h n)

/-- `⌊a⌋` is the largest idempotent below `a` (REC 57 b), SEA 49). -/
theorem le_sflr {a p : E} (hp : Papers.SEA.IsIdempotent p) (h : p ≼ a) : p ≼ sflr a := by
  have h1 : p ⊙ a = p := ((sea17_4 hp a).1).1 h
  have h2 : a ⊙ p = p := ((sea17_4 hp a).2.1).1 h
  exact le_sflr_of_absorb (h1.trans h2.symm) h1

/-- The **ceiling** `⌈a⌉ := ⌊a⊥⌋⊥`. -/
noncomputable def sceil (a : E) : E := orth (sflr (orth a))

theorem sceil_idem (a : E) : Papers.SEA.IsIdempotent (sceil a) := (sflr_idem _).compl

theorem le_sceil (a : E) : a ≼ sceil a := by
  have := orth_le_orth (sflr_le (orth a))
  rwa [orth_orth] at this

/-- `⌈a⌉` is the smallest idempotent above `a` (REC 57 a)). -/
theorem sceil_le {a p : E} (hp : Papers.SEA.IsIdempotent p) (h : a ≼ p) : sceil a ≼ p := by
  have := orth_le_orth (le_sflr hp.compl (orth_le_orth h))
  rwa [orth_orth] at this

theorem sceil_eq_self {p : E} (hp : Papers.SEA.IsIdempotent p) : sceil p = p :=
  le_antisymm' (sceil_le hp (le_refl' p)) (le_sceil p)

/-- If `a ⊙ b = a` then `⌈a⌉ ≼ b` — the form of REC 57 c) the proofs of
REC 105 and 109 use (the print writes the product in the other order). -/
theorem sceil_le_of_seq {a b : E} (h : a ⊙ b = a) : sceil a ≼ b := by
  have h0 : a ⊙ orth b = 0 := seq_eq_self_iff.1 h
  have h1 : orth b ⊙ a = 0 := seq_zero_comm h0
  have hc : Commutes (orth b) a := by show orth b ⊙ a = a ⊙ orth b; rw [h0, h1]
  have h2 : orth b ⊙ orth a = orth b := seq_eq_zero_iff.1 h1
  have := orth_le_orth (le_sflr_of_absorb hc.orth_r h2)
  rwa [orth_orth] at this

/-- For an idempotent `p`, `p ⊙ b = p` gives `p ≼ b` (SEA 17.4). -/
theorem idem_le_of_seq {p b : E} (hp : Papers.SEA.IsIdempotent p) (h : p ⊙ b = p) : p ≼ b :=
  ((sea17_4 hp b).1).2 h

end SEAFloor

/-! ## §5 The reconstruction -/

section Def

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- `g` and `f` are **⋄-adjoint** (REC 70) in the relational form used by REC
100, axiom 4: for every sharp `q` on `Y`, the image of `g ∘ π_q` — whenever it
exists — is `⌈q ∘ f⌉ = ⌊(q ∘ f)⊥⌋⊥ = (im π_{(q∘f)⊥})⊥`.  In a ⋄-effectus (REC
67), where all these images exist, this is `f^⋄ = g_⋄` (`rec100_diamondAdjoint`
below).  REC 100 needs this form because it uses ⋄-adjointness before images
are known to exist (REC 106 shows they do; REC 70 defines ⋄-adjointness only in
a ⋄-effectus). -/
def DiamondAdjointRel {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : Prop :=
  ∀ q : Pred Y, IsSharp q → ∀ {W : C} (π : W ⟶ Y), IsComprehension q π →
    ∀ i : Pred X, IsImage (π ≫ g) i →
    ∀ {V : C} (π' : V ⟶ X), IsComprehension (orth (f ≫ q)) π' →
    ∀ j : Pred X, IsImage π' j → i = orth j

end Def

/-- **REC 100** (`def:sequential-effectus`, short.tex:1847, Definition): a
**sequential effectus** is a normal (REC 30) effectus separated by states (REC
14) such that

1. it has filters and comprehensions (REC 22, 23);
2. comprehensions have images (REC 62);
3. the pure maps (REC 78) form a dagger category;
4. every pure map `f` is ⋄-adjoint (REC 70) to `f†`;
5. for every predicate `p` there is a unique `†`-positive pure map
   `asrt_p : A → A` with `1 ∘ asrt_p = p` (the assert map of `p`);
6. `p & q := q ∘ asrt_p` is a normal sequential product (REC 56) on every
   `Pred(A)`.

Rendering: the dagger is a function `dag` on all maps whose laws are asked for
pure maps only (its values on other maps are irrelevant); "the pure maps form a
category" is `pure_comp` (identities are pure in any effectus,
`isPure_id`); `†`-positive means `a = g† ∘ g` for a pure `g`; axiom 4 is the
relational form `DiamondAdjointRel` (see there); axiom 6 is data `sea` (the SEA
structure on `Pred(A)`) whose product is `q ∘ asrt_p` (`sea_seq`, stated for
any map with the properties of 5, so that no choice is involved), with
`sea_normal`. -/
class SequentialEffectus (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] where
  normal : NormalEffectus C
  separatedByStates : SeparatingStates C
  hasFilters : HasFilters C
  hasComprehension : HasComprehension C
  compr_image : ∀ {W X : C} {p : Pred X} {π : W ⟶ X}, IsComprehension p π →
    ∃ i : Pred X, IsImage π i
  dag : ∀ {X Y : C}, (X ⟶ Y) → (Y ⟶ X)
  pure_comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, IsPure f → IsPure g → IsPure (f ≫ g)
  pure_dag : ∀ {X Y : C} {f : X ⟶ Y}, IsPure f → IsPure (dag f)
  dag_id : ∀ X : C, dag (𝟙 X) = 𝟙 X
  dag_comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, IsPure f → IsPure g →
    dag (f ≫ g) = dag g ≫ dag f
  dag_dag : ∀ {X Y : C} {f : X ⟶ Y}, IsPure f → dag (dag f) = f
  diamond : ∀ {X Y : C} {f : X ⟶ Y}, IsPure f → DiamondAdjointRel f (dag f)
  asrt_existsUnique : ∀ {X : C} (p : Pred X), ∃! a : X ⟶ X,
    IsPure a ∧ (∃ (Y : C) (g : X ⟶ Y), IsPure g ∧ a = g ≫ dag g) ∧ a ≫ truth X = p
  sea : ∀ X : C, SEA (Pred X)
  sea_seq : ∀ {X : C} (p q : Pred X) (a : X ⟶ X), IsPure a →
    (∃ (Y : C) (g : X ⟶ Y), IsPure g ∧ a = g ≫ dag g) → a ≫ truth X = p →
      (sea X).seq p q = a ≫ q
  sea_normal : ∀ X : C, @IsNormalSEA (Pred X) _ (sea X)

section Sequential

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- Identities are pure in every effectus (an identity is a filter for `1`
followed by a comprehension for `1`). -/
theorem isPure_id (X : C) : IsPure (𝟙 X) :=
  ⟨X, 𝟙 X, 𝟙 X, 0, 1, quotient_basics_3 _, compr_basics_3 _, (Category.comp_id _).symm⟩

/-- Isomorphisms are pure. -/
theorem isPure_iso {X Y : C} (θ : X ⟶ Y) [IsIso θ] : IsPure θ :=
  ⟨Y, θ, 𝟙 Y, 0, 1, quotient_basics_3 _, compr_basics_3 _, (Category.comp_id _).symm⟩

/-- A comprehension is pure. -/
theorem isPure_compr {W X : C} {p : Pred X} {π : W ⟶ X} (h : IsComprehension p π) :
    IsPure π :=
  ⟨W, 𝟙 W, π, 0, p, quotient_basics_3 _, h, (Category.id_comp _).symm⟩

/-- A filter is pure. -/
theorem isPure_filter {X Q : C} {p : Pred X} {ξ : X ⟶ Q} (h : IsFilter p ξ) : IsPure ξ :=
  ⟨Q, ξ, 𝟙 Q, orth p, 1, (isFilter_iff_isQuotient _ _).1 h, compr_basics_3 _,
    (Category.comp_id _).symm⟩

/-- `1` is the image of the identity, so it is sharp. -/
theorem isImage_id_one (X : C) : IsImage (𝟙 X) (1 : Pred X) :=
  ⟨rfl, fun q hq => by
    rw [Category.id_comp, Category.id_comp] at hq
    rw [hq]; exact pcm_preorder_refl _⟩

theorem isSharp_one' (X : C) : IsSharp (1 : Pred X) := ⟨X, 𝟙 X, isImage_id_one X⟩

/-- A comprehension for `q` is one for its image (relational form of the proof of
REC 66 b)). -/
theorem isComprehension_of_isImage {W X : C} {q i : Pred X} {π : W ⟶ X}
    (hπ : IsComprehension q π) (hi : IsImage π i) : IsComprehension i π := by
  refine ⟨hi.1, fun Z g hg => hπ.2 g ?_⟩
  refine eabasics_le_antisymm (comp_le_comp g (pred_le_truth q)) ?_
  rw [← hg]
  exact comp_le_comp g (hi.2 q hπ.1)

/-- Images are unique. -/
theorem isImage_unique {X Y : C} {f : X ⟶ Y} {i j : Pred Y} (hi : IsImage f i)
    (hj : IsImage f j) : i = j :=
  eabasics_le_antisymm (hi.2 j hj.1) (hj.2 i hi.1)

/-- An isomorphism does not change images: `im(θ ≫ f) = im f` (relational). -/
theorem isImage_iso_comp {W X Y : C} (θ : W ⟶ X) [IsIso θ] {f : X ⟶ Y} {i : Pred Y} :
    IsImage (θ ≫ f) i ↔ IsImage f i := by
  constructor
  · intro h
    refine ⟨?_, fun q hq => h.2 q (by rw [Category.assoc, hq, Category.assoc])⟩
    have := congrArg (inv θ ≫ ·) h.1
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using this
  · intro h
    exact ⟨by rw [Category.assoc, h.1, Category.assoc], fun q hq => h.2 q (by
      have := congrArg (inv θ ≫ ·) hq
      simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using this)⟩

/-- **REC 101** (short.tex:1863, Remark): the uniqueness clause of REC 100,
axiom 5, is equivalent to the implication
`1 ∘ f† ∘ f = 1 ∘ g† ∘ g ⟹ f† ∘ f = g† ∘ g` for pure `f`, `g` (the analogue of
the CPM axiom of environment structures).  Stated for any dagger on the pure
maps that is closed under composition. -/
theorem rec101 (dag : ∀ {X Y : C}, (X ⟶ Y) → (Y ⟶ X))
    (pure_comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, IsPure f → IsPure g →
      IsPure (f ≫ g))
    (pure_dag : ∀ {X Y : C} {f : X ⟶ Y}, IsPure f → IsPure (dag f)) :
    (∀ {X : C} (p : Pred X) (a b : X ⟶ X),
        (IsPure a ∧ (∃ (Y : C) (g : X ⟶ Y), IsPure g ∧ a = g ≫ dag g) ∧ a ≫ truth X = p) →
        (IsPure b ∧ (∃ (Y : C) (g : X ⟶ Y), IsPure g ∧ b = g ≫ dag g) ∧ b ≫ truth X = p) →
        a = b) ↔
      ∀ {X Y Y' : C} (f : X ⟶ Y) (g : X ⟶ Y'), IsPure f → IsPure g →
        (f ≫ dag f) ≫ truth X = (g ≫ dag g) ≫ truth X → f ≫ dag f = g ≫ dag g := by
  constructor
  · intro hu X Y Y' f g hf hg he
    exact hu _ _ _ ⟨pure_comp hf (pure_dag hf), ⟨Y, f, hf, rfl⟩, rfl⟩
      ⟨pure_comp hg (pure_dag hg), ⟨Y', g, hg, rfl⟩, he.symm⟩
  · rintro h X p a b ⟨-, ⟨Y, f, hf, rfl⟩, hfa⟩ ⟨-, ⟨Y', g, hg, rfl⟩, hgb⟩
    exact h f g hf hg (hfa.trans hgb.symm)

variable [SequentialEffectus C]

namespace SequentialEffectus

instance instHasFilters : HasFilters C := SequentialEffectus.hasFilters
instance instHasComprehension : HasComprehension C := SequentialEffectus.hasComprehension
instance instHasQuotients : HasQuotients C := hasQuotients_of_hasFilters (C := C)

/-- The SEA structure of REC 100, axiom 6, as an instance. -/
instance instSEA (X : C) : SEA (Pred X) := SequentialEffectus.sea X

/-- The same, as a normal SEA of `Papers.SEA`. -/
instance instNormalSEA (X : C) : Papers.SEA.NormalSEA (Pred X) :=
  normalSEAOf (SequentialEffectus.sea_normal X)

end SequentialEffectus

open SequentialEffectus

/-- `†`-positivity (REC 100, axiom 5): `a = g† ∘ g` for a pure `g`. -/
def IsDagPos {X : C} (a : X ⟶ X) : Prop :=
  ∃ (Y : C) (g : X ⟶ Y), IsPure g ∧ a = g ≫ dag g

/-- The **assert map** `asrt_p` of REC 100, axiom 5. -/
noncomputable def asrtS {X : C} (p : Pred X) : X ⟶ X :=
  (asrt_existsUnique p).exists.choose

theorem asrtS_spec {X : C} (p : Pred X) :
    IsPure (asrtS p) ∧ IsDagPos (asrtS p) ∧ asrtS p ≫ truth X = p :=
  (asrt_existsUnique p).exists.choose_spec

theorem isPure_asrtS {X : C} (p : Pred X) : IsPure (asrtS p) := (asrtS_spec p).1

theorem asrtS_truth {X : C} (p : Pred X) : asrtS p ≫ truth X = p := (asrtS_spec p).2.2

theorem asrtS_unique {X : C} {p : Pred X} {a : X ⟶ X} (ha : IsPure a) (hpos : IsDagPos a)
    (h1 : a ≫ truth X = p) : a = asrtS p :=
  (asrt_existsUnique p).unique ⟨ha, hpos, h1⟩ (asrtS_spec p)

/-- A `†`-positive map is `†`-self-adjoint. -/
theorem dag_of_dagPos {X : C} {a : X ⟶ X} (h : IsDagPos a) : dag a = a := by
  obtain ⟨Y, g, hg, rfl⟩ := h
  rw [dag_comp hg (pure_dag hg), dag_dag hg]

theorem dag_asrtS {X : C} (p : Pred X) : dag (asrtS p) = asrtS p :=
  dag_of_dagPos (asrtS_spec p).2.1

/-- The sequential product of REC 100, axiom 6: `p & q = q ∘ asrt_p`. -/
theorem seq_eq {X : C} (p q : Pred X) : SEA.seq p q = asrtS p ≫ q :=
  sea_seq p q _ (asrtS_spec p).1 (asrtS_spec p).2.1 (asrtS_spec p).2.2

theorem seq_eq' {X : C} (p q : Pred X) :
    SequentialEffectAlgebra.seq p q = asrtS p ≫ q := seq_eq p q

/-! ### Floors and ceilings in the effectus (before images are known to exist) -/

/-- The floor `⌊p⌋ = im π_p` (REC 65), which exists by REC 100, axiom 2. -/
noncomputable def flrR {X : C} (p : Pred X) : Pred X :=
  (compr_image (isComprehension_comprMap p)).choose

theorem isImage_flrR {X : C} (p : Pred X) : IsImage (comprMap p) (flrR p) :=
  (compr_image (isComprehension_comprMap p)).choose_spec

/-- The ceiling `⌈p⌉ = ⌊p⊥⌋⊥` (REC 65). -/
noncomputable def ceilR {X : C} (p : Pred X) : Pred X := orth (flrR (orth p))

theorem isSharp_flrR {X : C} (p : Pred X) : IsSharp (flrR p) := ⟨_, _, isImage_flrR p⟩

theorem flrR_le {X : C} (p : Pred X) : flrR p ≼ p :=
  (isImage_flrR p).2 p (isComprehension_comprMap p).1

/-- If `q ∘ f = 1 ∘ f` then `⌊q⌋ ∘ f = 1 ∘ f` (REC 66 e), relational). -/
theorem comp_flrR {X Y : C} (f : Y ⟶ X) {q : Pred X} (h : f ≫ q = f ≫ truth X) :
    f ≫ flrR q = f ≫ truth X := by
  obtain ⟨g, rfl, -⟩ := (isComprehension_comprMap q).2 f h
  rw [Category.assoc, (isImage_flrR q).1, Category.assoc]

/-- A sharp predicate is its own floor (REC 66 f), relational). -/
theorem flrR_of_isSharp {X : C} {p : Pred X} (hp : IsSharp p) : flrR p = p := by
  obtain ⟨Y, g, hg⟩ := hp
  refine eabasics_le_antisymm (flrR_le p) (hg.2 _ ?_)
  exact comp_flrR g hg.1

/-- `p ∘ f = 0` gives `⌈p⌉ ∘ f = 0` (REC 66 e), relational). -/
theorem comp_ceilR_eq_zero {X Y : C} (f : Y ⟶ X) {p : Pred X} (h : f ≫ p = 0) :
    f ≫ ceilR p = 0 := by
  have h1 : f ≫ orth p = f ≫ truth X := by
    have := (comp_orth_eq_zero_iff f (orth p)).1
    rw [eabasics_orth_orth] at this
    exact this h
  exact (comp_orth_eq_zero_iff f (flrR (orth p))).2 (comp_flrR f h1)

/-! ### REC 105 -/

open Papers.SEA in
/-- The image of `asrt_p` is the SEA ceiling `⌈p⌉` (the first half of the proof
of REC 105). -/
theorem isImage_asrtS_sceil {X : C} (p : Pred X) : IsImage (asrtS p) (sceil p) := by
  refine ⟨?_, fun q hq => ?_⟩
  · rw [← seq_eq', asrtS_truth]
    exact ((sea17_5 (sceil_idem p) p).2.1).1 (le_sceil p)
  · rw [← seq_eq', asrtS_truth] at hq
    exact sceil_le_of_seq hq

/-- **REC 105** (`prop:idempotent-is-sharp`, short.tex:1895, Proposition): the
image of `asrt_p` exists and is `⌈p⌉`, both the SEA ceiling of REC 57 (the
smallest idempotent above `p`, `sceil`) and the effectus ceiling of REC 65
(`⌊p⊥⌋⊥`, `ceilR`); in particular `⌈p⌉` is sharp, `p` is sharp iff `p⊥` is,
and `p` is sharp iff it is idempotent.  The paper's proof: `q ∘ asrt_p =
1 ∘ asrt_p` means `p & q = p`, whence `q ≥ ⌈p⌉` (REC 57 c) in the form
`sceil_le_of_seq`: the print writes `q & p` and cites 57 c) for that order);
`asrt_p` is `†`-, hence ⋄-self-adjoint, and axiom 4 identifies the two
ceilings. -/
theorem rec105 {X : C} (p : Pred X) :
    IsImage (asrtS p) (sceil p) ∧ sceil p = ceilR p ∧ IsSharp (ceilR p) ∧
      (IsSharp p ↔ IsSharp (orth p)) ∧ (IsSharp p ↔ SEA.IsIdempotent p) := by
  -- the two ceilings agree: axiom 4 for `asrt_p` (with `asrt_p† = asrt_p`) at `q = 1`
  have hceil : ∀ r : Pred X, sceil r = ceilR r := by
    intro r
    have hd := diamond (isPure_asrtS r) (1 : Pred X) (isSharp_one' X) (𝟙 X)
      (compr_basics_3 (𝟙 X)) (sceil r) (by
        rw [Category.id_comp, dag_asrtS]; exact isImage_asrtS_sceil r)
      (comprMap (orth (asrtS r ≫ 1))) (isComprehension_comprMap _) _
      (isImage_flrR _)
    rw [hd]
    show orth (flrR (orth (asrtS r ≫ truth X))) = _
    rw [asrtS_truth]; rfl
  have hsh : ∀ r : Pred X, IsSharp (ceilR r) := fun r => by
    rw [← hceil]; exact ⟨_, _, isImage_asrtS_sceil r⟩
  have horth : ∀ r : Pred X, IsSharp r → IsSharp (orth r) := by
    intro r hr
    have := hsh (orth r)
    rwa [ceilR, eabasics_orth_orth, flrR_of_isSharp hr] at this
  refine ⟨isImage_asrtS_sceil p, hceil p, hsh p, ⟨horth p, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := horth _ h; rwa [eabasics_orth_orth] at this
  · have h1 : ceilR p = p := by
      rw [ceilR, flrR_of_isSharp (horth p h), eabasics_orth_orth]
    have := sceil_idem p
    rwa [hceil, h1] at this
  · have : sceil p = p := sceil_eq_self h
    exact ⟨_, _, this ▸ isImage_asrtS_sceil p⟩

theorem isIdempotent_of_isSharp {X : C} {p : Pred X} (hp : IsSharp p) : SEA.IsIdempotent p :=
  ((rec105 p).2.2.2.2).1 hp

theorem isSharp_of_isIdempotent {X : C} {p : Pred X} (hp : SEA.IsIdempotent p) : IsSharp p :=
  ((rec105 p).2.2.2.2).2 hp

theorem isSharp_orth {X : C} {p : Pred X} (hp : IsSharp p) : IsSharp (orth p) :=
  ((rec105 p).2.2.2.1).1 hp

/-! ### REC 108, 109 (placed before REC 106, which uses them) -/

/-- **REC 108** (short.tex:1933, Lemma): `asrt_p² = asrt_{p²}`.  The paper's
proof: `asrt_p ∘ asrt_p = asrt_p† ∘ asrt_p` is `†`-positive with
`1 ∘ asrt_p² = p & p`, and assert maps are unique. -/
theorem rec108 {X : C} (p : Pred X) : asrtS p ≫ asrtS p = asrtS (SEA.seq p p) := by
  refine asrtS_unique (pure_comp (isPure_asrtS p) (isPure_asrtS p))
    ⟨X, asrtS p, isPure_asrtS p, by rw [dag_asrtS]⟩ ?_
  rw [Category.assoc, asrtS_truth, seq_eq]

theorem asrtS_idem {X : C} {p : Pred X} (hp : IsSharp p) : asrtS p ≫ asrtS p = asrtS p := by
  rw [rec108, show SEA.seq p p = p from isIdempotent_of_isSharp hp]

/-- **REC 109** (`lem:compatible-filter-compression`, short.tex:1956, Lemma):
for every comprehension `π_p` of a sharp `p` there is a filter `ξ^p` of `p` with
`ξ^p ∘ π_p = id`, and then `π_p ∘ ξ^p = asrt_p`.  The paper's proof: write the
pure `asrt_p = π ∘ ξ`; `asrt_p = asrt_{p²} = asrt_p²` (REC 108) cancels to
`ξ ∘ π = id`; `1 ∘ ξ = 1 ∘ asrt_p = p` makes `ξ` a filter for `p`; `π` has image
`p` (if `q ∘ π = 1 ∘ π` then `p & q = p`, so `p ≤ q`: SEA 17.4 for the
idempotent `p`, which the print cites as REC 57 c)), so it is a comprehension
for `p`; any other comprehension of `p` differs from it by an isomorphism. -/
theorem rec109 {W X : C} {p : Pred X} (hp : IsSharp p) {π : W ⟶ X}
    (hπ : IsComprehension p π) :
    ∃ ξ : X ⟶ W, IsFilter p ξ ∧ π ≫ ξ = 𝟙 W ∧ ξ ≫ π = asrtS p := by
  obtain ⟨Q, ξ₀, π₀, r, t, hξ₀, hπ₀, e⟩ := isPure_asrtS p
  have hidem : asrtS p ≫ asrtS p = asrtS p := asrtS_idem hp
  have : Epi ξ₀ := quotient_basics_6 hξ₀
  have : Mono π₀ := compr_basics_5 hπ₀
  -- `ξ ∘ π = id`
  have hπξ : π₀ ≫ ξ₀ = 𝟙 Q := by
    rw [e] at hidem
    have h1 : ξ₀ ≫ (π₀ ≫ ξ₀ ≫ π₀) = ξ₀ ≫ π₀ := by simpa only [Category.assoc] using hidem
    have h2 : π₀ ≫ ξ₀ ≫ π₀ = π₀ := (cancel_epi ξ₀).1 h1
    exact (cancel_mono π₀).1 (by rw [Category.assoc, h2, Category.id_comp])
  -- `ξ` is a filter for `p`
  have hπt : π₀ ≫ truth X = truth Q := compr_total hπ₀
  have hξt : ξ₀ ≫ truth Q = p := by rw [← hπt, ← Category.assoc, ← e, asrtS_truth]
  have hrp : orth p = r := by
    rw [← hξt, quotient_basics_5 hξ₀, eabasics_orth_orth]
  have hξ₀' : IsFilter p ξ₀ := by rw [isFilter_iff_isQuotient, hrp]; exact hξ₀
  -- `π` has image `p`, so it is a comprehension for `p`
  have him : IsImage π₀ p := by
    refine ⟨?_, fun q hq => ?_⟩
    · rw [← asrtS_truth p, e]
      simp only [← Category.assoc, hπξ, Category.id_comp]
    · have h1 : SEA.seq p q = p := by
        rw [seq_eq, e, Category.assoc, hq, ← Category.assoc, ← e, asrtS_truth]
      exact idem_le_of_seq (isIdempotent_of_isSharp hp) h1
  have hπ₀' : IsComprehension p π₀ := isComprehension_of_isImage hπ₀ him
  -- transport to the given comprehension
  obtain ⟨θ, hθ, eθ, -⟩ := compr_basics_2 hπ hπ₀'
  refine ⟨ξ₀ ≫ inv θ, ?_, ?_, ?_⟩
  · rw [isFilter_iff_isQuotient] at hξ₀' ⊢
    exact quotient_basics_1 hξ₀' _
  · rw [← eθ, Category.assoc, ← Category.assoc π₀, hπξ, Category.id_comp, IsIso.hom_inv_id]
  · rw [← eθ, Category.assoc, IsIso.inv_hom_id_assoc, e]

/-- REC 109: the filters and comprehensions of a sequential effectus are
compatible (REC 74). -/
instance instCompatible : CompatibleFiltersComprehensions C where
  compatible π hp hπ := by
    obtain ⟨ξ, hξ, h1, -⟩ := rec109 hp hπ
    exact ⟨ξ, hξ, h1⟩

/-- REC 109 (and REC 101, last sentence): for a sharp `p` the assert map of REC
100 is the assert map `π_p ∘ ξ^p` of REC 75. -/
theorem asrtS_eq_asrtSharp {X : C} {p : Pred X} (hp : IsSharp p) :
    asrtS p = asrtSharp p hp := by
  obtain ⟨ξ, hξ, h1, h2⟩ := rec109 hp (isComprehension_comprMap p)
  rw [← h2]
  exact asrtSharp_eq hp (isComprehension_comprMap p) hξ h1

/-- `asrt_p ∘ π = π` for a comprehension `π` of a sharp `p`. -/
theorem compr_asrtS {W X : C} {p : Pred X} (hp : IsSharp p) {π : W ⟶ X}
    (hπ : IsComprehension p π) : π ≫ asrtS p = π := by
  obtain ⟨ξ, -, h1, h2⟩ := rec109 hp hπ
  rw [← h2, ← Category.assoc, h1, Category.id_comp]

/-- For a sharp `p`, `p ∘ f = 1 ∘ f` gives `asrt_p ∘ f = f`. -/
theorem comp_asrtS_of {Y X : C} {p : Pred X} (hp : IsSharp p) (f : Y ⟶ X)
    (h : f ≫ p = f ≫ truth X) : f ≫ asrtS p = f := by
  obtain ⟨g, rfl, -⟩ := (isComprehension_comprMap p).2 f h
  rw [Category.assoc, compr_asrtS hp (isComprehension_comprMap p)]

/-! ### REC 106, 107 -/

open Papers.SEA in
/-- The predicates killing `f` that are idempotent form an upwards directed set
(the step "the idempotents form a complete lattice" of the proof of REC 106,
done inside `Pred(A)`): for `r₁, r₂` in it, `⌈r₁ ⋁ (r₁⊥ & r₂)⌉` is in it and
above both. -/
theorem killing_directed {Y X : C} (f : Y ⟶ X) :
    IsUpDirected {r : Pred X | SEA.IsIdempotent r ∧ f ≫ r = 0} := by
  rintro r₁ ⟨h₁, hf₁⟩ r₂ ⟨h₂, hf₂⟩
  have hsh₁ : IsSharp (orth r₁) := isSharp_orth (isSharp_of_isIdempotent h₁)
  have hfr : f ≫ orth r₁ = f ≫ truth X := by
    have := (comp_orth_eq_zero_iff f (orth r₁)).1
    rw [eabasics_orth_orth] at this
    exact this hf₁
  have hfa : f ≫ asrtS (orth r₁) = f := comp_asrtS_of hsh₁ f hfr
  set b := orth r₁ ⊙ r₂ with hb
  have hbp : Perp r₁ b := perp_of_le_right (seq_le_left _ _) (EffectAlgebra.perp_orth r₁)
  set a := ovee r₁ b hbp with ha
  have hfa0 : f ≫ a = 0 := by
    obtain ⟨h', e⟩ := FinPAC.ovee_comp hbp f
    have hfb : f ≫ b = 0 := by
      rw [hb, seq_eq', ← Category.assoc, hfa, hf₂]
    rw [ha, e, PCM.ovee_congr hf₁ hfb _ (PCM.zero_perp 0), PCM.zero_ovee]
  refine ⟨sceil a, ⟨sceil_idem a, ?_⟩, ?_, ?_⟩
  · rw [(rec105 a).2.1]; exact comp_ceilR_eq_zero f hfa0
  · exact le_trans' (left_le_ovee hbp) (le_sceil a)
  · -- `r₂ ≼ ⌈a⌉`: with `c = ⌈a⌉`, `c⊥ ≼ r₁⊥` commutes with `r₁⊥`, so
    -- `c⊥ ⊙ r₂ = c⊥ ⊙ (r₁⊥ ⊙ r₂) = 0`
    set c := sceil a
    have hc : Papers.SEA.IsIdempotent c := sceil_idem a
    have hbc : b ≼ c := le_trans' (right_le_ovee hbp) (le_sceil a)
    have hr₁c : r₁ ≼ c := le_trans' (left_le_ovee hbp) (le_sceil a)
    have hc' : orth c ≼ orth r₁ := orth_le_orth hr₁c
    have hcomm : Commutes (orth c) (orth r₁) := by
      show orth c ⊙ orth r₁ = orth r₁ ⊙ orth c
      rw [((sea17_4 hc.compl (orth r₁)).1).1 hc', ((sea17_4 hc.compl (orth r₁)).2.1).1 hc']
    have h0 : orth c ⊙ b = 0 := ((sea17_5 hc b).2.2.2).1 hbc
    rw [hb, hcomm.assoc, ((sea17_4 hc.compl (orth r₁)).1).1 hc'] at h0
    exact ((sea17_5 hc r₂).2.2.1).2 (seq_zero_comm h0)

open Papers.SEA in
/-- **REC 106** (`prop:sequential-has-images`, short.tex:1917, Proposition): all
morphisms have images.  The paper's proof: `im f` is the infimum of the
idempotents `p` with `p ∘ f = 1 ∘ f`; normality of `f` makes it one of them; and
for any `q` with `q ∘ f = 1 ∘ f` also `⌊q⌋ ∘ f = 1 ∘ f`, with `⌊q⌋` sharp, hence
idempotent (REC 105).  The print cites SEA for "the idempotents form a complete
lattice"; we take the supremum `s` of the idempotents `r` with `r ∘ f = 0`, a
directed set (`killing_directed`), which is idempotent by S6 (`s⊥ & r = 0` for
each `r`), and put `im f = s⊥`. -/
theorem rec106 {Y X : C} (f : Y ⟶ X) : ∃ i : Pred X, IsImage f i := by
  set T := {r : Pred X | SEA.IsIdempotent r ∧ f ≫ r = 0} with hT
  have hTd : IsUpDirected T := killing_directed f
  obtain ⟨s, hs⟩ := (normal (C := C)).1 X T hTd
  have hTne : T.Nonempty := ⟨0, isIdempotent_zero, FinPAC.comp_zero f⟩
  -- `s` is idempotent
  have hsidem : Papers.SEA.IsIdempotent s := by
    have hsup := NormalSEA.seq_sup (orth s) (show EDirected T from ⟨hTne, hTd⟩)
      (show EIsSup T s from hs)
    rw [isIdempotent_iff]
    refine seq_zero_comm (eq_zero_of_le_zero (hsup.2 0 ?_))
    rintro _ ⟨r, ⟨hr, hfr⟩, rfl⟩
    have h1 : r ⊙ s = r := ((sea17_4 hr s).1).1 (hs.1 r ⟨hr, hfr⟩)
    rw [seq_zero_comm (seq_eq_self_iff.1 h1)]
    exact le_refl' _
  -- `s ∘ f = 0` by normality of `f`
  have hfs : f ≫ s = 0 := by
    have := ((normal (C := C)).2 f T s hTd hs).2 0 (by
      rintro _ ⟨r, ⟨-, hr⟩, rfl⟩; show f ≫ r ≼ 0; rw [hr]; exact pcm_preorder_refl _)
    exact eq_zero_of_le_zero this
  refine ⟨orth s, (comp_orth_eq_zero_iff f (orth s)).1 (by rw [eabasics_orth_orth]; exact hfs),
    fun q hq => ?_⟩
  have h1 : f ≫ orth (flrR q) = 0 := (comp_orth_eq_zero_iff f (flrR q)).2 (comp_flrR f hq)
  have h2 : orth (flrR q) ∈ T :=
    ⟨Papers.SEA.IsIdempotent.compl (isIdempotent_of_isSharp (isSharp_flrR q)), h1⟩
  have h3 := orth_le_orth (hs.1 _ h2)
  rw [eabasics_orth_orth] at h3
  exact le_trans' h3 (flrR_le q)

instance instHasImages : HasImages C := ⟨fun f => rec106 f⟩

/-- **REC 107** (short.tex:1925, Corollary): a sequential effectus is a
⋄-effectus (REC 67): it has images (REC 106), filters and comprehensions, and
`p` is sharp iff `p⊥` is (REC 105). -/
instance instDiamond : DiamondEffectus C where
  orth_sharp hs := isSharp_orth hs

theorem rec107 : DiamondEffectus C := inferInstance

theorem flrR_eq_floorPred {X : C} (p : Pred X) : flrR p = floorPred p :=
  isImage_unique (isImage_flrR p) (isImage_imPred _)

theorem ceilR_eq_ceilPred {X : C} (p : Pred X) : ceilR p = ceilPred p := by
  rw [ceilR, flrR_eq_floorPred]; rfl

/-- REC 100, axiom 4, in the form of REC 70 once the effectus is known to be a
⋄-effectus: every pure `f` is ⋄-adjoint to `f†`, `f^⋄ = (f†)_⋄`. -/
theorem rec100_diamondAdjoint {X Y : C} {f : X ⟶ Y} (hf : IsPure f) :
    DiamondAdjoint f (dag f) := by
  funext q
  apply Subtype.ext
  show ceilPred (f ≫ q.1) = imPred (comprMap q.1 ≫ dag f)
  have := diamond hf q.1 q.2 (comprMap q.1) (isComprehension_comprMap _) _ (isImage_imPred _)
    (comprMap (orth (f ≫ q.1))) (isComprehension_comprMap _) _ (isImage_imPred _)
  rw [this]; rfl


/-! ### REC 110–115 -/

/-- In a ⋄-effectus the image of `π_1 ≫ f` is that of `f` (`π_1` is iso). -/
theorem imPred_comprOne_comp {X Y : C} (f : X ⟶ Y) :
    imPred (comprMap (1 : Pred X) ≫ f) = imPred f := by
  have := isIso_comprMap_one X
  exact (im_ineq f (comprMap (1 : Pred X))).2 _ inferInstance

/-- A comprehension of a sharp `p` has image `p`. -/
theorem imPred_compr_sharp {W X : C} {p : Pred X} (hp : IsSharp p) {π : W ⟶ X}
    (hπ : IsComprehension p π) : imPred π = p := by
  rw [(rec65_floor_wd hπ).1]; exact (img_of_compr p).1.1 hp

/-- **REC 110** (`prop:dagger-of-compression`, short.tex:1983, Proposition): for a
sharp `p` and a comprehension `π_p` with filter `ξ^p`, `ξ^p ∘ π_p = id` and
`π_p ∘ ξ^p = asrt_p`, we have `π_p† = ξ^p`.  The paper's proof: by ⋄-adjointness
`⌈1 ∘ π_p†⌉ = (π_p)_⋄(1) = p` and `im (ξ^p)† = (ξ^p)^⋄(1) = p`, so `π_p† = h ∘ ξ^p`
and `(ξ^p)† = π_p ∘ g`; `id = id† = h ∘ g` makes `g` total, hence `(ξ^p)†` total;
then `(ξ^p)† ∘ ξ^p` is `†`-positive with `1 ∘ (ξ^p)† ∘ ξ^p = p`, so it is
`asrt_p = π_p ∘ ξ^p`, and `ξ^p` is epic. -/
theorem rec110 {W X : C} {p : Pred X} (hp : IsSharp p) {π : W ⟶ X}
    (hπ : IsComprehension p π) {ξ : X ⟶ W} (hξ : IsFilter p ξ) (h1 : π ≫ ξ = 𝟙 W)
    (h2 : ξ ≫ π = asrtS p) : dag π = ξ := by
  have hπp : IsPure π := isPure_compr hπ
  have hξp : IsPure ξ := isPure_filter hξ
  -- `⌈1 ∘ π†⌉ = p`
  have hA : ceilPred (dag π ≫ truth W) = p := by
    have hd := rec100_diamondAdjoint (pure_dag hπp)
    rw [dag_dag hπp] at hd
    have := congrArg (fun F => (F ⟨(1 : Pred W), isSharp_one' W⟩).1) hd
    simp only [diaPull, diaPush] at this
    rw [imPred_comprOne_comp, imPred_compr_sharp hp hπ] at this
    exact this
  -- `im (ξ^p)† = p`
  have hB : imPred (dag ξ) = p := by
    have hd := rec100_diamondAdjoint hξp
    have := congrArg (fun F => (F ⟨(1 : Pred W), isSharp_one' W⟩).1) hd
    simp only [diaPull, diaPush] at this
    rw [imPred_comprOne_comp, show ξ ≫ (1 : Pred W) = p from (rec27 (C := C)).2.2.1 hξ,
      ceil_of_isSharp hp] at this
    exact this.symm
  -- factorisations
  obtain ⟨h, hh, -⟩ := hξ.2 (dag π) (by rw [← hA]; exact le_ceilPred _)
  obtain ⟨g, hg, -⟩ := hπ.2 (dag ξ) (by rw [← hB]; exact (isImage_imPred _).1)
  have hgh : g ≫ h = 𝟙 W := by
    have e := dag_comp hπp hξp
    rw [h1, dag_id, ← hg, ← hh] at e
    rw [e]; simp only [Category.assoc]; rw [← Category.assoc π, h1, Category.id_comp]
  -- `g`, hence `(ξ^p)†`, is total
  have hgt : g ≫ truth W = truth W := by
    refine eabasics_le_antisymm (pred_le_truth _) ?_
    have := comp_le_comp g (pred_le_truth (h ≫ truth W))
    rwa [← Category.assoc, hgh, Category.id_comp] at this
  have hdt : dag ξ ≫ truth X = truth W := by
    rw [← hg, Category.assoc, compr_total hπ, hgt]
  -- `(ξ^p)† ∘ ξ^p = asrt_p`
  have hpos : ξ ≫ dag ξ = asrtS p := by
    refine asrtS_unique (pure_comp hξp (pure_dag hξp)) ⟨W, ξ, hξp, rfl⟩ ?_
    rw [Category.assoc, hdt]; exact (rec27 (C := C)).2.2.1 hξ
  have : Epi ξ := (rec27 (C := C)).1 hξ
  have e : dag ξ = π := (cancel_epi ξ).1 (by rw [hpos, h2])
  rw [← e, dag_dag hξp]

/-- REC 110 for the chosen compatible pair: `π_p† = ξ^p`. -/
theorem dag_comprMap {X : C} {p : Pred X} (hp : IsSharp p) :
    dag (comprMap p) = compatFilter p hp := by
  obtain ⟨hξ, h1⟩ := compatFilter_spec p hp
  refine rec110 hp (isComprehension_comprMap p) hξ h1 ?_
  rw [asrtS_eq_asrtSharp hp]; rfl

/-- REC 110, the other way round: `(ξ^p)† = π_p`. -/
theorem dag_compatFilter {X : C} {p : Pred X} (hp : IsSharp p) :
    dag (compatFilter p hp) = comprMap p := by
  rw [← dag_comprMap hp, dag_dag (isPure_compr (isComprehension_comprMap p))]

theorem asrtS_one (X : C) : asrtS (1 : Pred X) = 𝟙 X :=
  (asrtS_unique (isPure_id X) ⟨X, 𝟙 X, isPure_id X, by rw [dag_id, Category.comp_id]⟩
    (Category.id_comp _)).symm

/-- **REC 111** (`cor:dagger-of-iso`, short.tex:2014, Corollary): for an
isomorphism `Θ`, `Θ† = Θ⁻¹`.  The paper's proof: `Θ` is a filter and `Θ⁻¹` a
comprehension for the sharp predicate `1`, with `Θ ∘ Θ⁻¹ = id` and
`Θ⁻¹ ∘ Θ = id = asrt_1`; apply REC 110. -/
theorem rec111 {X Y : C} (θ : X ⟶ Y) [IsIso θ] : dag θ = inv θ := by
  have hξ : IsFilter (1 : Pred X) θ := by
    rw [isFilter_iff_isQuotient, eabasics_orth_one]; exact quotient_basics_3 θ
  have e := rec110 (isSharp_one' X) (compr_basics_3 (inv θ)) hξ (IsIso.inv_hom_id θ)
    (by rw [IsIso.hom_inv_id, asrtS_one])
  have e' := congrArg dag e
  rw [dag_dag (isPure_iso (inv θ))] at e'
  exact e'.symm

/-- **REC 112** (`prop:compressive`, short.tex:2023, Proposition): the sequential
product is compressible, for the states of the effectus: if `p` is sharp and
`p ∘ ω = 1` for a state `ω`, then `(p & a) ∘ ω = a ∘ ω` for all `a`.  The
paper's proof: `p ∘ ω = 1` gives `im ω ≤ p`, so `asrt_p ∘ ω = ω` (REC 77 a)).
(REC 59's compressibility quantifies over the real-valued states of a convex
SEA; what the proof gives — and what §5.4 then uses, as the paper says there —
is this internal form.) -/
theorem rec112 {X : C} {p : Pred X} (hp : IsSharp p) (ω : Stat X) (h : ω.1 ≫ p = 𝟙 _)
    (a : Pred X) : ω.1 ≫ SEA.seq p a = ω.1 ≫ a := by
  have ht : ω.1 ≫ truth X = 𝟙 _ := ω.2.trans truth_effObj_eq_id
  rw [seq_eq, ← Category.assoc, comp_asrtS_of hp ω.1 (h.trans ht.symm)]

/-- **REC 113** (`lem:pure-decomposition`, short.tex:2042, Lemma): every pure `f`
factors as `f = π_{im f} ∘ Θ ∘ ξ^{⌈1∘f⌉} ∘ asrt_{1∘f}` with `Θ` an isomorphism
(stated for any comprehension `π` of `im f`).  The paper's proof: `f = π' ∘ ξ'`
with `ξ'` a filter for `1 ∘ f` and `π'` a comprehension for `im f`; and
`ξ^{⌈1∘f⌉} ∘ asrt_{1∘f}` is a filter for `1 ∘ f` — it has `1 ∘ (–) = 1 ∘ f`,
image `1` (computed with `(–)_⋄`), and is pure, hence a filter followed by a
comprehension with image `1`, i.e. by an isomorphism. -/
theorem rec113 {X Y : C} {f : X ⟶ Y} (hf : IsPure f) {W : C} {π : W ⟶ Y}
    (hπ : IsComprehension (imPred f) π) :
    ∃ θ : comprObj (ceilPred (f ≫ truth Y)) ⟶ W, IsIso θ ∧
      f = asrtS (f ≫ truth Y) ≫ compatFilter _ (isSharp_ceil (f ≫ truth Y)) ≫ θ ≫ π := by
  set p : Pred X := f ≫ truth Y with hpdef
  obtain ⟨Q, ξ', π', r, t, hξ', hπ', e⟩ := hf
  -- `ξ'` is a filter for `1 ∘ f`
  have hπ't : π' ≫ truth Y = truth Q := compr_total hπ'
  have hξ'p : IsFilter p ξ' := by
    have h5 := quotient_basics_5 hξ'
    have : p = orth r := by rw [hpdef, e, Category.assoc, hπ't, h5]
    rw [isFilter_iff_isQuotient, this, eabasics_orth_orth]; exact hξ'
  -- `π'` is a comprehension for `im f`
  have : Epi ξ' := quotient_basics_6 hξ'
  have himf : IsImage f (imPred π') := by rw [e]; exact isImage_comp_epi ξ' (isImage_imPred π')
  have hπ'' : IsComprehension (imPred f) π' := by
    rw [imPred_eq f himf]; exact isComprehension_of_isImage hπ' (isImage_imPred π')
  obtain ⟨θ₁, hθ₁, eθ₁, -⟩ := compr_basics_2 hπ'' hπ
  -- `g = ξ^{⌈p⌉} ∘ asrt_p` is a filter for `p`
  set c := ceilPred p with hc
  have hcs : IsSharp c := isSharp_ceil p
  set g := asrtS p ≫ compatFilter c hcs with hg
  have hgp : IsPure g := pure_comp (isPure_asrtS p) (isPure_filter (compatFilter_spec c hcs).1)
  have himA : IsImage (asrtS p) c := by
    have h := (rec105 p).1; rwa [(rec105 p).2.1, ceilR_eq_ceilPred] at h
  have hgt : g ≫ truth _ = p := by
    rw [hg, Category.assoc, (rec27 (C := C)).2.2.1 (compatFilter_spec c hcs).1, himA.1,
      asrtS_truth]
  have himg : imPred g = 1 := by
    have e1 := diaPush_comp (asrtS p) (compatFilter c hcs) ⟨(1 : Pred X), isSharp_one' X⟩
    have e2 := congrArg Subtype.val e1
    simp only [diaPush] at e2
    rw [imPred_comprOne_comp, imPred_comprOne_comp, imPred_eq _ himA,
      (compatFilter_spec c hcs).2] at e2
    rw [e2]; exact imPred_eq _ (isImage_id_one _)
  obtain ⟨Q₂, ξ₂, π₂, r₂, t₂, hξ₂, hπ₂, e₂⟩ := hgp
  have : Epi ξ₂ := quotient_basics_6 hξ₂
  have himπ : IsImage π₂ 1 := by
    have h := isImage_imPred π₂
    have h2 : IsImage g (imPred π₂) := by rw [e₂]; exact isImage_comp_epi ξ₂ h
    rwa [← imPred_eq g h2, himg] at h
  obtain ⟨θ₃, hθ₃, eθ₃, -⟩ := compr_basics_2 (isComprehension_of_isImage hπ₂ himπ)
    (compr_basics_3 (𝟙 _))
  rw [Category.comp_id] at eθ₃
  have : IsIso π₂ := by rw [← eθ₃]; exact hθ₃
  have hgq : IsQuotient r₂ g := by rw [e₂]; exact quotient_basics_1 hξ₂ π₂
  have hgf : IsFilter p g := by
    have h5 := quotient_basics_5 hgq
    rw [hgt] at h5
    rw [isFilter_iff_isQuotient, h5, eabasics_orth_orth]; exact hgq
  -- two filters for `p` differ by an isomorphism
  obtain ⟨θ₂, hθ₂, eθ₂, -⟩ := quotient_basics_2 ((isFilter_iff_isQuotient _ _).1 hξ'p)
    ((isFilter_iff_isQuotient _ _).1 hgf)
  refine ⟨θ₂ ≫ θ₁, by have := hθ₁; have := hθ₂; infer_instance, ?_⟩
  rw [e, ← eθ₁, ← eθ₂]
  simp only [hg, Category.assoc]
  rfl

/-- ⋄-self-adjointness of assert maps: `(asrt_q)_⋄ = (asrt_q)^⋄`. -/
theorem diaPush_asrtS {X : C} (q : Pred X) : diaPush (asrtS q) = diaPull (asrtS q) := by
  have := rec100_diamondAdjoint (isPure_asrtS q)
  rw [dag_asrtS] at this
  exact this.symm

theorem isImage_asrtS_ceil {X : C} (s : Pred X) : IsImage (asrtS s) (ceilPred s) := by
  have h := (rec105 s).1; rwa [(rec105 s).2.1, ceilR_eq_ceilPred] at h

/-- The computation at the end of the proof of REC 114: if
`g = π_{c'} ∘ Θ ∘ ξ^{⌈s⌉} ∘ asrt_s` then `g† ∘ g = asrt_s ∘ asrt_s`. -/
theorem sq_of_decomp {X : C} (s₀ : Pred X) (hss : IsSharp (ceilPred s₀)) {c' : Pred X}
    (hcs' : IsSharp c') (θ : comprObj (ceilPred s₀) ⟶ comprObj c') [IsIso θ] (g : X ⟶ X)
    (eg : g = asrtS s₀ ≫ compatFilter _ hss ≫ θ ≫ comprMap c') :
    g ≫ dag g = asrtS s₀ ≫ asrtS s₀ := by
  subst eg
  have hA : IsPure (asrtS s₀) := isPure_asrtS s₀
  have hF : IsPure (compatFilter _ hss) := isPure_filter (compatFilter_spec _ hss).1
  have hT : IsPure θ := isPure_iso θ
  have hP : IsPure (comprMap c') := isPure_compr (isComprehension_comprMap _)
  have habs : asrtS s₀ ≫ asrtS (ceilPred s₀) = asrtS s₀ :=
    comp_asrtS_of hss _ (isImage_asrtS_ceil s₀).1
  have hfc : compatFilter (ceilPred s₀) hss ≫ comprMap (ceilPred s₀) = asrtS (ceilPred s₀) := by
    rw [asrtS_eq_asrtSharp hss]; rfl
  rw [dag_comp hA (pure_comp hF (pure_comp hT hP)), dag_comp hF (pure_comp hT hP),
    dag_comp hT hP, dag_comprMap hcs', rec111, dag_compatFilter, dag_asrtS]
  simp only [Category.assoc]
  rw [← Category.assoc (comprMap c') (compatFilter c' hcs'), (compatFilter_spec c' hcs').2,
    Category.id_comp, IsIso.hom_inv_id_assoc, ← Category.assoc (compatFilter _ hss), hfc,
    ← Category.assoc, habs]

/-- **REC 114** (short.tex:2092, Proposition): `asrt²_{p&q} = asrt_p ∘ asrt²_q ∘ asrt_p`
(and this is `asrt_{(p&q)²}`, REC 108).  The paper's proof: `im (asrt_q ∘ asrt_p) =
⌈q & p⌉` by the ⋄-calculus; REC 113 writes `asrt_q ∘ asrt_p =
π_{⌈q&p⌉} ∘ Θ ∘ ξ^{⌈p&q⌉} ∘ asrt_{p&q}`; its dagger is
`asrt_p ∘ asrt_q = asrt_{p&q} ∘ π_{⌈p&q⌉} ∘ Θ⁻¹ ∘ ξ^{⌈q&p⌉}` (REC 110, 111); compose
and use `ξ ∘ π = id`, `π ∘ ξ = asrt` and `asrt_{p&q} ∘ asrt_{⌈p&q⌉} = asrt_{p&q}`. -/
theorem rec114 {X : C} (p q : Pred X) :
    asrtS (SEA.seq p q) ≫ asrtS (SEA.seq p q) = asrtS p ≫ asrtS q ≫ asrtS q ≫ asrtS p ∧
      asrtS (SEA.seq p q) ≫ asrtS (SEA.seq p q) =
        asrtS (SEA.seq (SEA.seq p q) (SEA.seq p q)) := by
  refine ⟨?_, rec108 _⟩
  set g := asrtS p ≫ asrtS q with hg
  have hgp : IsPure g := pure_comp (isPure_asrtS p) (isPure_asrtS q)
  have hgt : g ≫ truth X = SEA.seq p q := by rw [hg, Category.assoc, asrtS_truth, seq_eq]
  -- `im g = ⌈q & p⌉`
  have himg : imPred g = ceilPred (SEA.seq q p) := by
    have e1 := congrArg Subtype.val
      (diaPush_comp (asrtS p) (asrtS q) ⟨(1 : Pred X), isSharp_one' X⟩)
    have hpush : diaPush (asrtS p) ⟨(1 : Pred X), isSharp_one' X⟩ =
        ⟨ceilPred p, isSharp_ceil p⟩ := Subtype.ext (by
      show imPred (comprMap (1 : Pred X) ≫ asrtS p) = ceilPred p
      rw [imPred_comprOne_comp, imPred_eq _ (isImage_asrtS_ceil p)])
    rw [hpush, diaPush_asrtS] at e1
    simp only [diaPush, diaPull] at e1
    rw [imPred_comprOne_comp, ← hg] at e1
    rw [e1, ceiling_within_ceiling, seq_eq]
  set c' := ceilPred (SEA.seq q p) with hc'
  have hcs' : IsSharp c' := isSharp_ceil _
  have hπ : IsComprehension (imPred g) (comprMap c') := by
    rw [himg]; exact isComprehension_comprMap _
  obtain ⟨θ, hθ, eg⟩ := rec113 hgp hπ
  have : IsIso θ := hθ
  have hgdg := sq_of_decomp (g ≫ truth X) (isSharp_ceil _) hcs' θ g eg
  rw [hgt] at hgdg
  rw [← hgdg, hg, dag_comp (isPure_asrtS p) (isPure_asrtS q), dag_asrtS, dag_asrtS]
  simp only [Category.assoc]

/-- **REC 115** (`cor:assert-is-quadratic`, short.tex:2131, Corollary): for sharp
`p, q`, `(p & q)² = p & (q & p)`; i.e. the sequential product of `Pred(A)` is
quadratic (REC 60).  The paper's proof: apply REC 114 to `1`, with
`asrt_q² = asrt_q` for sharp `q`. -/
theorem rec115 {X : C} {p q : Pred X} (_hp : IsSharp p) (hq : IsSharp q) :
    SEA.seq (SEA.seq p q) (SEA.seq p q) = SEA.seq p (SEA.seq q p) := by
  have h := congrArg (· ≫ truth X) (rec114 p q).1
  simp only [Category.assoc, asrtS_truth] at h
  rw [← Category.assoc (asrtS q) (asrtS q), asrtS_idem hq] at h
  rw [show SEA.seq (SEA.seq p q) (SEA.seq p q) = asrtS (SEA.seq p q) ≫ SEA.seq p q from
    seq_eq _ _, h, show SEA.seq p (SEA.seq q p) = asrtS p ≫ SEA.seq q p from seq_eq _ _, seq_eq q p]

/-- REC 115: the sequential product of every `Pred(A)` is quadratic (REC 60). -/
theorem rec115_isQuadratic (X : C) : IsQuadratic (E := Pred X) := by
  intro p q hp hq
  exact (rec115 (isSharp_of_isIdempotent hq) (isSharp_of_isIdempotent hp)).symm

-- **REC 116** (short.tex:2139, Remark): whether the dagger is structure or property;
-- the print leaves its own argument unfinished (a commented-out proposition ending in
-- `\TODO`).  No mathematical claim is asserted; not formalised.

end Sequential

/-! ## Order unit spaces: the norm of REC 41 -/

section OUSNorm

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]

/-- The set whose infimum is the order-unit norm (REC 41). -/
def ousNormSet (v : V) : Set ℝ := {l : ℝ | -(l • ouUnit V) ≤ v ∧ v ≤ l • ouUnit V}

theorem ousNorm_eq_rc (v : V) : ousNorm V v = sInf (ousNormSet v) := rfl

theorem ousNormSet_nonempty (v : V) : (ousNormSet v).Nonempty := by
  obtain ⟨n, h1, h2⟩ := Papers.OAP.oap58_orderUnit v
  exact ⟨n, h1, h2⟩

theorem ousNormSet_nonneg (hu : ouUnit V ≠ 0) {v : V} {l : ℝ} (h : l ∈ ousNormSet v) :
    0 ≤ l := by
  have h1 : -(l • ouUnit V) ≤ l • ouUnit V := h.1.trans h.2
  have h2 : (0 : V) ≤ (2 * l) • ouUnit V := by
    have := add_le_add_left h1 (l • ouUnit V)
    rw [neg_add_cancel] at this
    rwa [two_mul, add_smul]
  have := ou_nonneg_of_smul_unit_nonneg hu h2
  linarith

theorem ousNormSet_eq_univ (hu : ouUnit V = 0) (v : V) : ousNormSet v = Set.univ := by
  ext l
  simp only [ousNormSet, Set.mem_ofPred_eq, Set.mem_univ, hu, smul_zero, neg_zero,
    ou_eq_zero_of_unit_eq_zero hu v, le_refl, and_self]

theorem ousNorm_nonneg_rc (v : V) : 0 ≤ ousNorm V v := by
  by_cases hu : ouUnit V = 0
  · rw [ousNorm_eq_rc, ousNormSet_eq_univ hu, Real.sInf_of_not_bddBelow not_bddBelow_univ]
  · exact le_csInf (ousNormSet_nonempty v) fun l hl => ousNormSet_nonneg hu hl

/-- `-ε·1 ≤ v ≤ ε·1` gives `‖v‖ ≤ ε`. -/
theorem ousNorm_le_rc {v : V} {ε : ℝ} (hε : 0 ≤ ε) (h1 : -(ε • ouUnit V) ≤ v)
    (h2 : v ≤ ε • ouUnit V) : ousNorm V v ≤ ε := by
  by_cases hu : ouUnit V = 0
  · rw [ousNorm_eq_rc, ousNormSet_eq_univ hu, Real.sInf_of_not_bddBelow not_bddBelow_univ]
    exact hε
  · exact csInf_le ⟨0, fun l hl => ousNormSet_nonneg hu hl⟩ ⟨h1, h2⟩

/-- `‖v‖ < ε` gives `-ε·1 ≤ v ≤ ε·1`. -/
theorem ousNorm_bounds {v : V} {ε : ℝ} (h : ousNorm V v < ε) :
    -(ε • ouUnit V) ≤ v ∧ v ≤ ε • ouUnit V := by
  obtain ⟨l, ⟨hl1, hl2⟩, hlε⟩ := exists_lt_of_csInf_lt (ousNormSet_nonempty v) h
  have hm : l • ouUnit V ≤ ε • ouUnit V := ou_smul_unit_mono hlε.le
  exact ⟨(neg_le_neg hm).trans hl1, hl2.trans hm⟩

theorem ousNorm_neg (v : V) : ousNorm V (-v) = ousNorm V v := by
  have : ousNormSet (-v) = ousNormSet v := by
    ext l; simp only [ousNormSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨neg_le.1 h2, neg_le_neg_iff.1 h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨neg_le_neg h2, neg_le.1 h1⟩
  rw [ousNorm_eq_rc, ousNorm_eq_rc, this]

/-- A state (positive unital linear functional) is bounded by the norm:
`|φ v| ≤ ‖v‖`. -/
theorem abs_state_le (φ : V →ₗ[ℝ] ℝ) (hpos : ∀ v, 0 ≤ v → 0 ≤ φ v) (hu : φ (ouUnit V) = 1)
    (v : V) : |φ v| ≤ ousNorm V v := by
  refine le_csInf (ousNormSet_nonempty v) fun l hl => abs_le.2 ⟨?_, ?_⟩
  · have := hpos _ (sub_nonneg.2 hl.1)
    rw [map_sub, map_neg, map_smul, hu, smul_eq_mul, mul_one] at this
    linarith
  · have := hpos _ (sub_nonneg.2 hl.2)
    rw [map_sub, map_smul, hu, smul_eq_mul, mul_one] at this
    linarith

/-- An Archimedean order unit space is an order unit space in the sense of
REC 41: the order-unit seminorm is a norm and the positive cone is closed. -/
theorem isOUS_of_archimedean_rc (hA : OUSArchimedean V) : IsOUS V where
  norm_eq_zero v h := by
    have hb : ∀ ε : ℝ, 0 < ε → -(ε • ouUnit V) ≤ v ∧ v ≤ ε • ouUnit V :=
      fun ε hε => ousNorm_bounds (h ▸ hε)
    refine le_antisymm (hA v fun ε hε => (hb ε hε).2) ?_
    have := hA (-v) fun ε hε => neg_le.1 (hb ε hε).1
    exact neg_nonpos.1 this
  cone_closed v h := by
    have : ∀ ε : ℝ, 0 < ε → -v ≤ ε • ouUnit V := by
      intro ε hε
      obtain ⟨w, hw, hn⟩ := h ε hε
      have h1 := (ousNorm_bounds hn).1
      have h2 := neg_le_neg h1
      rw [neg_neg, neg_sub] at h2
      have : -v ≤ ε • ouUnit V - w := by
        calc -v = (w - v) - w := by abel
          _ ≤ ε • ouUnit V - w := sub_le_sub_right h2 w
      exact this.trans (sub_le_self _ hw)
    exact neg_nonpos.1 (hA (-v) this)

/-- Norm completeness in OAP's order form gives REC 41's Banach property. -/
theorem isBanachOUS_of (hC : Papers.OAP.OUSNormComplete V) : IsBanachOUS V := by
  intro s hs
  obtain ⟨v, hv⟩ := hC s fun ε hε => by
    obtain ⟨N, hN⟩ := hs ε hε
    exact ⟨N, fun m hm n hn => (ousNorm_bounds (hN m hm n hn)).2⟩
  refine ⟨v, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hv (ε / 2) (by positivity)
  refine ⟨N, fun n hn => lt_of_le_of_lt (ousNorm_le_rc (by positivity) ?_ (hN n hn).1) (by linarith)⟩
  have := (hN n hn).2
  rw [neg_le, neg_sub]; exact this

/-- OAP's directed completeness gives REC 41's. -/
theorem isDirectedCompleteOUS_of (hD : Papers.OAP.OUSDirectedComplete V) :
    IsDirectedCompleteOUS V := by
  intro D hDs hd
  rcases D.eq_empty_or_nonempty with hE | hne
  · refine ⟨0, ⟨le_rfl, ou_unit_nonneg⟩, by simp [hE], fun t ht _ => ht.1⟩
  · obtain ⟨s, hs1, hs2, hs3⟩ := Papers.OAP.ousDirected_iff.1 hD D hDs hne hd
    exact ⟨s, hs1, hs2, hs3⟩

end OUSNorm

/-! ## Linear maps out of the Gudder–Pulmannová space -/

section GPLift

variable {E : Type u} [EffectAlgebra E] [EffectModule I E] {W : Type w} [AddCommGroup W]
  [Module ℝ W] (F : E → W)
  (hadd : ∀ {a b : E} (h : Perp a b), F (ovee a b h) = F a + F b)
  (hsmul : ∀ (l : I) (a : E), F (l • a) = (l : ℝ) • F a)

include hsmul in
theorem gpConeRel_lift {x y : ℝ≥0 × E} (h : GP.coneRel x y) :
    ((x.1 : ℝ) • F x.2) = ((y.1 : ℝ) • F y.2) := by
  obtain ⟨N, hx, hy, e⟩ := h
  have e' := congrArg F e
  rw [hsmul, hsmul, GP.frac_coe hx, GP.frac_coe hy] at e'
  rcases eq_or_ne N 0 with hN | hN
  · have h1 : x.1 = 0 := le_antisymm (hN ▸ hx) zero_le
    have h2 : y.1 = 0 := le_antisymm (hN ▸ hy) zero_le
    rw [h1, h2]; simp
  · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have := congrArg (fun w => (N : ℝ) • w) e'
    simp only [_root_.smul_smul] at this
    rwa [mul_div_cancel₀ _ hN', mul_div_cancel₀ _ hN'] at this

/-- The lift of `F` to the cone. -/
noncomputable def gpConeLift : GP.Cone E → W :=
  Quotient.lift (fun x : ℝ≥0 × E => (x.1 : ℝ) • F x.2)
    (fun _ _ h => gpConeRel_lift F hsmul h)

theorem gpConeLift_mk (r : ℝ≥0) (a : E) :
    gpConeLift F hsmul (GP.Cone.mk r a) = (r : ℝ) • F a := rfl

include hadd in
theorem gpConeLift_add (x y : GP.Cone E) :
    gpConeLift F hsmul (x + y) = gpConeLift F hsmul x + gpConeLift F hsmul y := by
  induction x using GP.Cone.ind with
  | _ r a =>
  induction y using GP.Cone.ind with
  | _ s b =>
    have hp : Perp (GP.frac r (r + s) • a) (GP.frac s (r + s) • b) :=
      GP.smul_perp_smul' (GP.frac_perp (le_refl (r + s))) a b
    rw [GP.Cone.add_eq (le_refl (r + s)) hp, gpConeLift_mk, gpConeLift_mk, gpConeLift_mk,
      hadd, hsmul, hsmul, smul_add, _root_.smul_smul, _root_.smul_smul]
    rcases eq_or_ne (r + s) 0 with h0 | h0
    · have hr : r = 0 := le_antisymm (h0 ▸ le_self_add) zero_le
      have hs : s = 0 := le_antisymm (h0 ▸ le_add_self) zero_le
      subst hr; subst hs; simp
    · have h0' : ((r + s : ℝ≥0) : ℝ) ≠ 0 := by exact_mod_cast h0
      rw [GP.frac_coe le_self_add, GP.frac_coe le_add_self, mul_div_cancel₀ _ h0',
        mul_div_cancel₀ _ h0']

theorem gpConeLift_zero : gpConeLift F hsmul 0 = 0 := by
  rw [GP.Cone.zero_def, gpConeLift_mk]; simp

theorem gpConeLift_smul (t : ℝ≥0) (x : GP.Cone E) :
    gpConeLift F hsmul (t • x) = (t : ℝ) • gpConeLift F hsmul x := by
  induction x using GP.Cone.ind with
  | _ r a => rw [GP.Cone.smul_mk, gpConeLift_mk, gpConeLift_mk, _root_.smul_smul]; push_cast; rfl

/-- The lift of `F` to `GP.Vec E`, as a function. -/
noncomputable def gpLiftFun : GP.Vec E → W :=
  Quotient.lift (fun x : GP.Cone E × GP.Cone E => gpConeLift F hsmul x.1 - gpConeLift F hsmul x.2)
    (by
      rintro ⟨p, q⟩ ⟨p', q'⟩ h
      have h' : p + q' = p' + q := h
      have := congrArg (gpConeLift F hsmul) h'
      rw [gpConeLift_add F hadd hsmul, gpConeLift_add F hadd hsmul] at this
      show gpConeLift F hsmul p - gpConeLift F hsmul q = gpConeLift F hsmul p' - gpConeLift F hsmul q'
      rw [sub_eq_sub_iff_add_eq_add]; exact this)

theorem gpLiftFun_mk (p q : GP.Cone E) :
    gpLiftFun F hadd hsmul (GP.Vec.mk p q) = gpConeLift F hsmul p - gpConeLift F hsmul q := rfl

theorem gpLiftFun_add (x y : GP.Vec E) :
    gpLiftFun F hadd hsmul (x + y) = gpLiftFun F hadd hsmul x + gpLiftFun F hadd hsmul y := by
  induction x using GP.Vec.ind with
  | _ p q =>
  induction y using GP.Vec.ind with
  | _ p' q' =>
    rw [GP.Vec.mk_add, gpLiftFun_mk, gpLiftFun_mk, gpLiftFun_mk,
      gpConeLift_add F hadd hsmul, gpConeLift_add F hadd hsmul]
    abel

theorem gpLiftFun_nnsmul (t : ℝ≥0) (x : GP.Vec E) :
    gpLiftFun F hadd hsmul (t • x) = (t : ℝ) • gpLiftFun F hadd hsmul x := by
  induction x using GP.Vec.ind with
  | _ p q =>
    rw [GP.Vec.nnsmul_mk, gpLiftFun_mk, gpLiftFun_mk, gpConeLift_smul, gpConeLift_smul,
      smul_sub]

/-- **Linear extension**: an additive, `[0,1]`-homogeneous map out of a convex
effect algebra `E` extends uniquely to a linear map out of `GP.Vec E`
(the Gudder–Pulmannová space, REC 40), with `F̃ ∘ gmap = F`. -/
noncomputable def gpLift : GP.Vec E →ₗ[ℝ] W where
  toFun := gpLiftFun F hadd hsmul
  map_add' := gpLiftFun_add F hadd hsmul
  map_smul' t x := by
    show gpLiftFun F hadd hsmul (t • x) = t • gpLiftFun F hadd hsmul x
    have hneg : ∀ y : GP.Vec E, gpLiftFun F hadd hsmul (-y) = -gpLiftFun F hadd hsmul y := by
      intro y
      have := gpLiftFun_add F hadd hsmul y (-y)
      rw [add_neg_cancel] at this
      have h0 : gpLiftFun F hadd hsmul 0 = 0 := by
        rw [GP.Vec.zero_def, gpLiftFun_mk, sub_self]
      rw [h0] at this
      exact (neg_eq_of_add_eq_zero_right this.symm).symm
    rw [GP.Vec.rsmul_def, sub_eq_add_neg, gpLiftFun_add, hneg, gpLiftFun_nnsmul,
      gpLiftFun_nnsmul, ← neg_smul, ← add_smul]
    congr 1
    rw [Real.coe_toNNReal', Real.coe_toNNReal']
    rcases le_total 0 t with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring

theorem gpLift_gmap (a : E) : gpLift F hadd hsmul (GP.gmap a) = F a := by
  show gpLiftFun F hadd hsmul (GP.Vec.mk (GP.Cone.mk 1 a) 0) = F a
  rw [gpLiftFun_mk, gpConeLift_mk, gpConeLift_zero]; simp

theorem gp_rsmul_gmap (r : ℝ≥0) (a : E) :
    (r : ℝ) • GP.gmap a = GP.Vec.pos (GP.Cone.mk r a) := by
  calc (r : ℝ) • GP.gmap a = Real.toNNReal r • GP.gmap a := GP.Vec.rsmul_nonneg r.2 _
    _ = r • GP.gmap a := by rw [Real.toNNReal_coe]
    _ = GP.Vec.pos (GP.Cone.mk r a) := by
      rw [GP.gmap, GP.Vec.pos_nnsmul, GP.Cone.smul_mk, mul_one]

/-- Every vector is `r • gmap a - s • gmap b`. -/
theorem gp_exists_repr (x : GP.Vec E) :
    ∃ (r s : ℝ) (a b : E), 0 ≤ r ∧ 0 ≤ s ∧ x = r • GP.gmap a - s • GP.gmap b := by
  induction x using GP.Vec.ind with
  | _ p q =>
    obtain ⟨r, a, rfl⟩ := GP.Cone.exists_mk p
    obtain ⟨s, b, rfl⟩ := GP.Cone.exists_mk q
    refine ⟨r, s, a, b, r.2, s.2, ?_⟩
    rw [GP.Vec.mk_eq_sub, gp_rsmul_gmap, gp_rsmul_gmap]

/-- Linear maps out of `GP.Vec E` are determined by their values on `gmap`. -/
theorem gp_linearMap_ext {f g : GP.Vec E →ₗ[ℝ] W} (h : ∀ a : E, f (GP.gmap a) = g (GP.gmap a)) :
    f = g := by
  ext x
  obtain ⟨r, s, a, b, -, -, rfl⟩ := gp_exists_repr x
  simp only [map_sub, map_smul, h]

/-- The lift of a map into the positive cone is positive. -/
theorem gpLift_nonneg [PartialOrder W] [IsOrderedAddMonoid W] [PosSMulMono ℝ W]
    (hpos : ∀ a, 0 ≤ F a) {x : GP.Vec E} (hx : 0 ≤ x) : 0 ≤ gpLift F hadd hsmul x := by
  obtain ⟨p, rfl⟩ := GP.Vec.exists_of_zero_le hx
  obtain ⟨r, a, rfl⟩ := GP.Cone.exists_mk p
  show 0 ≤ gpLiftFun F hadd hsmul (GP.Vec.mk (GP.Cone.mk r a) 0)
  rw [gpLiftFun_mk, gpConeLift_mk, gpConeLift_zero, sub_zero]
  exact smul_nonneg r.2 (hpos a)

end GPLift

/-! ## Rational homogeneity on `[0,1]_{C(X)}` -/

section CXHom

variable {X : Type u} [TopologicalSpace X] {W : Type w} [AddCommGroup W] [Module ℝ W]

/-- `c · g` in `[0,1]_{C(X)}` for `c ∈ [0,1]`. -/
noncomputable def kscale (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (g : Set.Icc (0 : C(X, ℝ)) 1) :
    Set.Icc (0 : C(X, ℝ)) 1 :=
  ⟨c • (g : C(X, ℝ)), cIcc_mem (fun x => mul_nonneg hc0 (cIcc_nonneg g x))
    (fun x => by
      show c * (g : C(X, ℝ)) x ≤ 1
      nlinarith [cIcc_nonneg g x, cIcc_le_one g x])⟩

@[simp] theorem kscale_val (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (g : Set.Icc (0 : C(X, ℝ)) 1) :
    (kscale c hc0 hc1 g : C(X, ℝ)) = c • (g : C(X, ℝ)) := rfl

variable (P : Set.Icc (0 : C(X, ℝ)) 1 → W)
  (hP : ∀ (f g : Set.Icc (0 : C(X, ℝ)) 1) (h : (f : C(X, ℝ)) + g ≤ 1),
    P ⟨(f : C(X, ℝ)) + g, cIcc_mem (fun x => add_nonneg (cIcc_nonneg f x) (cIcc_nonneg g x))
      (fun x => cIcc_perp_apply h x)⟩ = P f + P g)

include hP in
theorem kP_congr_add {f g k : Set.Icc (0 : C(X, ℝ)) 1}
    (e : (k : C(X, ℝ)) = f + g) : P k = P f + P g := by
  have h : (f : C(X, ℝ)) + g ≤ 1 := e ▸ k.2.2
  rw [← hP f g h]; congr 1; exact Subtype.ext e

include hP in
theorem kP_zero (g : Set.Icc (0 : C(X, ℝ)) 1) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hc : c = 0) :
    P (kscale c hc0 hc1 g) = 0 := by
  have e := kP_congr_add P hP (f := kscale c hc0 hc1 g) (g := kscale c hc0 hc1 g)
    (k := kscale c hc0 hc1 g) (by simp [kscale_val, hc])
  exact (left_eq_add.1 e)

include hP in
theorem kP_nat (g : Set.Icc (0 : C(X, ℝ)) 1) {n : ℕ} (hn : 0 < n) :
    ∀ (j : ℕ) (h0 : 0 ≤ (j : ℝ) / n) (h1 : (j : ℝ) / n ≤ 1),
      P (kscale ((j : ℝ) / n) h0 h1 g) = (j : ℝ) • P (kscale (1 / n) (by positivity)
        (by rw [div_le_one (by exact_mod_cast hn)]; exact_mod_cast hn) g) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  intro j
  induction j with
  | zero =>
    intro h0 h1
    rw [kP_zero P hP g h0 h1 (by simp)]
    simp
  | succ j ih =>
    intro h0 h1
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / n := by positivity
    have hj1 : (j : ℝ) / n ≤ 1 := le_trans (div_le_div_of_nonneg_right (by push_cast; linarith)
      hn'.le) h1
    rw [kP_congr_add P hP (f := kscale ((j : ℝ) / n) hj0 hj1 g)
      (g := kscale (1 / n) (by positivity) (by rw [div_le_one hn']; exact_mod_cast hn) g) ?_,
      ih hj0 hj1]
    · push_cast; rw [add_smul, one_smul]
    · simp only [kscale_val]; rw [← add_smul]; congr 1; push_cast; ring

include hP in
/-- Rational homogeneity: `P((k/n)·g) = (k/n)·P g`. -/
theorem kP_rat (g : Set.Icc (0 : C(X, ℝ)) 1) {n : ℕ} (hn : 0 < n) (k : ℕ)
    (h0 : 0 ≤ (k : ℝ) / n) (h1 : (k : ℝ) / n ≤ 1) :
    P (kscale ((k : ℝ) / n) h0 h1 g) = ((k : ℝ) / n) • P g := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hg : P g = (n : ℝ) • P (kscale (1 / n) (by positivity)
      (by rw [div_le_one hn']; exact_mod_cast hn) g) := by
    rw [← kP_nat P hP g hn n (by positivity) (by rw [div_self hn'.ne'])]
    congr 1; exact Subtype.ext (by simp [kscale_val, div_self hn'.ne'])
  rw [kP_nat P hP g hn k h0 h1, hg, _root_.smul_smul]
  congr 1; field_simp

end CXHom

/-! ## The spectral theorem for normal SEAs, in the form §5 uses it -/

section KHelpers

variable {X : Type u} [TopologicalSpace X]

/-- An element of `[0,1]_{C(X)}` from a pointwise bounded function. -/
def kmk (g : C(X, ℝ)) (h0 : ∀ t, 0 ≤ g t) (h1 : ∀ t, g t ≤ 1) : Set.Icc (0 : C(X, ℝ)) 1 :=
  ⟨g, cIcc_mem h0 h1⟩

/-- The sum in `[0,1]_{C(X)}`. -/
def kadd (f g : Set.Icc (0 : C(X, ℝ)) 1) (h : (f : C(X, ℝ)) + g ≤ 1) :
    Set.Icc (0 : C(X, ℝ)) 1 :=
  kmk ((f : C(X, ℝ)) + g) (fun t => add_nonneg (cIcc_nonneg f t) (cIcc_nonneg g t))
    (fun t => cIcc_perp_apply h t)

/-- The product in `[0,1]_{C(X)}`. -/
def kmul (f g : Set.Icc (0 : C(X, ℝ)) 1) : Set.Icc (0 : C(X, ℝ)) 1 :=
  kmk ((f : C(X, ℝ)) * g) (fun t => mul_nonneg (cIcc_nonneg f t) (cIcc_nonneg g t))
    (fun t => by
      show (f : C(X, ℝ)) t * (g : C(X, ℝ)) t ≤ 1
      nlinarith [cIcc_nonneg f t, cIcc_le_one f t, cIcc_nonneg g t, cIcc_le_one g t])

/-- The constants `0` and `1`. -/
def kzero : Set.Icc (0 : C(X, ℝ)) 1 := kmk 0 (fun _ => le_rfl) (fun _ => zero_le_one)
def kone : Set.Icc (0 : C(X, ℝ)) 1 := kmk 1 (fun _ => zero_le_one) (fun _ => le_rfl)

@[simp] theorem kmk_val (g : C(X, ℝ)) (h0 h1) : ((kmk g h0 h1 : Set.Icc (0 : C(X, ℝ)) 1) : C(X, ℝ)) = g := rfl
@[simp] theorem kadd_val (f g : Set.Icc (0 : C(X, ℝ)) 1) (h) :
    ((kadd f g h : Set.Icc (0 : C(X, ℝ)) 1) : C(X, ℝ)) = f + g := rfl
@[simp] theorem kmul_val (f g : Set.Icc (0 : C(X, ℝ)) 1) :
    ((kmul f g : Set.Icc (0 : C(X, ℝ)) 1) : C(X, ℝ)) = f * g := rfl
@[simp] theorem kzero_val : ((kzero : Set.Icc (0 : C(X, ℝ)) 1) : C(X, ℝ)) = 0 := rfl
@[simp] theorem kone_val : ((kone : Set.Icc (0 : C(X, ℝ)) 1) : C(X, ℝ)) = 1 := rfl

theorem kext {f g : Set.Icc (0 : C(X, ℝ)) 1} (h : ∀ t, (f : C(X, ℝ)) t = (g : C(X, ℝ)) t) :
    f = g := Subtype.ext (ContinuousMap.ext h)

/-- The indicator of a clopen set. -/
noncomputable def kind (V : Set X) (hV : IsClopen V) : Set.Icc (0 : C(X, ℝ)) 1 :=
  kmk ⟨V.indicator fun _ => (1 : ℝ), hV.continuous_indicator continuous_const⟩
    (fun t => Set.indicator_nonneg (fun _ _ => zero_le_one) t)
    (fun t => Set.indicator_le_self' (fun _ _ => zero_le_one) t |>.trans (le_refl 1))

theorem kind_apply (V : Set X) (hV : IsClopen V) (t : X) :
    ((kind V hV : Set.Icc (0 : C(X, ℝ)) 1) : C(X, ℝ)) t = V.indicator (fun _ => (1 : ℝ)) t := rfl

end KHelpers

section Spectral

open Papers.SEA
open scoped Papers.SEA

/-- SEA's directed completeness (SEA 11) gives REC's (REC 30; the empty set has
supremum `0`). -/
theorem dcEA_of_seaDC {F : Type u} [EffectAlgebra F] (h : Papers.SEA.DirectedComplete F) :
    DirectedCompleteEA F := by
  intro D hD
  rcases D.eq_empty_or_nonempty with hE | hne
  · subst hE
    exact ⟨0, fun x hx => hx.elim, fun u _ => ⟨u, PCM.zero_perp u, PCM.zero_ovee u⟩⟩
  · obtain ⟨x, hx1, hx2⟩ := h D ⟨hne, hD⟩
    exact ⟨x, hx1, hx2⟩

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

/-- **The spectral theorem for normal SEAs** (SEA 36, recalled in REC 58), in the
form §5 uses it: the bicommutant `{a}''` of an element is a directed-complete
commutative effect monoid (SEA 28, 32), hence (REC 34, discharged by OAP 69)
`≅ B ⊕ C(X,[0,1])` with `B` a complete Boolean algebra and `X` extremally
disconnected compact Hausdorff.  Stated as a map `Ψ : B × C(X,[0,1]) → E` which is
additive, unital, multiplicative (for `⊙`) and injective, with `a` in its range. -/
theorem spectral_rep (a : E) :
    ∃ (B : Type u) (_ : CompleteBooleanAlgebra B) (X : Type u) (_ : TopologicalSpace X)
      (_ : CompactSpace X) (_ : T2Space X) (_ : ExtremallyDisconnected X)
      (Ψ : B → Set.Icc (0 : C(X, ℝ)) 1 → E),
      (∀ (b b' : B) (f f' : Set.Icc (0 : C(X, ℝ)) 1) (_ : b ⊓ b' = ⊥)
          (hf : (f : C(X, ℝ)) + f' ≤ 1),
        ∃ h' : Perp (Ψ b f) (Ψ b' f'), Ψ (b ⊔ b') (kadd f f' hf) = ovee (Ψ b f) (Ψ b' f') h') ∧
      Ψ ⊤ kone = 1 ∧
      (∀ b b' f f', Ψ (b ⊓ b') (kmul f f') = Ψ b f ⊙ Ψ b' f') ∧
      (∀ b f b' f', Ψ b f = Ψ b' f' → b = b' ∧ f = f') ∧
      ∃ b f, Ψ b f = a := by
  set M := (bicommutantSub ({a} : Set E)).carrier
  let _ : EffectMonoid M := bicommEM {a} (singleton_commuting a)
  have hdc : DirectedCompleteEA M := dcEA_of_seaDC (bicommEM_dc {a} (singleton_commuting a))
  obtain ⟨B, iB, X, iX, hc, ht, he, ⟨φ⟩⟩ := rec34_holds M hdc
  let _ := booleanEffectMonoid B
  let _ := continuousUnitIntervalEffectMonoid X
  refine ⟨B, iB, X, iX, hc, ht, he, fun b f => (φ.inv.toFun (b, f)).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro b b' f f' _ hf
    have hp : Perp ((b, f) : B × Set.Icc (0 : C(X, ℝ)) 1) (b', f') := ⟨‹_›, hf⟩
    exact ⟨φ.inv.perp_map hp, congrArg Subtype.val (φ.inv.ovee_map hp)⟩
  · exact congrArg Subtype.val φ.inv.map_one
  · intro b b' f f'
    exact congrArg Subtype.val (φ.inv.map_mul (b, f) (b', f'))
  · intro b f b' f' h
    have := congrArg φ.hom.toFun (Subtype.ext h : φ.inv.toFun (b, f) = φ.inv.toFun (b', f'))
    rw [φ.hom_inv, φ.hom_inv] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · refine ⟨(φ.hom.toFun ⟨a, subset_bicommutant _ rfl⟩).1,
      (φ.hom.toFun ⟨a, subset_bicommutant _ rfl⟩).2, ?_⟩
    show (φ.inv.toFun (φ.hom.toFun ⟨a, _⟩)).1 = a
    rw [φ.inv_hom]

variable [EffectModule I E] (hsm : ∀ (a b : E) (l : I), a ⊙ (l • b) = l • (a ⊙ b))

theorem ULin_hadd (q : E) {a b : E} (h : Perp a b) :
    GP.gmap (q ⊙ ovee a b h) = GP.gmap (q ⊙ a) + GP.gmap (q ⊙ b) := by
  obtain ⟨h', e⟩ := seq_ovee q h; rw [e, GP.gmap_ovee]

include hsm in
theorem ULin_hsmul (q : E) (l : I) (b : E) :
    GP.gmap (q ⊙ (l • b)) = (l : ℝ) • GP.gmap (q ⊙ b) := by
  rw [hsm, GP.gmap_smul]

/-- The operator `b ↦ q & b`, extended linearly to `V = GP.Vec E`. -/
noncomputable def ULin (q : E) : GP.Vec E →ₗ[ℝ] GP.Vec E :=
  gpLift (fun b => GP.gmap (q ⊙ b)) (ULin_hadd q) (ULin_hsmul hsm q)

theorem ULin_gmap (q b : E) : ULin hsm q (GP.gmap b) = GP.gmap (q ⊙ b) :=
  gpLift_gmap _ (ULin_hadd q) (ULin_hsmul hsm q) b

omit [NormalSEA E] in
theorem gmap_mono {a b : E} (h : a ≼ b) : GP.gmap a ≤ GP.gmap b := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [GP.gmap_ovee hc]; exact le_add_of_nonneg_right (GP.gmap_nonneg c)

omit [NormalSEA E] in
/-- Every vector is `2N·gmap a - N·1` for some `N > 0` and effect `a`. -/
theorem gp_affine_repr (y : GP.Vec E) :
    ∃ (N : ℝ) (a : E), 0 < N ∧ y = (2 * N) • GP.gmap a - N • GP.gunit := by
  obtain ⟨n, hn1, hn2⟩ := Papers.OAP.oap58_orderUnit y
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = n + 1 := ⟨_, rfl⟩
  have hN : 0 < N := by rw [hNdef]; positivity
  have hnN : (n : ℝ) • (GP.gunit : GP.Vec E) ≤ N • GP.gunit :=
    ou_smul_unit_mono (X := GP.Vec E) (by linarith)
  have h1 : -(N • (GP.gunit : GP.Vec E)) ≤ y := (neg_le_neg hnN).trans hn1
  have h2 : y ≤ N • (GP.gunit : GP.Vec E) := hn2.trans hnN
  set v : GP.Vec E := (2 * N)⁻¹ • (y + N • GP.gunit) with hv
  have hv0 : 0 ≤ v := smul_nonneg (by positivity) (by
    have := add_le_add_left h1 (N • GP.gunit); rwa [neg_add_cancel] at this)
  have hv1 : v ≤ GP.gunit := by
    have : y + N • (GP.gunit : GP.Vec E) ≤ (2 * N) • GP.gunit := by
      calc y + N • (GP.gunit : GP.Vec E) ≤ N • GP.gunit + N • GP.gunit := add_le_add_left h2 _
        _ = (2 * N) • GP.gunit := by rw [two_mul, add_smul]
    calc v ≤ (2 * N)⁻¹ • ((2 * N) • (GP.gunit : GP.Vec E)) :=
          smul_le_smul_of_nonneg_left this (by positivity)
      _ = GP.gunit := by rw [_root_.smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  obtain ⟨a, ha⟩ := GP.gmap_surjective_Icc (E := E) ⟨hv0, hv1⟩
  refine ⟨N, a, hN, ?_⟩
  rw [ha, hv, _root_.smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  abel

end Spectral


/-! ### Computations with a spectral representation -/

section SpecCalc

open Papers.SEA
open scoped Papers.SEA

variable {E : Type u} [EffectAlgebra E] [NormalSEA E] [EffectModule I E]
  (hsm : ∀ (a b : E) (l : I), a ⊙ (l • b) = l • (a ⊙ b))
  {B : Type u} [CompleteBooleanAlgebra B] {X : Type u} [TopologicalSpace X]
  (Ψ : B → Set.Icc (0 : C(X, ℝ)) 1 → E)
  (hadd : ∀ (b b' : B) (f f' : Set.Icc (0 : C(X, ℝ)) 1) (_ : b ⊓ b' = ⊥)
    (hf : (f : C(X, ℝ)) + f' ≤ 1),
    ∃ h' : Perp (Ψ b f) (Ψ b' f'), Ψ (b ⊔ b') (kadd f f' hf) = ovee (Ψ b f) (Ψ b' f') h')
  (hmul : ∀ b b' f f', Ψ (b ⊓ b') (kmul f f') = Ψ b f ⊙ Ψ b' f')

include hadd in
theorem spec_G_add {b b' : B} {f f' k : Set.Icc (0 : C(X, ℝ)) 1} (hb : b ⊓ b' = ⊥)
    (hk : ∀ t, (k : C(X, ℝ)) t = (f : C(X, ℝ)) t + (f' : C(X, ℝ)) t) :
    GP.gmap (Ψ (b ⊔ b') k) = GP.gmap (Ψ b f) + GP.gmap (Ψ b' f') := by
  have hf : (f : C(X, ℝ)) + f' ≤ 1 := fun t => by
    have := cIcc_le_one k t; rw [hk] at this; exact this
  obtain ⟨h', e⟩ := hadd b b' f f' hb hf
  have hk' : k = kadd f f' hf := kext fun t => by rw [hk]; rfl
  rw [hk', e, GP.gmap_ovee]

include hadd in
theorem spec_zero : Ψ ⊥ kzero = 0 := by
  obtain ⟨h', e⟩ := hadd ⊥ ⊥ kzero kzero (inf_idem _) (fun t => by simp)
  have hk : kadd (kzero : Set.Icc (0 : C(X, ℝ)) 1) kzero (fun t => by simp) = kzero :=
    kext fun t => by simp [kadd, kmk, kzero]
  rw [hk, sup_idem] at e
  exact eq_zero_of_ovee_self h' e.symm

include hadd in
theorem spec_G_bot_mono {f f' : Set.Icc (0 : C(X, ℝ)) 1}
    (h : ∀ t, (f : C(X, ℝ)) t ≤ (f' : C(X, ℝ)) t) :
    GP.gmap (Ψ ⊥ f) ≤ GP.gmap (Ψ ⊥ f') := by
  let d : Set.Icc (0 : C(X, ℝ)) 1 := kmk ((f' : C(X, ℝ)) - f) (fun t => by simp [h t])
    (fun t => by have := cIcc_le_one f' t; have := cIcc_nonneg f t; simp; linarith)
  have e := spec_G_add Ψ hadd (b := ⊥) (b' := ⊥) (f := f) (f' := d) (k := f') (inf_idem _)
    (fun t => by simp [d])
  rw [sup_idem] at e
  rw [e]; exact le_add_of_nonneg_right (GP.gmap_nonneg _)

include hadd in
theorem spec_G_rat (g : Set.Icc (0 : C(X, ℝ)) 1) {n : ℕ} (hn : 0 < n) (k : ℕ)
    (h0 : 0 ≤ (k : ℝ) / n) (h1 : (k : ℝ) / n ≤ 1) :
    GP.gmap (Ψ ⊥ (kscale ((k : ℝ) / n) h0 h1 g)) = ((k : ℝ) / n) • GP.gmap (Ψ ⊥ g) :=
  kP_rat (fun g => GP.gmap (Ψ ⊥ g)) (fun f f' hf => by
    have := spec_G_add Ψ hadd (b := ⊥) (b' := ⊥) (f := f) (f' := f')
      (k := kadd f f' hf) (inf_idem _) (fun t => rfl)
    rwa [sup_idem] at this) g hn k h0 h1

include hmul in
theorem spec_ULin (b b' : B) (f f' : Set.Icc (0 : C(X, ℝ)) 1) :
    ULin hsm (Ψ b f) (GP.gmap (Ψ b' f')) = GP.gmap (Ψ (b ⊓ b') (kmul f f')) := by
  rw [ULin_gmap, hmul]

include hmul in
theorem spec_idem {b : B} {f : Set.Icc (0 : C(X, ℝ)) 1} (hf : kmul f f = f) :
    Papers.SEA.IsIdempotent (Ψ b f) := by
  show Ψ b f ⊙ Ψ b f = Ψ b f
  rw [← hmul, inf_idem, hf]

include hadd hmul in
/-- The core of the "negative part" argument of REC 120's proof, for an element
`y = 2N·Ψ(b,f) - N·1` of `V`. -/
theorem spectral_neg_core [CompactSpace X] (hED : ExtremallyDisconnected X)
    (hone : Ψ ⊤ kone = 1)
    (hinj : ∀ b f b' f', Ψ b f = Ψ b' f' → b = b' ∧ f = f')
    {N : ℝ} (hN : 0 < N) (b : B) (f : Set.Icc (0 : C(X, ℝ)) 1)
    (hy : ¬ 0 ≤ (2 * N) • GP.gmap (Ψ b f) - N • GP.gunit) :
    ∃ q : E, Papers.SEA.IsIdempotent q ∧ q ≠ 0 ∧ ∃ (x z : GP.Vec E) (β : ℝ),
      0 ≤ x ∧ 0 ≤ z ∧ 0 < β ∧ (2 * N) • GP.gmap (Ψ b f) - N • GP.gunit = x - z ∧
      ULin hsm q x = 0 ∧ β • GP.gmap q ≤ ULin hsm q z ∧ z ≤ (4 * β) • GP.gunit := by
  set G : B → Set.Icc (0 : C(X, ℝ)) 1 → GP.Vec E := fun b f => GP.gmap (Ψ b f) with hG
  have hGadd := fun {b b' f f' k} hb hk => spec_G_add (E := E) Ψ hadd (b := b) (b' := b')
    (f := f) (f' := f') (k := k) hb hk
  have hG0 : G ⊥ kzero = 0 := by simp only [hG]; rw [spec_zero Ψ hadd, GP.gmap_zero]
  have hGnn : ∀ b f, 0 ≤ G b f := fun b f => GP.gmap_nonneg _
  -- auxiliary functions
  let half : Set.Icc (0 : C(X, ℝ)) 1 := kmk (ContinuousMap.const X (1 / 2 : ℝ))
    (fun t => by norm_num) (fun t => by norm_num)
  let w : Set.Icc (0 : C(X, ℝ)) 1 := kmk ((ContinuousMap.const X (1 / 2 : ℝ) - f) ⊔ 0)
    (fun t => by simp) (fun t => by
      have := cIcc_nonneg f t; simp only [ContinuousMap.sup_apply, ContinuousMap.sub_apply,
        ContinuousMap.const_apply, ContinuousMap.zero_apply]
      exact max_le (by linarith) zero_le_one)
  let u' : Set.Icc (0 : C(X, ℝ)) 1 := kmk (((f : C(X, ℝ)) - ContinuousMap.const X (1 / 2 : ℝ)) ⊔ 0)
    (fun t => by simp) (fun t => by
      have := cIcc_le_one f t; simp only [ContinuousMap.sup_apply, ContinuousMap.sub_apply,
        ContinuousMap.const_apply, ContinuousMap.zero_apply]
      exact max_le (by linarith) zero_le_one)
  let mx : Set.Icc (0 : C(X, ℝ)) 1 := kmk ((f : C(X, ℝ)) ⊔ ContinuousMap.const X (1 / 2 : ℝ))
    (fun t => le_max_of_le_right (by norm_num)) (fun t => max_le (cIcc_le_one f t) (by norm_num))
  have hw : ∀ t, (w : C(X, ℝ)) t = max (1 / 2 - (f : C(X, ℝ)) t) 0 := fun t => by simp [w]
  have hu : ∀ t, (u' : C(X, ℝ)) t = max ((f : C(X, ℝ)) t - 1 / 2) 0 := fun t => by simp [u']
  have hhalf : ∀ t, (half : C(X, ℝ)) t = 1 / 2 := fun t => by simp [half]
  have hmx : ∀ t, (mx : C(X, ℝ)) t = max ((f : C(X, ℝ)) t) (1 / 2) := fun t => by simp [mx]
  -- the identities in `V`
  have e1 : G b f = G b kzero + G ⊥ f := by
    have := hGadd (b := b) (b' := ⊥) (f := kzero) (f' := f) (k := f) (inf_bot_eq _) (fun t => by simp)
    rwa [sup_bot_eq] at this
  have e2 : G ⊥ f + G ⊥ w = G ⊥ half + G ⊥ u' := by
    have ha := hGadd (b := ⊥) (b' := ⊥) (f := f) (f' := w) (k := mx) (inf_idem _) (fun t => by
      rw [hmx, hw]; rcases le_total ((f : C(X, ℝ)) t) (1 / 2) with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring)
    have hb := hGadd (b := ⊥) (b' := ⊥) (f := half) (f' := u') (k := mx) (inf_idem _) (fun t => by
      rw [hmx, hu, hhalf]; rcases le_total ((f : C(X, ℝ)) t) (1 / 2) with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]; ring
      · rw [max_eq_left h, max_eq_left (by linarith)]; ring)
    rw [sup_idem] at ha hb
    exact ha.symm.trans hb
  have e3 : G ⊥ kone = G ⊥ half + G ⊥ half := by
    have := hGadd (b := ⊥) (b' := ⊥) (f := half) (f' := half) (k := kone) (inf_idem _)
      (fun t => by rw [hhalf]; simp; norm_num)
    rwa [sup_idem] at this
  have e4 : GP.gunit = G b kzero + G bᶜ kzero + G ⊥ kone := by
    have h1 := hGadd (b := b) (b' := bᶜ) (f := kzero) (f' := kzero) (k := kzero) (inf_compl_eq_bot)
      (fun t => by simp)
    have h2 := hGadd (b := ⊤) (b' := ⊥) (f := kzero) (f' := kone) (k := kone) (inf_bot_eq _)
      (fun t => by simp)
    rw [sup_compl_eq_top] at h1
    rw [sup_bot_eq] at h2
    have : GP.gunit = G ⊤ kone := by simp only [hG]; rw [hone]; rfl
    rw [this]; simp only [hG]; rw [h2, h1]
  set x : GP.Vec E := N • G b kzero + (2 * N) • G ⊥ u' with hx
  set z : GP.Vec E := N • G bᶜ kzero + (2 * N) • G ⊥ w with hz
  have hyxz : (2 * N) • G b f - N • GP.gunit = x - z := by
    have e2' : G ⊥ f = G ⊥ half + G ⊥ u' - G ⊥ w := by rw [← e2]; abel
    rw [e1, e4, e2', e3, hx, hz]; module
  have hx0 : 0 ≤ x := add_nonneg (smul_nonneg hN.le (hGnn _ _)) (smul_nonneg (by positivity) (hGnn _ _))
  have hz0 : 0 ≤ z := add_nonneg (smul_nonneg hN.le (hGnn _ _)) (smul_nonneg (by positivity) (hGnn _ _))
  have hGw_half : G ⊥ w ≤ G ⊥ half := spec_G_bot_mono Ψ hadd fun t => by
    rw [hw, hhalf]; have := cIcc_nonneg f t; exact max_le (by linarith) (by norm_num)
  have hGone_le : G ⊥ kone ≤ GP.gunit := by
    rw [e4]; exact le_add_of_nonneg_left (add_nonneg (hGnn _ _) (hGnn _ _))
  by_cases hbc : bᶜ = ⊥
  · -- Case B: the Boolean part is `⊤`; the negative part lives in `C(X)`
    have hbt : b = ⊤ := compl_eq_bot.1 hbc
    have hz' : z = (2 * N) • G ⊥ w := by rw [hz, hbc, hG0, smul_zero, zero_add]
    have hwne : ∃ t₁, 0 < (w : C(X, ℝ)) t₁ := by
      by_contra hcon
      push Not at hcon
      have hw0 : w = kzero := kext fun t => le_antisymm (hcon t) (cIcc_nonneg w t)
      apply hy
      rw [show (2 * N) • GP.gmap (Ψ b f) = (2 * N) • G b f from rfl, hyxz, hz', hw0, hG0,
        smul_zero, sub_zero]
      exact hx0
    obtain ⟨t₁, ht₁⟩ := hwne
    obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMaxOn ⟨t₁, Set.mem_univ _⟩
      (w : C(X, ℝ)).continuous.continuousOn
    set m := (w : C(X, ℝ)) t₀ with hm
    have hmax : ∀ t, (w : C(X, ℝ)) t ≤ m := fun t => ht₀ (Set.mem_univ t)
    have hm0 : 0 < m := lt_of_lt_of_le ht₁ (hmax t₁)
    have hm1 : m ≤ 1 / 2 := by
      rw [hm, hw]; have := cIcc_nonneg f t₀; exact max_le (by linarith) (by norm_num)
    set k : ℕ := ⌈2 / m⌉₊ with hk
    have hk1 : 2 / m ≤ (k : ℝ) := Nat.le_ceil _
    have hk2 : (k : ℝ) < 2 / m + 1 := Nat.ceil_lt_add_one (by positivity)
    have hk4 : (4 : ℝ) ≤ k := le_trans (by rw [le_div_iff₀ hm0]; linarith) hk1
    have hkpos : 0 < k := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hk4 : (0 : ℝ) < k)
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hlev : 1 / (k : ℝ) < m := by
      rw [div_lt_iff₀ hkR]
      have : 2 ≤ m * k := by rw [div_le_iff₀ hm0] at hk1; linarith
      linarith
    have hup : m ≤ 4 / (k : ℝ) := by
      rw [le_div_iff₀ hkR]
      have : (k : ℝ) * m < 2 + m := by
        have := mul_lt_mul_of_pos_right hk2 hm0
        rwa [add_mul, div_mul_cancel₀ _ hm0.ne', one_mul] at this
      linarith
    -- the clopen set where `w ≥ 1/k`
    set V : Set X := closure {t | 1 / (k : ℝ) < (w : C(X, ℝ)) t} with hVdef
    have hVc : IsClopen V := ⟨isClosed_closure,
      hED.open_closure _ (isOpen_lt continuous_const (w : C(X, ℝ)).continuous)⟩
    have hVw : ∀ t ∈ V, 1 / (k : ℝ) ≤ (w : C(X, ℝ)) t := fun t ht =>
      closure_minimal (fun s hs => le_of_lt hs)
        (isClosed_le continuous_const (w : C(X, ℝ)).continuous) ht
    have ht₀V : t₀ ∈ V := subset_closure hlev
    set χ := kind V hVc
    have hχ : ∀ t, (χ : C(X, ℝ)) t = V.indicator (fun _ => (1 : ℝ)) t := fun t => rfl
    have hχχ : kmul χ χ = χ := kext fun t => by
      simp only [kmul_val, ContinuousMap.mul_apply, hχ]
      by_cases ht : t ∈ V <;> simp [ht]
    refine ⟨Ψ ⊥ χ, spec_idem Ψ hmul hχχ, fun h0 => ?_, x, z, 2 * N / k, hx0, hz0,
      by positivity, hyxz, ?_, ?_, ?_⟩
    · have := (hinj ⊥ χ ⊥ kzero (h0.trans (spec_zero Ψ hadd).symm)).2
      have h1 := congrArg (fun g : Set.Icc (0 : C(X, ℝ)) 1 => (g : C(X, ℝ)) t₀) this
      simp only [hχ, Set.indicator_of_mem ht₀V, kzero_val, ContinuousMap.zero_apply] at h1
      exact one_ne_zero h1
    · have hχu : kmul χ u' = kzero := kext fun t => by
        simp only [kmul_val, ContinuousMap.mul_apply, hχ, kzero_val, ContinuousMap.zero_apply]
        by_cases ht : t ∈ V
        · rw [Set.indicator_of_mem ht, hu]
          have h1 := hVw t ht
          rw [hw] at h1
          have : (f : C(X, ℝ)) t < 1 / 2 := by
            by_contra hc; push Not at hc
            rw [max_eq_right (by linarith)] at h1
            exact absurd h1 (not_le.2 (by positivity))
          rw [max_eq_right (by linarith)]; ring
        · rw [Set.indicator_of_notMem ht]; ring
      have hχ0 : kmul χ kzero = kzero := kext fun t => by simp
      rw [hx, map_add, map_smul, map_smul, spec_ULin hsm Ψ hmul, spec_ULin hsm Ψ hmul, hχu, hχ0,
        bot_inf_eq, inf_idem, hG0] at *
      simp only [spec_zero Ψ hadd, GP.gmap_zero, smul_zero, add_zero]
    · have hle : ∀ t, (kscale (((1 : ℕ) : ℝ) / (k : ℝ)) (by positivity)
          (by rw [div_le_one hkR]; push_cast; linarith) χ : C(X, ℝ)) t ≤ (kmul χ w : C(X, ℝ)) t := by
        intro t
        simp only [kscale_val, kmul_val, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
          hχ, smul_eq_mul]
        by_cases ht : t ∈ V
        · rw [Set.indicator_of_mem ht, mul_one, one_mul]; push_cast; exact hVw t ht
        · rw [Set.indicator_of_notMem ht]; simp
      have h1 := spec_G_bot_mono Ψ hadd hle
      rw [spec_G_rat Ψ hadd χ hkpos 1] at h1
      rw [hz', map_smul, spec_ULin hsm Ψ hmul, inf_idem]
      calc (2 * N / k) • GP.gmap (Ψ ⊥ χ) = (2 * N) • ((((1 : ℕ) : ℝ) / k) • GP.gmap (Ψ ⊥ χ)) := by
            rw [_root_.smul_smul]; congr 1; push_cast; ring
        _ ≤ (2 * N) • GP.gmap (Ψ ⊥ (kmul χ w)) := smul_le_smul_of_nonneg_left h1 (by positivity)
    · have hle : ∀ t, (w : C(X, ℝ)) t ≤ ((kscale ((4 : ℕ) / (k : ℝ)) (by positivity)
          (by rw [div_le_one hkR]; exact_mod_cast hk4) kone : Set.Icc (0 : C(X, ℝ)) 1) :
            C(X, ℝ)) t := by
        intro t
        simp only [kscale_val, ContinuousMap.smul_apply, kone_val, ContinuousMap.one_apply,
          smul_eq_mul, mul_one]
        push_cast
        exact (hmax t).trans hup
      have h1 := spec_G_bot_mono Ψ hadd hle
      rw [spec_G_rat Ψ hadd kone hkpos 4] at h1
      rw [hz']
      calc (2 * N) • G ⊥ w ≤ (2 * N) • ((((4 : ℕ) : ℝ) / k) • G ⊥ kone) :=
            smul_le_smul_of_nonneg_left h1 (by positivity)
        _ ≤ (2 * N) • ((((4 : ℕ) : ℝ) / k) • GP.gunit) :=
            smul_le_smul_of_nonneg_left (smul_le_smul_of_nonneg_left hGone_le (by positivity))
              (by positivity)
        _ = (4 * (2 * N / k)) • GP.gunit := by rw [_root_.smul_smul]; congr 1; push_cast; ring
  · -- Case A: the Boolean part `bᶜ` is non-zero
    refine ⟨Ψ bᶜ kzero, spec_idem Ψ hmul (kext fun t => by simp), fun h0 => hbc ?_, x, z, N, hx0,
      hz0, hN, hyxz, ?_, ?_, ?_⟩
    · exact (hinj _ _ _ _ (h0.trans (spec_zero Ψ hadd).symm)).1
    · have h00 : ∀ g : Set.Icc (0 : C(X, ℝ)) 1, kmul kzero g = (kzero : Set.Icc (0 : C(X, ℝ)) 1) :=
        fun g => kext fun t => by simp
      rw [hx, map_add, map_smul, map_smul, spec_ULin hsm Ψ hmul, spec_ULin hsm Ψ hmul, h00, h00,
        compl_inf_self, inf_bot_eq]
      show N • G ⊥ kzero + (2 * N) • G ⊥ kzero = 0
      simp only [hG0, smul_zero, add_zero]
    · have h00 : ∀ g : Set.Icc (0 : C(X, ℝ)) 1, kmul kzero g = (kzero : Set.Icc (0 : C(X, ℝ)) 1) :=
        fun g => kext fun t => by simp
      rw [hz, map_add, map_smul, map_smul, spec_ULin hsm Ψ hmul, spec_ULin hsm Ψ hmul, h00, h00,
        inf_idem, inf_bot_eq]
      show N • G bᶜ kzero ≤ N • G bᶜ kzero + (2 * N) • G ⊥ kzero
      simp only [hG0, smul_zero, add_zero, le_refl]
    · calc z = N • G bᶜ kzero + (2 * N) • G ⊥ w := rfl
        _ ≤ N • G bᶜ kzero + (2 * N) • G ⊥ half :=
            add_le_add_right (smul_le_smul_of_nonneg_left hGw_half (by positivity)) _
        _ = N • (G bᶜ kzero + G ⊥ kone) := by rw [e3]; module
        _ ≤ N • GP.gunit := by
            refine smul_le_smul_of_nonneg_left ?_ hN.le
            rw [e4, add_assoc]; exact le_add_of_nonneg_left (hGnn _ _)
        _ ≤ (4 * N) • GP.gunit := by
            refine ou_smul_unit_mono (X := GP.Vec E) (by linarith)

end SpecCalc


section SpecDense

open Papers.SEA
open scoped Papers.SEA

theorem list_range_map_sum {W : Type w} [AddCommMonoid W] (g : ℕ → W) (n : ℕ) :
    ((List.range n).map g).sum = ∑ j ∈ Finset.range n, g j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

variable {E : Type u} [EffectAlgebra E] [NormalSEA E] [EffectModule I E]
  {B : Type u} [CompleteBooleanAlgebra B] {X : Type u} [TopologicalSpace X]
  (Ψ : B → Set.Icc (0 : C(X, ℝ)) 1 → E)
  (hadd : ∀ (b b' : B) (f f' : Set.Icc (0 : C(X, ℝ)) 1) (_ : b ⊓ b' = ⊥)
    (hf : (f : C(X, ℝ)) + f' ≤ 1),
    ∃ h' : Perp (Ψ b f) (Ψ b' f'), Ψ (b ⊔ b') (kadd f f' hf) = ovee (Ψ b f) (Ψ b' f') h')
  (hmul : ∀ b b' f f', Ψ (b ⊓ b') (kmul f f') = Ψ b f ⊙ Ψ b' f')

include hadd hmul in
/-- The core of the density of sharp combinations (REC 58, used by REC 121):
`2N·Ψ(b,f) - N·1` is within `2N/n` of a combination of idempotents, by the
level sets `closure {f > j/n}` (clopen, as `X` is extremally disconnected). -/
theorem spectral_dense_core (hED : ExtremallyDisconnected X) (hone : Ψ ⊤ kone = 1)
    {N : ℝ} (hN : 0 < N) (b : B) (f : Set.Icc (0 : C(X, ℝ)) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (ℝ × E), (∀ p ∈ l, Papers.SEA.IsIdempotent p.2) ∧
      ousNorm (GP.Vec E) ((2 * N) • GP.gmap (Ψ b f) - N • GP.gunit -
        (l.map fun p => p.1 • GP.gmap p.2).sum) < ε := by
  set G : B → Set.Icc (0 : C(X, ℝ)) 1 → GP.Vec E := fun b f => GP.gmap (Ψ b f) with hG
  have hGadd := fun {b b' f f' k} hb hk => spec_G_add (E := E) Ψ hadd (b := b) (b' := b')
    (f := f) (f' := f') (k := k) hb hk
  have hG0 : G ⊥ kzero = 0 := by simp only [hG]; rw [spec_zero Ψ hadd, GP.gmap_zero]
  have hGnn : ∀ b f, 0 ≤ G b f := fun b f => GP.gmap_nonneg _
  -- choose `n` with `2N/n < ε`
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * N / ε)
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnε : 2 * N / n < ε := by
    rw [div_lt_iff₀ hnR]; rw [div_lt_iff₀ hε] at hn; linarith
  -- partial sums `S j = min(f, j/n)` and layers
  let S : ℕ → Set.Icc (0 : C(X, ℝ)) 1 := fun j =>
    kmk ((f : C(X, ℝ)) ⊓ ContinuousMap.const X ((j : ℝ) / n))
      (fun t => le_min (cIcc_nonneg f t) (by simp; positivity))
      (fun t => min_le_of_left_le (cIcc_le_one f t))
  have hS : ∀ j t, (S j : C(X, ℝ)) t = min ((f : C(X, ℝ)) t) ((j : ℝ) / n) := fun j t => by
    simp [S]
  have hSmono : ∀ j t, (S j : C(X, ℝ)) t ≤ (S (j + 1) : C(X, ℝ)) t := fun j t => by
    rw [hS, hS]; exact min_le_min_left _ (div_le_div_of_nonneg_right (by push_cast; linarith)
      hnR.le)
  let L : ℕ → Set.Icc (0 : C(X, ℝ)) 1 := fun j =>
    kmk ((S (j + 1) : C(X, ℝ)) - S j) (fun t => by simp only [ContinuousMap.sub_apply]; linarith [hSmono j t])
      (fun t => by
        simp only [ContinuousMap.sub_apply]
        have := cIcc_le_one (S (j + 1)) t; have := cIcc_nonneg (S j) t; linarith)
  have hL : ∀ j t, (L j : C(X, ℝ)) t = (S (j + 1) : C(X, ℝ)) t - (S j : C(X, ℝ)) t :=
    fun j t => rfl
  -- the clopen level sets
  have hWc : ∀ j : ℕ, IsClopen (closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t}) := fun j =>
    ⟨isClosed_closure, hED.open_closure _ (isOpen_lt continuous_const (f : C(X, ℝ)).continuous)⟩
  have hWf : ∀ j : ℕ, ∀ t ∈ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t},
      (j : ℝ) / n ≤ (f : C(X, ℝ)) t := fun j t ht =>
    closure_minimal (fun s hs => le_of_lt hs) (isClosed_le continuous_const
      (f : C(X, ℝ)).continuous) ht
  have hWn : ∀ j : ℕ, ∀ t ∉ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t},
      (f : C(X, ℝ)) t ≤ (j : ℝ) / n := fun j t ht => by
    by_contra hc; push Not at hc; exact ht (subset_closure hc)
  let χ : ℕ → Set.Icc (0 : C(X, ℝ)) 1 := fun j => kind _ (hWc j)
  have hχ : ∀ j t, (χ j : C(X, ℝ)) t =
      (closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t}).indicator (fun _ => (1 : ℝ)) t :=
    fun j t => rfl
  have hn1 : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) / n := by positivity
  have hn2 : ((1 : ℕ) : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hnpos
  -- bounds on the layers
  have hup : ∀ j, G ⊥ (L j) ≤ (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j) := by
    intro j
    rw [← spec_G_rat Ψ hadd (χ j) hnpos 1 hn1 hn2]
    refine spec_G_bot_mono Ψ hadd fun t => ?_
    simp only [kscale_val, ContinuousMap.smul_apply, smul_eq_mul, hχ, hL, hS]
    by_cases ht : t ∈ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t}
    · rw [Set.indicator_of_mem ht, mul_one]
      have h1 := min_le_right ((f : C(X, ℝ)) t) (((j + 1 : ℕ) : ℝ) / n)
      have h2 := hWf j t ht
      rw [min_eq_right h2]; push_cast at h1 ⊢
      have : ((j : ℝ) + 1) / n = (j : ℝ) / n + 1 / n := by ring
      linarith
    · rw [Set.indicator_of_notMem ht, mul_zero]
      have h2 := hWn j t ht
      rw [min_eq_left h2, min_eq_left (h2.trans (div_le_div_of_nonneg_right (by push_cast; linarith)
        hnR.le))]; simp
  have hlow : ∀ j, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ (j + 1)) ≤ G ⊥ (L j) := by
    intro j
    rw [← spec_G_rat Ψ hadd (χ (j + 1)) hnpos 1 hn1 hn2]
    refine spec_G_bot_mono Ψ hadd fun t => ?_
    simp only [kscale_val, ContinuousMap.smul_apply, smul_eq_mul, hχ, hL, hS]
    by_cases ht : t ∈ closure {t | ((j + 1 : ℕ) : ℝ) / n < (f : C(X, ℝ)) t}
    · rw [Set.indicator_of_mem ht, mul_one]
      have h2 := hWf (j + 1) t ht
      rw [min_eq_right h2, min_eq_right ((div_le_div_of_nonneg_right (by push_cast; linarith)
        hnR.le).trans h2)]
      push_cast; ring_nf; rfl
    · rw [Set.indicator_of_notMem ht, mul_zero]
      linarith [hSmono j t, hS j t, hS (j + 1) t]
  -- `G ⊥ f` is the sum of the layers
  have hsum : ∀ m, G ⊥ (S m) = ∑ j ∈ Finset.range m, G ⊥ (L j) := by
    intro m
    induction m with
    | zero =>
      rw [Finset.sum_range_zero]
      have : S 0 = kzero := kext fun t => by
        rw [hS]; simp [min_eq_right (cIcc_nonneg f t)]
      rw [this, hG0]
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      have := hGadd (b := ⊥) (b' := ⊥) (f := S m) (f' := L m) (k := S (m + 1)) (inf_idem _)
        (fun t => by rw [hL]; ring)
      rwa [sup_idem] at this
  have hSn : S n = f := kext fun t => by
    rw [hS, div_self hnR.ne']; exact min_eq_left (cIcc_le_one f t)
  have hGf : G ⊥ f = ∑ j ∈ Finset.range n, G ⊥ (L j) := by rw [← hSn]; exact hsum n
  set T : GP.Vec E := ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j) with hT
  have hfT : G ⊥ f ≤ T := by rw [hGf]; exact Finset.sum_le_sum fun j _ => hup j
  have hGone : G ⊥ kone ≤ GP.gunit := by
    have := hGadd (b := ⊤) (b' := ⊥) (f := kzero) (f' := kone) (k := kone) (inf_bot_eq _)
      (fun t => by simp)
    rw [sup_bot_eq] at this
    have hu : GP.gunit = G ⊤ kone := by simp only [hG]; rw [hone]; rfl
    rw [hu]; simp only [hG]; rw [this]; exact le_add_of_nonneg_left (GP.gmap_nonneg _)
  have hTf : T - (((1 : ℕ) : ℝ) / n) • GP.gunit ≤ G ⊥ f := by
    have h1 : ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ (j + 1)) ≤ G ⊥ f := by
      rw [hGf]; exact Finset.sum_le_sum fun j _ => hlow j
    have h2 : ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ (j + 1)) =
        T - (((1 : ℕ) : ℝ) / n) • G ⊥ (χ 0) + (((1 : ℕ) : ℝ) / n) • G ⊥ (χ n) := by
      rw [hT]
      have := Finset.sum_range_succ' (fun j => (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j)) n
      have h3 := Finset.sum_range_succ (fun j => (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j)) n
      rw [this] at h3
      rw [eq_sub_of_add_eq h3.symm]; abel
    have h4 : G ⊥ (χ 0) ≤ G ⊥ kone := spec_G_bot_mono Ψ hadd fun t => cIcc_le_one _ t
    calc T - (((1 : ℕ) : ℝ) / n) • GP.gunit ≤ T - (((1 : ℕ) : ℝ) / n) • G ⊥ (χ 0) :=
          sub_le_sub_left (smul_le_smul_of_nonneg_left (h4.trans hGone) hn1) _
      _ ≤ T - (((1 : ℕ) : ℝ) / n) • G ⊥ (χ 0) + (((1 : ℕ) : ℝ) / n) • G ⊥ (χ n) :=
          le_add_of_nonneg_right (smul_nonneg hn1 (hGnn _ _))
      _ = _ := h2.symm
      _ ≤ G ⊥ f := h1
  -- the approximating combination
  refine ⟨[((2 * N), Ψ b kzero), (-N, 1)] ++
      (List.range n).map (fun j => (2 * N * (((1 : ℕ) : ℝ) / n), Ψ ⊥ (χ j))), ?_, ?_⟩
  · intro p hp
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range] at hp
    rcases hp with (rfl | rfl | h) | ⟨j, -, rfl⟩
    · exact spec_idem Ψ hmul (kext fun t => by simp)
    · exact Papers.SEA.isIdempotent_one
    · exact absurd h List.not_mem_nil
    · exact spec_idem Ψ hmul (kext fun t => by
        simp only [kmul_val, ContinuousMap.mul_apply, hχ]
        by_cases ht : t ∈ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t} <;> simp [ht])
  · have hsumL : (([((2 * N), Ψ b kzero), (-N, 1)] ++
        (List.range n).map (fun j => (2 * N * (((1 : ℕ) : ℝ) / n), Ψ ⊥ (χ j)))).map
          fun p : ℝ × E => p.1 • GP.gmap p.2).sum =
        (2 * N) • G b kzero - N • GP.gunit + (2 * N) • T := by
      rw [List.map_append, List.sum_append, List.map_map, list_range_map_sum, hT,
        Finset.smul_sum]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_def,
        _root_.smul_smul, neg_smul]
      rw [add_zero, ← sub_eq_add_neg]; rfl
    have e1 : G b f = G b kzero + G ⊥ f := by
      have := hGadd (b := b) (b' := ⊥) (f := kzero) (f' := f) (k := f) (inf_bot_eq _)
        (fun t => by simp)
      rwa [sup_bot_eq] at this
    have hdiff : (2 * N) • GP.gmap (Ψ b f) - N • GP.gunit -
        ((2 * N) • G b kzero - N • GP.gunit + (2 * N) • T) = (2 * N) • (G ⊥ f - T) := by
      show (2 * N) • G b f - _ - _ = _
      rw [e1]; module
    rw [hsumL, hdiff]
    refine lt_of_le_of_lt (ousNorm_le_rc (by positivity) ?_ ?_) hnε
    · have h1 : -((((1 : ℕ) : ℝ) / n) • GP.gunit) ≤ G ⊥ f - T := by
        rw [neg_le_sub_iff_le_add]; rw [sub_le_iff_le_add] at hTf
        exact hTf
      have := smul_le_smul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * N by positivity)
      calc -((2 * N / n) • GP.gunit) = (2 * N) • -((((1 : ℕ) : ℝ) / n) • GP.gunit) := by
            rw [smul_neg, _root_.smul_smul]; congr 2; push_cast; ring
        _ ≤ _ := this
    · have h1 : G ⊥ f - T ≤ 0 := sub_nonpos.2 hfT
      calc (2 * N) • (G ⊥ f - T) ≤ 0 := smul_nonpos_of_nonneg_of_nonpos (by positivity) h1
        _ ≤ (2 * N / n) • GP.gunit := smul_nonneg (by positivity) (GP.gmap_nonneg _)

end SpecDense

section SpecTop

open Papers.SEA
open scoped Papers.SEA

variable {E : Type u} [EffectAlgebra E] [NormalSEA E] [EffectModule I E]
  (hsm : ∀ (a b : E) (l : I), a ⊙ (l • b) = l • (a ⊙ b))

/-- **The negative part of a non-positive element** (the spectral step of the proof
of REC 120): for `y ∉ V⁺` there are a non-zero idempotent `q` and `x, z ≥ 0` with
`y = x - z`, `q & x = 0`, `q & z ≥ β q` and `z ≤ 4β·1` (`β > 0`).  (The print:
"write `y = y⁺ - y⁻` … find an idempotent `p ≠ 0` with `p & y < -α/2 p`".) -/
theorem spectral_neg (y : GP.Vec E) (hy : ¬ 0 ≤ y) :
    ∃ q : E, Papers.SEA.IsIdempotent q ∧ q ≠ 0 ∧ ∃ (x z : GP.Vec E) (β : ℝ),
      0 ≤ x ∧ 0 ≤ z ∧ 0 < β ∧ y = x - z ∧
      ULin hsm q x = 0 ∧ β • GP.gmap q ≤ ULin hsm q z ∧ z ≤ (4 * β) • GP.gunit := by
  obtain ⟨N, a, hN, rfl⟩ := gp_affine_repr y
  obtain ⟨B, _, X, _, _, _, hED, Ψ, hadd, hone, hmul, hinj, b, f, rfl⟩ := spectral_rep a
  exact spectral_neg_core hsm Ψ hadd hmul hED hone hinj hN b f hy

/-- **Density of sharp combinations** (REC 58: "the sharp effects span a norm-dense
set of effects"): every `w ∈ V` is a norm limit of finite linear combinations of
idempotents. -/
theorem spectral_dense (w : GP.Vec E) {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (ℝ × E), (∀ p ∈ l, Papers.SEA.IsIdempotent p.2) ∧
      ousNorm (GP.Vec E) (w - (l.map fun p => p.1 • GP.gmap p.2).sum) < ε := by
  obtain ⟨N, a, hN, rfl⟩ := gp_affine_repr w
  obtain ⟨B, _, X, _, _, _, hED, Ψ, hadd, hone, hmul, -, b, f, rfl⟩ := spectral_rep a
  exact spectral_dense_core Ψ hadd hmul hED hone hN b f hε

end SpecTop



/-! ## The scalars of a sequential effectus are irreducible -/

section IdemScalars

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- In an effectus with filters and comprehensions that is **separated by states**
(REC 14: *total* maps `I → A`), the only idempotent scalars are `0` and `1`.  For
an idempotent `s ≠ 1` the comprehension `{I|s}` has no states (a state `σ` would
give `π ∘ σ = 1`, hence `s = 1`), so separation makes `id_{I|s} = 0`, whence
`π_s = 0` and `s = 0` (as `s ∘ s = s = 1 ∘ s` factors through `π_s`). -/
theorem idem_scalar_trivial [HasQuotients C] [HasComprehension C] (hsep : SeparatingStates C)
    {s : Scal C} (hs : s ≫ s = s) : s = 0 ∨ s = 𝟙 _ := by
  by_cases h1 : s = 𝟙 _
  · exact Or.inr h1
  left
  have hπ := isComprehension_comprMap s
  have hno : ∀ sg : Stat (comprObj s), False := by
    intro sg
    obtain ⟨sg, hsg⟩ := sg
    have ht : sg ≫ truth _ = 𝟙 _ := hsg.trans truth_effObj_eq_id
    have hπt : comprMap s ≫ truth (effObj C) = truth _ := compr_total hπ
    have e1 : sg ≫ comprMap s = 𝟙 _ := by
      have h := congrArg (fun k => sg ≫ k) hπt
      rw [ht, truth_effObj_eq_id, Category.comp_id] at h
      exact h
    have e2 : comprMap s ≫ s = comprMap s := by
      rw [hπ.1, truth_effObj_eq_id, Category.comp_id]
    apply h1
    have h := congrArg (fun k => sg ≫ k) e2
    simp only [← Category.assoc, e1, Category.id_comp] at h
    exact h
  have hid : 𝟙 (comprObj s) = 0 := hsep _ _ fun sg => (hno sg).elim
  have hπ0 : comprMap s = 0 := by
    rw [← Category.id_comp (comprMap s), hid, FinPAC.zero_comp]
  obtain ⟨g, hg, -⟩ := hπ.2 s (by rw [hs, truth_effObj_eq_id, Category.comp_id])
  rw [← hg, hπ0, FinPAC.comp_zero]

/-- Hence (REC 21) the scalars of such an effectus are **irreducible** (REC 20). -/
theorem scal_irreducible_of_states [HasQuotients C] [HasComprehension C]
    (hsep : SeparatingStates C) : IsIrreducible (Scal C) :=
  rec21_irreducible_iff.2 fun p hp => by
    rcases idem_scalar_trivial hsep (show p ≫ p = p from hp) with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans scal_one_eq.symm)

end IdemScalars

/-! ## REC 36 (also proved in `Papers/REC/Tidy.lean` as `rec36_holds`; this file cannot import it) -/

section Rec36

open Papers.SEA (Commutes)

/-- A Hausdorff extremally disconnected space in which every clopen set is `∅` or
everything has at most one point. -/
theorem subsingleton_of_clopen {X : Type u} [TopologicalSpace X] [T2Space X]
    (hED : ExtremallyDisconnected X) (h : ∀ U : Set X, IsClopen U → U = ∅ ∨ U = Set.univ) :
    Subsingleton X := by
  refine ⟨fun x y => by_contra fun hxy => ?_⟩
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hxy
  have hc : IsClopen (closure U) := ⟨isClosed_closure, hED.open_closure U hU⟩
  have hy : y ∉ closure U := by
    rw [mem_closure_iff]; push Not
    exact ⟨V, hV, hyV, by rw [Set.inter_comm]; exact hUV.inter_eq⟩
  rcases h _ hc with h0 | h0
  · have := subset_closure hxU; rw [h0] at this; exact this
  · exact hy (h0 ▸ Set.mem_univ y)

/-- The indicator of a clopen set is an idempotent of `[0,1]_{C(X)}`. -/
theorem kind_mul_self {X : Type u} [TopologicalSpace X] (U : Set X) (hU : IsClopen U) :
    kmul (kind U hU) (kind U hU) = kind U hU :=
  kext fun t => by
    simp only [kmul_val, ContinuousMap.mul_apply, kind_apply]
    by_cases ht : t ∈ U <;> simp [ht]

/-- Composing an isomorphism of effect monoids with a mutually inverse pair of
homomorphisms. -/
def emIsoComp {M : Type u} {N : Type u} {P : Type w} [EffectMonoid M] [EffectMonoid N]
    [EffectMonoid P] (φ : EMIso M N) (H : EffectMonoidHom N P) (H' : EffectMonoidHom P N)
    (h1 : ∀ x, H'.toFun (H.toFun x) = x) (h2 : ∀ y, H.toFun (H'.toFun y) = y) : EMIso M P where
  hom :=
    { toFun := fun m => H.toFun (φ.hom.toFun m)
      perp_map := fun h => H.perp_map (φ.hom.perp_map h)
      ovee_map := fun h => by
        show H.toFun (φ.hom.toFun _) = _
        rw [φ.hom.ovee_map h, H.ovee_map]
      map_one := by show H.toFun (φ.hom.toFun 1) = 1; rw [φ.hom.map_one, H.map_one]
      map_mul := fun a b => by
        show H.toFun (φ.hom.toFun (a * b)) = _
        rw [φ.hom.map_mul, H.map_mul] }
  inv :=
    { toFun := fun r => φ.inv.toFun (H'.toFun r)
      perp_map := fun h => φ.inv.perp_map (H'.perp_map h)
      ovee_map := fun h => by
        show φ.inv.toFun (H'.toFun _) = _
        rw [H'.ovee_map h, φ.inv.ovee_map]
      map_one := by show φ.inv.toFun (H'.toFun 1) = 1; rw [H'.map_one, φ.inv.map_one]
      map_mul := fun a b => by
        show φ.inv.toFun (H'.toFun (a * b)) = _
        rw [H'.map_mul, φ.inv.map_mul] }
  inv_hom m := by
    show φ.inv.toFun (H'.toFun (H.toFun (φ.hom.toFun m))) = m
    rw [h1, φ.inv_hom]
  hom_inv r := by
    show H.toFun (φ.hom.toFun (φ.inv.toFun (H'.toFun r))) = r
    rw [φ.hom_inv, h2]

/-- **REC 36** (short.tex:776, Theorem) **holds**: an irreducible directed-complete
effect monoid is `{0}`, `{0,1}` or `[0,1]`.  From REC 34 (`rec34_holds`, OAP 69):
`M ≅ B ⊕ C(X,[0,1])`; irreducibility (REC 21: no idempotents but `0, 1`) forces
`B` or `X` to be trivial (the idempotent `(1,0)`), a trivial `B` makes every clopen
of `X` trivial, so `X` has at most one point (extremally disconnected Hausdorff),
and an empty `X` makes `B = {0,1}` or `{0}`.  (The print cites OAP; this is
OAP's argument through REC 34.)  Proved here independently of `Papers.REC.rec36_holds`
(`Papers/REC/Tidy.lean`, same statement), which this file cannot import. -/
theorem rec36_holds_rc : IrreducibleDCClassification.{u} := by
  intro M _ hdc hirr
  have hid := rec21_irreducible_iff.1 hirr
  obtain ⟨B, _, X, _, hc, ht, hED, ⟨φ⟩⟩ := rec34_holds M hdc
  let _ := booleanEffectMonoid B
  let _ := continuousUnitIntervalEffectMonoid X
  -- idempotents of `B × C(X,[0,1])` are `0` or `1`
  have hidem : ∀ (b : B) (f : Set.Icc (0 : C(X, ℝ)) 1), kmul f f = f →
      (b = ⊥ ∧ f = kzero) ∨ (b = ⊤ ∧ f = kone) := by
    intro b f hf
    have hx' : φ.inv.toFun (b, f) * φ.inv.toFun (b, f) = φ.inv.toFun (b, f) := by
      rw [← φ.inv.map_mul]
      exact congrArg φ.inv.toFun (Prod.ext (inf_idem b) hf)
    rcases hid _ hx' with h | h
    · left
      have := (φ.hom_inv (b, f)).symm
      rw [h, EffectMonoidHom.map_zero'] at this
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    · right
      have := (φ.hom_inv (b, f)).symm
      rw [h, φ.hom.map_one] at this
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  -- the idempotent `(⊤, 0)`
  rcases hidem ⊤ kzero (kext fun t => by simp) with ⟨hB, -⟩ | ⟨-, hK⟩
  · -- `B` is trivial
    have hBs : Subsingleton B := subsingleton_of_bot_eq_top hB.symm
    have hX : Subsingleton X := subsingleton_of_clopen hED fun U hU => by
      rcases hidem ⊥ (kind U hU) (kind_mul_self U hU) with ⟨-, h⟩ | ⟨-, h⟩
      · left
        ext t; simp only [Set.mem_empty_iff_false, iff_false]
        intro htU
        have := congrArg (fun g : Set.Icc (0 : C(X, ℝ)) 1 => (g : C(X, ℝ)) t) h
        simp [kind_apply, htU] at this
      · right
        ext t; simp only [Set.mem_univ, iff_true]
        by_contra htU
        have := congrArg (fun g : Set.Icc (0 : C(X, ℝ)) 1 => (g : C(X, ℝ)) t) h
        simp [kind_apply, htU] at this
    rcases isEmpty_or_nonempty X with hXe | hne
    · -- `X = ∅`: everything is trivial
      left
      refine ⟨fun a b => ?_⟩
      rw [← φ.inv_hom a, ← φ.inv_hom b]
      congr 1
      refine Prod.ext (Subsingleton.elim _ _) (kext fun t => (IsEmpty.false t).elim)
    · -- `X` is a point: `M ≅ [0,1]`
      right; right
      obtain ⟨x₀⟩ := hne
      let ev : B × Set.Icc (0 : C(X, ℝ)) 1 → I := fun x =>
        ⟨(x.2 : C(X, ℝ)) x₀, cIcc_nonneg x.2 x₀, cIcc_le_one x.2 x₀⟩
      let cst : I → B × Set.Icc (0 : C(X, ℝ)) 1 := fun r =>
        (⊥, kmk (ContinuousMap.const X (r : ℝ)) (fun _ => r.2.1) (fun _ => r.2.2))
      have hcst_ev : ∀ x, cst (ev x) = x := fun x => Prod.ext (Subsingleton.elim _ _)
        (kext fun t => by
          show ((x.2 : C(X, ℝ)) x₀) = (x.2 : C(X, ℝ)) t
          rw [Subsingleton.elim t x₀])
      have hev_cst : ∀ r, ev (cst r) = r := fun r => rfl
      let H : EffectMonoidHom (B × Set.Icc (0 : C(X, ℝ)) 1) I :=
        { toFun := ev
          perp_map := fun {x y} h => by
            show ((x.2 : C(X, ℝ)) x₀) + (y.2 : C(X, ℝ)) x₀ ≤ 1
            exact cIcc_perp_apply h.2 x₀
          ovee_map := fun h => rfl
          map_one := rfl
          map_mul := fun x y => rfl }
      let H' : EffectMonoidHom I (B × Set.Icc (0 : C(X, ℝ)) 1) :=
        { toFun := cst
          perp_map := fun {r s} h => ⟨inf_idem _, fun t => by
            show (r : ℝ) + s ≤ 1; exact h⟩
          ovee_map := fun {r s} h => Prod.ext (sup_idem _).symm (kext fun t => rfl)
          map_one := Prod.ext (Subsingleton.elim _ _) (kext fun t => rfl)
          map_mul := fun r s => Prod.ext (inf_idem _).symm (kext fun t => rfl) }
      exact ⟨emIsoComp φ H H' hcst_ev hev_cst⟩
  · -- `X = ∅` (as `0 = 1` in `C(X,[0,1])`)
    have hXe : IsEmpty X := ⟨fun t => by
      have := congrArg (fun g : Set.Icc (0 : C(X, ℝ)) 1 => (g : C(X, ℝ)) t) hK
      simp at this⟩
    have hKs : ∀ f g : Set.Icc (0 : C(X, ℝ)) 1, f = g := fun f g =>
      kext fun t => (IsEmpty.false t).elim
    -- every `b` is `⊥` or `⊤`
    have hB2 : ∀ b : B, b = ⊥ ∨ b = ⊤ := fun b => by
      rcases hidem b kzero (kext fun t => by simp) with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    by_cases hbt : (⊥ : B) = ⊤
    · left
      refine ⟨fun a b => ?_⟩
      rw [← φ.inv_hom a, ← φ.inv_hom b]
      congr 1
      refine Prod.ext ?_ (hKs _ _)
      rcases hB2 (φ.hom.toFun a).1 with h1 | h1 <;> rcases hB2 (φ.hom.toFun b).1 with h2 | h2 <;>
        simp [h1, h2, hbt]
    · right; left
      classical
      let tb : B × Set.Icc (0 : C(X, ℝ)) 1 → Bool := fun x => decide (x.1 = ⊤)
      let bt : Bool → B × Set.Icc (0 : C(X, ℝ)) 1 := fun c => (if c then ⊤ else ⊥, kzero)
      have hbt_tb : ∀ x, bt (tb x) = x := fun x => by
        refine Prod.ext ?_ (hKs _ _)
        rcases hB2 x.1 with h | h <;> simp [bt, tb, h, hbt]
      have htb_bt : ∀ c, tb (bt c) = c := fun c => by
        cases c <;> simp [bt, tb, hbt]
      have htt : ∀ x : B × Set.Icc (0 : C(X, ℝ)) 1, x.1 = ⊤ → tb x = true := fun x h => by
        simp [tb, h]
      have htf : ∀ x : B × Set.Icc (0 : C(X, ℝ)) 1, x.1 = ⊥ → tb x = false := fun x h => by
        simp [tb, h, hbt]
      have hperpB : ∀ x y : B × Set.Icc (0 : C(X, ℝ)) 1, Perp x y → Perp (tb x) (tb y) := by
        intro x y h
        show tb x ⊓ tb y = ⊥
        have h1 : x.1 ⊓ y.1 = ⊥ := h.1
        rcases hB2 x.1 with hx | hx
        · rw [htf x hx]; rfl
        · rcases hB2 y.1 with hy | hy
          · rw [htf y hy]; exact inf_bot_eq _
          · rw [hx, hy, inf_idem] at h1; exact absurd h1.symm hbt
      let H : EffectMonoidHom (B × Set.Icc (0 : C(X, ℝ)) 1) Bool :=
        { toFun := tb
          perp_map := fun h => hperpB _ _ h
          ovee_map := fun {x y} h => by
            show tb (x.1 ⊔ y.1, _) = tb x ⊔ tb y
            rcases hB2 x.1 with hx | hx <;> rcases hB2 y.1 with hy | hy
            · rw [htf x hx, htf y hy, htf _ (show x.1 ⊔ y.1 = ⊥ by rw [hx, hy, sup_idem])]; rfl
            · rw [htf x hx, htt y hy, htt _ (show x.1 ⊔ y.1 = ⊤ by rw [hy, sup_top_eq])]; rfl
            · rw [htt x hx, htf y hy, htt _ (show x.1 ⊔ y.1 = ⊤ by rw [hx, top_sup_eq])]; rfl
            · rw [htt x hx, htt y hy, htt _ (show x.1 ⊔ y.1 = ⊤ by rw [hx, top_sup_eq])]; rfl
          map_one := htt _ rfl
          map_mul := fun x y => by
            show tb (x.1 ⊓ y.1, _) = tb x ⊓ tb y
            rcases hB2 x.1 with hx | hx <;> rcases hB2 y.1 with hy | hy
            · rw [htf x hx, htf y hy, htf _ (show x.1 ⊓ y.1 = ⊥ by rw [hx, bot_inf_eq])]; rfl
            · rw [htf x hx, htt y hy, htf _ (show x.1 ⊓ y.1 = ⊥ by rw [hx, bot_inf_eq])]; rfl
            · rw [htt x hx, htf y hy, htf _ (show x.1 ⊓ y.1 = ⊥ by rw [hy, inf_bot_eq])]; rfl
            · rw [htt x hx, htt y hy, htt _ (show x.1 ⊓ y.1 = ⊤ by rw [hx, hy, inf_idem])]; rfl }
      let H' : EffectMonoidHom Bool (B × Set.Icc (0 : C(X, ℝ)) 1) :=
        { toFun := bt
          perp_map := fun {c d} h => ⟨by
            show (bt c).1 ⊓ (bt d).1 = ⊥
            have h' : c ⊓ d = ⊥ := h
            cases c <;> cases d <;> simp_all [bt], fun t => (IsEmpty.false t).elim⟩
          ovee_map := fun {c d} h => by
            refine Prod.ext ?_ (hKs _ _)
            show (if (c ⊔ d) then ⊤ else ⊥ : B) = (if c then ⊤ else ⊥) ⊔ (if d then ⊤ else ⊥)
            cases c <;> cases d <;> simp
          map_one := Prod.ext rfl (hKs _ _)
          map_mul := fun c d => by
            refine Prod.ext ?_ (hKs _ _)
            show (if (c ⊓ d) then ⊤ else ⊥ : B) = (if c then ⊤ else ⊥) ⊓ (if d then ⊤ else ⊥)
            cases c <;> cases d <;> simp }
      exact ⟨emIsoComp φ H H' hbt_tb htb_bt⟩

end Rec36


/-! ## §5.4 The predicate spaces are JB-algebras -/

/-! ### Order derivations (REC 117) and the cited results of Alfsen–Shultz -/

section OrderDerivation

variable (W : Type u) [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]

/-- Convergence in the order-unit norm of REC 41. -/
def OUSTendsto (s : ℕ → W) (w : W) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ousNorm W (s n - w) < ε

/-- The partial sums `∑_{k<n} (t^k/k!) δ^k v` of `e^{tδ} v`. -/
noncomputable def expPartialSum (δ : W →ₗ[ℝ] W) (t : ℝ) (v : W) (n : ℕ) : W :=
  ∑ k ∈ Finset.range n, (t ^ k / (k.factorial : ℝ)) • (δ ^ k) v

/-- **REC 117** (short.tex:2153, Definition): a bounded linear map `δ` on an order
unit space `W` is an **order derivation** when `e^{tδ} = ∑ (tδ)ⁿ/n!` is an order
isomorphism for every `t ∈ ℝ`.  Rendered with REC 41's norm: `δ` is bounded, and
for every `t` there is a linear bijection `e` with `e v = ∑ (t^k/k!) δ^k v` (the
series converging in norm) that is an order isomorphism. -/
def IsOrderDerivation (δ : W →ₗ[ℝ] W) : Prop :=
  (∃ c : ℝ, ∀ v, ousNorm W (δ v) ≤ c * ousNorm W v) ∧
    ∀ t : ℝ, ∃ e : W ≃ₗ[ℝ] W, (∀ v, OUSTendsto W (expPartialSum W δ t v) (e v)) ∧
      ∀ v w, v ≤ w ↔ e v ≤ e w

end OrderDerivation

/-- **REC 118** (`prop:order-derivation-condition`, short.tex:2158, Proposition),
*the statement* (Alfsen–Shultz, *State spaces of operator algebras*, Prop. 1.108):
on a Banach order unit space a bounded `δ` is an order derivation iff
`ω(a) = 0 ⟹ ω(δ a) = 0` for all `a ≥ 0` and states `ω`.  An external result,
recorded as a named `Prop`; the paper does not use it (REC 120 reworks the proof
of A–S 1.106 instead, because the effectus's states are not all the states of
`V_A`), and neither does this file. -/
def AlfsenShultzOrderDerivationCriterion : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W],
    IsOUS W → IsBanachOUS W → ∀ δ : W →ₗ[ℝ] W,
      (∃ c : ℝ, ∀ v, ousNorm W (δ v) ≤ c * ousNorm W v) →
      (IsOrderDerivation W δ ↔
        ∀ a : W, 0 ≤ a → ∀ ω : OUSState W, ω.toLin a = 0 → ω.toLin (δ a) = 0)

/-- **Alfsen–Shultz, *State spaces*, (1.82)**, with the step of the proof of their
Thm. 1.106 that REC 120 uses, as a named black box: on a Banach order unit space,
a bounded `δ` such that, for all small `λ > 0`, both `1 - λδ` and `1 + λδ` carry
non-positive elements to non-positive elements, is an order derivation.  (For
`λ‖δ‖ < 1` the map `1 ∓ λδ` is invertible, and (1.82) says its inverse is then
positive; `e^{±tδ} = lim ((1 ∓ (t/n)δ)^{-1})ⁿ` is a norm limit of positive maps,
hence positive as the cone is closed, and `e^{tδ} e^{-tδ} = 1`.) -/
def AlfsenShultzResolventCriterion : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W],
    IsOUS W → IsBanachOUS W → ∀ δ : W →ₗ[ℝ] W,
      (∃ c : ℝ, ∀ v, ousNorm W (δ v) ≤ c * ousNorm W v) →
      (∃ c : ℝ, 0 < c ∧ ∀ l : ℝ, 0 < l → l < c → ∀ y : W, ¬ 0 ≤ y → ¬ 0 ≤ y - l • δ y) →
      (∃ c : ℝ, 0 < c ∧ ∀ l : ℝ, 0 < l → l < c → ∀ y : W, ¬ 0 ≤ y → ¬ 0 ≤ y + l • δ y) →
      IsOrderDerivation W δ

/-- **Alfsen–Shultz, *Geometry of state spaces of operator algebras*, Thm. 9.48
(via 9.43)**, as a named black box, stated for a Banach order unit space (no
spectral duality, no dual space assumed) with a norm-dense set of combinations
of "projections": let `W` be a directed-complete Banach order unit space and
`(e_i)` an (injectively indexed) family in `[0,1]_W`, closed under `e ↦ 1 - e`,
with positive maps `U_i` ("compressions": `U_i 1 = e_i`, `U_i² = U_i`,
`U_i U_{i'} = 0`, and on `W⁺`, `U_i w = 0 ⟺ U_{i'} w = w`) such that every
`U_i - U_{i'}` is an order derivation and finite combinations of the `e_i` are
norm dense.  Then `W` is a JB-algebra (REC 44) whose product satisfies
`e_i * w = ½ (w + U_i w - U_{i'} w)`. -/
def AlfsenShultzJordanFromDerivations : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W],
    IsOUS W → IsBanachOUS W → IsDirectedCompleteOUS W →
    ∀ (ι : Type u) (e : ι → W) (U : ι → W →ₗ[ℝ] W) (c : ι → ι),
      Function.Injective e →
      (∀ i, 0 ≤ e i ∧ e i ≤ ouUnit W) → (∀ i, e (c i) = ouUnit W - e i) →
      (∀ i, (∀ w, 0 ≤ w → 0 ≤ U i w) ∧ U i (ouUnit W) = e i ∧ U i ∘ₗ U i = U i ∧
        U i ∘ₗ U (c i) = 0) →
      (∀ i w, 0 ≤ w → (U i w = 0 ↔ U (c i) w = w)) →
      (∀ i, IsOrderDerivation W (U i - U (c i))) →
      (∀ (w : W) (ε : ℝ), 0 < ε → ∃ l : List (ℝ × ι),
        ousNorm W (w - (l.map fun p => p.1 • e p.2).sum) < ε) →
      ∃ _ : Mul W, JBAlgebra W ∧
        ∀ i w, e i * w = (2⁻¹ : ℝ) • (w + (U i w - U (c i) w))

/-! ### The convex part of the predicates and its order unit space -/

section ConvexPart

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

/-- The convex part `s⊥ · Pred(A)` of the predicates of `A` (REC 93), for a
splitting `σs` of the scalars (REC 35).  In the paper's §5.4, which assumes "without
loss of generality" convex scalars, this is all of `Pred(A)`; here we work in `C`
itself with this part. -/
def CPt (σs : ScalarSplit C) (A : C) : Type v := PredPart (orth_idem σs.hs) A

variable (σs : ScalarSplit C)

noncomputable instance CPt.instEA (A : C) : EffectAlgebra (CPt σs A) :=
  PredPart.ea (orth_idem σs.hs)

noncomputable instance CPt.instEMod (A : C) : EffectModule I (CPt σs A) :=
  @ConvexEA.toEffectModule _ _ (σs.convex A)

/-- The unit `s⊥ ∘ 1` of the convex part is sharp, hence idempotent. -/
theorem cpt_unit_idem (A : C) : SEA.IsIdempotent (truth A ≫ orth σs.s) :=
  isIdempotent_of_isSharp (isSharp_of_states (orth_idem σs.hs) separatedByStates A)

noncomputable instance CPt.instSEA (A : C) : SEA (CPt σs A) :=
  partSEA (orth_idem σs.hs) (cpt_unit_idem σs A)

@[simp] theorem cpt_seq_val {A : C} (a b : CPt σs A) : (SEA.seq a b).1 = SEA.seq a.1 b.1 := rfl

/-- Suprema of directed subsets of the part are those of `Pred(A)`. -/
theorem cpt_isSup_val {A : C} {D : Set (CPt σs A)} (hD : IsUpDirected D) {s : CPt σs A}
    (hs : IsSupOf D s) : IsSupOf (Subtype.val '' D) s.1 := by
  have hD' : IsUpDirected (Subtype.val '' D) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hD x hx y hy
    exact ⟨_, ⟨z, hz, rfl⟩, (PredPart.le_iff _).1 hxz, (PredPart.le_iff _).1 hyz⟩
  obtain ⟨sg, hsg1, hsg2⟩ := (normal (C := C)).1 A _ hD'
  have hsgu : sg ≼ truth A ≫ orth σs.s :=
    hsg2 _ (by rintro _ ⟨x, -, rfl⟩; exact PredPart.le_one (orth_idem σs.hs) x)
  have hsgt : sg ≫ orth σs.s = sg :=
    part_of_le (orth_idem σs.hs) (by
      rw [Category.assoc, show orth σs.s ≫ orth σs.s = orth σs.s from orth_idem σs.hs]) hsgu
  have hsup : IsSupOf D (⟨sg, hsgt⟩ : CPt σs A) :=
    ⟨fun x hx => (PredPart.le_iff _).2 (hsg1 _ ⟨x, hx, rfl⟩),
      fun u hu => (PredPart.le_iff _).2 (hsg2 _ (by
        rintro _ ⟨x, hx, rfl⟩; exact (PredPart.le_iff _).1 (hu x hx)))⟩
  have : s = ⟨sg, hsgt⟩ := eabasics_le_antisymm (hs.2 _ hsup.1) (hsup.2 _ hs.1)
  rw [this]; exact ⟨hsg1, hsg2⟩

/-- The SEA of the convex part is normal (REC 56): suprema and commutation are
those of `Pred(A)`. -/
theorem cpt_isNormal (A : C) : @IsNormalSEA (CPt σs A) _ (CPt.instSEA σs A) := by
  refine ⟨PredPart.directedComplete (orth_idem σs.hs) ((normal (C := C)).1 A), ?_⟩
  intro D s hD hs a
  have hv := cpt_isSup_val σs hD hs
  have hD' : IsUpDirected (Subtype.val '' D) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hD x hx y hy
    exact ⟨_, ⟨z, hz, rfl⟩, (PredPart.le_iff _).1 hxz, (PredPart.le_iff _).1 hyz⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := (sea_normal A).2 _ s.1 hD' hv a.1
  refine ⟨⟨?_, ?_⟩, fun hc => Subtype.ext (h3 ?_)⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (PredPart.le_iff _).2 (h1 _ ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩)
  · intro t ht
    refine (PredPart.le_iff _).2 (h2 _ ?_)
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact (PredPart.le_iff _).1 (ht _ ⟨x, hx, rfl⟩)
  · rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hc x hx)

noncomputable instance CPt.instNormalSEA (A : C) : Papers.SEA.NormalSEA (CPt σs A) :=
  normalSEAOf (cpt_isNormal σs A)

instance CPt.instDC (A : C) : Papers.OAP.DirectedComplete (CPt σs A) :=
  oapDirectedComplete_of (PredPart.directedComplete (orth_idem σs.hs) ((normal (C := C)).1 A))

open scoped Papers.SEA in
/-- The sequential product of the part is homogeneous in its second argument. -/
theorem cpt_hsm (A : C) :
    ∀ (a b : CPt σs A) (l : I), a ⊙ (l • b) = l • (a ⊙ b) := by
  intro a b l
  apply Subtype.ext
  show SEA.seq a.1 (b.1 ≫ σs.c l) = SEA.seq a.1 b.1 ≫ σs.c l
  rw [seq_eq, seq_eq, Category.assoc]

/-- The order unit space `V_A` of the convex part: its Gudder–Pulmannová space
(REC 40, 42), with `Pred(A) ≅ [0,1]_{V_A}` on the convex part. -/
abbrev VA (A : C) : Type v := GP.Vec (CPt σs A)

theorem VA_archimedean (A : C) : OUSArchimedean (VA σs A) := Papers.OAP.gp_archimedean

/-- `V_A` is an order unit space in the sense of REC 41. -/
theorem VA_isOUS (A : C) : IsOUS (VA σs A) := isOUS_of_archimedean_rc (VA_archimedean σs A)

/-- `V_A` is a Banach order unit space (Wright's lemma, OAP's `wright_normComplete`). -/
theorem VA_banach (A : C) : IsBanachOUS (VA σs A) :=
  isBanachOUS_of (Papers.OAP.wright_normComplete
    (Papers.OAP.oap60_omega.1 Papers.OAP.gp_omegaComplete))

/-- `V_A` is directed complete (REC 41). -/
theorem VA_dc (A : C) : IsDirectedCompleteOUS (VA σs A) :=
  isDirectedCompleteOUS_of Papers.OAP.gp_directedComplete

/-- The operator `a ↦ p & a` on `V_A` (the linear extension of `asrt_p`). -/
noncomputable def Uop {A : C} (p : CPt σs A) : VA σs A →ₗ[ℝ] VA σs A := ULin (cpt_hsm σs A) p

/-- `D_p = asrt_p - asrt_{p⊥}` on `V_A` (REC 120). -/
noncomputable def Dop {A : C} (p : CPt σs A) : VA σs A →ₗ[ℝ] VA σs A :=
  Uop σs p - Uop σs (orth p)

open scoped Papers.SEA in
theorem Uop_gmap {A : C} (p b : CPt σs A) : Uop σs p (GP.gmap b) = GP.gmap (p ⊙ b) :=
  ULin_gmap _ p b

theorem Uop_nonneg {A : C} (p : CPt σs A) {v : VA σs A} (hv : 0 ≤ v) : 0 ≤ Uop σs p v :=
  gpLift_nonneg _ (ULin_hadd p) (ULin_hsmul (cpt_hsm σs A) p) (fun _ => GP.gmap_nonneg _) hv

open scoped Papers.SEA in
theorem Uop_unit {A : C} (p : CPt σs A) : Uop σs p (ouUnit (VA σs A)) = GP.gmap p := by
  show Uop σs p (GP.gmap 1) = _
  rw [Uop_gmap, Papers.SEA.seq_one]

theorem gmap_add_orth' {A : C} (p : CPt σs A) :
    GP.gmap p + GP.gmap (orth p) = ouUnit (VA σs A) :=
  Papers.OAP.gmap_add_orth p

/-- `‖D_p v‖ ≤ ‖v‖`: `D_p` is bounded (REC 117). -/
theorem Dop_bound {A : C} (p : CPt σs A) (v : VA σs A) :
    ousNorm (VA σs A) (Dop σs p v) ≤ ousNorm (VA σs A) v := by
  by_cases hu : ouUnit (VA σs A) = 0
  · rw [ou_eq_zero_of_unit_eq_zero hu (Dop σs p v)]
    rw [show ousNorm (VA σs A) 0 = 0 from le_antisymm (ousNorm_le_rc le_rfl (by simp) (by simp))
      (ousNorm_nonneg_rc _)]
    exact ousNorm_nonneg_rc _
  refine le_csInf (ousNormSet_nonempty v) fun l hl => ?_
  have hl0 := ousNormSet_nonneg hu hl
  have hb : ∀ q : CPt σs A, -(l • GP.gmap q) ≤ Uop σs q v ∧ Uop σs q v ≤ l • GP.gmap q := by
    intro q
    have h1 := Uop_nonneg σs q (sub_nonneg.2 hl.1)
    rw [map_sub, map_neg, map_smul, Uop_unit, sub_neg_eq_add] at h1
    have h2 := Uop_nonneg σs q (sub_nonneg.2 hl.2)
    rw [map_sub, map_smul, Uop_unit] at h2
    exact ⟨neg_le_iff_add_nonneg.2 h1, sub_nonneg.1 h2⟩
  obtain ⟨h1, h2⟩ := hb p
  obtain ⟨h3, h4⟩ := hb (orth p)
  have he := gmap_add_orth' σs p
  refine ousNorm_le_rc hl0 ?_ ?_
  · show -(l • ouUnit (VA σs A)) ≤ Uop σs p v - Uop σs (orth p) v
    calc -(l • ouUnit (VA σs A)) = -(l • GP.gmap p) - l • GP.gmap (orth p) := by
          rw [← he, smul_add]; abel
      _ ≤ Uop σs p v - Uop σs (orth p) v := sub_le_sub h1 h4
  · show Uop σs p v - Uop σs (orth p) v ≤ l • ouUnit (VA σs A)
    calc Uop σs p v - Uop σs (orth p) v ≤ l • GP.gmap p - -(l • GP.gmap (orth p)) :=
          sub_le_sub h2 h3
      _ = l • ouUnit (VA σs A) := by rw [← he, smul_add]; abel

end ConvexPart


/-! ### REC 119, REC 120 -/

section Rec120

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

variable (C) in
/-- **REC 119** (`lem:state-order-lemma`, short.tex:2165, Lemma), *the statement*:
for a sharp `p`, a predicate `a` and a state `ω` with `a ∘ ω = 0`,
`(p & a) ∘ ω = (p⊥ & a) ∘ ω`.  The print's proof is a citation ("exactly as" van de
Wetering 2018, *Sequential measurement characterises finite-dimensional quantum
theory*, Prop. 46, which is about the states of a compressible quadratic SEA, not
about an effectus's internal states); not reconstructed here, and recorded as the
named hypothesis `WeteringStateOrderLemma` of REC 120–121 and 102–103. -/
def WeteringStateOrderLemma : Prop :=
  ∀ {A : C} (p a : Pred A) (ω : Stat A), IsSharp p → ω.1 ≫ a = 0 →
    ω.1 ≫ SEA.seq p a = ω.1 ≫ SEA.seq (orth p) a

/-- **REC 119**, from the named hypothesis. -/
theorem rec119 (h119 : WeteringStateOrderLemma C) {A : C} {p : Pred A} (hp : IsSharp p)
    (a : Pred A) (ω : Stat A) (h : ω.1 ≫ a = 0) :
    ω.1 ≫ SEA.seq p a = ω.1 ≫ SEA.seq (orth p) a :=
  h119 p a ω hp h

/-- A comprehension of a non-zero sharp predicate has a state (REC 14). -/
theorem exists_state_compr {A : C} {q : Pred A} (hq : IsSharp q) (h0 : q ≠ 0) :
    Nonempty (Stat (comprObj q)) := by
  by_contra hne
  have hid : 𝟙 (comprObj q) = 0 := separatedByStates _ _ fun sg => (hne ⟨sg⟩).elim
  have hπ0 : comprMap q = 0 := by rw [← Category.id_comp (comprMap q), hid, FinPAC.zero_comp]
  apply h0
  rw [← flrR_of_isSharp hq]
  refine isImage_unique (isImage_flrR q) ?_
  rw [hπ0]
  exact ⟨by rw [FinPAC.zero_comp, FinPAC.zero_comp], fun r _ => zero_le_hom r⟩

variable (σs : ScalarSplit C)

/-- An element of the convex part. -/
def cptMk {A : C} (p : Pred A) (h : p ≫ orth σs.s = p) : CPt σs A := ⟨p, h⟩

@[simp] theorem cptMk_val {A : C} (p : Pred A) (h : p ≫ orth σs.s = p) :
    (cptMk σs p h).1 = p := rfl

theorem stateLin_hadd {B A : C} (ω : B ⟶ A) {a b : CPt σs A} (h : Perp a b) :
    GP.gmap (cptMk σs (A := B) (ω ≫ (ovee a b h).1) (by rw [Category.assoc, (ovee a b h).2])) =
      GP.gmap (cptMk σs (A := B) (ω ≫ a.1) (by rw [Category.assoc, a.2])) +
        GP.gmap (cptMk σs (A := B) (ω ≫ b.1) (by rw [Category.assoc, b.2])) := by
  obtain ⟨h', e⟩ := FinPAC.ovee_comp (show Perp a.1 b.1 from h) ω
  have hp : Perp (cptMk σs (A := B) (ω ≫ a.1) (by rw [Category.assoc, a.2]))
      (cptMk σs (A := B) (ω ≫ b.1) (by rw [Category.assoc, b.2])) := h'
  rw [← GP.gmap_ovee hp]
  congr 1; exact Subtype.ext e

theorem stateLin_hsmul {B A : C} (ω : B ⟶ A) (l : I) (a : CPt σs A) :
    GP.gmap (cptMk σs (A := B) (ω ≫ (l • a).1) (by rw [Category.assoc, (l • a).2])) =
      (l : ℝ) • GP.gmap (cptMk σs (A := B) (ω ≫ a.1) (by rw [Category.assoc, a.2])) := by
  rw [← GP.gmap_smul]
  congr 1
  exact Subtype.ext (Category.assoc _ _ _).symm

/-- `Pred(ω)` for a map `ω : B → A`, as a positive linear map `V_A → V_B`,
`a ↦ a ∘ ω`.  For a state `ω : I → A` this is the paper's "we can equivalently view
`ω` as a positive linear map `V_A → C(X)`" (REC 120). -/
noncomputable def stateLin {B A : C} (ω : B ⟶ A) : VA σs A →ₗ[ℝ] VA σs B :=
  gpLift (fun a : CPt σs A =>
      GP.gmap (cptMk σs (A := B) (ω ≫ a.1) (by rw [Category.assoc, a.2])))
    (stateLin_hadd σs ω) (stateLin_hsmul σs ω)

theorem stateLin_gmap {B A : C} (ω : B ⟶ A) (a : CPt σs A) :
    stateLin σs ω (GP.gmap a) =
      GP.gmap (cptMk σs (A := B) (ω ≫ a.1) (by rw [Category.assoc, a.2])) :=
  gpLift_gmap _ (stateLin_hadd σs ω) (stateLin_hsmul σs ω) a

theorem stateLin_nonneg {B A : C} (ω : B ⟶ A) {v : VA σs A} (hv : 0 ≤ v) :
    0 ≤ stateLin σs ω v :=
  gpLift_nonneg _ (stateLin_hadd σs ω) (stateLin_hsmul σs ω) (fun _ => GP.gmap_nonneg _) hv

theorem ou_gauge_unit_pos {X : Type w} [AddCommGroup X] [Module ℝ X] [PartialOrder X]
    [OrderUnitSpace X] (hu : ouUnit X ≠ 0) : 0 < ouGauge X (ouUnit X) := by
  have : (1 : ℝ) ≤ ouGauge X (ouUnit X) := ou_le_gauge fun r hr => by
    have h : (0 : X) ≤ (r - 1) • ouUnit X := by
      rw [sub_smul, one_smul]; exact sub_nonneg.2 hr
    have := ou_nonneg_of_smul_unit_nonneg hu h
    linarith
  linarith

/-- The unit `u = s⊥ ∘ 1` of the convex part acts as `w ↦ s⊥ ∘ w`. -/
theorem seq_unit_left {A : C} (w : Pred A) :
    SEA.seq (truth A ≫ orth σs.s) w = w ≫ orth σs.s := by
  rw [seq_eq, asrtS_eq_asrtSharp (isSharp_of_states (orth_idem σs.hs) separatedByStates A)]
  exact asrtT_pred (orth_idem σs.hs) (isSharp_of_states (orth_idem σs.hs) separatedByStates) w

theorem seq_unit_right {A : C} (w : Pred A) :
    SEA.seq w (truth A ≫ orth σs.s) = w ≫ orth σs.s := by
  rw [seq_eq, ← Category.assoc, asrtS_truth]

/-- For `e` in the convex part, `(s⊥ ∘ p⊥) & e = p⊥ & e`. -/
theorem cpt_seq_orth {A : C} (p e : CPt σs A) :
    SEA.seq (orth p).1 e.1 = SEA.seq (orth p.1) e.1 := by
  have hu : SEA.seq (truth A ≫ orth σs.s) (orth p.1) =
      SEA.seq (orth p.1) (truth A ≫ orth σs.s) := by
    rw [seq_unit_left, seq_unit_right]
  show SEA.seq (orth p.1 ≫ orth σs.s) e.1 = _
  rw [← seq_unit_left σs (orth p.1), ← SEA.comm_assoc hu, seq_unit_left, seq_eq,
    Category.assoc, e.2]

theorem cpt_idem_iff {A : C} (p : CPt σs A) :
    Papers.SEA.IsIdempotent p ↔ SEA.IsIdempotent p.1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem cpt_isSharp_orth {A : C} {p : CPt σs A} (hp : IsSharp p.1) : IsSharp (orth p).1 :=
  isSharp_of_isIdempotent ((cpt_idem_iff σs _).1
    (Papers.SEA.IsIdempotent.compl ((cpt_idem_iff σs p).2 (isIdempotent_of_isSharp hp))))

open scoped Papers.SEA in
/-- The core of **REC 120**'s proof, by the repaired route of the independent
review (ERRATA "REC 120"): for `y ∉ V⁺` and `0 < λ < 1/4`, `y - λ D_p y ∉ V⁺`. -/
theorem rec120_core (h119 : WeteringStateOrderLemma C) {A : C} (p : CPt σs A)
    (hp : IsSharp p.1) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1 / 4) (y : VA σs A)
    (hy : ¬ 0 ≤ y) : ¬ 0 ≤ y - l • Dop σs p y := by
  -- the spectral step: `y = x - z`, `q & x = 0`, `q & z ≥ β q`, `z ≤ 4β`
  obtain ⟨q, hqi, hq0, x, z, β, hx, hz, hβ, rfl, hqx, hqz, hz4⟩ :=
    spectral_neg (cpt_hsm σs A) y hy
  replace hqx : Uop σs q x = 0 := hqx
  replace hqz : β • GP.gmap q ≤ Uop σs q z := hqz
  have hqs : IsSharp q.1 := isSharp_of_isIdempotent ((cpt_idem_iff σs q).1 hqi)
  have hq0' : q.1 ≠ 0 := fun h => hq0 (Subtype.ext h)
  -- a *total* state `ω = π_q ∘ σ` below `q` (the review's repair)
  obtain ⟨sg⟩ := exists_state_compr hqs hq0'
  set ω : effObj C ⟶ A := sg.1 ≫ comprMap q.1 with hωdef
  have hπ := isComprehension_comprMap q.1
  have hωt : ω ≫ truth A = truth (effObj C) := by
    rw [hωdef, Category.assoc, compr_total hπ]; exact sg.2
  have hωq : ω ≫ q.1 = ω ≫ truth A := by
    rw [hωdef, Category.assoc, hπ.1, ← Category.assoc]
  have hωa : ω ≫ asrtS q.1 = ω := comp_asrtS_of hqs ω hωq
  set Ω := stateLin σs ω with hΩdef
  have hΩU : ∀ v, Ω (Uop σs q v) = Ω v := by
    have : Ω ∘ₗ Uop σs q = Ω := gp_linearMap_ext fun b => by
      rw [LinearMap.comp_apply, Uop_gmap, hΩdef, stateLin_gmap, stateLin_gmap]
      congr 1; apply Subtype.ext
      show ω ≫ SEA.seq q.1 b.1 = ω ≫ b.1
      rw [seq_eq, ← Category.assoc, hωa]
    intro v; exact LinearMap.congr_fun this v
  -- `Ω 1 = 1` and `Ω q = 1`
  have hIu : truth (effObj C) ≫ orth σs.s = truth (effObj C) := by
    have h : (ω ≫ q.1) ≫ orth σs.s = ω ≫ q.1 := by rw [Category.assoc, q.2]
    rw [hωq, hωt] at h; exact h
  have hΩ1 : Ω (ouUnit (VA σs A)) = ouUnit (VA σs (effObj C)) := by
    show Ω (GP.gmap 1) = GP.gmap 1
    rw [hΩdef, stateLin_gmap]; congr 1; apply Subtype.ext
    show ω ≫ (truth A ≫ orth σs.s) = truth (effObj C) ≫ orth σs.s
    rw [← Category.assoc, hωt]
  have hΩq : Ω (GP.gmap q) = ouUnit (VA σs (effObj C)) := by
    show Ω (GP.gmap q) = GP.gmap 1
    rw [hΩdef, stateLin_gmap]; congr 1; apply Subtype.ext
    show ω ≫ q.1 = truth (effObj C) ≫ orth σs.s
    rw [hωq, hωt, hIu]
  -- a real state `ψ` of `V_I`
  have hu_ne : ouUnit (VA σs (effObj C)) ≠ 0 := by
    intro h0
    have h1 : (1 : CPt σs (effObj C)) = 0 :=
      GP.gmap_injective (h0.trans (GP.gmap_zero (E := CPt σs (effObj C))).symm)
    have h2 : truth (effObj C) ≫ orth σs.s = 0 := congrArg Subtype.val h1
    rw [hIu, truth_effObj_eq_id] at h2
    apply hq0'
    rw [← Category.comp_id q.1, h2, FinPAC.comp_zero]
  obtain ⟨ψ, hψpos, hψ1, -⟩ := ou_exists_state hu_ne _ (ou_gauge_unit_pos hu_ne)
  set φ : VA σs A →ₗ[ℝ] ℝ := ψ ∘ₗ Ω with hφdef
  have hφpos : ∀ v, 0 ≤ v → 0 ≤ φ v := fun v hv => hψpos _ (stateLin_nonneg σs ω hv)
  have hφ1 : φ (ouUnit (VA σs A)) = 1 := by rw [hφdef, LinearMap.comp_apply, hΩ1, hψ1]
  -- the three facts about `ω`
  have hφx : φ x = 0 := by rw [hφdef, LinearMap.comp_apply, ← hΩU, hqx, map_zero, map_zero]
  have hφDx : φ (Dop σs p x) = 0 := by
    obtain ⟨c, hc⟩ := GP.Vec.exists_of_zero_le hx
    obtain ⟨r, e, rfl⟩ := GP.Cone.exists_mk c
    have hxe : x = (r : ℝ) • GP.gmap e := by rw [hc, gp_rsmul_gmap]
    rw [hxe, map_smul, map_smul]
    rcases eq_or_ne (r : ℝ) 0 with hr | hr
    · rw [hr, zero_smul]
    have hΩe : Ω (GP.gmap e) = 0 := by
      have := congrArg Ω hxe
      rw [map_smul] at this
      have h0 : Ω x = 0 := by rw [← hΩU, hqx, map_zero]
      rw [h0] at this
      exact (smul_eq_zero.1 this.symm).resolve_left hr
    rw [hΩdef, stateLin_gmap] at hΩe
    have hωe : ω ≫ e.1 = 0 :=
      congrArg (fun x : CPt σs (effObj C) => x.1)
        (GP.gmap_injective (hΩe.trans (GP.gmap_zero (E := CPt σs (effObj C))).symm))
    have h19 := rec119 h119 hp e.1 ⟨ω, hωt⟩ hωe
    have : Ω (Dop σs p (GP.gmap e)) = 0 := by
      rw [Dop, LinearMap.sub_apply, map_sub, Uop_gmap, Uop_gmap, hΩdef, stateLin_gmap,
        stateLin_gmap, sub_eq_zero]
      congr 1; apply Subtype.ext
      show ω ≫ SEA.seq p.1 e.1 = ω ≫ SEA.seq (orth p).1 e.1
      rw [cpt_seq_orth]; exact h19
    rw [hφdef, LinearMap.comp_apply, this, map_zero, smul_zero]
  -- the estimate
  have hφz : β ≤ φ z := by
    have h1 := hφpos _ (sub_nonneg.2 hqz)
    rw [map_sub, map_smul, sub_nonneg] at h1
    have e1 : φ (GP.gmap q) = 1 := by
      show ψ (Ω (GP.gmap q)) = 1; rw [hΩq, hψ1]
    have e2 : φ (Uop σs q z) = φ z := by
      show ψ (Ω (Uop σs q z)) = ψ (Ω z); rw [hΩU]
    rw [e1, e2, smul_eq_mul, mul_one] at h1; exact h1
  have hφDz : φ (Dop σs p z) ≤ 4 * β := by
    have h1 := abs_state_le φ hφpos hφ1 (Dop σs p z)
    have h2 := Dop_bound σs p z
    have h3 : ousNorm (VA σs A) z ≤ 4 * β :=
      ousNorm_le_rc (by positivity) ((neg_nonpos.2 (smul_nonneg (by positivity)
        ou_unit_nonneg)).trans hz) hz4
    exact (le_abs_self _).trans (h1.trans (h2.trans h3))
  intro hcon
  have h := hφpos _ hcon
  rw [map_sub, map_smul, map_sub, map_sub, map_sub, hφx, hφDx, smul_eq_mul] at h
  nlinarith

/-- **REC 120** (`prop:assert-is-derivation`, short.tex:2175, Proposition): for a
sharp `p`, `D_p = asrt_p - asrt_{p⊥}` is an order derivation on `V_A` (REC 117).
The paper's proof, **repaired** as in the independent review
(`docs/research/review-rec120.md`, ERRATA "REC 120"): by Alfsen–Shultz (1.82) and the
exponential formula (the named hypothesis `AlfsenShultzResolventCriterion`) it
suffices that `1 ∓ λδ` maps non-positive elements to non-positive ones for small
`λ > 0`; for `y ∉ V⁺` the spectral theorem (REC 58: `spectral_neg`) gives a sharp
`q ≠ 0` where `y` is very negative; the repair takes the **total** state
`ω = π_q ∘ σ` for a state `σ` of `{A|q}` (not the substate `asrt_q ∘ ω` of the
print), so that `asrt_q ∘ ω = ω` and Lemma 119 applies as stated; composing with a
real state of `V_I` puts every strict inequality in `ℝ`.  (`‖D_p‖ ≤ 1`, so the
print's bound `λ < ½‖δ‖⁻¹` becomes `λ < 1/4` with the constant 4 of `spectral_neg`.)
`p` ranges over the convex part of `Pred(A)` (all of it when the scalars are
convex, as in the paper's §5.4). -/
theorem rec120 (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)
    {A : C} (p : CPt σs A) (hp : IsSharp p.1) : IsOrderDerivation (VA σs A) (Dop σs p) := by
  have hDneg : Dop σs (orth p) = -Dop σs p := by
    simp only [Dop, eabasics_orth_orth, neg_sub]
  refine hRC (VA σs A) (VA_isOUS σs A) (VA_banach σs A) (Dop σs p)
    ⟨1, fun v => by rw [one_mul]; exact Dop_bound σs p v⟩
    ⟨1 / 4, by norm_num, fun l hl0 hl1 y hy => rec120_core σs h119 p hp hl0 hl1 y hy⟩
    ⟨1 / 4, by norm_num, fun l hl0 hl1 y hy => ?_⟩
  have := rec120_core σs h119 (orth p) (cpt_isSharp_orth σs hp) hl0 hl1 y hy
  rwa [hDneg, LinearMap.neg_apply, smul_neg, sub_neg_eq_add] at this

end Rec120

/-! ### REC 121 -/

section Rec121

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus
open scoped Papers.SEA

variable (σs : ScalarSplit C)

theorem list_attach_map_sum {α : Type*} {M : Type*} [AddCommMonoid M] {P : α → Prop}
    (l : List α) (hl : ∀ x ∈ l, P x) (F : α → M) :
    ((l.attach.map fun x => (⟨x.1, hl x.1 x.2⟩ : {a // P a})).map fun y => F y.1).sum =
      (l.map F).sum := by
  rw [List.map_map]
  simp

/-- **REC 121** (`prop:is-JB-algebra`, short.tex:2226, Proposition): `V_A` is a
JB-algebra, with `p * a = ½ (a + D_p a)` for sharp `p`.  The paper's proof invokes
Alfsen–Shultz, *Geometry*, Thm. 9.48 (via 9.43) — the named hypothesis
`AlfsenShultzJordanFromDerivations` — whose inputs are supplied here: `V_A` is a
directed-complete Banach order unit space (REC 41, Wright's lemma), the sharp
predicates with the maps `asrt_p` are compressions (idempotent, `asrt_p 1 = p`,
`asrt_p asrt_{p⊥} = 0`, and `asrt_p w = 0 ⟺ asrt_{p⊥} w = w` for `w ≥ 0`), every
`D_p` is an order derivation (REC 120), and combinations of sharp predicates are
norm dense (REC 58, `spectral_dense`). -/
theorem rec121 (hAS : AlfsenShultzJordanFromDerivations.{v})
    (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C) (A : C) :
    ∃ _ : Mul (VA σs A), JBAlgebra (VA σs A) ∧
      ∀ q : CPt σs A, IsSharp q.1 → ∀ w, GP.gmap q * w = (2⁻¹ : ℝ) • (w + Dop σs q w) := by
  let ι := {q : CPt σs A // Papers.SEA.IsIdempotent q}
  let e : ι → VA σs A := fun i => GP.gmap i.1
  let U : ι → VA σs A →ₗ[ℝ] VA σs A := fun i => Uop σs i.1
  let c : ι → ι := fun i => ⟨orth i.1, i.2.compl⟩
  have hsh : ∀ i : ι, IsSharp i.1.1 := fun i =>
    isSharp_of_isIdempotent ((cpt_idem_iff σs i.1).1 i.2)
  obtain ⟨m, hjb, hform⟩ := hAS (VA σs A) (VA_isOUS σs A) (VA_banach σs A) (VA_dc σs A) ι e U c
    (fun i j h => Subtype.ext (GP.gmap_injective h))
    (fun i => ⟨GP.gmap_nonneg _, GP.gmap_le_gunit _⟩)
    (fun i => by
      show GP.gmap (orth i.1) = ouUnit (VA σs A) - GP.gmap i.1
      rw [← gmap_add_orth' σs i.1]; abel)
    (fun i => ⟨fun w hw => Uop_nonneg σs i.1 hw, Uop_unit σs i.1,
      gp_linearMap_ext fun b => by
        show Uop σs i.1 (Uop σs i.1 (GP.gmap b)) = Uop σs i.1 (GP.gmap b)
        rw [Uop_gmap, Uop_gmap, (Papers.SEA.commutes_refl i.1).assoc, i.2],
      gp_linearMap_ext fun b => by
        show Uop σs i.1 (Uop σs (orth i.1) (GP.gmap b)) = 0
        rw [Uop_gmap, Uop_gmap, (Papers.SEA.commutes_orth_self i.1).assoc, i.2.seq_orth,
          Papers.SEA.zero_seq, GP.gmap_zero]⟩)
    (fun i w hw => by
      obtain ⟨p₀, rfl⟩ := GP.Vec.exists_of_zero_le hw
      obtain ⟨r, b, rfl⟩ := GP.Cone.exists_mk p₀
      rw [← gp_rsmul_gmap]
      show Uop σs i.1 ((r : ℝ) • GP.gmap b) = 0 ↔
        Uop σs (orth i.1) ((r : ℝ) • GP.gmap b) = (r : ℝ) • GP.gmap b
      rw [map_smul, map_smul, Uop_gmap, Uop_gmap]
      rcases eq_or_ne (r : ℝ) 0 with hr | hr
      · simp [hr]
      rw [smul_eq_zero, or_iff_right hr, ← GP.gmap_zero]
      constructor
      · intro h
        have h1 : i.1 ⊙ b = 0 := GP.gmap_injective h
        have h2 : b ≼ orth i.1 := by
          have := ((Papers.SEA.sea17_5 i.2.compl b).2.2.2).2
          rw [Papers.SEA.orth_orth] at this; exact this h1
        rw [((Papers.SEA.sea17_5 i.2.compl b).1).1 h2]
      · intro h
        have h1 : orth i.1 ⊙ b = b :=
          GP.gmap_injective ((smul_right_injective _ hr) h)
        have h2 : b ≼ orth i.1 := ((Papers.SEA.sea17_5 i.2.compl b).1).2 h1
        have := ((Papers.SEA.sea17_5 i.2.compl b).2.2.2).1 h2
        rw [Papers.SEA.orth_orth] at this
        rw [this])
    (fun i => rec120 σs hRC h119 i.1 (hsh i))
    (fun w ε hε => by
      obtain ⟨l, hl, hn⟩ := spectral_dense w hε
      refine ⟨l.attach.map fun x => (x.1.1, ⟨x.1.2, hl x.1 x.2⟩), ?_⟩
      have := list_attach_map_sum l hl (fun p => p.1 • GP.gmap p.2)
      convert hn using 3
      rw [← this, List.map_map, List.map_map]
      rfl)
  refine ⟨m, hjb, fun q hq w => ?_⟩
  have := hform ⟨q, (cpt_idem_iff σs q).2 (isIdempotent_of_isSharp hq)⟩ w
  simpa [Dop, e, U, c] using this

end Rec121


/-! ## §5.5 The main theorems -/

/-! ### The categories `CBA`, `JB_npc`, `JBW_npc` -/

section Cats

/-- **REC 102**: `CBA`, the category of complete Boolean algebras and monotone maps
(as printed). -/
structure CBACat : Type (u + 1) where
  carrier : Type u
  [ba : BooleanAlgebra carrier]
  complete : ∀ S : Set carrier, ∃ j, IsLUB S j

attribute [instance] CBACat.ba

instance : Category CBACat.{u} where
  Hom A B := { f : A.carrier → B.carrier // Monotone f }
  id _ := ⟨id, monotone_id⟩
  comp f g := ⟨g.1 ∘ f.1, g.2.comp f.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A linear map between order unit spaces is a **normal positive contraction**
(REC 47, 48): positive, `‖f v‖ ≤ ‖v‖`, and normal. -/
def IsNPC {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
    {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]
    (f : V →ₗ[ℝ] W) : Prop :=
  (∀ v, 0 ≤ v → 0 ≤ f v) ∧ (∀ v, ousNorm W (f v) ≤ ousNorm V v) ∧ IsNormalMap f

section NPC

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
  {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]
  {Z : Type u} [AddCommGroup Z] [Module ℝ Z] [PartialOrder Z] [OrderUnitSpace Z]

theorem monotone_of_pos {f : V →ₗ[ℝ] W} (h : ∀ v, 0 ≤ v → 0 ≤ f v) : Monotone f :=
  fun v w hvw => by have := h _ (sub_nonneg.2 hvw); rwa [map_sub, sub_nonneg] at this

theorem isNPC_id : IsNPC (LinearMap.id : V →ₗ[ℝ] V) :=
  ⟨fun _ h => h, fun _ => le_rfl, fun S s _ _ hs => by simpa using hs⟩

theorem isNPC_comp {f : V →ₗ[ℝ] W} {g : W →ₗ[ℝ] Z} (hf : IsNPC f) (hg : IsNPC g) :
    IsNPC (g ∘ₗ f) := by
  refine ⟨fun v hv => hg.1 _ (hf.1 _ hv), fun v => (hg.2.1 _).trans (hf.2.1 _),
    fun S s hne hdir hs => ?_⟩
  have h1 := hf.2.2 S s hne hdir hs
  have hmono := monotone_of_pos hf.1
  have h2 := hg.2.2 (f '' S) (f s) (hne.image _) (hdir.mono_comp hmono) h1
  rw [Set.image_image] at h2; exact h2

/-- A positive map with `0 ≤ f 1 ≤ 1` is a contraction. -/
theorem contraction_of_pos {f : V →ₗ[ℝ] W} (hpos : ∀ v, 0 ≤ v → 0 ≤ f v)
    (h1 : f (ouUnit V) ≤ ouUnit W) (v : V) : ousNorm W (f v) ≤ ousNorm V v := by
  by_cases hu : ouUnit V = 0
  · rw [ou_eq_zero_of_unit_eq_zero hu v, map_zero]
    exact le_trans (ousNorm_le_rc le_rfl (by simp) (by simp)) (ousNorm_nonneg_rc _)
  refine le_csInf (ousNormSet_nonempty v) fun l hl => ?_
  have hl0 := ousNormSet_nonneg hu hl
  have hf1 : 0 ≤ f (ouUnit V) := hpos _ ou_unit_nonneg
  have a1 := hpos _ (sub_nonneg.2 hl.1)
  rw [map_sub, map_neg, map_smul, sub_neg_eq_add] at a1
  have a2 := hpos _ (sub_nonneg.2 hl.2)
  rw [map_sub, map_smul] at a2
  refine ousNorm_le_rc hl0 ?_ ?_
  · calc -(l • ouUnit W) ≤ -(l • f (ouUnit V)) := neg_le_neg (ou_smul_le_smul hl0 h1)
      _ ≤ f v := neg_le_iff_add_nonneg.2 a1
  · calc f v ≤ l • f (ouUnit V) := sub_nonneg.1 a2
      _ ≤ l • ouUnit W := ou_smul_le_smul hl0 h1

end NPC

/-- **REC 102**: `JB_npc`, JB-algebras (REC 44) with normal positive linear
contractions (the paper does not define it; "analogously to `JBW_npc`", REC 48). -/
structure JBnpcCat : Type (u + 1) where
  carrier : Type u
  [acg : AddCommGroup carrier]
  [mod : Module ℝ carrier]
  [po : PartialOrder carrier]
  [ous : OrderUnitSpace carrier]
  [mul : Mul carrier]
  jb : JBAlgebra carrier

attribute [instance] JBnpcCat.acg JBnpcCat.mod JBnpcCat.po JBnpcCat.ous JBnpcCat.mul

instance : Category JBnpcCat.{u} where
  Hom A B := { f : A.carrier →ₗ[ℝ] B.carrier // IsNPC f }
  id _ := ⟨LinearMap.id, isNPC_id⟩
  comp f g := ⟨g.1 ∘ₗ f.1, isNPC_comp f.2 g.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- **REC 48** (`def:JBW-algebra`, short.tex:901, Definition), the category part:
`JBW_npc`, JBW-algebras with normal positive linear contractions. -/
structure JBWnpcCat : Type (u + 1) where
  carrier : Type u
  [acg : AddCommGroup carrier]
  [mod : Module ℝ carrier]
  [po : PartialOrder carrier]
  [ous : OrderUnitSpace carrier]
  [mul : Mul carrier]
  jbw : JBWAlgebra carrier

attribute [instance] JBWnpcCat.acg JBWnpcCat.mod JBWnpcCat.po JBWnpcCat.ous JBWnpcCat.mul

instance : Category JBWnpcCat.{u} where
  Hom A B := { f : A.carrier →ₗ[ℝ] B.carrier // IsNPC f }
  id _ := ⟨LinearMap.id, isNPC_id⟩
  comp f g := ⟨g.1 ∘ₗ f.1, isNPC_comp f.2 g.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end Cats

/-! ### `Pred(f)` on `V_A` is a normal positive contraction -/

section PredLin

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

variable (σs : ScalarSplit C)

/-- In a directed-complete Gudder–Pulmannová space, a supremum relative to `[0,1]`
of a non-empty directed subset of `[0,1]` is its supremum. -/
theorem gp_isLUB_of_rel {E : Type u} [EffectAlgebra E] [EffectModule I E]
    [Papers.OAP.DirectedComplete E] {D : Set (GP.Vec E)}
    (hD : D ⊆ Set.Icc 0 (ouUnit (GP.Vec E))) (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    {t : GP.Vec E} (ht : Papers.OAP.IsLUBIn (Set.Icc 0 (ouUnit (GP.Vec E))) D t) :
    IsLUB D t := by
  obtain ⟨t', ht'⟩ := (Papers.OAP.oap60_directed.1 Papers.OAP.gp_directedComplete) D hne hdir
    ⟨ouUnit _, fun d hd => (hD hd).2⟩
  obtain ⟨d, hd⟩ := hne
  have ht'I : t' ∈ Set.Icc 0 (ouUnit (GP.Vec E)) :=
    ⟨(hD hd).1.trans (ht'.1 hd), ht'.2 fun d hd => (hD hd).2⟩
  have e : t = t' := le_antisymm (ht.2.2 t' ht'I ht'.1) (ht'.2 ht.2.1)
  rw [e]; exact ht'

theorem stateLin_unit_le {B A : C} (g : B ⟶ A) :
    stateLin σs g (ouUnit (VA σs A)) ≤ ouUnit (VA σs B) := by
  show stateLin σs g (GP.gmap 1) ≤ GP.gmap 1
  rw [stateLin_gmap]
  refine gmap_mono ((PredPart.le_iff _).2 ?_)
  show g ≫ (truth A ≫ orth σs.s) ≼ truth B ≫ orth σs.s
  rw [← Category.assoc]
  exact le_comp_right' (pred_le_truth _) _

open scoped Papers.OAP in
/-- `Pred(g)` on `V_A` preserves suprema of directed sets (normality of the
effectus, REC 30, transported to `V_A`). -/
theorem stateLin_normal {B A : C} (g : B ⟶ A) : IsNormalMap (stateLin σs g) := by
  intro S s hne hdir hs
  set T := stateLin σs g with hT
  have hTmono : Monotone T := monotone_of_pos fun v hv => stateLin_nonneg σs g hv
  refine ⟨?_, fun w hw => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩; exact hTmono (hs.1 hx)
  obtain ⟨s₀, hs₀⟩ := hne
  set S' : Set (VA σs A) := {x | x ∈ S ∧ s₀ ≤ x} with hS'
  have hcof : ∀ x ∈ S, ∃ z ∈ S', x ≤ z := fun x hx => by
    obtain ⟨z, hz, hxz, h0z⟩ := hdir x hx s₀ hs₀; exact ⟨z, ⟨hz, h0z⟩, hxz⟩
  have hdir' : DirectedOn (· ≤ ·) S' := by
    rintro x ⟨hx, hx0⟩ y ⟨hy, -⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨z, ⟨hz, hx0.trans hxz⟩, hxz, hyz⟩
  have hsS' : IsLUB S' s := ⟨fun x hx => hs.1 hx.1, fun u hu => hs.2 fun x hx => by
    obtain ⟨z, hz, hxz⟩ := hcof x hx; exact hxz.trans (hu hz)⟩
  -- move `S'` into `[0,1]`
  obtain ⟨n₁, h11, -⟩ := Papers.OAP.oap58_orderUnit s₀
  obtain ⟨n₂, -, h22⟩ := Papers.OAP.oap58_orderUnit s
  set N : ℝ := n₁ + n₂ + 1 with hN
  have hN0 : 0 < N := by positivity
  have hsym : ∀ x, s₀ ≤ x → x ≤ s → x ∈ Papers.OAP.symIcc (VA σs A) N := fun x h1 h2 =>
    ⟨(neg_le_neg (ou_smul_unit_mono (by rw [hN]; linarith [(Nat.cast_nonneg n₂ : (0 : ℝ) ≤ n₂)]))).trans
      (h11.trans h1),
      h2.trans (h22.trans (ou_smul_unit_mono (by rw [hN]; linarith [(Nat.cast_nonneg n₁ : (0 : ℝ) ≤ n₁)])))⟩
  set G := Papers.OAP.affIso (V := VA σs A) N hN0 with hGdef
  have hGmem : ∀ x ∈ Papers.OAP.symIcc (VA σs A) N, G x ∈ Set.Icc 0 (ouUnit (VA σs A)) :=
    fun x hx => by
      rw [← Set.mem_preimage, Papers.OAP.affIso_preimage]; exact hx
  have hGS'I : ∀ x ∈ S', G x ∈ Set.Icc 0 (ouUnit (VA σs A)) :=
    fun x hx => hGmem x (hsym x hx.2 (hs.1 hx.1))
  have hsI : G s ∈ Set.Icc 0 (ouUnit (VA σs A)) :=
    hGmem s (hsym s (hs.1 hs₀) le_rfl)
  have hGS : IsLUB (G '' S') (G s) := ⟨by rintro _ ⟨x, hx, rfl⟩; exact G.monotone (hsS'.1 hx),
    fun u hu => by
      have : s ≤ G.symm u := hsS'.2 fun x hx => G.le_symm_apply.2 (hu ⟨x, hx, rfl⟩)
      exact G.le_symm_apply.1 this⟩
  -- the corresponding set of effects
  set D : Set (CPt σs A) := {a | GP.gmap a ∈ G '' S'} with hD
  have hDimg : GP.gmap '' D = G '' S' := by
    ext y; constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, ha⟩ := GP.gmap_surjective_Icc (hGS'I x hx)
      exact ⟨a, by rw [hD, Set.mem_ofPred_eq, ha]; exact ⟨x, hx, rfl⟩, ha⟩
  obtain ⟨as, has⟩ := GP.gmap_surjective_Icc hsI
  have hDsup : IsLUB D as := Papers.OAP.gmap_isLUBIn_iff.2 (by
    rw [hDimg, has]; exact ⟨hsI, hGS.1, fun w _ hw => hGS.2 hw⟩)
  have hDdir : IsUpDirected D := by
    rintro a ⟨x, hx, hax⟩ b ⟨y, hy, hby⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir' x hx y hy
    obtain ⟨c, hc⟩ := GP.gmap_surjective_Icc (hGS'I z hz)
    refine ⟨c, ⟨z, hz, hc.symm⟩, ?_, ?_⟩
    · exact Papers.OAP.gmap_le_gmap_iff.1 (by rw [← hax, hc]; exact G.monotone hxz)
    · exact Papers.OAP.gmap_le_gmap_iff.1 (by rw [← hby, hc]; exact G.monotone hyz)
  have hDsup' : IsSupOf D as := ⟨fun x hx => hDsup.1 hx, fun u hu => hDsup.2 hu⟩
  -- in `Pred(A)`, then through `g` by normality
  have hv := cpt_isSup_val σs hDdir hDsup'
  have hDdir' : IsUpDirected (Subtype.val '' D) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hDdir x hx y hy
    exact ⟨_, ⟨z, hz, rfl⟩, (PredPart.le_iff _).1 hxz, (PredPart.le_iff _).1 hyz⟩
  have hn := (normal (C := C)).2 g _ _ hDdir' hv
  set F : CPt σs A → CPt σs B := fun a => cptMk σs (A := B) (g ≫ a.1)
    (by rw [Category.assoc, a.2]) with hF
  have hFsup : IsLUB (F '' D) (F as) := by
    refine ⟨?_, fun u hu => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (PredPart.le_iff _).2 (hn.1 _ ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩)
    · refine (PredPart.le_iff _).2 (hn.2 _ ?_)
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact (PredPart.le_iff _).1 (hu ⟨x, hx, rfl⟩)
  have hrel := Papers.OAP.gmap_isLUBIn_iff.1 hFsup
  have himg : GP.gmap '' (F '' D) = T '' (G '' S') := by
    rw [← hDimg, Set.image_image, Set.image_image]
    ext y; simp only [Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, by rw [hT, stateLin_gmap]⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, by rw [hT, stateLin_gmap]⟩
  have hFs : GP.gmap (F as) = T (G s) := by rw [← has, hT, stateLin_gmap]
  rw [himg, hFs] at hrel
  have hsub : T '' (G '' S') ⊆ Set.Icc 0 (ouUnit (VA σs B)) := by
    rw [← himg]; rintro _ ⟨a, -, rfl⟩; exact ⟨GP.gmap_nonneg _, GP.gmap_le_gunit _⟩
  have hLUB := gp_isLUB_of_rel hsub
    ((Set.Nonempty.image G (⟨s₀, ⟨hs₀, le_rfl⟩⟩ : S'.Nonempty)).image T)
    ((hdir'.mono_comp G.monotone).mono_comp hTmono) hrel
  -- undo the affine map
  have hTG : ∀ x, T (G x) = (2 * N)⁻¹ • (T x + N • T (ouUnit (VA σs A))) := fun x => by
    rw [hGdef, Papers.OAP.affIso_apply, map_smul, map_add, map_smul]
  have hw' : ∀ x ∈ S', T (G x) ≤ (2 * N)⁻¹ • (w + N • T (ouUnit (VA σs A))) := fun x hx => by
    rw [hTG]
    exact smul_le_smul_of_nonneg_left (add_le_add_left (hw ⟨x, hx.1, rfl⟩) _) (by positivity)
  have h1 := hLUB.2 (by rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact hw' x hx)
  rw [hTG] at h1
  have h2 := le_of_smul_le_smul_left h1 (by positivity : (0 : ℝ) < (2 * N)⁻¹)
  exact (add_le_add_iff_right _).1 h2

/-- `Pred(g)` on `V_A` is a normal positive contraction (a morphism of `JB_npc`,
`JBW_npc`). -/
theorem stateLin_isNPC {B A : C} (g : B ⟶ A) : IsNPC (stateLin σs g) :=
  ⟨fun _ hv => stateLin_nonneg σs g hv,
    contraction_of_pos (fun _ hv => stateLin_nonneg σs g hv) (stateLin_unit_le σs g),
    stateLin_normal σs g⟩

theorem stateLin_comp {B B' A : C} (f : B' ⟶ B) (g : B ⟶ A) :
    stateLin σs (f ≫ g) = stateLin σs f ∘ₗ stateLin σs g :=
  gp_linearMap_ext fun a => by
    rw [LinearMap.comp_apply, stateLin_gmap, stateLin_gmap, stateLin_gmap]
    congr 1; exact Subtype.ext (Category.assoc _ _ _)

end PredLin


/-! ### Complete Boolean algebra structures on predicate spaces -/

section CBAOnSec

/-- A complete Boolean algebra structure on an effect algebra, whose lattice order
is the effect-algebra order `≼`. -/
structure CBAOn (E : Type u) [EffectAlgebra E] where
  ba : BooleanAlgebra E
  le_iff : ∀ a b : E, a ≼ b ↔ (letI := ba; a ≤ b)
  complete : ∀ S : Set E, ∃ j, (letI := ba; IsLUB S j)

/-- Transport along an isomorphism of effect algebras. -/
noncomputable def CBAOn.ofEAIso {E F : Type u} [EffectAlgebra E] [EffectAlgebra F]
    (φ : EAIso E F) (hF : CBAOn F) : CBAOn E :=
  let e : E ≃ F := ⟨φ.hom.toFun, φ.inv.toFun, φ.inv_hom, φ.hom_inv⟩
  let _ : BooleanAlgebra F := hF.ba
  { ba := e.booleanAlgebra
    le_iff := fun a b => (φ.le_iff).trans (hF.le_iff _ _)
    complete := fun S => by
      let _ := e.booleanAlgebra
      obtain ⟨j, hj⟩ := hF.complete (e '' S)
      refine ⟨e.symm j, fun x hx => ?_, fun u hu => ?_⟩
      · show e x ≤ e (e.symm j)
        rw [e.apply_symm_apply]; exact hj.1 ⟨x, hx, rfl⟩
      · show e (e.symm j) ≤ e u
        rw [e.apply_symm_apply]
        exact hj.2 (by rintro _ ⟨x, hx, rfl⟩; exact hu hx) }

variable {D : Type u} [Category.{v} D] [HasFiniteCoproducts D]
  [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D] [EffectusPartialForm D]

/-- The predicate functor `Pred : D → CBAᵒᵖ`, `A ↦ Pred(A)` (with a complete Boolean
algebra structure on each `Pred(A)` whose order is `≼`), `f ↦ (q ↦ q ∘ f)`. -/
noncomputable def cbaPredFunctor (hB : ∀ P : D, CBAOn (Pred P)) : D ⥤ CBACat.{v}ᵒᵖ where
  obj P := Opposite.op (@CBACat.mk (Pred P) (hB P).ba (hB P).complete)
  map {P Q} f := Quiver.Hom.op ⟨fun q => f ≫ q, fun a b h =>
    ((hB P).le_iff _ _).1 (comp_le_comp f (((hB Q).le_iff _ _).2 h))⟩
  map_id P := by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext; funext q; exact Category.id_comp q
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext; funext q; exact Category.assoc _ _ q

theorem cbaPredFunctor_map_eq (hB : ∀ P : D, CBAOn (Pred P)) {P Q : D} (f g : P ⟶ Q) :
    (cbaPredFunctor hB).map f = (cbaPredFunctor hB).map g ↔ ∀ q : Pred Q, f ≫ q = g ≫ q := by
  constructor
  · intro h q
    have h1 := congrArg Quiver.Hom.unop h
    have h2 := congrArg Subtype.val h1
    exact congrFun h2 q
  · intro h
    apply Quiver.Hom.unop_inj; apply Subtype.ext; funext q; exact h q

/-- `Pred : D → CBAᵒᵖ` is faithful iff `D` is separated by predicates. -/
theorem cbaPredFunctor_faithful_iff (hB : ∀ P : D, CBAOn (Pred P)) :
    (cbaPredFunctor hB).Faithful ↔ SeparatingPredicates D := by
  constructor
  · intro hF P Q f g h
    exact (cbaPredFunctor hB).map_injective ((cbaPredFunctor_map_eq hB f g).2 h)
  · intro hs
    exact ⟨fun {P Q} {f g} h => hs f g ((cbaPredFunctor_map_eq hB f g).1 h)⟩

end CBAOnSec

/-! ### REC 102 -/

section Rec102

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

variable (σs : ScalarSplit C)

/-- The Boolean part `s · Pred(A)` is a complete Boolean algebra (REC 96, 97, for a
given splitting). -/
theorem part_cba (A : C) : Nonempty (CBAOn (PredPart σs.hs A)) := by
  have hOA := σs.isOrthoalgebra separatedByStates A
  have hid := part_idem σs.hs hOA
  have hu : SEA.IsIdempotent (truth A ≫ σs.s) := hid 1
  let _ : SEA (PredPart σs.hs A) := partSEA σs.hs hu
  obtain ⟨B, hB⟩ := rec96 hOA
  exact ⟨⟨B, fun a b => (hB a b).1, boolean_complete_of_dc B (fun a b => (hB a b).1)
    (PredPart.directedComplete _ ((normal (C := C)).1 A))⟩⟩

/-- The complete Boolean algebra structure on the predicates of an object of the
Boolean part `C₁` of REC 102 (transported along `partPredIso`). -/
noncomputable def cbaOnPart (P : (dcSplitting σs separatedByStates).ε.Part) :
    CBAOn (Pred P) :=
  CBAOn.ofEAIso (partPredIso σs.hs (isSharp_of_states σs.hs separatedByStates)
    (Or.inl separatedByStates) P) (part_cba σs P.obj.X).some

/-- The predicate functor `C₁ → CBAᵒᵖ` of REC 102. -/
noncomputable abbrev rec102_cbaFunctor :
    (dcSplitting σs separatedByStates).ε.Part ⥤ CBACat.{v}ᵒᵖ :=
  cbaPredFunctor (cbaOnPart σs)

variable (hAS : AlfsenShultzJordanFromDerivations.{v})
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

/-- The Jordan product on `V_A` given by REC 121. -/
noncomputable def jbMul (A : C) : Mul (VA σs A) := (rec121 σs hAS hRC h119 A).choose

theorem jbMul_spec (A : C) : @JBAlgebra (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A) :=
  (rec121 σs hAS hRC h119 A).choose_spec.1

/-- `V_A` as an object of `JB_npc`. -/
noncomputable def jbObj (A : C) : JBnpcCat.{v} :=
  @JBnpcCat.mk (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A) (jbMul_spec σs hAS hRC h119 A)

/-- `Pred(f)` is the identity on `V` for the identity of the convex part `C₂`. -/
theorem stateLin_part_id (P : (dcSplitting σs separatedByStates).ε'.Part) :
    stateLin σs (𝟙 P : P ⟶ P).f = LinearMap.id :=
  gp_linearMap_ext fun a => by
    rw [stateLin_gmap, LinearMap.id_apply]
    congr 1; apply Subtype.ext
    show P.obj.p ≫ a.1 = a.1
    rw [(dcSplitting σs separatedByStates).ε'.prop P]
    show asrtT (orth σs.s) (isSharp_of_states (orth_idem σs.hs) separatedByStates) _ ≫ a.1 = a.1
    rw [asrtT_pred (orth_idem σs.hs), a.2]

/-- The predicate functor `C₂ → JB_npcᵒᵖ` of REC 102: `P ↦ V_P` (with
`Pred(P) ≅ [0,1]_{V_P}`), `f ↦ Pred(f)`. -/
noncomputable def rec102_jbFunctor :
    (dcSplitting σs separatedByStates).ε'.Part ⥤ JBnpcCat.{v}ᵒᵖ where
  obj P := Opposite.op (jbObj σs hAS hRC h119 P.obj.X)
  map {P Q} f := Quiver.Hom.op ⟨stateLin σs f.f, stateLin_isNPC σs f.f⟩
  map_id P := by
    apply Quiver.Hom.unop_inj; apply Subtype.ext
    exact stateLin_part_id σs P
  map_comp f g := by
    apply Quiver.Hom.unop_inj; apply Subtype.ext
    exact stateLin_comp σs f.f g.f

theorem rec102_jbFunctor_map_eq {P Q : (dcSplitting σs separatedByStates).ε'.Part}
    (f g : P ⟶ Q) :
    (rec102_jbFunctor σs hAS hRC h119).map f = (rec102_jbFunctor σs hAS hRC h119).map g ↔
      ∀ q : Pred Q, f ≫ q = g ≫ q := by
  constructor
  · intro h q
    have h1 := congrArg Quiver.Hom.unop h
    have hl : stateLin σs f.f = stateLin σs g.f := congrArg Subtype.val h1
    apply KCat.hom_ext
    show f.f ≫ q.f = g.f ≫ q.f
    have hq : q.f ≫ orth σs.s = q.f := by
      have := KCat.comp_p q
      change q.f ≫ asrtT (orth σs.s) _ (effObj C) = q.f at this
      rwa [asrtT_effObj (orth_idem σs.hs)] at this
    have := congrArg (fun φ => φ (GP.gmap (cptMk σs (A := Q.obj.X) q.f hq))) hl
    simp only [stateLin_gmap] at this
    exact congrArg (fun x : CPt σs P.obj.X => x.1) (GP.gmap_injective this)
  · intro h
    apply Quiver.Hom.unop_inj; apply Subtype.ext
    refine gp_linearMap_ext fun a => ?_
    show stateLin σs f.f (GP.gmap a) = stateLin σs g.f (GP.gmap a)
    rw [stateLin_gmap, stateLin_gmap]
    congr 1; apply Subtype.ext
    have hQ : Q.obj.p = asrtT (orth σs.s) (isSharp_of_states (orth_idem σs.hs) separatedByStates)
        Q.obj.X := (dcSplitting σs separatedByStates).ε'.prop Q
    let qa : Pred Q := KCat.homMk a.1 (by
      show Q.obj.p ≫ a.1 ≫ asrtT (orth σs.s) _ (effObj C) = a.1
      rw [asrtT_effObj (orth_idem σs.hs), a.2, hQ, asrtT_pred (orth_idem σs.hs), a.2])
    exact congrArg Karoubi.Hom.f (h qa)

section PartSep

variable {t : Scal C} (ht : t ≫ t = t) (hsh : ∀ A : C, IsSharp (truth A ≫ t))
  (hsep' : SeparatingStates C ∨ SeparatingPredicates C)

/-- In a part `C_t` (REC 92), maps that agree on the predicates of the part agree on
all predicates of `C`. -/
theorem part_pred_eq {P Q : (asrtIdem ht hsh hsep').Part} (f g : P ⟶ Q)
    (h : ∀ q : Pred Q, f ≫ q = g ≫ q) (b : Pred Q.obj.X) : f.f ≫ b = g.f ≫ b := by
  have hQ : Q.obj.p = asrtT t hsh Q.obj.X := (asrtIdem ht hsh hsep').prop Q
  have key : ∀ k : P ⟶ Q, k.f ≫ b = k.f ≫ (b ≫ t) := fun k => by
    calc k.f ≫ b = (k.f ≫ Q.obj.p) ≫ b := by rw [KCat.comp_p]
      _ = k.f ≫ (Q.obj.p ≫ b) := Category.assoc _ _ _
      _ = k.f ≫ (b ≫ t) := by rw [hQ, asrtT_pred ht hsh]
  let qb : Pred Q := KCat.homMk (b ≫ t) (by
    show Q.obj.p ≫ (b ≫ t) ≫ asrtT t hsh (effObj C) = b ≫ t
    rw [asrtT_effObj ht, Category.assoc b t t, ht, hQ, ← Category.assoc,
      asrtT_pred ht hsh, Category.assoc, ht])
  rw [key f, key g]
  exact congrArg Karoubi.Hom.f (h qb)

end PartSep

/-- For both parts, `Pred` separates the morphisms of the part exactly when
predicates of `C` separate the morphisms of `C` (the splitting of REC 95 is an
equivalence, and the predicates of a part are the corresponding part of `Pred`). -/
theorem parts_separated_iff :
    ((∀ {P Q : (dcSplitting σs separatedByStates).ε.Part} (f g : P ⟶ Q),
        (∀ q : Pred Q, f ≫ q = g ≫ q) → f = g) ∧
      (∀ {P Q : (dcSplitting σs separatedByStates).ε'.Part} (f g : P ⟶ Q),
        (∀ q : Pred Q, f ≫ q = g ≫ q) → f = g)) ↔ SeparatingPredicates C := by
  constructor
  · rintro ⟨h1, h2⟩ A B f g hfg
    apply (CentralSplitting.equivalence (dcSplitting σs separatedByStates)).functor.map_injective
    refine Prod.hom_ext (h1 _ _ fun q => KCat.hom_ext ?_) (h2 _ _ fun q => KCat.hom_ext ?_)
    · rw [KCat.comp_f, KCat.comp_f]
      exact (Category.assoc _ _ _).trans ((congrArg _ (hfg q.f)).trans (Category.assoc _ _ _).symm)
    · rw [KCat.comp_f, KCat.comp_f]
      exact (Category.assoc _ _ _).trans ((congrArg _ (hfg q.f)).trans (Category.assoc _ _ _).symm)
  · intro hs
    exact ⟨fun {P Q} f g h => KCat.hom_ext (hs _ _ fun b =>
        part_pred_eq σs.hs (isSharp_of_states σs.hs separatedByStates)
          (Or.inl separatedByStates) f g h b),
      fun {P Q} f g h => KCat.hom_ext (hs _ _ fun b =>
        part_pred_eq (orth_idem σs.hs) (isSharp_of_states (orth_idem σs.hs) separatedByStates)
          (Or.inl separatedByStates) f g h b)⟩

end Rec102


section Rec102Main

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

section PartLe

variable {t : Scal C} (ht : t ≫ t = t) (hsh : ∀ A : C, IsSharp (truth A ≫ t))
  (hsep' : SeparatingStates C ∨ SeparatingPredicates C)

/-- In a part `C_t`, the order of predicates is that of their underlying predicates
in `C` (through `partPredIso`). -/
theorem partPred_le_iff {P : (asrtIdem ht hsh hsep').Part} (a b : Pred P) :
    a ≼ b ↔ a.f ≼ b.f :=
  ((partPredIso ht hsh hsep' P).le_iff).trans (PredPart.le_iff ht)

end PartLe

theorem convexPart_pred_f (σs : ScalarSplit C) {P : (dcSplitting σs separatedByStates).ε'.Part}
    (q : Pred P) : q.f ≫ orth σs.s = q.f := by
  have := KCat.comp_p q
  change q.f ≫ asrtT (orth σs.s) _ (effObj C) = q.f at this
  rwa [asrtT_effObj (orth_idem σs.hs)] at this

theorem convexPart_homMk (σs : ScalarSplit C) (P : (dcSplitting σs separatedByStates).ε'.Part)
    (a : CPt σs P.obj.X) :
    P.obj.p ≫ a.1 ≫ (effObj (dcSplitting σs separatedByStates).ε'.Part).obj.p = a.1 := by
  show P.obj.p ≫ a.1 ≫ asrtT (orth σs.s) _ (effObj C) = a.1
  have hP : P.obj.p = asrtT (orth σs.s) (isSharp_of_states (orth_idem σs.hs) separatedByStates)
      P.obj.X := (dcSplitting σs separatedByStates).ε'.prop P
  rw [asrtT_effObj (orth_idem σs.hs), a.2, hP, asrtT_pred (orth_idem σs.hs), a.2]

/-- `Pred(P) ≅ [0,1]_{V_P}` for an object `P` of the convex part `C₂` (the predicates
of `(A, asrt_{s⊥∘1})` are the convex part of `Pred(A)`, `partPredIso`, which is the
unit interval of its Gudder–Pulmannová space). -/
noncomputable def predEquivPart (σs : ScalarSplit C)
    (P : (dcSplitting σs separatedByStates).ε'.Part) :
    Pred P ≃ Set.Icc (0 : VA σs P.obj.X) (ouUnit (VA σs P.obj.X)) where
  toFun q := Papers.OAP.gpEquiv (CPt σs P.obj.X) (cptMk σs q.f (convexPart_pred_f σs q))
  invFun v := KCat.homMk ((Papers.OAP.gpEquiv (CPt σs P.obj.X)).symm v).1
    (convexPart_homMk σs P _)
  left_inv q := KCat.hom_ext (by
    dsimp only
    rw [KCat.homMk_f, Equiv.symm_apply_apply]; rfl)
  right_inv v := by
    show (Papers.OAP.gpEquiv (CPt σs P.obj.X)) (cptMk σs _ _) = v
    conv_rhs => rw [← (Papers.OAP.gpEquiv (CPt σs P.obj.X)).apply_symm_apply v]
    rfl

theorem predEquivPart_spec (σs : ScalarSplit C) (P : (dcSplitting σs separatedByStates).ε'.Part) :
    (∀ a b : Pred P, a ≼ b ↔ ((predEquivPart σs P a : VA σs P.obj.X) ≤ predEquivPart σs P b)) ∧
    (∀ (a b : Pred P) (h : Perp a b), (predEquivPart σs P (ovee a b h) : VA σs P.obj.X) =
      predEquivPart σs P a + predEquivPart σs P b) ∧
    (predEquivPart σs P (truth P) : VA σs P.obj.X) = ouUnit (VA σs P.obj.X) := by
  refine ⟨fun a b => ?_, fun a b h => ?_, ?_⟩
  · show a ≼ b ↔ GP.gmap (cptMk σs a.f (convexPart_pred_f σs a)) ≤
      GP.gmap (cptMk σs b.f (convexPart_pred_f σs b))
    have h1 : (a.f : Pred P.obj.X) ≼ (b.f : Pred P.obj.X) ↔ cptMk σs a.f (convexPart_pred_f σs a) ≼
        cptMk σs b.f (convexPart_pred_f σs b) :=
      (PredPart.le_iff (orth_idem σs.hs) (A := P.obj.X) (p := cptMk σs a.f (convexPart_pred_f σs a))
        (q := cptMk σs b.f (convexPart_pred_f σs b))).symm
    exact (partPred_le_iff (orth_idem σs.hs) (isSharp_of_states (orth_idem σs.hs) separatedByStates)
      (Or.inl separatedByStates) a b).trans
        (h1.trans (Papers.OAP.gmap_le_gmap_iff (E := CPt σs P.obj.X)).symm)
  · show GP.gmap (cptMk σs (ovee a b h).f _) = GP.gmap (cptMk σs a.f _) + GP.gmap (cptMk σs b.f _)
    have hp : Perp (cptMk σs a.f (convexPart_pred_f σs a))
        (cptMk σs b.f (convexPart_pred_f σs b)) := h
    rw [← GP.gmap_ovee hp]
    rfl
  · show GP.gmap (cptMk σs (truth P).f _) = GP.gmap 1
    congr 1; apply Subtype.ext
    show P.obj.p ≫ truth P.obj.X = truth P.obj.X ≫ orth σs.s
    rw [(dcSplitting σs separatedByStates).ε'.prop P]
    exact asrtT_truth _ _

variable (hAS : AlfsenShultzJordanFromDerivations.{v})
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

/-- **REC 102** (`thm:JB-embedding`, short.tex:1869, Theorem): a sequential effectus
`C` is equivalent to a product of effectuses `C₁ × C₂` where the predicate spaces of
`C₁` are complete Boolean algebras and those of `C₂` are (unit intervals of)
directed-complete JB-algebras; the predicate functors `C₁ → CBAᵒᵖ`,
`C₂ → JB_npcᵒᵖ` (`rec102_cbaFunctor`: `P ↦ Pred(P)`, `f ↦ Pred(f)`;
`rec102_jbFunctor`: `P ↦ V_P` with `Pred(P) ≅ [0,1]_{V_P}`, `f ↦ Pred(f)`) are
faithful iff `C` is separated by predicates.  The paper's proof: images (REC 106)
and compatible filters and comprehensions (REC 109) make REC 95 apply (the splitting
`dcSplitting` at the idempotent scalar of REC 35, with REC 34 = OAP 69); the Boolean
part is Boolean by REC 96–97, the convex part JB by REC 121.  Named hypotheses: the
Alfsen–Shultz results at REC 120 and 121, and REC 119 (citation-only in the print).
Cosmetic fixes of the print (PLAN flag 11): `JB_npc` (never defined in the print) is
JB-algebras with normal positive contractions, and the predicate spaces of `C₂` are
unit intervals of JB-algebras.  See `rec102_trivial_factor`: one of `C₁`, `C₂` is
always trivial. -/
theorem rec102 :
    ∃ σs : ScalarSplit C,
      Nonempty (C ≌ (dcSplitting σs separatedByStates).ε.Part ×
        (dcSplitting σs separatedByStates).ε'.Part) ∧
      (∀ P : (dcSplitting σs separatedByStates).ε.Part, Nonempty (CBAOn (Pred P))) ∧
      (∀ P : (dcSplitting σs separatedByStates).ε'.Part,
        ∃ _ : Mul (VA σs P.obj.X), JBAlgebra (VA σs P.obj.X) ∧
          IsDirectedCompleteOUS (VA σs P.obj.X) ∧
          ∃ e : Pred P ≃ Set.Icc (0 : VA σs P.obj.X) (ouUnit (VA σs P.obj.X)),
            (∀ a b : Pred P, a ≼ b ↔ (e a : VA σs P.obj.X) ≤ e b) ∧
            (∀ (a b : Pred P) (h : Perp a b), (e (ovee a b h) : VA σs P.obj.X) = e a + e b) ∧
            (e (truth P) : VA σs P.obj.X) = ouUnit (VA σs P.obj.X)) ∧
      ((rec102_cbaFunctor σs).Faithful ∧ (rec102_jbFunctor σs hAS hRC h119).Faithful ↔
        SeparatingPredicates C) := by
  obtain ⟨σs⟩ := scalarSplit_exists rec34_holds.{v} (normal (C := C)).1
  refine ⟨σs, ⟨CentralSplitting.equivalence _⟩, fun P => ⟨cbaOnPart σs P⟩, fun P => ?_, ?_⟩
  · exact ⟨jbMul σs hAS hRC h119 P.obj.X, jbMul_spec σs hAS hRC h119 P.obj.X, VA_dc σs _,
      predEquivPart σs P, predEquivPart_spec σs P⟩
  · rw [← parts_separated_iff σs, cbaPredFunctor_faithful_iff]
    apply and_congr_right'
    constructor
    · intro hF P Q f g h
      exact hF.map_injective ((rec102_jbFunctor_map_eq σs hAS hRC h119 f g).2 h)
    · intro hs
      exact ⟨fun {P Q} {f g} h => hs f g ((rec102_jbFunctor_map_eq σs hAS hRC h119 f g).1 h)⟩

/-- REC 102, addendum: in a sequential effectus one of the two factors of the
splitting is trivial — the idempotent scalar `s` of REC 35 is `0` or `1`, because
comprehensions and separation by (total) states leave no other idempotent scalars
(`idem_scalar_trivial`). -/
theorem rec102_trivial_factor (σs : ScalarSplit C) : σs.s = 0 ∨ σs.s = 𝟙 _ :=
  idem_scalar_trivial separatedByStates σs.hs

/-- **REC 104** (short.tex:1878, Remark) — **its claim is false**: the remark says
that for a sequential effectus "our scalars can satisfy `Pred(I) ≅ [0,1]_{C(X)}`
where `X` is an arbitrary Stonean space".  But the scalars of a sequential effectus
have no idempotents besides `0, 1` (`scal_irreducible_of_states`), whereas
`[0,1]_{C(X)}` has the idempotent indicator of a non-trivial clopen set as soon as
the extremally disconnected Hausdorff space `X` has two points.  So `X` has at most
one point, the scalars are `{0}`, `{0,1}` or `[0,1]` (REC 36), and every sequential
effectus has irreducible scalars: REC 102 is the case of REC 103. -/
theorem rec104_false (X : Type w) [TopologicalSpace X] [T2Space X]
    (hED : ExtremallyDisconnected X) {x y : X} (hxy : x ≠ y) :
    IsEmpty (@EMIso (Scal C) (Set.Icc (0 : C(X, ℝ)) 1) _
      (continuousUnitIntervalEffectMonoid X)) := by
  let _ := continuousUnitIntervalEffectMonoid X
  refine ⟨fun φ => ?_⟩
  have hirr := scal_irreducible_of_states (C := C) separatedByStates
  have hid := rec21_irreducible_iff.1 hirr
  -- a non-trivial clopen set
  obtain ⟨U, hU, hxU, hyU⟩ : ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ y ∉ U := by
    obtain ⟨U, V, hUo, hVo, hxU, hyV, hUV⟩ := t2_separation hxy
    refine ⟨closure U, ⟨isClosed_closure, hED.open_closure U hUo⟩, subset_closure hxU, ?_⟩
    rw [mem_closure_iff]; push Not
    exact ⟨V, hVo, hyV, by rw [Set.inter_comm]; exact hUV.inter_eq⟩
  have hχ : kmul (kind U hU) (kind U hU) = kind U hU := kind_mul_self U hU
  have he : φ.inv.toFun (kind U hU) * φ.inv.toFun (kind U hU) = φ.inv.toFun (kind U hU) := by
    rw [← φ.inv.map_mul]; exact congrArg _ hχ
  rcases hid _ he with h | h
  · have := congrArg φ.hom.toFun h
    rw [φ.hom_inv, EffectMonoidHom.map_zero'] at this
    have h2 := congrArg (fun g : Set.Icc (0 : C(X, ℝ)) 1 => (g : C(X, ℝ)) x) this
    simp only [kind_apply, Set.indicator_of_mem hxU] at h2
    exact one_ne_zero h2
  · have := congrArg φ.hom.toFun h
    rw [φ.hom_inv, φ.hom.map_one] at this
    have h2 := congrArg (fun g : Set.Icc (0 : C(X, ℝ)) 1 => (g : C(X, ℝ)) y) this
    simp only [kind_apply, Set.indicator_of_notMem hyU] at h2
    exact zero_ne_one h2

end Rec102Main


/-! ### REC 103 -/

section Rec103

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

/-- Irreducible scalars of a sequential effectus are `{0}`, `{0,1}` or `[0,1]`
(REC 36, `rec36_holds_rc`, applied to the directed-complete effect monoid `Pred(I)`). -/
theorem seq_scal_cases (hirr : IsIrreducible (Scal C)) :
    Subsingleton (Scal C) ∨ ScalarsAreTwo C ∨ IsRealEffectus C := by
  rcases rec36_holds_rc (Scal C) ((normal (C := C)).1 (effObj C)) hirr with h | h | h
  · exact Or.inl h
  · obtain ⟨φ⟩ := h; exact Or.inr (Or.inl ⟨φ.hom, φ.inv, φ.inv_hom, φ.hom_inv⟩)
  · obtain ⟨φ⟩ := h; exact Or.inr (Or.inr ⟨φ.hom, φ.inv, φ.inv_hom, φ.hom_inv⟩)

/-- With scalars `{0}` or `{0,1}` every predicate space is an orthoalgebra (REC 38). -/
theorem pred_isOrthoalgebra (h : Subsingleton (Scal C) ∨ ScalarsAreTwo C) (A : C) :
    IsOrthoalgebra (Pred A) := by
  rcases h with h | h
  · intro p _
    have h0 : (𝟙 (effObj C) : Scal C) = 0 := Subsingleton.elim _ _
    rw [← Category.comp_id p, h0, FinPAC.comp_zero]
  · exact rec38 separatedByStates h A

/-- An orthoalgebraic predicate space of a sequential effectus is a complete Boolean
algebra (REC 96, with completeness from directed completeness). -/
noncomputable def cbaOnPred (hOA : ∀ A : C, IsOrthoalgebra (Pred A)) (A : C) :
    CBAOn (Pred A) :=
  ⟨(rec96 (hOA A)).choose, fun a b => ((rec96 (hOA A)).choose_spec a b).1,
    boolean_complete_of_dc (rec96 (hOA A)).choose (fun a b => ((rec96 (hOA A)).choose_spec a b).1)
      ((normal (C := C)).1 A)⟩

/-- The splitting of real scalars `Pred(I) ≅ [0,1]`: `s = 0`, `c_λ = ψ(λ)`. -/
noncomputable def realSplit (ψ₀ : EffectMonoidHom I (Scal C)) : ScalarSplit C where
  s := 0
  hs := FinPAC.zero_comp _
  bool x hx _ := by rw [← hx, FinPAC.comp_zero]
  c := ψ₀.toFun
  c_mul l m := (ψ₀.map_mul l m).symm
  c_add l m h := ⟨ψ₀.perp_map (show Perp l m from h), (ψ₀.ovee_map (show Perp l m from h)).symm⟩
  c_one := by
    rw [ψ₀.map_one]; exact eabasics_orth_zero.symm

theorem orth_zero_scal : orth (0 : Scal C) = 𝟙 (effObj C) :=
  eabasics_orth_zero.trans scal_one_eq

/-- With `s = 0` the convex part is all of `Pred(A)`. -/
theorem cpt_all (σs : ScalarSplit C) (h0 : σs.s = 0) {A : C} (p : Pred A) :
    p ≫ orth σs.s = p := by
  rw [h0, orth_zero_scal, Category.comp_id]

variable (hAS : AlfsenShultzJordanFromDerivations.{v})
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

section JBW

variable (φ₀ : EffectMonoidHom (Scal C) I) (ψ₀ : EffectMonoidHom I (Scal C))
  (h1 : ∀ k, ψ₀.toFun (φ₀.toFun k) = k) (h2 : ∀ r, φ₀.toFun (ψ₀.toFun r) = r)

theorem realVal_hadd {a b : CPt (realSplit ψ₀) (effObj C)} (h : Perp a b) :
    ((φ₀.toFun (ovee a b h).1 : I) : ℝ) = ((φ₀.toFun a.1 : I) : ℝ) + ((φ₀.toFun b.1 : I) : ℝ) := by
  show ((φ₀.toFun (ovee a.1 b.1 h) : I) : ℝ) = _
  rw [φ₀.ovee_map h]; rfl

include h2 in
theorem realVal_hsmul (l : I) (a : CPt (realSplit ψ₀) (effObj C)) :
    ((φ₀.toFun (l • a).1 : I) : ℝ) = (l : ℝ) • ((φ₀.toFun a.1 : I) : ℝ) := by
  show ((φ₀.toFun (a.1 ≫ ψ₀.toFun l) : I) : ℝ) = (l : ℝ) • ((φ₀.toFun a.1 : I) : ℝ)
  rw [show a.1 ≫ ψ₀.toFun l = ψ₀.toFun l * a.1 from rfl, φ₀.map_mul, h2]
  rfl

/-- The real value `V_I → ℝ` of the scalars `Pred(I) ≅ [0,1]`. -/
noncomputable def realVal : VA (realSplit ψ₀) (effObj C) →ₗ[ℝ] ℝ :=
  gpLift (fun a => ((φ₀.toFun a.1 : I) : ℝ)) (realVal_hadd φ₀ ψ₀) (realVal_hsmul φ₀ ψ₀ h2)

theorem realVal_gmap (a : CPt (realSplit ψ₀) (effObj C)) :
    realVal φ₀ ψ₀ h2 (GP.gmap a) = ((φ₀.toFun a.1 : I) : ℝ) :=
  gpLift_gmap _ (realVal_hadd φ₀ ψ₀) (realVal_hsmul φ₀ ψ₀ h2) a

theorem realVal_unit : realVal φ₀ ψ₀ h2 GP.gunit = 1 := by
  show realVal φ₀ ψ₀ h2 (GP.gmap 1) = 1
  rw [realVal_gmap]
  show ((φ₀.toFun (truth (effObj C) ≫ orth 0) : I) : ℝ) = 1
  rw [orth_zero_scal, Category.comp_id, truth_effObj_eq_id, ← scal_one_eq, φ₀.map_one]; rfl

theorem realVal_nonneg {v : VA (realSplit ψ₀) (effObj C)} (hv : 0 ≤ v) :
    0 ≤ realVal φ₀ ψ₀ h2 v :=
  gpLift_nonneg (E := CPt (realSplit ψ₀) (effObj C))
    (fun a : CPt (realSplit ψ₀) (effObj C) => ((φ₀.toFun a.1 : I) : ℝ))
    (realVal_hadd φ₀ ψ₀) (realVal_hsmul φ₀ ψ₀ h2)
    (fun a : CPt (realSplit ψ₀) (effObj C) => (φ₀.toFun a.1).2.1) hv

theorem realVal_mono : Monotone (realVal φ₀ ψ₀ h2) := fun v w hvw => by
  have := realVal_nonneg φ₀ ψ₀ h2 (sub_nonneg.2 hvw); rwa [map_sub, sub_nonneg] at this

/-- `x ≼ y` in `[0,1]` iff `x ≤ y`. -/
theorem unitInterval_le_iff (x y : I) : x ≼ y ↔ (x : ℝ) ≤ y := by
  constructor
  · rintro ⟨c, _, rfl⟩; show (x : ℝ) ≤ x + c; linarith [c.2.1]
  · intro h
    refine ⟨⟨(y : ℝ) - x, by linarith, by linarith [y.2.2, x.2.1]⟩, ?_, Subtype.ext ?_⟩
    · show (x : ℝ) + ((y : ℝ) - x) ≤ 1; linarith [y.2.2]
    · show (x : ℝ) + ((y : ℝ) - x) = y; ring

theorem gmap_half (A : C) :
    GP.gmap (Papers.OAP.ihalf • (1 : CPt (realSplit ψ₀) A)) =
      (1 / 2 : ℝ) • (GP.gunit : VA (realSplit ψ₀) A) := by
  rw [GP.gmap_smul]; rfl

/-- Effect monoid morphisms are monotone (as `Papers.OAP.emHom_monotone`, not imported). -/
theorem emHom_mono_loc {M : Type*} {N : Type*} [EffectMonoid M] [EffectMonoid N]
    (f : EffectMonoidHom M N) {a b : M} (h : a ≼ b) : f.toFun a ≼ f.toFun b := by
  obtain ⟨c, hac, rfl⟩ := Papers.OAP.le_def.1 h
  exact Papers.OAP.le_def.2 ⟨f.toFun c, f.perp_map hac, by
    rw [Papers.OAP.oplus_eq (f.perp_map hac), Papers.OAP.oplus_eq hac, f.ovee_map hac]⟩

include h1 in
/-- The real value reflects the order: `V_I ≅ ℝ`. -/
theorem realVal_le_iff (v w : VA (realSplit ψ₀) (effObj C)) :
    realVal φ₀ ψ₀ h2 v ≤ realVal φ₀ ψ₀ h2 w ↔ v ≤ w := by
  refine ⟨fun h => ?_, fun h => realVal_mono φ₀ ψ₀ h2 h⟩
  rw [← sub_nonneg] at h ⊢
  rw [← map_sub] at h
  obtain ⟨N, a, hN, e⟩ := gp_affine_repr (w - v)
  rw [e] at h ⊢
  rw [map_sub, map_smul, map_smul, realVal_gmap, realVal_unit] at h
  have ha : (1 / 2 : ℝ) ≤ φ₀.toFun a.1 := by
    simp only [smul_eq_mul, mul_one] at h; nlinarith
  set half : CPt (realSplit ψ₀) (effObj C) := Papers.OAP.ihalf • (1 : CPt _ _) with hhdef
  have hhalf : ((φ₀.toFun half.1 : I) : ℝ) = 1 / 2 := by
    show ((φ₀.toFun ((truth (effObj C) ≫ orth 0) ≫ ψ₀.toFun Papers.OAP.ihalf) : I) : ℝ) = _
    rw [orth_zero_scal, Category.comp_id, truth_effObj_eq_id, Category.id_comp, h2]; rfl
  have hs : φ₀.toFun half.1 ≼ φ₀.toFun a.1 :=
    (unitInterval_le_iff _ _).2 (by rw [hhalf]; exact ha)
  have hs' := emHom_mono_loc ψ₀ hs
  rw [h1, h1] at hs'
  have hle : half ≼ a := (PredPart.le_iff _).2 hs'
  have := gmap_mono hle
  rw [hhdef, gmap_half] at this
  have h3 : (2 * N) • ((1 / 2 : ℝ) • (GP.gunit : VA (realSplit ψ₀) (effObj C))) ≤
      (2 * N) • GP.gmap a := ou_smul_le_smul (by positivity) this
  rw [_root_.smul_smul, show 2 * N * (1 / 2) = N by ring] at h3
  exact sub_nonneg.2 h3

include h1 in
theorem realVal_normal : IsNormalMap (realVal φ₀ ψ₀ h2) := by
  intro S s _ _ hs
  refine ⟨by rintro _ ⟨x, hx, rfl⟩; exact realVal_mono φ₀ ψ₀ h2 (hs.1 hx), fun t ht => ?_⟩
  have htv : realVal φ₀ ψ₀ h2 (t • GP.gunit) = t := by
    rw [map_smul, realVal_unit, smul_eq_mul, mul_one]
  have hs' : s ≤ t • (GP.gunit : VA (realSplit ψ₀) (effObj C)) :=
    hs.2 fun x hx => (realVal_le_iff φ₀ ψ₀ h1 h2 _ _).1 (by rw [htv]; exact ht ⟨x, hx, rfl⟩)
  have := realVal_mono φ₀ ψ₀ h2 hs'
  rwa [htv] at this

/-- The normal state `a ↦ ω(a)` of `V_A` for a state `ω` of the effectus
(REC 103's "these correspond to normal states `ω* : V_A → ℝ`"). -/
noncomputable def normalState {A : C} (ω : Stat A) : OUSState (VA (realSplit ψ₀) A) where
  toLin := realVal φ₀ ψ₀ h2 ∘ₗ stateLin (realSplit ψ₀) ω.1
  nonneg a ha := realVal_nonneg φ₀ ψ₀ h2 (stateLin_nonneg _ ω.1 ha)
  unital := by
    rw [LinearMap.comp_apply]
    have : stateLin (realSplit ψ₀) ω.1 (ouUnit (VA (realSplit ψ₀) A)) = GP.gunit := by
      show stateLin _ ω.1 (GP.gmap 1) = GP.gmap 1
      rw [stateLin_gmap]; congr 1; apply Subtype.ext
      show ω.1 ≫ (truth A ≫ orth 0) = truth (effObj C) ≫ orth 0
      rw [← Category.assoc, ω.2]
    rw [this, realVal_unit]

include h1 in
theorem normalState_normal {A : C} (ω : Stat A) :
    IsNormalMap (normalState φ₀ ψ₀ h2 ω).toLin := by
  intro S s hne hdir hs
  have e1 := stateLin_normal (realSplit ψ₀) ω.1 S s hne hdir hs
  have e2 := realVal_normal φ₀ ψ₀ h1 h2 _ _ (hne.image _)
    (hdir.mono_comp (monotone_of_pos fun _ hv => stateLin_nonneg _ ω.1 hv)) e1
  rw [Set.image_image] at e2
  exact e2

include h1 h2 in
/-- With `Pred(I) ≅ [0,1]`, the normal states of the effectus separate `V_A`: it is a
JBW-algebra (REC 48) once it is a JB-algebra. -/
theorem separating_normal_states (A : C) :
    HasSeparatingNormalStates (VA (realSplit ψ₀) A) := by
  intro v w hvw
  obtain ⟨N, a, hN, e⟩ := gp_affine_repr (v - w)
  set half : CPt (realSplit ψ₀) A := Papers.OAP.ihalf • (1 : CPt _ _) with hhdef
  have hne : a.1 ≠ half.1 := by
    intro h
    have : a = half := Subtype.ext h
    apply hvw
    rw [← sub_eq_zero, e, this, hhdef, gmap_half, _root_.smul_smul,
      show 2 * N * (1 / 2) = N by ring, sub_self]
  obtain ⟨ω, hω⟩ : ∃ ω : Stat A, ω.1 ≫ a.1 ≠ ω.1 ≫ half.1 := by
    by_contra hc; push Not at hc
    exact hne (separatedByStates _ _ hc)
  refine ⟨normalState φ₀ ψ₀ h2 ω, normalState_normal φ₀ ψ₀ h1 h2 ω, fun heq => ?_⟩
  have h0 : (normalState φ₀ ψ₀ h2 ω).toLin (v - w) = 0 := by rw [map_sub, heq, sub_self]
  have hu : (normalState φ₀ ψ₀ h2 ω).toLin GP.gunit = 1 := (normalState φ₀ ψ₀ h2 ω).unital
  rw [e, map_sub, map_smul, map_smul, hu] at h0
  have hga : (normalState φ₀ ψ₀ h2 ω).toLin (GP.gmap a) = ((φ₀.toFun (ω.1 ≫ a.1) : I) : ℝ) := by
    show realVal φ₀ ψ₀ h2 (stateLin _ ω.1 (GP.gmap a)) = _
    rw [stateLin_gmap, realVal_gmap]; rfl
  rw [hga] at h0
  have hhalf : ((φ₀.toFun (ω.1 ≫ half.1) : I) : ℝ) = 1 / 2 := by
    show ((φ₀.toFun (ω.1 ≫ ((truth A ≫ orth 0) ≫ ψ₀.toFun Papers.OAP.ihalf)) : I) : ℝ) = _
    rw [← Category.assoc, ← Category.assoc, ω.2, orth_zero_scal, Category.comp_id,
      truth_effObj_eq_id, Category.id_comp, h2]; rfl
  apply hω
  have h3 : ((φ₀.toFun (ω.1 ≫ a.1) : I) : ℝ) = ((φ₀.toFun (ω.1 ≫ half.1) : I) : ℝ) := by
    rw [hhalf]; simp only [smul_eq_mul, mul_one] at h0
    have : (2 * N) * ((φ₀.toFun (ω.1 ≫ a.1) : I) : ℝ) = N := by linarith
    field_simp at this ⊢; nlinarith
  have h4 : φ₀.toFun (ω.1 ≫ a.1) = φ₀.toFun (ω.1 ≫ half.1) := Subtype.ext h3
  rw [← h1 (ω.1 ≫ a.1), h4, h1]

end JBW

/-- `V_A` as an object of `JBW_npc`. -/
noncomputable def jbwObj (σs : ScalarSplit C)
    (hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A)) (A : C) :
    JBWnpcCat.{v} :=
  @JBWnpcCat.mk (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A) (hJBW A)

theorem stateLin_id (σs : ScalarSplit C) (A : C) : stateLin σs (𝟙 A) = LinearMap.id :=
  gp_linearMap_ext fun a => by
    rw [stateLin_gmap, LinearMap.id_apply]; congr 1; exact Subtype.ext (Category.id_comp _)

/-- The predicate functor `C → JBW_npcᵒᵖ` of REC 103 (`A ↦ V_A`, `f ↦ Pred(f)`). -/
noncomputable def rec103_jbwFunctor (σs : ScalarSplit C)
    (hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A)) :
    C ⥤ JBWnpcCat.{v}ᵒᵖ where
  obj A := Opposite.op (jbwObj hAS hRC h119 σs hJBW A)
  map f := Quiver.Hom.op ⟨stateLin σs f, stateLin_isNPC σs f⟩
  map_id A := by
    apply Quiver.Hom.unop_inj; apply Subtype.ext; exact stateLin_id σs A
  map_comp f g := by
    apply Quiver.Hom.unop_inj; apply Subtype.ext; exact stateLin_comp σs f g

theorem rec103_jbwFunctor_faithful_iff (σs : ScalarSplit C) (h0 : σs.s = 0)
    (hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A)) :
    (rec103_jbwFunctor hAS hRC h119 σs hJBW).Faithful ↔ SeparatingPredicates C := by
  have key : ∀ {A B : C} (f g : A ⟶ B), (rec103_jbwFunctor hAS hRC h119 σs hJBW).map f =
      (rec103_jbwFunctor hAS hRC h119 σs hJBW).map g ↔ ∀ b : Pred B, f ≫ b = g ≫ b := by
    intro A B f g
    constructor
    · intro h b
      have hl : stateLin σs f = stateLin σs g :=
        congrArg Subtype.val (congrArg Quiver.Hom.unop h)
      have := congrArg (fun φ => φ (GP.gmap (cptMk σs (A := B) b (cpt_all σs h0 b)))) hl
      simp only [stateLin_gmap] at this
      exact congrArg (fun x : CPt σs A => x.1) (GP.gmap_injective this)
    · intro h
      apply Quiver.Hom.unop_inj; apply Subtype.ext
      refine gp_linearMap_ext fun a => ?_
      show stateLin σs f (GP.gmap a) = stateLin σs g (GP.gmap a)
      rw [stateLin_gmap, stateLin_gmap]; congr 1; exact Subtype.ext (h a.1)
  constructor
  · intro hF A B f g h
    exact hF.map_injective ((key f g).2 h)
  · intro hs
    exact ⟨fun {A B} {f g} h => hs f g ((key f g).1 h)⟩

/-- **REC 103** (`thm:JBW-CBA`, short.tex:1874, Theorem): a sequential effectus with
irreducible scalars has either all predicate spaces complete Boolean algebras, or all
of them unit intervals of JBW-algebras; the predicate functor `C → CBAᵒᵖ` resp.
`C → JBW_npcᵒᵖ` is faithful iff `C` is separated by predicates.  The paper's proof:
the scalars are `{0}`, `{0,1}` or `[0,1]` (REC 36, discharged here through REC 34 =
OAP 69); in the first two cases the predicate spaces are orthoalgebras (REC 38), hence
complete Boolean algebras (REC 96); with `[0,1]` scalars they are unit intervals of
directed-complete JB-algebras (REC 121), and the effectus's states give normal states
of `V_A` separating it, so `V_A` is JBW.  Named hypotheses as for REC 102.  (The
irreducibility hypothesis is automatic, `scal_irreducible_of_states`; "CBA *of*
JBW_npc" is read "CBA *or* JBW_npc", PLAN flag 11.) -/
theorem rec103 (hirr : IsIrreducible (Scal C)) :
    (∃ hB : ∀ A : C, CBAOn (Pred A), (cbaPredFunctor hB).Faithful ↔ SeparatingPredicates C) ∨
    (∃ (σs : ScalarSplit C) (hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A)),
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : VA σs A) (ouUnit (VA σs A)),
        (∀ a b : Pred A, a ≼ b ↔ (e a : VA σs A) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b), (e (ovee a b h) : VA σs A) = e a + e b) ∧
        (e (truth A) : VA σs A) = ouUnit (VA σs A)) ∧
      ((rec103_jbwFunctor hAS hRC h119 σs hJBW).Faithful ↔ SeparatingPredicates C)) := by
  rcases seq_scal_cases hirr with h | h | ⟨φ₀, ψ₀, h1, h2⟩
  · exact Or.inl ⟨cbaOnPred (pred_isOrthoalgebra (Or.inl h)), cbaPredFunctor_faithful_iff _⟩
  · exact Or.inl ⟨cbaOnPred (pred_isOrthoalgebra (Or.inr h)), cbaPredFunctor_faithful_iff _⟩
  · right
    set σs := realSplit ψ₀ with hσs
    have h0 : σs.s = 0 := rfl
    have hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A) := fun A =>
      @JBWAlgebra.mk (VA σs A) _ _ _ _ (jbMul σs hAS hRC h119 A) (jbMul_spec σs hAS hRC h119 A)
        (VA_dc σs A) (separating_normal_states φ₀ ψ₀ h1 h2 A)
    refine ⟨σs, hJBW, fun A => ?_, rec103_jbwFunctor_faithful_iff hAS hRC h119 σs h0 hJBW⟩
    let e₁ : Pred A ≃ CPt σs A :=
      ⟨fun p => cptMk σs p (cpt_all σs h0 p), fun q => q.1, fun _ => rfl, fun _ => rfl⟩
    refine ⟨e₁.trans (Papers.OAP.gpEquiv (CPt σs A)), fun a b => ?_, fun a b h => ?_, ?_⟩
    · exact (PredPart.le_iff (orth_idem σs.hs) (p := cptMk σs a (cpt_all σs h0 a))
        (q := cptMk σs b (cpt_all σs h0 b))).symm.trans
          (Papers.OAP.gmap_le_gmap_iff (E := CPt σs A)).symm
    · show GP.gmap (cptMk σs (ovee a b h) _) = GP.gmap (cptMk σs a _) + GP.gmap (cptMk σs b _)
      have hp : Perp (cptMk σs a (cpt_all σs h0 a)) (cptMk σs b (cpt_all σs h0 b)) := h
      rw [← GP.gmap_ovee hp]; rfl
    · show GP.gmap (cptMk σs (truth A) _) = GP.gmap 1
      congr 1; apply Subtype.ext
      show truth A = truth A ≫ orth σs.s
      rw [cpt_all σs h0]

end Rec103

end Papers.REC
