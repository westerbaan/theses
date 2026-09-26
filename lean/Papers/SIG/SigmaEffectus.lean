/-
Papers/SIG/SigmaEffectus.lean

SIG §3 up to §3.1 (main.tex:437–768), points SIG 12, 13, 16–23: effectuses
and σ-effectuses, their morphisms, tests, σ-effect algebras (and their
canonical countable sums), Proposition 18 and Corollary 19, σ-additivity
versus ω-continuity (Lemma 20), (σ-)effect monoids and their examples.

Design (see `Papers/SIG/PLAN.md`):
* `SigmaEffectus C` is a new class over `[HasCountableCoproducts C]` and a
  σ-PAM on each hom-set; its fields are the printed axioms.  Every
  σ-effectus is a tree effectus in partial form (instance
  `effectusPartialForm_of_sigmaEffectus`), so the tree's `Pred`, `Scal`,
  `Substate`, `Stat`, `IsTotal`, `effPair`, … apply.
* A σ-effect algebra is an effect algebra whose `≼` is ω-complete; its
  canonical countable sums are the relation `IsCSum x s` ("`s` is the
  supremum of the finite partial sums of `x`"), not a second instance.
* Points 14, 15 (the examples `Pfn` and `W*ᵒᵖ`) live in their own files.
-/
import Papers.SIG.Prelim
import Theses.B.Eff.StatesPredicates

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits Theses.B.Eff

namespace Papers.SIG

open SigmaPAM

universe u v u' v'

/-! ## SIG 12: effectuses, σ-effectuses and their morphisms -/

/-- **SIG 12** (`def:effectus`, main.tex:440, Definition): an **effectus**
(in partial form) is a finPAC `C` with a unit object `I` such that
(i) each `C(A, I)` is an effect algebra, with top `1_A` and bottom `0`;
(ii) `1 ∘ f = 0` implies `f = 0`; (iii) `1 ∘ f ⊥ 1 ∘ g` implies `f ⊥ g`.
This is the tree's `EffectusPartialForm` over a `FinPAC` (180VII); the
theorem records the three printed conditions in the tree's terms. -/
theorem effectus_conditions {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] :
    (∀ A : C, (1 : A ⟶ effObj C) = truth A ∧ (0 : A ⟶ effObj C) = 0) ∧
      (∀ {A B : C} (f : A ⟶ B), f ≫ truth B = 0 → f = 0) ∧
      (∀ {A B : C} (f g : A ⟶ B), Perp (f ≫ truth B) (g ≫ truth B) → Perp f g) :=
  ⟨fun _ => ⟨rfl, rfl⟩, fun _ h => EffectusPartialForm.eq_zero_of_one_zero h,
    fun _ _ h => EffectusPartialForm.perp_of_one_perp h⟩

/-- **SIG 12** (`def:effectus`, main.tex:461, Definition): a **σ-effectus**
is a σ-PAC `C` with a distinguished object `I` satisfying the same
conditions (i)–(iii): each `C(A, I)` (with the PCM induced by its σ-PAM) is
an effect algebra with top `1_A`, `1 ∘ f = 0` implies `f = 0`, and
`1 ∘ f ⊥ 1 ∘ g` implies `f ⊥ g`.  The fields spell out the effect-algebra
structure of `C(A, I)` on top of the hom-PCM, as the tree does (180VII). -/
class SigmaEffectus (C : Type u) [Category.{v} C] [HasCountableCoproducts C]
    [∀ X Y : C, SigmaPAM (X ⟶ Y)] extends SigmaPAC C where
  I : C
  one : ∀ X : C, X ⟶ I
  orth : ∀ {X : C}, (X ⟶ I) → (X ⟶ I)
  perp_orth : ∀ {X : C} (p : X ⟶ I), Perp p (orth p)
  ovee_orth : ∀ {X : C} (p : X ⟶ I), ovee p (orth p) (perp_orth p) = one X
  orth_unique : ∀ {X : C} {p q : X ⟶ I} (h : Perp p q), ovee p q h = one X → q = orth p
  eq_zero_of_perp_one : ∀ {X : C} {p : X ⟶ I}, Perp p (one X) → p = 0
  eq_zero_of_one_zero : ∀ {X Y : C} {f : X ⟶ Y}, f ≫ one Y = 0 → f = 0
  perp_of_one_perp : ∀ {X Y : C} {f g : X ⟶ Y}, Perp (f ≫ one Y) (g ≫ one Y) → Perp f g

/-- **SIG 12** (`def:effectus`, main.tex:461): every σ-effectus is an
effectus (in partial form), for the finPAC structure `finPAC_of_sigmaPAC`. -/
noncomputable instance effectusPartialForm_of_sigmaEffectus {C : Type u} [Category.{v} C]
    [HasCountableCoproducts C] [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C] :
    EffectusPartialForm C where
  I := SigmaEffectus.I
  one := SigmaEffectus.one
  orth := SigmaEffectus.orth
  perp_orth := SigmaEffectus.perp_orth
  ovee_orth := SigmaEffectus.ovee_orth
  orth_unique := SigmaEffectus.orth_unique
  eq_zero_of_perp_one := SigmaEffectus.eq_zero_of_perp_one
  perp_of_one_perp := SigmaEffectus.perp_of_one_perp
  eq_zero_of_one_zero := SigmaEffectus.eq_zero_of_one_zero

/-- **SIG 12** (`def:effectus`, main.tex:475, Definition): a **morphism of
effectuses** `C → D` is a functor `F` preserving finite coproducts and the
unit: there is an isomorphism `u : I_D ≅ F I_C` with `F 1_A = u ∘ 1_{FA}`. -/
structure EffectusMorphism (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
    (D : Type u') [Category.{v'} D] [HasFiniteCoproducts D]
    [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D] [EffectusPartialForm D] where
  F : C ⥤ D
  preserves : PreservesFiniteCoproducts F
  u : effObj D ≅ F.obj (effObj C)
  map_truth : ∀ A : C, F.map (truth A) = truth (F.obj A) ≫ u.hom

/-- **SIG 12** (`def:effectus`, main.tex:475, Definition): a **morphism of
σ-effectuses** preserves countable coproducts and the unit. -/
structure SigmaEffectusMorphism (C : Type u) [Category.{v} C] [HasCountableCoproducts C]
    [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]
    (D : Type u') [Category.{v'} D] [HasCountableCoproducts D]
    [∀ X Y : D, SigmaPAM (X ⟶ Y)] [SigmaEffectus D] where
  F : C ⥤ D
  preserves : ∀ (J : Type) [Countable J], PreservesColimitsOfShape (Discrete J) F
  u : effObj D ≅ F.obj (effObj C)
  map_truth : ∀ A : C, F.map (truth A) = truth (F.obj A) ≫ u.hom

/-! **SIG 12** (main.tex:481–494): *predicates* `Pred A = C(A, I)`, *substates*
`C(I, A)`, *total* maps (`1 ∘ f = 1`, forming the wide subcategory `Tot C`),
*states* (total substates) and *scalars* `C(I, I)` are the tree's `Pred`,
`Substate`, `IsTotal`, `Tot`, `Stat` and `Scal` (190II), which apply to a
σ-effectus through `effectusPartialForm_of_sigmaEffectus`. -/

/-- **SIG 13** (`remark:operational-interpretation`, main.tex:496, Remark):
in the operational reading of a (σ-)effectus, a **test** from `A` to `B` is a
summable family of events `(f_x : A ⟶ B)_{x ∈ X}` whose sum is total. -/
def IsTest {C : Type u} [Category.{v} C] [HasCountableCoproducts C]
    [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C] {A B : C} {X : Type} [Countable X]
    (f : X → (A ⟶ B)) : Prop :=
  ∃ s : A ⟶ B, SumsTo f s ∧ IsTotal s

/-- **SIG 13** (main.tex:518): a closed test `(s_x : I ⟶ I)` has
`⋁ s_x = 1`. -/
theorem isTest_scalar_iff {C : Type u} [Category.{v} C] [HasCountableCoproducts C]
    [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C] {X : Type} [Countable X]
    (f : X → Scal C) : IsTest f ↔ SumsTo f (1 : Scal C) := by
  constructor
  · rintro ⟨s, hs, ht⟩
    have : s = 1 := by
      have h' : s ≫ truth (effObj C) = truth (effObj C) := ht
      rw [truth_effObj_eq_id, Category.comp_id] at h'
      exact h'.trans truth_effObj_eq_id.symm
    rwa [this] at hs
  · intro h
    refine ⟨1, h, ?_⟩
    show truth (effObj C) ≫ truth (effObj C) = truth (effObj C)
    rw [truth_effObj_eq_id, Category.comp_id]

/-! **SIG 16** (`partial-total-remark`, main.tex:574, Remark): effectuses in
partial form correspond to effectuses in total form (Cho): this is the tree's
`Theses.B.Eff.eff_partial_to_total` and `cho_thm_*` (180X).  Whether
σ-effectuses in total form admit an intrinsic characterisation is left open
by the paper; nothing to formalise. -/

/-! ## SIG 17–20: σ-effect algebras -/

section SigmaEA

variable {E : Type u} [EffectAlgebra E]

/-- `s` is the supremum of `S` for the effect-algebra order `≼`. -/
def IsSupOf (S : Set E) (s : E) : Prop :=
  (∀ t ∈ S, t ≼ s) ∧ ∀ c, (∀ t ∈ S, t ≼ c) → s ≼ c

theorem IsSupOf.unique {S : Set E} {s t : E} (hs : IsSupOf S s) (ht : IsSupOf S t) : s = t :=
  eabasics_le_antisymm (hs.2 t ht.1) (ht.2 s hs.1)

/-- Suprema of mutually cofinal sets agree. -/
theorem isSupOf_iff_of_cofinal {S T : Set E} (hTS : ∀ b ∈ T, ∃ a ∈ S, b ≼ a)
    (hST : ∀ a ∈ S, ∃ b ∈ T, a ≼ b) (s : E) : IsSupOf S s ↔ IsSupOf T s := by
  have key : ∀ {S T : Set E}, (∀ b ∈ T, ∃ a ∈ S, b ≼ a) → (∀ a ∈ S, ∃ b ∈ T, a ≼ b) →
      IsSupOf S s → IsSupOf T s := by
    intro S T hTS hST hs
    refine ⟨fun b hb => ?_, fun c hc => hs.2 c fun a ha => ?_⟩
    · obtain ⟨a, ha, hba⟩ := hTS b hb
      exact pcm_preorder_trans hba (hs.1 a ha)
    · obtain ⟨b, hb, hab⟩ := hST a ha
      exact pcm_preorder_trans hab (hc b hb)
  exact ⟨key hTS hST, key hST hTS⟩

/-- **SIG 17** (`def:sigma-effect-algebra`, main.tex:609, Definition): the
order of an effect algebra is **ω-complete** if every increasing sequence
`a₀ ≤ a₁ ≤ ⋯` has a supremum. -/
def OmegaComplete (E : Type u) [EffectAlgebra E] : Prop :=
  ∀ a : ℕ → E, (∀ n, a n ≼ a (n + 1)) → ∃ s, IsSupOf (Set.range a) s

/-- **SIG 17** (`def:sigma-effect-algebra`, main.tex:609, Definition): a
**σ-effect algebra** is an effect algebra whose order is ω-complete. -/
def IsSigmaEffectAlgebra (E : Type u) [EffectAlgebra E] : Prop := OmegaComplete E

variable {J : Type}

/-- The finite partial sum `⊕_{j∈F} x_j` (as a relation). -/
def FinSum (x : J → E) (F : Finset J) (s : E) : Prop := PCM.IsSumOf (F.toList.map x) s

/-- **SIG 17** (main.tex:618, Definition): a countable family is
**summable** when all its finite subfamilies are. -/
def CSummable (x : J → E) : Prop := ∀ F : Finset J, ∃ s, FinSum x F s

/-- **SIG 17** (main.tex:621, Definition): the canonical countable sum:
`⋁_j x_j = ⋁_F ⊕_{j∈F} x_j`, the supremum of the finite partial sums. -/
def IsCSum (x : J → E) (s : E) : Prop := CSummable x ∧ IsSupOf {t | ∃ F, FinSum x F t} s

theorem finSum_unique {x : J → E} {F : Finset J} {s t : E} (hs : FinSum x F s)
    (ht : FinSum x F t) : s = t := isSumOf_unique hs ht

theorem IsCSum.unique {x : J → E} {s t : E} (hs : IsCSum x s) (ht : IsCSum x t) : s = t :=
  hs.2.unique ht.2

theorem finSum_empty (x : J → E) : FinSum x ∅ 0 := by
  unfold FinSum; rw [Finset.toList_empty]; exact PCM.IsSumOf.nil

theorem finSum_insert [DecidableEq J] (x : J → E) {F : Finset J} {j : J} (hj : j ∉ F)
    (s : E) : FinSum x (insert j F) s ↔ PCM.IsSumOf (x j :: F.toList.map x) s := by
  unfold FinSum
  have hp := (Finset.toList_insert hj).map x
  exact ⟨PCM.isSumOf_perm hp, PCM.isSumOf_perm hp.symm⟩

/-- The list of `G` is a permutation of the lists of `F` and `G \ F`. -/
theorem toList_perm_sdiff [DecidableEq J] {F G : Finset J} (hFG : F ⊆ G) :
    G.toList.Perm (F.toList ++ (G \ F).toList) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, Finset.coe_toList, Finset.coe_toList,
    Finset.coe_toList]
  have : G = F.disjUnion (G \ F) Finset.disjoint_sdiff := by
    rw [Finset.disjUnion_eq_union, Finset.union_sdiff_of_subset hFG]
  conv_lhs => rw [this]
  rfl

/-- Monotonicity of finite partial sums. -/
theorem finSum_mono {x : J → E} {F G : Finset J} (hFG : F ⊆ G) {t : E} (ht : FinSum x G t) :
    ∃ s, FinSum x F s ∧ s ≼ t := by
  classical
  have hp : (G.toList.map x).Perm (F.toList.map x ++ (G \ F).toList.map x) := by
    rw [← List.map_append]; exact (toList_perm_sdiff hFG).map x
  obtain ⟨s₁, s₂, h₁, -, hp', e⟩ := isSumOf_split (PCM.isSumOf_perm hp ht)
  exact ⟨s₁, h₁, s₂, hp', e⟩

theorem CSummable.of_chain {x : J → E} {G : ℕ → Finset J} (hcof : ∀ F : Finset J, ∃ n, F ⊆ G n)
    (ht : ∀ n, ∃ t, FinSum x (G n) t) : CSummable x := by
  intro F
  obtain ⟨n, hn⟩ := hcof F
  obtain ⟨t, ht⟩ := ht n
  obtain ⟨s, hs, -⟩ := finSum_mono hn ht
  exact ⟨s, hs⟩

/-- The canonical sum is the supremum along any increasing cofinal chain of
finite subsets. -/
theorem isCSum_iff_of_chain {x : J → E} (hx : CSummable x) {G : ℕ → Finset J}
    (hcof : ∀ F : Finset J, ∃ n, F ⊆ G n) {t : ℕ → E} (ht : ∀ n, FinSum x (G n) (t n))
    (s : E) : IsCSum x s ↔ IsSupOf (Set.range t) s := by
  unfold IsCSum
  rw [and_iff_right hx]
  refine isSupOf_iff_of_cofinal ?_ ?_ s
  · rintro _ ⟨n, rfl⟩
    exact ⟨t n, ⟨G n, ht n⟩, pcm_preorder_refl _⟩
  · rintro a ⟨F, hF⟩
    obtain ⟨n, hn⟩ := hcof F
    obtain ⟨s', hs', hle⟩ := finSum_mono hn (ht n)
    rw [finSum_unique hF hs']
    exact ⟨t n, ⟨n, rfl⟩, hle⟩

/-- A countable index set has an increasing chain of finite subsets
exhausting it. -/
theorem exists_chain (J : Type) [Countable J] :
    ∃ G : ℕ → Finset J, Monotone G ∧ ∀ F : Finset J, ∃ n, F ⊆ G n := by
  classical
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact ⟨fun _ => ∅, fun _ _ _ => le_rfl, fun F => ⟨0, by
      rw [Finset.eq_empty_of_isEmpty F]⟩⟩
  · obtain ⟨g, hg⟩ := exists_surjective_nat J
    refine ⟨fun n => (Finset.range n).image g, fun m n hmn =>
      Finset.image_subset_image (Finset.range_mono hmn), fun F => ?_⟩
    let g' := Function.surjInv hg
    refine ⟨(F.image g').sup id + 1, fun j hj => ?_⟩
    rw [Finset.mem_image]
    refine ⟨g' j, Finset.mem_range.2 (Nat.lt_succ_of_le ?_), Function.surjInv_eq hg j⟩
    exact Finset.le_sup (f := id) (Finset.mem_image_of_mem g' hj)

/-- In an ω-complete effect algebra every summable countable family has a
canonical sum (the supremum in SIG 17 exists "by ω-completeness"). -/
theorem exists_isCSum (hE : OmegaComplete E) [Countable J] {x : J → E} (hx : CSummable x) :
    ∃ s, IsCSum x s := by
  obtain ⟨G, hG, hcof⟩ := exists_chain J
  choose t ht using fun n => hx (G n)
  have hmono : ∀ n, t n ≼ t (n + 1) := by
    intro n
    obtain ⟨s, hs, hle⟩ := finSum_mono (hG (Nat.le_succ n)) (ht (n + 1))
    rwa [finSum_unique (ht n) hs]
  obtain ⟨s, hs⟩ := hE t hmono
  exact ⟨s, (isCSum_iff_of_chain hx hcof ht s).2 hs⟩

/-- An additive map preserves finite sums. -/
theorem IsAdditive.isSumOf {D : Type v} [EffectAlgebra D] {f : E → D} (hf : IsAdditive f)
    {l : List E} {s : E} (h : PCM.IsSumOf l s) : PCM.IsSumOf (l.map f) (f s) := by
  induction h with
  | nil => rw [hf.1]; exact PCM.IsSumOf.nil
  | cons hl hp ih =>
    obtain ⟨hp', e⟩ := hf.2 hp
    rw [← e]; exact PCM.IsSumOf.cons ih hp'

theorem IsAdditive.finSum {D : Type v} [EffectAlgebra D] {f : E → D} (hf : IsAdditive f)
    {x : J → E} {F : Finset J} {s : E} (h : FinSum x F s) : FinSum (fun j => f (x j)) F (f s) := by
  have := hf.isSumOf h
  rwa [List.map_map] at this

/-- The differences `b₀ = a₀`, `b_{n+1} = a_{n+1} ⊖ a_n` of an increasing
sequence (as in the proof of SIG 18). -/
noncomputable def diffSeq (a : ℕ → E) (ha : ∀ n, a n ≼ a (n + 1)) : ℕ → E
  | 0 => a 0
  | n + 1 => ominus (a (n + 1)) (a n) (ha n)

theorem finSum_diffSeq (a : ℕ → E) (ha : ∀ n, a n ≼ a (n + 1)) (n : ℕ) :
    FinSum (diffSeq a ha) (Finset.range (n + 1)) (a n) := by
  induction n with
  | zero =>
    unfold FinSum
    rw [Finset.range_one, Finset.toList_singleton]
    have := isSumOf_singleton (diffSeq a ha 0)
    exact this
  | succ n ih =>
    rw [Finset.range_add_one, finSum_insert _ Finset.notMem_range_self]
    obtain ⟨h, e⟩ := isDiff_ominus (ha n)
    have h' : Perp (diffSeq a ha (n + 1)) (a n) := PCM.perp_comm h
    have e' : ovee (diffSeq a ha (n + 1)) (a n) h' = a (n + 1) := by
      rw [← PCM.ovee_comm]; exact e
    rw [← e']
    exact PCM.IsSumOf.cons ih h'

theorem cofinal_range (F : Finset ℕ) : ∃ n, F ⊆ Finset.range (n + 1) := by
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range F
  exact ⟨n, hn.trans (Finset.range_mono (Nat.le_succ n))⟩

theorem isCSum_diffSeq_iff (a : ℕ → E) (ha : ∀ n, a n ≼ a (n + 1)) (s : E) :
    IsCSum (diffSeq a ha) s ↔ IsSupOf (Set.range a) s :=
  isCSum_iff_of_chain (CSummable.of_chain cofinal_range fun n => ⟨_, finSum_diffSeq a ha n⟩)
    cofinal_range (finSum_diffSeq a ha) s

end SigmaEA

/-- "The σ-PAM structure extends the PCM structure of `E`": binary σ-sums are
the effect-algebra sums. -/
def SigmaPAMExtends (E : Type u) [EffectAlgebra E] [SigmaPAM E] : Prop :=
  ∀ a b s : E, (∃ h : Perp a b, ovee a b h = s) ↔ SumsTo ![a, b] s

/-! ### The canonical σ-PAM of a σ-effect algebra

The text after SIG 17 (main.tex:625): "the definition of sums of countable
families equips each σ-effect algebra with a canonical σ-PAM structure that
extends its PCM structure" — printed without proof.  The substance is
partition-associativity of canonical sums, which rests on the fact that `⊕`
preserves suprema of increasing sequences (`isSupOf_ovee_chain`). -/

section Canonical

variable {E : Type u} [EffectAlgebra E]

theorem chain_le {a : ℕ → E} (ha : ∀ n, a n ≼ a (n + 1)) {m n : ℕ} (h : m ≤ n) :
    a m ≼ a n := by
  induction h with
  | refl => exact pcm_preorder_refl _
  | step _ ih => exact pcm_preorder_trans ih (ha _)

/-- Order cancellation: `a ⊕ y ≤ a ⊕ z` implies `y ≤ z`. -/
theorem le_of_ovee_le_ovee {a y z : E} (hy : Perp a y) (hz : Perp a z)
    (h : ovee a y hy ≼ ovee a z hz) : y ≼ z := by
  obtain ⟨w, hw, e⟩ := h
  have h1 : Perp y w := PCM.perp_of_ovee_perp hy hw
  have h2 : Perp a (ovee y w h1) := PCM.perp_ovee_of_ovee_perp hy hw
  have e2 : ovee a (ovee y w h1) h2 = ovee a z hz := (PCM.ovee_assoc hy hw).symm.trans e
  refine ⟨w, h1, eabasics_cancellation (PCM.perp_comm h2) (PCM.perp_comm hz) ?_⟩
  exact (PCM.ovee_comm h2).symm.trans (e2.trans (PCM.ovee_comm hz))

/-- Monotonicity of `⊕` in both arguments. -/
theorem ovee_le_ovee {a a' b b' : E} (ha : a ≼ a') (hb : b ≼ b') (h' : Perp a' b') :
    ∃ h : Perp a b, ovee a b h ≼ ovee a' b' h' := by
  obtain ⟨h1, l1⟩ := eabasics_le_perp_compat ha h'
  obtain ⟨h2, l2⟩ := eabasics_le_perp_compat hb (PCM.perp_comm h1)
  refine ⟨PCM.perp_comm h2, pcm_preorder_trans ?_ l1⟩
  rw [PCM.ovee_comm (PCM.perp_comm h2), PCM.ovee_comm h1]
  exact l2

/-- `x ≤ c` with `c = x ⊕ d`: then `x ⊕ y ≤ c` iff `y ≤ d`. -/
theorem le_of_ovee_le {x y c : E} (hxy : Perp x y) (h : ovee x y hxy ≼ c) (hx : x ≼ c) :
    ∃ d, ∃ hd : Perp x d, ovee x d hd = c ∧ y ≼ d := by
  obtain ⟨d, hd, rfl⟩ := hx
  exact ⟨d, hd, rfl, le_of_ovee_le_ovee hxy hd h⟩

/-- **`⊕` preserves suprema of increasing sequences**: if `aₙ ↑ a`,
`bₙ ↑ b` and `aₙ ⊥ bₙ` for all `n`, then `a ⊥ b` and `a ⊕ b = ⋁ (aₙ ⊕ bₙ)`. -/
theorem isSupOf_ovee_chain {a b : ℕ → E} (ha : ∀ n, a n ≼ a (n + 1))
    (hb : ∀ n, b n ≼ b (n + 1)) {sa sb : E} (hsa : IsSupOf (Set.range a) sa)
    (hsb : IsSupOf (Set.range b) sb) (h : ∀ n, Perp (a n) (b n)) :
    ∃ hs : Perp sa sb, IsSupOf (Set.range fun n => ovee (a n) (b n) (h n)) (ovee sa sb hs) := by
  -- `a m ⊥ b n` for all `m, n`
  have hmn : ∀ m n, Perp (a m) (b n) := by
    intro m n
    exact (ovee_le_ovee (chain_le ha (le_max_left m n)) (chain_le hb (le_max_right m n))
      (h (max m n))).1
  -- `a m ⊥ sb`
  have hm : ∀ m, Perp (a m) sb := by
    intro m
    have : sb ≼ orth (a m) := hsb.2 _ (by
      rintro _ ⟨n, rfl⟩
      exact eabasics_perp_iff_le_orth.1 (PCM.perp_comm (hmn m n)))
    exact PCM.perp_comm (eabasics_perp_iff_le_orth.2 this)
  have hs : Perp sa sb := by
    refine eabasics_perp_iff_le_orth.2 (hsa.2 _ ?_)
    rintro _ ⟨m, rfl⟩
    exact eabasics_perp_iff_le_orth.1 (hm m)
  refine ⟨hs, ?_, fun c hc => ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (ovee_le_ovee (hsa.1 _ ⟨n, rfl⟩) (hsb.1 _ ⟨n, rfl⟩) hs).2
  · -- for each `m`: `a m ⊕ b n ≤ c` for all `n`, hence `a m ⊕ sb ≤ c`
    have step1 : ∀ m, ∃ hp : Perp (a m) sb, ovee (a m) sb hp ≼ c := by
      intro m
      have hle : ∀ n, ovee (a m) (b n) (hmn m n) ≼ c := by
        intro n
        have hk := hc _ ⟨max m n, rfl⟩
        exact pcm_preorder_trans (ovee_le_ovee (chain_le ha (le_max_left m n))
          (chain_le hb (le_max_right m n)) (h (max m n))).2 hk
      have hac : a m ≼ c := pcm_preorder_trans
        ⟨b 0, hmn m 0, rfl⟩ (hle 0)
      obtain ⟨d, hd, e, -⟩ := le_of_ovee_le (hmn m 0) (hle 0) hac
      have hbd : sb ≼ d := hsb.2 d (by
        rintro _ ⟨n, rfl⟩
        exact le_of_ovee_le_ovee (hmn m n) hd (e ▸ hle n))
      obtain ⟨hp, hle'⟩ := ovee_le_ovee (pcm_preorder_refl (a m)) hbd hd
      exact ⟨hp, e ▸ hle'⟩
    -- then `sa ⊕ sb ≤ c`, symmetrically
    have hsbc : sb ≼ c := pcm_preorder_trans ⟨a 0, PCM.perp_comm (hm 0), by
      rw [← PCM.ovee_comm]⟩ (step1 0).2
    obtain ⟨d, hd, e, -⟩ := le_of_ovee_le (PCM.perp_comm (hm 0))
      (by rw [← PCM.ovee_comm]; exact (step1 0).2) hsbc
    have had : sa ≼ d := hsa.2 d (by
      rintro _ ⟨m, rfl⟩
      obtain ⟨hp, hle⟩ := step1 m
      refine le_of_ovee_le_ovee (PCM.perp_comm hp) hd ?_
      rw [e, ← PCM.ovee_comm]; exact hle)
    obtain ⟨hp, hle'⟩ := ovee_le_ovee had (pcm_preorder_refl sb) (PCM.perp_comm hd)
    rw [PCM.ovee_comm hd] at e
    rw [← e]
    exact hle'

variable {J K : Type}

/-- Reindexing a finite partial sum along an injection. -/
theorem toList_map_perm {J' : Type} (ψ : J' ↪ J) (F : Finset J') :
    (F.map ψ).toList.Perm (F.toList.map ψ) := by
  rw [← Multiset.coe_eq_coe, Finset.coe_toList, ← Multiset.map_coe, Finset.coe_toList,
    Finset.map_val]

theorem finSum_comp_iff {J' : Type} (x : J → E) (ψ : J' ↪ J) (F : Finset J') (s : E) :
    FinSum (fun j => x (ψ j)) F s ↔ FinSum x (F.map ψ) s := by
  unfold FinSum
  have e : (F.toList.map fun j => x (ψ j)) = (F.toList.map ψ).map x := by
    rw [List.map_map]; rfl
  have hp : ((F.map ψ).toList.map x).Perm (F.toList.map fun j => x (ψ j)) := by
    rw [e]; exact (toList_map_perm ψ F).map x
  exact ⟨fun h => PCM.isSumOf_perm hp.symm h, fun h => PCM.isSumOf_perm hp h⟩

theorem CSummable.comp {J' : Type} {x : J → E} (hx : CSummable x) (ψ : J' ↪ J) :
    CSummable (fun j => x (ψ j)) := fun F => by
  obtain ⟨s, hs⟩ := hx (F.map ψ)
  exact ⟨s, (finSum_comp_iff x ψ F s).2 hs⟩

/-- A finite partial sum lies below the canonical sum. -/
theorem IsCSum.finSum_le {x : J → E} {s : E} (hs : IsCSum x s) {F : Finset J} {t : E}
    (ht : FinSum x F t) : t ≼ s := hs.2.1 t ⟨F, ht⟩

/-- The canonical sum of a subfamily lies below the canonical sum. -/
theorem IsCSum.le_of_comp {J' : Type} {x : J → E} {s : E} (hs : IsCSum x s) (ψ : J' ↪ J)
    {w : E} (hw : IsCSum (fun j => x (ψ j)) w) : w ≼ s :=
  hw.2.2 s (by
    rintro t ⟨F, hF⟩
    exact hs.finSum_le ((finSum_comp_iff x ψ F t).1 hF))

theorem isCSum_comp_equiv (e : J ≃ K) (x : K → E) (s : E) :
    IsCSum (fun j => x (e j)) s ↔ IsCSum x s := by
  have key : ∀ {J K : Type} (e : J ≃ K) (x : K → E) (s : E),
      IsCSum x s → IsCSum (fun j => x (e j)) s := by
    intro J K e x s hs
    refine ⟨hs.1.comp e.toEmbedding, fun t ht => ?_, fun c hc => hs.2.2 c ?_⟩
    · obtain ⟨F, hF⟩ := ht
      exact hs.finSum_le ((finSum_comp_iff x e.toEmbedding F t).1 hF)
    · rintro t ⟨F, hF⟩
      refine hc t ⟨F.map e.symm.toEmbedding, (finSum_comp_iff x e.toEmbedding _ t).2 ?_⟩
      rwa [Finset.map_map, show e.symm.toEmbedding.trans e.toEmbedding =
        Function.Embedding.refl K from by ext; simp, Finset.map_refl]
  refine ⟨fun h => ?_, key e x s⟩
  have := key e.symm (fun j => x (e j)) s h
  simpa using this

theorem isCSum_of_isEmpty [IsEmpty J] (x : J → E) : IsCSum x 0 := by
  have hF : ∀ F : Finset J, F = ∅ := Finset.eq_empty_of_isEmpty
  refine ⟨fun F => ⟨0, by rw [hF F]; exact finSum_empty x⟩, ?_, fun c _ => pcm_zero_le c⟩
  rintro t ⟨F, hF'⟩
  rw [hF F] at hF'
  rw [finSum_unique hF' (finSum_empty x)]
  exact pcm_preorder_refl _

theorem finSum_singleton (x : J → E) (j : J) : FinSum x {j} (x j) := by
  unfold FinSum; rw [Finset.toList_singleton]; exact isSumOf_singleton (x j)

theorem isCSum_of_unique [Unique J] (x : J → E) : IsCSum x (x default) := by
  have hF : ∀ F : Finset J, F = ∅ ∨ F = {default} := fun F =>
    Finset.subset_singleton_iff.1 (fun j _ => by rw [Unique.eq_default j]; simp)
  have hfin : ∀ F : Finset J, ∃ t, FinSum x F t ∧ t ≼ x default := by
    intro F
    rcases hF F with rfl | rfl
    · exact ⟨0, finSum_empty x, pcm_zero_le _⟩
    · exact ⟨x default, finSum_singleton x _, pcm_preorder_refl _⟩
  refine ⟨fun F => (hfin F).imp fun _ h => h.1, ?_, fun c hc => hc _ ⟨{default},
    finSum_singleton x _⟩⟩
  rintro t ⟨F, hF'⟩
  obtain ⟨t', ht', hle⟩ := hfin F
  rw [finSum_unique hF' ht']; exact hle

/-- The finite subsets `G.disjSum H` of `J ⊕ J'`. -/
theorem toList_disjSum_perm {J' : Type} (G : Finset J) (H : Finset J') :
    (G.disjSum H).toList.Perm (G.toList.map Sum.inl ++ H.toList.map Sum.inr) := by
  rw [← Multiset.coe_eq_coe, Finset.coe_toList, ← Multiset.coe_add, ← Multiset.map_coe,
    ← Multiset.map_coe, Finset.coe_toList, Finset.coe_toList]
  rfl

theorem finSum_disjSum_iff {J' : Type} (y : J → E) (z : J' → E) (G : Finset J)
    (H : Finset J') (s : E) :
    FinSum (Sum.elim y z) (G.disjSum H) s ↔
      ∃ u v, FinSum y G u ∧ FinSum z H v ∧ ∃ h : Perp u v, ovee u v h = s := by
  unfold FinSum
  have hp : ((G.disjSum H).toList.map (Sum.elim y z)).Perm (G.toList.map y ++ H.toList.map z) := by
    have := (toList_disjSum_perm G H).map (Sum.elim y z)
    simpa [List.map_append, List.map_map] using this
  constructor
  · intro h
    obtain ⟨u, v, hu, hv, huv, e⟩ := isSumOf_split (PCM.isSumOf_perm hp h)
    exact ⟨u, v, hu, hv, huv, e⟩
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    exact PCM.isSumOf_perm hp.symm (isSumOf_append hu hv huv)

/-- Canonical sums over a disjoint union `J ⊕ J'` (partition-associativity
for a two-block partition). -/
theorem isCSum_sum_elim_iff (hE : OmegaComplete E) [Countable J] {J' : Type} [Countable J']
    (y : J → E) (z : J' → E) (s : E) :
    IsCSum (Sum.elim y z) s ↔
      ∃ u v, IsCSum y u ∧ IsCSum z v ∧ ∃ h : Perp u v, ovee u v h = s := by
  classical
  obtain ⟨G, hG, hGc⟩ := exists_chain J
  obtain ⟨H, hH, hHc⟩ := exists_chain J'
  have hKc : ∀ F : Finset (J ⊕ J'), ∃ n, F ⊆ (G n).disjSum (H n) := by
    intro F
    obtain ⟨n₁, h₁⟩ := hGc (F.preimage Sum.inl Sum.inl_injective.injOn)
    obtain ⟨n₂, h₂⟩ := hHc (F.preimage Sum.inr Sum.inr_injective.injOn)
    refine ⟨max n₁ n₂, fun j hj => ?_⟩
    rcases j with j | j
    · exact Finset.inl_mem_disjSum.2 (hG (le_max_left n₁ n₂)
        (h₁ (Finset.mem_preimage.2 hj)))
    · exact Finset.inr_mem_disjSum.2 (hH (le_max_right n₁ n₂)
        (h₂ (Finset.mem_preimage.2 hj)))
  -- partial sums along the chains
  have chainSums : ∀ {L : Type} {w : L → E} {C : ℕ → Finset L}, Monotone C →
      (∀ F, ∃ n, F ⊆ C n) → CSummable w →
      ∃ t : ℕ → E, (∀ n, FinSum w (C n) (t n)) ∧ ∀ n, t n ≼ t (n + 1) := by
    intro L w C hC _ hw
    choose t ht using fun n => hw (C n)
    refine ⟨t, ht, fun n => ?_⟩
    obtain ⟨s', hs', hle⟩ := finSum_mono (hC (Nat.le_succ n)) (ht (n + 1))
    rwa [finSum_unique (ht n) hs']
  constructor
  · intro hs
    have hy : CSummable y := hs.1.comp ⟨Sum.inl, Sum.inl_injective⟩
    have hz : CSummable z := hs.1.comp ⟨Sum.inr, Sum.inr_injective⟩
    obtain ⟨u, hu⟩ := exists_isCSum hE hy
    obtain ⟨v, hv⟩ := exists_isCSum hE hz
    obtain ⟨t, ht, htm⟩ := chainSums hG hGc hy
    obtain ⟨r, hr, hrm⟩ := chainSums hH hHc hz
    have hq : ∀ n, ∃ q, FinSum (Sum.elim y z) ((G n).disjSum (H n)) q := fun n => hs.1 _
    choose q hq using hq
    have hsplit : ∀ n, ∃ h : Perp (t n) (r n), ovee (t n) (r n) h = q n := by
      intro n
      obtain ⟨u', v', hu', hv', h, e⟩ := (finSum_disjSum_iff y z _ _ _).1 (hq n)
      rw [finSum_unique (ht n) hu', finSum_unique (hr n) hv']
      exact ⟨h, e⟩
    choose hp hpe using hsplit
    obtain ⟨huv, hsup⟩ := isSupOf_ovee_chain htm hrm
      ((isCSum_iff_of_chain hy hGc ht u).1 hu) ((isCSum_iff_of_chain hz hHc hr v).1 hv) hp
    refine ⟨u, v, hu, hv, huv, ?_⟩
    have h1 := (isCSum_iff_of_chain hs.1 hKc hq s).1 hs
    have e : (fun n => ovee (t n) (r n) (hp n)) = q := funext hpe
    rw [e] at hsup
    exact hsup.unique h1
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    obtain ⟨t, ht, htm⟩ := chainSums hG hGc hu.1
    obtain ⟨r, hr, hrm⟩ := chainSums hH hHc hv.1
    have hp : ∀ n, Perp (t n) (r n) := fun n =>
      (ovee_le_ovee (hu.finSum_le (ht n)) (hv.finSum_le (hr n)) huv).1
    obtain ⟨huv', hsup⟩ := isSupOf_ovee_chain htm hrm
      ((isCSum_iff_of_chain hu.1 hGc ht u).1 hu) ((isCSum_iff_of_chain hv.1 hHc hr v).1 hv) hp
    have hq : ∀ n, FinSum (Sum.elim y z) ((G n).disjSum (H n)) (ovee (t n) (r n) (hp n)) :=
      fun n => (finSum_disjSum_iff y z _ _ _).2 ⟨_, _, ht n, hr n, hp n, rfl⟩
    have hK : CSummable (Sum.elim y z) := CSummable.of_chain hKc fun n => ⟨_, hq n⟩
    exact (isCSum_iff_of_chain hK hKc hq _).2 hsup

/-- Splitting a canonical sum along a predicate. -/
theorem isCSum_split_iff (hE : OmegaComplete E) [Countable J] (x : J → E) (P : J → Prop)
    (s : E) :
    IsCSum x s ↔ ∃ u v, IsCSum (fun j : {j // P j} => x j.1) u ∧
      IsCSum (fun j : {j // ¬ P j} => x j.1) v ∧ ∃ h : Perp u v, ovee u v h = s := by
  classical
  rw [← isCSum_sum_elim_iff hE, ← isCSum_comp_equiv (Equiv.sumCompl P).symm]
  refine iff_of_eq (congrArg (IsCSum · s) (funext fun j => ?_))
  by_cases h : P j <;> simp [Equiv.sumCompl, h]

/-- Partition-associativity over a finite set of blocks. -/
theorem isCSum_finite_blocks (hE : OmegaComplete E) [Countable J] (x : J → E) (p : J → K)
    (t : K → E) (ht : ∀ k, IsCSum (fun j : {j // p j = k} => x j.1) (t k)) (F : Finset K)
    (w : E) : FinSum t F w ↔ IsCSum (fun j : {j // p j ∈ F} => x j.1) w := by
  classical
  induction F using Finset.induction_on generalizing w with
  | empty =>
    have : IsEmpty {j // p j ∈ (∅ : Finset K)} := ⟨fun j => by simpa using j.2⟩
    constructor
    · intro h; rw [finSum_unique h (finSum_empty t)]; exact isCSum_of_isEmpty _
    · intro h; rw [h.unique (isCSum_of_isEmpty _)]; exact finSum_empty t
  | insert k F hk ih =>
    rw [finSum_insert t hk, PCM.isSumOf_cons_iff,
      isCSum_split_iff hE _ (fun j : {j // p j ∈ insert k F} => p j.1 = k)]
    -- identify the two blocks
    let e₁ : {j : {j // p j ∈ insert k F} // p j.1 = k} ≃ {j // p j = k} :=
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun j => p j ∈ insert k F)
        (fun j => p j = k)).trans (Equiv.subtypeEquivRight fun j => by
          constructor
          · exact fun h => h.2
          · intro h; exact ⟨by simp [h], h⟩)
    let e₂ : {j : {j // p j ∈ insert k F} // ¬ p j.1 = k} ≃ {j // p j ∈ F} :=
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun j => p j ∈ insert k F)
        (fun j => ¬ p j = k)).trans (Equiv.subtypeEquivRight fun j => by
          constructor
          · rintro ⟨h1, h2⟩
            rcases Finset.mem_insert.1 h1 with h | h
            · exact absurd h h2
            · exact h
          · intro h
            refine ⟨Finset.mem_insert_of_mem h, fun h' => hk (h' ▸ h)⟩)
    have h₁ : ∀ u, IsCSum (fun j : {j : {j // p j ∈ insert k F} // p j.1 = k} => x j.1.1) u ↔
        IsCSum (fun j : {j // p j = k} => x j.1) u := fun u =>
      isCSum_comp_equiv e₁ (fun j : {j // p j = k} => x j.1) u
    have h₂ : ∀ v, IsCSum (fun j : {j : {j // p j ∈ insert k F} // ¬ p j.1 = k} => x j.1.1) v ↔
        IsCSum (fun j : {j // p j ∈ F} => x j.1) v := fun v =>
      isCSum_comp_equiv e₂ (fun j : {j // p j ∈ F} => x j.1) v
    constructor
    · rintro ⟨v, hv, h, rfl⟩
      exact ⟨t k, v, (h₁ _).2 (ht k), (h₂ _).2 ((ih v).1 hv), h, rfl⟩
    · rintro ⟨u, v, hu, hv, h, rfl⟩
      have hku : t k = u := (ht k).unique ((h₁ u).1 hu)
      subst hku
      exact ⟨v, (ih v).2 ((h₂ v).1 hv), h, rfl⟩

/-- **Partition-associativity of canonical sums.** -/
theorem isCSum_partition_iff (hE : OmegaComplete E) [Countable J] [Countable K] (x : J → E)
    (p : J → K) (s : E) :
    IsCSum x s ↔ ∃ t : K → E,
      (∀ k, IsCSum (fun j : {j // p j = k} => x j.1) (t k)) ∧ IsCSum t s := by
  classical
  have hsub : ∀ (P : J → Prop), CSummable x → CSummable (fun j : {j // P j} => x j.1) :=
    fun P hx => hx.comp ⟨Subtype.val, Subtype.val_injective⟩
  constructor
  · intro hs
    choose t ht using fun k => exists_isCSum hE (hsub (fun j => p j = k) hs.1)
    refine ⟨t, ht, ?_⟩
    -- the finite partial sums of `t` are the canonical sums over `p⁻¹ F`
    have hw : ∀ F : Finset K, ∃ w, FinSum t F w ∧ w ≼ s := by
      intro F
      obtain ⟨w, hw⟩ := exists_isCSum hE (hsub (fun j => p j ∈ F) hs.1)
      exact ⟨w, (isCSum_finite_blocks hE x p t ht F w).2 hw,
        hs.le_of_comp ⟨Subtype.val, Subtype.val_injective⟩ hw⟩
    refine ⟨fun F => (hw F).imp fun _ h => h.1, ?_, fun c hc => hs.2.2 c ?_⟩
    · rintro w ⟨F, hF⟩
      obtain ⟨w', hw', hle⟩ := hw F
      rw [finSum_unique hF hw']; exact hle
    · -- a finite partial sum of `x` lies below one of `t`
      rintro a ⟨G, hG⟩
      obtain ⟨w, hw', -⟩ := hw (G.image p)
      have hcs := (isCSum_finite_blocks hE x p t ht _ w).1 hw'
      refine pcm_preorder_trans ?_ (hc w ⟨_, hw'⟩)
      let G' : Finset {j // p j ∈ G.image p} := G.subtype (fun j => p j ∈ G.image p)
      have hG' : G'.map (Function.Embedding.subtype _) = G := by
        rw [Finset.subtype_map, Finset.filter_true_of_mem]
        intro j hj; exact Finset.mem_image_of_mem p hj
      obtain ⟨a', ha'⟩ := hcs.1 G'
      have : FinSum x G a' := by
        have h1 := (finSum_comp_iff x (Function.Embedding.subtype _) G' a').1 ha'
        rwa [hG'] at h1
      rw [finSum_unique hG this]
      exact hcs.finSum_le ha'
  · rintro ⟨t, ht, hts⟩
    -- every finite partial sum of `x` lies below a finite partial sum of `t`
    have hbound : ∀ G : Finset J, ∃ a, FinSum x G a ∧ a ≼ s := by
      intro G
      obtain ⟨w, hw⟩ := hts.1 (G.image p)
      have hcs := (isCSum_finite_blocks hE x p t ht _ w).1 hw
      let G' : Finset {j // p j ∈ G.image p} := G.subtype (fun j => p j ∈ G.image p)
      have hG' : G'.map (Function.Embedding.subtype _) = G := by
        rw [Finset.subtype_map, Finset.filter_true_of_mem]
        intro j hj; exact Finset.mem_image_of_mem p hj
      obtain ⟨a', ha'⟩ := hcs.1 G'
      have : FinSum x G a' := by
        have h1 := (finSum_comp_iff x (Function.Embedding.subtype _) G' a').1 ha'
        rwa [hG'] at h1
      exact ⟨a', this, pcm_preorder_trans (hcs.finSum_le ha') (hts.finSum_le hw)⟩
    refine ⟨fun G => (hbound G).imp fun _ h => h.1, ?_, fun c hc => hts.2.2 c ?_⟩
    · rintro a ⟨G, hG⟩
      obtain ⟨a', ha', hle⟩ := hbound G
      rw [finSum_unique hG ha']; exact hle
    · rintro w ⟨F, hF⟩
      have hcs := (isCSum_finite_blocks hE x p t ht F w).1 hF
      refine hcs.2.2 c ?_
      rintro a ⟨G, hG⟩
      exact hc a ⟨_, (finSum_comp_iff x ⟨Subtype.val, Subtype.val_injective⟩ G a).1 hG⟩

theorem finSum_univ_iff {J : Type} (x : J → E) (F : Finset J) (s : E) :
    FinSum (fun j : F => x j.1) Finset.univ s ↔ FinSum x F s := by
  have h := finSum_comp_iff x (Function.Embedding.subtype (· ∈ F)) Finset.univ s
  have e : (Finset.univ : Finset F).map (Function.Embedding.subtype (· ∈ F)) = F := by
    ext j
    constructor
    · intro hj; obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hj; exact a.2
    · intro hj; exact Finset.mem_map.2 ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩
  rw [e] at h
  exact h

/-- A canonical sum over a finite index set is the finite sum over all of it. -/
theorem isCSum_of_finSum_univ {J : Type} [Fintype J] {x : J → E} {s : E}
    (hs : FinSum x Finset.univ s) : IsCSum x s := by
  refine ⟨fun F => ?_, fun t ⟨F, hF⟩ => ?_, fun c hc => hc s ⟨_, hs⟩⟩
  · obtain ⟨t, ht, -⟩ := finSum_mono (Finset.subset_univ F) hs; exact ⟨t, ht⟩
  · obtain ⟨t', ht', hle⟩ := finSum_mono (Finset.subset_univ F) hs
    rw [finSum_unique hF ht']; exact hle

/-- A canonical sum of two elements is their binary sum. -/
theorem isCSum_pair_iff (a b s : E) : IsCSum ![a, b] s ↔ ∃ h : Perp a b, ovee a b h = s := by
  have huniv : ∀ s, FinSum ![a, b] Finset.univ s ↔ ∃ h : Perp a b, ovee a b h = s := by
    intro s
    unfold FinSum
    have hp : ((Finset.univ : Finset (Fin 2)).toList.map ![a, b]).Perm [a, b] := by
      rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    rw [show (PCM.IsSumOf ((Finset.univ : Finset (Fin 2)).toList.map ![a, b]) s ↔
      PCM.IsSumOf [a, b] s) from ⟨PCM.isSumOf_perm hp, PCM.isSumOf_perm hp.symm⟩]
    constructor
    · intro h
      obtain ⟨t, ht, hp', e⟩ := PCM.isSumOf_cons_iff.1 h
      obtain ⟨t', ht', hp'', e'⟩ := PCM.isSumOf_cons_iff.1 ht
      rw [PCM.isSumOf_nil_iff] at ht'
      subst ht'
      rw [PCM.ovee_zero] at e'
      subst e'
      exact ⟨hp', e⟩
    · rintro ⟨h, rfl⟩; exact isSumOf_pair a b h
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := hs.1 Finset.univ
    rw [hs.unique (isCSum_of_finSum_univ ht)]
    exact (huniv t).1 ht
  · intro h
    exact isCSum_of_finSum_univ ((huniv s).2 h)

/-- **SIG 17** (main.tex:625, text after the Definition): the canonical
countable sums make a σ-effect algebra a σ-PAM. -/
noncomputable def canonicalSigmaPAM (hE : OmegaComplete E) : SigmaPAM E where
  Summable x := CSummable x
  sum x h := (exists_isCSum hE h).choose
  nonempty := ⟨0⟩
  summable_iff_partition x p := by
    constructor
    · intro hx
      obtain ⟨t, ht, hts⟩ := (isCSum_partition_iff hE x p _).1 (exists_isCSum hE hx).choose_spec
      refine ⟨fun k => (ht k).1, ?_⟩
      have : (fun k => (exists_isCSum hE (ht k).1).choose) = t :=
        funext fun k => (exists_isCSum hE (ht k).1).choose_spec.unique (ht k)
      show CSummable _
      rw [this]; exact hts.1
    · rintro ⟨h, h'⟩
      exact ((isCSum_partition_iff hE x p _).2 ⟨_, fun k => (exists_isCSum hE (h k)).choose_spec,
        (exists_isCSum hE h').choose_spec⟩).1
  sum_partition x p hx h h' := by
    obtain ⟨t, ht, hts⟩ := (isCSum_partition_iff hE x p _).1 (exists_isCSum hE hx).choose_spec
    have e : (fun k => (exists_isCSum hE (h k)).choose) = t :=
      funext fun k => (exists_isCSum hE (h k)).choose_spec.unique (ht k)
    have key : ∀ w, IsCSum (fun k => (exists_isCSum hE (h k)).choose) w → IsCSum x w := by
      intro w hw
      rw [e] at hw
      exact (isCSum_partition_iff hE x p w).2 ⟨t, ht, hw⟩
    exact (exists_isCSum hE hx).choose_spec.unique (key _ (exists_isCSum hE h').choose_spec)
  summable_unique x := (isCSum_of_unique x).1
  sum_unique x h := (exists_isCSum hE h).choose_spec.unique (isCSum_of_unique x)
  limit x h := fun F => by
    obtain ⟨s, hs⟩ := h F Finset.univ
    exact ⟨s, (finSum_univ_iff x F s).1 hs⟩

theorem canonical_sumsTo_iff (hE : OmegaComplete E) {J : Type} [Countable J] (x : J → E)
    (s : E) : @SumsTo E (canonicalSigmaPAM hE) J _ x s ↔ IsCSum x s := by
  constructor
  · rintro ⟨h, rfl⟩; exact (exists_isCSum hE h).choose_spec
  · intro h; exact ⟨h.1, (exists_isCSum hE h.1).choose_spec.unique h⟩

/-- **SIG 17** (main.tex:625): the canonical σ-PAM extends the PCM of
`E`. -/
theorem canonicalSigmaPAM_extends (hE : OmegaComplete E) :
    @SigmaPAMExtends E _ (canonicalSigmaPAM hE) := by
  intro a b s
  rw [canonical_sumsTo_iff]
  exact (isCSum_pair_iff a b s).symm

end Canonical

/-! ### SIG 18: an effect algebra with a σ-PAM structure -/

section Prop18

variable {E : Type u} [EffectAlgebra E] [SigmaPAM E]

variable (hS : SigmaPAMExtends E)
include hS

theorem zero_eq_of_extends : (SigmaPAM.zero : E) = 0 := by
  obtain ⟨h, e⟩ := (hS _ _ _).2 (sumsTo_zero_pair (0 : E))
  have h0 : Perp (0 : E) 0 := PCM.zero_perp 0
  refine eabasics_cancellation h h0 ?_
  rw [e, PCM.zero_ovee]

theorem isSumOf_toPCM_iff (l : List E) (s : E) :
    @PCM.IsSumOf E toPCM l s ↔ PCM.IsSumOf l s := by
  induction l generalizing s with
  | nil =>
    rw [@PCM.isSumOf_nil_iff E toPCM, PCM.isSumOf_nil_iff, toPCM_zero, zero_eq_of_extends hS]
  | cons a l ih =>
    rw [@PCM.isSumOf_cons_iff E toPCM, PCM.isSumOf_cons_iff]
    refine exists_congr fun t => ?_
    constructor
    · rintro ⟨ht, hp, e⟩
      obtain ⟨hp', e'⟩ := (hS a t s).2 ⟨hp, e⟩
      exact ⟨(ih t).1 ht, hp', e'⟩
    · rintro ⟨ht, hp, e⟩
      obtain ⟨hp', e'⟩ := (hS a t s).1 ⟨hp, e⟩
      exact ⟨(ih t).2 ht, hp', e'⟩

theorem finSum_iff_sumsTo {J : Type} (x : J → E) (F : Finset J) (s : E) :
    FinSum x F s ↔ SumsTo (fun j : F => x j.1) s := by
  rw [sumsTo_finset_iff, isSumOf_toPCM_iff hS]; rfl

theorem perp_of_sumsTo {a b s : E} (h : SumsTo ![a, b] s) : ∃ hp : Perp a b, ovee a b hp = s :=
  (hS a b s).2 h

/-- Direction `σ-sum ⇒ canonical sum` of SIG 18, for any countable family. -/
theorem isCSum_of_sumsTo {J : Type} [Countable J] {x : J → E} {s : E} (h : SumsTo x s) :
    IsCSum x s := by
  classical
  have hsub : ∀ F : Finset J, ∃ t, FinSum x F t := fun F =>
    ⟨_, (finSum_iff_sumsTo hS x F _).2 (sumsTo_sum (summable_subfamily h.summable (· ∈ F)))⟩
  refine ⟨hsub, ?_, ?_⟩
  · -- `s = (⊕_F x) ⊕ (⋁_{J∖F} x)`, so each finite partial sum is below `s`
    rintro t ⟨F, hF⟩
    obtain ⟨u, v, hu, hv, huv⟩ := (sumsTo_split x (· ∈ F) s).1 h
    rw [(finSum_iff_sumsTo hS x F t).1 hF |>.unique hu]
    obtain ⟨hp, e⟩ := perp_of_sumsTo hS huv
    exact ⟨v, hp, e⟩
  · -- an upper bound `c` of the finite partial sums: `c^⊥, x_0, x_1, …` is
    -- summable (limit axiom), hence `s ⊥ c^⊥`, i.e. `s ≤ c`
    intro c hc
    have hy : Summable (Sum.elim x (fun _ : Unit => orth c)) := by
      refine summable_sum_elim_of_finite x _ fun F => ?_
      obtain ⟨t, ht⟩ := hsub F
      have ht' := (finSum_iff_sumsTo hS x F t).1 ht
      have htc : Perp t (orth c) := by
        rw [eabasics_perp_iff_le_orth, eabasics_orth_orth]; exact hc t ⟨F, ht⟩
      exact ⟨t, ht', ((hS _ _ _).1 ⟨htc, rfl⟩).summable⟩
    obtain ⟨u, v, hu, hv, huv⟩ := (sumsTo_sum_iff _ _ _).1 (sumsTo_sum hy)
    have hv' : v = orth c := hv.unique (sumsTo_of_unique' (fun _ : Unit => orth c) ())
    rw [hu.unique h, hv'] at huv
    obtain ⟨hp, -⟩ := perp_of_sumsTo hS huv
    rw [← eabasics_orth_orth c, ← eabasics_perp_iff_le_orth]
    exact hp

/-- **SIG 18** (`prop:effect-algebra-PAM-iff-complete`, main.tex:631,
Proposition): let `E` be an effect algebra with a σ-PAM structure extending
its PCM structure.  Then `E` is ω-complete, hence a σ-effect algebra, and the
σ-PAM structure coincides with the canonical one: a countable family sums to
`s` in the given σ-PAM iff `s` is its canonical sum. -/
theorem sigmaPAM_extends_omegaComplete :
    OmegaComplete E ∧ ∀ (J : Type) [Countable J] (x : J → E) (s : E), SumsTo x s ↔ IsCSum x s := by
  have hcoinc : ∀ (J : Type) [Countable J] (x : J → E) (s : E), SumsTo x s ↔ IsCSum x s := by
    intro J _ x s
    refine ⟨isCSum_of_sumsTo hS, fun h => ?_⟩
    have hx : Summable x := limit x fun F => by
      obtain ⟨t, ht⟩ := h.1 F
      exact ((finSum_iff_sumsTo hS x F t).1 ht).summable
    rw [h.unique (isCSum_of_sumsTo hS (sumsTo_sum hx))]
    exact sumsTo_sum hx
  refine ⟨fun a ha => ?_, hcoinc⟩
  -- the differences `b_n` are summable (limit axiom) and their sum is `⋁ a_n`
  have hb : Summable (diffSeq a ha) := limit _ fun F => by
    obtain ⟨n, hn⟩ := cofinal_range F
    obtain ⟨t, ht, -⟩ := finSum_mono hn (finSum_diffSeq a ha n)
    exact ((finSum_iff_sumsTo hS _ F t).1 ht).summable
  exact ⟨_, (isCSum_diffSeq_iff a ha _).1 ((hcoinc ℕ _ _).1 (sumsTo_sum hb))⟩

end Prop18

/-- **SIG 19** (main.tex:641, Corollary): for any object `A` of a σ-effectus,
`Pred A = C(A, I)` is a σ-effect algebra (and its σ-PAM sums are the
canonical ones). -/
theorem pred_sigmaEffectAlgebra {C : Type u} [Category.{v} C] [HasCountableCoproducts C]
    [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C] (A : C) :
    IsSigmaEffectAlgebra (A ⟶ effObj C) ∧
      ∀ (J : Type) [Countable J] (x : J → (A ⟶ effObj C)) (s : A ⟶ effObj C),
        SumsTo x s ↔ IsCSum x s :=
  sigmaPAM_extends_omegaComplete (fun _ _ _ => Iff.rfl)

section Lemma20

variable {E : Type u} {D : Type v} [EffectAlgebra E] [EffectAlgebra D]

/-- σ-additivity for the canonical sums of σ-effect algebras: a summable
family is sent to a summable family, and `f (⋁ x_j) = ⋁ f x_j`. -/
def IsSigmaAdditiveC (f : E → D) : Prop :=
  ∀ (J : Type) [Countable J] (x : J → E) (s : E), IsCSum x s → IsCSum (fun j => f (x j)) (f s)

theorem IsSigmaAdditiveC.congr {f g : E → D} (h : ∀ a, f a = g a) (hf : IsSigmaAdditiveC f) :
    IsSigmaAdditiveC g := by
  intro J _ x s hs
  have := hf J x s hs
  simp only [h] at this
  exact this

/-- **ω-continuity**: `f` preserves suprema of increasing sequences. -/
def IsOmegaContinuous (f : E → D) : Prop :=
  ∀ a : ℕ → E, (∀ n, a n ≼ a (n + 1)) → ∀ s, IsSupOf (Set.range a) s →
    IsSupOf (Set.range fun n => f (a n)) (f s)

/-- **SIG 20** (`lem:sigma-additive-equiv-omega-conti`, main.tex:651,
Lemma): an additive map `f : E → D` of σ-effect algebras is σ-additive iff
it is ω-continuous.  (Printed without proof, "straightforwardly verifiable";
ω-completeness is not needed, so it is not assumed.) -/
theorem sigmaAdditive_iff_omegaContinuous {f : E → D} (hf : IsAdditive f) :
    IsSigmaAdditiveC f ↔ IsOmegaContinuous f := by
  constructor
  · intro h a ha s hs
    have h1 := h ℕ (diffSeq a ha) s ((isCSum_diffSeq_iff a ha s).2 hs)
    have hfin : ∀ n, FinSum (fun j => f (diffSeq a ha j)) (Finset.range (n + 1)) (f (a n)) :=
      fun n => hf.finSum (finSum_diffSeq a ha n)
    exact (isCSum_iff_of_chain h1.1 cofinal_range hfin (f s)).1 h1
  · intro h J _ x s hs
    obtain ⟨G, hG, hcof⟩ := exists_chain J
    choose t ht using fun n => hs.1 (G n)
    have hmono : ∀ n, t n ≼ t (n + 1) := by
      intro n
      obtain ⟨s', hs', hle⟩ := finSum_mono (hG (Nat.le_succ n)) (ht (n + 1))
      rwa [finSum_unique (ht n) hs']
    have h1 := h t hmono s ((isCSum_iff_of_chain hs.1 hcof ht s).1 hs)
    have hfx : CSummable (fun j => f (x j)) := fun F => by
      obtain ⟨u, hu⟩ := hs.1 F
      exact ⟨_, hf.finSum hu⟩
    exact (isCSum_iff_of_chain hfx hcof (fun n => hf.finSum (ht n)) (f s)).2 h1

end Lemma20

/-! ## SIG 21–23: effect monoids and σ-effect monoids -/

section EffectMonoids

/-- **SIG 21** (`def:effectmonoid`, main.tex:669, Definition): an **effect
monoid** is an effect algebra with an associative, unital, *biadditive*
multiplication.  The tree's `EffectMonoid` (178II) asks instead for the
four-term distributivity `(a ⊕ b)(c ⊕ d) = ac ⊕ bc ⊕ ad ⊕ bd`; given unit
and associativity the two are equivalent. -/
theorem effectMonoid_distrib_iff_biadditive {M : Type u} [EffectAlgebra M] [Mul M]
    (one_mul : ∀ a : M, 1 * a = a) (mul_one : ∀ a : M, a * 1 = a)
    (mul_assoc : ∀ a b c : M, a * b * c = a * (b * c)) :
    (∀ {a b c d : M} (hab : Perp a b) (hcd : Perp c d),
        PCM.IsSumOf [a * c, b * c, a * d, b * d] (ovee a b hab * ovee c d hcd)) ↔
      IsBiadditive (fun a b : M => a * b) := by
  constructor
  · intro hd
    let _ : EffectMonoid M :=
      { ‹EffectAlgebra M›, ‹Mul M› with
        one_mul := one_mul, mul_one := mul_one, mul_assoc := mul_assoc, distrib := hd }
    refine ⟨fun a => ⟨(exc_emonzero a).1, fun h => ?_⟩, fun b => ⟨(exc_emonzero b).2, fun h => ?_⟩⟩
    · obtain ⟨h', e⟩ := emon_mul_ovee a h
      exact ⟨h', e.symm⟩
    · obtain ⟨h', e⟩ := emon_ovee_mul b h
      exact ⟨h', e.symm⟩
  · rintro ⟨hl, hr⟩ a b c d hab hcd
    obtain ⟨h1, e1⟩ := (hl (ovee a b hab)).2 hcd
    obtain ⟨h2, e2⟩ := (hr c).2 hab
    obtain ⟨h3, e3⟩ := (hr d).2 hab
    have hp : Perp (ovee (a * c) (b * c) h2) (ovee (a * d) (b * d) h3) := by
      rw [e2, e3]; exact h1
    have key : ovee a b hab * ovee c d hcd
        = ovee (ovee (a * c) (b * c) h2) (ovee (a * d) (b * d) h3) hp :=
      e1.symm.trans (PCM.ovee_congr e2.symm e3.symm h1 hp)
    rw [key]
    exact isSumOf_append (isSumOf_pair _ _ h2) (isSumOf_pair _ _ h3) hp

/-- **SIG 21** (`def:effectmonoid`, main.tex:669, Definition): a
**σ-effect monoid** is an effect monoid whose effect algebra is a σ-effect
algebra and whose multiplication is σ-biadditive (for the canonical sums). -/
def IsSigmaEffectMonoid (M : Type u) [EffectMonoid M] : Prop :=
  OmegaComplete M ∧ (∀ a : M, IsSigmaAdditiveC (fun b => a * b)) ∧
    ∀ b : M, IsSigmaAdditiveC (fun a => a * b)

/-- **SIG 21** (`def:effectmonoid`, main.tex:689, Definition): the
**opposite** effect monoid `Mᵒᵖ`: the same effect algebra with
`a ·' b = b · a`. -/
def opEffectMonoid (M : Type u) [EffectMonoid M] : EffectMonoid M :=
  { (inferInstance : EffectAlgebra M) with
    mul := fun a b => b * a
    one_mul := fun a => EffectMonoid.mul_one a
    mul_one := fun a => EffectMonoid.one_mul a
    mul_assoc := fun a b c => (EffectMonoid.mul_assoc c b a).symm
    distrib := fun {a b c d} hab hcd => by
      have := EffectMonoid.distrib hcd hab
      refine PCM.isSumOf_perm ?_ this
      exact List.Perm.cons _ (List.Perm.swap _ _ _) }

theorem effectMonoid_ext {M : Type u} {a b : EffectMonoid M}
    (h1 : a.toEffectAlgebra = b.toEffectAlgebra) (h2 : a.toMul = b.toMul) : a = b := by
  cases a; cases b; cases h1; cases h2; rfl

/-- **SIG 21** (`def:effectmonoid`, main.tex:692): `M` is commutative iff
`M = Mᵒᵖ`. -/
theorem commutative_iff_eq_op (M : Type u) [inst : EffectMonoid M] :
    EffectMonoid.Commutative M ↔ opEffectMonoid M = inst := by
  constructor
  · intro hc
    refine effectMonoid_ext rfl ?_
    show (⟨fun a b => b * a⟩ : Mul M) = ⟨fun a b => a * b⟩
    congr 1
    funext a b
    exact hc b a
  · intro h a b
    exact (congrArg (fun m : EffectMonoid M => m.toMul.mul a b) h).symm

/-- The algebraic order of the Boolean effect algebra is the lattice
order. -/
theorem boolean_le_iff {L : Type u} [BooleanAlgebra L] (a b : L) :
    @PCM.le L (booleanEffectAlgebra L).toPCM a b ↔ a ≤ b := by
  let _ := booleanEffectAlgebra L
  constructor
  · rintro ⟨c, -, rfl⟩
    exact le_sup_left
  · intro h
    refine ⟨b ⊓ aᶜ, ?_, ?_⟩
    · show a ⊓ (b ⊓ aᶜ) = ⊥
      rw [inf_left_comm, inf_compl_eq_bot, inf_bot_eq]
    · show a ⊔ (b ⊓ aᶜ) = b
      rw [sup_inf_left, sup_compl_eq_top, inf_top_eq, sup_eq_right.2 h]

/-- **SIG 22** (`ex:booleanalgebra`, main.tex:710, Example): a Boolean
algebra is an effect monoid with `a · b = a ∧ b` (the tree's
`booleanEffectMonoid`, 178III.2), and an ω-complete Boolean algebra is a
σ-effect monoid. -/
theorem booleanAlgebra_isSigmaEffectMonoid (L : Type u) [BooleanAlgebra L]
    (hω : ∀ a : ℕ → L, Monotone a → ∃ s, IsLUB (Set.range a) s) :
    letI := booleanEffectMonoid L
    IsSigmaEffectMonoid L := by
  let _ := booleanEffectMonoid L
  have hle : ∀ a b : L, a ≼ b ↔ a ≤ b := boolean_le_iff
  have hsup : ∀ (S : Set L) (s : L), IsSupOf S s ↔ IsLUB S s := by
    intro S s
    simp only [IsSupOf, hle]
    rfl
  -- `a ∧ -` preserves suprema of increasing sequences
  have hcont : ∀ a : L, IsOmegaContinuous (fun b : L => a * b) := by
    intro a b _ s hs
    rw [hsup] at hs ⊢
    refine ⟨?_, fun c hc => ?_⟩
    · rintro _ ⟨n, rfl⟩
      exact inf_le_inf_left a (hs.1 ⟨n, rfl⟩)
    · have hb : ∀ n, b n ≤ c ⊔ aᶜ := by
        intro n
        have h1 : a ⊓ b n ≤ c := hc ⟨n, rfl⟩
        calc b n = (a ⊓ b n) ⊔ (aᶜ ⊓ b n) := by
                rw [← inf_sup_right, sup_compl_eq_top, top_inf_eq]
          _ ≤ c ⊔ aᶜ := sup_le_sup h1 inf_le_left
      have : s ≤ c ⊔ aᶜ := hs.2 (by rintro _ ⟨n, rfl⟩; exact hb n)
      calc a * s = a ⊓ s := rfl
        _ ≤ a ⊓ (c ⊔ aᶜ) := inf_le_inf_left a this
        _ = a ⊓ c := by rw [inf_sup_left, inf_compl_eq_bot, sup_bot_eq]
        _ ≤ c := inf_le_right
  have hadd : ∀ a : L, IsAdditive (fun b : L => a * b) := fun a =>
    ⟨(exc_emonzero a).1, fun h => by
      obtain ⟨h', e⟩ := emon_mul_ovee a h
      exact ⟨h', e.symm⟩⟩
  have hcomm : ∀ a b : L, a * b = b * a := fun a b => inf_comm a b
  refine ⟨fun a ha => ?_, fun a => (sigmaAdditive_iff_omegaContinuous (hadd a)).2 (hcont a),
    ?_⟩
  · obtain ⟨s, hs⟩ := hω a (monotone_nat_of_le_succ fun n => (hle _ _).1 (ha n))
    exact ⟨s, (hsup _ _).2 hs⟩
  · intro b
    exact ((sigmaAdditive_iff_omegaContinuous (hadd b)).2 (hcont b)).congr fun a => hcomm b a

/-- **SIG 22** (`ex:booleanalgebra`, main.tex:711, Example): `{0,1}` is a
σ-effect monoid. -/
theorem bool_isSigmaEffectMonoid : IsSigmaEffectMonoid Bool :=
  booleanAlgebra_isSigmaEffectMonoid Bool fun a _ => ⟨⨆ n, a n, isLUB_iSup⟩

/-- **SIG 23** (`ex:CX`, main.tex:718, Example): the real unit interval
`[0,1]`, with the usual product and partial addition (the tree's
`unitInterval.effectMonoid`, 178III.1), is a σ-effect monoid. -/
theorem unitInterval_isSigmaEffectMonoid : IsSigmaEffectMonoid unitInterval := by
  have hsup : ∀ (a : ℕ → unitInterval) (s : unitInterval),
      IsSupOf (Set.range a) s ↔ IsLUB (Set.range fun n => (a n : ℝ)) (s : ℝ) := by
    intro a s
    simp only [IsSupOf, unitInterval_le_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rintro _ ⟨n, rfl⟩; exact h1 _ ⟨n, rfl⟩, fun c hc => ?_⟩
      by_cases hc1 : c ≤ 1
      · have hc0 : 0 ≤ c := le_trans (a 0).2.1 (hc ⟨0, rfl⟩)
        exact h2 ⟨c, hc0, hc1⟩ (by rintro _ ⟨n, rfl⟩; exact hc ⟨n, rfl⟩)
      · exact le_trans s.2.2 (le_of_lt (not_le.1 hc1))
    · rintro ⟨h1, h2⟩
      exact ⟨by rintro _ ⟨n, rfl⟩; exact h1 ⟨n, rfl⟩,
        fun c hc => h2 (by rintro _ ⟨n, rfl⟩; exact hc _ ⟨n, rfl⟩)⟩
  have hbdd : ∀ a : ℕ → unitInterval, BddAbove (Set.range fun n => (a n : ℝ)) :=
    fun a => ⟨1, by rintro _ ⟨n, rfl⟩; exact (a n).2.2⟩
  have hcont : ∀ r : unitInterval, IsOmegaContinuous (fun b : unitInterval => r * b) := by
    intro r a _ s hs
    rw [hsup] at hs ⊢
    have hs' : (s : ℝ) = ⨆ n, (a n : ℝ) := hs.unique (isLUB_ciSup (hbdd a))
    have : ((r * s : unitInterval) : ℝ) = ⨆ n, ((r * a n : unitInterval) : ℝ) := by
      push_cast
      rw [hs', Real.mul_iSup_of_nonneg r.2.1]
    rw [this]
    exact isLUB_ciSup (hbdd fun n => r * a n)
  have hadd : ∀ r : unitInterval, IsAdditive (fun b : unitInterval => r * b) := fun r =>
    ⟨(exc_emonzero r).1, fun h => by
      obtain ⟨h', e⟩ := emon_mul_ovee r h
      exact ⟨h', e.symm⟩⟩
  refine ⟨fun a ha => ?_, fun r => (sigmaAdditive_iff_omegaContinuous (hadd r)).2 (hcont r),
    ?_⟩
  · have hmono : Monotone fun n => (a n : ℝ) :=
      monotone_nat_of_le_succ fun n => unitInterval_le_iff.1 (ha n)
    refine ⟨⟨⨆ n, (a n : ℝ), le_trans (a 0).2.1 (le_ciSup (hbdd a) 0),
      ciSup_le fun n => (a n).2.2⟩, (hsup _ _).2 (isLUB_ciSup (hbdd a))⟩
  · intro r
    exact ((sigmaAdditive_iff_omegaContinuous (hadd r)).2 (hcont r)).congr fun a => mul_comm r a

/-! **SIG 23** (`ex:CX`, main.tex:723): for a compact Hausdorff space `X`
the unit interval `[0,1]_{C(X)}` is an effect monoid with the pointwise
product: the tree's `continuousUnitIntervalEffectMonoid X` (195VI).  That it
is ω-complete iff `X` is basically disconnected (tree:
`BasicallyDisconnected`) is cited from Gillman–Jerison 1H, 3N.5 and not
formalised here; nor is "the scalars of `W*ᵒᵖ` are `[0,1]`", which needs the
σ-effectus `W*ᵒᵖ` of SIG 15. -/

end EffectMonoids

end Papers.SIG
