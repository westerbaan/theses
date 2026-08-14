/-
Theses/B/Eff/EffectAlgebras.lean

Statements of thesis B (Bas Westerbaan, *Dagger and Dilation in the Category
of Von Neumann Algebras*, arXiv:1803.01911), chapter "Diamond, andthen,
dagger" (`eff.tex`), lines 170–747: partial commutative monoids (PCMs),
effect algebras, orthomodular lattices, effect monoids and effect modules.

Conventions (see `CONVENTIONS.md`):

* The partial operation `ovee` of a PCM is modelled in the *Perp-relation
  style*: a relation `Perp : M → M → Prop` ("the sum is defined") together
  with a total operation `ovee : (a b : M) → Perp a b → M` on the graph of
  `Perp`.  This style is used consistently throughout `Theses.B.Eff`.
* `Definition` points are real definitions; `Lemma`/`Proposition`/`Exercise`
  points are theorems.  Example points that make substantive claims appear as
  instances/defs or as theorems.  Proofs still outstanding are marked `sorry`
  and listed, with the reason, in `PROVING-LOG.md`.
-/
import Theses.Common

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace Theses.B.Eff

universe u v w

/-! ## Partial commutative monoids (parsec 174) -/

/-- **174II** (`dfn-pcm`, eff.tex:185, Definition): a **partial commutative
monoid** (PCM) is a set `M` with a distinguished element `0` and a partial
binary operation `⋁` — modelled here by a definedness relation `Perp a b`
("`a ⊥ b`", the sum of `a` and `b` is defined) and a total operation
`ovee a b h` on its graph — such that

1. *(partial commutativity)* if `a ⊥ b` then `b ⊥ a` and `a ⋁ b = b ⋁ a`;
2. *(partial associativity)* if `a ⊥ b` and `(a ⋁ b) ⊥ c`, then `b ⊥ c`,
   `a ⊥ (b ⋁ c)` and `(a ⋁ b) ⋁ c = a ⋁ (b ⋁ c)`; and
3. *(zero)* `0 ⊥ a` and `0 ⋁ a = a`. -/
class PCM (M : Type u) extends Zero M where
  /-- `Perp a b` ("`a ⊥ b`"): the partial sum `a ⋁ b` is defined. -/
  Perp : M → M → Prop
  /-- The partial sum `a ⋁ b`, given that it is defined. -/
  ovee : (a b : M) → Perp a b → M
  perp_comm : ∀ {a b : M}, Perp a b → Perp b a
  ovee_comm : ∀ {a b : M} (h : Perp a b), ovee a b h = ovee b a (perp_comm h)
  perp_of_ovee_perp : ∀ {a b c : M} (hab : Perp a b), Perp (ovee a b hab) c → Perp b c
  perp_ovee_of_ovee_perp : ∀ {a b c : M} (hab : Perp a b) (h : Perp (ovee a b hab) c),
    Perp a (ovee b c (perp_of_ovee_perp hab h))
  ovee_assoc : ∀ {a b c : M} (hab : Perp a b) (h : Perp (ovee a b hab) c),
    ovee (ovee a b hab) c h
      = ovee a (ovee b c (perp_of_ovee_perp hab h)) (perp_ovee_of_ovee_perp hab h)
  zero_perp : ∀ a : M, Perp 0 a
  zero_ovee : ∀ a : M, ovee 0 a (zero_perp a) = a

export PCM (Perp ovee)

/-- **174II** (`dfn-pcm`, eff.tex:215, Definition): for `a, b` in a PCM `M`
we say `a ≤ b` iff `a ⋁ c = b` for some `c ∈ M`.  (Written `PCM.le`, scoped
notation `a ≼ b`, to keep it apart from ambient orders on concrete
carriers.) -/
def PCM.le {M : Type u} [PCM M] (a b : M) : Prop :=
  ∃ c, ∃ h : Perp a c, ovee a c h = b

@[inherit_doc] scoped infix:50 " ≼ " => PCM.le

/-- The infimum of `a` and `b` with respect to the algebraic order `≼` of a
PCM (used to state 177Ia, 208IX, … without registering an `LE` instance). -/
def PCM.IsInf {M : Type u} [PCM M] (a b m : M) : Prop :=
  m ≼ a ∧ m ≼ b ∧ ∀ c, c ≼ a → c ≼ b → c ≼ m

/-- The supremum of `a` and `b` with respect to the algebraic order `≼` of a
PCM. -/
def PCM.IsSup {M : Type u} [PCM M] (a b j : M) : Prop :=
  a ≼ j ∧ b ≼ j ∧ ∀ c, a ≼ c → b ≼ c → j ≼ c

/-- **174II** (`dfn-pcm`, eff.tex:203, Definition): a **PCM homomorphism**
`f : M → N`: whenever `a ⊥ b` also `f a ⊥ f b` and
`f a ⋁ f b = f (a ⋁ b)`. -/
structure PCMHom (M : Type u) (N : Type v) [PCM M] [PCM N] where
  toFun : M → N
  perp_map : ∀ {a b : M}, Perp a b → Perp (toFun a) (toFun b)
  ovee_map : ∀ {a b : M} (h : Perp a b),
    toFun (ovee a b h) = ovee (toFun a) (toFun b) (perp_map h)

instance {M N : Type u} [PCM M] [PCM N] : CoeFun (PCMHom M N) (fun _ => M → N) :=
  ⟨PCMHom.toFun⟩

/-- The identity PCM homomorphism. -/
def PCMHom.id (M : Type u) [PCM M] : PCMHom M M where
  toFun := _root_.id
  perp_map h := h
  ovee_map _ := rfl

/-- Composition of PCM homomorphisms. -/
def PCMHom.comp {M N K : Type u} [PCM M] [PCM N] [PCM K]
    (g : PCMHom N K) (f : PCMHom M N) : PCMHom M K where
  toFun := g.toFun ∘ f.toFun
  perp_map h := g.perp_map (f.perp_map h)
  ovee_map h := by
    show g.toFun (f.toFun _) = _
    rw [f.ovee_map, g.ovee_map]; rfl

/-- **174II** (`dfn-pcm`, eff.tex:211, Definition): the category **PCM** of
PCMs and PCM homomorphisms (objects bundled). -/
structure PCMCat : Type (u + 1) where
  carrier : Type u
  [str : PCM carrier]

attribute [instance] PCMCat.str

instance : CoeSort PCMCat.{u} (Type u) := ⟨PCMCat.carrier⟩

/-- Bundle a PCM as an object of the category `PCMCat`. -/
def PCMCat.of (M : Type u) [PCM M] : PCMCat := ⟨M⟩

instance : Category PCMCat.{u} where
  Hom M N := PCMHom M N
  id M := PCMHom.id M
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Helper (right unit): `a ⋁ 0 = a`, the mirror image of `PCM.zero_ovee`. -/
theorem PCM.ovee_zero {M : Type u} [PCM M] (a : M) (h : Perp a 0) :
    ovee a 0 h = a := by
  rw [PCM.ovee_comm]; exact PCM.zero_ovee a

/-- Helper: `a ⊥ 0` in any PCM. -/
theorem PCM.perp_zero {M : Type u} [PCM M] (a : M) : Perp a (0 : M) :=
  PCM.perp_comm (PCM.zero_perp a)

/-- Helper (left unit, arbitrary definedness proof): `0 ⋁ a = a`. -/
theorem PCM.zero_ovee' {M : Type u} [PCM M] (a : M) (h : Perp 0 a) :
    ovee 0 a h = a :=
  PCM.zero_ovee a

/-- Helper (congruence): `ovee` only depends on its two element arguments,
the definedness proof being irrelevant. -/
theorem PCM.ovee_congr {M : Type u} [PCM M] {a b a' b' : M} (ha : a = a')
    (hb : b = b') (h : Perp a b) (h' : Perp a' b') :
    ovee a b h = ovee a' b' h' := by
  subst ha; subst hb; rfl

/-- Helper (associativity, right-to-left): if `b ⊥ c` and `a ⊥ (b ⋁ c)`, then
`a ⊥ b`, `(a ⋁ b) ⊥ c` and `(a ⋁ b) ⋁ c = a ⋁ (b ⋁ c)`.  (The axiom
`PCM.ovee_assoc` only provides the left-to-right direction.) -/
theorem PCM.assoc_left {M : Type u} [PCM M] {a b c : M} (hbc : Perp b c)
    (h : Perp a (ovee b c hbc)) :
    ∃ (hab : Perp a b) (h' : Perp (ovee a b hab) c),
      ovee (ovee a b hab) c h' = ovee a (ovee b c hbc) h := by
  have hcb : Perp c b := PCM.perp_comm hbc
  have e1 : ovee c b hcb = ovee b c hbc := (PCM.ovee_comm hbc).symm
  have h2 : Perp (ovee c b hcb) a := by rw [e1]; exact PCM.perp_comm h
  have hba : Perp b a := PCM.perp_of_ovee_perp hcb h2
  have hab : Perp a b := PCM.perp_comm hba
  have h3 : Perp c (ovee b a hba) := PCM.perp_ovee_of_ovee_perp hcb h2
  have e2 : ovee b a hba = ovee a b hab := PCM.ovee_comm hba
  have h4 : Perp c (ovee a b hab) := by rw [← e2]; exact h3
  refine ⟨hab, PCM.perp_comm h4, ?_⟩
  have h5 : Perp (ovee b c hbc) a := by rw [← e1]; exact h2
  calc ovee (ovee a b hab) c (PCM.perp_comm h4)
      = ovee c (ovee a b hab) h4 := PCM.ovee_comm _
    _ = ovee c (ovee b a hba) h3 := PCM.ovee_congr rfl e2.symm _ _
    _ = ovee (ovee c b hcb) a h2 := (PCM.ovee_assoc hcb h2).symm
    _ = ovee (ovee b c hbc) a h5 := PCM.ovee_congr e1 rfl _ _
    _ = ovee a (ovee b c hbc) h := (PCM.ovee_comm h).symm

/-- **174III** (`pcm-preorder`, eff.tex:220, Exercise), part 1: `≼` is
reflexive on a PCM. -/
theorem pcm_preorder_refl {M : Type u} [PCM M] (a : M) : a ≼ a :=
  ⟨0, PCM.perp_comm (PCM.zero_perp a), by
    rw [PCM.ovee_comm, PCM.zero_ovee]⟩

/-- **174III** (`pcm-preorder`, eff.tex:220, Exercise), part 2: `≼` is
transitive on a PCM, so a PCM is preordered by `≼`. -/
theorem pcm_preorder_trans {M : Type u} [PCM M] {a b c : M} :
    a ≼ b → b ≼ c → a ≼ c := by
  rintro ⟨x, hax, rfl⟩ ⟨y, hby, rfl⟩
  exact ⟨ovee x y (PCM.perp_of_ovee_perp hax hby),
    PCM.perp_ovee_of_ovee_perp hax hby, (PCM.ovee_assoc hax hby).symm⟩

/-- The relation "`s` is a sum of the (multiset of) elements listed in `l`"
in a PCM, by iterating `ovee` (used for 174IV, and for the distributivity
axiom of effect monoids, 178II). -/
inductive PCM.IsSumOf {M : Type u} [PCM M] : List M → M → Prop
  | nil : PCM.IsSumOf [] 0
  | cons {a : M} {l : List M} {s : M} (hl : PCM.IsSumOf l s) (h : Perp a s) :
      PCM.IsSumOf (a :: l) (ovee a s h)

/-- Helper: inversion for `PCM.IsSumOf` on the empty list. -/
theorem PCM.isSumOf_nil_iff {M : Type u} [PCM M] {s : M} :
    PCM.IsSumOf [] s ↔ s = 0 := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact PCM.IsSumOf.nil

/-- Helper: inversion for `PCM.IsSumOf` on a cons. -/
theorem PCM.isSumOf_cons_iff {M : Type u} [PCM M] {a : M} {l : List M} {s : M} :
    PCM.IsSumOf (a :: l) s ↔
      ∃ (t : M) (_ : PCM.IsSumOf l t) (h : Perp a t), ovee a t h = s := by
  constructor
  · intro h
    cases h with
    | cons hl hp => exact ⟨_, hl, hp, rfl⟩
  · rintro ⟨t, hl, hp, rfl⟩
    exact PCM.IsSumOf.cons hl hp

/-- Helper for **174IV**: transposing the first two summands (this is where
`PCM.assoc_left` and partial commutativity do the work). -/
theorem PCM.isSumOf_swap {M : Type u} [PCM M] {a b : M} {l : List M} {s : M}
    (hs : PCM.IsSumOf (a :: b :: l) s) : PCM.IsSumOf (b :: a :: l) s := by
  rw [PCM.isSumOf_cons_iff] at hs
  obtain ⟨t2, hbl, h2, rfl⟩ := hs
  rw [PCM.isSumOf_cons_iff] at hbl
  obtain ⟨t, hl, h1, rfl⟩ := hbl
  -- `a ⋁ (b ⋁ t) = (a ⋁ b) ⋁ t = (b ⋁ a) ⋁ t = b ⋁ (a ⋁ t)`
  obtain ⟨hab, h', he⟩ := PCM.assoc_left h1 h2
  have hba : Perp b a := PCM.perp_comm hab
  have hcomm : ovee b a hba = ovee a b hab := PCM.ovee_comm hba
  have h'' : Perp (ovee b a hba) t := by rw [hcomm]; exact h'
  have key : ovee b (ovee a t (PCM.perp_of_ovee_perp hba h''))
      (PCM.perp_ovee_of_ovee_perp hba h'') = ovee a (ovee b t h1) h2 := by
    rw [← PCM.ovee_assoc hba h'', ← he]
    exact PCM.ovee_congr hcomm rfl _ _
  rw [← key]
  exact PCM.IsSumOf.cons (PCM.IsSumOf.cons hl _) _

/-- **174IV** (eff.tex:223, stated there without proof): in a PCM a sum
depends only on which elements occur (and how often), not on their order: if
`x₁ ⋁ ⋯ ⋁ xₙ` exists, then so does the sum over any permutation of the list,
with the same value.  (Generalized/permutation associativity.  The argument
is ours: induction over `List.Perm`, the transposition case being
`PCM.isSumOf_swap`.) -/
theorem PCM.isSumOf_perm {M : Type u} [PCM M] {l l' : List M} {s : M}
    (hp : l.Perm l') (hs : PCM.IsSumOf l s) : PCM.IsSumOf l' s := by
  induction hp generalizing s with
  | nil => exact hs
  | cons x _ ih =>
    rw [PCM.isSumOf_cons_iff] at hs
    obtain ⟨t, hl, hperp, rfl⟩ := hs
    exact PCM.IsSumOf.cons (ih hl) hperp
  | swap x y l => exact PCM.isSumOf_swap hs
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hs)

/-! ## Effect algebras (parsecs 175–177) -/

/-- **175I** (`dfn-ea`, eff.tex:247, Definition): an **effect algebra** (EA)
is a PCM `E` with a distinguished element `1` such that

1. *(orthocomplement)* every `a` has a unique `aᵖ` (written `orth a`) with
   `a ⋁ aᵖ = 1`; and
2. *(zero–one)* if `a ⊥ 1` then `a = 0`. -/
class EffectAlgebra (E : Type u) extends PCM E, One E where
  /-- The orthocomplement `aᵖ`. -/
  orth : E → E
  perp_orth : ∀ a : E, Perp a (orth a)
  ovee_orth : ∀ a : E, ovee a (orth a) (perp_orth a) = 1
  orth_unique : ∀ {a b : E} (h : Perp a b), ovee a b h = 1 → b = orth a
  eq_zero_of_perp_one : ∀ {a : E}, Perp a 1 → a = 0

export EffectAlgebra (orth)

/-- **175I** (`dfn-ea`, eff.tex:265, Definition): an **effect algebra
homomorphism** is a PCM homomorphism that preserves `1`: *(additive)*
`a ⊥ b` implies `f a ⊥ f b` and `f a ⋁ f b = f (a ⋁ b)`; *(unital)*
`f 1 = 1`.  (That `f 0 = 0` and `f (orth a) = orth (f a)` follow is
`exc-eamorphism`, 176V.) -/
structure EAHom (E : Type u) (F : Type v) [EffectAlgebra E] [EffectAlgebra F]
    extends PCMHom E F where
  map_one : toFun 1 = 1

instance {E F : Type u} [EffectAlgebra E] [EffectAlgebra F] :
    CoeFun (EAHom E F) (fun _ => E → F) := ⟨fun f => f.toFun⟩

/-- Helper (extensionality): effect algebra homomorphisms are determined by
their underlying function. -/
theorem EAHom.ext {E : Type u} {F : Type v} [EffectAlgebra E] [EffectAlgebra F]
    {f g : EAHom E F} (h : f.toFun = g.toFun) : f = g := by
  obtain ⟨⟨f₁, _, _⟩, _⟩ := f
  obtain ⟨⟨g₁, _, _⟩, _⟩ := g
  dsimp only at h
  subst h
  rfl

/-- The identity effect algebra homomorphism. -/
def EAHom.id (E : Type u) [EffectAlgebra E] : EAHom E E :=
  { PCMHom.id E with map_one := rfl }

/-- Composition of effect algebra homomorphisms. -/
def EAHom.comp {E F G : Type u} [EffectAlgebra E] [EffectAlgebra F] [EffectAlgebra G]
    (g : EAHom F G) (f : EAHom E F) : EAHom E G :=
  { g.toPCMHom.comp f.toPCMHom with
    map_one := by
      show g.toFun (f.toFun 1) = 1
      rw [f.map_one, g.map_one] }

/-- **175I** (`dfn-ea`, eff.tex:279, Definition): the category **EA** of
effect algebras and effect algebra homomorphisms. -/
structure EACat : Type (u + 1) where
  carrier : Type u
  [str : EffectAlgebra carrier]

attribute [instance] EACat.str

instance : CoeSort EACat.{u} (Type u) := ⟨EACat.carrier⟩

/-- Bundle an effect algebra as an object of `EACat`. -/
def EACat.of (E : Type u) [EffectAlgebra E] : EACat := ⟨E⟩

instance : Category EACat.{u} where
  Hom E F := EAHom E F
  id E := EAHom.id E
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- **175I** (`dfn-ea`, eff.tex:283, Definition): a subset `D ⊆ E` is a
**sub-effect algebra** if `0, 1 ∈ D` and `D` is closed under defined sums
and orthocomplements. -/
structure SubEffectAlgebra (E : Type u) [EffectAlgebra E] where
  carrier : Set E
  zero_mem : (0 : E) ∈ carrier
  one_mem : (1 : E) ∈ carrier
  ovee_mem : ∀ {a b : E} (h : Perp a b), a ∈ carrier → b ∈ carrier →
    ovee a b h ∈ carrier
  orth_mem : ∀ {a : E}, a ∈ carrier → orth a ∈ carrier

/-- **175II.1** (`eaexamples`, eff.tex:289, Examples): the real unit interval
`[0,1]` is an effect algebra with `x ⊥ y` iff `x + y ≤ 1`, `x ⋁ y = x + y`
and `xᵖ = 1 - x`. -/
noncomputable instance unitInterval.effectAlgebra : EffectAlgebra I where
  zero := 0
  one := 1
  Perp x y := (x : ℝ) + (y : ℝ) ≤ 1
  ovee x y h := ⟨(x : ℝ) + y, add_nonneg x.2.1 y.2.1, h⟩
  orth x := ⟨1 - (x : ℝ), by linarith [x.2.2], by linarith [x.2.1]⟩
  perp_comm := by intro a b h; simpa [add_comm] using h
  ovee_comm := by intro a b h; apply Subtype.ext; simp [add_comm]
  perp_of_ovee_perp := by
    intro a b c _ h
    have h' : (a : ℝ) + b + c ≤ 1 := h
    show (b : ℝ) + c ≤ 1
    linarith [a.2.1]
  perp_ovee_of_ovee_perp := by
    intro a b c _ h
    have h' : (a : ℝ) + b + c ≤ 1 := h
    show (a : ℝ) + ((b : ℝ) + c) ≤ 1
    linarith
  ovee_assoc := by intro a b c _ _; apply Subtype.ext; simp [add_assoc]
  zero_perp := by
    intro a
    show (0 : ℝ) + (a : ℝ) ≤ 1
    linarith [a.2.2]
  zero_ovee := by intro a; apply Subtype.ext; simp
  perp_orth := by
    intro a
    show (a : ℝ) + (1 - (a : ℝ)) ≤ 1
    linarith
  ovee_orth := by intro a; apply Subtype.ext; simp
  orth_unique := by
    intro a b h heq
    apply Subtype.ext
    have : (a : ℝ) + b = 1 := congrArg Subtype.val heq
    simp only; linarith
  eq_zero_of_perp_one := by
    intro a h
    have h' : (a : ℝ) + 1 ≤ 1 := h
    apply Subtype.ext
    show (a : ℝ) = 0
    linarith [a.2.1]

/-- **175II.2** (`eaexamples`, eff.tex:299, Examples): for an ordered abelian
group `G` with a distinguished element `u ≥ 0`, the order interval
`[0,u]_G` is an effect algebra with `x ⊥ y` iff `x + y ≤ u`, `x ⋁ y = x + y`
and `xᵖ = u - x`. -/
noncomputable def orderIntervalEffectAlgebra (G : Type u) [AddCommGroup G]
    [PartialOrder G] [IsOrderedAddMonoid G] (u : G) (hu : 0 ≤ u) :
    EffectAlgebra (Set.Icc (0 : G) u) where
  zero := ⟨0, le_refl 0, hu⟩
  one := ⟨u, hu, le_refl u⟩
  Perp x y := (x : G) + y ≤ u
  ovee x y h := ⟨(x : G) + y, add_nonneg x.2.1 y.2.1, h⟩
  orth x := ⟨u - x, sub_nonneg.mpr x.2.2, sub_le_self u x.2.1⟩
  perp_comm := by
    intro a b h
    show (b : G) + a ≤ u
    rw [add_comm]; exact h
  ovee_comm := by intro a b _; apply Subtype.ext; exact add_comm _ _
  perp_of_ovee_perp := by
    intro a b c _ h
    have h' : (a : G) + b + c ≤ u := h
    show (b : G) + c ≤ u
    refine le_trans ?_ h'
    rw [add_assoc]
    exact le_add_of_nonneg_left a.2.1
  perp_ovee_of_ovee_perp := by
    intro a b c _ h
    have h' : (a : G) + b + c ≤ u := h
    show (a : G) + ((b : G) + c) ≤ u
    rwa [← add_assoc]
  ovee_assoc := by intro a b c _ _; apply Subtype.ext; exact add_assoc _ _ _
  zero_perp := by
    intro a
    show (0 : G) + (a : G) ≤ u
    rw [zero_add]; exact a.2.2
  zero_ovee := by intro a; apply Subtype.ext; exact zero_add _
  perp_orth := by
    intro a
    show (a : G) + (u - (a : G)) ≤ u
    rw [show (a : G) + (u - (a : G)) = u by abel]
  ovee_orth := by
    intro a; apply Subtype.ext
    show (a : G) + (u - (a : G)) = u
    abel
  orth_unique := by
    intro a b h heq
    have h' : (a : G) + b = u := congrArg Subtype.val heq
    apply Subtype.ext
    show (b : G) = u - (a : G)
    exact eq_sub_of_add_eq' h'
  eq_zero_of_perp_one := by
    intro a h
    have h' : (a : G) + u ≤ u := h
    apply Subtype.ext
    show (a : G) = 0
    refine le_antisymm ?_ a.2.1
    have h₂ : (a : G) + u ≤ 0 + u := by rwa [zero_add]
    exact le_of_add_le_add_right h₂

/-- **175II.3** (`eaexamples`, eff.tex:307, Examples): the set of **effects**
`[0,1]_𝒜` of a von Neumann algebra `𝒜` is an effect algebra with `a ⊥ b`
iff `a + b ≤ 1`, `a ⋁ b = a + b` and `aᵖ = 1 - a`.  (The "effect" in effect
algebra originates from this example.) -/
noncomputable instance effectsEffectAlgebra (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    EffectAlgebra (Theses.effects A) where
  zero := ⟨0, le_refl 0, zero_le_one⟩
  one := ⟨1, zero_le_one, le_refl 1⟩
  Perp a b := (a : A) + b ≤ 1
  ovee a b h := ⟨(a : A) + b, add_nonneg a.2.1 b.2.1, h⟩
  orth a := ⟨1 - a, sub_nonneg.mpr a.2.2, sub_le_self 1 a.2.1⟩
  perp_comm := by
    intro a b h
    show (b : A) + a ≤ 1
    rw [add_comm]; exact h
  ovee_comm := by intro a b _; apply Subtype.ext; exact add_comm _ _
  perp_of_ovee_perp := by
    intro a b c _ h
    have h' : (a : A) + b + c ≤ 1 := h
    show (b : A) + c ≤ 1
    refine le_trans ?_ h'
    rw [add_assoc]
    exact le_add_of_nonneg_left a.2.1
  perp_ovee_of_ovee_perp := by
    intro a b c _ h
    have h' : (a : A) + b + c ≤ 1 := h
    show (a : A) + ((b : A) + c) ≤ 1
    rwa [← add_assoc]
  ovee_assoc := by intro a b c _ _; apply Subtype.ext; exact add_assoc _ _ _
  zero_perp := by
    intro a
    show (0 : A) + (a : A) ≤ 1
    rw [zero_add]; exact a.2.2
  zero_ovee := by intro a; apply Subtype.ext; exact zero_add _
  perp_orth := by
    intro a
    show (a : A) + (1 - (a : A)) ≤ 1
    rw [show (a : A) + (1 - (a : A)) = 1 by abel]
  ovee_orth := by
    intro a; apply Subtype.ext
    show (a : A) + (1 - (a : A)) = 1
    abel
  orth_unique := by
    intro a b h heq
    have h' : (a : A) + b = 1 := congrArg Subtype.val heq
    apply Subtype.ext
    show (b : A) = 1 - (a : A)
    exact eq_sub_of_add_eq' h'
  eq_zero_of_perp_one := by
    intro a h
    have h' : (a : A) + 1 ≤ 1 := h
    apply Subtype.ext
    show (a : A) = 0
    refine le_antisymm ?_ a.2.1
    have h₂ : (a : A) + 1 ≤ 0 + 1 := by rwa [zero_add]
    exact le_of_add_le_add_right h₂

/-- **175II.5** (`eaexamples`, eff.tex:323, Examples): any Boolean algebra
`L` is an effect algebra with complement as orthocomplement, `x ⊥ y` iff
`x ⊓ y = ⊥`, and `x ⋁ y = x ⊔ y`.  (A `def`, not an instance, to avoid
instance clashes on lattice carriers.) -/
def booleanEffectAlgebra (L : Type u) [BooleanAlgebra L] : EffectAlgebra L where
  zero := ⊥
  one := ⊤
  Perp x y := x ⊓ y = ⊥
  ovee x y _ := x ⊔ y
  orth x := xᶜ
  perp_comm := by intro a b h; rw [inf_comm]; exact h
  ovee_comm := by intro a b _; exact sup_comm a b
  perp_of_ovee_perp := by
    intro a b c _ h
    show b ⊓ c = ⊥
    have : b ⊓ c ≤ (a ⊔ b) ⊓ c := inf_le_inf_right c le_sup_right
    exact le_bot_iff.mp (h ▸ this)
  perp_ovee_of_ovee_perp := by
    intro a b c hab h
    have hac : a ⊓ c = ⊥ :=
      le_bot_iff.mp (h ▸ (inf_le_inf_right c le_sup_left : a ⊓ c ≤ (a ⊔ b) ⊓ c))
    show a ⊓ (b ⊔ c) = ⊥
    rw [inf_sup_left, hab, hac, sup_idem]
  ovee_assoc := by intro a b c _ _; exact sup_assoc a b c
  zero_perp := by intro a; show (⊥ : L) ⊓ a = ⊥; exact bot_inf_eq a
  zero_ovee := by intro a; show (⊥ : L) ⊔ a = a; exact bot_sup_eq a
  perp_orth := by intro a; show a ⊓ aᶜ = ⊥; exact inf_compl_eq_bot
  ovee_orth := by intro a; show a ⊔ aᶜ = ⊤; exact sup_compl_eq_top
  orth_unique := by
    intro a b h heq
    exact (compl_unique h heq).symm
  eq_zero_of_perp_one := by
    intro a h
    have h' : a ⊓ (⊤ : L) = ⊥ := h
    rwa [inf_top_eq] at h'

/-- The two-element Boolean algebra `2 = {0, 1}` as an effect algebra
(175II.6, `eaexamples`). -/
instance : EffectAlgebra Bool := booleanEffectAlgebra Bool

/-- The one-element (Boolean) effect algebra `1 = {0 = 1}` (175II.6,
`eaexamples`). -/
instance : EffectAlgebra PUnit where
  zero := PUnit.unit
  one := PUnit.unit
  Perp _ _ := True
  ovee _ _ _ := PUnit.unit
  orth _ := PUnit.unit
  perp_comm _ := trivial
  ovee_comm _ := rfl
  perp_of_ovee_perp _ _ := trivial
  perp_ovee_of_ovee_perp _ _ := trivial
  ovee_assoc _ _ := rfl
  zero_perp _ := trivial
  zero_ovee _ := rfl
  perp_orth _ := trivial
  ovee_orth _ := rfl
  orth_unique _ _ := rfl
  eq_zero_of_perp_one _ := rfl

/-- **175II.6** (`eaexamples`, eff.tex:330, Examples): the one-element
Boolean algebra `1` is the final object of **EA**. -/
theorem eaexamples_final : Nonempty (IsTerminal (EACat.of PUnit.{u + 1})) := by
  have mk : ∀ E : EACat.{u}, (E ⟶ EACat.of PUnit.{u + 1}) := fun _ =>
    { toFun := fun _ => PUnit.unit
      perp_map := fun _ => trivial
      ovee_map := fun _ => rfl
      map_one := rfl }
  exact ⟨IsTerminal.ofUniqueHom mk fun _ _ => EAHom.ext (funext fun _ => rfl)⟩

/-- **175II.6** (`eaexamples`, eff.tex:330, Examples): the two-element
Boolean algebra `2` is the initial object of **EA**.  (Stated in universe 0,
where `Bool` lives.) -/
theorem eaexamples_initial : Nonempty (IsInitial (EACat.of Bool)) := by
  -- `f 0 = 0` for any effect algebra homomorphism (176V.1, proved below as
  -- `exc_eamorphism_map_zero`; inlined here as that comes later in the file).
  have hz : ∀ (E : EACat.{0}) (f : EACat.of Bool ⟶ E), f.toFun false = 0 := by
    intro E f
    have h : Perp (f.toFun 0) (f.toFun 1) := f.perp_map (PCM.zero_perp 1)
    rw [f.map_one] at h
    exact EffectAlgebra.eq_zero_of_perp_one h
  let mk : ∀ E : EACat.{0}, (EACat.of Bool ⟶ E) := by
    intro E
    have hp : ∀ {a b : Bool}, Perp a b →
        Perp (if a then (1 : E.carrier) else 0) (if b then (1 : E.carrier) else 0) := by
      intro a b h
      cases a <;> cases b
      · exact PCM.zero_perp 0
      · exact PCM.zero_perp 1
      · exact PCM.perp_zero 1
      · have h' : (true : Bool) ⊓ true = ⊥ := h
        exact absurd h' (by decide)
    have ho : ∀ {a b : Bool} (h : Perp a b),
        (if (ovee a b h) then (1 : E.carrier) else 0)
          = ovee (if a then (1 : E.carrier) else 0)
              (if b then (1 : E.carrier) else 0) (hp h) := by
      intro a b h
      cases a <;> cases b
      · exact (PCM.zero_ovee (0 : E.carrier)).symm
      · exact (PCM.zero_ovee (1 : E.carrier)).symm
      · exact (PCM.ovee_zero (1 : E.carrier) _).symm
      · have h' : (true : Bool) ⊓ true = ⊥ := h
        exact absurd h' (by decide)
    exact
      { toFun := fun b : Bool => if b then (1 : E.carrier) else 0
        perp_map := hp
        ovee_map := ho
        map_one := rfl }
  refine ⟨IsInitial.ofUniqueHom mk ?_⟩
  intro E f
  refine EAHom.ext (funext fun b => ?_)
  cases b
  · exact hz E f
  · exact f.map_one

/-- **175III** (`ea-product`, eff.tex:338, Exercise), part 1: the cartesian
product `E × F` of two effect algebras is an effect algebra with
componentwise operations. -/
instance prodEffectAlgebra (E F : Type u) [EffectAlgebra E] [EffectAlgebra F] :
    EffectAlgebra (E × F) where
  zero := (0, 0)
  one := (1, 1)
  Perp p q := Perp p.1 q.1 ∧ Perp p.2 q.2
  ovee p q h := (ovee p.1 q.1 h.1, ovee p.2 q.2 h.2)
  orth p := (orth p.1, orth p.2)
  perp_comm h := ⟨PCM.perp_comm h.1, PCM.perp_comm h.2⟩
  ovee_comm h := Prod.ext (PCM.ovee_comm h.1) (PCM.ovee_comm h.2)
  perp_of_ovee_perp hab h :=
    ⟨PCM.perp_of_ovee_perp hab.1 h.1, PCM.perp_of_ovee_perp hab.2 h.2⟩
  perp_ovee_of_ovee_perp hab h :=
    ⟨PCM.perp_ovee_of_ovee_perp hab.1 h.1, PCM.perp_ovee_of_ovee_perp hab.2 h.2⟩
  ovee_assoc hab h := Prod.ext (PCM.ovee_assoc hab.1 h.1) (PCM.ovee_assoc hab.2 h.2)
  zero_perp a := ⟨PCM.zero_perp a.1, PCM.zero_perp a.2⟩
  zero_ovee a := Prod.ext (PCM.zero_ovee a.1) (PCM.zero_ovee a.2)
  perp_orth a := ⟨EffectAlgebra.perp_orth a.1, EffectAlgebra.perp_orth a.2⟩
  ovee_orth a := Prod.ext (EffectAlgebra.ovee_orth a.1) (EffectAlgebra.ovee_orth a.2)
  orth_unique h heq :=
    Prod.ext (EffectAlgebra.orth_unique h.1 (congrArg Prod.fst heq))
      (EffectAlgebra.orth_unique h.2 (congrArg Prod.snd heq))
  eq_zero_of_perp_one h :=
    Prod.ext (EffectAlgebra.eq_zero_of_perp_one h.1)
      (EffectAlgebra.eq_zero_of_perp_one h.2)

/-- **175III** (`ea-product`, eff.tex:338, Exercise), part 2: `E × F` with
the componentwise structure is the categorical product in **EA** (stated
here as: **EA** has binary products). -/
theorem ea_product_categorical : HasBinaryProducts EACat.{u} := by
  have hl : ∀ {X Y : EACat.{u}}, HasLimit (pair X Y) := by
    intro X Y
    let p1 : EACat.of (X.carrier × Y.carrier) ⟶ X :=
      { toFun := Prod.fst
        perp_map := fun h => h.1
        ovee_map := fun _ => rfl
        map_one := rfl }
    let p2 : EACat.of (X.carrier × Y.carrier) ⟶ Y :=
      { toFun := Prod.snd
        perp_map := fun h => h.2
        ovee_map := fun _ => rfl
        map_one := rfl }
    let lift : ∀ s : BinaryFan X Y, (s.pt ⟶ EACat.of (X.carrier × Y.carrier)) :=
      fun s =>
      { toFun := fun z => (s.fst.toFun z, s.snd.toFun z)
        perp_map := fun h => ⟨s.fst.perp_map h, s.snd.perp_map h⟩
        ovee_map := fun h => Prod.ext (s.fst.ovee_map h) (s.snd.ovee_map h)
        map_one := Prod.ext s.fst.map_one s.snd.map_one }
    refine HasLimit.mk ⟨BinaryFan.mk p1 p2,
      BinaryFan.isLimitMk lift (fun _ => rfl) (fun _ => rfl) ?_⟩
    intro s m e₁ e₂
    refine EAHom.ext (funext fun z => Prod.ext ?_ ?_)
    · exact congrFun (congrArg (fun f : s.pt ⟶ X => f.toFun) e₁) z
    · exact congrFun (congrArg (fun f : s.pt ⟶ Y => f.toFun) e₂) z
  exact hasBinaryProducts_of_hasLimit_pair EACat.{u}

/-- The data of an effect algebra *without* the zero axiom (`0 ⊥ a` and
`0 ⋁ a = a`), used to state the redundancy exercise **175IV**
(`ea-redund`). -/
structure EASansZero (M : Type u) where
  zero : M
  one : M
  Perp : M → M → Prop
  ovee : (a b : M) → Perp a b → M
  perp_comm : ∀ {a b : M}, Perp a b → Perp b a
  ovee_comm : ∀ {a b : M} (h : Perp a b), ovee a b h = ovee b a (perp_comm h)
  perp_of_ovee_perp : ∀ {a b c : M} (hab : Perp a b), Perp (ovee a b hab) c → Perp b c
  perp_ovee_of_ovee_perp : ∀ {a b c : M} (hab : Perp a b) (h : Perp (ovee a b hab) c),
    Perp a (ovee b c (perp_of_ovee_perp hab h))
  ovee_assoc : ∀ {a b c : M} (hab : Perp a b) (h : Perp (ovee a b hab) c),
    ovee (ovee a b hab) c h
      = ovee a (ovee b c (perp_of_ovee_perp hab h)) (perp_ovee_of_ovee_perp hab h)
  orth : M → M
  perp_orth : ∀ a : M, Perp a (orth a)
  ovee_orth : ∀ a : M, ovee a (orth a) (perp_orth a) = one
  orth_unique : ∀ {a b : M} (h : Perp a b), ovee a b h = one → b = orth a
  eq_zero_of_perp_one : ∀ {a : M}, Perp a one → a = zero

/-- **175IV** (`ea-redund`, eff.tex:348, Exercise): the zero axiom of an
effect algebra is redundant — it follows from partial commutativity, partial
associativity, orthocomplement and zero–one. -/
theorem ea_redund {M : Type u} (S : EASansZero M) :
    ∀ a : M, ∃ h : S.Perp S.zero a, S.ovee S.zero a h = a := by
  have congr' : ∀ {x y x' y' : M}, x = x' → y = y' →
      ∀ (h : S.Perp x y) (h' : S.Perp x' y'), S.ovee x y h = S.ovee x' y' h' := by
    rintro x y x' y' rfl rfl h h'; rfl
  -- `1ᵖ = 0`, by the zero–one law applied to `1ᵖ ⊥ 1`.
  have h1 : S.orth S.one = S.zero :=
    S.eq_zero_of_perp_one (S.perp_comm (S.perp_orth S.one))
  -- `aᵖᵖ = a`, by uniqueness of the orthocomplement.
  have hinv : ∀ a : M, S.orth (S.orth a) = a := by
    intro a
    refine (S.orth_unique (S.perp_comm (S.perp_orth a)) ?_).symm
    exact (S.ovee_comm (S.perp_orth a)).symm.trans (S.ovee_orth a)
  -- `pᵖ ⋁ 0 = pᵖ`, from `p ⋁ (pᵖ ⋁ 0) = (p ⋁ pᵖ) ⋁ 0 = 1 ⋁ 1ᵖ = 1`.
  have key : ∀ p : M, ∃ h : S.Perp (S.orth p) S.zero,
      S.ovee (S.orth p) S.zero h = S.orth p := by
    intro p
    have hpo : S.Perp p (S.orth p) := S.perp_orth p
    have hone : S.ovee p (S.orth p) hpo = S.one := S.ovee_orth p
    have hpz : S.Perp (S.ovee p (S.orth p) hpo) S.zero := by
      rw [← h1, ← hone]; exact S.perp_orth _
    have hazero : S.Perp (S.orth p) S.zero := S.perp_of_ovee_perp hpo hpz
    have hA : S.Perp p (S.ovee (S.orth p) S.zero hazero) :=
      S.perp_ovee_of_ovee_perp hpo hpz
    have e1 : S.ovee (S.ovee p (S.orth p) hpo) S.zero hpz
        = S.ovee p (S.ovee (S.orth p) S.zero hazero) hA := S.ovee_assoc hpo hpz
    have hE : S.ovee p (S.ovee (S.orth p) S.zero hazero) hA = S.one := by
      refine e1.symm.trans (Eq.trans ?_ (S.ovee_orth S.one))
      exact congr' hone h1.symm hpz (S.perp_orth S.one)
    exact ⟨hazero, S.orth_unique hA hE⟩
  intro a
  obtain ⟨h, e⟩ := key (S.orth a)
  have ha : S.Perp a S.zero := (hinv a) ▸ h
  have ea' : S.ovee a S.zero ha = a := by
    rw [congr' (hinv a).symm rfl ha h, e, hinv a]
  exact ⟨S.perp_comm ha, (S.ovee_comm ha).symm.trans ea'⟩

section EABasics

variable {E : Type u} [EffectAlgebra E]

/-- **175V.1** (`eabasics`, eff.tex:354, Proposition): *(involution)*
`aᵖᵖ = a`. -/
theorem eabasics_orth_orth (a : E) : orth (orth a) = a :=
  (EffectAlgebra.orth_unique (PCM.perp_comm (EffectAlgebra.perp_orth a))
    (by rw [← PCM.ovee_comm]; exact EffectAlgebra.ovee_orth a)).symm

/-- **175V.2** (`eabasics`, eff.tex:354, Proposition): `1ᵖ = 0`. -/
theorem eabasics_orth_one : orth (1 : E) = 0 := by
  have := eabasics_orth_orth (0 : E)
  rwa [(EffectAlgebra.orth_unique (PCM.zero_perp (1 : E)) (PCM.zero_ovee 1)).symm] at this

/-- **175V.2** (`eabasics`, eff.tex:354, Proposition): `0ᵖ = 1`. -/
theorem eabasics_orth_zero : orth (0 : E) = 1 :=
  (EffectAlgebra.orth_unique (PCM.zero_perp (1 : E)) (PCM.zero_ovee 1)).symm

/-- **175V.3** (`eabasics`, eff.tex:354, Proposition): *(positivity)* if
`a ⋁ b = 0` then `a = 0` and `b = 0`. -/
theorem eabasics_positivity {a b : E} (h : Perp a b) (h0 : ovee a b h = 0) :
    a = 0 ∧ b = 0 := by
  have key : ∀ {x y : E} (hxy : Perp x y), ovee x y hxy = 0 → y = 0 := by
    intro x y hxy hxy0
    refine EffectAlgebra.eq_zero_of_perp_one (PCM.perp_of_ovee_perp hxy ?_)
    rw [hxy0]; exact PCM.zero_perp 1
  refine ⟨key (PCM.perp_comm h) ?_, key h h0⟩
  rw [← PCM.ovee_comm]; exact h0

/-- **175V.4** (`eabasics`, eff.tex:354, Proposition): *(cancellation)* if
`a ⋁ c = b ⋁ c` then `a = b`. -/
theorem eabasics_cancellation {a b c : E} (h₁ : Perp a c) (h₂ : Perp b c)
    (h : ovee a c h₁ = ovee b c h₂) : a = b := by
  -- `c ⋁ (a ⋁ c)ᵖ` is an orthocomplement of `a` and, since `a ⋁ c = b ⋁ c`,
  -- also one of `b`; orthocomplements are unique and involutive.
  have key : ∀ {x : E} (hx : Perp x c),
      ovee c (orth (ovee x c hx))
          (PCM.perp_of_ovee_perp hx (EffectAlgebra.perp_orth (ovee x c hx))) = orth x := by
    intro x hx
    refine EffectAlgebra.orth_unique
      (PCM.perp_ovee_of_ovee_perp hx (EffectAlgebra.perp_orth (ovee x c hx))) ?_
    rw [← PCM.ovee_assoc hx (EffectAlgebra.perp_orth (ovee x c hx))]
    exact EffectAlgebra.ovee_orth _
  have ha := key h₁
  have hb := key h₂
  have : orth a = orth b := by
    rw [← ha, ← hb]
    congr 1
    simp only [h]
  rw [← eabasics_orth_orth a, ← eabasics_orth_orth b, this]

/-- Helper: if `a ⊥ b` then `b ≼ aᵖ`, with witness `(a ⋁ b)ᵖ`. -/
theorem perp_le_orth {a b : E} (h : Perp a b) : b ≼ orth a := by
  have hab' : Perp (ovee a b h) (orth (ovee a b h)) := EffectAlgebra.perp_orth _
  refine ⟨orth (ovee a b h), PCM.perp_of_ovee_perp h hab',
    EffectAlgebra.orth_unique (PCM.perp_ovee_of_ovee_perp h hab') ?_⟩
  rw [← PCM.ovee_assoc h hab']
  exact EffectAlgebra.ovee_orth _

/-- **175V.5** (`eabasics`, eff.tex:354, Proposition): the relation `≼` of
174II partially orders `E` (antisymmetry; reflexivity and transitivity are
174III). -/
theorem eabasics_le_antisymm {a b : E} (hab : a ≼ b) (hba : b ≼ a) : a = b := by
  obtain ⟨x, hax, rfl⟩ := hab
  obtain ⟨y, hby, hy⟩ := hba
  have hxy : Perp x y := PCM.perp_of_ovee_perp hax hby
  have hsum : ovee a (ovee x y hxy) (PCM.perp_ovee_of_ovee_perp hax hby) = a := by
    rw [← PCM.ovee_assoc hax hby]; exact hy
  have h0 : ovee x y hxy = 0 := by
    refine eabasics_cancellation (c := a)
      (PCM.perp_comm (PCM.perp_ovee_of_ovee_perp hax hby)) (PCM.zero_perp a) ?_
    rw [← PCM.ovee_comm, PCM.zero_ovee]; exact hsum
  have hx0 : x = 0 := (eabasics_positivity hxy h0).1
  subst hx0
  exact (PCM.ovee_zero a hax).symm

/-- **175V.6** (`eabasics`, eff.tex:354, Proposition): `a ≼ b` iff
`bᵖ ≼ aᵖ`. -/
theorem eabasics_le_iff_orth_le {a b : E} : a ≼ b ↔ orth b ≼ orth a := by
  -- `a ⋁ c = b` implies `c ⋁ bᵖ = aᵖ`, hence `bᵖ ≼ aᵖ`.
  have key : ∀ {x y : E}, x ≼ y → orth y ≼ orth x := by
    rintro x y ⟨c, hxc, rfl⟩
    have hp : Perp (ovee x c hxc) (orth (ovee x c hxc)) := EffectAlgebra.perp_orth _
    have h1 : Perp c (orth (ovee x c hxc)) := PCM.perp_of_ovee_perp hxc hp
    have h2 : ovee c (orth (ovee x c hxc)) h1 = orth x :=
      EffectAlgebra.orth_unique (PCM.perp_ovee_of_ovee_perp hxc hp) (by
        rw [← PCM.ovee_assoc hxc hp]; exact EffectAlgebra.ovee_orth _)
    exact ⟨c, PCM.perp_comm h1, by rw [← PCM.ovee_comm]; exact h2⟩
  refine ⟨key, fun h => ?_⟩
  have := key h
  rwa [eabasics_orth_orth, eabasics_orth_orth] at this

/-- **175V.7** (`eabasics`, eff.tex:354, Proposition): if `a ≼ b` and
`b ⊥ c`, then `a ⊥ c` and `a ⋁ c ≼ b ⋁ c`. -/
theorem eabasics_le_perp_compat {a b c : E} (hab : a ≼ b) (hbc : Perp b c) :
    ∃ hac : Perp a c, ovee a c hac ≼ ovee b c hbc := by
  -- Write `b = a ⋁ d`; then `b ⋁ c = a ⋁ (d ⋁ c) = a ⋁ (c ⋁ d) = (a ⋁ c) ⋁ d`.
  obtain ⟨d, had, rfl⟩ := hab
  have hdc : Perp d c := PCM.perp_of_ovee_perp had hbc
  have hA : Perp a (ovee d c hdc) := PCM.perp_ovee_of_ovee_perp had hbc
  have eA : ovee (ovee a d had) c hbc = ovee a (ovee d c hdc) hA :=
    PCM.ovee_assoc had hbc
  have hcd : Perp c d := PCM.perp_comm hdc
  have e : ovee c d hcd = ovee d c hdc := (PCM.ovee_comm hdc).symm
  have hB : Perp a (ovee c d hcd) := by rw [e]; exact hA
  obtain ⟨hac, h', eq⟩ := PCM.assoc_left hcd hB
  refine ⟨hac, d, h', ?_⟩
  rw [eq, eA]
  exact PCM.ovee_congr rfl e hB hA

/-- **175V.8** (`eabasics`, eff.tex:354, Proposition): `a ⊥ b` iff
`a ≼ bᵖ`. -/
theorem eabasics_perp_iff_le_orth {a b : E} : Perp a b ↔ a ≼ orth b := by
  constructor
  · exact fun h => perp_le_orth (PCM.perp_comm h)
  · rintro ⟨c, hac, hc⟩
    -- `a ⋁ c = bᵖ`, so `b ⊥ (c ⋁ a)`, whence `a ⊥ b`.
    have h1 : Perp b (ovee a c hac) := by rw [hc]; exact EffectAlgebra.perp_orth b
    refine PCM.perp_of_ovee_perp (PCM.perp_comm hac) (PCM.perp_comm ?_)
    rwa [PCM.ovee_comm] at h1


/-! ### Partial difference and D-posets (parsec 176) -/

/-- **176I** (eff.tex:430, Definition): `IsDiff b a c` says that `c` is *the*
difference `b ⊖ a`, i.e. `a ⋁ c = b`; by cancellation such a `c` is unique
if it exists. -/
def IsDiff (b a c : E) : Prop := ∃ h : Perp a c, ovee a c h = b

/-- **176I** (eff.tex:430, Definition): well-definedness of `⊖` — the
difference is unique (by cancellation). -/
theorem isDiff_unique {b a c c' : E} (h : IsDiff b a c) (h' : IsDiff b a c') :
    c = c' := by
  obtain ⟨h1, e1⟩ := h
  obtain ⟨h2, e2⟩ := h'
  have k1 : ovee c a (PCM.perp_comm h1) = b := by rw [← PCM.ovee_comm h1]; exact e1
  have k2 : ovee c' a (PCM.perp_comm h2) = b := by rw [← PCM.ovee_comm h2]; exact e2
  exact eabasics_cancellation (PCM.perp_comm h1) (PCM.perp_comm h2) (k1.trans k2.symm)

/-- **176I** (eff.tex:430, Definition): the difference `b ⊖ a`, defined when
`a ≼ b`. -/
noncomputable def ominus (b a : E) (h : a ≼ b) : E := h.choose

/-- The defining property of `ominus`: `b ⊖ a` really is a difference. -/
theorem isDiff_ominus {b a : E} (h : a ≼ b) : IsDiff b a (ominus b a h) :=
  h.choose_spec

/-- **176II** (`exc-dposet`, eff.tex:437, Exercise\*), (D1): `a ⊖ b` is
defined iff `b ≼ a`. -/
theorem exc_dposet_D1 {a b : E} : (∃ c, IsDiff a b c) ↔ b ≼ a := Iff.rfl

/-- **176II** (`exc-dposet`, eff.tex:437, Exercise\*), (D2): `a ⊖ b ≼ a`
(when defined). -/
theorem exc_dposet_D2 {a b c : E} (h : IsDiff a b c) : c ≼ a := by
  obtain ⟨hbc, e⟩ := h
  exact ⟨b, PCM.perp_comm hbc, by rw [← PCM.ovee_comm]; exact e⟩

/-- **176II** (`exc-dposet`, eff.tex:437, Exercise\*), (D3):
`a ⊖ (a ⊖ b) = b` (when defined). -/
theorem exc_dposet_D3 {a b c : E} (h : IsDiff a b c) : IsDiff a c b := by
  obtain ⟨hbc, e⟩ := h
  exact ⟨PCM.perp_comm hbc, by rw [← PCM.ovee_comm]; exact e⟩

/-- **176II** (`exc-dposet`, eff.tex:437, Exercise\*), (D4): if
`a ≼ b ≼ c`, then `c ⊖ b ≼ c ⊖ a` and
`(c ⊖ a) ⊖ (c ⊖ b) = b ⊖ a`. -/
theorem exc_dposet_D4 {a b c u v : E} (hab : a ≼ b) (hbc : b ≼ c)
    (hu : IsDiff c b u) (hv : IsDiff c a v) :
    u ≼ v ∧ ∀ w, IsDiff v u w → IsDiff b a w := by
  -- Write `b = a ⋁ t`; then `c = b ⋁ u = a ⋁ (t ⋁ u) = a ⋁ v`, so `v = t ⋁ u`.
  obtain ⟨t, hat, rfl⟩ := hab
  obtain ⟨hbu, hc⟩ := hu
  obtain ⟨hav, hc'⟩ := hv
  have htu : Perp t u := PCM.perp_of_ovee_perp hat hbu
  have hatu : Perp a (ovee t u htu) := PCM.perp_ovee_of_ovee_perp hat hbu
  have ec : ovee a (ovee t u htu) hatu = c := by
    rw [← PCM.ovee_assoc hat hbu]; exact hc
  have hveq : ovee t u htu = v := by
    have k1 : ovee (ovee t u htu) a (PCM.perp_comm hatu) = c := by
      rw [← PCM.ovee_comm hatu]; exact ec
    have k2 : ovee v a (PCM.perp_comm hav) = c := by
      rw [← PCM.ovee_comm hav]; exact hc'
    exact eabasics_cancellation (PCM.perp_comm hatu) (PCM.perp_comm hav)
      (k1.trans k2.symm)
  refine ⟨⟨t, PCM.perp_comm htu, by rw [← PCM.ovee_comm htu]; exact hveq⟩, ?_⟩
  rintro w ⟨huw, hw⟩
  have hwt : w = t := by
    have k1 : ovee w u (PCM.perp_comm huw) = v := by
      rw [← PCM.ovee_comm huw]; exact hw
    exact eabasics_cancellation (PCM.perp_comm huw) htu (k1.trans hveq.symm)
  subst hwt
  exact ⟨hat, rfl⟩

end EABasics

/-- **176IV** (eff.tex:457, Remark): a **difference-poset** (D-poset): a
poset with maximum `1` and a partial operation `⊖` (here `sub a b h` for
`h : b ≤ a`, building (D1) into the type) satisfying (D2)–(D4).  By 176III
this is an alternative axiomatization of effect algebras. -/
class DPoset (E : Type u) extends PartialOrder E, OrderTop E where
  /-- The difference `a ⊖ b`, defined for `b ≤ a` (D1). -/
  sub : (a b : E) → b ≤ a → E
  /-- (D2) `a ⊖ b ≤ a`. -/
  sub_le : ∀ {a b : E} (h : b ≤ a), sub a b h ≤ a
  /-- (D3) `a ⊖ (a ⊖ b) = b`. -/
  sub_sub : ∀ {a b : E} (h : b ≤ a), sub a (sub a b h) (sub_le h) = b
  /-- (D4), first half: if `a ≤ b ≤ c` then `c ⊖ b ≤ c ⊖ a`. -/
  sub_antitone : ∀ {a b c : E} (hab : a ≤ b) (hbc : b ≤ c),
    sub c b hbc ≤ sub c a (hab.trans hbc)
  /-- (D4), second half: `(c ⊖ a) ⊖ (c ⊖ b) = b ⊖ a`. -/
  sub_sub_eq : ∀ {a b c : E} (hab : a ≤ b) (hbc : b ≤ c),
    sub (sub c a (hab.trans hbc)) (sub c b hbc) (sub_antitone hab hbc) = sub b a hab

namespace DPoset

variable {E : Type u} [DPoset E]

/-- Helper for 176III: `a ⊖ b` does not depend on the proof of `b ≤ a`, so it
is a congruence in both of its element arguments. -/
theorem sub_congr {a b a' b' : E} (ha : a = a') (hb : b = b')
    {h : b ≤ a} {h' : b' ≤ a'} : sub a b h = sub a' b' h' := by
  subst ha; subst hb; rfl

/-- Helper for 176III: `(1 ⊖ b) ⊖ (c ⊖ b) = 1 ⊖ c` for `b ≤ c` (two
applications of (D3)/(D4)). -/
theorem sub_top_sub {b c : E} (hc : b ≤ c) :
    ∃ hle : sub c b hc ≤ sub ⊤ b (hc.trans le_top),
      sub (sub ⊤ b (hc.trans le_top)) (sub c b hc) hle = sub ⊤ c le_top := by
  have e1 : sub (sub ⊤ b (hc.trans le_top)) (sub ⊤ c le_top)
      (sub_antitone hc le_top) = sub c b hc := sub_sub_eq hc le_top
  have hle : sub c b hc ≤ sub ⊤ b (hc.trans le_top) := by
    rw [← e1]; exact sub_le _
  exact ⟨hle, (sub_congr rfl e1.symm).trans (sub_sub (sub_antitone hc le_top))⟩

/-- **176III**: `⊖` is cancellative in its first argument — this is what makes
`a ⋁ b = c ⇔ c ⊖ b = a` at most single-valued. -/
theorem sub_left_cancel {b c₁ c₂ : E} (h₁ : b ≤ c₁) (h₂ : b ≤ c₂)
    (h : sub c₁ b h₁ = sub c₂ b h₂) : c₁ = c₂ := by
  obtain ⟨hle₁, e₁⟩ := sub_top_sub h₁
  obtain ⟨hle₂, e₂⟩ := sub_top_sub h₂
  have key : sub ⊤ c₁ le_top = sub ⊤ c₂ le_top := by
    rw [← e₁, ← e₂]; exact sub_congr rfl h
  calc c₁ = sub ⊤ (sub ⊤ c₁ le_top) (sub_le le_top) := (sub_sub le_top).symm
    _ = sub ⊤ (sub ⊤ c₂ le_top) (sub_le le_top) := sub_congr rfl key
    _ = c₂ := sub_sub le_top

/-- **176III**: the definedness relation of the effect algebra structure on a
D-poset: `a ⊥ b` when `a = c ⊖ b` for some `c ≥ b`. -/
def DPerp (a b : E) : Prop := ∃ (c : E) (h : b ≤ c), sub c b h = a

/-- **176III**: the partial sum `a ⋁ b` of a D-poset. -/
noncomputable def dovee (a b : E) (h : DPerp a b) : E := h.choose

theorem le_dovee {a b : E} (h : DPerp a b) : b ≤ dovee a b h := h.choose_spec.choose

theorem sub_dovee {a b : E} (h : DPerp a b) :
    sub (dovee a b h) b (le_dovee h) = a := h.choose_spec.choose_spec

/-- `a ⋁ b` is the unique `c ≥ b` with `c ⊖ b = a`. -/
theorem dovee_eq {a b c : E} (hab : DPerp a b) (h : b ≤ c) (e : sub c b h = a) :
    dovee a b hab = c :=
  sub_left_cancel (le_dovee hab) h ((sub_dovee hab).trans e.symm)

theorem le_left_dovee {a b : E} (h : DPerp a b) : a ≤ dovee a b h := by
  have hh := sub_le (le_dovee h)
  rwa [sub_dovee h] at hh

theorem sub_dovee_left {a b : E} (h : DPerp a b) :
    sub (dovee a b h) a (le_left_dovee h) = b :=
  (sub_congr rfl (sub_dovee h).symm).trans (sub_sub (le_dovee h))

theorem dperp_comm {a b : E} (h : DPerp a b) : DPerp b a :=
  ⟨dovee a b h, le_left_dovee h, sub_dovee_left h⟩

theorem dovee_comm {a b : E} (h : DPerp a b) :
    dovee a b h = dovee b a (dperp_comm h) :=
  (dovee_eq (dperp_comm h) (le_left_dovee h) (sub_dovee_left h)).symm

/-- Abbreviation for the proof `a ≤ (a ⋁ b) ⋁ c` used throughout the proof of
partial associativity (176III). -/
theorem le_dovee_dovee {a b c : E} (hab : DPerp a b)
    (h : DPerp (dovee a b hab) c) : a ≤ dovee (dovee a b hab) c h :=
  (le_left_dovee hab).trans (le_left_dovee h)

/-- The key computation of partial associativity (176III): applying (D4) to
`a ≤ a ⋁ b ≤ (a ⋁ b) ⋁ c` gives `(((a ⋁ b) ⋁ c) ⊖ a) ⊖ c = b`. -/
theorem sub_dovee_dovee_sub {a b c : E} (hab : DPerp a b)
    (h : DPerp (dovee a b hab) c) :
    ∃ hle : c ≤ sub (dovee (dovee a b hab) c h) a (le_dovee_dovee hab h),
      sub (sub (dovee (dovee a b hab) c h) a (le_dovee_dovee hab h)) c hle = b := by
  have hvu : sub (dovee (dovee a b hab) c h) (dovee a b hab) (le_left_dovee h) = c :=
    sub_dovee_left h
  have hua : sub (dovee a b hab) a (le_left_dovee hab) = b := sub_dovee_left hab
  have hle : c ≤ sub (dovee (dovee a b hab) c h) a (le_dovee_dovee hab h) := by
    have hh := sub_antitone (le_left_dovee hab) (le_left_dovee h)
    rwa [hvu] at hh
  refine ⟨hle, ?_⟩
  calc sub (sub (dovee (dovee a b hab) c h) a (le_dovee_dovee hab h)) c hle
      = sub (sub (dovee (dovee a b hab) c h) a (le_dovee_dovee hab h))
          (sub (dovee (dovee a b hab) c h) (dovee a b hab) (le_left_dovee h))
          (sub_antitone (le_left_dovee hab) (le_left_dovee h)) := sub_congr rfl hvu.symm
    _ = sub (dovee a b hab) a (le_left_dovee hab) :=
        sub_sub_eq (le_left_dovee hab) (le_left_dovee h)
    _ = b := hua

theorem dperp_of_dovee_dperp {a b c : E} (hab : DPerp a b)
    (h : DPerp (dovee a b hab) c) : DPerp b c :=
  ⟨_, (sub_dovee_dovee_sub hab h).choose, (sub_dovee_dovee_sub hab h).choose_spec⟩

theorem dovee_bc {a b c : E} (hab : DPerp a b) (h : DPerp (dovee a b hab) c) :
    dovee b c (dperp_of_dovee_dperp hab h)
      = sub (dovee (dovee a b hab) c h) a (le_dovee_dovee hab h) :=
  dovee_eq _ (sub_dovee_dovee_sub hab h).choose (sub_dovee_dovee_sub hab h).choose_spec

theorem dperp_dovee_of_dovee_dperp {a b c : E} (hab : DPerp a b)
    (h : DPerp (dovee a b hab) c) :
    DPerp a (dovee b c (dperp_of_dovee_dperp hab h)) := by
  refine ⟨dovee (dovee a b hab) c h, ?_, ?_⟩
  · rw [dovee_bc hab h]; exact sub_le _
  · exact (sub_congr rfl (dovee_bc hab h)).trans (sub_sub (le_dovee_dovee hab h))

theorem dovee_assoc {a b c : E} (hab : DPerp a b)
    (h : DPerp (dovee a b hab) c) :
    dovee (dovee a b hab) c h
      = dovee a (dovee b c (dperp_of_dovee_dperp hab h))
          (dperp_dovee_of_dovee_dperp hab h) :=
  (dovee_eq _ (by rw [dovee_bc hab h]; exact sub_le _)
    ((sub_congr rfl (dovee_bc hab h)).trans (sub_sub (le_dovee_dovee hab h)))).symm


/-- **176III**: `1 ⊖ 1` is the least element. -/
theorem dzero_le (x : E) : sub (⊤ : E) ⊤ le_rfl ≤ x := by
  have e : sub (⊤ : E) (sub ⊤ x le_top) (sub_le le_top) = x := sub_sub le_top
  have hle := sub_antitone (le_top : sub (⊤ : E) x le_top ≤ ⊤) (le_refl (⊤ : E))
  rwa [e] at hle

/-- **176III**: `x ⊖ (1 ⊖ 1) = x` (the zero law, via (D4)). -/
theorem dsub_zero (x : E) : sub x (sub (⊤ : E) ⊤ le_rfl) (dzero_le x) = x := by
  have e : sub (⊤ : E) (sub ⊤ x le_top) (sub_le le_top) = x := sub_sub le_top
  calc sub x (sub (⊤ : E) ⊤ le_rfl) (dzero_le x)
      = sub (sub (⊤ : E) (sub ⊤ x le_top) (sub_le le_top))
          (sub (⊤ : E) ⊤ (le_refl (⊤ : E)))
          (sub_antitone (le_top : sub (⊤ : E) x le_top ≤ ⊤) (le_refl (⊤ : E))) :=
        sub_congr e.symm rfl
    _ = sub (⊤ : E) (sub ⊤ x le_top) le_top :=
        sub_sub_eq (le_top : sub (⊤ : E) x le_top ≤ ⊤) (le_refl (⊤ : E))
    _ = x := e

theorem dzero_perp (x : E) : DPerp (sub (⊤ : E) ⊤ le_rfl) x :=
  dperp_comm ⟨x, dzero_le x, dsub_zero x⟩

theorem dzero_dovee (x : E) (h : DPerp (sub (⊤ : E) ⊤ le_rfl) x) :
    dovee _ x h = x := by
  rw [dovee_comm h]
  exact dovee_eq _ (dzero_le x) (dsub_zero x)

theorem dperp_orth (a : E) : DPerp a (sub (⊤ : E) a le_top) :=
  ⟨⊤, le_top, sub_sub le_top⟩

theorem dovee_orth (a : E) (h : DPerp a (sub (⊤ : E) a le_top)) :
    dovee a _ h = ⊤ :=
  dovee_eq _ le_top (sub_sub le_top)

theorem dorth_unique {a b : E} (h : DPerp a b) (e : dovee a b h = ⊤) :
    b = sub (⊤ : E) a le_top := by
  have hab : sub (⊤ : E) b le_top = a :=
    (sub_congr e rfl).symm.trans (sub_dovee h)
  exact ((sub_congr rfl hab).symm.trans (sub_sub (le_top : b ≤ ⊤))).symm

theorem deq_zero_of_dperp_top {a : E} (h : DPerp a ⊤) :
    a = sub (⊤ : E) ⊤ le_rfl := by
  obtain ⟨c, hc, e⟩ := h
  exact e.symm.trans (sub_congr (le_antisymm le_top hc) rfl)

end DPoset

/-- **176III** (eff.tex:448, Exercise\* continued): the effect algebra
structure carried by a D-poset (`a ⋁ b = c ⇔ c ⊖ b = a`, `0 = 1 ⊖ 1`,
`aᵖ = 1 ⊖ a`). -/
noncomputable def dposetEffectAlgebra (E : Type u) [DPoset E] : EffectAlgebra E where
  zero := DPoset.sub (⊤ : E) ⊤ le_rfl
  one := ⊤
  Perp := DPoset.DPerp
  ovee := DPoset.dovee
  perp_comm := DPoset.dperp_comm
  ovee_comm := DPoset.dovee_comm
  perp_of_ovee_perp := DPoset.dperp_of_dovee_dperp
  perp_ovee_of_ovee_perp := DPoset.dperp_dovee_of_dovee_dperp
  ovee_assoc := DPoset.dovee_assoc
  zero_perp := DPoset.dzero_perp
  zero_ovee := fun a => DPoset.dzero_dovee a _
  orth := fun a => DPoset.sub (⊤ : E) a le_top
  perp_orth := DPoset.dperp_orth
  ovee_orth := fun a => DPoset.dovee_orth a _
  orth_unique := DPoset.dorth_unique
  eq_zero_of_perp_one := DPoset.deq_zero_of_dperp_top

/-- **176III** (eff.tex:448, Exercise\* continued): a D-poset `E` carries an
effect algebra structure (`a ⋁ b = c ⇔ c ⊖ b = a`, `aᵖ = 1 ⊖ a`) whose
order and difference agree with the given ones. -/
theorem exc_dposet_ea (E : Type u) [DPoset E] :
    ∃ ea : EffectAlgebra E,
      (∀ a b : E, @PCM.le E ea.toPCM a b ↔ a ≤ b) ∧
      (∀ a : E, @EffectAlgebra.orth E ea a = DPoset.sub ⊤ a le_top) := by
  refine ⟨dposetEffectAlgebra E, fun a b => ?_, fun _ => rfl⟩
  constructor
  · rintro ⟨c, hc, e⟩
    have hle : a ≤ DPoset.dovee a c hc := DPoset.le_left_dovee hc
    have e' : DPoset.dovee a c hc = b := e
    rwa [e'] at hle
  · intro hab
    exact ⟨DPoset.sub b a hab,
      ⟨b, DPoset.sub_le hab, DPoset.sub_sub hab⟩,
      DPoset.dovee_eq _ (DPoset.sub_le hab) (DPoset.sub_sub hab)⟩

section EAMorphism

variable {E : Type u} {F : Type u} [EffectAlgebra E] [EffectAlgebra F]

/-- **176V.1** (`exc-eamorphism`, eff.tex:465, Exercise): an effect algebra
homomorphism preserves zero: `f 0 = 0`. -/
theorem exc_eamorphism_map_zero (f : EAHom E F) : f.toFun 0 = 0 := by
  have h : Perp (f.toFun 0) (f.toFun 1) := f.perp_map (PCM.zero_perp 1)
  rw [f.map_one] at h
  exact EffectAlgebra.eq_zero_of_perp_one h

/-- **176V.2** (`exc-eamorphism`, eff.tex:465, Exercise): an effect algebra
homomorphism is order preserving. -/
theorem exc_eamorphism_monotone (f : EAHom E F) {a b : E} (h : a ≼ b) :
    f.toFun a ≼ f.toFun b := by
  obtain ⟨c, hac, rfl⟩ := h
  exact ⟨f.toFun c, f.perp_map hac, (f.ovee_map hac).symm⟩

/-- **176V.3** (`exc-eamorphism`, eff.tex:465, Exercise): if `a ⊖ b` is
defined, then `f (a ⊖ b) = f a ⊖ f b`. -/
theorem exc_eamorphism_map_diff (f : EAHom E F) {a b c : E} (h : IsDiff a b c) :
    IsDiff (f.toFun a) (f.toFun b) (f.toFun c) := by
  obtain ⟨hbc, e⟩ := h
  exact ⟨f.perp_map hbc, by rw [← f.ovee_map hbc, e]⟩

/-- **176V.4** (`exc-eamorphism`, eff.tex:465, Exercise): consequently
`f (aᵖ) = (f a)ᵖ`. -/
theorem exc_eamorphism_map_orth (f : EAHom E F) (a : E) :
    f.toFun (orth a) = orth (f.toFun a) := by
  refine EffectAlgebra.orth_unique (f.perp_map (EffectAlgebra.perp_orth a)) ?_
  rw [← f.ovee_map (EffectAlgebra.perp_orth a), EffectAlgebra.ovee_orth, f.map_one]

end EAMorphism

/-! ### Infima and suprema in an effect algebra

Section 2.1.1 of the author's *master's* thesis (Bas Westerbaan, *Quantum
Programs as Kleisli Maps*, `westerbaan.name/~bas/math/master.pdf`) collects the
order-theoretic facts that 177Ia rests on.  We transcribe them here — they are
the `⋁`-versus-`∨` bridge that several later proofs want — with **one
correction**: the master's thesis's Corollary 14 claims that `a ⋁ (·)` and
`a ⊖ (·)` transport infima to suprema *and back*, on the grounds that suprema
and infima taken inside `↓aᵖ` (resp. `↓a`) agree with those taken in `E`.  That
is true for the halves recorded below, but **false** for the remaining two: an
upper bound of a set contained in `↓a` need not itself lie below `a`, so a
supremum computed inside `↓a` need not be a supremum in `E`.  The
counterexample is `WrightTriangle` below; it is also what refutes 177Ia as
printed.  (Master's thesis Proposition 13.2, about the dual operation
`a ⊛ b = (aᵖ ⋁ bᵖ)ᵖ`, is omitted: that operation is not part of this
development.) -/

section MscOrder

variable {E : Type u} [EffectAlgebra E]

/-- Helper: `b ⊖ a` being defined witnesses `a ≼ b`. -/
theorem le_of_isDiff {a b u : E} (h : IsDiff a b u) : b ≼ a := ⟨u, h⟩

/-- Helper: `PCM.IsInf` is symmetric. -/
theorem isInf_comm {a b m : E} (h : PCM.IsInf a b m) : PCM.IsInf b a m :=
  ⟨h.2.1, h.1, fun c h1 h2 => h.2.2 c h2 h1⟩

/-- Helper: `PCM.IsSup` is symmetric. -/
theorem isSup_comm {a b j : E} (h : PCM.IsSup a b j) : PCM.IsSup b a j :=
  ⟨h.2.1, h.1, fun c h1 h2 => h.2.2 c h2 h1⟩

/-- Helper: infima are unique (by antisymmetry of `≼`, 175V.5). -/
theorem isInf_unique {a b m m' : E} (h : PCM.IsInf a b m) (h' : PCM.IsInf a b m') :
    m = m' :=
  eabasics_le_antisymm (h'.2.2 m h.1 h.2.1) (h.2.2 m' h'.1 h'.2.1)

/-- Helper: suprema are unique (by antisymmetry of `≼`, 175V.5). -/
theorem isSup_unique {a b j j' : E} (h : PCM.IsSup a b j) (h' : PCM.IsSup a b j') :
    j = j' :=
  eabasics_le_antisymm (h.2.2 j' h'.1 h'.2.1) (h'.2.2 j h.1 h.2.1)

/-- **Master's thesis, Proposition 13.1**: `x ↦ a ⋁ x` is an order isomorphism
from `↓aᵖ` onto `↑a`.  Here: it is an order *embedding* (surjectivity onto `↑a`
is the definition of `≼`, and the inverse is `x ↦ x ⊖ a`). -/
theorem msc_prop13_1 {a b c : E} (hb : Perp a b) (hc : Perp a c) :
    ovee a b hb ≼ ovee a c hc ↔ b ≼ c := by
  constructor
  · rintro ⟨t, ht, e⟩
    have hbt : Perp b t := PCM.perp_of_ovee_perp hb ht
    have hA : Perp a (ovee b t hbt) := PCM.perp_ovee_of_ovee_perp hb ht
    have e2 : ovee a (ovee b t hbt) hA = ovee a c hc := by
      rw [← PCM.ovee_assoc hb ht]; exact e
    have e3 : ovee (ovee b t hbt) a (PCM.perp_comm hA) = ovee c a (PCM.perp_comm hc) := by
      rw [← PCM.ovee_comm hA, ← PCM.ovee_comm hc]; exact e2
    exact ⟨t, hbt, eabasics_cancellation (PCM.perp_comm hA) (PCM.perp_comm hc) e3⟩
  · intro h
    obtain ⟨hba, hle⟩ := eabasics_le_perp_compat h (PCM.perp_comm hc)
    rw [PCM.ovee_comm hb, PCM.ovee_comm hc]
    exact hle

/-- **Master's thesis, Proposition 13.3**: `x ↦ a ⊖ x` is order *reversing* on
`↓a` (the antitone half of the anti-isomorphism). -/
theorem msc_sub_antitone {a b c u v : E} (hu : IsDiff a b u) (hv : IsDiff a c v)
    (h : b ≼ c) : v ≼ u :=
  (exc_dposet_D4 h (le_of_isDiff hv) hv hu).1

/-- **Master's thesis, Proposition 13.3**: `x ↦ a ⊖ x` is an order
anti-isomorphism of `↓a` onto itself; being its own inverse (176II (D3),
`exc_dposet_D3`), it *reflects* the order as well: for `b, c ≼ a` with
`a ⊖ b = u` and `a ⊖ c = v` one has `b ≼ c ↔ v ≼ u`. -/
theorem msc_prop13_3 {a b c u v : E} (hu : IsDiff a b u) (hv : IsDiff a c v) :
    b ≼ c ↔ v ≼ u :=
  ⟨msc_sub_antitone hu hv,
   fun h => msc_sub_antitone (exc_dposet_D3 hv) (exc_dposet_D3 hu) h⟩

/-- **Master's thesis, Corollary 14.1** (supremum half): `a ⋁ (·)` carries a
supremum of `b, c ≼ aᵖ` to a supremum of `a ⋁ b` and `a ⋁ c`.  (Sound in this
direction: every upper bound of `a ⋁ b`, `a ⋁ c` lies above `a`, hence in the
codomain `↑a` of the isomorphism.) -/
theorem msc_cor14_1_sup {a b c j : E} (hb : Perp a b) (hc : Perp a c)
    (hj : PCM.IsSup b c j) :
    ∃ haj : Perp a j, PCM.IsSup (ovee a b hb) (ovee a c hc) (ovee a j haj) := by
  have haj : Perp a j :=
    PCM.perp_comm (eabasics_perp_iff_le_orth.mpr
      (hj.2.2 _ (eabasics_perp_iff_le_orth.mp (PCM.perp_comm hb))
        (eabasics_perp_iff_le_orth.mp (PCM.perp_comm hc))))
  refine ⟨haj, (msc_prop13_1 hb haj).mpr hj.1, (msc_prop13_1 hc haj).mpr hj.2.1, ?_⟩
  rintro d hbd hcd
  obtain ⟨e, hae, rfl⟩ : ∃ e, ∃ h : Perp a e, ovee a e h = d :=
    pcm_preorder_trans ⟨b, hb, rfl⟩ hbd
  exact (msc_prop13_1 haj hae).mpr
    (hj.2.2 e ((msc_prop13_1 hb hae).mp hbd) ((msc_prop13_1 hc hae).mp hcd))

/-- **Master's thesis, Corollary 14.1** (infimum half): an infimum of `a ⋁ b`
and `a ⋁ c` of the form `a ⋁ m` comes from an infimum `m` of `b` and `c`.
(Sound in this direction: every lower bound of `a ⋁ b`, `a ⋁ c` that matters is
of the form `a ⋁ d`.  The *converse* — that an infimum of `b, c` yields one of
`a ⋁ b`, `a ⋁ c` — is the direction the master's thesis's proof does not
establish, since a lower bound of `a ⋁ b` and `a ⋁ c` need not be above `a`.) -/
theorem msc_cor14_1_inf {a b c m : E} (hb : Perp a b) (hc : Perp a c)
    (ham : Perp a m) (hk : PCM.IsInf (ovee a b hb) (ovee a c hc) (ovee a m ham)) :
    PCM.IsInf b c m := by
  refine ⟨(msc_prop13_1 ham hb).mp hk.1, (msc_prop13_1 ham hc).mp hk.2.1, fun d hdb hdc => ?_⟩
  have had : Perp a d :=
    PCM.perp_comm (eabasics_perp_iff_le_orth.mpr
      (pcm_preorder_trans hdb (eabasics_perp_iff_le_orth.mp (PCM.perp_comm hb))))
  exact (msc_prop13_1 had ham).mp
    (hk.2.2 _ ((msc_prop13_1 had hb).mpr hdb) ((msc_prop13_1 had hc).mpr hdc))

/-- **Master's thesis, Corollary 14.2** (infimum half — this one is true as
stated): if `b, c ≼ a` have a supremum `j` in `E`, then `a ⊖ b` and `a ⊖ c`
have the infimum `a ⊖ j` in `E`.  (Sound: every lower bound of `a ⊖ b` and
`a ⊖ c` is automatically `≼ a`.) -/
theorem msc_cor14_2_inf {a b c j u v m : E}
    (hu : IsDiff a b u) (hv : IsDiff a c v) (hj : PCM.IsSup b c j) (hm : IsDiff a j m) :
    PCM.IsInf u v m := by
  refine ⟨msc_sub_antitone hu hm hj.1, msc_sub_antitone hv hm hj.2.1, fun d hdu hdv => ?_⟩
  have hda : d ≼ a := pcm_preorder_trans hdu (exc_dposet_D2 hu)
  obtain ⟨e, he⟩ : ∃ e, IsDiff a d e := hda
  have hbe : b ≼ e := (msc_prop13_3 he (exc_dposet_D3 hu)).mp hdu
  have hce : c ≼ e := (msc_prop13_3 he (exc_dposet_D3 hv)).mp hdv
  exact (msc_prop13_3 hm (exc_dposet_D3 he)).mp (hj.2.2 e hbe hce)

/-- **Master's thesis, Corollary 14.2** (supremum half — *honest* form): if
`b, c ≼ a` have an infimum `m` in `E`, then `a ⊖ m` is the least upper bound of
`a ⊖ b` and `a ⊖ c` **among the elements below `a`**.  It need *not* be their
least upper bound in `E`: the master's thesis's claim that it is is refuted by
`WrightTriangle.no_sup_a1_a2` below (take `a = a₁ ⋁ a₂`, `b = a₁`, `c = a₂`,
`m = 0`).  This is exactly the gap in the printed proof of 177Ia. -/
theorem msc_cor14_2_sup_below {a b c m u v j : E}
    (hu : IsDiff a b u) (hv : IsDiff a c v) (hm : PCM.IsInf b c m) (hj : IsDiff a m j) :
    u ≼ j ∧ v ≼ j ∧ ∀ d, d ≼ a → u ≼ d → v ≼ d → j ≼ d := by
  refine ⟨msc_sub_antitone hj hu hm.1, msc_sub_antitone hj hv hm.2.1, fun d hda hud hvd => ?_⟩
  obtain ⟨e, he⟩ : ∃ e, IsDiff a d e := hda
  have heb : e ≼ b := (msc_prop13_3 (exc_dposet_D3 hu) he).mp hud
  have hec : e ≼ c := (msc_prop13_3 (exc_dposet_D3 hv) he).mp hvd
  exact (msc_prop13_3 (exc_dposet_D3 he) hj).mp (hm.2.2 e heb hec)

/-- **Master's thesis, Proposition 15**: if `a ⊥ b` and `a ∨ b` exists, then
`a ∧ b` exists and equals `(a ⋁ b) ⊖ (a ∨ b)`. -/
theorem msc_prop15 {a b j m : E} (hab : Perp a b) (hj : PCM.IsSup a b j)
    (hm : IsDiff (ovee a b hab) j m) : PCM.IsInf a b m := by
  have hu : IsDiff (ovee a b hab) a b := ⟨hab, rfl⟩
  have hv : IsDiff (ovee a b hab) b a :=
    ⟨PCM.perp_comm hab, by rw [← PCM.ovee_comm]⟩
  exact isInf_comm (msc_cor14_2_inf hu hv hj hm)

/-- **Master's thesis, Proposition 15**, existence form. -/
theorem msc_prop15' {a b j : E} (hab : Perp a b) (hj : PCM.IsSup a b j) :
    ∃ m, IsDiff (ovee a b hab) j m ∧ PCM.IsInf a b m := by
  have hja : j ≼ ovee a b hab :=
    hj.2.2 _ ⟨b, hab, rfl⟩ ⟨a, PCM.perp_comm hab, by rw [← PCM.ovee_comm]⟩
  obtain ⟨m, hm⟩ := hja
  exact ⟨m, hm, msc_prop15 hab hj hm⟩

/-- **Master's thesis, Corollary 16.2**: whenever both exist,
`(a ∨ b) ⋁ (a ∧ b) = a ⋁ b`.  This is the identity of 177Ia; what 177Ia adds —
that the supremum exists as soon as the infimum does — is false (see
`WrightTriangle.not_ea_modularity_prop`). -/
theorem msc_cor16_2 {a b j m : E} (hab : Perp a b) (hm : PCM.IsInf a b m)
    (hj : PCM.IsSup a b j) : ∃ hmj : Perp m j, ovee m j hmj = ovee a b hab := by
  obtain ⟨m', hdiff, hm'⟩ := msc_prop15' hab hj
  obtain rfl : m = m' := isInf_unique hm hm'
  obtain ⟨hp, he⟩ := hdiff
  exact ⟨PCM.perp_comm hp, by rw [← PCM.ovee_comm]; exact he⟩

/-- **Master's thesis, Corollary 16.1**, honest form: if `a ⊥ b`, `a ∧ b = 0`
and `a ∨ b` exists, then `a ∨ b = a ⋁ b` — the `⋁`-versus-`∨` bridge.  (That
`a ∨ b` *exists* under the first two hypotheses is the false part; in
`WrightTriangle`, `a₁ ⊥ a₂` and `a₁ ∧ a₂ = 0` while `a₁ ∨ a₂` does not
exist.) -/
theorem msc_cor16_1 {a b j : E} (hab : Perp a b) (hm : PCM.IsInf a b 0)
    (hj : PCM.IsSup a b j) : j = ovee a b hab := by
  obtain ⟨hmj, he⟩ := msc_cor16_2 hab hm hj
  rw [← he, PCM.ovee_comm, PCM.ovee_zero]

end MscOrder

/-! ### A counterexample: the Wright triangle

The Greechie diagram with three three-atom blocks pasted in a loop of order
three — `B₁ = {a₁, a₄, a₂}`, `B₂ = {a₂, a₅, a₃}`, `B₃ = {a₃, a₆, a₁}`, each
block a copy of `2³` and `cᵢ = aᵢᵖ` — is an effect algebra (indeed an
orthoalgebra) that is not an orthomodular poset.  All fourteen elements and the
whole partial addition are given explicitly below, and every effect algebra
axiom is checked by `decide`.

Since `a₁ ⊥ a₂` while `c₃ = a₃ᵖ = a₂ ⋁ a₅ = a₆ ⋁ a₁` and `c₄ = a₄ᵖ = a₁ ⋁ a₂`
are *two incomparable* upper bounds of `{a₁, a₂}`, the pair `a₁, a₂` has an
infimum (namely `0`) but **no** supremum.  That refutes 177Ia and the lemma its
proof rests on. -/

namespace WrightTriangle

/-- The fourteen elements of the Wright triangle: `0`, the six atoms `aᵢ`,
their orthocomplements `cᵢ = aᵢᵖ`, and `1`. -/
inductive W where
  | zero | a1 | a2 | a3 | a4 | a5 | a6 | c1 | c2 | c3 | c4 | c5 | c6 | one
  deriving DecidableEq

open W

instance : Fintype W where
  elems := ⟨[zero, a1, a2, a3, a4, a5, a6, c1, c2, c3, c4, c5, c6, one], by decide⟩
  complete := by intro x; cases x <;> decide

/-- The partial addition, as a table: `0` is neutral, the atoms of a common
block add up to the orthocomplement of the third atom of that block, and
`aᵢ ⋁ cᵢ = 1`.  Blocks: `{a₁,a₄,a₂}`, `{a₂,a₅,a₃}`, `{a₃,a₆,a₁}`. -/
def add : W → W → Option W
  | zero, b => some b
  | a, zero => some a
  | a1, a4 => some c2 | a4, a1 => some c2
  | a1, a2 => some c4 | a2, a1 => some c4
  | a4, a2 => some c1 | a2, a4 => some c1
  | a2, a5 => some c3 | a5, a2 => some c3
  | a2, a3 => some c5 | a3, a2 => some c5
  | a5, a3 => some c2 | a3, a5 => some c2
  | a3, a6 => some c1 | a6, a3 => some c1
  | a3, a1 => some c6 | a1, a3 => some c6
  | a6, a1 => some c3 | a1, a6 => some c3
  | a1, c1 => some one | c1, a1 => some one
  | a2, c2 => some one | c2, a2 => some one
  | a3, c3 => some one | c3, a3 => some one
  | a4, c4 => some one | c4, a4 => some one
  | a5, c5 => some one | c5, a5 => some one
  | a6, c6 => some one | c6, a6 => some one
  | _, _ => none

/-- The orthocomplement. -/
def orthW : W → W
  | zero => one | one => zero
  | a1 => c1 | a2 => c2 | a3 => c3 | a4 => c4 | a5 => c5 | a6 => c6
  | c1 => a1 | c2 => a2 | c3 => a3 | c4 => a4 | c5 => a5 | c6 => a6

instance instPCMW : PCM W where
  zero := W.zero
  Perp a b := (add a b).isSome
  ovee a b h := (add a b).get h
  perp_comm := by decide
  ovee_comm := by decide
  perp_of_ovee_perp := by decide
  perp_ovee_of_ovee_perp := by decide
  ovee_assoc := by decide
  zero_perp := by decide
  zero_ovee := by decide

instance decPerpW (a b : W) : Decidable (Perp a b) :=
  inferInstanceAs (Decidable ((add a b).isSome = true))

theorem perp_orthW : ∀ a : W, Perp a (orthW a) := by decide

theorem ovee_orthW : ∀ a : W, ovee a (orthW a) (perp_orthW a) = W.one := by decide

theorem orth_uniqueW : ∀ {a b : W} (h : Perp a b), ovee a b h = W.one → b = orthW a := by
  decide

theorem zero_oneW : ∀ {a : W}, Perp a W.one → a = W.zero := by decide

instance instEAW : EffectAlgebra W where
  one := W.one
  orth := orthW
  perp_orth := perp_orthW
  ovee_orth := ovee_orthW
  orth_unique := orth_uniqueW
  eq_zero_of_perp_one := zero_oneW

theorem perp_a1_a2 : Perp a1 a2 := by decide

theorem perp_a2_a1 : Perp a2 a1 := by decide

theorem ovee_a2_a1 : ovee a2 a1 perp_a2_a1 = ovee a1 a2 perp_a1_a2 := by decide

/-- `a₁ ∧ a₂ = 0`: the only element below both atoms is `0`. -/
theorem isInf_a1_a2 : PCM.IsInf a1 a2 (0 : W) := by
  unfold PCM.IsInf PCM.le
  decide

/-- `a₁ ∨ a₂` does not exist: `c₃` and `c₄` are incomparable upper bounds. -/
theorem no_sup_a1_a2 : ¬ ∃ j : W, PCM.IsSup a1 a2 j := by
  unfold PCM.IsSup PCM.le
  decide

/-- **177Ia is false as printed** (`ea-modularity-prop`, eff.tex:484): in the
Wright triangle `a₁ ⊥ a₂` and `a₁ ∧ a₂ = 0` exists, yet `a₁ ∨ a₂` does not.
(Every orthoalgebra has `a ∧ b = 0` for `a ⊥ b`, so the Proposition would make
every orthoalgebra an orthomodular poset.) -/
theorem not_ea_modularity_prop :
    ¬ ∀ (E : Type) [EffectAlgebra E] (a b m : E) (hab : Perp a b),
        PCM.IsInf a b m →
          ∃ (j : E) (hmj : Perp m j), PCM.IsSup a b j ∧ ovee a b hab = ovee m j hmj := by
  intro H
  obtain ⟨j, _, hj, _⟩ := H W a1 a2 0 perp_a1_a2 isInf_a1_a2
  exact no_sup_a1_a2 ⟨j, hj⟩

/-- **The lemma of `modularity-lemma-proof` (eff.tex:492) is false too**, even
when strengthened by `c ⊥ d`: with `x = a₁ ⋁ a₂`, `c = a₁`, `d = a₂` one has
`x ⊖ c = a₂`, `x ⊖ d = a₁`, whose infimum is `0`, while `c ∨ d` does not
exist. -/
theorem not_modularity_lemma :
    ¬ ∀ (E : Type) [EffectAlgebra E] (x c d u v m : E), Perp c d →
        IsDiff x c u → IsDiff x d v → PCM.IsInf u v m → ∃ j, PCM.IsSup c d j := by
  intro H
  refine no_sup_a1_a2 (H W (ovee a1 a2 perp_a1_a2) a1 a2 a2 a1 0 perp_a1_a2
    ⟨perp_a1_a2, rfl⟩ ⟨perp_a2_a1, ovee_a2_a1⟩ (isInf_comm isInf_a1_a2))

end WrightTriangle

/-- **177Ia** (`ea-modularity-prop`, eff.tex:484, Proposition), **realigned**:
as printed the Proposition claims that for `a ⊥ b` the existence of `a ∧ b`
already gives `a ∨ b`; that is **false**, see
`WrightTriangle.not_ea_modularity_prop` and the 177Ia row of `ERRATA.md`.  What
survives — and is all that the thesis's own applications use — is the identity
`a ⋁ b = (a ∧ b) ⋁ (a ∨ b)` whenever *both* the infimum and the supremum exist
(master's thesis, Corollary 16.2). -/
theorem ea_modularity_prop {E : Type u} [EffectAlgebra E] {a b m j : E}
    (hab : Perp a b) (hm : PCM.IsInf a b m) (hj : PCM.IsSup a b j) :
    ∃ hmj : Perp m j, ovee a b hab = ovee m j hmj := by
  obtain ⟨hmj, he⟩ := msc_cor16_2 hab hm hj
  exact ⟨hmj, he.symm⟩

/-! ## Orthomodular lattices (parsec 177) -/

/-- **177IV** (`dfn-orthomodular-lattice`, eff.tex:536, Definition): an
**ortholattice** is a bounded lattice with an orthocomplement `(·)ᶜ`
satisfying `a ⊓ aᶜ = ⊥`, `a ⊔ aᶜ = ⊤`, antitonicity and involutivity. -/
class Ortholattice (L : Type u) extends Lattice L, BoundedOrder L, Compl L where
  inf_compl : ∀ a : L, a ⊓ aᶜ = ⊥
  sup_compl : ∀ a : L, a ⊔ aᶜ = ⊤
  compl_antitone : ∀ {a b : L}, a ≤ b → bᶜ ≤ aᶜ
  compl_compl : ∀ a : L, aᶜᶜ = a

/-- **177IV** (`dfn-orthomodular-lattice`, eff.tex:552, Definition): an
ortholattice is **orthomodular** provided `a ≤ b → a ⊔ (aᶜ ⊓ b) = b`. -/
class OrthomodularLattice (L : Type u) extends Ortholattice L where
  orthomodular : ∀ {a b : L}, a ≤ b → a ⊔ (aᶜ ⊓ b) = b

/-- Helper: in an ortholattice `a ≤ bᶜ` implies `b ≤ aᶜ` (the orthogonality
relation is symmetric). -/
theorem Ortholattice.le_compl_comm {L : Type u} [Ortholattice L] {a b : L}
    (h : a ≤ bᶜ) : b ≤ aᶜ := by
  have h' := Ortholattice.compl_antitone h
  rwa [Ortholattice.compl_compl] at h'

/-- Helper: `⊤ᶜ = ⊥` in an ortholattice. -/
theorem Ortholattice.compl_top {L : Type u} [Ortholattice L] : (⊤ : L)ᶜ = ⊥ := by
  have h := Ortholattice.inf_compl (⊤ : L)
  rwa [top_inf_eq] at h

/-- **177V** (eff.tex:559, Example): the lattice of projections of a von
Neumann algebra is an orthomodular lattice with `pᶜ = 1 - p`. -/
theorem projections_orthomodularLattice (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    Nonempty (OrthomodularLattice { p : A // IsStarProjection p }) := sorry

/-- **175II.4** (`eaexamples`, eff.tex:317, Examples): any orthomodular
lattice `L` is an effect algebra with the same orthocomplement, `x ⊥ y` iff
`x ≤ yᶜ`, and `x ⋁ y = x ⊔ y`. -/
def orthomodularEffectAlgebra (L : Type u) [OrthomodularLattice L] :
    EffectAlgebra L where
  zero := ⊥
  one := ⊤
  Perp x y := x ≤ yᶜ
  ovee x y _ := x ⊔ y
  orth x := xᶜ
  perp_comm h := Ortholattice.le_compl_comm h
  ovee_comm := by intro a b _; exact sup_comm a b
  perp_of_ovee_perp := by
    intro a b c _ h
    exact le_sup_right.trans h
  perp_ovee_of_ovee_perp := by
    intro a b c hab h
    have hb : b ≤ aᶜ := Ortholattice.le_compl_comm hab
    have hc : c ≤ aᶜ :=
      (Ortholattice.le_compl_comm h).trans (Ortholattice.compl_antitone le_sup_left)
    exact Ortholattice.le_compl_comm (sup_le hb hc)
  ovee_assoc := by intro a b c _ _; exact sup_assoc a b c
  zero_perp := by intro a; exact bot_le
  zero_ovee := by intro a; exact bot_sup_eq a
  perp_orth := by intro a; exact le_of_eq (Ortholattice.compl_compl a).symm
  ovee_orth := by intro a; exact Ortholattice.sup_compl a
  orth_unique := by
    intro a b h heq
    have heq' : a ⊔ b = (⊤ : L) := heq
    have hb : b ≤ aᶜ := Ortholattice.le_compl_comm h
    have hx : bᶜ ⊓ aᶜ = ⊥ := by
      have h1 : a ≤ (bᶜ ⊓ aᶜ)ᶜ := Ortholattice.le_compl_comm inf_le_right
      have h2 : b ≤ (bᶜ ⊓ aᶜ)ᶜ := Ortholattice.le_compl_comm inf_le_left
      have h3 : (bᶜ ⊓ aᶜ)ᶜ = ⊤ := top_le_iff.mp (heq' ▸ sup_le h1 h2)
      have h4 := congrArg (fun z : L => zᶜ) h3
      simpa [Ortholattice.compl_compl, Ortholattice.compl_top] using h4
    have hom := OrthomodularLattice.orthomodular hb
    rwa [hx, sup_bot_eq] at hom
  eq_zero_of_perp_one := by
    intro a h
    have h' : a ≤ (⊤ : L)ᶜ := h
    rw [Ortholattice.compl_top] at h'
    exact le_bot_iff.mp h'

/-- **177VI** (`orth-ea-is-orthomodular`, eff.tex:564, Proposition): an
effect algebra that is an ortholattice (for its algebraic order, with
orthocomplement as lattice complement) is orthomodular. -/
theorem orth_ea_is_orthomodular (E : Type u) [EffectAlgebra E] [Ortholattice E]
    (hle : ∀ a b : E, a ≤ b ↔ a ≼ b)
    (hcompl : ∀ a : E, aᶜ = orth a) :
    ∀ {a b : E}, a ≤ b → a ⊔ (aᶜ ⊓ b) = b := by
  -- the two orders agree, hence so do the two bottoms and tops
  have hbot : (⊥ : E) = 0 := by
    obtain ⟨c, hc, he⟩ := (hle ⊥ 0).mp bot_le
    exact (eabasics_positivity hc he).1
  have htop : (⊤ : E) = 1 := by
    have h1 : orth (⊤ : E) ≼ orth 1 :=
      eabasics_le_iff_orth_le.mp ((hle 1 ⊤).mp le_top)
    rw [eabasics_orth_one] at h1
    obtain ⟨c, hc, he⟩ := h1
    have h2 := congrArg orth (eabasics_positivity hc he).1
    rwa [eabasics_orth_orth, eabasics_orth_zero] at h2
  -- de Morgan, from antitonicity and involutivity of the orthocomplement
  have hdm : ∀ y z : E, orth (y ⊔ z) = orth y ⊓ orth z := by
    intro y z
    simp only [← hcompl]
    refine le_antisymm (le_inf (Ortholattice.compl_antitone le_sup_left)
      (Ortholattice.compl_antitone le_sup_right)) ?_
    have h1 : y ≤ (yᶜ ⊓ zᶜ)ᶜ := by
      have h := Ortholattice.compl_antitone (inf_le_left : yᶜ ⊓ zᶜ ≤ yᶜ)
      rwa [Ortholattice.compl_compl] at h
    have h2 : z ≤ (yᶜ ⊓ zᶜ)ᶜ := by
      have h := Ortholattice.compl_antitone (inf_le_right : yᶜ ⊓ zᶜ ≤ zᶜ)
      rwa [Ortholattice.compl_compl] at h
    have h3 := Ortholattice.compl_antitone (sup_le h1 h2)
    rwa [Ortholattice.compl_compl] at h3
  -- the key step: for orthogonal `p, q` with `p ∧ q = 0` the partial sum
  -- `p ⋁ q` is the supremum `p ∨ q` (this is `ea-modularity-prop` for
  -- `x = p ⋁ q`; the upper bound `p ∨ q` of `p, q` is automatically below
  -- `x`, which is what makes the argument of eff.tex:500 go through)
  have key : ∀ (p q : E) (h : Perp p q), p ⊓ q = ⊥ → ovee p q h = p ⊔ q := by
    intro p q h hpq
    obtain ⟨x, hx⟩ : ∃ x : E, ovee p q h = x := ⟨_, rfl⟩
    rw [hx]
    have hqp : Perp q p := PCM.perp_comm h
    have hxqp : ovee q p hqp = x := (PCM.ovee_comm h).symm.trans hx
    have hoxx : Perp (orth x) x := PCM.perp_comm (EffectAlgebra.perp_orth x)
    have hoxx1 : ovee (orth x) x hoxx = 1 :=
      (PCM.ovee_comm (EffectAlgebra.perp_orth x)).symm.trans
        (EffectAlgebra.ovee_orth x)
    -- `p = (xᵖ ⋁ q)ᵖ` and `q = (xᵖ ⋁ p)ᵖ`
    have hox_qp : Perp (orth x) (ovee q p hqp) := by rw [hxqp]; exact hoxx
    obtain ⟨hoxq, hu, heu⟩ := PCM.assoc_left hqp hox_qp
    have hup : p = orth (ovee (orth x) q hoxq) :=
      EffectAlgebra.orth_unique hu (by
        rw [heu, PCM.ovee_congr rfl hxqp hox_qp hoxx]; exact hoxx1)
    have hox_pq : Perp (orth x) (ovee p q h) := by rw [hx]; exact hoxx
    obtain ⟨hoxp, hv, hev⟩ := PCM.assoc_left h hox_pq
    have hvq : q = orth (ovee (orth x) p hoxp) :=
      EffectAlgebra.orth_unique hv (by
        rw [hev, PCM.ovee_congr rfl hx hox_pq hoxx]; exact hoxx1)
    -- hence `(xᵖ ⋁ q) ∨ (xᵖ ⋁ p) = 1`, since its orthocomplement is `p ∧ q`
    have h7 : ovee (orth x) q hoxq ⊔ ovee (orth x) p hoxp = 1 := by
      have h6 : orth (ovee (orth x) q hoxq ⊔ ovee (orth x) p hoxp) = 0 := by
        rw [hdm, ← hup, ← hvq, hpq, hbot]
      have h6' := congrArg orth h6
      rwa [eabasics_orth_orth, eabasics_orth_zero] at h6'
    -- `p ∨ q ≤ x`, so `xᵖ ⋁ (p ∨ q)` is defined and dominates both terms
    have hpx : p ≼ x := ⟨q, h, hx⟩
    have hqx : q ≼ x := ⟨p, hqp, hxqp⟩
    have hsx : (p ⊔ q) ≼ x :=
      (hle _ _).mp (sup_le ((hle _ _).mpr hpx) ((hle _ _).mpr hqx))
    have hsox : Perp (p ⊔ q) (orth x) :=
      eabasics_perp_iff_le_orth.mpr (by rwa [eabasics_orth_orth])
    have hoxs : Perp (orth x) (p ⊔ q) := PCM.perp_comm hsox
    have e2 : ovee (p ⊔ q) (orth x) hsox = ovee (orth x) (p ⊔ q) hoxs :=
      PCM.ovee_comm hsox
    obtain ⟨hqox, hmq⟩ :=
      eabasics_le_perp_compat ((hle q (p ⊔ q)).mp le_sup_right) hsox
    obtain ⟨hpox, hmp⟩ :=
      eabasics_le_perp_compat ((hle p (p ⊔ q)).mp le_sup_left) hsox
    have e1 : ovee q (orth x) hqox = ovee (orth x) q hoxq := PCM.ovee_comm hqox
    have e3 : ovee p (orth x) hpox = ovee (orth x) p hoxp := PCM.ovee_comm hpox
    rw [e1, e2] at hmq
    rw [e3, e2] at hmp
    -- so `xᵖ ⋁ (p ∨ q) = 1`, whence `p ∨ q = x`
    have hw1 : ovee (orth x) (p ⊔ q) hoxs = 1 := by
      refine le_antisymm ?_ ?_
      · rw [← htop]; exact le_top
      · rw [← h7]; exact sup_le ((hle _ _).mpr hmq) ((hle _ _).mpr hmp)
    have hfin := EffectAlgebra.orth_unique hoxs hw1
    rw [eabasics_orth_orth] at hfin
    exact hfin.symm
  -- the proposition itself
  intro a b hab
  have hc_le_orth : (aᶜ ⊓ b) ≼ orth a := by
    have h : aᶜ ⊓ b ≤ orth a := by rw [← hcompl a]; exact inf_le_left
    exact (hle _ _).mp h
  have hac : Perp a (aᶜ ⊓ b) :=
    PCM.perp_comm (eabasics_perp_iff_le_orth.mpr hc_le_orth)
  have hinf : a ⊓ (aᶜ ⊓ b) = ⊥ :=
    le_antisymm ((inf_le_inf_left a inf_le_left).trans
      (le_of_eq (Ortholattice.inf_compl a))) bot_le
  have hsup := key a (aᶜ ⊓ b) hac hinf
  -- `b ⊖ a` is below `aᵖ ∧ b`, so `b ≤ a ⋁ (aᵖ ∧ b) = a ∨ (aᵖ ∧ b) ≤ b`
  obtain ⟨d, had, hd⟩ := (hle a b).mp hab
  have hd_le_ac : d ≤ aᶜ := by rw [hcompl]; exact (hle _ _).mpr (perp_le_orth had)
  have hd_le_b : d ≤ b :=
    (hle _ _).mpr ⟨a, PCM.perp_comm had, (PCM.ovee_comm had).symm.trans hd⟩
  have hle1 : b ≤ a ⊔ (aᶜ ⊓ b) := by
    rw [← hsup]
    obtain ⟨hdA, hmono⟩ :=
      eabasics_le_perp_compat ((hle _ _).mp (le_inf hd_le_ac hd_le_b))
        (PCM.perp_comm hac)
    rw [show ovee d a hdA = b from (PCM.ovee_comm had).symm.trans hd,
      show ovee (aᶜ ⊓ b) a (PCM.perp_comm hac) = ovee a (aᶜ ⊓ b) hac from
        (PCM.ovee_comm hac).symm] at hmono
    exact (hle _ _).mpr hmono
  exact le_antisymm (sup_le hab inf_le_right) hle1

/-! ## Effect monoids (parsec 178) -/

/-- **178II** (`dfn-effect-monoid`, eff.tex:599, Definition): an **effect
monoid** is an effect algebra `M` with a (total) binary operation `⊙`
(written `*`) such that for all `a, b, c, d ∈ M`:

1. *(unit)* `1 ⊙ a = a ⊙ 1 = a`;
2. *(associativity)* `(a ⊙ b) ⊙ c = a ⊙ (b ⊙ c)`; and
3. *(distributivity)* if `a ⊥ b` and `c ⊥ d`, then the sum
   `(a ⊙ c) ⋁ (b ⊙ c) ⋁ (a ⊙ d) ⋁ (b ⊙ d)` exists and equals
   `(a ⋁ b) ⊙ (c ⋁ d)` (stated via `PCM.IsSumOf`). -/
class EffectMonoid (M : Type u) extends EffectAlgebra M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a
  mul_assoc : ∀ a b c : M, a * b * c = a * (b * c)
  distrib : ∀ {a b c d : M} (hab : Perp a b) (hcd : Perp c d),
    PCM.IsSumOf [a * c, b * c, a * d, b * d] (ovee a b hab * ovee c d hcd)

/-- **178II** (`dfn-effect-monoid`, eff.tex:623, Definition): an effect
monoid is **commutative** if `a ⊙ b = b ⊙ a` for all `a, b`. -/
def EffectMonoid.Commutative (M : Type u) [EffectMonoid M] : Prop :=
  ∀ a b : M, a * b = b * a

/-- **178II** (`dfn-effect-monoid`, eff.tex:626, Definition): an **effect
monoid homomorphism** is an effect algebra homomorphism that moreover
preserves `⊙`. -/
structure EffectMonoidHom (M : Type u) (N : Type v)
    [EffectMonoid M] [EffectMonoid N] extends EAHom M N where
  map_mul : ∀ a b : M, toFun (a * b) = toFun a * toFun b

/-- **178III.2** (`eff-monoid-examples`, eff.tex:640, Examples): every
Boolean algebra is an effect monoid with `x ⊙ y = x ⊓ y`. -/
def booleanEffectMonoid (L : Type u) [BooleanAlgebra L] : EffectMonoid L :=
  { booleanEffectAlgebra L with
    mul := (· ⊓ ·)
    one_mul := by intro a; exact top_inf_eq a
    mul_one := by intro a; exact inf_top_eq a
    mul_assoc := by intro a b c; exact inf_assoc a b c
    distrib := by
      let _ : EffectAlgebra L := booleanEffectAlgebra L
      intro a b c d hab hcd
      have hab' : a ⊓ b = ⊥ := hab
      have hcd' : c ⊓ d = ⊥ := hcd
      have hba' : b ⊓ a = ⊥ := by rw [inf_comm]; exact hab'
      have hdc' : d ⊓ c = ⊥ := by rw [inf_comm]; exact hcd'
      have sub_bot : ∀ {x y p q : L}, p ≤ x → q ≤ y → x ⊓ y = ⊥ → p ⊓ q = ⊥ :=
        fun hp hq h => le_bot_iff.mp (h ▸ inf_le_inf hp hq)
      have e1 : (a ⊓ d) ⊓ (b ⊓ d) = ⊥ := sub_bot inf_le_left inf_le_left hab'
      have e2 : (b ⊓ c) ⊓ (a ⊓ d) = ⊥ := sub_bot inf_le_left inf_le_left hba'
      have e3 : (b ⊓ c) ⊓ (b ⊓ d) = ⊥ := sub_bot inf_le_right inf_le_right hcd'
      have e4 : (a ⊓ c) ⊓ (b ⊓ c) = ⊥ := sub_bot inf_le_left inf_le_left hab'
      have e5 : (a ⊓ c) ⊓ (a ⊓ d) = ⊥ := sub_bot inf_le_right inf_le_right hcd'
      have e6 : (a ⊓ c) ⊓ (b ⊓ d) = ⊥ := sub_bot inf_le_left inf_le_left hab'
      refine PCM.isSumOf_cons_iff.mpr
        ⟨(b ⊓ c) ⊔ ((a ⊓ d) ⊔ (b ⊓ d)), ?_, ?_, ?_⟩
      · refine PCM.isSumOf_cons_iff.mpr ⟨(a ⊓ d) ⊔ (b ⊓ d), ?_, ?_, rfl⟩
        · refine PCM.isSumOf_cons_iff.mpr ⟨b ⊓ d, ?_, ?_, rfl⟩
          · exact PCM.isSumOf_cons_iff.mpr
              ⟨0, PCM.IsSumOf.nil, PCM.perp_zero _, PCM.ovee_zero _ _⟩
          · show (a ⊓ d) ⊓ (b ⊓ d) = ⊥
            exact e1
        · show (b ⊓ c) ⊓ ((a ⊓ d) ⊔ (b ⊓ d)) = ⊥
          simp only [inf_sup_left, e2, e3, sup_bot_eq]
      · show (a ⊓ c) ⊓ ((b ⊓ c) ⊔ ((a ⊓ d) ⊔ (b ⊓ d))) = ⊥
        simp only [inf_sup_left, e4, e5, e6, sup_bot_eq]
      · show (a ⊓ c) ⊔ ((b ⊓ c) ⊔ ((a ⊓ d) ⊔ (b ⊓ d))) = (a ⊔ b) ⊓ (c ⊔ d)
        rw [inf_sup_right, inf_sup_left, inf_sup_left]
        simp only [sup_assoc, sup_left_comm] }

/-- **178III.3** (`eff-monoid-examples`, eff.tex:646, Examples): the
two-element Boolean algebra `2` is an effect monoid with
`x ⊙ y = x ∧ y`. -/
instance : EffectMonoid Bool := booleanEffectMonoid Bool

/-- **178III.1** (`eff-monoid-examples`, eff.tex:636, Examples): `[0,1]` is
a commutative effect monoid with the usual product. -/
noncomputable instance unitInterval.effectMonoid : EffectMonoid I :=
  { unitInterval.effectAlgebra with
    mul := (· * ·)
    one_mul := by intro a; exact _root_.one_mul a
    mul_one := by intro a; exact _root_.mul_one a
    mul_assoc := by intro a b c; exact _root_.mul_assoc a b c
    distrib := by
      intro a b c d hab hcd
      have hab' : (a : ℝ) + b ≤ 1 := hab
      have hcd' : (c : ℝ) + d ≤ 1 := hcd
      obtain ⟨ha0, ha1⟩ := a.2
      obtain ⟨hb0, hb1⟩ := b.2
      obtain ⟨hc0, hc1⟩ := c.2
      obtain ⟨hd0, hd1⟩ := d.2
      have m1 : (0 : ℝ) ≤ (a : ℝ) * c := mul_nonneg ha0 hc0
      have m2 : (0 : ℝ) ≤ (b : ℝ) * c := mul_nonneg hb0 hc0
      have m3 : (0 : ℝ) ≤ (a : ℝ) * d := mul_nonneg ha0 hd0
      have m4 : (0 : ℝ) ≤ (b : ℝ) * d := mul_nonneg hb0 hd0
      have hprod : ((a : ℝ) + b) * ((c : ℝ) + d) ≤ 1 := by nlinarith
      have hP : ∀ x y : I, (x : ℝ) + (y : ℝ) ≤ 1 → Perp x y := fun _ _ h => h
      have hO : ∀ (x y : I) (h : Perp x y),
          ((ovee x y h : I) : ℝ) = (x : ℝ) + (y : ℝ) := fun _ _ _ => rfl
      refine PCM.isSumOf_cons_iff.mpr
        ⟨⟨(b : ℝ) * c + ((a : ℝ) * d + (b : ℝ) * d), by nlinarith, by nlinarith⟩,
          ?_, hP _ _ ?_, ?_⟩
      · refine PCM.isSumOf_cons_iff.mpr
          ⟨⟨(a : ℝ) * d + (b : ℝ) * d, by nlinarith, by nlinarith⟩, ?_, hP _ _ ?_, ?_⟩
        · refine PCM.isSumOf_cons_iff.mpr ⟨b * d, ?_, hP _ _ ?_, ?_⟩
          · exact PCM.isSumOf_cons_iff.mpr
              ⟨0, PCM.IsSumOf.nil, PCM.perp_zero _, PCM.ovee_zero _ _⟩
          · show ((a * d : I) : ℝ) + ((b * d : I) : ℝ) ≤ 1
            simp only [Set.Icc.coe_mul]
            nlinarith
          · apply Subtype.ext
            simp only [hO, Set.Icc.coe_mul]
        · show ((b * c : I) : ℝ) + ((a : ℝ) * d + (b : ℝ) * d) ≤ 1
          simp only [Set.Icc.coe_mul]
          nlinarith
        · apply Subtype.ext
          simp only [hO, Set.Icc.coe_mul]
      · show ((a * c : I) : ℝ) + ((b : ℝ) * c + ((a : ℝ) * d + (b : ℝ) * d)) ≤ 1
        simp only [Set.Icc.coe_mul]
        nlinarith
      · apply Subtype.ext
        simp only [hO, Set.Icc.coe_mul]
        ring }

/- **178III.1** (`eff-monoid-examples`, eff.tex:636, Examples), uniqueness:
`unitInterval_effectMonoid_unique` belongs here, but its proof needs
`exc_emonzero` (178IIIa) and hence is stated below, after that exercise. -/

/-- **178III.2** (`eff-monoid-examples`, eff.tex:640, Examples): every finite
effect monoid comes from a Boolean algebra as in `booleanEffectMonoid` — and
is in particular commutative. -/
theorem finite_effectMonoid_boolean (M : Type u) [em : EffectMonoid M] [Finite M] :
    ∃ ba : BooleanAlgebra M, @booleanEffectMonoid M ba = em := sorry

/-- **178III.2** (`eff-monoid-examples`, eff.tex:640, Examples), corollary:
every finite effect monoid is commutative. -/
theorem finite_effectMonoid_commutative (M : Type u) [EffectMonoid M] [Finite M] :
    EffectMonoid.Commutative M := sorry

/-- **178III.4** (`eff-monoid-examples`, eff.tex:651, Examples): there is a
non-commutative effect monoid (one exists on the lexicographically ordered
vector space `ℝ⁵`). -/
theorem exists_noncommutative_effectMonoid :
    ∃ (M : Type) (_ : EffectMonoid M), ¬ EffectMonoid.Commutative M := sorry

/-- **178IIIa** (`exc-emonzero`, eff.tex:661, Exercise): `a ⊙ 0 = 0 = 0 ⊙ a`
in any effect monoid.  (The thesis's "`a ⊙ 0 = a = 0 ⊙ a`" is a typo for
"`= 0 =`".) -/
theorem exc_emonzero {M : Type u} [EffectMonoid M] (a : M) :
    a * 0 = 0 ∧ (0 : M) * a = 0 := by
  -- `(x ⋁ 0) ⊙ (0 ⋁ 0) = x ⊙ 0` expands to `(x⊙0) ⋁ (0⊙0) ⋁ (x⊙0) ⋁ (0⊙0)`;
  -- cancelling the leading `x⊙0` and using positivity gives `x ⊙ 0 = 0`.
  have hmul0 : ∀ x : M, x * 0 = 0 := by
    intro x
    have hd := EffectMonoid.distrib (PCM.perp_zero x) (PCM.zero_perp (0 : M))
    rw [PCM.ovee_zero x (PCM.perp_zero x), PCM.zero_ovee (0 : M)] at hd
    rw [PCM.isSumOf_cons_iff] at hd
    obtain ⟨t, ht, hp, he⟩ := hd
    have ht0 : t = 0 := by
      refine eabasics_cancellation (c := x * 0) (PCM.perp_comm hp) (PCM.zero_perp _) ?_
      rw [← PCM.ovee_comm hp, he, PCM.zero_ovee']
    subst ht0
    rw [PCM.isSumOf_cons_iff] at ht
    obtain ⟨t2, ht2, hp2, he2⟩ := ht
    have h2 := eabasics_positivity hp2 he2
    rw [PCM.isSumOf_cons_iff] at ht2
    obtain ⟨t3, ht3, hp3, he3⟩ := ht2
    exact (eabasics_positivity hp3 (he3.trans h2.2)).1
  refine ⟨hmul0 a, ?_⟩
  -- `(0 ⋁ 0) ⊙ (0 ⋁ a) = 0 ⊙ a` expands to `(0⊙0) ⋁ (0⊙0) ⋁ (0⊙a) ⋁ (0⊙a)`.
  have hd := EffectMonoid.distrib (PCM.zero_perp (0 : M)) (PCM.zero_perp a)
  rw [PCM.zero_ovee (0 : M), PCM.zero_ovee a, hmul0 0] at hd
  rw [PCM.isSumOf_cons_iff] at hd
  obtain ⟨t1, ht1, hp1, he1⟩ := hd
  rw [PCM.zero_ovee' t1 hp1] at he1
  subst he1
  rw [PCM.isSumOf_cons_iff] at ht1
  obtain ⟨t2, ht2, hp2, he2⟩ := ht1
  rw [PCM.zero_ovee' t2 hp2] at he2
  subst he2
  rw [PCM.isSumOf_cons_iff] at ht2
  obtain ⟨t3, ht3, hp3, he3⟩ := ht2
  have ht30 : t3 = 0 := by
    refine eabasics_cancellation (c := (0 : M) * a) (PCM.perp_comm hp3)
      (PCM.zero_perp _) ?_
    rw [← PCM.ovee_comm hp3, he3, PCM.zero_ovee']
  subst ht30
  rw [PCM.isSumOf_cons_iff] at ht3
  obtain ⟨t4, ht4, hp4, he4⟩ := ht3
  exact (eabasics_positivity hp4 he4).1

/-- Helper (one-sided distributivity): in an effect monoid `c ⊥ d` implies
`a ⊙ c ⊥ a ⊙ d` and `(a ⊙ c) ⋁ (a ⊙ d) = a ⊙ (c ⋁ d)`.  This is *not* an
axiom — 178II only gives the four-fold law — but it follows from it once
`0 ⊙ x = 0` is known (178IIIa), by instantiating at `(a ⋁ 0) ⊙ (c ⋁ d)`.
(The `exc-emonzero` solution in `bsols.tex` uses one-sided distributivity to
*prove* `a ⊙ 0 = 0`, which is circular; see PROVING-LOG.) -/
theorem emon_mul_ovee {M : Type u} [EffectMonoid M] (a : M) {c d : M}
    (hcd : Perp c d) :
    ∃ h : Perp (a * c) (a * d), a * ovee c d hcd = ovee (a * c) (a * d) h := by
  have hd := EffectMonoid.distrib (PCM.perp_zero a) hcd
  rw [PCM.ovee_zero a (PCM.perp_zero a), (exc_emonzero c).2, (exc_emonzero d).2] at hd
  -- `hd : IsSumOf [a⊙c, 0, a⊙d, 0] (a ⊙ (c ⋁ d))`; peel the four summands off
  rw [PCM.isSumOf_cons_iff] at hd
  obtain ⟨t1, ht1, hp1, he1⟩ := hd
  rw [PCM.isSumOf_cons_iff] at ht1
  obtain ⟨t2, ht2, hp2, he2⟩ := ht1
  rw [PCM.isSumOf_cons_iff] at ht2
  obtain ⟨t3, ht3, hp3, he3⟩ := ht2
  rw [PCM.isSumOf_cons_iff] at ht3
  obtain ⟨t4, ht4, hp4, he4⟩ := ht3
  rw [PCM.isSumOf_nil_iff] at ht4
  subst ht4
  rw [PCM.zero_ovee] at he4
  subst he4
  rw [PCM.ovee_zero _ hp3] at he3
  subst he3
  rw [PCM.zero_ovee] at he2
  subst he2
  exact ⟨hp1, he1.symm⟩

/-- Helper for 178III.1 (Cauchy's functional equation on `[0,1]`): a map
`m : [0,1] × [0,1] → ℝ` that is nonnegative, satisfies `m x 1 = x` and is
additive in its second argument on defined sums is the product.

The proof is the standard one: additivity plus nonnegativity make `y ↦ m x y`
monotone, an induction gives `m x (n·y) = n · m x y`, hence `m x (k/n) =
x · k/n`, and monotonicity squeezes an arbitrary `y` between `⌊ny⌋/n` and `y`.
Only the *lower* bound `x·y - 1/n ≤ m x y` is proved by squeezing; the upper
bound comes for free from `m x y + m x (1-y) = m x 1 = x`. -/
private theorem unitInterval_cauchy (m : I → I → ℝ)
    (hnn : ∀ x y : I, 0 ≤ m x y)
    (hone : ∀ x : I, m x 1 = (x : ℝ))
    (hadd : ∀ (x y z w : I), (y : ℝ) + (z : ℝ) = (w : ℝ) → m x w = m x y + m x z) :
    ∀ x y : I, m x y = (x : ℝ) * (y : ℝ) := by
  intro a b
  -- additivity + nonnegativity ⟹ monotone
  have hmono : ∀ x y : I, (x : ℝ) ≤ (y : ℝ) → m a x ≤ m a y := by
    intro x y hxy
    have hd0 : (0 : ℝ) ≤ (y : ℝ) - (x : ℝ) := by linarith
    have hd1 : (y : ℝ) - (x : ℝ) ≤ 1 := by linarith [x.2.1, y.2.2]
    have := hadd a x ⟨(y : ℝ) - (x : ℝ), hd0, hd1⟩ y (by simp)
    have h2 := hnn a ⟨(y : ℝ) - (x : ℝ), hd0, hd1⟩
    linarith
  -- `n`-fold sums: `m a (n·x) = n · m a x`
  have hnat : ∀ (n : ℕ) (x w : I), (n : ℝ) * (x : ℝ) = (w : ℝ) → m a w = n * m a x := by
    intro n
    induction n with
    | zero =>
      intro x w hw
      have hw0 : (w : ℝ) = 0 := by simpa using hw.symm
      have : w = (0 : I) := Subtype.ext (by simpa using hw0)
      subst this
      have := hadd a 0 0 0 (by norm_num)
      push_cast
      linarith
    | succ n ih =>
      intro x w hw
      have hx0 : (0 : ℝ) ≤ (x : ℝ) := x.2.1
      have hu0 : (0 : ℝ) ≤ (n : ℝ) * (x : ℝ) := by positivity
      have hu1 : (n : ℝ) * (x : ℝ) ≤ 1 := by
        have : (n : ℝ) * (x : ℝ) ≤ ((n : ℝ) + 1) * (x : ℝ) := by nlinarith
        have hw1 : (w : ℝ) ≤ 1 := w.2.2
        push_cast at hw
        linarith
      have hsum : ((⟨(n : ℝ) * (x : ℝ), hu0, hu1⟩ : I) : ℝ) + (x : ℝ) = (w : ℝ) := by
        push_cast at hw ⊢; linarith
      have h1 := hadd a ⟨(n : ℝ) * (x : ℝ), hu0, hu1⟩ x w hsum
      have h2 := ih x ⟨(n : ℝ) * (x : ℝ), hu0, hu1⟩ rfl
      push_cast
      rw [h1, h2]; ring
  -- hence `m a (k/n) = a · k/n`
  have hfrac : ∀ (k n : ℕ) (x : I), 0 < n → (x : ℝ) = (k : ℝ) / (n : ℝ) →
      m a x = (a : ℝ) * ((k : ℝ) / (n : ℝ)) := by
    intro k n x hn hx
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have he0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    have he1 : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn']; exact_mod_cast hn
    set e : I := ⟨1 / (n : ℝ), he0, he1⟩ with he
    have h1 : m a 1 = (n : ℝ) * m a e := by
      refine hnat n e 1 ?_
      show (n : ℝ) * (1 / (n : ℝ)) = ((1 : I) : ℝ)
      rw [show ((1 : I) : ℝ) = 1 from rfl]
      field_simp
    have h2 : m a e = (a : ℝ) / (n : ℝ) := by
      rw [hone] at h1
      field_simp at h1 ⊢
      linarith
    have h3 : m a x = (k : ℝ) * m a e := by
      refine hnat k e x ?_
      rw [hx]; show (k : ℝ) * (1 / (n : ℝ)) = (k : ℝ) / (n : ℝ)
      field_simp
    rw [h3, h2]; ring
  -- lower bound, by squeezing with `k = ⌊n·x⌋`
  have hlow : ∀ (x : I) (n : ℕ), 0 < n → (a : ℝ) * (x : ℝ) - 1 / (n : ℝ) ≤ m a x := by
    intro x n hn
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    set k : ℕ := ⌊(n : ℝ) * (x : ℝ)⌋₊ with hk
    have hnx0 : (0 : ℝ) ≤ (n : ℝ) * (x : ℝ) := mul_nonneg hn'.le x.2.1
    have hk1 : (k : ℝ) ≤ (n : ℝ) * (x : ℝ) := Nat.floor_le hnx0
    have hk2 : (n : ℝ) * (x : ℝ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hkn : (k : ℝ) ≤ (n : ℝ) := by nlinarith [x.2.2]
    have hy0 : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := by positivity
    have hy1 : (k : ℝ) / (n : ℝ) ≤ 1 := by rw [div_le_one hn']; exact hkn
    have hval := hfrac k n ⟨(k : ℝ) / (n : ℝ), hy0, hy1⟩ hn rfl
    have hle : ((⟨(k : ℝ) / (n : ℝ), hy0, hy1⟩ : I) : ℝ) ≤ (x : ℝ) := by
      show (k : ℝ) / (n : ℝ) ≤ (x : ℝ)
      rw [div_le_iff₀ hn']; nlinarith
    have := hmono _ _ hle
    rw [hval] at this
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := a.2.1
    have ha1 : (a : ℝ) ≤ 1 := a.2.2
    have hgap : (x : ℝ) - 1 / (n : ℝ) ≤ (k : ℝ) / (n : ℝ) := by
      rw [sub_le_iff_le_add, show (k : ℝ) / (n : ℝ) + 1 / (n : ℝ)
        = ((k : ℝ) + 1) / (n : ℝ) by ring, le_div_iff₀ hn']
      nlinarith
    nlinarith
  have hge : ∀ x : I, (a : ℝ) * (x : ℝ) ≤ m a x := by
    intro x
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have hnpos : 0 < n + 1 := Nat.succ_pos n
    have := hlow x (n + 1) hnpos
    push_cast at this hn
    linarith
  -- upper bound: `m a b = a - m a bᵖ ≤ a - a·(1-b) = a·b`
  have hb0 : (0 : ℝ) ≤ 1 - (b : ℝ) := by linarith [b.2.2]
  have hb1 : 1 - (b : ℝ) ≤ 1 := by linarith [b.2.1]
  have hsplit := hadd a b ⟨1 - (b : ℝ), hb0, hb1⟩ 1
    (by show (b : ℝ) + (1 - (b : ℝ)) = ((1 : I) : ℝ); simp)
  rw [hone] at hsplit
  have hgeb := hge b
  have hgec := hge ⟨1 - (b : ℝ), hb0, hb1⟩
  show m a b = (a : ℝ) * (b : ℝ)
  have hco : ((⟨1 - (b : ℝ), hb0, hb1⟩ : I) : ℝ) = 1 - (b : ℝ) := rfl
  rw [hco] at hgec
  nlinarith

/-- **178III.1** (`eff-monoid-examples`, eff.tex:636, Examples): the usual
product is the *only* way to turn the effect algebra `[0,1]` into an effect
monoid.

⚠ The thesis states this without proof, citing `basmsc` prop. 41, so the
argument below is ours: `y ↦ a ⊙ y` is additive (`emon_mul_ovee`) with
`a ⊙ 1 = a`, and Cauchy's functional equation with monotonicity forces
`a ⊙ y = a · y` (`unitInterval_cauchy`). -/
theorem unitInterval_effectMonoid_unique (em : EffectMonoid I)
    (h : em.toEffectAlgebra = unitInterval.effectAlgebra) :
    ∀ a b : I, em.toMul.mul a b = a * b := by
  -- transport `em`'s unit law and one-sided distributivity along `h`, so that
  -- `⊥` and `⋁` become the *standard* ones while `⊙` stays unknown
  have hone := @EffectMonoid.mul_one I em
  have hdist := @emon_mul_ovee I em
  rw [h] at hone hdist
  have hadd : ∀ (x y z w : I), (y : ℝ) + (z : ℝ) = (w : ℝ) →
      ((em.toMul.mul x w : I) : ℝ)
        = ((em.toMul.mul x y : I) : ℝ) + ((em.toMul.mul x z : I) : ℝ) := by
    intro x y z w hw
    have hcd : Perp y z := by
      show (y : ℝ) + (z : ℝ) ≤ 1
      rw [hw]; exact w.2.2
    obtain ⟨hp, he⟩ := hdist x hcd
    have hwe : ovee y z hcd = w :=
      Subtype.ext (by show (y : ℝ) + (z : ℝ) = (w : ℝ); exact hw)
    rw [hwe] at he
    exact congrArg Subtype.val he
  intro a b
  have key := unitInterval_cauchy (fun x y => ((em.toMul.mul x y : I) : ℝ))
    (fun x y => (em.toMul.mul x y).2.1) (fun x => congrArg _ (hone x)) hadd a b
  refine Subtype.ext ?_
  rw [Set.Icc.coe_mul]
  exact key

/-- Helper: the head of a list is below its sum. -/
theorem PCM.le_of_isSumOf_cons {M : Type u} [PCM M] {a : M} {l : List M} {s : M}
    (h : PCM.IsSumOf (a :: l) s) : a ≼ s := by
  rw [PCM.isSumOf_cons_iff] at h
  obtain ⟨t, _, hp, he⟩ := h
  exact ⟨t, hp, he⟩

/-- Helper for 178V: `a ⊙ b ≼ a` in an effect monoid, since
`(a ⊙ b) ⋁ (a ⊙ bᵖ) = a ⊙ 1 = a`. -/
theorem emon_mul_le_self {M : Type u} [EffectMonoid M] (a b : M) : a * b ≼ a := by
  have hd := EffectMonoid.distrib (PCM.perp_zero a) (EffectAlgebra.perp_orth b)
  rw [PCM.ovee_zero a (PCM.perp_zero a), EffectAlgebra.ovee_orth b,
    EffectMonoid.mul_one a] at hd
  exact PCM.le_of_isSumOf_cons hd

/-- Helper: sums are monotone termwise. -/
theorem PCM.isSumOf_le_of_forall₂ {M : Type u} [EffectAlgebra M] {l l' : List M}
    (hle : List.Forall₂ (· ≼ ·) l' l) :
    ∀ {s s' : M}, PCM.IsSumOf l s → PCM.IsSumOf l' s' → s' ≼ s := by
  induction hle with
  | nil =>
    intro s s' h h'
    rw [PCM.isSumOf_nil_iff] at h h'
    rw [h, h']
    exact pcm_preorder_refl 0
  | cons hxx _ ih =>
    intro s s' h h'
    rw [PCM.isSumOf_cons_iff] at h h'
    obtain ⟨u, hu, hp, he⟩ := h
    obtain ⟨u', hu', hp', he'⟩ := h'
    obtain ⟨h1, k1⟩ := eabasics_le_perp_compat hxx hp
    obtain ⟨h2, k2⟩ := eabasics_le_perp_compat (ih hu hu') (PCM.perp_comm h1)
    rw [← he, ← he']
    refine pcm_preorder_trans ?_ k1
    rw [show ovee _ u' hp' = ovee u' _ h2 from PCM.ovee_comm hp',
      show ovee _ u h1 = ovee u _ (PCM.perp_comm h1) from PCM.ovee_comm h1]
    exact k2

/-- Helper for 178V: the list version of the statement, from which the
indexed one follows by moving `i` to the front of the list. -/
theorem emond_lemma_for_conv_list {M : Type u} [EffectMonoid M]
    (l : List (M × M)) (h1 : PCM.IsSumOf (l.map Prod.fst) 1)
    (h2 : PCM.IsSumOf (l.map fun p => p.1 * p.2) 1) :
    ∀ p ∈ l, p.1 * p.2 = p.1 := by
  classical
  have hf₂ : ∀ t : List (M × M),
      List.Forall₂ (· ≼ ·) (t.map fun q => q.1 * q.2) (t.map Prod.fst) := by
    intro t
    induction t with
    | nil => exact List.Forall₂.nil
    | cons c u ih => exact List.Forall₂.cons (emon_mul_le_self c.1 c.2) ih
  intro p hp
  have hperm : l.Perm (p :: l.erase p) := List.perm_cons_erase hp
  have k1 := PCM.isSumOf_perm (hperm.map Prod.fst) h1
  have k2 := PCM.isSumOf_perm (hperm.map fun q => q.1 * q.2) h2
  rw [List.map_cons, PCM.isSumOf_cons_iff] at k1 k2
  obtain ⟨s, hs, hps, hes⟩ := k1
  obtain ⟨s', hs', hps', hes'⟩ := k2
  -- `s = p₁ᵖ` and `s' = (p₁ ⊙ p₂)ᵖ`
  have e1 : s = orth p.1 := EffectAlgebra.orth_unique hps hes
  have e2 : s' = orth (p.1 * p.2) := EffectAlgebra.orth_unique hps' hes'
  -- `⋁_{j ≠ i} aⱼ ⊙ bⱼ ≤ ⋁_{j ≠ i} aⱼ`, i.e. `(p₁ ⊙ p₂)ᵖ ≤ p₁ᵖ`
  have hmono : s' ≼ s := PCM.isSumOf_le_of_forall₂ (hf₂ (l.erase p)) hs hs'
  -- and `p₁ ⊙ p₂ ≤ p₁` gives `p₁ᵖ ≤ (p₁ ⊙ p₂)ᵖ`
  have hmono' : s ≼ s' := by
    rw [e1, e2]
    exact eabasics_le_iff_orth_le.mp (emon_mul_le_self p.1 p.2)
  have := eabasics_le_antisymm hmono' hmono
  rw [e1, e2] at this
  have h3 := congrArg orth this
  rwa [eabasics_orth_orth, eabasics_orth_orth, eq_comm] at h3

/-- **178V** (`emond-lemma-for-conv`, eff.tex:669, Exercise): if `M` is an
effect monoid and `a₁, …, aₙ, b₁, …, bₙ ∈ M` with `⋁ᵢ aᵢ = 1` and
`⋁ᵢ aᵢ ⊙ bᵢ = 1`, then `aᵢ ⊙ bᵢ = aᵢ` for every `i`. -/
theorem emond_lemma_for_conv {M : Type u} [EffectMonoid M] {n : ℕ}
    (a b : Fin n → M)
    (ha : PCM.IsSumOf (List.ofFn a) 1)
    (hab : PCM.IsSumOf (List.ofFn fun i => a i * b i) 1) :
    ∀ i, a i * b i = a i := by
  intro i
  refine emond_lemma_for_conv_list (List.ofFn fun j => (a j, b j)) ?_ ?_
    (a i, b i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · rw [List.map_ofFn]; exact ha
  · rw [List.map_ofFn]; exact hab

/-! ## Effect modules (parsec 179) -/

/-- **179II** (`dfn-effect-module`, eff.tex:686, Definition): an **effect
module** `E` over an effect monoid `M` is an effect algebra with a scalar
multiplication `M × E → E` such that

1. `(λ ⊙ μ) • a = λ • (μ • a)`;
2. if `a ⊥ b` then `λ • a ⊥ λ • b` and `(λ • a) ⋁ (λ • b) = λ • (a ⋁ b)`;
3. if `λ ⊥ μ` then `λ • a ⊥ μ • a` and `(λ • a) ⋁ (μ • a) = (λ ⋁ μ) • a`;
4. `1 • a = a`. -/
class EffectModule (M : Type u) (E : Type v) [EffectMonoid M] [EffectAlgebra E]
    extends SMul M E where
  mul_smul : ∀ (l m : M) (a : E), (l * m) • a = l • m • a
  smul_perp : ∀ (l : M) {a b : E} (h : Perp a b),
    ∃ h' : Perp (l • a) (l • b), ovee (l • a) (l • b) h' = l • ovee a b h
  perp_smul : ∀ {l m : M} (h : Perp l m) (a : E),
    ∃ h' : Perp (l • a) (m • a), ovee (l • a) (m • a) h' = ovee l m h • a
  one_smul : ∀ a : E, (1 : M) • a = a

/-- **179II** (`dfn-effect-module`, eff.tex:711, Definition): an
**`M`-effect module homomorphism** is an effect algebra homomorphism `f`
with `λ • f a = f (λ • a)`. -/
structure EffectModuleHom (M : Type u) (E F : Type v) [EffectMonoid M]
    [EffectAlgebra E] [EffectAlgebra F] [EffectModule M E] [EffectModule M F]
    extends EAHom E F where
  map_smul : ∀ (l : M) (a : E), toFun (l • a) = l • toFun a

/-- The identity effect module homomorphism. -/
def EffectModuleHom.id (M : Type u) (E : Type v) [EffectMonoid M]
    [EffectAlgebra E] [EffectModule M E] : EffectModuleHom M E E :=
  { EAHom.id E with map_smul := fun _ _ => rfl }

/-- Composition of effect module homomorphisms. -/
def EffectModuleHom.comp {M : Type u} {E F G : Type v} [EffectMonoid M]
    [EffectAlgebra E] [EffectAlgebra F] [EffectAlgebra G]
    [EffectModule M E] [EffectModule M F] [EffectModule M G]
    (g : EffectModuleHom M F G) (f : EffectModuleHom M E F) :
    EffectModuleHom M E G :=
  { g.toEAHom.comp f.toEAHom with
    map_smul := fun l a => by
      show g.toFun (f.toFun (l • a)) = l • g.toFun (f.toFun a)
      rw [f.map_smul, g.map_smul] }

/-- **179II** (`dfn-effect-module`, eff.tex:717, Definition): the category
`EMod_M` of effect modules over `M` and `M`-effect module homomorphisms. -/
structure EModCat (M : Type u) [EffectMonoid M] : Type (max u (v + 1)) where
  carrier : Type v
  [eaStr : EffectAlgebra carrier]
  [modStr : EffectModule M carrier]

attribute [instance] EModCat.eaStr EModCat.modStr

instance (M : Type u) [EffectMonoid M] : CoeSort (EModCat.{u, v} M) (Type v) :=
  ⟨EModCat.carrier⟩

/-- Bundle an effect module as an object of `EMod_M`. -/
def EModCat.of (M : Type u) [EffectMonoid M] (E : Type v) [EffectAlgebra E]
    [EffectModule M E] : EModCat.{u, v} M := ⟨E⟩

instance (M : Type u) [EffectMonoid M] : Category (EModCat.{u, v} M) where
  Hom E F := EffectModuleHom M E F
  id E := EffectModuleHom.id M E
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- **179III.1** (eff.tex:722, Examples): every effect algebra is an effect
module over the two-element effect monoid `2` (= `Bool`). -/
def effectModuleBool (E : Type v) [EffectAlgebra E] : EffectModule Bool E where
  smul b a := if b then a else 0
  mul_smul := by intro l m a; cases l <;> cases m <;> rfl
  smul_perp := by
    intro l a b h
    cases l
    · exact ⟨PCM.zero_perp 0, PCM.zero_ovee 0⟩
    · exact ⟨h, rfl⟩
  perp_smul := by
    intro l m h a
    cases l <;> cases m
    · exact ⟨PCM.zero_perp 0, PCM.zero_ovee 0⟩
    · exact ⟨PCM.zero_perp a, PCM.zero_ovee a⟩
    · exact ⟨PCM.perp_zero a, PCM.ovee_zero a _⟩
    · have h' : (true : Bool) ⊓ true = ⊥ := h
      exact absurd h' (by decide)
  one_smul := by intro a; rfl

/-- Helper for 179III.1: the effect module structure over `2` on an effect
algebra is unique — `1 • a = a` by the module axioms and `0 • a = 0` because
`0 • a ⋁ 0 • a = 0 • a`. -/
theorem effectModule_bool_smul {E : Type v} [EffectAlgebra E]
    [EffectModule Bool E] (l : Bool) (a : E) : l • a = if l then a else 0 := by
  have hpf : Perp (false : Bool) (false : Bool) := rfl
  cases l
  · obtain ⟨h', e⟩ := EffectModule.perp_smul (M := Bool) (E := E)
      (l := false) (m := false) hpf a
    have e' : ovee ((false : Bool) • a) ((false : Bool) • a) h' = (false : Bool) • a := by
      rw [e]; rfl
    show (false : Bool) • a = (0 : E)
    exact eabasics_cancellation (c := (false : Bool) • a) h'
      (PCM.zero_perp _) (e'.trans (PCM.zero_ovee _).symm)
  · show (true : Bool) • a = a
    exact EffectModule.one_smul a

/-- **179III.1** (eff.tex:722, Examples): `EA ≅ EMod₂` — the category of
effect algebras is equivalent to that of effect modules over `2`. -/
theorem ea_equiv_emod_two :
    Nonempty (EACat.{u} ≌ EModCat.{0, u} Bool) :=
  -- every effect algebra is a `2`-effect module, and every effect algebra
  -- homomorphism is `2`-linear because it preserves `0`
  let F : EACat.{u} ⥤ EModCat.{0, u} Bool :=
    { obj := fun E => @EModCat.mk Bool _ E.carrier E.str (effectModuleBool E.carrier)
      map := fun {A B} f =>
        @EffectModuleHom.mk Bool A.carrier B.carrier _ A.str B.str
          (effectModuleBool A.carrier) (effectModuleBool B.carrier) f
          (fun l _ => by
            cases l
            · exact exc_eamorphism_map_zero f
            · rfl)
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  -- the forgetful functor the other way
  let G : EModCat.{0, u} Bool ⥤ EACat.{u} :=
    { obj := fun E => ⟨E.carrier⟩
      map := fun f => f.toEAHom
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  -- `G ⋙ F` is the identity on the underlying effect algebra, and the
  -- `2`-action is uniquely determined, so the identity map is an isomorphism
  let ε : ∀ E : EModCat.{0, u} Bool, (G ⋙ F).obj E ≅ E := fun E =>
    { hom := @EffectModuleHom.mk Bool E.carrier E.carrier _ E.eaStr E.eaStr
        (effectModuleBool E.carrier) E.modStr (EAHom.id E.carrier)
        (fun l a => (effectModule_bool_smul l a).symm)
      inv := @EffectModuleHom.mk Bool E.carrier E.carrier _ E.eaStr E.eaStr
        E.modStr (effectModuleBool E.carrier) (EAHom.id E.carrier)
        (fun l a => effectModule_bool_smul l a)
      hom_inv_id := rfl
      inv_hom_id := rfl }
  ⟨CategoryTheory.Equivalence.mk F G (Iso.refl _)
    (NatIso.ofComponents ε (fun _ => rfl))⟩

/-- The one-element effect monoid `1` (179III.1). -/
instance : EffectMonoid PUnit :=
  { (inferInstance : EffectAlgebra PUnit) with
    mul := fun _ _ => PUnit.unit
    one_mul _ := rfl
    mul_one _ := rfl
    mul_assoc _ _ _ := rfl
    distrib := by
      intro a b c d hab hcd
      exact PCM.IsSumOf.cons (PCM.IsSumOf.cons (PCM.IsSumOf.cons
        (PCM.IsSumOf.cons PCM.IsSumOf.nil trivial) trivial) trivial) trivial }

/-- **179III.1** (eff.tex:722, Examples): the only effect module over the
one-element effect monoid `1` is (up to isomorphism) the one-element effect
algebra. -/
theorem emod_punit_subsingleton (E : Type v) [EffectAlgebra E]
    [EffectModule PUnit E] : Subsingleton E := by
  -- `1 = 0` in `1`, so `a ⋁ a = (1 ⋁ 1) • a = 1 • a = a`, whence `a = 0`.
  have hone := EffectModule.one_smul (M := PUnit) (E := E)
  have key : ∀ a : E, a = 0 := by
    intro a
    obtain ⟨h', e⟩ :=
      EffectModule.perp_smul (M := PUnit) (E := E) (l := PUnit.unit) (m := PUnit.unit)
        trivial a
    have hpa : Perp a a := by rw [← hone a]; exact h'
    have e' : ovee _ _ h' = a := by rw [e]; exact hone a
    have ea : ovee a a hpa = a :=
      (PCM.ovee_congr (hone a) (hone a) h' hpa).symm.trans e'
    exact eabasics_cancellation (c := a) hpa (PCM.zero_perp a)
      (ea.trans (PCM.zero_ovee a).symm)
  exact ⟨fun x y => (key x).trans (key y).symm⟩

/-- **179III.2** (eff.tex:731, Examples): if `V` is an ordered real vector
space with `u ≥ 0`, then `[0,u]_V` is an effect module over `[0,1]`
(effect modules over `[0,1]` are exactly the *convex effect algebras*). -/
noncomputable def orderIntervalEffectModule (V : Type v) [AddCommGroup V]
    [Module ℝ V] [PartialOrder V] [IsOrderedAddMonoid V] [PosSMulMono ℝ V]
    [SMulPosMono ℝ V] (u : V) (hu : 0 ≤ u) :
    @EffectModule I (Set.Icc (0 : V) u) _ (orderIntervalEffectAlgebra V u hu) :=
  letI := orderIntervalEffectAlgebra V u hu
  { smul := fun r v => ⟨(r : ℝ) • (v : V), smul_nonneg r.2.1 v.2.1, by
      calc (r : ℝ) • (v : V) ≤ (r : ℝ) • u := smul_le_smul_of_nonneg_left v.2.2 r.2.1
        _ ≤ (1 : ℝ) • u := smul_le_smul_of_nonneg_right r.2.2 hu
        _ = u := one_smul ℝ u⟩
    mul_smul := by
      intro l m a
      exact Subtype.ext (mul_smul (l : ℝ) (m : ℝ) (a : V))
    smul_perp := by
      intro l a b h
      have hab : (a : V) + b ≤ u := h
      have hp : ((l : ℝ) • (a : V)) + (l : ℝ) • (b : V) ≤ u := by
        rw [← smul_add]
        calc (l : ℝ) • ((a : V) + b) ≤ (l : ℝ) • u :=
              smul_le_smul_of_nonneg_left hab l.2.1
          _ ≤ (1 : ℝ) • u := smul_le_smul_of_nonneg_right l.2.2 hu
          _ = u := one_smul ℝ u
      exact ⟨hp, Subtype.ext (smul_add (l : ℝ) (a : V) (b : V)).symm⟩
    perp_smul := by
      intro l m h a
      have hlm : (l : ℝ) + m ≤ 1 := h
      have hp : ((l : ℝ) • (a : V)) + (m : ℝ) • (a : V) ≤ u := by
        rw [← add_smul]
        calc ((l : ℝ) + m) • (a : V) ≤ (1 : ℝ) • (a : V) :=
              smul_le_smul_of_nonneg_right hlm a.2.1
          _ = (a : V) := one_smul ℝ _
          _ ≤ u := a.2.2
      exact ⟨hp, Subtype.ext (add_smul (l : ℝ) (m : ℝ) (a : V)).symm⟩
    one_smul := by
      intro a
      exact Subtype.ext (one_smul ℝ (a : V)) }

/-- **179III.2** (eff.tex:731, Examples): *representation theorem* (Gudder–
Pulmannová): every effect module over `[0,1]` is isomorphic to the order
interval `[0,u]` of an ordered real vector space `V` with order unit `u`,
by a bijection preserving partial sum and scalar multiplication.

**PARKED — this is not a result of the thesis.**  eff.tex:739 asserts it by
*citation only* ("In fact, every effect module over `[0,1]` is of this form
`\cite{gudder1998representation}`"); there is no proof in the text to
transcribe, and nothing in this development uses it.  Proving it is an
independent project (Gudder's representation theorem), not part of validating
the thesis.

Note also that the statement below is **weaker than the cited result**: it
produces only `[PartialOrder V] [IsOrderedAddMonoid V]` and `0 ≤ u`, whereas
"ordered real vector space with order unit" additionally requires the positive
cone to be closed under nonnegative scalars (`PosSMulMono`/`SMulPosMono`, as in
`orderIntervalEffectModule` above) and `u` to be an order unit.  If this is ever
revived, strengthen it first — as written it would be provable without being the
theorem. -/
theorem effectModule_unitInterval_representation (E : Type u) [EffectAlgebra E]
    [EffectModule I E] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℝ V) (_ : PartialOrder V)
      (_ : IsOrderedAddMonoid V) (u : V) (_ : 0 ≤ u)
      (f : E → Set.Icc (0 : V) u),
        Function.Bijective f ∧
        (∀ (a b : E) (h : Perp a b), (f (ovee a b h) : V) = (f a : V) + (f b : V)) ∧
        (∀ (r : I) (a : E), (f (r • a) : V) = (r : ℝ) • (f a : V)) := sorry

end Theses.B.Eff
