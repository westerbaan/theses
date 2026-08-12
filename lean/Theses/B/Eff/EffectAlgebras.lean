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
  points are `sorry`-ed theorems.  Example points that make substantive
  claims appear as instances/defs whose *data* is genuine and whose proof
  obligations are `sorry`-ed, or as `sorry`-ed theorems.
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

/-- **174III** (`pcm-preorder`, eff.tex:220, Exercise), part 1: `≼` is
reflexive on a PCM. -/
theorem pcm_preorder_refl {M : Type u} [PCM M] (a : M) : a ≼ a := sorry

/-- **174III** (`pcm-preorder`, eff.tex:220, Exercise), part 2: `≼` is
transitive on a PCM, so a PCM is preordered by `≼`. -/
theorem pcm_preorder_trans {M : Type u} [PCM M] {a b c : M} :
    a ≼ b → b ≼ c → a ≼ c := sorry

/-- The relation "`s` is a sum of the (multiset of) elements listed in `l`"
in a PCM, by iterating `ovee` (used for 174IV, and for the distributivity
axiom of effect monoids, 178II). -/
inductive PCM.IsSumOf {M : Type u} [PCM M] : List M → M → Prop
  | nil : PCM.IsSumOf [] 0
  | cons {a : M} {l : List M} {s : M} (hl : PCM.IsSumOf l s) (h : Perp a s) :
      PCM.IsSumOf (a :: l) (ovee a s h)

/-- **174IV** (eff.tex:223): in a PCM a sum depends only on which elements
occur (and how often), not on their order: if `x₁ ⋁ ⋯ ⋁ xₙ` exists, then so
does the sum over any permutation, with the same value. -/
theorem PCM.isSumOf_perm {M : Type u} [PCM M] {l l' : List M} {s : M}
    (hp : l.Perm l') (hs : PCM.IsSumOf l s) : PCM.IsSumOf l' s := sorry

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
and `xᵖ = 1 - x`.  (Data genuine; verification obligations `sorry`-ed.) -/
noncomputable instance unitInterval.effectAlgebra : EffectAlgebra I where
  zero := 0
  one := 1
  Perp x y := (x : ℝ) + (y : ℝ) ≤ 1
  ovee x y _ := ⟨(x : ℝ) + y, sorry⟩
  orth x := ⟨1 - (x : ℝ), sorry⟩
  perp_comm := sorry
  ovee_comm := sorry
  perp_of_ovee_perp := sorry
  perp_ovee_of_ovee_perp := sorry
  ovee_assoc := sorry
  zero_perp := sorry
  zero_ovee := sorry
  perp_orth := sorry
  ovee_orth := sorry
  orth_unique := sorry
  eq_zero_of_perp_one := sorry

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
  ovee x y _ := ⟨(x : G) + y, sorry⟩
  orth x := ⟨u - x, sorry⟩
  perp_comm := sorry
  ovee_comm := sorry
  perp_of_ovee_perp := sorry
  perp_ovee_of_ovee_perp := sorry
  ovee_assoc := sorry
  zero_perp := sorry
  zero_ovee := sorry
  perp_orth := sorry
  ovee_orth := sorry
  orth_unique := sorry
  eq_zero_of_perp_one := sorry

/-- **175II.3** (`eaexamples`, eff.tex:307, Examples): the set of **effects**
`[0,1]_𝒜` of a von Neumann algebra `𝒜` is an effect algebra with `a ⊥ b`
iff `a + b ≤ 1`, `a ⋁ b = a + b` and `aᵖ = 1 - a`.  (The "effect" in effect
algebra originates from this example.) -/
noncomputable instance effectsEffectAlgebra (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    EffectAlgebra (Theses.effects A) where
  zero := ⟨0, le_refl 0, sorry⟩
  one := ⟨1, sorry, le_refl 1⟩
  Perp a b := (a : A) + b ≤ 1
  ovee a b _ := ⟨(a : A) + b, sorry⟩
  orth a := ⟨1 - a, sorry⟩
  perp_comm := sorry
  ovee_comm := sorry
  perp_of_ovee_perp := sorry
  perp_ovee_of_ovee_perp := sorry
  ovee_assoc := sorry
  zero_perp := sorry
  zero_ovee := sorry
  perp_orth := sorry
  ovee_orth := sorry
  orth_unique := sorry
  eq_zero_of_perp_one := sorry

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
  perp_comm := sorry
  ovee_comm := sorry
  perp_of_ovee_perp := sorry
  perp_ovee_of_ovee_perp := sorry
  ovee_assoc := sorry
  zero_perp := sorry
  zero_ovee := sorry
  perp_orth := sorry
  ovee_orth := sorry
  orth_unique := sorry
  eq_zero_of_perp_one := sorry

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
  perp_comm := sorry
  ovee_comm := sorry
  perp_of_ovee_perp := sorry
  perp_ovee_of_ovee_perp := sorry
  ovee_assoc := sorry
  zero_perp := sorry
  zero_ovee := sorry
  perp_orth := sorry
  ovee_orth := sorry
  orth_unique := sorry
  eq_zero_of_perp_one := sorry

/-- **175II.6** (`eaexamples`, eff.tex:330, Examples): the one-element
Boolean algebra `1` is the final object of **EA**. -/
theorem eaexamples_final : Nonempty (IsTerminal (EACat.of PUnit.{u + 1})) := sorry

/-- **175II.6** (`eaexamples`, eff.tex:330, Examples): the two-element
Boolean algebra `2` is the initial object of **EA**.  (Stated in universe 0,
where `Bool` lives.) -/
theorem eaexamples_initial : Nonempty (IsInitial (EACat.of Bool)) := sorry

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
  perp_comm := sorry
  ovee_comm := sorry
  perp_of_ovee_perp := sorry
  perp_ovee_of_ovee_perp := sorry
  ovee_assoc := sorry
  zero_perp := sorry
  zero_ovee := sorry
  perp_orth := sorry
  ovee_orth := sorry
  orth_unique := sorry
  eq_zero_of_perp_one := sorry

/-- **175III** (`ea-product`, eff.tex:338, Exercise), part 2: `E × F` with
the componentwise structure is the categorical product in **EA** (stated
here as: **EA** has binary products). -/
theorem ea_product_categorical : HasBinaryProducts EACat.{u} := sorry

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
    ∀ a : M, ∃ h : S.Perp S.zero a, S.ovee S.zero a h = a := sorry

section EABasics

variable {E : Type u} [EffectAlgebra E]

/-- **175V.1** (`eabasics`, eff.tex:354, Proposition): *(involution)*
`aᵖᵖ = a`. -/
theorem eabasics_orth_orth (a : E) : orth (orth a) = a := sorry

/-- **175V.2** (`eabasics`, eff.tex:354, Proposition): `1ᵖ = 0`. -/
theorem eabasics_orth_one : orth (1 : E) = 0 := sorry

/-- **175V.2** (`eabasics`, eff.tex:354, Proposition): `0ᵖ = 1`. -/
theorem eabasics_orth_zero : orth (0 : E) = 1 := sorry

/-- **175V.3** (`eabasics`, eff.tex:354, Proposition): *(positivity)* if
`a ⋁ b = 0` then `a = 0` and `b = 0`. -/
theorem eabasics_positivity {a b : E} (h : Perp a b) (h0 : ovee a b h = 0) :
    a = 0 ∧ b = 0 := sorry

/-- **175V.4** (`eabasics`, eff.tex:354, Proposition): *(cancellation)* if
`a ⋁ c = b ⋁ c` then `a = b`. -/
theorem eabasics_cancellation {a b c : E} (h₁ : Perp a c) (h₂ : Perp b c)
    (h : ovee a c h₁ = ovee b c h₂) : a = b := sorry

/-- **175V.5** (`eabasics`, eff.tex:354, Proposition): the relation `≼` of
174II partially orders `E` (antisymmetry; reflexivity and transitivity are
174III). -/
theorem eabasics_le_antisymm {a b : E} (hab : a ≼ b) (hba : b ≼ a) : a = b := sorry

/-- **175V.6** (`eabasics`, eff.tex:354, Proposition): `a ≼ b` iff
`bᵖ ≼ aᵖ`. -/
theorem eabasics_le_iff_orth_le {a b : E} : a ≼ b ↔ orth b ≼ orth a := sorry

/-- **175V.7** (`eabasics`, eff.tex:354, Proposition): if `a ≼ b` and
`b ⊥ c`, then `a ⊥ c` and `a ⋁ c ≼ b ⋁ c`. -/
theorem eabasics_le_perp_compat {a b c : E} (hab : a ≼ b) (hbc : Perp b c) :
    ∃ hac : Perp a c, ovee a c hac ≼ ovee b c hbc := sorry

/-- **175V.8** (`eabasics`, eff.tex:354, Proposition): `a ⊥ b` iff
`a ≼ bᵖ`. -/
theorem eabasics_perp_iff_le_orth {a b : E} : Perp a b ↔ a ≼ orth b := sorry

/-! ### Partial difference and D-posets (parsec 176) -/

/-- **176I** (eff.tex:430, Definition): `IsDiff b a c` says that `c` is *the*
difference `b ⊖ a`, i.e. `a ⋁ c = b`; by cancellation such a `c` is unique
if it exists. -/
def IsDiff (b a c : E) : Prop := ∃ h : Perp a c, ovee a c h = b

/-- **176I** (eff.tex:430, Definition): well-definedness of `⊖` — the
difference is unique (by cancellation). -/
theorem isDiff_unique {b a c c' : E} (h : IsDiff b a c) (h' : IsDiff b a c') :
    c = c' := sorry

/-- **176I** (eff.tex:430, Definition): the difference `b ⊖ a`, defined when
`a ≼ b`. -/
noncomputable def ominus (b a : E) (h : a ≼ b) : E := h.choose

/-- The defining property of `ominus`: `b ⊖ a` really is a difference. -/
theorem isDiff_ominus {b a : E} (h : a ≼ b) : IsDiff b a (ominus b a h) :=
  h.choose_spec

/-- **176II** (`exc-dposet`, eff.tex:437, Exercise\*), (D1): `a ⊖ b` is
defined iff `b ≼ a`. -/
theorem exc_dposet_D1 {a b : E} : (∃ c, IsDiff a b c) ↔ b ≼ a := sorry

/-- **176II** (`exc-dposet`, eff.tex:437, Exercise\*), (D2): `a ⊖ b ≼ a`
(when defined). -/
theorem exc_dposet_D2 {a b c : E} (h : IsDiff a b c) : c ≼ a := sorry

/-- **176II** (`exc-dposet`, eff.tex:437, Exercise\*), (D3):
`a ⊖ (a ⊖ b) = b` (when defined). -/
theorem exc_dposet_D3 {a b c : E} (h : IsDiff a b c) : IsDiff a c b := sorry

/-- **176II** (`exc-dposet`, eff.tex:437, Exercise\*), (D4): if
`a ≼ b ≼ c`, then `c ⊖ b ≼ c ⊖ a` and
`(c ⊖ a) ⊖ (c ⊖ b) = b ⊖ a`. -/
theorem exc_dposet_D4 {a b c u v : E} (hab : a ≼ b) (hbc : b ≼ c)
    (hu : IsDiff c b u) (hv : IsDiff c a v) :
    u ≼ v ∧ ∀ w, IsDiff v u w → IsDiff b a w := sorry

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

/-- **176III** (eff.tex:448, Exercise\* continued): a D-poset `E` carries an
effect algebra structure (`a ⋁ b = c ⇔ c ⊖ b = a`, `aᵖ = 1 ⊖ a`) whose
order and difference agree with the given ones. -/
theorem exc_dposet_ea (E : Type u) [DPoset E] :
    ∃ ea : EffectAlgebra E,
      (∀ a b : E, @PCM.le E ea.toPCM a b ↔ a ≤ b) ∧
      (∀ a : E, @EffectAlgebra.orth E ea a = DPoset.sub ⊤ a le_top) := sorry

section EAMorphism

variable {E : Type u} {F : Type u} [EffectAlgebra E] [EffectAlgebra F]

/-- **176V.1** (`exc-eamorphism`, eff.tex:465, Exercise): an effect algebra
homomorphism preserves zero: `f 0 = 0`. -/
theorem exc_eamorphism_map_zero (f : EAHom E F) : f.toFun 0 = 0 := sorry

/-- **176V.2** (`exc-eamorphism`, eff.tex:465, Exercise): an effect algebra
homomorphism is order preserving. -/
theorem exc_eamorphism_monotone (f : EAHom E F) {a b : E} (h : a ≼ b) :
    f.toFun a ≼ f.toFun b := sorry

/-- **176V.3** (`exc-eamorphism`, eff.tex:465, Exercise): if `a ⊖ b` is
defined, then `f (a ⊖ b) = f a ⊖ f b`. -/
theorem exc_eamorphism_map_diff (f : EAHom E F) {a b c : E} (h : IsDiff a b c) :
    IsDiff (f.toFun a) (f.toFun b) (f.toFun c) := sorry

/-- **176V.4** (`exc-eamorphism`, eff.tex:465, Exercise): consequently
`f (aᵖ) = (f a)ᵖ`. -/
theorem exc_eamorphism_map_orth (f : EAHom E F) (a : E) :
    f.toFun (orth a) = orth (f.toFun a) := sorry

end EAMorphism

/-- **177Ia** (`ea-modularity-prop`, eff.tex:484, Proposition): in an effect
algebra, if the infimum `a ⊓ b` exists for `a ⊥ b`, then the supremum
`a ⊔ b` exists as well, and `a ⋁ b = (a ⊓ b) ⋁ (a ⊔ b)`. -/
theorem ea_modularity_prop {E : Type u} [EffectAlgebra E] {a b m : E}
    (hab : Perp a b) (hm : PCM.IsInf a b m) :
    ∃ (j : E) (hmj : Perp m j), PCM.IsSup a b j ∧ ovee a b hab = ovee m j hmj :=
  sorry

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
  perp_comm := sorry
  ovee_comm := sorry
  perp_of_ovee_perp := sorry
  perp_ovee_of_ovee_perp := sorry
  ovee_assoc := sorry
  zero_perp := sorry
  zero_ovee := sorry
  perp_orth := sorry
  ovee_orth := sorry
  orth_unique := sorry
  eq_zero_of_perp_one := sorry

/-- **177VI** (`orth-ea-is-orthomodular`, eff.tex:564, Proposition): an
effect algebra that is an ortholattice (for its algebraic order, with
orthocomplement as lattice complement) is orthomodular. -/
theorem orth_ea_is_orthomodular (E : Type u) [EffectAlgebra E] [Ortholattice E]
    (hle : ∀ a b : E, a ≤ b ↔ a ≼ b)
    (hcompl : ∀ a : E, aᶜ = orth a) :
    ∀ {a b : E}, a ≤ b → a ⊔ (aᶜ ⊓ b) = b := sorry

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
    one_mul := sorry
    mul_one := sorry
    mul_assoc := sorry
    distrib := sorry }

/-- **178III.3** (`eff-monoid-examples`, eff.tex:646, Examples): the
two-element Boolean algebra `2` is an effect monoid with
`x ⊙ y = x ∧ y`. -/
instance : EffectMonoid Bool := booleanEffectMonoid Bool

/-- **178III.1** (`eff-monoid-examples`, eff.tex:636, Examples): `[0,1]` is
a commutative effect monoid with the usual product. -/
noncomputable instance unitInterval.effectMonoid : EffectMonoid I :=
  { unitInterval.effectAlgebra with
    mul := (· * ·)
    one_mul := sorry
    mul_one := sorry
    mul_assoc := sorry
    distrib := sorry }

/-- **178III.1** (`eff-monoid-examples`, eff.tex:636, Examples): the usual
product is the *only* way to turn the effect algebra `[0,1]` into an effect
monoid. -/
theorem unitInterval_effectMonoid_unique (em : EffectMonoid I)
    (h : em.toEffectAlgebra = unitInterval.effectAlgebra) :
    ∀ a b : I, em.toMul.mul a b = a * b := sorry

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
    a * 0 = 0 ∧ (0 : M) * a = 0 := sorry

/-- **178V** (`emond-lemma-for-conv`, eff.tex:669, Exercise): if `M` is an
effect monoid and `a₁, …, aₙ, b₁, …, bₙ ∈ M` with `⋁ᵢ aᵢ = 1` and
`⋁ᵢ aᵢ ⊙ bᵢ = 1`, then `aᵢ ⊙ bᵢ = aᵢ` for every `i`. -/
theorem emond_lemma_for_conv {M : Type u} [EffectMonoid M] {n : ℕ}
    (a b : Fin n → M)
    (ha : PCM.IsSumOf (List.ofFn a) 1)
    (hab : PCM.IsSumOf (List.ofFn fun i => a i * b i) 1) :
    ∀ i, a i * b i = a i := sorry

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
  mul_smul := sorry
  smul_perp := sorry
  perp_smul := sorry
  one_smul := sorry

/-- **179III.1** (eff.tex:722, Examples): `EA ≅ EMod₂` — the category of
effect algebras is equivalent to that of effect modules over `2`. -/
theorem ea_equiv_emod_two :
    Nonempty (EACat.{u} ≌ EModCat.{0, u} Bool) := sorry

/-- The one-element effect monoid `1` (179III.1). -/
instance : EffectMonoid PUnit :=
  { (inferInstance : EffectAlgebra PUnit) with
    mul := fun _ _ => PUnit.unit
    one_mul := sorry
    mul_one := sorry
    mul_assoc := sorry
    distrib := sorry }

/-- **179III.1** (eff.tex:722, Examples): the only effect module over the
one-element effect monoid `1` is (up to isomorphism) the one-element effect
algebra. -/
theorem emod_punit_subsingleton (E : Type v) [EffectAlgebra E]
    [EffectModule PUnit E] : Subsingleton E := sorry

/-- **179III.2** (eff.tex:731, Examples): if `V` is an ordered real vector
space with `u ≥ 0`, then `[0,u]_V` is an effect module over `[0,1]`
(effect modules over `[0,1]` are exactly the *convex effect algebras*). -/
noncomputable def orderIntervalEffectModule (V : Type v) [AddCommGroup V]
    [Module ℝ V] [PartialOrder V] [IsOrderedAddMonoid V] (u : V) (hu : 0 ≤ u) :
    @EffectModule I (Set.Icc (0 : V) u) _ (orderIntervalEffectAlgebra V u hu) :=
  letI := orderIntervalEffectAlgebra V u hu
  { smul := fun r v => ⟨(r : ℝ) • (v : V), sorry⟩
    mul_smul := sorry
    smul_perp := sorry
    perp_smul := sorry
    one_smul := sorry }

/-- **179III.2** (eff.tex:731, Examples): *representation theorem* (Gudder–
Pulmannová): every effect module over `[0,1]` is isomorphic to the order
interval `[0,u]` of an ordered real vector space `V` with order unit `u`,
by a bijection preserving partial sum and scalar multiplication. -/
theorem effectModule_unitInterval_representation (E : Type u) [EffectAlgebra E]
    [EffectModule I E] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℝ V) (_ : PartialOrder V)
      (_ : IsOrderedAddMonoid V) (u : V) (_ : 0 ≤ u)
      (f : E → Set.Icc (0 : V) u),
        Function.Bijective f ∧
        (∀ (a b : E) (h : Perp a b), (f (ovee a b h) : V) = (f a : V) + (f b : V)) ∧
        (∀ (r : I) (a : E), (f (r • a) : V) = (r : ℝ) • (f a : V)) := sorry

end Theses.B.Eff
