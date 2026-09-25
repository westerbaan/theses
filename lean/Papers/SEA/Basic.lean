/-
Copyright: the authors of the theses formalisation.

# SEA §2.1–2.2: sequential effect algebras and effect monoids

A. Westerbaan, B. Westerbaan, J. van de Wetering, *The three types of normal
sequential effect algebras*, Quantum 2020 (arXiv:2004.12749),
`../papers/2004.12749/second.tex`, points **SEA 1**–**SEA 37**.

Conventions: `Papers/README.md`; plan: `Papers/SEA/PLAN.md`.

* Effect algebras, their order `≼`, `orth` and `ominus` are the theses'
  (`Theses.B.Eff.EffectAlgebra`, eff.tex 175I).
* A convex action is an effect module over `[0,1]` (`EffectModule I E`,
  eff.tex 179II).
* A SEA is the theses' `SequentialEffectAlgebra` (eff.tex 225IV) **plus** the
  unconditional half of S5 (`SEAlgebra.seq_comm_seq`), which eff.tex's S5 only asks
  for summable `a, b`.
* Directed completeness, suprema and normality are new here, stated with the
  effect-algebra order `≼`.
* Where the paper cites the companion paper OAP ("[first]") for a result we do
  not prove, the result is a `Prop` below (`SEA35`, `OAP43`, `OAP47`) and is
  an explicit hypothesis of the declarations that need it.
-/
import Theses.B.Eff.VNExamples

namespace Papers.SEA

open Theses.B.Eff
open scoped unitInterval

universe u v

/-! ## Effect-algebra basics (SEA 1–7) -/

section EABasics

variable {E : Type u} [EffectAlgebra E]

theorem le_refl' (a : E) : a ≼ a := pcm_preorder_refl a

theorem le_trans' {a b c : E} (h1 : a ≼ b) (h2 : b ≼ c) : a ≼ c := pcm_preorder_trans h1 h2

theorem le_antisymm' {a b : E} (h1 : a ≼ b) (h2 : b ≼ a) : a = b := eabasics_le_antisymm h1 h2

theorem zero_le' (a : E) : (0 : E) ≼ a := ⟨a, PCM.zero_perp a, PCM.zero_ovee a⟩

theorem le_one' (a : E) : a ≼ 1 :=
  ⟨orth a, EffectAlgebra.perp_orth a, EffectAlgebra.ovee_orth a⟩

theorem orth_orth (a : E) : orth (orth a) = a := eabasics_orth_orth a

theorem orth_le_orth {a b : E} (h : a ≼ b) : orth b ≼ orth a := eabasics_le_iff_orth_le.mp h

theorem le_of_orth_le_orth {a b : E} (h : orth b ≼ orth a) : a ≼ b :=
  eabasics_le_iff_orth_le.mpr h

theorem perp_iff_le_orth {a b : E} : Perp a b ↔ a ≼ orth b := eabasics_perp_iff_le_orth

theorem left_le_ovee {a b : E} (h : Perp a b) : a ≼ ovee a b h := ⟨b, h, rfl⟩

theorem right_le_ovee {a b : E} (h : Perp a b) : b ≼ ovee a b h :=
  ⟨a, PCM.perp_comm h, (PCM.ovee_comm h).symm⟩

theorem perp_of_le_left {a a' b : E} (ha : a ≼ a') (h : Perp a' b) : Perp a b :=
  perp_iff_le_orth.mpr (le_trans' ha (perp_iff_le_orth.mp h))

theorem perp_of_le_right {a b b' : E} (hb : b ≼ b') (h : Perp a b') : Perp a b :=
  PCM.perp_comm (perp_of_le_left hb (PCM.perp_comm h))

theorem perp_of_le {a a' b b' : E} (ha : a ≼ a') (hb : b ≼ b') (h : Perp a' b') :
    Perp a b := perp_of_le_left ha (perp_of_le_right hb h)

theorem eq_zero_of_le_zero {a : E} (h : a ≼ 0) : a = 0 := le_antisymm' h (zero_le' a)

theorem ovee_zero_eq (a : E) (h : Perp a 0) : ovee a 0 h = a := PCM.ovee_zero a h

theorem zero_ovee_eq (a : E) (h : Perp 0 a) : ovee 0 a h = a := PCM.zero_ovee' a h

theorem ovee_comm' {a b : E} (h : Perp a b) (h' : Perp b a) : ovee a b h = ovee b a h' :=
  PCM.ovee_comm h

/-- Cancellation on the left: `a ⋁ b = a ⋁ c` implies `b = c`. -/
theorem cancel_left {a b c : E} (h1 : Perp a b) (h2 : Perp a c)
    (e : ovee a b h1 = ovee a c h2) : b = c := by
  refine eabasics_cancellation (PCM.perp_comm h1) (PCM.perp_comm h2) ?_
  rw [← PCM.ovee_comm h1, ← PCM.ovee_comm h2, e]

/-- `x ⋁ y = x` forces `y = 0`. -/
theorem eq_zero_of_ovee_eq_self {x y : E} (h : Perp x y) (e : ovee x y h = x) : y = 0 :=
  cancel_left h (PCM.perp_zero x) (e.trans (ovee_zero_eq x _).symm)

/-- `x ⋁ x = x` forces `x = 0`. -/
theorem eq_zero_of_ovee_self {x : E} (h : Perp x x) (e : ovee x x h = x) : x = 0 :=
  eq_zero_of_ovee_eq_self h e

/-- `(a ⋁ b)⊥ ⋁ b = a⊥`, i.e. `a⊥ = b ⋁ (a ⋁ b)⊥`. -/
theorem orth_left_eq {a b : E} (h : Perp a b) :
    ∃ h' : Perp b (orth (ovee a b h)), ovee b (orth (ovee a b h)) h' = orth a := by
  have h1 : Perp (ovee a b h) (orth (ovee a b h)) := EffectAlgebra.perp_orth _
  refine ⟨PCM.perp_of_ovee_perp h h1, ?_⟩
  refine (EffectAlgebra.orth_unique (PCM.perp_ovee_of_ovee_perp h h1) ?_)
  rw [← PCM.ovee_assoc h h1]; exact EffectAlgebra.ovee_orth _

/-- The sum `a ⋁ b` is monotone in `b`. -/
theorem ovee_le_ovee_right {a b c : E} (hbc : b ≼ c) (h : Perp a c) :
    ∃ h' : Perp a b, ovee a b h' ≼ ovee a c h := by
  have := eabasics_le_perp_compat hbc (PCM.perp_comm h)
  obtain ⟨h1, hle⟩ := this
  refine ⟨PCM.perp_comm h1, ?_⟩
  rw [PCM.ovee_comm (PCM.perp_comm h1), PCM.ovee_comm h]
  exact hle

/-- Order cancellation: `a ⋁ b ≼ a ⋁ c` implies `b ≼ c`. -/
theorem le_of_ovee_le_ovee {a b c : E} (h1 : Perp a b) (h2 : Perp a c)
    (hle : ovee a b h1 ≼ ovee a c h2) : b ≼ c := by
  obtain ⟨d, hd, e⟩ := hle
  have e' := PCM.ovee_assoc h1 hd
  refine ⟨d, PCM.perp_of_ovee_perp h1 hd, ?_⟩
  exact cancel_left _ h2 (e'.symm.trans e)

/-- The difference `b ⊖ a` (for `a ≼ b`) satisfies `a ⋁ (b ⊖ a) = b`. -/
theorem ovee_ominus {a b : E} (h : a ≼ b) :
    ∃ h' : Perp a (ominus b a h), ovee a (ominus b a h) h' = b := isDiff_ominus h

/-- `b ⊖ a` is the unique `c` with `a ⋁ c = b`. -/
theorem ominus_eq {a b c : E} (hab : a ≼ b) (h : Perp a c) (e : ovee a c h = b) :
    ominus b a hab = c := isDiff_unique (isDiff_ominus hab) ⟨h, e⟩

/-- **SEA 1** (second.tex:219, Definition): an effect algebra is the theses'
`EffectAlgebra` (eff.tex 175I — commutativity, zero, associativity,
orthocomplement, zero-one law; the same five axioms).  The consequences the
definition lists: `≼` is a partial order with minimum `0` and maximum `1`,
`a ↦ a⊥` is an order anti-isomorphism, `a ⊥ b` iff `a ≼ b⊥`, and the `c` with
`a ⋁ c = b` is unique (`b ⊖ a`). -/
theorem sea1_order :
    (∀ a : E, a ≼ a) ∧ (∀ a b c : E, a ≼ b → b ≼ c → a ≼ c) ∧
    (∀ a b : E, a ≼ b → b ≼ a → a = b) ∧ (∀ a : E, (0 : E) ≼ a ∧ a ≼ 1) ∧
    (∀ a b : E, a ≼ b ↔ orth b ≼ orth a) ∧ Function.Bijective (orth : E → E) ∧
    (∀ a b : E, Perp a b ↔ a ≼ orth b) ∧
    (∀ a b c c' : E, IsDiff b a c → IsDiff b a c' → c = c') :=
  ⟨le_refl', fun _ _ _ => le_trans', fun _ _ => le_antisymm', fun a => ⟨zero_le' a, le_one' a⟩,
    fun _ _ => eabasics_le_iff_orth_le,
    ⟨fun a b h => by rw [← orth_orth a, h, orth_orth], fun a => ⟨orth a, orth_orth a⟩⟩,
    fun _ _ => perp_iff_le_orth, fun _ _ _ _ => isDiff_unique⟩

-- **SEA 2** (second.tex:247, Remark): terminology only ("summable" for `⊥`,
-- `⋁` for the sum); no declaration.

/-- **SEA 7** (second.tex:309, Proposition): in any effect algebra
(1) `a⊥⊥ = a`; (2) `a ⋁ b = 0` implies `a = b = 0`; (3) `a ⋁ b = a ⋁ c`
implies `b = c`; (4) `a ≼ b` iff `b⊥ ≼ a⊥`; (5) `a ⊥ b` iff `a ≼ b⊥`.
These are eff.tex 175V, cited by the paper as `[basthesis, §175V]`. -/
theorem sea7_basic :
    (∀ a : E, orth (orth a) = a) ∧
    (∀ (a b : E) (h : Perp a b), ovee a b h = 0 → a = 0 ∧ b = 0) ∧
    (∀ (a b c : E) (h1 : Perp a b) (h2 : Perp a c), ovee a b h1 = ovee a c h2 → b = c) ∧
    (∀ a b : E, a ≼ b ↔ orth b ≼ orth a) ∧
    (∀ a b : E, Perp a b ↔ a ≼ orth b) :=
  ⟨orth_orth, fun _ _ h => eabasics_positivity h, fun _ _ _ => cancel_left,
    fun _ _ => eabasics_le_iff_orth_le, fun _ _ => perp_iff_le_orth⟩

end EABasics

/-! ### Examples of effect algebras (SEA 3–6) -/

section EAExamples

/-- In the effect algebra of a Boolean algebra, `≼` is the lattice order. -/
theorem boolean_le_iff {L : Type u} [BooleanAlgebra L] (a b : L) :
    @PCM.le L (booleanEffectAlgebra L).toPCM a b ↔ a ≤ b := by
  let _ := booleanEffectAlgebra L
  constructor
  · rintro ⟨c, _, rfl⟩
    exact le_sup_left (a := a) (b := c)
  · intro h
    refine ⟨b \ a, (show a ⊓ b \ a = ⊥ from inf_sdiff_self_right), ?_⟩
    show a ⊔ b \ a = b
    exact sup_sdiff_cancel_right h

/-- **SEA 3** (`ex:orthomodularlattice`, second.tex:258, Example): a Boolean
algebra `B` is an effect algebra with `x ⊥ y` iff `x ∧ y = 0`, `x ⋁ y = x ∨ y`,
`x⊥` the complement (the theses' `booleanEffectAlgebra`, eff.tex 175II.5),
and the effect-algebra order is the lattice order.  The parenthetical
generalisation to orthomodular posets is false as printed
(`sea3_orthomodular_false_as_printed`); repaired, for orthomodular lattices,
in `sea3_orthomodular_repaired`. -/
theorem sea3_boolean (L : Type u) [BooleanAlgebra L] :
    (∀ x y : L, @Perp L (booleanEffectAlgebra L).toPCM x y ↔ x ⊓ y = ⊥) ∧
    (∀ (x y : L) (h : @Perp L (booleanEffectAlgebra L).toPCM x y),
      @ovee L (booleanEffectAlgebra L).toPCM x y h = x ⊔ y) ∧
    (∀ x : L, @orth L (booleanEffectAlgebra L) x = xᶜ) ∧
    (∀ x y : L, @PCM.le L (booleanEffectAlgebra L).toPCM x y ↔ x ≤ y) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ => rfl, boolean_le_iff⟩

/-- The orthomodular lattice `MO2` ("Chinese lantern"): `⊥ < a, a', b, b' < ⊤`
with `a^⊥ = a'`, `b^⊥ = b'` (the same witness the OAP formalisation uses for
OAP 2, repeated here since `Papers.OAP` cannot be imported). -/
inductive MO2 where
  | bot | top | a | a' | b | b'
  deriving DecidableEq

namespace MO2

/-- The order of `MO2`, as a boolean table. -/
def leb : MO2 → MO2 → Bool
  | bot, _ => true
  | _, top => true
  | x, y => decide (x = y)

instance : LE MO2 := ⟨fun x y => leb x y = true⟩

instance : DecidableRel (α := MO2) (· ≤ ·) := fun x y =>
  inferInstanceAs (Decidable (leb x y = true))

instance : Fintype MO2 where
  elems := ⟨[bot, top, a, a', b, b'], by decide⟩
  complete := by intro x; cases x <;> decide

def sup' (x y : MO2) : MO2 := if leb x y then y else if leb y x then x else top

def inf' (x y : MO2) : MO2 := if leb x y then x else if leb y x then y else bot

def compl' : MO2 → MO2
  | bot => top | top => bot | a => a' | a' => a | b => b' | b' => b

instance : Lattice MO2 where
  le := (· ≤ ·)
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  sup := sup'
  inf := inf'
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : BoundedOrder MO2 where
  top := top
  le_top := by decide
  bot := bot
  bot_le := by decide

instance : Compl MO2 := ⟨compl'⟩

instance : OrthomodularLattice MO2 where
  inf_compl := by decide
  sup_compl := by decide
  compl_antitone := by decide
  compl_compl := by decide
  orthomodular := by decide

end MO2

/-- **SEA 3** (`ex:orthomodularlattice`, second.tex:258, Example), the
parenthetical "or more generally, an orthomodular poset" — **false as
printed**: with `x ⊥ y ⟺ x ∧ y = 0`, `x ⋁ y = x ∨ y` and the orthocomplement,
the orthomodular lattice `MO2` is not an effect algebra (`a ∧ b = 0`,
`a ∨ b = 1`, but `b ≠ a^⊥`).  The same slip as OAP 2 (the example is copied
from there).  Repaired: `x ⊥ y ⟺ x ≤ y^⊥`, `sea3_orthomodular_repaired`. -/
theorem sea3_orthomodular_false_as_printed :
    ∃ (L : Type) (_ : OrthomodularLattice L),
      ¬ ∃ inst : EffectAlgebra L,
        (∀ x y : L, @Perp L inst.toPCM x y ↔ x ⊓ y = ⊥) ∧
        (∀ (x y : L) (h : @Perp L inst.toPCM x y), @ovee L inst.toPCM x y h = x ⊔ y) ∧
        ∀ x : L, @orth L inst x = xᶜ := by
  refine ⟨MO2, inferInstance, ?_⟩
  rintro ⟨inst, hP, hO, hC⟩
  have hab : @Perp MO2 inst.toPCM MO2.a MO2.b := (hP _ _).2 (by decide)
  have hone := @EffectAlgebra.ovee_orth MO2 inst MO2.a
  rw [hO, hC] at hone
  have e : @ovee MO2 inst.toPCM _ _ hab = 1 := by
    rw [hO, ← hone]; decide
  have := @EffectAlgebra.orth_unique MO2 inst _ _ hab e
  rw [hC] at this
  exact absurd this (by decide)

/-- **SEA 3** (`ex:orthomodularlattice`, second.tex:258, Example), repaired
for orthomodular lattices: with `x ⊥ y ⟺ x ≤ y^⊥` (the theses'
`orthomodularEffectAlgebra`, eff.tex 175II.4) the effect-algebra order is the
lattice order. -/
theorem sea3_orthomodular_repaired (L : Type u) [OrthomodularLattice L] (x y : L) :
    @PCM.le L (orthomodularEffectAlgebra L).toPCM x y ↔ x ≤ y := by
  let _ := orthomodularEffectAlgebra L
  constructor
  · rintro ⟨c, -, rfl⟩; exact le_sup_left
  · intro h
    refine ⟨xᶜ ⊓ y, ?_, OrthomodularLattice.orthomodular h⟩
    show x ≤ (xᶜ ⊓ y)ᶜ
    exact Ortholattice.le_compl_comm inf_le_left

/-- In the interval effect algebra `[0,u]_G`, `≼` is the order of `G`. -/
theorem interval_le_iff {G : Type u} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    (w : G) (hw : 0 ≤ w) (a b : Set.Icc (0 : G) w) :
    @PCM.le _ (orderIntervalEffectAlgebra G w hw).toPCM a b ↔ (a : G) ≤ b := by
  let _ := orderIntervalEffectAlgebra G w hw
  constructor
  · rintro ⟨c, _, rfl⟩
    show (a : G) ≤ (a : G) + c
    exact le_add_of_nonneg_right c.2.1
  · intro h
    refine ⟨⟨(b : G) - a, sub_nonneg.mpr h, le_trans (sub_le_self _ a.2.1) b.2.2⟩, ?_, ?_⟩
    · show (a : G) + ((b : G) - a) ≤ w
      rw [add_sub_cancel]; exact b.2.2
    · apply Subtype.ext
      show (a : G) + ((b : G) - a) = b
      rw [add_sub_cancel]

/-- **SEA 4** (`ex:cstaralgebra`, second.tex:270, Example): for an ordered
abelian group `G` and `u ≥ 0`, `[0,u]_G` is an effect algebra with `a ⊥ b`
iff `a + b ≤ u`, `a ⋁ b = a + b`, `a⊥ = u - a` (the theses'
`orderIntervalEffectAlgebra`, eff.tex 175II.2), and its effect-algebra order
is the order of `G`.  The C*-algebra case `[0,1]_C` is the instance
`G = C`, `u = 1`. -/
theorem sea4_interval {G : Type u} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    (w : G) (hw : 0 ≤ w) :
    (∀ a b : Set.Icc (0 : G) w,
      @Perp _ (orderIntervalEffectAlgebra G w hw).toPCM a b ↔ (a : G) + b ≤ w) ∧
    (∀ (a b : Set.Icc (0 : G) w) (h : @Perp _ (orderIntervalEffectAlgebra G w hw).toPCM a b),
      ((@ovee _ (orderIntervalEffectAlgebra G w hw).toPCM a b h : Set.Icc (0 : G) w) : G)
        = a + b) ∧
    (∀ a : Set.Icc (0 : G) w, ((@orth _ (orderIntervalEffectAlgebra G w hw) a :
        Set.Icc (0 : G) w) : G) = w - a) ∧
    (∀ a b : Set.Icc (0 : G) w,
      @PCM.le _ (orderIntervalEffectAlgebra G w hw).toPCM a b ↔ (a : G) ≤ b) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ => rfl, interval_le_iff w hw⟩

-- **SEA 5** (second.tex:293, Remark): GPT motivation; no declaration.

/-- **SEA 6** (`eaprod`, second.tex:297, Example): the direct sum `E ⊕ F`
with componentwise operations is an effect algebra — the theses'
`prodEffectAlgebra` (eff.tex 175III), whose categorical-product property (the
footnote) is `ea_product_categorical`. -/
theorem sea6_prod (E F : Type u) [EffectAlgebra E] [EffectAlgebra F] :
    (∀ p q : E × F, Perp p q ↔ Perp p.1 q.1 ∧ Perp p.2 q.2) ∧
    (∀ (p q : E × F) (h : Perp p q), ovee p q h = (ovee p.1 q.1 h.1, ovee p.2 q.2 h.2)) ∧
    (∀ p : E × F, orth p = (orth p.1, orth p.2)) ∧ ((1 : E × F) = (1, 1)) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ => rfl, rfl⟩

end EAExamples

/-! ## Convex effect algebras (SEA 8–10) -/

/-- **SEA 8** (`def:convex`, second.tex:322, Definition): a *convex action*
on an effect algebra `E` is a map `[0,1] × E → E` with `λ(μa) = (λμ)a`,
`λa ⊥ μa` and `λa ⋁ μa = (λ+μ)a` when `λ + μ ≤ 1`, `1a = a`, and
`λ(a ⋁ b) = λa ⋁ λb`.  These are exactly the axioms of an effect module over
the effect monoid `[0,1]` (the theses' `EffectModule I E`, eff.tex 179II),
whose `λ ⊥ μ` in `[0,1]` means `λ + μ ≤ 1` and `λ ⋁ μ = λ + μ`. -/
abbrev ConvexAction (E : Type u) [EffectAlgebra E] := EffectModule I E

/-- **SEA 8** (`def:convex`, second.tex:322, Definition): an effect algebra
is *convex* when it carries at least one convex action. -/
def IsConvex (E : Type u) [EffectAlgebra E] : Prop := Nonempty (ConvexAction E)

/-- **SEA 8**: the action axioms spelled out as printed, for any convex
action. -/
theorem convexAction_axioms {E : Type u} [EffectAlgebra E] [ConvexAction E] :
    (∀ (l m : I) (a : E), l • (m • a) = (l * m) • a) ∧
    (∀ (l m : I) (a : E) (h : (l : ℝ) + m ≤ 1),
      ∃ h' : Perp (l • a) (m • a), ((ovee (l • a) (m • a) h' : E) =
        (⟨(l : ℝ) + m, add_nonneg l.2.1 m.2.1, h⟩ : I) • a)) ∧
    (∀ a : E, (1 : I) • a = a) ∧
    (∀ (l : I) (a b : E) (h : Perp a b),
      ∃ h' : Perp (l • a) (l • b), l • ovee a b h = ovee (l • a) (l • b) h') := by
  refine ⟨fun l m a => (EffectModule.mul_smul l m a).symm, fun l m a h => ?_,
    EffectModule.one_smul, fun l a b h => ?_⟩
  · obtain ⟨h', e⟩ := EffectModule.perp_smul (M := I) (show Perp l m from h) a
    exact ⟨h', e⟩
  · obtain ⟨h', e⟩ := EffectModule.smul_perp (E := E) l h
    exact ⟨h', e.symm⟩

/-- **SEA 9** (second.tex:345, Example), first half: for an ordered real
vector space `V` and `u ≥ 0`, `[0,u]_V` is a convex effect algebra with the
obvious action (the theses' `orderIntervalEffectModule`, eff.tex 179III.2).
The converse — every convex effect algebra is `[0,u]_V` — is the theses'
`effectModule_unitInterval_representation` (Gudder–Pulmannová, eff.tex
179III.2), with `u` an order unit. -/
theorem sea9_interval_convex (V : Type u) [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [IsOrderedAddMonoid V] [PosSMulMono ℝ V] [SMulPosMono ℝ V] (w : V) (hw : 0 ≤ w) :
    @IsConvex _ (orderIntervalEffectAlgebra V w hw) :=
  ⟨orderIntervalEffectModule V w hw⟩

-- **SEA 10** (second.tex:350, Remark): literature; no declaration.

/-! ## Directed completeness (SEA 11–14) -/

section Directed

variable {E : Type u} [EffectAlgebra E]

/-- **SEA 11** (second.tex:360, Definition): a subset `S` of an effect
algebra is *directed* when it is non-empty and any two elements of `S` have
an upper bound in `S` (for the effect-algebra order `≼`). -/
def EDirected (S : Set E) : Prop :=
  S.Nonempty ∧ ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≼ c ∧ b ≼ c

/-- `x` is the supremum of `S` for `≼`. -/
def EIsSup (S : Set E) (x : E) : Prop :=
  (∀ s ∈ S, s ≼ x) ∧ ∀ y, (∀ s ∈ S, s ≼ y) → x ≼ y

/-- `x` is the infimum of `S` for `≼`. -/
def EIsInf (S : Set E) (x : E) : Prop :=
  (∀ s ∈ S, x ≼ s) ∧ ∀ y, (∀ s ∈ S, y ≼ s) → y ≼ x

/-- A *filtered* (downwards directed) subset. -/
def EFiltered (S : Set E) : Prop :=
  S.Nonempty ∧ ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, c ≼ a ∧ c ≼ b

/-- **SEA 11** (second.tex:360, Definition): `E` is *directed complete* when
every directed subset has a supremum. -/
def DirectedComplete (E : Type u) [EffectAlgebra E] : Prop :=
  ∀ S : Set E, EDirected S → ∃ x, EIsSup S x

theorem EIsSup.unique {S : Set E} {x y : E} (hx : EIsSup S x) (hy : EIsSup S y) : x = y :=
  le_antisymm' (hx.2 y hy.1) (hy.2 x hx.1)

theorem EIsInf.unique {S : Set E} {x y : E} (hx : EIsInf S x) (hy : EIsInf S y) : x = y :=
  le_antisymm' (hy.2 x hx.1) (hx.2 y hy.1)

/-- A chain of the form `n ↦ f n`, monotone, is directed. -/
theorem eDirected_range_of_monotone {f : ℕ → E} (hf : ∀ n, f n ≼ f (n + 1)) :
    EDirected (Set.range f) := by
  have mono : ∀ n m, n ≤ m → f n ≼ f m := by
    intro n m hnm
    induction hnm with
    | refl => exact le_refl' _
    | step _ ih => exact le_trans' ih (hf _)
  refine ⟨⟨f 0, 0, rfl⟩, ?_⟩
  rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
  exact ⟨f (max n m), ⟨_, rfl⟩, mono _ _ (le_max_left _ _), mono _ _ (le_max_right _ _)⟩

/-- `orth` carries suprema to infima. -/
theorem eIsInf_orth_of_eIsSup {S : Set E} {x : E} (h : EIsSup S x) :
    EIsInf (orth '' S) (orth x) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩; exact orth_le_orth (h.1 s hs)
  · intro y hy
    have : x ≼ orth y := h.2 _ (fun s hs => by
      have := orth_le_orth (hy (orth s) ⟨s, hs, rfl⟩)
      rwa [orth_orth] at this)
    have := orth_le_orth this
    rwa [orth_orth] at this

/-- `orth` carries infima to suprema. -/
theorem eIsSup_orth_of_eIsInf {S : Set E} {x : E} (h : EIsInf S x) :
    EIsSup (orth '' S) (orth x) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩; exact orth_le_orth (h.1 s hs)
  · intro y hy
    have : orth y ≼ x := h.2 _ (fun s hs => by
      have := orth_le_orth (hy (orth s) ⟨s, hs, rfl⟩)
      rwa [orth_orth] at this)
    have := orth_le_orth this
    rwa [orth_orth] at this

theorem orth_image_orth (S : Set E) : orth '' (orth '' S) = S := by
  ext x; simp [orth_orth]

/-- **SEA 14** (`remark:infima`, second.tex:389, Remark): because `(·)⊥` is an
order anti-isomorphism, a directed-complete effect algebra has infima of all
filtered sets. -/
theorem exists_inf_of_filtered (hE : DirectedComplete E) {S : Set E} (hS : EFiltered S) :
    ∃ x, EIsInf S x := by
  have hD : EDirected (orth '' S) := by
    obtain ⟨⟨s, hs⟩, h⟩ := hS
    refine ⟨⟨orth s, s, hs, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hca, hcb⟩ := h a ha b hb
    exact ⟨orth c, ⟨c, hc, rfl⟩, orth_le_orth hca, orth_le_orth hcb⟩
  obtain ⟨x, hx⟩ := hE _ hD
  refine ⟨orth x, ?_⟩
  have := eIsInf_orth_of_eIsSup hx
  rwa [orth_image_orth] at this

/-- **SEA 14** (`remark:infima`, second.tex:389, Remark), the special case the
paper singles out: a decreasing sequence in a directed-complete effect algebra
has an infimum. -/
theorem exists_inf_of_antitone (hE : DirectedComplete E) {f : ℕ → E}
    (hf : ∀ n, f (n + 1) ≼ f n) : ∃ x, EIsInf (Set.range f) x := by
  refine exists_inf_of_filtered hE ⟨⟨f 0, 0, rfl⟩, ?_⟩
  have mono : ∀ n m, n ≤ m → f m ≼ f n := by
    intro n m hnm
    induction hnm with
    | refl => exact le_refl' _
    | step _ ih => exact le_trans' (hf _) ih
  rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
  exact ⟨f (max n m), ⟨_, rfl⟩, mono _ _ (le_max_left _ _), mono _ _ (le_max_right _ _)⟩

end Directed

/-- **SEA 12** (second.tex:369, Example): a complete Boolean algebra is a
directed-complete effect algebra (with the effect algebra of SEA 3). -/
theorem sea12_completeBoolean_directedComplete (L : Type u) [CompleteBooleanAlgebra L] :
    @DirectedComplete L (booleanEffectAlgebra L) := by
  let _ := booleanEffectAlgebra L
  intro S _
  refine ⟨sSup S, fun s hs => (boolean_le_iff s _).mpr (le_sSup hs), fun y hy => ?_⟩
  exact (boolean_le_iff _ y).mpr (sSup_le fun s hs => (boolean_le_iff s y).mp (hy s hs))


/-! ### Sums of lists, suprema of sums (SEA 20, 21) -/

section Sums

variable {E : Type u} [EffectAlgebra E]

/-- A list has at most one sum. -/
theorem isSumOf_unique {l : List E} {s t : E} (hs : PCM.IsSumOf l s) (ht : PCM.IsSumOf l t) :
    s = t := by
  induction l generalizing s t with
  | nil => rw [PCM.isSumOf_nil_iff.mp hs, PCM.isSumOf_nil_iff.mp ht]
  | cons x l ih =>
    obtain ⟨s', hs', h1, rfl⟩ := PCM.isSumOf_cons_iff.mp hs
    obtain ⟨t', ht', h2, rfl⟩ := PCM.isSumOf_cons_iff.mp ht
    exact PCM.ovee_congr rfl (ih hs' ht') _ _

/-- Sums of concatenated lists. -/
theorem isSumOf_append {l l' : List E} {s t : E} (hs : PCM.IsSumOf l s)
    (ht : PCM.IsSumOf l' t) (h : Perp s t) : PCM.IsSumOf (l ++ l') (ovee s t h) := by
  induction l generalizing s with
  | nil =>
    have hs0 := PCM.isSumOf_nil_iff.mp hs
    subst hs0
    rw [zero_ovee_eq]; exact ht
  | cons x l ih =>
    obtain ⟨s', hs', h1, rfl⟩ := PCM.isSumOf_cons_iff.mp hs
    have := ih hs' (PCM.perp_of_ovee_perp h1 h)
    rw [PCM.ovee_assoc h1 h]
    exact PCM.IsSumOf.cons this _

/-- Every prefix of a summable list is summable, with a smaller sum. -/
theorem isSumOf_prefix {l l' : List E} {s : E} (hs : PCM.IsSumOf (l ++ l') s) :
    ∃ t, PCM.IsSumOf l t ∧ t ≼ s := by
  induction l generalizing s with
  | nil => exact ⟨0, PCM.IsSumOf.nil, zero_le' s⟩
  | cons x l ih =>
    obtain ⟨s', hs', h1, rfl⟩ := PCM.isSumOf_cons_iff.mp hs
    obtain ⟨t, ht, hle⟩ := ih hs'
    obtain ⟨h2, hle2⟩ := ovee_le_ovee_right hle h1
    exact ⟨ovee x t h2, PCM.IsSumOf.cons ht h2, hle2⟩

theorem isSumOf_replicate_succ {n : ℕ} {a s : E} :
    PCM.IsSumOf (List.replicate (n + 1) a) s ↔
      ∃ t, PCM.IsSumOf (List.replicate n a) t ∧ ∃ h : Perp a t, ovee a t h = s := by
  rw [List.replicate_succ, PCM.isSumOf_cons_iff]
  constructor
  · rintro ⟨t, ht, h, e⟩; exact ⟨t, ht, h, e⟩
  · rintro ⟨t, ht, h, e⟩; exact ⟨t, ht, h, e⟩

/-- The sum `a ⋁ ⋁S = ⋁ₛ (a ⋁ s)` for a non-empty `S` whose supremum exists
(the content of SEA 20, without directed completeness). -/
theorem ovee_isSup {S : Set E} {x a : E} (hne : S.Nonempty) (hx : EIsSup S x)
    (ha : ∀ s ∈ S, Perp a s) :
    ∃ h : Perp a x, EIsSup {y | ∃ s ∈ S, ∃ h : Perp a s, ovee a s h = y} (ovee a x h) := by
  have hxa : x ≼ orth a := hx.2 _ (fun s hs => perp_iff_le_orth.mp (PCM.perp_comm (ha s hs)))
  have hax : Perp a x := PCM.perp_comm (perp_iff_le_orth.mpr hxa)
  refine ⟨hax, ?_, ?_⟩
  · rintro _ ⟨s, hs, h, rfl⟩
    obtain ⟨h', hle⟩ := ovee_le_ovee_right (hx.1 s hs) hax
    exact hle
  · intro y hy
    obtain ⟨s0, hs0⟩ := hne
    have hay : a ≼ y := le_trans' (left_le_ovee (ha s0 hs0)) (hy _ ⟨s0, hs0, ha s0 hs0, rfl⟩)
    obtain ⟨hd, ed⟩ := ovee_ominus hay
    have hxd : x ≼ ominus y a hay := hx.2 _ (fun s hs => by
      refine le_of_ovee_le_ovee (ha s hs) hd ?_
      rw [ed]; exact hy _ ⟨s, hs, ha s hs, rfl⟩)
    obtain ⟨h', hle⟩ := ovee_le_ovee_right hxd hd
    rw [ed] at hle
    exact hle

/-- **SEA 20** (`lem:addition-normal`, second.tex:630, Lemma): in a
directed-complete effect algebra, if `S` is directed and `a ⊥ s` for all
`s ∈ S`, then `a ⊥ ⋁S` and `a ⋁ ⋁S = ⋁_{s∈S} a ⋁ s`.  Proof as printed:
`b ↦ a ⋁ b` is an order isomorphism `[0,a⊥] → [a,1]` (inverse `b ↦ b ⊖ a`),
so it preserves suprema. -/
theorem sea20_ovee_sup (hE : DirectedComplete E) {S : Set E} (hS : EDirected S) {a : E}
    (ha : ∀ s ∈ S, Perp a s) :
    ∃ x, EIsSup S x ∧ ∃ h : Perp a x,
      EIsSup {y | ∃ s ∈ S, ∃ h : Perp a s, ovee a s h = y} (ovee a x h) := by
  obtain ⟨x, hx⟩ := hE S hS
  exact ⟨x, hx, ovee_isSup hS.1 hx ha⟩

/-- **SEA 21** (`lem:archemedeanomegadirectedcomplete`, second.tex:645,
Lemma): the only element `a` of a directed-complete effect algebra whose
`n`-fold sum `na` exists for every `n` is `0`.  Proof as printed:
`a ⋁ ⋁ₙ na = ⋁ₙ (n+1)a = ⋁ₙ na`, so `a = 0` by cancellation. -/
theorem sea21_archimedean (hE : DirectedComplete E) {a : E}
    (h : ∀ n : ℕ, ∃ x, PCM.IsSumOf (List.replicate n a) x) : a = 0 := by
  choose f hf using h
  have hsucc : ∀ n, ∃ hp : Perp a (f n), ovee a (f n) hp = f (n + 1) := by
    intro n
    obtain ⟨t, ht, hp, e⟩ := isSumOf_replicate_succ.mp (hf (n + 1))
    have := isSumOf_unique ht (hf n)
    subst this
    exact ⟨hp, e⟩
  have hf0 : f 0 = 0 := PCM.isSumOf_nil_iff.mp (hf 0)
  have hmono : ∀ n, f n ≼ f (n + 1) := by
    intro n; obtain ⟨hp, e⟩ := hsucc n; rw [← e]; exact right_le_ovee hp
  have hD := eDirected_range_of_monotone hmono
  have ha : ∀ s ∈ Set.range f, Perp a s := by
    rintro _ ⟨n, rfl⟩; exact (hsucc n).1
  obtain ⟨u, hu, hau, hsup⟩ := sea20_ovee_sup hE hD ha
  -- the sums `a ⋁ f n` are exactly the `f (n+1)`, whose supremum is again `u`
  have hsup' : EIsSup {y | ∃ s ∈ Set.range f, ∃ h : Perp a s, ovee a s h = y} u := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨n, rfl⟩, hp, rfl⟩
      have e := (hsucc n).2
      rw [PCM.ovee_congr rfl rfl hp (hsucc n).1, e]
      exact hu.1 _ ⟨n + 1, rfl⟩
    · intro y hy
      refine hu.2 y ?_
      rintro _ ⟨n, rfl⟩
      cases n with
      | zero => rw [hf0]; exact zero_le' y
      | succ n =>
        have := hy _ ⟨f n, ⟨n, rfl⟩, (hsucc n).1, rfl⟩
        rwa [(hsucc n).2] at this
  have e : ovee a u hau = u := hsup.unique hsup'
  refine eabasics_cancellation hau (PCM.zero_perp u) ?_
  rw [e, zero_ovee_eq]

end Sums

/-! ## Sequential effect algebras (SEA 15–28) -/

/-- **SEA 15** (`defn:sea`, second.tex:411, Definition): a *sequential effect
algebra* is an effect algebra with a total binary operation `⊙` such that

* (S1) `a ⊙ (b ⋁ c) = a ⊙ b ⋁ a ⊙ c` whenever `b ⊥ c`;
* (S2) `1 ⊙ a = a`;
* (S3) `a ⊙ b = 0` implies `b ⊙ a = 0`;
* (S4) if `a | b` then `a | b⊥` and `a ⊙ (b ⊙ c) = (a ⊙ b) ⊙ c`;
* (S5) if `c | a` and `c | b` then `c | a ⊙ b`, and if moreover `a ⊥ b`
  then `c | a ⋁ b`,

where `a | b` ("`a` and `b` commute") means `a ⊙ b = b ⊙ a`.

We extend the theses' `SequentialEffectAlgebra` (eff.tex 225IV), which
carries S1–S4 and the part of S5 asserted *under* `a ⊥ b`; the field
`seq_comm_seq` adds the half of S5 that the paper asserts for *all* `a, b`
(eff.tex asks `c | a ⊙ b` only for summable `a, b`). -/
class SEAlgebra (E : Type u) [EffectAlgebra E] extends SequentialEffectAlgebra E where
  /-- (S5), first half, for arbitrary `a, b`: `c | a` and `c | b` give
  `c | a ⊙ b`. -/
  seq_comm_seq : ∀ {a b c : E}, seq c a = seq a c → seq c b = seq b c →
    seq c (seq a b) = seq (seq a b) c

/-- The sequential product `a ⊙ b` (the paper's `a ∘ b`). -/
scoped infixl:70 " ⊙ " => SequentialEffectAlgebra.seq

section SEADefs

variable {E : Type u} [EffectAlgebra E] [SEAlgebra E]

/-- **SEA 15**: `a` and `b` *commute*, `a | b`, when `a ⊙ b = b ⊙ a`. -/
def Commutes (a b : E) : Prop := a ⊙ b = b ⊙ a

/-- **SEA 15**: `E` is *commutative* when all its elements commute. -/
def IsCommutativeSEA (E : Type u) [EffectAlgebra E] [SEAlgebra E] : Prop := ∀ a b : E, Commutes a b

/-- **SEA 15**: `a` is *central* when it commutes with every element. -/
def IsCentral (a : E) : Prop := ∀ b : E, Commutes a b

/-- **SEA 15**: the *centre* `Z(E)`, the set of central elements. -/
def center (E : Type u) [EffectAlgebra E] [SEAlgebra E] : Set E := {a | IsCentral a}

/-- **SEA 15**: `p` is an *idempotent* when `p ⊙ p = p`. -/
def IsIdempotent (p : E) : Prop := p ⊙ p = p

/-- **SEA 15**: `E` is *Boolean* when every element is an idempotent. -/
def IsBooleanSEA (E : Type u) [EffectAlgebra E] [SEAlgebra E] : Prop := ∀ a : E, IsIdempotent a

/-- **SEA 15**: `a` and `b` are *orthogonal* when `a ⊙ b = 0`. -/
def Orthogonal (a b : E) : Prop := a ⊙ b = 0

end SEADefs

/-- **SEA 15** (`defn:sea`, second.tex:411, Definition): a SEA is *normal*
when it is directed complete and

* (S6) for directed `S`, `a ⊙ ⋁S = ⋁_{s∈S} a ⊙ s`, and `a | ⋁S` when
  `a | s` for all `s ∈ S`.

(The first half of S6 is stated as "`a ⊙ ⋁S` is the supremum of
`{a ⊙ s}`", which asserts the existence of the right-hand side.) -/
class NormalSEA (E : Type u) [EffectAlgebra E] extends SEAlgebra E where
  directedComplete : DirectedComplete E
  seq_sup : ∀ (a : E) {S : Set E} {x : E}, EDirected S → EIsSup S x →
    EIsSup (seq a '' S) (seq a x)
  comm_sup : ∀ (a : E) {S : Set E} {x : E}, EDirected S → EIsSup S x →
    (∀ s ∈ S, seq a s = seq s a) → seq a x = seq x a

section SEABasics

variable {E : Type u} [EffectAlgebra E] [SEAlgebra E]

/-! ### The axioms as lemmas -/

theorem seq_ovee (c : E) {a b : E} (h : Perp a b) :
    ∃ h' : Perp (c ⊙ a) (c ⊙ b), c ⊙ ovee a b h = ovee (c ⊙ a) (c ⊙ b) h' := by
  obtain ⟨h', e⟩ := SequentialEffectAlgebra.seq_add c h
  exact ⟨h', e.symm⟩

theorem seq_perp (c : E) {a b : E} (h : Perp a b) : Perp (c ⊙ a) (c ⊙ b) :=
  (seq_ovee c h).1

theorem seq_ovee_eq (c : E) {a b : E} (h : Perp a b) (h' : Perp (c ⊙ a) (c ⊙ b)) :
    c ⊙ ovee a b h = ovee (c ⊙ a) (c ⊙ b) h' := (seq_ovee c h).2

theorem one_seq (a : E) : (1 : E) ⊙ a = a := SequentialEffectAlgebra.one_seq a

theorem seq_zero_comm {a b : E} (h : a ⊙ b = 0) : b ⊙ a = 0 :=
  SequentialEffectAlgebra.seq_zero_comm a b h

theorem Commutes.symm {a b : E} (h : Commutes a b) : Commutes b a := Eq.symm h

theorem commutes_refl (a : E) : Commutes a a := rfl

theorem Commutes.orth_r {a b : E} (h : Commutes a b) : Commutes a (orth b) :=
  SequentialEffectAlgebra.seq_comm_orth h

theorem Commutes.orth_l {a b : E} (h : Commutes a b) : Commutes (orth a) b :=
  Eq.symm (Commutes.orth_r (Eq.symm h))

theorem Commutes.of_orth_r {a b : E} (h : Commutes a (orth b)) : Commutes a b := by
  have := h.orth_r; rwa [orth_orth] at this

theorem Commutes.assoc {a b : E} (h : Commutes a b) (c : E) : a ⊙ (b ⊙ c) = (a ⊙ b) ⊙ c :=
  (SequentialEffectAlgebra.seq_comm_assoc h c).symm

theorem Commutes.seq {a b c : E} (ha : Commutes c a) (hb : Commutes c b) :
    Commutes c (a ⊙ b) := SEAlgebra.seq_comm_seq ha hb

theorem Commutes.ovee {a b c : E} (h : Perp a b) (ha : Commutes c a) (hb : Commutes c b) :
    Commutes c (ovee a b h) := (SequentialEffectAlgebra.seq_comm_compat h ha hb).2

/-! ### SEA 17 -/

/-- **SEA 17.1** (`prop:SEAbasicproperties`, second.tex:490, Proposition):
`a ⊙ 0 = 0`. -/
theorem seq_zero (a : E) : a ⊙ (0 : E) = 0 := by
  have h00 : Perp (0 : E) 0 := PCM.zero_perp 0
  obtain ⟨h', e⟩ := seq_ovee a h00
  rw [zero_ovee_eq] at e
  exact eq_zero_of_ovee_self h' e.symm

/-- **SEA 17.1**: `0 ⊙ a = 0` (by S3). -/
theorem zero_seq (a : E) : (0 : E) ⊙ a = 0 := seq_zero_comm (seq_zero a)

/-- **SEA 17.1**: `a ⊙ 1 = a` (`a | 0`, so `a | 0⊥ = 1` by S4). -/
theorem seq_one (a : E) : a ⊙ (1 : E) = a := by
  have h0 : Commutes a (0 : E) := by
    show a ⊙ 0 = 0 ⊙ a; rw [seq_zero, zero_seq]
  have := h0.orth_r
  rw [eabasics_orth_zero] at this
  rw [this]; exact one_seq a

/-- **SEA 17.1** (`prop:SEAbasicproperties`, second.tex:490, Proposition):
`a ⊙ 0 = 0 ⊙ a = 0` and `a ⊙ 1 = 1 ⊙ a = a`. -/
theorem sea17_1 (a : E) : a ⊙ (0 : E) = 0 ∧ (0 : E) ⊙ a = 0 ∧ a ⊙ (1 : E) = a ∧
    (1 : E) ⊙ a = a :=
  ⟨seq_zero a, zero_seq a, seq_one a, one_seq a⟩

/-- `a = a ⊙ b ⋁ a ⊙ b⊥`. -/
theorem seq_split (a b : E) :
    ∃ h : Perp (a ⊙ b) (a ⊙ orth b), ovee (a ⊙ b) (a ⊙ orth b) h = a := by
  obtain ⟨h', e⟩ := seq_ovee a (EffectAlgebra.perp_orth b)
  rw [EffectAlgebra.ovee_orth, seq_one] at e
  exact ⟨h', e.symm⟩

/-- `a ⊙ b = a` iff `a ⊙ b⊥ = 0`. -/
theorem seq_eq_self_iff {a b : E} : a ⊙ b = a ↔ a ⊙ orth b = 0 := by
  obtain ⟨h, e⟩ := seq_split a b
  constructor
  · intro h1
    refine cancel_left (a := a ⊙ b) h (PCM.perp_zero _) ?_
    rw [e, ovee_zero_eq, h1]
  · intro h0
    have h' : Perp (a ⊙ b) 0 := PCM.perp_zero _
    have e' := e
    rw [PCM.ovee_congr rfl h0 h h', ovee_zero_eq] at e'
    exact e'

/-- `a ⊙ b = 0` iff `a ⊙ b⊥ = a`. -/
theorem seq_eq_zero_iff {a b : E} : a ⊙ b = 0 ↔ a ⊙ orth b = a := by
  rw [seq_eq_self_iff, orth_orth]

/-- **SEA 15**: `p` is idempotent iff `p ⊙ p⊥ = 0`. -/
theorem isIdempotent_iff (p : E) : IsIdempotent p ↔ p ⊙ orth p = 0 := seq_eq_self_iff

/-- **SEA 17.3** (`prop:SEAbasicproperties`, second.tex:490, Proposition): if
`a ≼ b` then `c ⊙ a ≼ c ⊙ b` (by S1). -/
theorem seq_mono (c : E) {a b : E} (h : a ≼ b) : c ⊙ a ≼ c ⊙ b := by
  obtain ⟨d, hd, rfl⟩ := h
  obtain ⟨h', e⟩ := seq_ovee c hd
  rw [e]; exact left_le_ovee h'

/-- **SEA 17.2** (`prop:SEAbasicproperties`, second.tex:490, Proposition):
`a ⊙ b ≼ a` (17.3 with `b ≼ 1`). -/
theorem seq_le_left (a b : E) : a ⊙ b ≼ a := by
  have := seq_mono a (le_one' b); rwa [seq_one] at this

/-- `p ⊙ p⊥ = 0 = p⊥ ⊙ p` for an idempotent `p`. -/
theorem IsIdempotent.seq_orth {p : E} (hp : IsIdempotent p) : p ⊙ orth p = 0 :=
  (isIdempotent_iff p).mp hp

theorem IsIdempotent.orth_seq {p : E} (hp : IsIdempotent p) : orth p ⊙ p = 0 :=
  seq_zero_comm hp.seq_orth

/-- **SEA 17.6** (`prop:SEAbasicproperties`, second.tex:490, Proposition):
if `p` is idempotent, so is `p⊥` (`p ⊙ p⊥ = 0` gives `p⊥ ⊙ p = 0` by S3). -/
theorem IsIdempotent.compl {p : E} (hp : IsIdempotent p) : IsIdempotent (orth p) := by
  rw [isIdempotent_iff, orth_orth]; exact hp.orth_seq

theorem isIdempotent_zero : IsIdempotent (0 : E) := seq_zero 0

theorem isIdempotent_one : IsIdempotent (1 : E) := seq_one 1

/-- **SEA 17.5** (`prop:SEAbasicproperties`, second.tex:490, Proposition): for
an idempotent `p`, `a ≼ p` iff `p ⊙ a = a` iff `a ⊙ p = a` iff `a ⊙ p⊥ = 0`
iff `p⊥ ⊙ a = 0`.  Proof as printed, by the cycle
`a ≼ p ⇒ p⊥ ⊙ a = 0 ⇒ a ⊙ p⊥ = 0 ⇒ a ⊙ p = a ⇒ p ⊙ a = a ⇒ a ≼ p`.
(The printed cycle writes "`a ⊙ p = a ⇒ p ⊙ a = 0`" for the fourth arrow; the
proof text right after it proves `p ⊙ a = a`, which is what is meant.) -/
theorem sea17_5 {p : E} (hp : IsIdempotent p) (a : E) :
    (a ≼ p ↔ p ⊙ a = a) ∧ (a ≼ p ↔ a ⊙ p = a) ∧ (a ≼ p ↔ a ⊙ orth p = 0) ∧
      (a ≼ p ↔ orth p ⊙ a = 0) := by
  have i1 : a ≼ p → orth p ⊙ a = 0 := fun h =>
    eq_zero_of_le_zero (by have := seq_mono (orth p) h; rwa [hp.orth_seq] at this)
  have i2 : orth p ⊙ a = 0 → a ⊙ orth p = 0 := seq_zero_comm
  have i3 : a ⊙ orth p = 0 → a ⊙ p = a := seq_eq_self_iff.mpr
  have i4 : a ⊙ p = a → p ⊙ a = a := by
    intro h
    have h1 : a ⊙ orth p = 0 := seq_eq_self_iff.mp h
    have hc : Commutes a (orth p) := by
      show a ⊙ orth p = orth p ⊙ a; rw [h1, seq_zero_comm h1]
    have := hc.of_orth_r
    rw [← this]; exact h
  have i5 : p ⊙ a = a → a ≼ p := fun h => by rw [← h]; exact seq_le_left p a
  exact ⟨⟨fun h => i4 (i3 (i2 (i1 h))), i5⟩, ⟨fun h => i3 (i2 (i1 h)), fun h => i5 (i4 h)⟩,
    ⟨fun h => i2 (i1 h), fun h => i5 (i4 (i3 h))⟩, ⟨i1, fun h => i5 (i4 (i3 (i2 h)))⟩⟩

/-- **SEA 17.4** (`prop:SEAbasicproperties`, second.tex:490, Proposition): for
an idempotent `p`, `p ≼ a` iff `p ⊙ a = p` iff `a ⊙ p = p` iff `a⊥ ⊙ p = 0`
iff `p ⊙ a⊥ = 0`.  Proof as printed: `p ≼ a` iff `a⊥ ≼ p⊥`, then 17.5 for the
idempotent `p⊥`; `p ⊙ a = p` iff `p ⊙ a⊥ = 0` by S1; and `p ≼ a` gives
`p | a⊥`, hence `p | a` by S4. -/
theorem sea17_4 {p : E} (hp : IsIdempotent p) (a : E) :
    (p ≼ a ↔ p ⊙ a = p) ∧ (p ≼ a ↔ a ⊙ p = p) ∧ (p ≼ a ↔ orth a ⊙ p = 0) ∧
      (p ≼ a ↔ p ⊙ orth a = 0) := by
  have h5 := sea17_5 hp.compl (orth a)
  rw [orth_orth] at h5
  have e1 : p ≼ a ↔ orth a ⊙ p = 0 := eabasics_le_iff_orth_le.trans h5.2.2.1
  have e2 : p ≼ a ↔ p ⊙ orth a = 0 := eabasics_le_iff_orth_le.trans h5.2.2.2
  have e3 : p ≼ a ↔ p ⊙ a = p := e2.trans seq_eq_self_iff.symm
  have e4 : p ≼ a ↔ a ⊙ p = p := by
    constructor
    · intro h
      have hc : Commutes p (orth a) := by
        show p ⊙ orth a = orth a ⊙ p; rw [e2.mp h, e1.mp h]
      rw [← hc.of_orth_r]; exact e3.mp h
    · intro h; rw [← h]; exact seq_le_left a p
  exact ⟨e3, e4, e1, e2⟩

omit [SEAlgebra E] in
/-- Helper: `p ⋁ (p ⋁ a)⊥ = a⊥`. -/
theorem orth_right_eq {a b : E} (h : Perp a b) :
    ∃ h' : Perp a (orth (ovee a b h)), ovee a (orth (ovee a b h)) h' = orth b := by
  obtain ⟨h', e⟩ := orth_left_eq (PCM.perp_comm h)
  have e2 : ovee b a (PCM.perp_comm h) = ovee a b h := (PCM.ovee_comm h).symm
  rw [PCM.ovee_congr rfl (congrArg orth e2) h' (by rw [← e2]; exact h')] at e
  exact ⟨_, e⟩

/-- **SEA 17.7** (`prop:SEAbasicproperties`, second.tex:490, Proposition): if
`p` is idempotent and `p ⊥ a`, then `a` is idempotent iff `p ⋁ a` is.
Proof as printed for `⇒`: `(p⋁a) ⊙ p = p` and `(p⋁a) ⊙ a = a` by 17.4, so
`(p⋁a)² = p ⋁ a` by S1 (the print's "`= p ⊙ a`" is a slip for `p ⋁ a`).
For `⇐` the print writes `a⊥ = p⊥ ⋁ (p ⋁ a)⊥`; the identity that holds (and
that the argument needs) is `a⊥ = p ⋁ (p ⋁ a)⊥`, a sum of two summable
idempotents, to which `⇒` applies; then 17.6. -/
theorem sea17_7 {p a : E} (hp : IsIdempotent p) (h : Perp p a) :
    IsIdempotent a ↔ IsIdempotent (ovee p a h) := by
  have fwd : ∀ {p a : E} (hp : IsIdempotent p) (h : Perp p a), IsIdempotent a →
      IsIdempotent (ovee p a h) := by
    intro p a hp h ha
    have e1 : ovee p a h ⊙ p = p := ((sea17_4 hp _).2.1).mp (left_le_ovee h)
    have e2 : ovee p a h ⊙ a = a := ((sea17_4 ha _).2.1).mp (right_le_ovee h)
    obtain ⟨h', e⟩ := seq_ovee (ovee p a h) h
    show ovee p a h ⊙ ovee p a h = ovee p a h
    rw [e, PCM.ovee_congr e1 e2 h' h]
  refine ⟨fwd hp h, fun hq => ?_⟩
  obtain ⟨h', e⟩ := orth_right_eq h
  have := fwd hp h' hq.compl
  rw [e] at this
  have := this.compl
  rwa [orth_orth] at this

/-- **SEA 18** (`lem:summableunderidempotent`, second.tex:601, Lemma): if `p`
is idempotent, `a, b ≼ p` and `a ⋁ b` exists, then `a ⋁ b ≼ p`.  Proof as
printed: `p⊥ ⊙ a = 0 = p⊥ ⊙ b`, so `p⊥ ⊙ (a ⋁ b) = 0`. -/
theorem sea18_ovee_le {p a b : E} (hp : IsIdempotent p) (ha : a ≼ p) (hb : b ≼ p)
    (h : Perp a b) : ovee a b h ≼ p := by
  refine ((sea17_5 hp _).2.2.2).mpr ?_
  obtain ⟨h', e⟩ := seq_ovee (orth p) h
  rw [e, PCM.ovee_congr (((sea17_5 hp _).2.2.2).mp ha) (((sea17_5 hp _).2.2.2).mp hb) h'
    (PCM.zero_perp 0), zero_ovee_eq]

/-- `a | a⊥` (S4 applied to `a | a`). -/
theorem commutes_orth_self (a : E) : Commutes a (orth a) := (commutes_refl a).orth_r

/-- **SEA 19** (`lem:selfsummable`, second.tex:614, Lemma): in a SEA,
`a ⊙ a⊥` is summable with itself.  (Printed proof: expand
`1 = a ⋁ a⊥` as `a² ⋁ 2(a ⊙ a⊥) ⋁ (a⊥)²`; we use the equivalent
observation that `a ⊙ a⊥ ≼ a` and `a⊥ ⊙ a ≼ a⊥` are summable, and
`a ⊙ a⊥ = a⊥ ⊙ a` by S4.) -/
theorem sea19_selfSummable (a : E) : Perp (a ⊙ orth a) (a ⊙ orth a) := by
  have h1 : Perp (a ⊙ orth a) (orth a ⊙ a) :=
    perp_of_le (seq_le_left a (orth a)) (seq_le_left (orth a) a) (EffectAlgebra.perp_orth a)
  have e : a ⊙ orth a = orth a ⊙ a := commutes_orth_self a
  rw [← e] at h1
  exact h1

end SEABasics


/-! ### No nilpotents (SEA 22) -/

section Nilpotent

variable {E : Type u} [EffectAlgebra E] [SEAlgebra E]

omit [SEAlgebra E] in
/-- A pair as a list sum. -/
theorem isSumOf_pair {x y : E} (h : Perp x y) : PCM.IsSumOf [x, y] (ovee x y h) := by
  have h1 : PCM.IsSumOf [y] (ovee y 0 (PCM.perp_zero y)) := PCM.IsSumOf.cons PCM.IsSumOf.nil _
  rw [ovee_zero_eq] at h1
  exact PCM.IsSumOf.cons h1 h

/-- The doubling step of SEA 22: if `x² = 0` then `x ⊥ x` and `(x ⋁ x)² = 0`. -/
theorem sq_zero_double {x : E} (hx : x ⊙ x = 0) :
    ∃ h : Perp x x, ovee x x h ⊙ ovee x x h = 0 := by
  have e : x ⊙ orth x = x := seq_eq_zero_iff.mp hx
  have h : Perp x x := by have := sea19_selfSummable x; rwa [e] at this
  refine ⟨h, ?_⟩
  have hc : Commutes x (ovee x x h) := (commutes_refl x).ovee h (commutes_refl x)
  have hxy : x ⊙ ovee x x h = 0 := by
    obtain ⟨h', e'⟩ := seq_ovee x h
    rw [e', PCM.ovee_congr hx hx h' (PCM.zero_perp 0), zero_ovee_eq]
  have hyx : ovee x x h ⊙ x = 0 := by rw [← hc]; exact hxy
  obtain ⟨h', e'⟩ := seq_ovee (ovee x x h) h
  rw [e', PCM.ovee_congr hyx hyx h' (PCM.zero_perp 0), zero_ovee_eq]

end Nilpotent

/-- **SEA 22** (`lem:nonilpotents`, second.tex:659, Lemma): in a normal SEA,
`a² = 0` implies `a = 0`.  Proof as printed: `a = a ⊙ a⊥` is self-summable
(SEA 19) and `(a ⋁ a)² = 0`; so `2ⁿa` exists for all `n`, hence every `ma`
exists, and `a = 0` by SEA 21. -/
theorem sea22_noNilpotents {E : Type u} [EffectAlgebra E] [NormalSEA E] {a : E} (ha : a ⊙ a = 0) : a = 0 := by
  have hpow : ∀ n : ℕ, ∃ x, PCM.IsSumOf (List.replicate (2 ^ n) a) x ∧ x ⊙ x = 0 := by
    intro n
    induction n with
    | zero =>
      refine ⟨a, ?_, ha⟩
      have := PCM.IsSumOf.cons (a := a) PCM.IsSumOf.nil (PCM.perp_zero a)
      rw [ovee_zero_eq] at this; exact this
    | succ n ih =>
      obtain ⟨x, hx, hxx⟩ := ih
      obtain ⟨h, hyy⟩ := sq_zero_double hxx
      refine ⟨ovee x x h, ?_, hyy⟩
      rw [pow_succ, mul_two, List.replicate_add]
      exact isSumOf_append hx hx h
  refine sea21_archimedean NormalSEA.directedComplete (fun m => ?_)
  obtain ⟨x, hx, -⟩ := hpow m
  have hm : m ≤ 2 ^ m := (Nat.lt_two_pow_self).le
  rw [← Nat.add_sub_cancel' hm, List.replicate_add] at hx
  obtain ⟨t, ht, -⟩ := isSumOf_prefix hx
  exact ⟨t, ht⟩


/-! ### Downsets and left corners (SEA 23) -/

section Downset

variable {E : Type u} [EffectAlgebra E]

/-- The downset `[0,p] = {a ; a ≼ p}` of an element `p`. -/
abbrev Downset (p : E) : Type u := {a : E // a ≼ p}

/-- The downset `[0,p]` is an effect algebra with `a ⊥ b` iff `a ⋁ b` exists
in `E` and lies below `p`, and complement `a ↦ p ⊖ a`. -/
noncomputable instance downsetEA (p : E) : EffectAlgebra (Downset p) where
  zero := ⟨0, zero_le' p⟩
  one := ⟨p, le_refl' p⟩
  Perp a b := ∃ h : Perp a.1 b.1, ovee a.1 b.1 h ≼ p
  ovee a b h := ⟨ovee a.1 b.1 h.1, h.2⟩
  orth a := ⟨ominus p a.1 a.2, exc_dposet_D2 (isDiff_ominus a.2)⟩
  perp_comm := by
    rintro a b ⟨h, hle⟩
    exact ⟨PCM.perp_comm h, by rw [← PCM.ovee_comm h]; exact hle⟩
  ovee_comm := by
    rintro a b ⟨h, hle⟩; exact Subtype.ext (PCM.ovee_comm h)
  perp_of_ovee_perp := by
    rintro a b c ⟨hab, _⟩ ⟨h, hle⟩
    have e := PCM.ovee_assoc hab h
    refine ⟨PCM.perp_of_ovee_perp hab h,
      le_trans' (right_le_ovee (PCM.perp_ovee_of_ovee_perp hab h)) ?_⟩
    rw [← e]; exact hle
  perp_ovee_of_ovee_perp := by
    rintro a b c ⟨hab, _⟩ ⟨h, hle⟩
    have e := PCM.ovee_assoc hab h
    refine ⟨PCM.perp_ovee_of_ovee_perp hab h, ?_⟩
    show ovee a.1 (ovee b.1 c.1 _) _ ≼ p
    rw [← e]; exact hle
  ovee_assoc := by
    rintro a b c ⟨hab, _⟩ ⟨h, _⟩; exact Subtype.ext (PCM.ovee_assoc hab h)
  zero_perp := fun a => ⟨PCM.zero_perp a.1, by
    show ovee 0 a.1 _ ≼ p; rw [zero_ovee_eq]; exact a.2⟩
  zero_ovee := fun a => Subtype.ext (zero_ovee_eq a.1 _)
  perp_orth := fun a => ⟨(isDiff_ominus a.2).1, by
    show ovee a.1 (ominus p a.1 a.2) _ ≼ p; rw [(isDiff_ominus a.2).2]; exact le_refl' p⟩
  ovee_orth := fun a => Subtype.ext (isDiff_ominus a.2).2
  orth_unique := by
    rintro a b ⟨h, hle⟩ e
    apply Subtype.ext
    exact (ominus_eq a.2 h (congrArg Subtype.val e)).symm
  eq_zero_of_perp_one := by
    rintro a ⟨h, hle⟩
    apply Subtype.ext
    refine eq_zero_of_le_zero ?_
    have h1 : Perp a.1 p := h
    have hle1 : ovee a.1 p h1 ≼ p := hle
    have h' : Perp p a.1 := PCM.perp_comm h1
    refine le_of_ovee_le_ovee h' (PCM.perp_zero p) ?_
    rw [ovee_zero_eq, ← PCM.ovee_comm h1]; exact hle1

theorem downset_perp_iff {p : E} {a b : Downset p} :
    Perp a b ↔ ∃ h : Perp a.1 b.1, ovee a.1 b.1 h ≼ p := Iff.rfl

@[simp] theorem downset_ovee_val {p : E} {a b : Downset p} (h : Perp a b) :
    (ovee a b h).1 = ovee a.1 b.1 h.1 := rfl

@[simp] theorem downset_zero_val {p : E} : (0 : Downset p).1 = 0 := rfl

@[simp] theorem downset_one_val {p : E} : (1 : Downset p).1 = p := rfl

theorem downset_orth_val {p : E} (a : Downset p) : (orth a).1 = ominus p a.1 a.2 := rfl

/-- In `[0,p]` the order is that of `E`. -/
theorem downset_le_iff {p : E} {a b : Downset p} : a ≼ b ↔ a.1 ≼ b.1 := by
  constructor
  · rintro ⟨c, h, rfl⟩; exact left_le_ovee h.1
  · rintro ⟨d, h, e⟩
    have hd : d ≼ p := le_trans' (right_le_ovee h) (e ▸ b.2)
    exact ⟨⟨d, hd⟩, ⟨h, by simp only; rw [e]; exact b.2⟩, Subtype.ext e⟩

/-- A supremum in `E` of a subset of `[0,p]` is its supremum in `[0,p]`. -/
theorem downset_isSup_of {p : E} {S : Set (Downset p)} {z : E}
    (hz : EIsSup (Subtype.val '' S) z) :
    ∃ hzp : z ≼ p, EIsSup S (⟨z, hzp⟩ : Downset p) := by
  have hzp : z ≼ p := hz.2 p (by rintro _ ⟨a, _, rfl⟩; exact a.2)
  refine ⟨hzp, fun a ha => downset_le_iff.mpr (hz.1 _ ⟨a, ha, rfl⟩), fun y hy => ?_⟩
  exact downset_le_iff.mpr (hz.2 _ (by rintro _ ⟨a, ha, rfl⟩; exact downset_le_iff.mp (hy a ha)))

theorem downset_directed_iff {p : E} {S : Set (Downset p)} :
    EDirected S ↔ EDirected (Subtype.val '' S) := by
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    refine ⟨⟨a.1, a, ha, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, h1, h2⟩ := h a ha b hb
    exact ⟨c.1, ⟨c, hc, rfl⟩, downset_le_iff.mp h1, downset_le_iff.mp h2⟩
  · rintro ⟨⟨_, a, ha, rfl⟩, h⟩
    refine ⟨⟨a, ha⟩, fun a ha b hb => ?_⟩
    obtain ⟨_, ⟨c, hc, rfl⟩, h1, h2⟩ := h a.1 ⟨a, ha, rfl⟩ b.1 ⟨b, hb, rfl⟩
    exact ⟨c, hc, downset_le_iff.mpr h1, downset_le_iff.mpr h2⟩

/-- A directed-complete effect algebra has directed-complete downsets, with
the same suprema. -/
theorem downset_directedComplete {p : E} (hE : DirectedComplete E) :
    DirectedComplete (Downset p) := by
  intro S hS
  obtain ⟨z, hz⟩ := hE _ (downset_directed_iff.mp hS)
  obtain ⟨hzp, h⟩ := downset_isSup_of hz
  exact ⟨_, h⟩

/-- Suprema in `[0,p]` are suprema in `E` (when `E` is directed complete). -/
theorem downset_isSup_val {p : E} (hE : DirectedComplete E) {S : Set (Downset p)}
    (hS : EDirected S) {x : Downset p} (hx : EIsSup S x) : EIsSup (Subtype.val '' S) x.1 := by
  obtain ⟨z, hz⟩ := hE _ (downset_directed_iff.mp hS)
  obtain ⟨hzp, h⟩ := downset_isSup_of hz
  have := hx.unique h
  rw [this]; exact hz

end Downset

section Corner

variable {E : Type u} [EffectAlgebra E] [SEAlgebra E]

/-- **SEA 23**: the *left corner* `p ⊙ E = {p ⊙ a ; a ∈ E}`. -/
def leftCorner (p : E) : Set E := Set.range (p ⊙ ·)

/-- **SEA 23**, first step of the proof: for an idempotent `p`,
`p ⊙ E = {a ; a ≼ p}` (by SEA 17.5). -/
theorem leftCorner_eq {p : E} (hp : IsIdempotent p) : leftCorner p = {a | a ≼ p} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩; exact seq_le_left p b
  · intro h; exact ⟨a, ((sea17_5 hp a).1).mp h⟩

/-- **SEA 23**: for idempotent `p`, summability in `p ⊙ E` is summability in
`E` (SEA 18). -/
theorem corner_perp_iff {p : E} (hp : IsIdempotent p) {a b : Downset p} :
    Perp a b ↔ Perp a.1 b.1 :=
  ⟨fun h => h.1, fun h => ⟨h, sea18_ovee_le hp a.2 b.2 h⟩⟩

omit [SEAlgebra E] in
/-- `(b ⋁ p⊥)⊥ = p ⊖ b` for `b ≼ p`. -/
theorem orth_ovee_orth_eq {p b : E} (hb : b ≼ p) :
    ∃ h : Perp (orth p) b, orth (ovee (orth p) b h) = ominus p b hb :=
  isDiff_eq_orth_ovee_orth (isDiff_ominus hb)

/-- The sequential product restricted to `[0,p]`. -/
def cornerSeq (p : E) (a b : Downset p) : Downset p :=
  ⟨a.1 ⊙ b.1, le_trans' (seq_le_left a.1 b.1) a.2⟩

/-- **SEA 23** (second.tex:679, Proposition): for an idempotent `p`, the left
corner `p ⊙ E` (as `[0,p]`, by `leftCorner_eq`), with the sum and zero of `E`
(`corner_perp_iff`) and complement `a ↦ p ⊖ a`, is a SEA under the restricted
sequential product.  Proof as printed: all axioms are inherited except the
first half of S4, which follows from `a | p⊥`, S5 (`a | b ⋁ p⊥`) and S4 in `E`
(`(b ⋁ p⊥)⊥ = p ⊖ b`). -/
@[instance_reducible] noncomputable def cornerSEA {p : E} (hp : IsIdempotent p) : SEAlgebra (Downset p) where
  seq := cornerSeq p
  seq_add := by
    rintro c a b ⟨h, hle⟩
    obtain ⟨h', e⟩ := seq_ovee c.1 h
    have hle' : ovee (c.1 ⊙ a.1) (c.1 ⊙ b.1) h' ≼ c.1 := by rw [← e]; exact seq_le_left _ _
    exact ⟨⟨h', le_trans' hle' c.2⟩, Subtype.ext e.symm⟩
  one_seq := fun a => Subtype.ext (((sea17_5 hp a.1).1).mp a.2)
  seq_zero_comm := fun a b h => Subtype.ext (seq_zero_comm (congrArg Subtype.val h))
  seq_comm_orth := by
    intro a b h
    have hab : Commutes a.1 b.1 := congrArg Subtype.val h
    have h1 : a.1 ⊙ orth p = 0 := ((sea17_5 hp a.1).2.2.1).mp a.2
    have hap : Commutes a.1 (orth p) := by
      show a.1 ⊙ orth p = orth p ⊙ a.1; rw [h1, seq_zero_comm h1]
    obtain ⟨hpb, e⟩ := orth_ovee_orth_eq b.2
    have := (hap.ovee hpb hab).orth_r
    rw [e] at this
    exact Subtype.ext this
  seq_comm_assoc := fun {a b} h c =>
    Subtype.ext (SequentialEffectAlgebra.seq_comm_assoc (congrArg Subtype.val h) c.1)
  seq_comm_compat := fun {a b c} h hca hcb =>
    ⟨Subtype.ext (SequentialEffectAlgebra.seq_comm_compat h.1 (congrArg Subtype.val hca)
        (congrArg Subtype.val hcb)).1,
      Subtype.ext (SequentialEffectAlgebra.seq_comm_compat h.1 (congrArg Subtype.val hca)
        (congrArg Subtype.val hcb)).2⟩
  seq_comm_seq := fun {a b c} hca hcb =>
    Subtype.ext (SEAlgebra.seq_comm_seq (congrArg Subtype.val hca) (congrArg Subtype.val hcb))

theorem cornerSEA_seq {p : E} (hp : IsIdempotent p) (a b : Downset p) :
    (@SequentialEffectAlgebra.seq _ _ (cornerSEA hp).toSequentialEffectAlgebra a b).1
      = a.1 ⊙ b.1 := rfl

end Corner

/-- **SEA 23** (second.tex:679, Proposition), second half: if `E` is normal
then so is `p ⊙ E`.  As printed: suprema in the principal downset are those of
`E`, and the product is the restriction. -/
@[instance_reducible] noncomputable def cornerNormalSEA {E : Type u} [EffectAlgebra E] [NormalSEA E] {p : E} (hp : IsIdempotent p) :
    NormalSEA (Downset p) :=
  { cornerSEA hp with
    directedComplete := downset_directedComplete NormalSEA.directedComplete
    seq_sup := by
      intro a S x hS hx
      have hv := downset_isSup_val NormalSEA.directedComplete hS hx
      have h1 := NormalSEA.seq_sup a.1 (downset_directed_iff.mp hS) hv
      have himg : Subtype.val '' (cornerSeq p a '' S) =
          SequentialEffectAlgebra.seq a.1 '' (Subtype.val '' S) := by
        ext y; constructor
        · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩; exact ⟨s.1, ⟨s, hs, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩; exact ⟨cornerSeq p a s, ⟨s, hs, rfl⟩, rfl⟩
      rw [← himg] at h1
      obtain ⟨_, h2⟩ := downset_isSup_of h1
      exact h2
    comm_sup := by
      intro a S x hS hx hcomm
      have hv := downset_isSup_val NormalSEA.directedComplete hS hx
      refine Subtype.ext (NormalSEA.comm_sup a.1 (downset_directed_iff.mp hS) hv ?_)
      rintro _ ⟨s, hs, rfl⟩
      exact congrArg Subtype.val (hcomm s hs) }


/-! ### Direct sums and isomorphisms (SEA 24) -/

/-- An isomorphism of effect algebras: a bijection preserving `1`, preserving
and reflecting summability, and preserving sums. -/
structure EAIso (E : Type u) (F : Type v) [EffectAlgebra E] [EffectAlgebra F]
    extends E ≃ F where
  map_one : toFun 1 = 1
  perp_iff : ∀ a b : E, Perp (toFun a) (toFun b) ↔ Perp a b
  map_ovee : ∀ (a b : E) (h : Perp a b) (h' : Perp (toFun a) (toFun b)),
    toFun (ovee a b h) = ovee (toFun a) (toFun b) h'

/-- An isomorphism of SEAs: an effect algebra isomorphism preserving `⊙`. -/
structure SEAIso (E : Type u) (F : Type v) [EffectAlgebra E] [EffectAlgebra F]
    [SEAlgebra E] [SEAlgebra F] extends EAIso E F where
  map_seq : ∀ a b : E, toFun (a ⊙ b) = toFun a ⊙ toFun b

/-- The direct sum of two SEAs is a SEA, componentwise. -/
instance prodSEA (E F : Type u) [EffectAlgebra E] [EffectAlgebra F] [SEAlgebra E]
    [SEAlgebra F] : SEAlgebra (E × F) where
  seq a b := (a.1 ⊙ b.1, a.2 ⊙ b.2)
  seq_add := by
    rintro c a b ⟨h1, h2⟩
    obtain ⟨h1', e1⟩ := seq_ovee c.1 h1
    obtain ⟨h2', e2⟩ := seq_ovee c.2 h2
    exact ⟨⟨h1', h2'⟩, Prod.ext e1.symm e2.symm⟩
  one_seq a := Prod.ext (one_seq a.1) (one_seq a.2)
  seq_zero_comm a b h := Prod.ext (seq_zero_comm (congrArg Prod.fst h))
    (seq_zero_comm (congrArg Prod.snd h))
  seq_comm_orth h := Prod.ext (Commutes.orth_r (congrArg Prod.fst h))
    (Commutes.orth_r (congrArg Prod.snd h))
  seq_comm_assoc h c := Prod.ext (SequentialEffectAlgebra.seq_comm_assoc (congrArg Prod.fst h) c.1)
    (SequentialEffectAlgebra.seq_comm_assoc (congrArg Prod.snd h) c.2)
  seq_comm_compat h hca hcb :=
    ⟨Prod.ext (Commutes.seq (congrArg Prod.fst hca) (congrArg Prod.fst hcb))
      (Commutes.seq (congrArg Prod.snd hca) (congrArg Prod.snd hcb)),
     Prod.ext (Commutes.ovee h.1 (congrArg Prod.fst hca) (congrArg Prod.fst hcb))
      (Commutes.ovee h.2 (congrArg Prod.snd hca) (congrArg Prod.snd hcb))⟩
  seq_comm_seq hca hcb := Prod.ext (Commutes.seq (congrArg Prod.fst hca) (congrArg Prod.fst hcb))
      (Commutes.seq (congrArg Prod.snd hca) (congrArg Prod.snd hcb))

section Split

variable {E : Type u} [EffectAlgebra E]

/-- A sum of a concatenation splits into the sums of the two parts. -/
theorem isSumOf_append_split {l l' : List E} {s : E} (hs : PCM.IsSumOf (l ++ l') s) :
    ∃ t t', PCM.IsSumOf l t ∧ PCM.IsSumOf l' t' ∧ ∃ h : Perp t t', ovee t t' h = s := by
  induction l generalizing s with
  | nil => exact ⟨0, s, PCM.IsSumOf.nil, hs, PCM.zero_perp s, zero_ovee_eq s _⟩
  | cons x l ih =>
    obtain ⟨s', hs', h1, rfl⟩ := PCM.isSumOf_cons_iff.mp hs
    obtain ⟨t, t', ht, ht', h, rfl⟩ := ih hs'
    obtain ⟨hxt, h', e⟩ := PCM.assoc_left h h1
    exact ⟨ovee x t hxt, t', PCM.IsSumOf.cons ht hxt, ht', h', e⟩

end Split

section CentralSplit

variable {E : Type u} [EffectAlgebra E] [SEAlgebra E]

theorem IsCentral.orth_central {p : E} (hp : IsCentral p) : IsCentral (orth p) :=
  fun b => (hp b).orth_l

/-- **SEA 24** (`prop:central-splits`, second.tex:714, Proposition): for a
central idempotent `p`, `E ≅ p ⊙ E ⊕ p⊥ ⊙ E` via `a ↦ (p ⊙ a, p⊥ ⊙ a)`, as
SEAs.  Proof as printed: the map is additive and unital, order reflecting
(`a = p ⊙ a ⋁ p⊥ ⊙ a` by centrality), surjective (`a ⋁ b ↦ (a, b)`), and
multiplicative by `p ⊙ (a ⊙ b) = (p ⊙ a) ⊙ b = ((p ⊙ a) ⊙ p) ⊙ b
= (p ⊙ a) ⊙ (p ⊙ b)`. -/
noncomputable def sea24_centralSplit {p : E} (hp : IsIdempotent p) (hc : IsCentral p) :
    @SEAIso E (Downset p × Downset (orth p)) _ _ _
      (@prodSEA _ _ _ _ (cornerSEA hp) (cornerSEA hp.compl)) := by
  letI := cornerSEA hp
  letI := cornerSEA hp.compl
  have hp' : IsIdempotent (orth p) := hp.compl
  have hc' : IsCentral (orth p) := hc.orth_central
  -- `p ⊙ y = 0` for `y ≼ p⊥`, and `p⊥ ⊙ x = 0` for `x ≼ p`
  have kill1 : ∀ y : Downset (orth p), p ⊙ y.1 = 0 := fun y => by
    have := ((sea17_5 hp' y.1).2.2.2).mp y.2; rwa [orth_orth] at this
  have kill2 : ∀ x : Downset p, orth p ⊙ x.1 = 0 := fun x => ((sea17_5 hp x.1).2.2.2).mp x.2
  have fix1 : ∀ x : Downset p, p ⊙ x.1 = x.1 := fun x => ((sea17_5 hp x.1).1).mp x.2
  have fix2 : ∀ y : Downset (orth p), orth p ⊙ y.1 = y.1 := fun y =>
    ((sea17_5 hp' y.1).1).mp y.2
  have hxy : ∀ (x : Downset p) (y : Downset (orth p)), Perp x.1 y.1 := fun x y =>
    perp_of_le x.2 y.2 (EffectAlgebra.perp_orth p)
  have recon : ∀ a : E, ∃ h : Perp (p ⊙ a) (orth p ⊙ a), ovee (p ⊙ a) (orth p ⊙ a) h = a := by
    intro a
    obtain ⟨h, e⟩ := seq_split a p
    have e1 : a ⊙ p = p ⊙ a := (hc a).symm
    have e2 : a ⊙ orth p = orth p ⊙ a := (hc' a).symm
    have h'' : Perp (p ⊙ a) (orth p ⊙ a) := by rw [← e1, ← e2]; exact h
    exact ⟨h'', (PCM.ovee_congr e1 e2 h h'').symm.trans e⟩
  refine
    { toFun := fun a => (⟨p ⊙ a, seq_le_left p a⟩, ⟨orth p ⊙ a, seq_le_left (orth p) a⟩)
      invFun := fun xy => ovee xy.1.1 xy.2.1 (hxy xy.1 xy.2)
      left_inv := fun a => (recon a).2
      right_inv := ?_
      map_one := ?_
      perp_iff := ?_
      map_ovee := ?_
      map_seq := ?_ }
  · rintro ⟨x, y⟩
    obtain ⟨h1, e1⟩ := seq_ovee p (hxy x y)
    obtain ⟨h2, e2⟩ := seq_ovee (orth p) (hxy x y)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show p ⊙ ovee x.1 y.1 _ = x.1
      rw [e1, PCM.ovee_congr (fix1 x) (kill1 y) h1 (PCM.perp_zero _), ovee_zero_eq]
    · show orth p ⊙ ovee x.1 y.1 _ = y.1
      rw [e2, PCM.ovee_congr (kill2 x) (fix2 y) h2 (PCM.zero_perp _), zero_ovee_eq]
  · exact Prod.ext (Subtype.ext (seq_one p)) (Subtype.ext (seq_one (orth p)))
  · intro a b
    constructor
    · rintro ⟨⟨h1, hle1⟩, ⟨h2, hle2⟩⟩
      -- `u = p⊙a ⋁ p⊙b ≼ p` and `v = p⊥⊙a ⋁ p⊥⊙b ≼ p⊥` are summable
      have huv : Perp (ovee (p ⊙ a) (p ⊙ b) h1) (ovee (orth p ⊙ a) (orth p ⊙ b) h2) :=
        perp_of_le hle1 hle2 (EffectAlgebra.perp_orth p)
      have hsum := isSumOf_append (isSumOf_pair h1) (isSumOf_pair h2) huv
      have hperm : ([p ⊙ a, p ⊙ b] ++ [orth p ⊙ a, orth p ⊙ b]).Perm
          ([p ⊙ a, orth p ⊙ a] ++ [p ⊙ b, orth p ⊙ b]) := by
        simp only [List.cons_append, List.nil_append]
        exact List.Perm.cons _ (List.Perm.swap _ _ _)
      obtain ⟨t, t', ht, ht', h, -⟩ := isSumOf_append_split (PCM.isSumOf_perm hperm hsum)
      obtain ⟨ha, ea⟩ := recon a
      obtain ⟨hb, eb⟩ := recon b
      have e1 := isSumOf_unique ht (isSumOf_pair ha)
      have e2 := isSumOf_unique ht' (isSumOf_pair hb)
      rw [ea] at e1; rw [eb] at e2
      subst e1; subst e2; exact h
    · intro h
      exact ⟨(corner_perp_iff hp).mpr (seq_perp p h),
        (corner_perp_iff hp').mpr (seq_perp (orth p) h)⟩
  · intro a b h h'
    obtain ⟨h1, e1⟩ := seq_ovee p h
    obtain ⟨h2, e2⟩ := seq_ovee (orth p) h
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  · intro a b
    have key : ∀ q : E, IsIdempotent q → IsCentral q → q ⊙ (a ⊙ b) = (q ⊙ a) ⊙ (q ⊙ b) := by
      intro q hq hqc
      have hqa : q ⊙ (q ⊙ a) = q ⊙ a := ((sea17_5 hq _).1).mp (seq_le_left q a)
      calc q ⊙ (a ⊙ b) = (q ⊙ a) ⊙ b := (hqc a).assoc b
        _ = (q ⊙ (q ⊙ a)) ⊙ b := by rw [hqa]
        _ = ((q ⊙ a) ⊙ q) ⊙ b := by rw [hqc (q ⊙ a)]
        _ = (q ⊙ a) ⊙ (q ⊙ b) := ((hqc (q ⊙ a)).symm.assoc b).symm
    exact Prod.ext (Subtype.ext (key p hp hc)) (Subtype.ext (key (orth p) hp' hc'))

/-- **SEA 25** (second.tex:737, Definition): an idempotent `p` is *Boolean*
when `p ⊙ E` is Boolean, i.e. every `a ≼ p` is an idempotent. -/
def IsBooleanIdempotent (p : E) : Prop := IsIdempotent p ∧ ∀ a : E, a ≼ p → IsIdempotent a

/-- **SEA 25**: the "i.e." of the definition — `p ⊙ E` is a Boolean SEA iff
every `a ≼ p` is idempotent. -/
theorem isBooleanIdempotent_iff {p : E} (hp : IsIdempotent p) :
    @IsBooleanSEA _ _ (cornerSEA hp) ↔ ∀ a : E, a ≼ p → IsIdempotent a := by
  constructor
  · intro h a ha
    exact congrArg Subtype.val (h ⟨a, ha⟩)
  · intro h a
    exact Subtype.ext (h a.1 a.2)

/-- **SEA 26** (second.tex:743, Definition): the *commutant*
`S' = {a ; a | s for all s ∈ S}`. -/
def commutant (S : Set E) : Set E := {a | ∀ s ∈ S, Commutes a s}

/-- **SEA 26** (second.tex:743, Definition): the *bicommutant* `S'' = (S')'`. -/
def bicommutant (S : Set E) : Set E := commutant (commutant S)

theorem commutant_anti {S T : Set E} (h : S ⊆ T) : commutant T ⊆ commutant S :=
  fun _ ha s hs => ha s (h hs)

theorem subset_bicommutant (S : Set E) : S ⊆ bicommutant S :=
  fun s hs _ ha => (ha s hs).symm

end CentralSplit

-- **SEA 27** (second.tex:752, Remark): for `B(H)` the bicommutant `{a}''` is
-- the least commutative von Neumann subalgebra containing `a`, but not in
-- general (`[0,1]²`, `a = (0,1)`, where `{a}'' = E`).  Illustrative, no
-- declaration; see the audit row for a remark on its wording.


/-! ### Sub-SEAs and bicommutants (SEA 28) -/

section SubEA

variable {E : Type u} [EffectAlgebra E]

/-- The effect algebra on a sub-effect algebra (eff.tex 175I), with the
operations of `E`. -/
noncomputable instance subEA (T : SubEffectAlgebra E) : EffectAlgebra T.carrier where
  zero := ⟨0, T.zero_mem⟩
  one := ⟨1, T.one_mem⟩
  Perp a b := Perp a.1 b.1
  ovee a b h := ⟨ovee a.1 b.1 h, T.ovee_mem h a.2 b.2⟩
  orth a := ⟨orth a.1, T.orth_mem a.2⟩
  perp_comm h := PCM.perp_comm h
  ovee_comm h := Subtype.ext (PCM.ovee_comm h)
  perp_of_ovee_perp hab h := PCM.perp_of_ovee_perp hab h
  perp_ovee_of_ovee_perp hab h := PCM.perp_ovee_of_ovee_perp hab h
  ovee_assoc hab h := Subtype.ext (PCM.ovee_assoc hab h)
  zero_perp a := PCM.zero_perp a.1
  zero_ovee a := Subtype.ext (PCM.zero_ovee a.1)
  perp_orth a := EffectAlgebra.perp_orth a.1
  ovee_orth a := Subtype.ext (EffectAlgebra.ovee_orth a.1)
  orth_unique h e := Subtype.ext (EffectAlgebra.orth_unique h (congrArg Subtype.val e))
  eq_zero_of_perp_one h := Subtype.ext (EffectAlgebra.eq_zero_of_perp_one h)

variable {T : SubEffectAlgebra E}

@[simp] theorem subEA_ovee_val {a b : T.carrier} (h : Perp a b) :
    (ovee a b h).1 = ovee a.1 b.1 h := rfl

@[simp] theorem subEA_orth_val (a : T.carrier) : (orth a).1 = orth a.1 := rfl

@[simp] theorem subEA_zero_val : (0 : T.carrier).1 = 0 := rfl

@[simp] theorem subEA_one_val : (1 : T.carrier).1 = 1 := rfl

/-- In a sub-effect algebra the order is that of `E` (the difference
`b ⊖ a = (b⊥ ⋁ a)⊥` stays inside). -/
theorem subEA_le_iff {a b : T.carrier} : a ≼ b ↔ a.1 ≼ b.1 := by
  constructor
  · rintro ⟨c, h, rfl⟩; exact left_le_ovee (show Perp a.1 c.1 from h)
  · rintro ⟨d, h, e⟩
    obtain ⟨hp, e'⟩ := isDiff_eq_orth_ovee_orth (show IsDiff b.1 a.1 d from ⟨h, e⟩)
    have hd : d ∈ T.carrier := by
      rw [← e']; exact T.orth_mem (T.ovee_mem hp (T.orth_mem b.2) a.2)
    exact ⟨⟨d, hd⟩, h, Subtype.ext e⟩

theorem subEA_directed_iff {S : Set T.carrier} :
    EDirected S ↔ EDirected (Subtype.val '' S) := by
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    refine ⟨⟨a.1, a, ha, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, h1, h2⟩ := h a ha b hb
    exact ⟨c.1, ⟨c, hc, rfl⟩, subEA_le_iff.mp h1, subEA_le_iff.mp h2⟩
  · rintro ⟨⟨_, a, ha, rfl⟩, h⟩
    refine ⟨⟨a, ha⟩, fun a ha b hb => ?_⟩
    obtain ⟨_, ⟨c, hc, rfl⟩, h1, h2⟩ := h a.1 ⟨a, ha, rfl⟩ b.1 ⟨b, hb, rfl⟩
    exact ⟨c, hc, subEA_le_iff.mpr h1, subEA_le_iff.mpr h2⟩

/-- A supremum in `E` lying in the sub-effect algebra is a supremum there. -/
theorem subEA_isSup_of {S : Set T.carrier} {z : E} (hz : EIsSup (Subtype.val '' S) z)
    (hzT : z ∈ T.carrier) : EIsSup S (⟨z, hzT⟩ : T.carrier) := by
  refine ⟨fun a ha => subEA_le_iff.mpr (hz.1 _ ⟨a, ha, rfl⟩), fun y hy => ?_⟩
  exact subEA_le_iff.mpr (hz.2 _ (by rintro _ ⟨a, ha, rfl⟩; exact subEA_le_iff.mp (hy a ha)))

end SubEA

/-- A *sub-SEA*: a sub-effect algebra closed under `⊙`. -/
structure SubSEA (E : Type u) [EffectAlgebra E] [SEAlgebra E] extends SubEffectAlgebra E where
  seq_mem : ∀ {a b : E}, a ∈ carrier → b ∈ carrier → a ⊙ b ∈ carrier

/-- A *sub-normal-SEA*: a sub-SEA closed under directed suprema. -/
structure SubNormalSEA (E : Type u) [EffectAlgebra E] [NormalSEA E] extends SubSEA E where
  sup_mem : ∀ {S : Set E} {x : E}, S ⊆ carrier → EDirected S → EIsSup S x → x ∈ carrier

/-- A sub-SEA is a SEA under the restricted operations. -/
noncomputable instance subSEA {E : Type u} [EffectAlgebra E] [SEAlgebra E] (T : SubSEA E) :
    SEAlgebra T.carrier where
  seq a b := ⟨a.1 ⊙ b.1, T.seq_mem a.2 b.2⟩
  seq_add c a b h := by
    obtain ⟨h', e⟩ := seq_ovee c.1 (show Perp a.1 b.1 from h)
    exact ⟨h', Subtype.ext e.symm⟩
  one_seq a := Subtype.ext (one_seq a.1)
  seq_zero_comm a b h := Subtype.ext (seq_zero_comm (congrArg Subtype.val h))
  seq_comm_orth h := Subtype.ext (Commutes.orth_r (congrArg Subtype.val h))
  seq_comm_assoc h c :=
    Subtype.ext (SequentialEffectAlgebra.seq_comm_assoc (congrArg Subtype.val h) c.1)
  seq_comm_compat {a b c} h hca hcb :=
    ⟨Subtype.ext (Commutes.seq (E := E) (congrArg Subtype.val hca) (congrArg Subtype.val hcb)),
     Subtype.ext (Commutes.ovee (E := E) (show Perp a.1 b.1 from h) (congrArg Subtype.val hca)
      (congrArg Subtype.val hcb))⟩
  seq_comm_seq hca hcb :=
    Subtype.ext (Commutes.seq (congrArg Subtype.val hca) (congrArg Subtype.val hcb))

@[simp] theorem subSEA_seq_val {E : Type u} [EffectAlgebra E] [SEAlgebra E] {T : SubSEA E}
    (a b : T.carrier) : (a ⊙ b).1 = a.1 ⊙ b.1 := rfl

section SubNormal

variable {E : Type u} [EffectAlgebra E] [NormalSEA E] (T : SubNormalSEA E)

/-- Suprema in a sub-normal-SEA are those of `E`. -/
theorem subNormal_isSup_val {S : Set T.carrier} (hS : EDirected S) {x : T.carrier}
    (hx : EIsSup S x) : EIsSup (Subtype.val '' S) x.1 := by
  have hS' := (subEA_directed_iff (T := T.toSubEffectAlgebra)).mp hS
  obtain ⟨z, hz⟩ := NormalSEA.directedComplete _ hS'
  have hzT : z ∈ T.carrier := T.sup_mem (by rintro _ ⟨a, _, rfl⟩; exact a.2) hS' hz
  have := hx.unique (subEA_isSup_of (T := T.toSubEffectAlgebra) hz hzT)
  rw [this]; exact hz

/-- A sub-normal-SEA is a normal SEA. -/
noncomputable instance subNormalSEA : NormalSEA T.carrier :=
  { subSEA T.toSubSEA with
    directedComplete := by
      intro S hS
      have hS' := (subEA_directed_iff (T := T.toSubEffectAlgebra)).mp hS
      obtain ⟨z, hz⟩ := NormalSEA.directedComplete _ hS'
      have hzT : z ∈ T.carrier := T.sup_mem (by rintro _ ⟨a, _, rfl⟩; exact a.2) hS' hz
      exact ⟨_, subEA_isSup_of (T := T.toSubEffectAlgebra) hz hzT⟩
    seq_sup := by
      intro a S x hS hx
      have hv := subNormal_isSup_val T hS hx
      have hS' := (subEA_directed_iff (T := T.toSubEffectAlgebra)).mp hS
      have h1 := NormalSEA.seq_sup a.1 hS' hv
      have himg : Subtype.val '' ((fun b : T.carrier => (⟨a.1 ⊙ b.1, T.seq_mem a.2 b.2⟩ :
          T.carrier)) '' S) = SequentialEffectAlgebra.seq a.1 '' (Subtype.val '' S) := by
        ext y; constructor
        · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩; exact ⟨s.1, ⟨s, hs, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
          exact ⟨⟨a.1 ⊙ s.1, T.seq_mem a.2 s.2⟩, ⟨s, hs, rfl⟩, rfl⟩
      rw [← himg] at h1
      exact subEA_isSup_of (T := T.toSubEffectAlgebra) h1 (T.seq_mem a.2 x.2)
    comm_sup := by
      intro a S x hS hx hcomm
      have hv := subNormal_isSup_val T hS hx
      have hS' := (subEA_directed_iff (T := T.toSubEffectAlgebra)).mp hS
      refine Subtype.ext (NormalSEA.comm_sup a.1 hS' hv ?_)
      rintro _ ⟨s, hs, rfl⟩
      exact congrArg Subtype.val (hcomm s hs) }

end SubNormal

section Commutant

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

/-- **SEA 28** (`prop:doublecommutant`, second.tex:768, Proposition), first
step of the proof: for an arbitrary `S`, the commutant `S'` contains `0, 1`
and is closed under sums, complements, `⊙` (S4, S5) and directed suprema
(S6), so it is a sub-normal-SEA. -/
noncomputable def commutantSub (S : Set E) : SubNormalSEA E where
  carrier := commutant S
  zero_mem := fun s _ => by show (0 : E) ⊙ s = s ⊙ 0; rw [zero_seq, seq_zero]
  one_mem := fun s _ => by show (1 : E) ⊙ s = s ⊙ 1; rw [one_seq, seq_one]
  ovee_mem := fun h ha hb s hs => ((ha s hs).symm.ovee h (hb s hs).symm).symm
  orth_mem := fun ha s hs => ((ha s hs).symm.orth_r).symm
  seq_mem := fun ha hb s hs => ((ha s hs).symm.seq (hb s hs).symm).symm
  sup_mem := by
    intro D x hD hdir hx s hs
    exact (NormalSEA.comm_sup s hdir hx (fun d hd => (hD hd s hs).symm)).symm

/-- The bicommutant `S''` as a sub-normal-SEA. -/
noncomputable def bicommutantSub (S : Set E) : SubNormalSEA E := commutantSub (commutant S)

theorem bicommutantSub_carrier (S : Set E) : (bicommutantSub S).carrier = bicommutant S := rfl

/-- **SEA 28** (`prop:doublecommutant`, second.tex:768, Proposition): if `S`
consists of mutually commuting elements of a normal SEA `E`, then `S''` is a
commutative normal SEA (a sub-normal-SEA of `E`, by `commutantSub`, containing
`S`).  Proof as printed: `S ⊆ S'`, so `S'' ⊆ S'`, and `S''` commutes with
`S'`, hence with itself. -/
theorem sea28_bicommutant_commutative (S : Set E) (hS : ∀ a ∈ S, ∀ b ∈ S, Commutes a b) :
    S ⊆ (bicommutantSub S).carrier ∧ IsCommutativeSEA (bicommutantSub S).carrier := by
  refine ⟨subset_bicommutant S, fun a b => Subtype.ext ?_⟩
  have hSS : S ⊆ commutant S := fun a ha b hb => hS a ha b hb
  have hb : b.1 ∈ commutant S := commutant_anti hSS b.2
  exact a.2 b.1 hb

end Commutant

/-! ## Effect monoids (SEA 29–34) -/

section EM

variable {M : Type u} [EffectMonoid M]

/-- **SEA 29** (`def:effectmonoid`, second.tex:815, Definition): an effect
monoid is the theses' `EffectMonoid` (eff.tex 178II), an effect algebra with a
total multiplication.  Its distributivity axiom is eff.tex's four-term law; the
paper's form — unit, bi-additivity, associativity — is recovered here. -/
theorem sea29_effectMonoid_axioms :
    (∀ x : M, x * 1 = x ∧ 1 * x = x) ∧
    (∀ (x y z : M) (h : Perp y z), ∃ (h1 : Perp (x * y) (x * z)) (h2 : Perp (y * x) (z * x)),
      x * ovee y z h = ovee (x * y) (x * z) h1 ∧ ovee y z h * x = ovee (y * x) (z * x) h2) ∧
    (∀ x y z : M, x * (y * z) = x * y * z) := by
  refine ⟨fun x => ⟨EffectMonoid.mul_one x, EffectMonoid.one_mul x⟩, fun x y z h => ?_,
    fun x y z => (EffectMonoid.mul_assoc x y z).symm⟩
  obtain ⟨h1, e1⟩ := emon_mul_ovee x h
  obtain ⟨h2, e2⟩ := emon_ovee_mul x h
  exact ⟨h1, h2, e1, e2⟩

/-- **SEA 29**: an *idempotent* of an effect monoid, `p² = p`. -/
def EMIdempotent (p : M) : Prop := p * p = p

/-- **SEA 29**: `x` and `y` are *orthogonal* when `x ⊙ y = y ⊙ x = 0`. -/
def EMOrthogonal (x y : M) : Prop := x * y = 0 ∧ y * x = 0

/-- **SEA 29**: an effect monoid is *Boolean* when all its elements are
idempotent.  (Commutativity is the theses' `EffectMonoid.Commutative`.) -/
def IsBooleanEM (M : Type u) [EffectMonoid M] : Prop := ∀ a : M, a * a = a

end EM

/-- An isomorphism of effect monoids. -/
structure EMIso (M : Type u) (N : Type v) [EffectMonoid M] [EffectMonoid N]
    extends EAIso M N where
  map_mul : ∀ a b : M, toFun (a * b) = toFun a * toFun b

/-- **SEA 30** (`ex:booleanalgebra`, second.tex:844, Example): a Boolean
algebra is a Boolean commutative effect monoid with `x ⊙ y = x ∧ y` (the
theses' `booleanEffectMonoid`, eff.tex 178III.2).  The converse ("any Boolean
effect monoid is a Boolean algebra", cited from OAP 47) is the hypothesis
`OAP47` below, in the directed-complete form SEA uses. -/
theorem sea30_booleanAlgebra (L : Type u) [BooleanAlgebra L] :
    (∀ x y : L, @HMul.hMul L L L (@instHMul L (booleanEffectMonoid L).toMul) x y = x ⊓ y) ∧
    @EffectMonoid.Commutative L (booleanEffectMonoid L) ∧
    @IsBooleanEM L (booleanEffectMonoid L) :=
  ⟨fun _ _ => rfl, fun x y => inf_comm x y, fun x => inf_idem x⟩

/-- **OAP 47** (`prop:sharpeffectmonoidisbooleanalgebra`, first.tex:1645), in
the form SEA 30, 36 and 44 use it: a directed-complete Boolean effect monoid is
(isomorphic, as an effect monoid, to) a complete Boolean algebra.  Not proved
here — waits on the OAP formalisation; an explicit hypothesis wherever used. -/
def OAP47 : Prop :=
  ∀ (M : Type u) [EffectMonoid M], DirectedComplete M → IsBooleanEM M →
    ∃ (B : Type u) (_ : CompleteBooleanAlgebra B), Nonempty (@EMIso M B _ (booleanEffectMonoid B))

/-! ### `[0,1]_R` of an ordered ring (SEA 31) -/

section Interval

variable {R : Type u} [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]

/-- In the interval effect algebra `[0,1]_R`, a list whose values sum to
`s` in `R` has sum `s`. -/
theorem interval_isSumOf (h01 : (0 : R) ≤ 1) :
    ∀ (l : List (Set.Icc (0 : R) 1)) (s : Set.Icc (0 : R) 1),
      (l.map Subtype.val).sum = s.1 →
        @PCM.IsSumOf _ (orderIntervalEffectAlgebra R 1 h01).toPCM l s := by
  let _ := orderIntervalEffectAlgebra R 1 h01
  intro l
  induction l with
  | nil =>
    intro s hs
    have : s = 0 := Subtype.ext (by rw [← hs]; rfl)
    subst this; exact PCM.IsSumOf.nil
  | cons x l ih =>
    intro s hs
    simp only [List.map_cons, List.sum_cons] at hs
    have ht0 : (0 : R) ≤ (l.map Subtype.val).sum :=
      List.sum_nonneg (by intro y hy; obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy; exact z.2.1)
    have ht1 : (l.map Subtype.val).sum ≤ 1 := by
      have : (l.map Subtype.val).sum ≤ x.1 + (l.map Subtype.val).sum :=
        le_add_of_nonneg_left x.2.1
      exact le_trans this (by rw [hs]; exact s.2.2)
    have hperp : Perp x (⟨_, ht0, ht1⟩ : Set.Icc (0 : R) 1) := by
      show x.1 + (l.map Subtype.val).sum ≤ 1
      rw [hs]; exact s.2.2
    have := PCM.IsSumOf.cons (ih ⟨_, ht0, ht1⟩ rfl) hperp
    have e : ovee x (⟨_, ht0, ht1⟩ : Set.Icc (0 : R) 1) hperp = s := Subtype.ext hs
    rwa [e] at this

/-- **SEA 31** (`ex:CX`, second.tex:852, Example): the unit interval `[0,1]_R`
of a partially ordered unital ring `R` in which sums and products of positive
elements are positive is an effect monoid under the ring product.  (`0 ≤ 1`
is needed for `[0,1]_R` to be non-empty and is a hypothesis; closure of the
positive cone under `+` is `IsOrderedAddMonoid`, under `·` is `hmul`.) -/
@[instance_reducible] noncomputable def intervalEffectMonoid (h01 : (0 : R) ≤ 1)
    (hmul : ∀ a b : R, 0 ≤ a → 0 ≤ b → 0 ≤ a * b) : EffectMonoid (Set.Icc (0 : R) 1) :=
  { orderIntervalEffectAlgebra R 1 h01 with
    mul := fun a b => ⟨a.1 * b.1, hmul _ _ a.2.1 b.2.1, by
      have h1 : a.1 * b.1 ≤ a.1 := by
        have := hmul a.1 (1 - b.1) a.2.1 (sub_nonneg.mpr b.2.2)
        rw [mul_sub, mul_one] at this
        exact sub_nonneg.mp this
      exact le_trans h1 a.2.2⟩
    one_mul := fun a => Subtype.ext (one_mul a.1)
    mul_one := fun a => Subtype.ext (mul_one a.1)
    mul_assoc := fun a b c => Subtype.ext (mul_assoc a.1 b.1 c.1)
    distrib := by
      intro a b c d hab hcd
      refine interval_isSumOf h01 _ _ ?_
      show a.1 * c.1 + (b.1 * c.1 + (a.1 * d.1 + (b.1 * d.1 + 0))) = (a.1 + b.1) * (c.1 + d.1)
      noncomm_ring }

end Interval

/-- `C(X, ℝ)` with the pointwise order: positive elements are closed under
`+` and `·`, and `0 ≤ 1`. -/
theorem cx_mul_nonneg {X : Type u} [TopologicalSpace X] (f g : C(X, ℝ)) (hf : 0 ≤ f)
    (hg : 0 ≤ g) : 0 ≤ f * g :=
  ContinuousMap.le_def.mpr fun x => by
    simpa using mul_nonneg (ContinuousMap.le_def.mp hf x) (ContinuousMap.le_def.mp hg x)

theorem cx_zero_le_one {X : Type u} [TopologicalSpace X] : (0 : C(X, ℝ)) ≤ 1 :=
  ContinuousMap.le_def.mpr fun x => by simp

/-- The unit interval `[0,1]_{C(X)}` of continuous functions `X → [0,1]`. -/
abbrev CXI (X : Type u) [TopologicalSpace X] : Type u := Set.Icc (0 : C(X, ℝ)) 1

noncomputable instance CXI.effectMonoid (X : Type u) [TopologicalSpace X] :
    EffectMonoid (CXI X) :=
  intervalEffectMonoid cx_zero_le_one cx_mul_nonneg

/-- **SEA 31** (`ex:CX`, second.tex:852, Example): for a compact Hausdorff
space `X`, `[0,1]_{C(X)}` is a commutative effect monoid.  (Compactness is not
needed for this.) -/
theorem sea31_CX_commutative (X : Type u) [TopologicalSpace X] :
    EffectMonoid.Commutative (CXI X) := fun a b => Subtype.ext (mul_comm a.1 b.1)

/-- **SEA 31** (`ex:CX`, second.tex:852, Example): a non-commutative effect
monoid that is not a SEA — the theses' `LexNC` example (eff.tex 178III.4,
after `[basmaster, Cor. 51]`), where `e₃ ⊙ e₂ = 0` but `e₂ ⊙ e₃ = e₅ ≠ 0`, so
S3 fails. -/
theorem sea31_noncommutative_not_sea :
    ¬ @EffectMonoid.Commutative _ LexNC.effectMonoid ∧
    ∃ a b : Set.Icc (0 : LexNC.V) LexNC.u,
      @HMul.hMul _ _ _ (@instHMul _ LexNC.effectMonoid.toMul) a b = 0 ∧
      @HMul.hMul _ _ _ (@instHMul _ LexNC.effectMonoid.toMul) b a ≠ 0 := by
  refine ⟨LexNC.not_commutative, ⟨LexNC.e3, LexNC.e3_mem⟩, ⟨LexNC.e2, LexNC.e2_mem⟩, ?_, ?_⟩
  · apply Subtype.ext
    show LexNC.vmul LexNC.e3 LexNC.e2 = 0
    refine LexNC.LexR.ext ?_ (LexNC.LexR.ext ?_ (LexNC.LexR.ext ?_ (LexNC.LexR.ext ?_ ?_))) <;>
      simp [LexNC.vmul, LexNC.e2, LexNC.e3, LexNC.nmul]
  · intro h
    have h3 : LexNC.vmul LexNC.e2 LexNC.e3 = 0 := congrArg Subtype.val h
    have h4 := congrArg (fun v : LexNC.V => v.tl.tl.tl.tl) h3
    simp only [LexNC.vmul, LexNC.e2, LexNC.e3, LexNC.nmul, LexNC.LexR.hd_mk, LexNC.LexR.tl_mk,
      LexNC.LexR.tl_add, LexNC.LexR.tl_smul, LexNC.LexR.tl_zero] at h4
    norm_num at h4

/-- **SEA 31** (second.tex:695, the sentence after Example 31): an effect
monoid with `a ⊙ b = 0 ⇒ b ⊙ a = 0` is a SEA with `a ∘ b = a ⊙ b`. -/
@[instance_reducible] noncomputable def emSEA (M : Type u) [EffectMonoid M] (h3 : ∀ a b : M, a * b = 0 → b * a = 0) :
    SEAlgebra M where
  seq a b := a * b
  seq_add c a b h := by
    obtain ⟨h', e⟩ := emon_mul_ovee c h
    exact ⟨h', e.symm⟩
  one_seq := EffectMonoid.one_mul
  seq_zero_comm := h3
  seq_comm_orth := by
    intro a b hab
    show a * orth b = orth b * a
    obtain ⟨h1, e1⟩ := emon_mul_ovee a (EffectAlgebra.perp_orth b)
    obtain ⟨h2, e2⟩ := emon_ovee_mul a (EffectAlgebra.perp_orth b)
    rw [EffectAlgebra.ovee_orth, EffectMonoid.mul_one] at e1
    rw [EffectAlgebra.ovee_orth, EffectMonoid.one_mul] at e2
    have hab' : a * b = b * a := hab
    have h2' : Perp (a * b) (orth b * a) := by rw [hab']; exact h2
    refine cancel_left h1 h2' ?_
    rw [← e1, PCM.ovee_congr hab' rfl h2' h2, ← e2]
  seq_comm_assoc := fun _ c => EffectMonoid.mul_assoc _ _ c
  seq_comm_compat := by
    intro a b c h hca hcb
    have hca' : c * a = a * c := hca
    have hcb' : c * b = b * c := hcb
    refine ⟨?_, ?_⟩
    · show c * (a * b) = a * b * c
      rw [← EffectMonoid.mul_assoc, hca', EffectMonoid.mul_assoc, hcb', EffectMonoid.mul_assoc]
    · show c * ovee a b h = ovee a b h * c
      obtain ⟨h1, e1⟩ := emon_mul_ovee c h
      obtain ⟨h2, e2⟩ := emon_ovee_mul c h
      rw [e1, e2]; exact PCM.ovee_congr hca' hcb' _ _
  seq_comm_seq := by
    intro a b c hca hcb
    have hca' : c * a = a * c := hca
    have hcb' : c * b = b * c := hcb
    show c * (a * b) = a * b * c
    rw [← EffectMonoid.mul_assoc, hca', EffectMonoid.mul_assoc, hcb', EffectMonoid.mul_assoc]

/-! ### Commutative SEAs are commutative effect monoids (SEA 32) -/

section CommSEA

variable {E : Type u} [EffectAlgebra E] [SEAlgebra E]

/-- A commutative SEA as an effect monoid, with `a ⊙ b := a ∘ b`. -/
@[instance_reducible] noncomputable def seaToEM (hc : IsCommutativeSEA E) : EffectMonoid E :=
  { (inferInstance : EffectAlgebra E) with
    mul := fun a b => a ⊙ b
    one_mul := one_seq
    mul_one := seq_one
    mul_assoc := fun a b c => ((hc a b).assoc c).symm
    distrib := by
      intro a b c d hab hcd
      -- `(a ⋁ b) ⊙ c = c ⊙ (a ⋁ b) = c ⊙ a ⋁ c ⊙ b = a ⊙ c ⋁ b ⊙ c`
      have col : ∀ x : E, ∃ h : Perp (a ⊙ x) (b ⊙ x), ovee a b hab ⊙ x = ovee (a ⊙ x) (b ⊙ x) h := by
        intro x
        obtain ⟨h1, e1⟩ := seq_ovee x hab
        have ea : x ⊙ a = a ⊙ x := hc x a
        have eb : x ⊙ b = b ⊙ x := hc x b
        have h2 : Perp (a ⊙ x) (b ⊙ x) := by rw [← ea, ← eb]; exact h1
        refine ⟨h2, ?_⟩
        rw [← hc x (ovee a b hab), e1]; exact PCM.ovee_congr ea eb _ _
      obtain ⟨hc', ec⟩ := col c
      obtain ⟨hd', ed⟩ := col d
      obtain ⟨h', e⟩ := seq_ovee (ovee a b hab) hcd
      have h'' : Perp (ovee (a ⊙ c) (b ⊙ c) hc') (ovee (a ⊙ d) (b ⊙ d) hd') := by
        rw [← ec, ← ed]; exact h'
      have := isSumOf_append (isSumOf_pair hc') (isSumOf_pair hd') h''
      have e2 : ovee (ovee (a ⊙ c) (b ⊙ c) hc') (ovee (a ⊙ d) (b ⊙ d) hd') h'' =
          ovee a b hab ⊙ ovee c d hcd := by
        rw [e]; exact PCM.ovee_congr ec.symm ed.symm _ _
      rw [e2] at this
      exact this }

theorem seaToEM_mul (hc : IsCommutativeSEA E) (a b : E) :
    @HMul.hMul E E E (@instHMul E (seaToEM hc).toMul) a b = a ⊙ b := rfl

/-- **SEA 32** (`prop:commutativemonoidissequential`, second.tex:878,
Example), first claim, SEA ⇒ EM: a commutative SEA is a commutative effect
monoid with `a ⊙ b := a ∘ b` (same effect algebra). -/
theorem sea32_commSEA_to_EM (hc : IsCommutativeSEA E) :
    @EffectMonoid.Commutative E (seaToEM hc) ∧
    (seaToEM hc).toEffectAlgebra = (inferInstance : EffectAlgebra E) :=
  ⟨fun a b => hc a b, rfl⟩

end CommSEA

/-- **SEA 32** (`prop:commutativemonoidissequential`, second.tex:878,
Example), first claim, EM ⇒ SEA: a commutative effect monoid is a commutative
SEA with `a ∘ b := a ⊙ b` (the theses' `commEffectMonoidSEA`, eff.tex 225V,
plus the unconditional S5). -/
@[instance_reducible] noncomputable def commEMToSEA (M : Type u) [EffectMonoid M] (hc : EffectMonoid.Commutative M) :
    SEAlgebra M :=
  emSEA M (fun a b h => (hc b a).trans h)

theorem sea32_commEM_to_SEA (M : Type u) [EffectMonoid M] (hc : EffectMonoid.Commutative M) :
    (∀ a b : M, @SequentialEffectAlgebra.seq M _ (commEMToSEA M hc).toSequentialEffectAlgebra a b
      = a * b) ∧ @IsCommutativeSEA M _ (commEMToSEA M hc) :=
  ⟨fun _ _ => rfl, fun a b => hc a b⟩

/-- **SEA 32** (`prop:commutativemonoidissequential`, second.tex:878,
Example), second claim, ⇒: a normal commutative SEA is a directed-complete
commutative effect monoid. -/
theorem sea32_normal_to_dc {E : Type u} [EffectAlgebra E] [NormalSEA E] (hc : IsCommutativeSEA E) :
    @DirectedComplete E (seaToEM hc).toEffectAlgebra ∧ @EffectMonoid.Commutative E (seaToEM hc) :=
  ⟨(show DirectedComplete E from NormalSEA.directedComplete), fun a b => hc a b⟩

/-- **OAP 43** (`thm:multisnormal`, first.tex:1525), in the form SEA 32 uses
(footnote: "the product in a directed-complete commutative effect monoid is
always normal"): in a directed-complete effect monoid, `a ⊙ (–)` preserves
directed suprema.  Not proved here — waits on OAP 43. -/
def OAP43 : Prop :=
  ∀ (M : Type u) [EffectMonoid M], DirectedComplete M →
    ∀ (a : M) {S : Set M} {x : M}, EDirected S → EIsSup S x → EIsSup ((a * ·) '' S) (a * x)

/-- **SEA 32** (`prop:commutativemonoidissequential`, second.tex:878,
Example), second claim, ⇐, given OAP 43: a directed-complete commutative
effect monoid is a normal commutative SEA with `a ∘ b := a ⊙ b`. -/
@[instance_reducible] noncomputable def sea32_dc_to_normal (h43 : OAP43.{u}) (M : Type u) [EffectMonoid M]
    (hc : EffectMonoid.Commutative M) (hdc : DirectedComplete M) : NormalSEA M :=
  { commEMToSEA M hc with
    directedComplete := hdc
    seq_sup := fun a _ _ hS hx => h43 M hdc a hS hx
    comm_sup := fun a _ x _ _ _ => hc a x }

-- **SEA 33** (second.tex:883, Remark): Gudder's "distributive" SEAs are the
-- effect monoids with `a ⊙ b = 0 ⇔ b ⊙ a = 0` (cf. `emSEA`); no declaration.

/-! ### Corners of effect monoids (SEA 34) -/

section EMCorner

variable {M : Type u} [EffectMonoid M]

theorem emon_split_right' (x q : M) :
    ∃ h : Perp (x * q) (x * orth q), ovee (x * q) (x * orth q) h = x := by
  obtain ⟨h', e⟩ := emon_mul_ovee x (EffectAlgebra.perp_orth q)
  rw [EffectAlgebra.ovee_orth, EffectMonoid.mul_one] at e
  exact ⟨h', e.symm⟩

theorem emon_split_left' (x q : M) :
    ∃ h : Perp (q * x) (orth q * x), ovee (q * x) (orth q * x) h = x := by
  obtain ⟨h', e⟩ := emon_ovee_mul x (EffectAlgebra.perp_orth q)
  rw [EffectAlgebra.ovee_orth, EffectMonoid.one_mul] at e
  exact ⟨h', e.symm⟩

theorem em_idem_mul_orth {p : M} (hp : p * p = p) : p * orth p = 0 := by
  obtain ⟨h, e⟩ := emon_split_right' p p
  have h' : Perp p (p * orth p) := by have := h; rwa [hp] at this
  rw [PCM.ovee_congr hp rfl h h'] at e
  exact eq_zero_of_ovee_eq_self _ e

theorem em_idem_orth_mul {p : M} (hp : p * p = p) : orth p * p = 0 := by
  obtain ⟨h, e⟩ := emon_split_left' p p
  have h' : Perp p (orth p * p) := by have := h; rwa [hp] at this
  rw [PCM.ovee_congr hp rfl h h'] at e
  exact eq_zero_of_ovee_eq_self _ e

theorem em_idem_orth {p : M} (hp : p * p = p) : orth p * orth p = orth p := by
  obtain ⟨h, e⟩ := emon_split_left' (orth p) p
  rw [PCM.ovee_congr (em_idem_mul_orth hp) rfl h (PCM.zero_perp _), zero_ovee_eq] at e
  exact e

/-- **OAP 20** (`lem:idempotentscommute`, first.tex:707), proved here because
it is cheap: an idempotent `p` of an effect monoid commutes with everything.
(`p a p⊥ ≼ p p⊥ = 0` gives `p a = p a p`; `p⊥ a p ≼ p⊥ p = 0` gives
`a p = p a p`.) -/
theorem em_idempotent_central {p : M} (hp : p * p = p) (a : M) : p * a = a * p := by
  have z1 : p * a * orth p = 0 := by
    rw [EffectMonoid.mul_assoc]
    refine eq_zero_of_le_zero ?_
    have := emon_mul_mono_right p (emon_mul_le_self_right a (orth p))
    rwa [em_idem_mul_orth hp] at this
  have z2 : orth p * (a * p) = 0 := by
    refine eq_zero_of_le_zero ?_
    have := emon_mul_mono_right (orth p) (emon_mul_le_self_right a p)
    rwa [em_idem_orth_mul hp] at this
  have e1 : p * a = p * a * p := by
    obtain ⟨h, e⟩ := emon_split_right' (p * a) p
    rw [PCM.ovee_congr rfl z1 h (PCM.perp_zero _), ovee_zero_eq] at e
    exact e.symm
  have e2 : a * p = p * (a * p) := by
    obtain ⟨h, e⟩ := emon_split_left' (a * p) p
    rw [PCM.ovee_congr rfl z2 h (PCM.perp_zero _), ovee_zero_eq] at e
    exact e.symm
  rw [e1, e2, EffectMonoid.mul_assoc]

end EMCorner


section EMCorner2

variable {M : Type u} [EffectMonoid M]

theorem em_le_idem_mul_left {p a : M} (hp : p * p = p) (ha : a ≼ p) : p * a = a := by
  have z : orth p * a = 0 := eq_zero_of_le_zero (by
    have := emon_mul_mono_right (orth p) ha; rwa [em_idem_orth_mul hp] at this)
  obtain ⟨h, e⟩ := emon_split_left' a p
  rw [PCM.ovee_congr rfl z h (PCM.perp_zero _), ovee_zero_eq] at e
  exact e

theorem em_le_idem_mul_right {p a : M} (hp : p * p = p) (ha : a ≼ p) : a * p = a := by
  rw [← em_idempotent_central hp]; exact em_le_idem_mul_left hp ha

theorem em_orth_le_mul_zero {p a : M} (hp : p * p = p) (ha : a ≼ orth p) : p * a = 0 :=
  eq_zero_of_le_zero (by
    have := emon_mul_mono_right p ha; rwa [em_idem_mul_orth hp] at this)

/-- A list of elements of `[0,p]` whose sum in `M` exists (and so is `≼ p`)
has that sum in `[0,p]`. -/
theorem downset_isSumOf {E : Type u} [EffectAlgebra E] {p : E} :
    ∀ (l : List (Downset p)) (s : Downset p),
      PCM.IsSumOf (l.map Subtype.val) s.1 → PCM.IsSumOf l s := by
  intro l
  induction l with
  | nil =>
    intro s hs
    have : s = 0 := Subtype.ext (PCM.isSumOf_nil_iff.mp hs)
    subst this; exact PCM.IsSumOf.nil
  | cons x l ih =>
    intro s hs
    obtain ⟨t, ht, h, e⟩ := PCM.isSumOf_cons_iff.mp hs
    have hle : ovee x.1 t h ≼ p := by rw [e]; exact s.2
    have htp : t ≼ p := le_trans' (right_le_ovee h) hle
    have hD : Perp x (⟨t, htp⟩ : Downset p) := ⟨h, hle⟩
    have := PCM.IsSumOf.cons (ih ⟨t, htp⟩ ht) hD
    have e' : ovee x (⟨t, htp⟩ : Downset p) hD = s := Subtype.ext e
    rwa [e'] at this

/-- **SEA 34** (`cornersexample`, second.tex:887, Example): for an idempotent
`p` of an effect monoid, the left corner `pM` (as `[0,p]`, `emCorner_eq`) is
an effect monoid with unit `p` and the operations of `M`. -/
@[instance_reducible] noncomputable def cornerEM {p : M} (hp : p * p = p) : EffectMonoid (Downset p) :=
  { downsetEA p with
    mul := fun a b => ⟨a.1 * b.1, le_trans' (emon_mul_le_self a.1 b.1) a.2⟩
    one_mul := fun a => Subtype.ext (em_le_idem_mul_left hp a.2)
    mul_one := fun a => Subtype.ext (em_le_idem_mul_right hp a.2)
    mul_assoc := fun a b c => Subtype.ext (EffectMonoid.mul_assoc a.1 b.1 c.1)
    distrib := by
      intro a b c d hab hcd
      exact downset_isSumOf _ _ (EffectMonoid.distrib hab.1 hcd.1) }

theorem cornerEM_mul_val {p : M} (hp : p * p = p) (a b : Downset p) :
    (@HMul.hMul _ _ _ (@instHMul _ (cornerEM hp).toMul) a b).1 = a.1 * b.1 := rfl

/-- **SEA 34**: `pM = {p ⊙ e ; e ∈ M}` is `[0,p]`, and it is also the right
corner `Mp` ("analogous facts hold for the right corner": since `p` is
central, OAP 20, the two corners coincide). -/
theorem emCorner_eq {p : M} (hp : p * p = p) :
    Set.range (p * ·) = {a | a ≼ p} ∧ Set.range (· * p) = Set.range (p * ·) := by
  refine ⟨?_, ?_⟩
  · ext a; constructor
    · rintro ⟨b, rfl⟩; exact emon_mul_le_self p b
    · intro h; exact ⟨a, em_le_idem_mul_left hp h⟩
  · ext a; constructor
    · rintro ⟨b, rfl⟩; exact ⟨b, em_idempotent_central hp b⟩
    · rintro ⟨b, rfl⟩; exact ⟨b, (em_idempotent_central hp b).symm⟩

/-- **SEA 34**: in the corner, the complement is `(p ⊙ e)⊥ = p ⊙ e⊥`. -/
theorem emCorner_orth {p : M} (e : M) :
    (orth (⟨p * e, emon_mul_le_self p e⟩ : Downset p)).1 = p * orth e := by
  obtain ⟨h, e1⟩ := emon_mul_ovee p (EffectAlgebra.perp_orth e)
  rw [EffectAlgebra.ovee_orth, EffectMonoid.mul_one] at e1
  exact ominus_eq _ h e1.symm

end EMCorner2

/-! ### Direct sums of effect monoids and isomorphisms -/

section ProdEM

theorem isSumOf_prod {E F : Type u} [EffectAlgebra E] [EffectAlgebra F] :
    ∀ (l1 : List E) (l2 : List F) (s1 : E) (s2 : F),
      PCM.IsSumOf l1 s1 → PCM.IsSumOf l2 s2 → l1.length = l2.length →
        PCM.IsSumOf (List.zipWith Prod.mk l1 l2) (s1, s2) := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 s1 s2 h1 h2 hl
    cases l2 with
    | nil =>
      rw [PCM.isSumOf_nil_iff.mp h1, PCM.isSumOf_nil_iff.mp h2]; exact PCM.IsSumOf.nil
    | cons _ _ => simp at hl
  | cons x l1 ih =>
    intro l2 s1 s2 h1 h2 hl
    cases l2 with
    | nil => simp at hl
    | cons y l2 =>
      obtain ⟨t1, ht1, hp1, rfl⟩ := PCM.isSumOf_cons_iff.mp h1
      obtain ⟨t2, ht2, hp2, rfl⟩ := PCM.isSumOf_cons_iff.mp h2
      simp only [List.length_cons, add_left_inj] at hl
      exact PCM.IsSumOf.cons (a := (x, y)) (ih l2 t1 t2 ht1 ht2 hl) ⟨hp1, hp2⟩

/-- The direct sum of two effect monoids, componentwise. -/
noncomputable instance prodEM (M N : Type u) [EffectMonoid M] [EffectMonoid N] :
    EffectMonoid (M × N) :=
  { prodEffectAlgebra M N with
    mul := fun a b => (a.1 * b.1, a.2 * b.2)
    one_mul := fun a => Prod.ext (EffectMonoid.one_mul a.1) (EffectMonoid.one_mul a.2)
    mul_one := fun a => Prod.ext (EffectMonoid.mul_one a.1) (EffectMonoid.mul_one a.2)
    mul_assoc := fun a b c =>
      Prod.ext (EffectMonoid.mul_assoc a.1 b.1 c.1) (EffectMonoid.mul_assoc a.2 b.2 c.2)
    distrib := by
      intro a b c d hab hcd
      exact isSumOf_prod _ _ _ _ (EffectMonoid.distrib hab.1 hcd.1)
        (EffectMonoid.distrib hab.2 hcd.2) rfl }

end ProdEM

universe w

namespace EMIso

variable {M : Type u} {N : Type v} {K : Type w} [EffectMonoid M] [EffectMonoid N] [EffectMonoid K]

theorem apply_symm (f : EMIso M N) (b : N) : f.toFun (f.invFun b) = b := f.right_inv b

theorem symm_apply (f : EMIso M N) (a : M) : f.invFun (f.toFun a) = a := f.left_inv a

theorem injective (f : EMIso M N) : Function.Injective f.toFun := f.toEquiv.injective

/-- The inverse of an effect monoid isomorphism. -/
def symm (f : EMIso M N) : EMIso N M where
  toEquiv := f.toEquiv.symm
  map_one := f.injective (by
    show f.toFun (f.invFun 1) = f.toFun 1; rw [apply_symm, f.map_one])
  perp_iff := fun a b => by
    have := f.perp_iff (f.invFun a) (f.invFun b)
    rw [apply_symm, apply_symm] at this
    exact this.symm
  map_ovee := fun a b h h' => f.injective (by
    show f.toFun (f.invFun (ovee a b h)) = f.toFun (ovee (f.invFun a) (f.invFun b) h')
    rw [apply_symm, f.map_ovee (f.invFun a) (f.invFun b) h' ((f.perp_iff _ _).mpr h')]
    exact PCM.ovee_congr (apply_symm f a).symm (apply_symm f b).symm _ _)
  map_mul := fun a b => f.injective (by
    show f.toFun (f.invFun (a * b)) = f.toFun (f.invFun a * f.invFun b)
    rw [apply_symm, f.map_mul, apply_symm, apply_symm])

/-- Composition of effect monoid isomorphisms. -/
def trans (f : EMIso M N) (g : EMIso N K) : EMIso M K where
  toEquiv := f.toEquiv.trans g.toEquiv
  map_one := by
    show g.toFun (f.toFun 1) = 1; rw [f.map_one, g.map_one]
  perp_iff := fun a b => (g.perp_iff _ _).trans (f.perp_iff a b)
  map_ovee := fun a b h h' => by
    show g.toFun (f.toFun (ovee a b h)) = ovee (g.toFun (f.toFun a)) (g.toFun (f.toFun b)) h'
    rw [f.map_ovee a b h ((f.perp_iff a b).mpr h)]
    exact g.map_ovee _ _ _ _
  map_mul := fun a b => by
    show g.toFun (f.toFun (a * b)) = g.toFun (f.toFun a) * g.toFun (f.toFun b)
    rw [f.map_mul, g.map_mul]

end EMIso

/-- The direct sum of two effect monoid isomorphisms. -/
def EMIso.prodMap {M M' N N' : Type u} [EffectMonoid M] [EffectMonoid M'] [EffectMonoid N]
    [EffectMonoid N'] (f : EMIso M M') (g : EMIso N N') : EMIso (M × N) (M' × N') where
  toEquiv := f.toEquiv.prodCongr g.toEquiv
  map_one := Prod.ext f.map_one g.map_one
  perp_iff := fun a b => and_congr (f.perp_iff a.1 b.1) (g.perp_iff a.2 b.2)
  map_ovee := fun _ _ _ h' => Prod.ext (f.map_ovee _ _ _ h'.1) (g.map_ovee _ _ _ h'.2)
  map_mul := fun _ _ => Prod.ext (f.map_mul _ _) (g.map_mul _ _)

section CornerIso

variable {E : Type u} [EffectAlgebra E]

/-- Rearranging: if `a = a₁ ⋁ a₂`, `b = b₁ ⋁ b₂` and `(a₁ ⋁ b₁) ⊥ (a₂ ⋁ b₂)`,
then `a ⊥ b`. -/
theorem perp_of_parts {a1 a2 b1 b2 a b : E} (ha : ∃ h : Perp a1 a2, ovee a1 a2 h = a)
    (hb : ∃ h : Perp b1 b2, ovee b1 b2 h = b) (h1 : Perp a1 b1) (h2 : Perp a2 b2)
    (h12 : Perp (ovee a1 b1 h1) (ovee a2 b2 h2)) : Perp a b := by
  have hsum := isSumOf_append (isSumOf_pair h1) (isSumOf_pair h2) h12
  have hperm : ([a1, b1] ++ [a2, b2]).Perm ([a1, a2] ++ [b1, b2]) := by
    simp only [List.cons_append, List.nil_append]
    exact List.Perm.cons _ (List.Perm.swap _ _ _)
  obtain ⟨t, t', ht, ht', h, -⟩ := isSumOf_append_split (PCM.isSumOf_perm hperm hsum)
  obtain ⟨ha', ea⟩ := ha
  obtain ⟨hb', eb⟩ := hb
  have e1 := isSumOf_unique ht (isSumOf_pair ha')
  have e2 := isSumOf_unique ht' (isSumOf_pair hb')
  rw [ea] at e1; rw [eb] at e2
  subst e1; subst e2; exact h

end CornerIso

/-- **SEA 34** (`cornersexample`, second.tex:887, Example), the isomorphism
(OAP 21, `cor:corneriso`, proved here because it is cheap once idempotents
are central): for an idempotent `p` of an effect monoid,
`e ↦ (p ⊙ e, p⊥ ⊙ e)` is an isomorphism `M ≅ pM ⊕ p⊥M` of effect monoids. -/
noncomputable def sea34_cornerIso {M : Type u} [EffectMonoid M] {p : M} (hp : p * p = p) :
    @EMIso M (Downset p × Downset (orth p)) _
      (@prodEM _ _ (cornerEM hp) (cornerEM (em_idem_orth hp))) := by
  letI := cornerEM hp
  letI := cornerEM (em_idem_orth hp)
  have hp' : orth p * orth p = orth p := em_idem_orth hp
  have hxy : ∀ (x : Downset p) (y : Downset (orth p)), Perp x.1 y.1 := fun x y =>
    perp_of_le x.2 y.2 (EffectAlgebra.perp_orth p)
  have kill1 : ∀ y : Downset (orth p), p * y.1 = 0 := fun y => em_orth_le_mul_zero hp y.2
  have kill2 : ∀ x : Downset p, orth p * x.1 = 0 := fun x =>
    em_orth_le_mul_zero hp' (by rw [orth_orth]; exact x.2)
  refine
    { toFun := fun a => (⟨p * a, emon_mul_le_self p a⟩, ⟨orth p * a, emon_mul_le_self _ a⟩)
      invFun := fun xy => ovee xy.1.1 xy.2.1 (hxy xy.1 xy.2)
      left_inv := fun a => (emon_split_left' a p).2
      right_inv := ?_
      map_one := ?_
      perp_iff := ?_
      map_ovee := ?_
      map_mul := ?_ }
  · rintro ⟨x, y⟩
    obtain ⟨h1, e1⟩ := emon_mul_ovee p (hxy x y)
    obtain ⟨h2, e2⟩ := emon_mul_ovee (orth p) (hxy x y)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show p * ovee x.1 y.1 _ = x.1
      rw [e1, PCM.ovee_congr (em_le_idem_mul_left hp x.2) (kill1 y) h1 (PCM.perp_zero _),
        ovee_zero_eq]
    · show orth p * ovee x.1 y.1 _ = y.1
      rw [e2, PCM.ovee_congr (kill2 x) (em_le_idem_mul_left hp' y.2) h2 (PCM.zero_perp _),
        zero_ovee_eq]
  · exact Prod.ext (Subtype.ext (EffectMonoid.mul_one p))
      (Subtype.ext (EffectMonoid.mul_one (orth p)))
  · intro a b
    constructor
    · rintro ⟨⟨h1, hle1⟩, ⟨h2, hle2⟩⟩
      exact perp_of_parts (emon_split_left' a p) (emon_split_left' b p) h1 h2
        (perp_of_le hle1 hle2 (EffectAlgebra.perp_orth p))
    · intro h
      obtain ⟨h1, e1⟩ := emon_mul_ovee p h
      obtain ⟨h2, e2⟩ := emon_mul_ovee (orth p) h
      exact ⟨⟨h1, by rw [← e1]; exact emon_mul_le_self _ _⟩,
        ⟨h2, by rw [← e2]; exact emon_mul_le_self _ _⟩⟩
  · intro a b h h'
    obtain ⟨h1, e1⟩ := emon_mul_ovee p h
    obtain ⟨h2, e2⟩ := emon_mul_ovee (orth p) h
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  · intro a b
    have key : ∀ q : M, q * q = q → q * (a * b) = q * a * (q * b) := by
      intro q hq
      rw [← EffectMonoid.mul_assoc (q * a), ← em_idempotent_central hq (q * a),
        ← EffectMonoid.mul_assoc q q, hq, EffectMonoid.mul_assoc]
    exact Prod.ext (Subtype.ext (key p hp)) (Subtype.ext (key (orth p) hp'))

/-! ### The representation theorem (SEA 35–37) -/

/-- **SEA 35** (`thm:first`, second.tex:907, Theorem), cited from OAP (it is
OAP 57 `thm:directedcompleteisconvex` with OAP 69 `mainthmdirectedcomplete`):
in every directed-complete effect monoid `M` there is an idempotent `p` such
that `pM` is a convex effect algebra and `p⊥M` is Boolean; furthermore
`pM ≅ [0,1]_{C(X)}` for an extremally disconnected compact Hausdorff `X`.
Not proved here — waits on OAP 57/69; an explicit hypothesis of SEA 36, 37. -/
def SEA35 : Prop :=
  ∀ (M : Type u) [EffectMonoid M], DirectedComplete M →
    ∃ (p : M) (hp : p * p = p), IsConvex (Downset p) ∧ (∀ a : M, a ≼ orth p → a * a = a) ∧
      ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X),
        ExtremallyDisconnected X ∧ Nonempty (@EMIso (Downset p) (CXI X) (cornerEM hp) _)

/-- SEA 35 with SEA 34 and OAP 47: every directed-complete effect monoid is
`[0,1]_{C(X)} ⊕ B` for an extremally disconnected compact Hausdorff `X` and a
complete Boolean algebra `B` (this is the form of OAP 69). -/
theorem dcem_structure (h35 : SEA35.{u}) (h47 : OAP47.{u}) (M : Type u) [EffectMonoid M]
    (hM : DirectedComplete M) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X),
      ExtremallyDisconnected X ∧ ∃ (B : Type u) (_ : CompleteBooleanAlgebra B),
        Nonempty (@EMIso M (CXI X × B) _ (@prodEM _ _ _ (booleanEffectMonoid B))) := by
  obtain ⟨p, hp, -, hbool, X, tX, cX, hX, edX, ⟨φ⟩⟩ := h35 M hM
  let _ := cornerEM hp
  let _ := cornerEM (em_idem_orth hp)
  have hdc : DirectedComplete (Downset (orth p)) := downset_directedComplete hM
  have hb : IsBooleanEM (Downset (orth p)) := fun a => Subtype.ext (hbool a.1 a.2)
  obtain ⟨B, cB, ⟨ψ⟩⟩ := h47 (Downset (orth p)) hdc hb
  let _ := booleanEffectMonoid B
  exact ⟨X, tX, cX, hX, edX, B, cB, ⟨(sea34_cornerIso hp).trans (φ.prodMap ψ)⟩⟩

section Bicommutant

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

/-- The bicommutant of a mutually commuting set, as a (commutative)
effect monoid (SEA 28 with SEA 32). -/
@[instance_reducible] noncomputable def bicommEM (S : Set E) (hS : ∀ a ∈ S, ∀ b ∈ S, Commutes a b) :
    EffectMonoid (bicommutantSub S).carrier :=
  seaToEM (sea28_bicommutant_commutative S hS).2

theorem bicommEM_dc (S : Set E) (hS : ∀ a ∈ S, ∀ b ∈ S, Commutes a b) :
    @DirectedComplete _ (bicommEM S hS).toEffectAlgebra :=
  (show DirectedComplete (bicommutantSub S).carrier from NormalSEA.directedComplete)

theorem singleton_commuting (a : E) : ∀ x ∈ ({a} : Set E), ∀ y ∈ ({a} : Set E), Commutes x y := by
  intro x hx y hy
  rw [Set.mem_singleton_iff] at hx hy
  subst hx; subst hy; rfl

/-- **SEA 36** (`seaspectral`, second.tex:917, Corollary; spectral theorem for
normal SEAs): for `a` in a normal SEA `E` there are an extremally
disconnected compact Hausdorff `X` and a complete Boolean algebra `B` with
`{a}'' ≅ [0,1]_{C(X)} ⊕ B`.  Proof as printed: `{a}''` is a commutative normal
SEA (SEA 28), hence a directed-complete effect monoid (SEA 32); apply SEA 35.
Uses SEA 35 and OAP 47 as hypotheses (the Boolean summand is a complete Boolean
algebra by OAP 47). -/
theorem sea36_spectral (h35 : SEA35.{u}) (h47 : OAP47.{u}) (a : E) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X),
      ExtremallyDisconnected X ∧ ∃ (B : Type u) (_ : CompleteBooleanAlgebra B),
        Nonempty (@EMIso (bicommutantSub ({a} : Set E)).carrier (CXI X × B)
          (bicommEM {a} (singleton_commuting a)) (@prodEM _ _ _ (booleanEffectMonoid B))) :=
  @dcem_structure h35 h47 _ (bicommEM {a} (singleton_commuting a))
    (bicommEM_dc {a} (singleton_commuting a))

end Bicommutant

section Sqrt

/-- Square roots exist and are unique in `[0,1]_{C(X)} ⊕ B`. -/
theorem cxb_sqrt (X : Type u) [TopologicalSpace X] (B : Type u) [CompleteBooleanAlgebra B] :
    letI := booleanEffectMonoid B
    (∀ z : CXI X × B, ∃ y : CXI X × B, y * y = z) ∧
      (∀ y z : CXI X × B, y * y = z * z → y = z) := by
  let _ := booleanEffectMonoid B
  have hmul : ∀ y z : CXI X × B, (y * z).1.1 = y.1.1 * z.1.1 ∧ (y * z).2 = y.2 ⊓ z.2 :=
    fun _ _ => ⟨rfl, rfl⟩
  refine ⟨fun z => ?_, fun y z h => ?_⟩
  · -- the pointwise square root on the `C(X)` part, the element itself on the Boolean part
    let f : C(X, ℝ) := ⟨fun x => Real.sqrt (z.1.1 x), Real.continuous_sqrt.comp z.1.1.continuous⟩
    have hf0 : (0 : C(X, ℝ)) ≤ f := ContinuousMap.le_def.mpr fun x => by
      simp [f, Real.sqrt_nonneg]
    have hf1 : f ≤ 1 := ContinuousMap.le_def.mpr fun x => by
      simp only [f, ContinuousMap.coe_mk, ContinuousMap.one_apply]
      exact Real.sqrt_le_one.mpr (by simpa using ContinuousMap.le_def.mp z.1.2.2 x)
    refine ⟨(⟨f, hf0, hf1⟩, z.2), Prod.ext (Subtype.ext ?_) (inf_idem z.2)⟩
    ext x
    show Real.sqrt (z.1.1 x) * Real.sqrt (z.1.1 x) = z.1.1 x
    exact Real.mul_self_sqrt (by simpa using ContinuousMap.le_def.mp z.1.2.1 x)
  · refine Prod.ext (Subtype.ext ?_) ?_
    · ext x
      have e : y.1.1 x * y.1.1 x = z.1.1 x * z.1.1 x := by
        have := congrArg (fun w : CXI X × B => w.1.1 x) h
        simpa [hmul] using this
      have hy : 0 ≤ y.1.1 x := by simpa using ContinuousMap.le_def.mp y.1.2.1 x
      have hz : 0 ≤ z.1.1 x := by simpa using ContinuousMap.le_def.mp z.1.2.1 x
      rw [← Real.sqrt_mul_self hy, ← Real.sqrt_mul_self hz, e]
    · have := congrArg Prod.snd h
      simpa [hmul] using this

/-- In a directed-complete effect monoid (given SEA 35 and OAP 47) every
element has a unique square root: transport `cxb_sqrt` along SEA 36's
isomorphism. -/
theorem dcem_sqrt (h35 : SEA35.{u}) (h47 : OAP47.{u}) (M : Type u) [EffectMonoid M]
    (hM : DirectedComplete M) :
    (∀ x : M, ∃ y : M, y * y = x) ∧ (∀ y z : M, y * y = z * z → y = z) := by
  obtain ⟨X, tX, cX, hX, -, B, cB, ⟨φ⟩⟩ := dcem_structure h35 h47 M hM
  let _ := booleanEffectMonoid B
  obtain ⟨hex, huniq⟩ := cxb_sqrt X B
  refine ⟨fun x => ?_, fun y z h => ?_⟩
  · obtain ⟨w, hw⟩ := hex (φ.toFun x)
    refine ⟨φ.invFun w, φ.injective ?_⟩
    rw [φ.map_mul, EMIso.apply_symm]
    exact hw
  · apply φ.injective
    apply huniq
    have e1 := φ.map_mul y y
    have e2 := φ.map_mul z z
    rw [h] at e1
    exact e1.symm.trans e2

/-- **SEA 37** (second.tex:933, Corollary): every element `a` of a normal SEA
has a unique square root, `∃! b, b ⊙ b = a` (answering Gudder's Problem 20 for
normal SEAs).  Proof as printed: a root exists in `{a}''` (SEA 36); if
`c ⊙ c = a` then `c | a`, so `c` commutes with the root `b ∈ {a}''`, and `b`
and `c` are both roots of `a` in the commutative `{b, c}''`, where roots are
unique.  Uses SEA 35 and OAP 47 as hypotheses. -/
theorem sea37_sqrt (h35 : SEA35.{u}) (h47 : OAP47.{u}) {E : Type u} [EffectAlgebra E]
    [NormalSEA E] (a : E) : ∃! b : E, b ⊙ b = a := by
  -- existence, in `{a}''`
  let _ := bicommEM {a} (singleton_commuting a)
  obtain ⟨hex, -⟩ := dcem_sqrt h35 h47 _ (bicommEM_dc {a} (singleton_commuting a))
  obtain ⟨y, hy⟩ := hex ⟨a, subset_bicommutant {a} rfl⟩
  have hy' : y.1 ⊙ y.1 = a := congrArg Subtype.val hy
  refine ⟨y.1, hy', fun c hc => ?_⟩
  -- `c | a`, hence `c ∈ {a}'` and `y | c`
  have hca : c ∈ commutant ({a} : Set E) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs, ← hc]
    exact (commutes_refl c).seq (commutes_refl c)
  have hyc : Commutes y.1 c := y.2 c hca
  let S : Set E := {y.1, c}
  have hS : ∀ u ∈ S, ∀ v ∈ S, Commutes u v := by
    intro u hu v hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · exact hyc
    · exact hyc.symm
    · rfl
  let _ := bicommEM S hS
  obtain ⟨-, huniq⟩ := dcem_sqrt h35 h47 _ (bicommEM_dc S hS)
  have hyS : y.1 ∈ (bicommutantSub S).carrier := subset_bicommutant S (Or.inl rfl)
  have hcS : c ∈ (bicommutantSub S).carrier := subset_bicommutant S (Or.inr rfl)
  have := huniq ⟨c, hcS⟩ ⟨y.1, hyS⟩ (Subtype.ext (by
    show c ⊙ c = y.1 ⊙ y.1; rw [hc, hy']))
  exact congrArg Subtype.val this

end Sqrt


/-! ## The C*-algebra examples (SEA 13, 16) -/

section CStar

open scoped ComplexStarModule

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `[0,1]_A` with the effect algebra structure of SEA 4 (`u = 1`). -/
@[instance_reducible] noncomputable def cstarEA (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    EffectAlgebra (Set.Icc (0 : A) 1) :=
  orderIntervalEffectAlgebra A 1 zero_le_one

theorem rsmul_nonneg' {x : A} (hx : 0 ≤ x) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ (r : ℂ) • x :=
  Theses.A.CStar.ofReal_smul_nonneg hx hr

theorem rsmul_mono' {r : ℝ} (hr : 0 ≤ r) {x y : A} (h : x ≤ y) : (r : ℂ) • x ≤ (r : ℂ) • y := by
  have h1 := rsmul_nonneg' (sub_nonneg.mpr h) hr
  rw [smul_sub] at h1; exact sub_nonneg.mp h1

theorem rsmul_le_rsmul' {r s : ℝ} (h : r ≤ s) {x : A} (hx : 0 ≤ x) :
    (r : ℂ) • x ≤ (s : ℂ) • x := by
  have h1 := rsmul_nonneg' hx (sub_nonneg.mpr h)
  rw [Complex.ofReal_sub, sub_smul] at h1; exact sub_nonneg.mp h1

omit [PartialOrder A] [StarOrderedRing A] in
theorem rsmul_inv_smul {r : ℝ} (hr : r ≠ 0) (x : A) : ((r⁻¹ : ℝ) : ℂ) • ((r : ℂ) • x) = x := by
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr, Complex.ofReal_one, one_smul]

omit [PartialOrder A] [StarOrderedRing A] in
theorem rsmul_smul_inv {r : ℝ} (hr : r ≠ 0) (x : A) : (r : ℂ) • (((r⁻¹ : ℝ) : ℂ) • x) = x := by
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr, Complex.ofReal_one, one_smul]

/-- For `0 ≤ x`: `(‖x‖ + 1)⁻¹ x ≤ 1`. -/
theorem scale_le_one {x : A} (hx : 0 ≤ x) : (((‖x‖ + 1)⁻¹ : ℝ) : ℂ) • x ≤ 1 := by
  have hpos : (0 : ℝ) < ‖x‖ + 1 := by positivity
  have h0 : 0 ≤ (((‖x‖ + 1)⁻¹ : ℝ) : ℂ) • x := rsmul_nonneg' hx (inv_nonneg.mpr hpos.le)
  refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ h0).mp ?_
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),
    inv_mul_le_iff₀ hpos]
  linarith

/-- The self-adjoint elements underlying a subset of `[0,1]_A`. -/
def saImage (S : Set (Set.Icc (0 : A) 1)) : Set (selfAdjoint A) :=
  (fun x : Set.Icc (0 : A) 1 => (⟨x.1, IsSelfAdjoint.of_nonneg x.2.1⟩ : selfAdjoint A)) '' S

/-- A least upper bound among self-adjoint elements of a non-empty subset of
`[0,1]_A` is its supremum in `[0,1]_A`. -/
theorem isSup_of_isLUB {S : Set (Set.Icc (0 : A) 1)} (hne : S.Nonempty) {s : selfAdjoint A}
    (hs : IsLUB (saImage S) s) :
    ∃ h : (s : A) ∈ Set.Icc (0 : A) 1, @EIsSup _ (cstarEA A) S ⟨s, h⟩ := by
  let _ := cstarEA A
  obtain ⟨x0, hx0⟩ := hne
  have hs0 : (0 : A) ≤ s := le_trans x0.2.1 (hs.1 ⟨x0, hx0, rfl⟩)
  have hs1 : (s : A) ≤ 1 := by
    have : (⟨1, IsSelfAdjoint.one A⟩ : selfAdjoint A) ∈ upperBounds (saImage S) := by
      rintro _ ⟨a, _, rfl⟩; exact a.2.2
    exact hs.2 this
  refine ⟨⟨hs0, hs1⟩, fun a ha => (interval_le_iff 1 zero_le_one a _).mpr (hs.1 ⟨a, ha, rfl⟩),
    fun y hy => (interval_le_iff 1 zero_le_one _ y).mpr ?_⟩
  have : (⟨y.1, IsSelfAdjoint.of_nonneg y.2.1⟩ : selfAdjoint A) ∈ upperBounds (saImage S) := by
    rintro _ ⟨a, ha, rfl⟩; exact (interval_le_iff 1 zero_le_one a y).mp (hy a ha)
  exact hs.2 this

theorem saImage_directed {S : Set (Set.Icc (0 : A) 1)} (hS : @EDirected _ (cstarEA A) S) :
    (saImage S).Nonempty ∧ DirectedOn (· ≤ ·) (saImage S) ∧ BddAbove (saImage S) := by
  let _ := cstarEA A
  obtain ⟨⟨x0, hx0⟩, hdir⟩ := hS
  refine ⟨⟨_, x0, hx0, rfl⟩, ?_, ⟨⟨1, IsSelfAdjoint.one A⟩, by rintro _ ⟨a, _, rfl⟩; exact a.2.2⟩⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
  exact ⟨_, ⟨c, hc, rfl⟩, (interval_le_iff 1 zero_le_one a c).mp hac,
    (interval_le_iff 1 zero_le_one b c).mp hbc⟩

/-- A least upper bound among self-adjoint elements is one in `A`: an upper
bound of a non-empty set of self-adjoint elements is self-adjoint. -/
theorem isLUB_coe_of_isLUB {D : Set (selfAdjoint A)} (hne : D.Nonempty) {t : selfAdjoint A}
    (h : IsLUB D t) : IsLUB ((↑) '' D : Set A) (t : A) := by
  refine ⟨by rintro _ ⟨d, hd, rfl⟩; exact h.1 hd, fun c hc => ?_⟩
  obtain ⟨d0, hd0⟩ := hne
  have hcd : (d0 : A) ≤ c := hc ⟨d0, hd0, rfl⟩
  have hsa : IsSelfAdjoint c := by
    have h1 : IsSelfAdjoint (c - d0) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hcd)
    have := h1.add d0.2
    rwa [sub_add_cancel] at this
  have : (⟨c, hsa⟩ : selfAdjoint A) ∈ upperBounds D := fun d hd => hc ⟨d, hd, rfl⟩
  exact h.2 this

/-- **SEA 13** (second.tex:374, Example), first claim, `⇐`: if every
non-empty bounded directed set of self-adjoint elements of `A` has a least
upper bound, then `[0,1]_A` is directed complete. -/
theorem sea13_dc_of_bdc
    (h : ∀ D : Set (selfAdjoint A), D.Nonempty → DirectedOn (· ≤ ·) D → BddAbove D →
      ∃ s, IsLUB D s) : @DirectedComplete _ (cstarEA A) := by
  intro S hS
  obtain ⟨hne, hdir, hbdd⟩ := saImage_directed hS
  obtain ⟨s, hs⟩ := h _ hne hdir hbdd
  obtain ⟨hmem, hsup⟩ := isSup_of_isLUB hS.1 hs
  exact ⟨_, hsup⟩

/-- **SEA 13** (second.tex:374, Example), first claim, `⇒`: if `[0,1]_A` is
directed complete, then every non-empty bounded directed set `D` of
self-adjoint elements has a least upper bound.  (Shift `D` by one of its
elements `d₀` and scale into `[0,1]_A`; a second rescaling shows that the
supremum there is below every self-adjoint upper bound.) -/
theorem sea13_bdc_of_dc (hdc : @DirectedComplete _ (cstarEA A)) (D : Set (selfAdjoint A))
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hbdd : BddAbove D) : ∃ s, IsLUB D s := by
  let _ := cstarEA A
  obtain ⟨d0, hd0⟩ := hne
  obtain ⟨b, hb⟩ := hbdd
  have hc0 : (0 : A) ≤ (b : A) - d0 := sub_nonneg.mpr (hb hd0)
  set l : ℝ := (‖(b : A) - d0‖ + 1)⁻¹ with hl
  have hlpos : 0 < l := by rw [hl]; positivity
  have hl0 : 0 ≤ l := hlpos.le
  have mem : ∀ d : selfAdjoint A, d ∈ D → (d0 : A) ≤ d →
      (l : ℂ) • ((d : A) - d0) ∈ Set.Icc (0 : A) 1 := fun d hd h =>
    ⟨rsmul_nonneg' (sub_nonneg.mpr h) hl0,
      le_trans (rsmul_mono' hl0 (sub_le_sub_right (show (d : A) ≤ (b : A) from hb hd) _))
        (scale_le_one hc0)⟩
  let T : Set (Set.Icc (0 : A) 1) :=
    {x | ∃ (d : selfAdjoint A) (hd : d ∈ D) (h : (d0 : A) ≤ d), x = ⟨_, mem d hd h⟩}
  have hle_iff : ∀ x y : Set.Icc (0 : A) 1, x ≼ y ↔ (x : A) ≤ y :=
    interval_le_iff 1 zero_le_one
  have hT : EDirected T := by
    refine ⟨⟨_, d0, hd0, le_rfl, rfl⟩, ?_⟩
    rintro _ ⟨d, hd, h, rfl⟩ _ ⟨e, he, h', rfl⟩
    obtain ⟨f, hf, hdf, hef⟩ := hdir d hd e he
    have hdf' : (d : A) ≤ f := hdf
    have hef' : (e : A) ≤ f := hef
    refine ⟨_, ⟨f, hf, le_trans h hdf', rfl⟩, (hle_iff _ _).mpr ?_, (hle_iff _ _).mpr ?_⟩
    · exact rsmul_mono' hl0 (sub_le_sub_right hdf' _)
    · exact rsmul_mono' hl0 (sub_le_sub_right hef' _)
  obtain ⟨s, hs⟩ := hdc T hT
  have hsA : IsSelfAdjoint (((l⁻¹ : ℝ) : ℂ) • (s : A) + d0) :=
    (IsSelfAdjoint.of_nonneg (rsmul_nonneg' s.2.1 (inv_nonneg.mpr hl0))).add d0.2
  refine ⟨⟨_, hsA⟩, ?_, ?_⟩
  · -- upper bound
    intro d hd
    obtain ⟨f, hf, hdf, hd0f⟩ := hdir d hd d0 hd0
    have hdf' : (d : A) ≤ f := hdf
    have hd0f' : (d0 : A) ≤ f := hd0f
    have h1 : (l : ℂ) • ((f : A) - d0) ≤ s := (hle_iff _ _).mp (hs.1 _ ⟨f, hf, hd0f', rfl⟩)
    have h2 := rsmul_mono' (inv_nonneg.mpr hl0) h1
    rw [rsmul_inv_smul hlpos.ne'] at h2
    show (d : A) ≤ ((l⁻¹ : ℝ) : ℂ) • (s : A) + d0
    calc (d : A) ≤ f := hdf'
      _ = ((f : A) - d0) + d0 := by abel
      _ ≤ ((l⁻¹ : ℝ) : ℂ) • (s : A) + d0 := add_le_add h2 le_rfl
  · -- least
    intro c hc
    have hcd : (d0 : A) ≤ c := hc hd0
    set w : A := (l : ℂ) • ((c : A) - d0) with hw
    have hw0 : 0 ≤ w := rsmul_nonneg' (sub_nonneg.mpr hcd) hl0
    set m : ℝ := ‖w‖ + 1 with hm
    have hmpos : 0 < m := by rw [hm]; positivity
    set k : ℝ := m⁻¹ with hk
    have hk0 : 0 ≤ k := inv_nonneg.mpr hmpos.le
    have hk1 : k ≤ 1 := inv_le_one_of_one_le₀ (by rw [hm]; linarith [norm_nonneg w])
    -- every element of `T` is below `w`
    have hTw : ∀ x ∈ T, (x : A) ≤ w := by
      rintro _ ⟨d, hd, h, rfl⟩
      exact rsmul_mono' hl0 (sub_le_sub_right (show (d : A) ≤ (c : A) from hc hd) _)
    have memk : ∀ x : Set.Icc (0 : A) 1, (k : ℂ) • (x : A) ∈ Set.Icc (0 : A) 1 := fun x =>
      ⟨rsmul_nonneg' x.2.1 hk0, le_trans (rsmul_mono' hk0 x.2.2) (by
        have := rsmul_le_rsmul' hk1 (zero_le_one' A); rwa [Complex.ofReal_one, one_smul] at this)⟩
    let T' : Set (Set.Icc (0 : A) 1) := (fun x => ⟨_, memk x⟩) '' T
    have hT' : EDirected T' := by
      obtain ⟨⟨x0, hx0⟩, hdirT⟩ := hT
      refine ⟨⟨_, x0, hx0, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdirT x hx y hy
      exact ⟨_, ⟨z, hz, rfl⟩, (hle_iff _ _).mpr (rsmul_mono' hk0 ((hle_iff _ _).mp hxz)),
        (hle_iff _ _).mpr (rsmul_mono' hk0 ((hle_iff _ _).mp hyz))⟩
    obtain ⟨s', hs'⟩ := hdc T' hT'
    -- `s' ≤ k w`
    have hkw : (k : ℂ) • w ∈ Set.Icc (0 : A) 1 := ⟨rsmul_nonneg' hw0 hk0, scale_le_one hw0⟩
    have h1 : (s' : A) ≤ (k : ℂ) • w := (hle_iff _ _).mp (hs'.2 ⟨_, hkw⟩ (by
      rintro _ ⟨x, hx, rfl⟩; exact (hle_iff _ _).mpr (rsmul_mono' hk0 (hTw x hx))))
    -- `s' ≤ k · 1`, so `m s' ∈ [0,1]`
    have hk1' : (k : ℂ) • (1 : A) ∈ Set.Icc (0 : A) 1 := memk 1
    have h2 : (s' : A) ≤ (k : ℂ) • (1 : A) := (hle_iff _ _).mp (hs'.2 ⟨_, hk1'⟩ (by
      rintro _ ⟨x, _, rfl⟩; exact (hle_iff _ _).mpr (rsmul_mono' hk0 x.2.2)))
    have hms : (m : ℂ) • (s' : A) ∈ Set.Icc (0 : A) 1 := by
      refine ⟨rsmul_nonneg' s'.2.1 hmpos.le, ?_⟩
      have := rsmul_mono' hmpos.le h2
      rwa [hk, rsmul_smul_inv hmpos.ne'] at this
    -- `m s'` bounds `T`, so `s ≤ m s' ≤ w`
    have h3 : (s : A) ≤ (m : ℂ) • (s' : A) := (hle_iff _ _).mp (hs.2 ⟨_, hms⟩ (by
      intro x hx
      have hx' : (k : ℂ) • (x : A) ≤ s' := (hle_iff _ _).mp (hs'.1 _ ⟨x, hx, rfl⟩)
      have := rsmul_mono' hmpos.le hx'
      rw [hk, rsmul_smul_inv hmpos.ne'] at this
      exact (hle_iff _ _).mpr this))
    have h4 : (s : A) ≤ w := by
      have := rsmul_mono' hmpos.le h1
      rw [hk, rsmul_smul_inv hmpos.ne'] at this
      exact le_trans h3 this
    have h5 := rsmul_mono' (inv_nonneg.mpr hl0) h4
    rw [hw, rsmul_inv_smul hlpos.ne'] at h5
    show ((l⁻¹ : ℝ) : ℂ) • (s : A) + d0 ≤ c
    calc ((l⁻¹ : ℝ) : ℂ) • (s : A) + d0 ≤ ((c : A) - d0) + d0 := add_le_add h5 le_rfl
      _ = c := by abel

/-- **SEA 13** (second.tex:374, Example), first claim: `[0,1]_A` is a
directed-complete effect algebra iff `A` is *bounded-directed complete* —
every non-empty bounded directed set of self-adjoint elements has a least upper
bound (the first axiom of the theses' `VonNeumannAlgebra`, vn.tex 42I).  The
print's gloss "every bounded set of self-adjoint elements has a least upper
bound" drops *directed* (see the audit row).  The second claim (`C(X)` is
bounded-directed complete iff `X` is extremally disconnected, cited from
Gillman–Jerison) is not formalised. -/
theorem sea13_directedComplete_iff :
    @DirectedComplete _ (cstarEA A) ↔
      ∀ D : Set (selfAdjoint A), D.Nonempty → DirectedOn (· ≤ ·) D → BddAbove D →
        ∃ s, IsLUB D s :=
  ⟨fun h => sea13_bdc_of_dc h, sea13_dc_of_bdc⟩

/-- **SEA 16** (`ex:canonical-sea`, second.tex:475, Example), first claim:
for a (unital) C*-algebra `A`, `[0,1]_A` is a SEA with `a ∘ b = √a b √a`.
The axioms are the theses' `sqrtConj` lemmas (`Theses/B/Eff/VNExamples.lean`,
there for von Neumann algebras only); the unconditional half of S5 holds
because the theses' proof of `c | a ∘ b` never used `a ⊥ b`. -/
@[instance_reducible] noncomputable def cstarSEA (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    @SEAlgebra (Set.Icc (0 : A) 1) (cstarEA A) := by
  letI := cstarEA A
  exact
  { seq := fun a b => ⟨sqrtConj (a : A) (b : A), sqrtConj_nonneg b.2.1,
      sqrtConj_le_one a.2.1 a.2.2 b.2.2⟩
    seq_add := fun c {a b} h => by
      have hab : (a : A) + (b : A) ≤ 1 := h
      have hperp : (sqrtConj (c : A) (a : A)) + sqrtConj (c : A) (b : A) ≤ 1 := by
        rw [sqrtConj_add]; exact sqrtConj_le_one c.2.1 c.2.2 hab
      exact ⟨hperp, Subtype.ext (sqrtConj_add _ _ _)⟩
    one_seq := fun a => Subtype.ext (sqrtConj_one_left (a : A))
    seq_zero_comm := fun a b hab =>
      Subtype.ext (sqrtConj_eq_zero_comm a.2.1 b.2.1 (congrArg Subtype.val hab))
    seq_comm_orth := fun {a b} h => by
      have hcomm : Commute (a : A) (b : A) :=
        commute_of_sqrtConj_eq a.2.1 b.2.1 (congrArg Subtype.val h)
      have hb' : (0 : A) ≤ 1 - (b : A) := sub_nonneg.mpr b.2.2
      have hc2 : Commute (a : A) (1 - (b : A)) := (Commute.one_right (a : A)).sub_right hcomm
      exact Subtype.ext (sqrtConj_comm_of_commute a.2.1 hb' hc2)
    seq_comm_assoc := fun {a b} h c => by
      have hcomm : Commute (a : A) (b : A) :=
        commute_of_sqrtConj_eq a.2.1 b.2.1 (congrArg Subtype.val h)
      exact Subtype.ext (sqrtConj_assoc_of_commute a.2.1 b.2.1 hcomm (c : A))
    seq_comm_compat := fun {a b c} h hca hcb => by
      have h1 : Commute (c : A) (a : A) :=
        commute_of_sqrtConj_eq c.2.1 a.2.1 (congrArg Subtype.val hca)
      have h2 : Commute (c : A) (b : A) :=
        commute_of_sqrtConj_eq c.2.1 b.2.1 (congrArg Subtype.val hcb)
      have hsa : Commute (c : A) (CFC.sqrt (a : A)) := (commute_sqrt h1.symm).symm
      have h3 : Commute (c : A) (sqrtConj (a : A) (b : A)) := (hsa.mul_right h2).mul_right hsa
      have h4 : Commute (c : A) ((a : A) + (b : A)) := h1.add_right h2
      exact ⟨Subtype.ext (sqrtConj_comm_of_commute c.2.1 (sqrtConj_nonneg b.2.1) h3),
        Subtype.ext (sqrtConj_comm_of_commute c.2.1 (add_nonneg a.2.1 b.2.1) h4)⟩
    seq_comm_seq := fun {a b c} hca hcb => by
      have h1 : Commute (c : A) (a : A) :=
        commute_of_sqrtConj_eq c.2.1 a.2.1 (congrArg Subtype.val hca)
      have h2 : Commute (c : A) (b : A) :=
        commute_of_sqrtConj_eq c.2.1 b.2.1 (congrArg Subtype.val hcb)
      have hsa : Commute (c : A) (CFC.sqrt (a : A)) := (commute_sqrt h1.symm).symm
      have h3 : Commute (c : A) (sqrtConj (a : A) (b : A)) := (hsa.mul_right h2).mul_right hsa
      exact Subtype.ext (sqrtConj_comm_of_commute c.2.1 (sqrtConj_nonneg b.2.1) h3) }

/-- **SEA 16** (`ex:canonical-sea`, second.tex:475, Example): the sequential
product of `cstarSEA` is `a ∘ b = √a b √a`. -/
theorem sea16_cstar_sea (a b : Set.Icc (0 : A) 1) :
    ((@SequentialEffectAlgebra.seq _ (cstarEA A) (cstarSEA A).toSequentialEffectAlgebra a b :
      Set.Icc (0 : A) 1) : A) = CFC.sqrt (a : A) * (b : A) * CFC.sqrt (a : A) := rfl

/-- An element of `[0,1]_A` commuting with every element of a bounded directed
set of self-adjoint elements of a von Neumann algebra commutes with its
supremum.  (`u = a + i√(1-a²)` is a unitary commuting with `D`, so
`u* (⋁D) u = ⋁ u* d u = ⋁D` by 44VIII; hence `⋁D` commutes with `u`, `u*`,
and `a = ℜu`.) -/
theorem commute_dirSup [Theses.VonNeumannAlgebra A] {a : A} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (D : Set (selfAdjoint A)) (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D)
    (hc : ∀ d ∈ D, Commute a (d : A)) : Commute a ((Theses.dirSup D h : selfAdjoint A) : A) := by
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha0
  have ha2 : a ^ 2 ≤ 1 := by
    have e : sqrtConj a a = a * a := sqrtConj_eq_mul_of_commute ha0 (Commute.refl a)
    rw [sq, ← e]; exact sqrtConj_le_one ha0 ha1 ha1
  have hsq : 0 ≤ 1 - a ^ 2 := sub_nonneg.mpr ha2
  set b : A := CFC.sqrt (1 - a ^ 2) with hbdef
  have hbnn : 0 ≤ b := CFC.sqrt_nonneg _
  have hbsa : IsSelfAdjoint b := .of_nonneg hbnn
  have hbb : b * b = 1 - a ^ 2 := CFC.sqrt_mul_sqrt_self _ hsq
  have hcommb : ∀ x : A, Commute a x → Commute b x := by
    intro x hx
    rw [hbdef, CFC.sqrt_eq_cfc]
    exact Commute.cfc_nnreal ((Commute.one_left x).sub_left (hx.pow_left 2)) NNReal.sqrt
  have hcomm : Commute b a := hcommb a (Commute.refl a)
  set u : A := a + Complex.I • b with hu
  have hRe : (ℜ u : A) = a := by
    rw [hu, map_add, realPart_I_smul, hbsa.imaginaryPart]
    simp [hsa.coe_realPart]
  have hIm : (ℑ u : A) = b := by
    rw [hu, map_add, imaginaryPart_I_smul, hsa.imaginaryPart]
    simp [hbsa.coe_realPart]
  have hn : IsStarNormal u :=
    isStarNormal_iff_commute_realPart_imaginaryPart.mpr (by rw [hRe, hIm]; exact hcomm.symm)
  have huu : u ∈ unitary A := by
    rw [(Theses.A.CStar.unitary_basic_4 u).2 hn, hRe, hIm, sq b, hbb]
    abel
  have hsu : star u * u = 1 := Unitary.star_mul_self_of_mem huu
  have hus : u * star u = 1 := Unitary.mul_star_self_of_mem huu
  -- `u` commutes with every `d ∈ D`
  have hud : ∀ d ∈ D, Commute u (d : A) := fun d hd =>
    (hc d hd).add_left ((hcommb _ (hc d hd)).smul_left Complex.I)
  -- `u* d u = d`, so the conjugated set is `D` itself
  have himg : ((fun d : selfAdjoint A => star u * (d : A) * u) '' D) = ((↑) '' D : Set A) := by
    ext x; constructor
    · rintro ⟨d, hd, rfl⟩
      refine ⟨d, hd, ?_⟩
      show (d : A) = star u * d * u
      rw [mul_assoc, ← (hud d hd).eq, ← mul_assoc, hsu, one_mul]
    · rintro ⟨d, hd, rfl⟩
      refine ⟨d, hd, ?_⟩
      show star u * (d : A) * u = d
      rw [mul_assoc, ← (hud d hd).eq, ← mul_assoc, hsu, one_mul]
  have hL1 := Theses.A.VN.ad_normal u D h
  rw [himg] at hL1
  have hL2 := isLUB_coe_of_isLUB h.1 (Theses.isLUB_dirSup D h)
  set t : A := ((Theses.dirSup D h : selfAdjoint A) : A) with ht
  have hconj : star u * t * u = t := hL1.unique hL2
  have htu : Commute t u := by
    show t * u = u * t
    calc t * u = (u * star u) * t * u := by rw [hus, one_mul]
      _ = u * (star u * t * u) := by noncomm_ring
      _ = u * t := by rw [hconj]
  have htsa : IsSelfAdjoint t := (Theses.dirSup D h).2
  have htus : Commute t (star u) := by
    have := htu.star_star
    rwa [htsa.star_eq] at this
  have : Commute t (ℜ u : A) := by
    rw [realPart_apply_coe]
    exact ((htu.add_right htus).smul_right _)
  rw [hRe] at this
  exact this.symm

/-- **SEA 16** (`ex:canonical-sea`, second.tex:475, Example), second claim,
for von Neumann algebras: `[0,1]_A` is a *normal* SEA with the same
sequential product.  (The print states it for bounded-directed complete
C*-algebras; we cover the von Neumann algebra case the print names, via the
theses' 44VIII `ad_normal` — see the audit row.) -/
@[instance_reducible] noncomputable def vnNormalSEA (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Theses.VonNeumannAlgebra A] : @NormalSEA (Set.Icc (0 : A) 1) (cstarEA A) := by
  letI := cstarEA A
  letI := cstarSEA A
  have hle_iff : ∀ x y : Set.Icc (0 : A) 1, x ≼ y ↔ (x : A) ≤ y :=
    interval_le_iff 1 zero_le_one
  -- the supremum of a directed `S ⊆ [0,1]_A` is `⋁ (saImage S)`
  have supEq : ∀ {S : Set (Set.Icc (0 : A) 1)} (hS : EDirected S) {x : Set.Icc (0 : A) 1},
      EIsSup S x → (x : A) = ((Theses.dirSup _ (saImage_directed hS) : selfAdjoint A) : A) := by
    intro S hS x hx
    obtain ⟨hmem, hsup⟩ := isSup_of_isLUB hS.1 (Theses.isLUB_dirSup _ (saImage_directed hS))
    exact congrArg Subtype.val (hx.unique hsup)
  exact
  { cstarSEA A with
    directedComplete := sea13_dc_of_bdc (fun D hne hdir hbdd =>
      Theses.VonNeumannAlgebra.isLUB_of_bddAbove_directed D hne hdir hbdd)
    seq_sup := by
      intro a S x hS hx
      have h := saImage_directed hS
      have hL := Theses.A.VN.ad_normal (CFC.sqrt (a : A)) (saImage S) h
      rw [← supEq hS hx] at hL
      have hst : star (CFC.sqrt (a : A)) = CFC.sqrt (a : A) :=
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
      rw [hst] at hL
      refine ⟨?_, fun y hy => (hle_iff _ _).mpr (hL.2 ?_)⟩
      · rintro _ ⟨s, hs, rfl⟩
        refine (hle_iff _ _).mpr (hL.1 ⟨⟨s.1, IsSelfAdjoint.of_nonneg s.2.1⟩, ⟨s, hs, rfl⟩, ?_⟩)
        rfl
      · rintro _ ⟨d, ⟨s, hs, rfl⟩, rfl⟩
        have := (hle_iff _ _).mp (hy _ ⟨s, hs, rfl⟩)
        exact this
    comm_sup := by
      intro a S x hS hx hcomm
      have h := saImage_directed hS
      have hc : ∀ d ∈ saImage S, Commute (a : A) (d : A) := by
        rintro _ ⟨s, hs, rfl⟩
        exact commute_of_sqrtConj_eq a.2.1 s.2.1 (congrArg Subtype.val (hcomm s hs))
      have := commute_dirSup a.2.1 a.2.2 (saImage S) h hc
      rw [← supEq hS hx] at this
      exact Subtype.ext (sqrtConj_comm_of_commute a.2.1 x.2.1 this) }

end CStar

end Papers.SEA
