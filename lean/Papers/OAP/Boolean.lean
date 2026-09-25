/-
Papers/OAP/Boolean.lean

A. Westerbaan, B. Westerbaan, J. van de Wetering, *A characterisation of
ordered abstract probabilities* (LICS 2020, arXiv:1912.10040), source
`../papers/1912.10040/first.tex`: §6 *Boolean algebras, halves and
convexity* — points **OAP 44**–**OAP 50**.

Conventions (see `Papers/README.md`, `Papers/OAP/PLAN.md`):

* The set of idempotents `P(M)` is Basic's `idempotents M`; its Boolean
  algebra structure (OAP 45) is the def `idemBooleanAlgebra M`, registered
  as a *scoped* instance.  Its order is the subtype order of the effect
  algebra order of `M`, its meet is the product and its complement is `orth`.
* A convex effect algebra (OAP 49) is one carrying a `ConvexAction`: an
  action `I × E → E` of the real unit interval `I = [0,1]` with the print's
  four axioms.  `ConvexAction` is equivalent to the tree's `EffectModule I E`
  (thesis B 179II over the effect monoid `[0,1]`, 178III.1):
  `ConvexAction.toEffectModule`, `ConvexAction.ofEffectModule`.
* OAP 50: for a half `a` (`a ⋁ a = 1`) the dyadic element `m/2ⁿ ↦ m·aⁿ` is
  `dyEl a n m`; the element `λ̄` of a real `λ ∈ [0,1]` is `dyCl a λ`, the
  supremum of the dyadic elements strictly below `λ` (and `0`).
-/
import Papers.OAP.FloorCeiling

set_option warn.classDefReducibility false

namespace Papers.OAP

open Theses.B.Eff
open scoped Papers.OAP unitInterval

universe u v

/-! ## OAP 44: Boolean elements -/

section BooleanDef

variable {M : Type u} [EffectMonoid M]

/-- **OAP 44** (first.tex:1583, Definition): an element `a` of an effect
monoid is **Boolean** when every `b ≤ a` is idempotent. -/
def IsBooleanElem (a : M) : Prop := ∀ b : M, b ≤ a → b * b = b

variable (M) in
/-- **OAP 44** (first.tex:1583, Definition): an effect monoid is **Boolean**
when `1` is Boolean, i.e. every element is idempotent. -/
def IsBooleanEM : Prop := IsBooleanElem (1 : M)

theorem isBooleanEM_iff : IsBooleanEM M ↔ ∀ a : M, a * a = a :=
  ⟨fun h a => h a (le_one' a), fun h a _ => h a⟩

end BooleanDef

/-! ## OAP 45: the idempotents form a Boolean algebra -/

section Idempotents

variable {M : Type u} [EffectMonoid M]

/-- The product of two idempotents is idempotent (via OAP 20). -/
theorem idem_mul {p q : M} (hp : p * p = p) (hq : q * q = q) : p * q * (p * q) = p * q := by
  calc p * q * (p * q) = p * (q * p) * q := by simp only [emul_assoc]
    _ = p * (p * q) * q := by rw [oap20 hq p]
    _ = p * q := by rw [← emul_assoc p p q, hp, emul_assoc, hq]

/-- OAP 45, first step of the proof: for idempotents `p·q = p ∧ q`, the
infimum taken in `M`. -/
theorem isGLB_idem {p q : M} (hp : p * p = p) (hq : q * q = q) : IsGLB {p, q} (p * q) := by
  refine ⟨?_, fun r hr => ?_⟩
  · rintro _ (rfl | rfl)
    · exact emul_le_left _ _
    · exact emul_le_right _ _
  · have h1 : r * p = r := emul_eq_of_le' hp (hr (Set.mem_insert _ _))
    have h2 : r * q = r := emul_eq_of_le' hq (hr (by simp))
    calc r = r * (p * q) := by rw [← emul_assoc, h1, h2]
      _ ≤ p * q := emul_le_right _ _

/-- OAP 45: for idempotents `p ∨ q = (p^⊥ ∧ q^⊥)^⊥ = (p^⊥·q^⊥)^⊥`, the
supremum taken in `M` ("the complement is an order anti-isomorphism"). -/
theorem isLUB_idem {p q : M} (hp : p * p = p) (hq : q * q = q) :
    IsLUB {p, q} (orth (orth p * orth q)) := by
  apply isLUB_orth_of_isGLB
  rw [Set.image_pair]
  exact isGLB_idem (idem_orth hp) (idem_orth hq)

/-- OAP 45: `(p^⊥·q^⊥)^⊥ = p ⋁ p^⊥·q` (in any effect monoid; for idempotents
the left-hand side is `p ∨ q`: "by uniqueness of complements"). -/
theorem orth_orth_mul_orth (p q : M) :
    Perp p (orth p * q) ∧ orth (orth p * orth q) = p ⋎ orth p * q := by
  have h1 := mul_oplus (orth p) (perp_orth q)
  rw [oplus_orth, emul_one] at h1
  have hpp : Perp p (orth p * q ⋎ orth p * orth q) := by rw [← h1.2]; exact perp_orth p
  obtain ⟨ha, hb⟩ := perp_assoc_left h1.1 hpp
  refine ⟨ha, ?_⟩
  have e : (p ⋎ orth p * q) ⋎ orth p * orth q = 1 := by
    rw [oplus_assoc' h1.1 hpp, ← h1.2, oplus_orth]
  rw [eq_orth_of_oplus hb e, orth_orth]

/-- For idempotents: `p ⊥ q ⟺ p·q = 0`. -/
theorem perp_idem_iff {p q : M} (hq : q * q = q) : Perp p q ↔ p * q = 0 := by
  have hsplit := mul_oplus p (perp_orth q)
  rw [oplus_orth, emul_one] at hsplit
  constructor
  · intro h
    have h' : p * orth q = p := emul_eq_of_le' (idem_orth hq) (perp_iff_le_orth.1 h)
    rw [h'] at hsplit
    have e : p * q ⋎ p = 0 ⋎ p := by rw [zero_oplus]; exact hsplit.2.symm
    exact oplus_right_cancel (h' ▸ hsplit.1) (zero_perp p) e
  · intro h
    rw [h, zero_oplus] at hsplit
    rw [perp_iff_le_orth, hsplit.2]
    exact emul_le_right _ _

/-- For orthogonal idempotents `p ⋁ q = p ∨ q = (p^⊥·q^⊥)^⊥`. -/
theorem oplus_idem_eq {p q : M} (hp : p * p = p) (hq : q * q = q) (h : Perp p q) :
    p ⋎ q = orth (orth p * orth q) := by
  have hpq : p * q = 0 := (perp_idem_iff hq).1 h
  have hq' : orth p * q = q := by
    have hs := mul_oplus q (perp_orth p)
    rw [oplus_orth, emul_one, ← oap20 hp q, hpq, zero_oplus] at hs
    rw [oap20 (idem_orth hp) q]; exact hs.2.symm
  rw [(orth_orth_mul_orth p q).2, hq']

/-- `p ∧ q^⊥ ⋁ p ∧ q = p` in the form `p·(p·q)^⊥ = p·q^⊥`. -/
theorem mul_orth_mul_idem {p q : M} (hp : p * p = p) : p * orth (p * q) = p * orth q := by
  have h1 := mul_oplus p (perp_orth (p * q))
  have h2 := mul_oplus p (perp_orth q)
  rw [oplus_orth, emul_one, ← emul_assoc, hp] at h1
  rw [oplus_orth, emul_one] at h2
  have e : p * q ⋎ p * orth (p * q) = p * q ⋎ p * orth q := by rw [← h1.2, ← h2.2]
  exact oplus_left_cancel h1.1 h2.1 e

variable (M) in
/-- The lattice structure on `P(M)`: the order is that of `M`, the meet is
the product, and the join is `(p^⊥·q^⊥)^⊥` (OAP 45). -/
noncomputable def idemLattice : Lattice (idempotents M) :=
  { (Subtype.partialOrder _ : PartialOrder (idempotents M)) with
    inf := fun p q => ⟨p.1 * q.1, idem_mul p.2 q.2⟩
    sup := fun p q => ⟨orth (orth p.1 * orth q.1),
      idem_orth (idem_mul (idem_orth p.2) (idem_orth q.2))⟩
    inf_le_left := fun p q => (isGLB_idem p.2 q.2).1 (Set.mem_insert _ _)
    inf_le_right := fun p q => (isGLB_idem p.2 q.2).1 (by simp)
    le_inf := fun p q r h1 h2 => (isGLB_idem q.2 r.2).2 (by
      rintro _ (rfl | rfl)
      · exact h1
      · exact h2)
    le_sup_left := fun p q => (isLUB_idem p.2 q.2).1 (Set.mem_insert _ _)
    le_sup_right := fun p q => (isLUB_idem p.2 q.2).1 (by simp)
    sup_le := fun p q r h1 h2 => (isLUB_idem p.2 q.2).2 (by
      rintro _ (rfl | rfl)
      · exact h1
      · exact h2) }

/-- OAP 45, distributivity `p ∧ (q ∨ r) = (p ∧ q) ∨ (p ∧ r)`, as an equation
in `M`: both sides equal `p·q ⋁ p·q^⊥·r` (the print's "straightforward
exercise"). -/
theorem idem_distrib {p q r : M} (hp : p * p = p) :
    p * orth (orth q * orth r) = orth (orth (p * q) * orth (p * r)) := by
  obtain ⟨h1, e1⟩ := orth_orth_mul_orth q r
  obtain ⟨h2, e2⟩ := orth_orth_mul_orth (p * q) (p * r)
  rw [e1, e2, (mul_oplus p h1).2]
  congr 1
  calc p * (orth q * r) = p * orth q * r := (emul_assoc _ _ _).symm
    _ = p * orth (p * q) * r := by rw [mul_orth_mul_idem hp]
    _ = orth (p * q) * p * r := by rw [oap20 hp]
    _ = orth (p * q) * (p * r) := emul_assoc _ _ _

variable (M) in
/-- **OAP 45** (`prop:booleanalgebra`, first.tex:1590, Proposition): the set
of idempotents `P(M)` of an effect monoid is a Boolean algebra (order of `M`,
meet `p·q`, join `(p^⊥·q^⊥)^⊥`, complement `p^⊥`, bounds `0`, `1`). -/
noncomputable def idemBooleanAlgebra : BooleanAlgebra (idempotents M) :=
  letI := idemLattice M
  letI : DistribLattice (idempotents M) :=
    DistribLattice.ofInfSupLe fun p q r => le_of_eq (Subtype.ext (idem_distrib p.2))
  { (inferInstance : DistribLattice (idempotents M)) with
    top := ⟨1, emul_one 1⟩
    bot := ⟨0, emul_zero 0⟩
    le_top := fun p => le_one' p.1
    bot_le := fun p => zero_le' p.1
    compl := fun p => ⟨orth p.1, idem_orth p.2⟩
    inf_compl_le_bot := fun p => le_of_eq (Subtype.ext ((oap18 p.1).1 p.2))
    top_le_sup_compl := fun p => by
      show (1 : M) ≤ orth (orth p.1 * orth (orth p.1))
      rw [(oap18 (orth p.1)).1 (idem_orth p.2), ← oap1_one_eq_orth_zero] }

attribute [scoped instance] idemBooleanAlgebra

/-- **OAP 45**: the order of `P(M)` is that of `M`. -/
theorem idem_le_iff {p q : idempotents M} : p ≤ q ↔ p.1 ≤ q.1 := Iff.rfl

/-- **OAP 45**: in `P(M)`, `p ∧ q = p·q`, and this is the infimum in `M`. -/
theorem oap45_inf (p q : idempotents M) : (p ⊓ q).1 = p.1 * q.1 ∧ IsGLB {p.1, q.1} (p.1 * q.1) :=
  ⟨rfl, isGLB_idem p.2 q.2⟩

/-- **OAP 45**: in `P(M)`, `p ∨ q = (p^⊥ ∧ q^⊥)^⊥`, the supremum in `M`, and
`p ∨ q = p ⋁ (p^⊥·q)`. -/
theorem oap45_sup (p q : idempotents M) :
    (p ⊔ q).1 = orth (orth p.1 * orth q.1) ∧ IsLUB {p.1, q.1} (p ⊔ q).1 ∧
      Perp p.1 (orth p.1 * q.1) ∧ (p ⊔ q).1 = p.1 ⋎ orth p.1 * q.1 :=
  ⟨rfl, isLUB_idem p.2 q.2, orth_orth_mul_orth p.1 q.1⟩

/-- **OAP 45**: the complement of `P(M)` is the orthocomplement of `M`. -/
theorem oap45_compl (p : idempotents M) : (pᶜ).1 = orth p.1 := rfl

end Idempotents

/-! ### A Boolean effect monoid is a Boolean algebra (OAP 45, second sentence) -/

section BooleanIso

variable {M : Type u} [EffectMonoid M]

/-- The effect monoid morphism `P(M) → M` (inclusion), where `P(M)` carries
the effect monoid of its Boolean algebra (`booleanEffectMonoid`, OAP 6):
`p ⊥ q` iff `p ∧ q = 0`, `p ⋁ q = p ∨ q`, `p·q = p ∧ q`. -/
noncomputable def idemIncl (M : Type u) [EffectMonoid M] :
    @EffectMonoidHom (idempotents M) M (booleanEffectMonoid _) _ :=
  letI := booleanEffectMonoid (idempotents M)
  { toFun := Subtype.val
    perp_map := fun {p q} h => (perp_idem_iff q.2).2 (congrArg Subtype.val h)
    ovee_map := fun {p q} h => by
      have h' : Perp p.1 q.1 := (perp_idem_iff q.2).2 (congrArg Subtype.val h)
      rw [← oplus_eq h', oplus_idem_eq p.2 q.2 h']
      rfl
    map_one := rfl
    map_mul := fun _ _ => rfl }

/-- In a Boolean effect monoid, the identification `M → P(M)`. -/
noncomputable def booleanIso (hM : IsBooleanEM M) :
    @EffectMonoidHom M (idempotents M) _ (booleanEffectMonoid _) :=
  letI := booleanEffectMonoid (idempotents M)
  { toFun := fun x => ⟨x, hM x (le_one' x)⟩
    perp_map := fun {a b} h => Subtype.ext ((perp_idem_iff (hM b (le_one' b))).1 h)
    ovee_map := fun {a b} h => Subtype.ext (by
      show ovee a b h = orth (orth a * orth b)
      rw [← oplus_eq h, oplus_idem_eq (hM a (le_one' a)) (hM b (le_one' b)) h])
    map_one := rfl
    map_mul := fun _ _ => rfl }

/-- **OAP 45** (`prop:booleanalgebra`, first.tex:1590, Proposition), second
sentence, forward direction: a Boolean effect monoid `M` is isomorphic (as an
effect monoid) to the Boolean algebra `P(M)` with its effect monoid structure
`booleanEffectMonoid` (OAP 6); so `M` *is* a Boolean algebra. -/
theorem oap45_isIso (hM : IsBooleanEM M) :
    @EMIsIso M (idempotents M) _ (booleanEffectMonoid _) (booleanIso hM) :=
  ⟨idemIncl M, fun _ => rfl, fun _ => rfl⟩

/-- **OAP 45** (`prop:booleanalgebra`, first.tex:1590, Proposition): "an
effect monoid is Boolean iff it is a Boolean algebra" — iff it is isomorphic
to (the effect monoid of, OAP 6) a Boolean algebra. -/
theorem oap45_iff :
    IsBooleanEM M ↔ ∃ (B : Type u) (_ : BooleanAlgebra B)
      (f : @EffectMonoidHom M B _ (booleanEffectMonoid B)),
      @EMIsIso M B _ (booleanEffectMonoid B) f := by
  constructor
  · intro hM
    exact ⟨idempotents M, idemBooleanAlgebra M, booleanIso hM, oap45_isIso hM⟩
  · rintro ⟨B, _, f, g, hgf, -⟩
    rw [isBooleanEM_iff]
    intro x
    let _ := booleanEffectMonoid B
    rw [← hgf x, ← g.map_mul]
    congr 1
    show f.toFun x ⊓ f.toFun x = f.toFun x
    exact inf_idem _

end BooleanIso

/-! ## OAP 46, OAP 47: ω-completeness -/

section OmegaIdem

variable {M : Type u} [EffectMonoid M] [OmegaComplete M]

/-- The supremum in `M` of an increasing sequence of idempotents is
idempotent (via the floor, OAP 35).  Used in OAP 46, where the print leaves
it implicit. -/
theorem idem_of_isLUB {f : ℕ → M} (hf : ∀ n, f n * f n = f n) {s : M}
    (hs : IsLUB (Set.range f) s) : s * s = s := by
  have h : s ≤ floor s := hs.2 (by rintro _ ⟨n, rfl⟩; exact le_floor (hf n) (hs.1 ⟨n, rfl⟩))
  have e : floor s = s := le_antisymm (floor_le s) h
  rw [← e]; exact floor_idem s

/-- **OAP 46** (`prop:completelattice`, first.tex:1620, Proposition): if `M`
is ω-complete, then the Boolean algebra `P(M)` is ω-complete: every countable
`A ⊆ P(M)` has a supremum in `P(M)`, which is also its supremum in `M`. -/
theorem oap46 (A : Set (idempotents M)) (hA : A.Countable) :
    ∃ s : idempotents M, IsLUB A s ∧ IsLUB (Subtype.val '' A) s.1 := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · refine ⟨⊥, ⟨by simp, fun b _ => zero_le' b.1⟩, ?_⟩
    simp only [Set.image_empty, isLUB_empty_iff]
    exact fun b => zero_le' b
  obtain ⟨p, rfl⟩ := hA.exists_eq_range hne
  -- `q₀ = p₀`, `qₙ₊₁ = qₙ ∨ pₙ₊₁`
  let q : ℕ → idempotents M := fun n => Nat.rec (p 0) (fun n qn => qn ⊔ p (n + 1)) n
  have hq : Monotone q := monotone_nat_of_le_succ fun n => (le_sup_left : q n ≤ q n ⊔ p (n + 1))
  obtain ⟨s, hs⟩ := OmegaComplete.exists_isLUB (fun n => (q n).1) fun m n h => hq h
  have hsi : s * s = s := idem_of_isLUB (fun n => (q n).2) hs
  have hpq : ∀ n, (p n).1 ≤ (q n).1 := by
    intro n; cases n with
    | zero => exact le_rfl
    | succ n => exact (le_sup_right : p (n + 1) ≤ q n ⊔ p (n + 1))
  have hub : ∀ u : M, (∀ n, (p n).1 ≤ u) → ∀ n, (q n).1 ≤ u := by
    intro u hu n
    induction n with
    | zero => exact hu 0
    | succ n ih =>
      exact (isLUB_idem (q n).2 (p (n + 1)).2).2 (by
        rintro _ (rfl | rfl)
        · exact ih
        · exact hu (n + 1))
  have hM : IsLUB (Subtype.val '' Set.range p) s := by
    refine ⟨?_, fun u hu => hs.2 ?_⟩
    · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact le_trans (hpq n) (hs.1 ⟨n, rfl⟩)
    · rintro _ ⟨n, rfl⟩
      exact hub u (fun n => hu ⟨_, ⟨n, rfl⟩, rfl⟩) n
  refine ⟨⟨s, hsi⟩, ⟨?_, fun u hu => ?_⟩, hM⟩
  · rintro _ ⟨n, rfl⟩; exact hM.1 ⟨_, ⟨n, rfl⟩, rfl⟩
  · exact hM.2 (by rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact hu ⟨n, rfl⟩)

/-- **OAP 46**, in the form of OAP 15: `P(M)` with its Boolean algebra effect
monoid is an ω-complete effect algebra. -/
theorem oap46_omegaComplete :
    @OmegaComplete (idempotents M) (booleanEffectAlgebra _) :=
  oap15_omega _ fun f _ => (oap46 (Set.range f) (Set.countable_range f)).imp fun _ h => h.1

/-- **OAP 47** (`prop:sharpeffectmonoidisbooleanalgebra`, first.tex:1645,
Proposition): an ω-complete Boolean effect monoid `M` is an ω-complete
Boolean algebra: `M ≅ P(M)` as effect monoids (OAP 45), and every countable
subset of `P(M)` has a supremum (OAP 46). -/
theorem oap47 (hM : IsBooleanEM M) :
    @EMIsIso M (idempotents M) _ (booleanEffectMonoid _) (booleanIso hM) ∧
      (∀ A : Set (idempotents M), A.Countable → ∃ s, IsLUB A s) ∧
      @OmegaComplete (idempotents M) (booleanEffectAlgebra _) :=
  ⟨oap45_isIso hM, fun A hA => (oap46 A hA).imp fun _ h => h.1, oap46_omegaComplete⟩

end OmegaIdem

/-! ## OAP 48, OAP 49: halvable and convex effect algebras -/

section Convex

variable {E : Type u} [EffectAlgebra E]

/-- **OAP 48** (first.tex:1656, Definition): an element `a` of an effect
algebra is **halvable** when `a = b ⋁ b` for some `b`. -/
def IsHalvable (a : E) : Prop := ∃ b : E, Perp b b ∧ b ⋎ b = a

variable (E) in
/-- **OAP 48** (first.tex:1656, Definition): an effect algebra is
**halvable** when `1` is halvable. -/
def HalvableEA : Prop := IsHalvable (1 : E)

variable (E) in
/-- **OAP 49** (`def:convexeffectalgebra`, first.tex:1664, Definition): a
**convex action** of the real unit interval `[0,1]` on `E`:
`λ·(μ·a) = (λμ)·a`; if `λ + μ ≤ 1` then `λ·a ⊥ μ·a` and
`λ·a ⋁ μ·a = (λ+μ)·a`; if `a ⊥ b` then `λ·a ⊥ λ·b` and
`λ·(a ⋁ b) = λ·a ⋁ λ·b`; `1·a = a`.  (The second axiom is stated for every
`ν ∈ [0,1]` with `ν = λ + μ`, which is the print's "if `λ + μ ≤ 1`".) -/
structure ConvexAction where
  /-- The action `λ·a`. -/
  act : I → E → E
  act_act : ∀ (l m : I) (a : E), act l (act m a) = act (l * m) a
  add_act : ∀ (l m ν : I) (a : E), (l : ℝ) + m = ν →
    Perp (act l a) (act m a) ∧ act l a ⋎ act m a = act ν a
  act_oplus : ∀ (l : I) {a b : E}, Perp a b →
    Perp (act l a) (act l b) ∧ act l (a ⋎ b) = act l a ⋎ act l b
  one_act : ∀ a : E, act 1 a = a

variable (E) in
/-- **OAP 49** (`def:convexeffectalgebra`, first.tex:1664, Definition): `E`
is **convex** if there exists a convex action on it. -/
def IsConvex : Prop := Nonempty (ConvexAction E)

/-- **OAP 49**: a convex action is an effect module over the effect monoid
`[0,1]` in the tree's sense (thesis B 179II, `EffectModule I E`). -/
def ConvexAction.toEffectModule (c : ConvexAction E) : EffectModule I E where
  smul := c.act
  mul_smul l m a := (c.act_act l m a).symm
  smul_perp l {a b} h := by
    obtain ⟨h', e⟩ := c.act_oplus l h
    refine ⟨h', ?_⟩
    show ovee (c.act l a) (c.act l b) h' = c.act l (ovee a b h)
    rw [← oplus_eq h', ← oplus_eq h, e]
  perp_smul {l m} h a := by
    obtain ⟨h', e⟩ := c.add_act l m (ovee l m h) a rfl
    refine ⟨h', ?_⟩
    show ovee (c.act l a) (c.act m a) h' = c.act (ovee l m h) a
    rw [← oplus_eq h', e]
  one_smul := c.one_act

/-- **OAP 49**: conversely, an effect module over `[0,1]` (tree, 179II) is a
convex action.  So "convex" is the tree's "`[0,1]`-effect module". -/
def ConvexAction.ofEffectModule [EffectModule I E] : ConvexAction E where
  act l a := l • a
  act_act l m a := (EffectModule.mul_smul l m a).symm
  add_act l m ν a h := by
    have hlm : Perp l m := by
      show (l : ℝ) + m ≤ 1
      rw [h]; exact ν.2.2
    obtain ⟨h', e⟩ := EffectModule.perp_smul (M := I) hlm a
    refine ⟨h', ?_⟩
    rw [oplus_eq h', e]
    congr 1
    exact Subtype.ext h
  act_oplus l {a b} h := by
    obtain ⟨h', e⟩ := EffectModule.smul_perp l h
    exact ⟨h', by rw [oplus_eq h, oplus_eq h', e]⟩
  one_act := EffectModule.one_smul

/-- **OAP 49**: `E` is convex iff it is a `[0,1]`-effect module (tree). -/
theorem oap49_iff : IsConvex E ↔ Nonempty (EffectModule I E) :=
  ⟨fun ⟨c⟩ => ⟨c.toEffectModule⟩, fun ⟨m⟩ => ⟨@ConvexAction.ofEffectModule E _ m⟩⟩

end Convex

/-! ## OAP 50: a halvable ω-complete effect monoid is convex -/

section NSumTools

variable {E : Type u} [EffectAlgebra E]

/-- The `m`-fold sum `m·x = x ⋁ ⋯ ⋁ x`, made total (the partial sums of the
constant sequence). -/
noncomputable def nsum (x : E) (m : ℕ) : E := psum (fun _ => x) m

theorem IsNSum.eq_nsum {x : E} {m : ℕ} {s : E} (h : IsNSum x m s) : nsum x m = s := by
  induction m generalizing s with
  | zero => cases h; rfl
  | succ m ih =>
    obtain ⟨t, ht, -, rfl⟩ := isNSum_succ_iff.1 h
    show nsum x m ⋎ x = t ⋎ x
    rw [ih ht]

/-- If `(m+k)x` exists then `mx ⊥ kx` and `mx ⋁ kx = (m+k)x`. -/
theorem IsNSum.split {x : E} {m k : ℕ} {u s t : E} (hu : IsNSum x (m + k) u)
    (hs : IsNSum x m s) (ht : IsNSum x k t) : Perp s t ∧ s ⋎ t = u := by
  induction k generalizing u t with
  | zero =>
    cases ht
    exact ⟨perp_zero s, by rw [oplus_zero]; exact hs.unique hu⟩
  | succ k ih =>
    obtain ⟨t', ht', htx, rfl⟩ := isNSum_succ_iff.1 ht
    rw [← Nat.add_assoc] at hu
    obtain ⟨u', hu', hux, rfl⟩ := isNSum_succ_iff.1 hu
    obtain ⟨h1, e1⟩ := ih hu' ht'
    subst e1
    exact ⟨perp_oplus_of_oplus_perp h1 hux, (oplus_assoc h1 hux).symm⟩

/-- `k·x = y` and `m·y = s` give `(km)·x = s`. -/
theorem IsNSum.comp {x y : E} {k m : ℕ} {s : E} (hy : IsNSum x k y) (hs : IsNSum y m s) :
    IsNSum x (k * m) s := by
  induction m generalizing s with
  | zero => cases hs; exact IsNSum.zero
  | succ m ih =>
    obtain ⟨t, ht, hty, rfl⟩ := isNSum_succ_iff.1 hs
    rw [Nat.mul_succ]
    exact (ih ht).add hy hty

end NSumTools

theorem IsNSum.emul_left {M : Type u} [EffectMonoid M] {x y : M} {k : ℕ} {s : M}
    (hs : IsNSum x k s) : IsNSum (y * x) k (y * s) := by
  induction k generalizing s with
  | zero => cases hs; rw [emul_zero]; exact IsNSum.zero
  | succ k ih =>
    obtain ⟨t, ht, hp, rfl⟩ := isNSum_succ_iff.1 hs
    obtain ⟨hp', e⟩ := mul_oplus y hp
    rw [e]; exact (ih ht).succ hp'

section Suprema

variable {E : Type u} [EffectAlgebra E]

/-- Two sets, all of whose elements are pairwise summable: `⋁S ⋁ ⋁T` is the
supremum of the pairwise sums (OAP 24, point 1, twice). -/
theorem isLUB_image2_oplus {S T : Set E} {F G : E} (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hF : IsLUB S F) (hG : IsLUB T G) (hp : ∀ s ∈ S, ∀ t ∈ T, Perp s t) :
    Perp F G ∧ IsLUB (Set.image2 (· ⋎ ·) S T) (F ⋎ G) := by
  have h1 : ∀ s ∈ S, Perp s G ∧ IsLUB ((s ⋎ ·) '' T) (s ⋎ G) := fun s hs =>
    oap24_1 hTne (fun t ht => le_orth_of_perp (hp s hs t ht)) hG
  obtain ⟨hGF, h2⟩ := oap24_1 (x := G) hSne
    (fun s hs => le_orth_of_perp (PCM.perp_comm (h1 s hs).1)) hF
  have hFG : Perp F G := PCM.perp_comm hGF
  refine ⟨hFG, ?_, fun u hu => ?_⟩
  · rintro _ ⟨s, hs, t, ht, rfl⟩; exact oplus_le_oplus (hF.1 hs) (hG.1 ht) hFG
  · have hm : ∀ s ∈ S, s ⋎ G ≤ u := fun s hs =>
      (h1 s hs).2.2 (by rintro _ ⟨t, ht, rfl⟩; exact hu ⟨s, hs, t, ht, rfl⟩)
    rw [oplus_comm]
    exact h2.2 (by rintro _ ⟨s, hs, rfl⟩; show G ⋎ s ≤ u; rw [oplus_comm]; exact hm s hs)

/-- Mutually cofinal sets have the same suprema. -/
theorem isLUB_of_cofinal {α : Type*} [Preorder α] {A B : Set α} {x : α} (hA : IsLUB A x)
    (hAB : ∀ a ∈ A, ∃ b ∈ B, a ≤ b) (hBA : ∀ b ∈ B, ∃ a ∈ A, b ≤ a) : IsLUB B x :=
  ⟨fun b hb => let ⟨_, ha, h⟩ := hBA b hb; le_trans h (hA.1 ha),
   fun _ hu => hA.2 fun a ha => let ⟨_, hb, h⟩ := hAB a ha; le_trans h (hu hb)⟩

end Suprema

section OmegaTools

variable {M : Type u} [EffectMonoid M] [OmegaComplete M]

/-- `(⋁S)·(⋁T) = ⋁_{s,t} s·t` for non-empty `S`, `T` (OAP 43, twice). -/
theorem isLUB_image2_mul {S T : Set M} {F G : M} (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hF : IsLUB S F) (hG : IsLUB T G) : IsLUB (Set.image2 (· * ·) S T) (F * G) := by
  have h1 := isLUB_mul_right hSne hF G
  refine ⟨?_, fun u hu => h1.2 ?_⟩
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    exact le_trans (emul_le_emul_left s (hG.1 ht)) (emul_le_emul_right (hF.1 hs) G)
  · rintro _ ⟨s, hs, rfl⟩
    exact (isLUB_mul_left hTne hG s).2 (by rintro _ ⟨t, ht, rfl⟩; exact hu ⟨s, hs, t, ht, rfl⟩)

/-- An Archimedean principle: if `eₖ ≤ x`, `⋀ₖ eₖ = 0` and `x ⊖ eₖ ≤ u` for
all `k`, then `x ≤ u`.  (Via the meet `x ∧ u` of OAP 37.) -/
theorem le_of_osub_le {x u : M} {e : ℕ → M} (he : ∀ k, e k ≤ x)
    (hglb : IsGLB (Set.range e) 0) (hu : ∀ k, x ⊖ e k ≤ u) : x ≤ u := by
  set w := emInf x u
  have hwx : w ≤ x := emInf_le_left x u
  have hlow : ∀ k, x ⊖ w ≤ e k := fun k => by
    have h1 : x ⊖ e k ≤ w := le_emInf (osub_le (he k)) (hu k)
    have := osub_le_osub_right hwx h1
    rwa [osub_osub (he k)] at this
  have h0 : x ⊖ w = 0 := eq_zero_of_le_zero (hglb.2 (by rintro _ ⟨k, rfl⟩; exact hlow k))
  have hx : w ⋎ (x ⊖ w) = x := oplus_osub hwx
  rw [h0, oplus_zero] at hx
  calc x = w := hx.symm
    _ ≤ u := emInf_le_right x u

end OmegaTools

section Dyadic

/-- Real inequalities between dyadic rationals `m/2ⁿ ≤ m'/2ⁿ'` as natural
number inequalities at the common level `n + n'`. -/
theorem dy_nat_le {n n' m m' : ℕ} (h : (m : ℝ) / 2 ^ n ≤ m' / 2 ^ n') :
    2 ^ n' * m ≤ 2 ^ n * m' := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
  have : ((2 ^ n' * m : ℕ) : ℝ) ≤ ((2 ^ n * m' : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

theorem dy_nat_le_pow {n m : ℕ} (h : (m : ℝ) / 2 ^ n ≤ 1) : m ≤ 2 ^ n := by
  rw [div_le_one (by positivity)] at h
  exact_mod_cast h

theorem dy_val_pair (n n' m m' : ℕ) :
    ((2 ^ n' * m + 2 ^ n * m' : ℕ) : ℝ) / 2 ^ (n + n') = (m : ℝ) / 2 ^ n + m' / 2 ^ n' := by
  push_cast; rw [pow_add]; field_simp

theorem dy_val_mul (n n' m m' : ℕ) :
    ((m * m' : ℕ) : ℝ) / 2 ^ (n + n') = (m : ℝ) / 2 ^ n * (m' / 2 ^ n') := by
  rw [Nat.cast_mul, pow_add, mul_div_mul_comm]

theorem dy_val_nonneg (n m : ℕ) : (0 : ℝ) ≤ (m : ℝ) / 2 ^ n := by positivity

theorem dy_val_le {r : ℝ} (hr : 0 ≤ r) {n m : ℕ} (h : m = 0 ∨ (m : ℝ) / 2 ^ n < r) :
    (m : ℝ) / 2 ^ n ≤ r := by
  rcases h with rfl | h
  · simpa using hr
  · exact h.le

/-- Dyadic approximation from below: for `r ≥ 0` and every `K` there is
`m/2ᴷ` with `m = 0` or `m/2ᴷ < r`, and `r - 2⁻ᴷ ≤ m/2ᴷ ≤ r`. -/
theorem dyadic_approx {r : ℝ} (hr : 0 ≤ r) (K : ℕ) :
    ∃ m : ℕ, (m = 0 ∨ (m : ℝ) / 2 ^ K < r) ∧ r - 1 / 2 ^ K ≤ (m : ℝ) / 2 ^ K ∧
      (m : ℝ) / 2 ^ K ≤ r := by
  have h2 : (0 : ℝ) < 2 ^ K := by positivity
  rcases hr.eq_or_lt with rfl | hpos
  · refine ⟨0, Or.inl rfl, ?_, by simp⟩
    rw [Nat.cast_zero, zero_div, zero_sub, neg_nonpos]; positivity
  set c := ⌈r * 2 ^ K⌉₊
  have hc0 : 0 < c := Nat.ceil_pos.2 (by positivity)
  have hc1 : (c : ℝ) < r * 2 ^ K + 1 := Nat.ceil_lt_add_one (by positivity)
  have hc2 : r * 2 ^ K ≤ c := Nat.le_ceil _
  have hm : ((c - 1 : ℕ) : ℝ) = c - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  refine ⟨c - 1, Or.inr ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ h2, hm]; linarith
  · rw [le_div_iff₀ h2, sub_mul, one_div, inv_mul_cancel₀ h2.ne', hm]; linarith
  · rw [div_le_iff₀ h2, hm]; linarith

theorem exists_inv_two_pow_lt {ε : ℝ} (hε : 0 < ε) : ∃ K : ℕ, 1 / (2 : ℝ) ^ K < ε := by
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨K, by rwa [div_pow, one_pow] at hK⟩

end Dyadic

section Half

variable {M : Type u} [EffectMonoid M]

/-- `a` is a half: `a ⊥ a` and `a ⋁ a = 1`. -/
def IsHalf (a : M) : Prop := Perp a a ∧ a ⋎ a = 1

variable {a : M}

/-- `2ⁿ·aⁿ = (a ⋁ a)ⁿ = 1` (as in OAP 26, point 3). -/
theorem IsHalf.pow_nsum (h : IsHalf a) (n : ℕ) : IsNSum (a ^ n) (2 ^ n) 1 := by
  have key : IsNSum (a ^ n) (2 ^ n) ((a ⋎ a) ^ n) := by
    induction n with
    | zero => simpa using isNSum_one (1 : M)
    | succ n ih =>
      obtain ⟨hp, e⟩ := mul_oplus ((a ⋎ a) ^ n) h.1
      rw [emul_pow_succ, emul_pow_succ, e, pow_succ 2, mul_two]
      exact ih.emul_right.add ih.emul_right hp
  rwa [h.2, one_pow] at key

variable (a) in
/-- The dyadic element `m/2ⁿ ↦ m·aⁿ` of the proof of OAP 50 (the print's
`\overline{q}` for `q = m/2ⁿ`). -/
noncomputable def dyEl (n m : ℕ) : M := nsum (a ^ n) m

theorem dyEl_zero (n : ℕ) : dyEl a n 0 = 0 := rfl

theorem dyEl_one (n : ℕ) : dyEl a n 1 = a ^ n := by
  show (0 : M) ⋎ a ^ n = a ^ n
  exact zero_oplus _

theorem IsHalf.isNSum_dyEl (h : IsHalf a) {n m : ℕ} (hm : m ≤ 2 ^ n) :
    IsNSum (a ^ n) m (dyEl a n m) := by
  obtain ⟨t, ht, -⟩ := (h.pow_nsum n).le_of_le hm
  rw [dyEl, ht.eq_nsum]; exact ht

theorem IsHalf.dyEl_add (h : IsHalf a) {n m k : ℕ} (hmk : m + k ≤ 2 ^ n) :
    Perp (dyEl a n m) (dyEl a n k) ∧ dyEl a n m ⋎ dyEl a n k = dyEl a n (m + k) :=
  (h.isNSum_dyEl hmk).split (h.isNSum_dyEl (by omega)) (h.isNSum_dyEl (by omega))

theorem IsHalf.dyEl_mono (h : IsHalf a) {n m m' : ℕ} (hmm : m ≤ m') (hm' : m' ≤ 2 ^ n) :
    dyEl a n m ≤ dyEl a n m' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmm
  have := h.dyEl_add hm'
  rw [← this.2]; exact le_oplus_left this.1

/-- "`\overline{q} = m aⁿ` is independent of the choice of `m` and `n`":
`(2ʲm)·aⁿ⁺ʲ = m·aⁿ`. -/
theorem IsHalf.dyEl_shift (h : IsHalf a) {n m : ℕ} (hm : m ≤ 2 ^ n) (j : ℕ) :
    dyEl a (n + j) (2 ^ j * m) = dyEl a n m := by
  have h1 : IsNSum (a ^ (n + j)) (2 ^ j) (a ^ n) := by
    have := (h.pow_nsum j).emul_left (y := a ^ n)
    rwa [emul_one, ← pow_add] at this
  exact (h1.comp (h.isNSum_dyEl hm)).eq_nsum

/-- The dyadic elements are monotone in the value `m/2ⁿ`. -/
theorem IsHalf.dyEl_le (h : IsHalf a) {n n' m m' : ℕ} (hm : m ≤ 2 ^ n) (hm' : m' ≤ 2 ^ n')
    (hv : (m : ℝ) / 2 ^ n ≤ m' / 2 ^ n') : dyEl a n m ≤ dyEl a n' m' := by
  rw [← h.dyEl_shift hm n', ← h.dyEl_shift hm' n, Nat.add_comm n' n]
  apply h.dyEl_mono (dy_nat_le hv)
  rw [pow_add]; exact Nat.mul_le_mul_left _ hm'

/-- Dyadic elements add as their values do. -/
theorem IsHalf.dyEl_pair (h : IsHalf a) {n n' m m' : ℕ} (hm : m ≤ 2 ^ n) (hm' : m' ≤ 2 ^ n')
    (hv : (m : ℝ) / 2 ^ n + m' / 2 ^ n' ≤ 1) :
    2 ^ n' * m + 2 ^ n * m' ≤ 2 ^ (n + n') ∧ Perp (dyEl a n m) (dyEl a n' m') ∧
      dyEl a n m ⋎ dyEl a n' m' = dyEl a (n + n') (2 ^ n' * m + 2 ^ n * m') := by
  have hb : 2 ^ n' * m + 2 ^ n * m' ≤ 2 ^ (n + n') :=
    dy_nat_le_pow (by rw [dy_val_pair]; exact hv)
  have := h.dyEl_add hb
  rw [h.dyEl_shift hm n', Nat.add_comm n n', h.dyEl_shift hm' n, Nat.add_comm n' n] at this
  exact ⟨hb, this⟩

/-- Dyadic elements multiply as their values do: `m aⁿ · m' aⁿ' = (mm') aⁿ⁺ⁿ'`. -/
theorem IsHalf.dyEl_mul (h : IsHalf a) {n n' m m' : ℕ} (hm : m ≤ 2 ^ n) (hm' : m' ≤ 2 ^ n') :
    dyEl a n m * dyEl a n' m' = dyEl a (n + n') (m * m') := by
  have h1 := (h.isNSum_dyEl hm').emul_left (y := a ^ n)
  have h2 := (h.isNSum_dyEl hm).emul_right (y := dyEl a n' m')
  rw [← pow_add] at h1
  rw [Nat.mul_comm]
  exact ((h1.comp h2).eq_nsum).symm

variable (a) in
/-- The dyadic elements strictly below `r` (together with `0`). -/
def dySet (r : ℝ) : Set M :=
  {x | ∃ n m : ℕ, m ≤ 2 ^ n ∧ (m = 0 ∨ (m : ℝ) / 2 ^ n < r) ∧ x = dyEl a n m}

theorem zero_mem_dySet (r : ℝ) : (0 : M) ∈ dySet a r := ⟨0, 0, by simp, Or.inl rfl, rfl⟩

theorem dySet_nonempty (r : ℝ) : (dySet a r).Nonempty := ⟨0, zero_mem_dySet r⟩

open Classical in
variable (a) in
/-- The print's `\overline{λ}` for real `λ`: the supremum of the dyadic
elements `\overline{q}` with `q < λ` (see `isLUB_dyCl`). -/
noncomputable def dyCl (r : ℝ) : M := if h : ∃ s, IsLUB (dySet a r) s then h.choose else 0

variable [OmegaComplete M]

/-- `\overline{λ}` exists: the dyadic elements below `λ` form a countable
chain. -/
theorem IsHalf.isLUB_dyCl (h : IsHalf a) (r : ℝ) : IsLUB (dySet a r) (dyCl a r) := by
  have hex : ∃ s, IsLUB (dySet a r) s := by
    refine (oap13_omegaComplete_iff.1 inferInstance) _ ?_ ⟨dySet_nonempty r, ?_⟩
    · refine (Set.countable_range fun p : ℕ × ℕ => dyEl a p.1 p.2).mono ?_
      rintro _ ⟨n, m, -, -, rfl⟩; exact ⟨(n, m), rfl⟩
    · rintro _ ⟨n, m, hm, hr, rfl⟩ _ ⟨n', m', hm', hr', rfl⟩
      rcases le_total ((m : ℝ) / 2 ^ n) (m' / 2 ^ n') with hv | hv
      · exact ⟨_, ⟨n', m', hm', hr', rfl⟩, h.dyEl_le hm hm' hv, le_rfl⟩
      · exact ⟨_, ⟨n, m, hm, hr, rfl⟩, le_rfl, h.dyEl_le hm' hm hv⟩
  unfold dyCl
  split_ifs
  exact hex.choose_spec

/-- "Both definitions of `\overline{q}` coincide": for dyadic `q = m/2ⁿ`,
`\overline{q} = m·aⁿ`.  As in the print: `m aⁿ ⊖ aⁿ⁺ᵏ` is the dyadic element
of `q - 2^{-(n+k)}` and `⋀ₖ aⁿ⁺ᵏ = 0` (OAP 26). -/
theorem IsHalf.dyCl_dyEl (h : IsHalf a) {n m : ℕ} (hm : m ≤ 2 ^ n) :
    dyCl a ((m : ℝ) / 2 ^ n) = dyEl a n m := by
  refine (h.isLUB_dyCl _).unique ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨n', m', hm', hr, rfl⟩
    rcases hr with rfl | hr
    · exact zero_le' _
    · exact h.dyEl_le hm' hm hr.le
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · exact zero_le' u
  -- `m·aⁿ = (2ᵏm - 1)·aⁿ⁺ᵏ ⋁ aⁿ⁺ᵏ`
  have split : ∀ k : ℕ, Perp (a ^ (n + k)) (dyEl a (n + k) (2 ^ k * m - 1)) ∧
      a ^ (n + k) ⋎ dyEl a (n + k) (2 ^ k * m - 1) = dyEl a n m := fun k => by
    have hk : 1 ≤ 2 ^ k * m := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hb : 1 + (2 ^ k * m - 1) ≤ 2 ^ (n + k) := by
      rw [Nat.add_sub_cancel' hk, pow_add, Nat.mul_comm (2 ^ n)]
      exact Nat.mul_le_mul_left _ hm
    have := h.dyEl_add hb
    rw [Nat.add_sub_cancel' hk, h.dyEl_shift hm, dyEl_one] at this
    exact this
  have hglb : IsGLB (Set.range fun k => a ^ (n + k)) 0 := by
    refine ⟨by rintro _ ⟨k, rfl⟩; exact zero_le' _, fun l hl => (oap26_3 h.1).2 ?_⟩
    rintro _ ⟨k, rfl⟩
    exact le_trans (hl ⟨k, rfl⟩) (pow_antitone a (Nat.le_add_left k n))
  refine le_of_osub_le (e := fun k => a ^ (n + k)) (fun k => ?_) hglb fun k => ?_
  · rw [← (split k).2]; exact le_oplus_left (split k).1
  · have e : dyEl a n m ⊖ a ^ (n + k) = dyEl a (n + k) (2 ^ k * m - 1) :=
      (osub_eq_iff (by rw [← (split k).2]; exact le_oplus_left (split k).1)).2 (split k)
    simp only [e]
    refine hu ⟨n + k, 2 ^ k * m - 1, le_trans (Nat.sub_le _ _)
      (by rw [pow_add, Nat.mul_comm (2 ^ n)]; exact Nat.mul_le_mul_left _ hm), Or.inr ?_, rfl⟩
    have hk : 1 ≤ 2 ^ k * m := Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [Nat.cast_sub hk, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat, pow_add,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n, pow_pos (by norm_num : (0 : ℝ) < 2) k]

theorem IsHalf.dyCl_one (h : IsHalf a) : dyCl a 1 = 1 := by
  have := h.dyCl_dyEl (n := 0) (m := 1) (by norm_num)
  simpa [dyEl_one] using this

/-- `\overline{λ + μ} = \overline{λ} ⋁ \overline{μ}` (addition preserves
suprema, OAP 24). -/
theorem IsHalf.dyCl_add (h : IsHalf a) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) (hrt : r + t ≤ 1) :
    Perp (dyCl a r) (dyCl a t) ∧ dyCl a r ⋎ dyCl a t = dyCl a (r + t) := by
  have hp : ∀ s ∈ dySet a r, ∀ u ∈ dySet a t, Perp s u := by
    rintro _ ⟨n, m, hm, hmr, rfl⟩ _ ⟨n', m', hm', hmt, rfl⟩
    exact (h.dyEl_pair hm hm' (by linarith [dy_val_le hr hmr, dy_val_le ht hmt])).2.1
  obtain ⟨hFG, hL⟩ := isLUB_image2_oplus (dySet_nonempty r) (dySet_nonempty t)
    (h.isLUB_dyCl r) (h.isLUB_dyCl t) hp
  refine ⟨hFG, (isLUB_of_cofinal hL ?_ ?_).unique (h.isLUB_dyCl (r + t))⟩
  · rintro _ ⟨_, ⟨n, m, hm, hmr, rfl⟩, _, ⟨n', m', hm', hmt, rfl⟩, rfl⟩
    obtain ⟨hb, -, e⟩ := h.dyEl_pair hm hm' (by linarith [dy_val_le hr hmr, dy_val_le ht hmt])
    refine ⟨_, ⟨n + n', _, hb, ?_, e⟩, le_rfl⟩
    rcases hmr with rfl | h1 <;> rcases hmt with rfl | h2
    · left; simp
    · right; rw [dy_val_pair]; simp only [Nat.cast_zero, zero_div]; linarith
    · right; rw [dy_val_pair]; simp only [Nat.cast_zero, zero_div]; linarith
    · right; rw [dy_val_pair]; linarith
  · rintro _ ⟨n, m, hm, hmv, rfl⟩
    rcases hmv with rfl | hv
    · exact ⟨_, ⟨0, zero_mem_dySet r, 0, zero_mem_dySet t, rfl⟩, zero_le' _⟩
    obtain ⟨K, hK⟩ := exists_inv_two_pow_lt (ε := (r + t - m / 2 ^ n) / 2) (by linarith)
    obtain ⟨m1, i1, l1, u1⟩ := dyadic_approx hr K
    obtain ⟨m2, i2, l2, u2⟩ := dyadic_approx ht K
    have b1 : m1 ≤ 2 ^ K := dy_nat_le_pow (by linarith)
    have b2 : m2 ≤ 2 ^ K := dy_nat_le_pow (by linarith)
    obtain ⟨hb, -, e⟩ := h.dyEl_pair b1 b2 (by linarith)
    refine ⟨_, ⟨_, ⟨K, m1, b1, i1, rfl⟩, _, ⟨K, m2, b2, i2, rfl⟩, rfl⟩, ?_⟩
    simp only
    rw [e]
    exact h.dyEl_le hm hb (by rw [dy_val_pair]; linarith)

/-- `\overline{λμ} = \overline{λ}·\overline{μ}` (multiplication preserves
suprema, OAP 43). -/
theorem IsHalf.dyCl_mul (h : IsHalf a) {r t : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (ht : 0 ≤ t)
    (ht1 : t ≤ 1) : dyCl a r * dyCl a t = dyCl a (r * t) := by
  have hL := isLUB_image2_mul (dySet_nonempty r) (dySet_nonempty t)
    (h.isLUB_dyCl r) (h.isLUB_dyCl t)
  refine (isLUB_of_cofinal hL ?_ ?_).unique (h.isLUB_dyCl (r * t))
  · rintro _ ⟨_, ⟨n, m, hm, hmr, rfl⟩, _, ⟨n', m', hm', hmt, rfl⟩, rfl⟩
    have hb : m * m' ≤ 2 ^ (n + n') := by rw [pow_add]; exact Nat.mul_le_mul hm hm'
    refine ⟨_, ⟨n + n', m * m', hb, ?_, h.dyEl_mul hm hm'⟩, le_rfl⟩
    rcases hmr with rfl | h1
    · left; simp
    rcases hmt with rfl | h2
    · left; simp
    right; rw [dy_val_mul]
    exact mul_lt_mul'' h1 h2 (dy_val_nonneg _ _) (dy_val_nonneg _ _)
  · rintro _ ⟨n, m, hm, hmv, rfl⟩
    rcases hmv with rfl | hv
    · exact ⟨_, ⟨0, zero_mem_dySet r, 0, zero_mem_dySet t, rfl⟩, zero_le' _⟩
    obtain ⟨K, hK⟩ := exists_inv_two_pow_lt (ε := (r * t - m / 2 ^ n) / 2) (by linarith)
    obtain ⟨m1, i1, l1, u1⟩ := dyadic_approx hr K
    obtain ⟨m2, i2, l2, u2⟩ := dyadic_approx ht K
    have b1 : m1 ≤ 2 ^ K := dy_nat_le_pow (by linarith)
    have b2 : m2 ≤ 2 ^ K := dy_nat_le_pow (by linarith)
    have hb : m1 * m2 ≤ 2 ^ (K + K) := by rw [pow_add]; exact Nat.mul_le_mul b1 b2
    refine ⟨_, ⟨_, ⟨K, m1, b1, i1, rfl⟩, _, ⟨K, m2, b2, i2, rfl⟩, rfl⟩, ?_⟩
    simp only
    rw [h.dyEl_mul b1 b2]
    refine h.dyEl_le hm hb ?_
    rw [dy_val_mul]
    set d := (m1 : ℝ) / 2 ^ K
    set e := (m2 : ℝ) / 2 ^ K
    have hd0 : 0 ≤ d := dy_val_nonneg _ _
    have he0 : 0 ≤ e := dy_val_nonneg _ _
    have k1 : r * (t - e) ≤ 1 * (1 / 2 ^ K) := mul_le_mul hr1 (by linarith) (by linarith) zero_le_one
    have k2 : e * (r - d) ≤ 1 * (1 / 2 ^ K) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) zero_le_one
    nlinarith

/-- The convex action `(λ, s) ↦ \overline{λ}·s` of a half `a` (proof of
OAP 50). -/
noncomputable def IsHalf.convexAction (h : IsHalf a) : ConvexAction M where
  act l x := dyCl a l * x
  act_act l m x := by
    show dyCl a l * (dyCl a m * x) = dyCl a ((l * m : I) : ℝ) * x
    rw [← emul_assoc, h.dyCl_mul l.2.1 l.2.2 m.2.1 m.2.2, Set.Icc.coe_mul]
  add_act l m ν x e := by
    obtain ⟨hp, hs⟩ := h.dyCl_add l.2.1 m.2.1 (by rw [e]; exact ν.2.2)
    obtain ⟨hp', e'⟩ := oplus_mul x hp
    refine ⟨hp', ?_⟩
    show dyCl a l * x ⋎ dyCl a m * x = dyCl a ν * x
    rw [← e', hs, e]
  act_oplus l _ _ hab := mul_oplus _ hab
  one_act x := by
    show dyCl a ((1 : I) : ℝ) * x = x
    rw [Set.Icc.coe_one, h.dyCl_one, eone_mul]

theorem IsHalf.convexAction_act (h : IsHalf a) (l : I) (x : M) :
    h.convexAction.act l x = dyCl a l * x := rfl

/-- **OAP 50** (`prop:dircompleteisconvex`, first.tex:1867, Proposition): a
halvable ω-complete effect monoid is convex.  The action is
`λ·s = \overline{λ}·s` (`IsHalf.convexAction`), with `\overline{m/2ⁿ} = m aⁿ`
for a half `a` (`IsHalf.dyCl_dyEl`). -/
theorem oap50 (hM : HalvableEA M) : IsConvex M := by
  obtain ⟨a, ha, h1⟩ := hM
  exact ⟨IsHalf.convexAction (a := a) ⟨ha, h1⟩⟩

end Half

end Papers.OAP
