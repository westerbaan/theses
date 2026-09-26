/-
Papers/SIG/Prelim.lean

SIG §2 "Preliminaries" (main.tex:190–436), points SIG 1–11: partial
commutative monoids, partially σ-additive monoids (σ-PAMs), PCM- and
σ-PAM-enriched categories, partial projections and compatible families,
finitely partially additive categories (finPACs) and partially σ-additive
categories (σ-PACs), effect algebras.

Design (see `Papers/SIG/PLAN.md`):
* PCMs and effect algebras are the tree's `Theses.B.Eff.PCM` (174II) and
  `EffectAlgebra` (175I); finPACs are the tree's `FinPAC` (180VII).
* A σ-PAM is the new class `SigmaPAM`: a partial sum on families `J → M`
  indexed by countable `J : Type`.  Partition-associativity is stated for the
  fibres of an arbitrary map `p : J → K`, so partition blocks may be empty.
  The PCM a σ-PAM induces (the note after SIG 2) is `SigmaPAM.toPCM`, a `def`;
  for hom-sets it is installed by the instance `homPCM`.
-/
import Theses.B.Eff.Effectus

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits Theses.B.Eff

namespace Papers.SIG

universe u v w

/-! ## SIG 1: partial commutative monoids -/

/-- **SIG 1** (`def:pcm`, main.tex:201, Definition): a **PCM** is a set with
`0` and a partial binary operation `⊕` which is associative, commutative and
unital, `=` being Kleene equality.  This is the tree's `PCM` (174II); its
associativity axiom is one direction of the Kleene equation
`(x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)`, and this theorem is the equation itself, in both
directions. -/
theorem pcm_assoc_kleene {M : Type u} [PCM M] (x y z s : M) :
    (∃ (hxy : Perp x y) (h : Perp (ovee x y hxy) z), ovee (ovee x y hxy) z h = s) ↔
      ∃ (hyz : Perp y z) (h : Perp x (ovee y z hyz)), ovee x (ovee y z hyz) h = s := by
  constructor
  · rintro ⟨hxy, h, rfl⟩
    exact ⟨PCM.perp_of_ovee_perp hxy h, PCM.perp_ovee_of_ovee_perp hxy h,
      (PCM.ovee_assoc hxy h).symm⟩
  · rintro ⟨hyz, h, rfl⟩
    obtain ⟨hxy, h', e⟩ := PCM.assoc_left hyz h
    exact ⟨hxy, h', e⟩

/-- **SIG 1** (`def:pcm`, main.tex:201, Definition): a map `f : M → N` of
PCMs is **additive** if `f 0 = 0` and `f x ⊕ f y = f (x ⊕ y)` whenever
`x ⊥ y` (Kleene: the left side is defined).  The tree's `PCMHom` omits
`f 0 = 0`, hence this predicate. -/
def IsAdditive {M : Type u} {N : Type v} [PCM M] [PCM N] (f : M → N) : Prop :=
  f 0 = 0 ∧ ∀ {x y : M} (h : Perp x y), ∃ h' : Perp (f x) (f y), ovee (f x) (f y) h' = f (ovee x y h)

/-- **SIG 1** (`def:pcm`, main.tex:201, Definition): `g : M × N → L` is
**biadditive** if it is additive in each argument. -/
def IsBiadditive {M : Type u} {N : Type v} {L : Type w} [PCM M] [PCM N] [PCM L]
    (g : M → N → L) : Prop :=
  (∀ x, IsAdditive (g x)) ∧ ∀ y, IsAdditive (fun x => g x y)

/-! ## SIG 2: partially σ-additive monoids -/

/-- **SIG 2** (main.tex:249, Definition): a **partially σ-additive monoid**
(σ-PAM) is a nonempty set `M` with a partial operation `⋁` on countable
families (`Summable x`: the sum is defined; `sum x h` its value) such that

* *(partition-associativity)* for a countable family `(x_j)_{j∈J}` and a
  countable partition `J = ⊎_{k∈K} J_k` — given here as the fibres
  `J_k = {j | p j = k}` of a map `p : J → K`, so blocks may be empty — the
  family is summable iff each `(x_j)_{j∈J_k}` is summable and so is
  `(⋁_{j∈J_k} x_j)_k`; and then `⋁_J x_j = ⋁_k ⋁_{J_k} x_j`;
* *(unary sum)* a family indexed by a one-element set is summable, with sum
  its only member;
* *(limit)* a countable family is summable if all its finite subfamilies are.

Countable index sets are types `J : Type` with `[Countable J]` (finite ones
included). -/
class SigmaPAM (M : Type u) where
  /-- `Summable x`: the countable family `x` is summable. -/
  Summable : ∀ {J : Type} [Countable J], (J → M) → Prop
  /-- The sum `⋁_j x_j` of a summable family. -/
  sum : ∀ {J : Type} [Countable J] (x : J → M), Summable x → M
  nonempty : Nonempty M
  summable_iff_partition : ∀ {J K : Type} [Countable J] [Countable K] (x : J → M)
    (p : J → K), Summable x ↔
      ∃ h : ∀ k, Summable (fun j : {j // p j = k} => x j.1),
        Summable (fun k => sum (fun j : {j // p j = k} => x j.1) (h k))
  sum_partition : ∀ {J K : Type} [Countable J] [Countable K] (x : J → M) (p : J → K)
    (hx : Summable x) (h : ∀ k, Summable (fun j : {j // p j = k} => x j.1))
    (h' : Summable (fun k => sum (fun j : {j // p j = k} => x j.1) (h k))),
    sum x hx = sum (fun k => sum (fun j : {j // p j = k} => x j.1) (h k)) h'
  summable_unique : ∀ {J : Type} [Unique J] (x : J → M), Summable x
  sum_unique : ∀ {J : Type} [Unique J] (x : J → M) (h : Summable x), sum x h = x default
  limit : ∀ {J : Type} [Countable J] (x : J → M),
    (∀ F : Finset J, Summable (fun j : F => x j.1)) → Summable x

namespace SigmaPAM

variable {M : Type u} [SigmaPAM M]

/-- `SumsTo x s`: the family `x` is summable with sum `s` (the relational
form of `sum`, used throughout to avoid dependent rewriting). -/
def SumsTo {J : Type} [Countable J] (x : J → M) (s : M) : Prop :=
  ∃ h : Summable x, sum x h = s

section API

variable {J K : Type} [Countable J] [Countable K]

theorem sumsTo_sum {x : J → M} (h : Summable x) : SumsTo x (sum x h) := ⟨h, rfl⟩

theorem SumsTo.summable {x : J → M} {s : M} (h : SumsTo x s) : Summable x := h.1

theorem SumsTo.sum_eq {x : J → M} {s : M} (h : SumsTo x s) (h' : Summable x) :
    sum x h' = s := h.2

theorem SumsTo.unique {x : J → M} {s t : M} (hs : SumsTo x s) (ht : SumsTo x t) : s = t := by
  obtain ⟨h, rfl⟩ := hs
  obtain ⟨h', rfl⟩ := ht
  rfl

theorem sum_congr {x y : J → M} (e : x = y) (hx : Summable x) (hy : Summable y) :
    sum x hx = sum y hy := by
  subst e; rfl

theorem sumsTo_congr {x y : J → M} (e : ∀ j, x j = y j) {s : M} :
    SumsTo x s ↔ SumsTo y s := by
  rw [funext e]

/-- Partition-associativity in relational form: `x` sums to `s` iff the
blocks `x|_{p⁻¹ k}` sum to some `t k` and `t` sums to `s`. -/
theorem sumsTo_partition_iff (x : J → M) (p : J → K) (s : M) :
    SumsTo x s ↔ ∃ t : K → M,
      (∀ k, SumsTo (fun j : {j // p j = k} => x j.1) (t k)) ∧ SumsTo t s := by
  constructor
  · rintro ⟨hx, rfl⟩
    obtain ⟨h, h'⟩ := (summable_iff_partition x p).1 hx
    exact ⟨_, fun k => sumsTo_sum (h k), h', (sum_partition x p hx h h').symm⟩
  · rintro ⟨t, ht, hts⟩
    have h : ∀ k, Summable (fun j : {j // p j = k} => x j.1) := fun k => (ht k).summable
    have e : (fun k => sum (fun j : {j // p j = k} => x j.1) (h k)) = t :=
      funext fun k => (sumsTo_sum (h k)).unique (ht k)
    have h' : Summable (fun k => sum (fun j : {j // p j = k} => x j.1) (h k)) := by
      rw [e]; exact hts.summable
    have hx := (summable_iff_partition x p).2 ⟨h, h'⟩
    refine ⟨hx, ?_⟩
    rw [sum_partition x p hx h h', sum_congr e h' hts.summable]
    exact hts.sum_eq _

/-- The unary sum axiom in relational form. -/
theorem sumsTo_of_unique {I : Type} [Unique I] (x : I → M) : SumsTo x (x default) :=
  ⟨summable_unique x, sum_unique x _⟩

theorem sumsTo_of_unique' {I : Type} [Unique I] (x : I → M) (i : I) : SumsTo x (x i) := by
  rw [Unique.eq_default i]; exact sumsTo_of_unique x

/-- Sums are invariant under reindexing along a bijection (from
partition-associativity with singleton blocks and the unary axiom). -/
theorem sumsTo_comp_equiv (e : J ≃ K) (x : K → M) (s : M) :
    SumsTo (x ∘ e) s ↔ SumsTo x s := by
  rw [sumsTo_partition_iff (x ∘ e) e]
  have hu : ∀ k, SumsTo (fun j : {j // e j = k} => (x ∘ e) j.1) (x k) := by
    intro k
    let _ : Unique {j // e j = k} :=
      { default := ⟨e.symm k, by simp⟩
        uniq := fun j => Subtype.ext ((e.symm_apply_eq.mpr j.2.symm).symm) }
    have h := sumsTo_of_unique (fun j : {j // e j = k} => (x ∘ e) j.1)
    have hd : (x ∘ e) (default : {j // e j = k}).1 = x k := by
      show x (e (e.symm k)) = x k
      rw [e.apply_symm_apply]
    rwa [hd] at h
  constructor
  · rintro ⟨t, ht, hts⟩
    have : t = x := funext fun k => (ht k).unique (hu k)
    rwa [this] at hts
  · intro hs
    exact ⟨x, hu, hs⟩

theorem sumsTo_comp_equiv' (e : J ≃ K) (x : K → M) (y : J → M) (hy : ∀ j, y j = x (e j))
    (s : M) : SumsTo y s ↔ SumsTo x s := by
  rw [← sumsTo_comp_equiv e x s]
  exact sumsTo_congr hy

/-- Empty families are summable. -/
theorem summable_of_isEmpty {I : Type} [IsEmpty I] (x : I → M) : Summable x := by
  obtain ⟨m⟩ := (nonempty : Nonempty M)
  have h1 : SumsTo (fun _ : Unit => m) m := sumsTo_of_unique _
  obtain ⟨t, ht, -⟩ := (sumsTo_partition_iff (fun _ : Unit => m) (fun _ => true) m).1 h1
  have h2 := ht false
  have : IsEmpty {j : Unit // (fun _ => true) j = false} :=
    ⟨fun j => Bool.noConfusion j.2⟩
  have e : I ≃ {j : Unit // (fun _ => true) j = false} := Equiv.equivOfIsEmpty _ _
  have h3 := (sumsTo_comp_equiv' e (fun j : {j : Unit // (fun _ => true) j = false} => m) x
    (fun i => isEmptyElim i) (t false)).2 h2
  exact h3.summable

/-- The **zero** of a σ-PAM: the sum of the empty family (note after SIG 2). -/
noncomputable def zero : M := sum (Empty.elim : Empty → M) (summable_of_isEmpty _)

theorem sumsTo_of_isEmpty {I : Type} [IsEmpty I] (x : I → M) : SumsTo x zero := by
  have e : I ≃ Empty := Equiv.equivOfIsEmpty _ _
  exact (sumsTo_comp_equiv' e (Empty.elim : Empty → M) x (fun i => isEmptyElim i) _).2
    (sumsTo_sum _)

/-- The fibre of `Sum.elim (fun _ => 0) (fun _ => 1)` over `0` is the left
summand. -/
private noncomputable def fibreInl (J J' : Type) :
    J ≃ {j : J ⊕ J' // Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) j = 0} :=
  Equiv.ofBijective (fun a => ⟨Sum.inl a, rfl⟩)
    ⟨fun a b h => Sum.inl_injective (congrArg Subtype.val h), by
      rintro ⟨(a | b), h⟩
      · exact ⟨a, rfl⟩
      · simp at h⟩

private noncomputable def fibreInr (J J' : Type) :
    J' ≃ {j : J ⊕ J' // Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) j = 1} :=
  Equiv.ofBijective (fun b => ⟨Sum.inr b, rfl⟩)
    ⟨fun a b h => Sum.inr_injective (congrArg Subtype.val h), by
      rintro ⟨(a | b), h⟩
      · simp at h
      · exact ⟨b, rfl⟩⟩

/-- Splitting a sum over a disjoint union `J ⊕ J'`. -/
theorem sumsTo_sum_iff {J' : Type} [Countable J'] (x : J → M) (y : J' → M) (s : M) :
    SumsTo (Sum.elim x y) s ↔ ∃ a b, SumsTo x a ∧ SumsTo y b ∧ SumsTo ![a, b] s := by
  rw [sumsTo_partition_iff (Sum.elim x y) (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1))]
  have h0 : ∀ a, SumsTo (fun j : {j : J ⊕ J' //
      Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) j = 0} => Sum.elim x y j.1) a ↔
      SumsTo x a := fun a =>
    (sumsTo_comp_equiv' (fibreInl J J') _ x (fun _ => rfl) a).symm
  have h1 : ∀ b, SumsTo (fun j : {j : J ⊕ J' //
      Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) j = 1} => Sum.elim x y j.1) b ↔
      SumsTo y b := fun b =>
    (sumsTo_comp_equiv' (fibreInr J J') _ y (fun _ => rfl) b).symm
  constructor
  · rintro ⟨t, ht, hts⟩
    refine ⟨t 0, t 1, (h0 _).1 (ht 0), (h1 _).1 (ht 1), ?_⟩
    have : t = ![t 0, t 1] := by
      funext i; fin_cases i <;> rfl
    rwa [this] at hts
  · rintro ⟨a, b, ha, hb, hs⟩
    refine ⟨![a, b], ?_, hs⟩
    intro k
    fin_cases k
    · exact (h0 a).2 ha
    · exact (h1 b).2 hb

/-- Binary sums commute. -/
theorem sumsTo_pair_comm {a b s : M} (h : SumsTo ![a, b] s) : SumsTo ![b, a] s :=
  (sumsTo_comp_equiv' (Equiv.swap (0 : Fin 2) 1) ![a, b] ![b, a]
    (by intro i; fin_cases i <;> rfl) s).2 h

/-- `0 ⊕ a = a`. -/
theorem sumsTo_zero_pair (a : M) : SumsTo ![zero, a] a := by
  let _ : Unique (Empty ⊕ Unit) :=
    { default := Sum.inr ()
      uniq := by rintro (e | ⟨⟩); exact e.elim; rfl }
  have h : SumsTo (Sum.elim (Empty.elim : Empty → M) (fun _ : Unit => a)) a :=
    sumsTo_of_unique' _ (Sum.inr ())
  obtain ⟨u, v, hu, hv, huv⟩ := (sumsTo_sum_iff _ _ _).1 h
  have hu' : u = zero := hu.unique (sumsTo_of_isEmpty _)
  have hv' : v = a := hv.unique (sumsTo_of_unique' (fun _ : Unit => a) ())
  rw [hu', hv'] at huv
  exact huv

/-- The bijection `Unit ⊕ Fin 2 ≃ Fin 2 ⊕ Unit` regrouping `a, (b, c)` as
`(a, b), c`. -/
private def regroup : Unit ⊕ Fin 2 ≃ Fin 2 ⊕ Unit where
  toFun := Sum.elim (fun _ => Sum.inl 0) (fun i => if i = 0 then Sum.inl 1 else Sum.inr ())
  invFun := Sum.elim (fun i => if i = 0 then Sum.inl () else Sum.inr 0) (fun _ => Sum.inr 1)
  left_inv := by rintro (⟨⟩ | i) <;> [rfl; (fin_cases i <;> rfl)]
  right_inv := by rintro (i | ⟨⟩) <;> [(fin_cases i <;> rfl); rfl]

/-- Associativity of binary sums: `(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)`. -/
theorem sumsTo_pair_assoc {a b c u v : M} (hab : SumsTo ![a, b] u) (h : SumsTo ![u, c] v) :
    ∃ w, SumsTo ![b, c] w ∧ SumsTo ![a, w] v := by
  have h1 : SumsTo (Sum.elim ![a, b] (fun _ : Unit => c)) v :=
    (sumsTo_sum_iff _ _ _).2 ⟨u, c, hab, sumsTo_of_unique' _ (), h⟩
  have h2 : SumsTo (Sum.elim (fun _ : Unit => a) ![b, c]) v := by
    refine (sumsTo_comp_equiv' regroup _ _ ?_ v).2 h1
    rintro (⟨⟩ | i)
    · rfl
    · fin_cases i <;> rfl
  obtain ⟨a', w, ha', hw, hs⟩ := (sumsTo_sum_iff _ _ _).1 h2
  have ha : a' = a := ha'.unique (sumsTo_of_unique' (fun _ : Unit => a) ())
  rw [ha] at hs
  exact ⟨w, hw, hs⟩

theorem sumsTo_pair_assoc' {a b c w v : M} (hbc : SumsTo ![b, c] w) (h : SumsTo ![a, w] v) :
    ∃ u, SumsTo ![a, b] u ∧ SumsTo ![u, c] v := by
  obtain ⟨u, h1, h2⟩ := sumsTo_pair_assoc (sumsTo_pair_comm hbc) (sumsTo_pair_comm h)
  exact ⟨u, sumsTo_pair_comm h1, sumsTo_pair_comm h2⟩

end API

/-- **SIG 2** (main.tex:249, Definition), the closing note: every σ-PAM is a
PCM via `x₁ ⊕ x₂ = ⋁_{i∈{1,2}} xᵢ` and `0 = ⋁ ∅`. -/
noncomputable def toPCM : PCM M where
  zero := zero
  Perp a b := Summable ![a, b]
  ovee a b h := sum ![a, b] h
  perp_comm h := (sumsTo_pair_comm (sumsTo_sum h)).summable
  ovee_comm h := ((sumsTo_pair_comm (sumsTo_sum h)).sum_eq _).symm
  perp_of_ovee_perp hab h := by
    obtain ⟨w, hw, -⟩ := sumsTo_pair_assoc (sumsTo_sum hab) (sumsTo_sum h)
    exact hw.summable
  perp_ovee_of_ovee_perp hab h := by
    obtain ⟨w, hw, hv⟩ := sumsTo_pair_assoc (sumsTo_sum hab) (sumsTo_sum h)
    rw [hw.sum_eq]; exact hv.summable
  ovee_assoc hab h := by
    obtain ⟨w, hw, hv⟩ := sumsTo_pair_assoc (sumsTo_sum hab) (sumsTo_sum h)
    exact (hv.sum_eq hv.summable).symm.trans (sum_congr (by rw [hw.sum_eq]) _ _)
  zero_perp a := (sumsTo_zero_pair a).summable
  zero_ovee a := (sumsTo_zero_pair a).sum_eq _

/-- Under `toPCM`, `a ⊥ b` with `a ⊕ b = s` is the binary σ-sum. -/
theorem toPCM_sumsTo_iff (a b s : M) :
    (∃ h : @Perp M toPCM a b, @ovee M toPCM a b h = s) ↔ SumsTo ![a, b] s := Iff.rfl

theorem toPCM_zero : (@OfNat.ofNat M 0 (@Zero.toOfNat0 M (@PCM.toZero M toPCM))) = zero :=
  rfl

/-- Finite sums (iterated `⊕` of `toPCM` along a list) are σ-sums of the
corresponding finite family. -/
theorem sumsTo_ofFn_iff {n : ℕ} (f : Fin n → M) (s : M) :
    SumsTo f s ↔ @PCM.IsSumOf M toPCM (List.ofFn f) s := by
  let _ : PCM M := toPCM
  induction n generalizing s with
  | zero =>
    rw [List.ofFn_zero, PCM.isSumOf_nil_iff]
    constructor
    · intro h; exact h.unique (sumsTo_of_isEmpty _)
    · rintro rfl; exact sumsTo_of_isEmpty _
  | succ n ih =>
    let e : Fin (n + 1) ≃ Fin n ⊕ PUnit.{1} :=
      (finSuccEquiv n).trans (Equiv.optionEquivSumPUnit _)
    have hx : ∀ i, f i = Sum.elim (fun i : Fin n => f i.succ) (fun _ => f 0) (e i) := by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [e]
      · simp [e]
    rw [sumsTo_comp_equiv' e _ _ hx, sumsTo_sum_iff, List.ofFn_succ, PCM.isSumOf_cons_iff]
    constructor
    · rintro ⟨t, b, ht, hb, hs⟩
      have hb' : b = f 0 := hb.unique (sumsTo_of_unique' (fun _ : PUnit.{1} => f 0) PUnit.unit)
      rw [hb'] at hs
      exact ⟨t, (ih _ t).1 ht, (sumsTo_pair_comm hs).summable,
        (sumsTo_pair_comm hs).sum_eq _⟩
    · rintro ⟨t, ht, hp, rfl⟩
      exact ⟨t, f 0, (ih _ t).2 ht, sumsTo_of_unique' _ PUnit.unit,
        sumsTo_pair_comm (sumsTo_sum hp)⟩

/-- A finite subfamily `(x_j)_{j∈F}` sums to `s` iff the list of its members
(in the order of `F.toList`) sums to `s` in `toPCM`. -/
theorem sumsTo_finset_iff {J : Type} (x : J → M) (F : Finset J) (s : M) :
    SumsTo (fun j : F => x j.1) s ↔ @PCM.IsSumOf M toPCM (F.toList.map x) s := by
  let _ : PCM M := toPCM
  let e : Fin F.card ≃ F := F.equivFin.symm
  rw [← sumsTo_comp_equiv e, sumsTo_ofFn_iff]
  have hp : (List.ofFn ((fun j : F => x j.1) ∘ e)).Perm (F.toList.map x) := by
    have : List.ofFn ((fun j : F => x j.1) ∘ e) = (List.ofFn fun i => (e i).1).map x := by
      rw [List.map_ofFn]; rfl
    rw [this]
    refine List.Perm.map x ((List.perm_ext_iff_of_nodup ?_ F.nodup_toList).2 fun a => ?_)
    · exact List.nodup_ofFn.2 fun i j h => e.injective (Subtype.ext h)
    · rw [List.mem_ofFn, Finset.mem_toList]
      constructor
      · rintro ⟨i, rfl⟩; exact (e i).2
      · intro ha; exact ⟨e.symm ⟨a, ha⟩, by simp⟩
  exact ⟨fun h => PCM.isSumOf_perm hp h, fun h => PCM.isSumOf_perm hp.symm h⟩

/-- Sub-families of summable families are summable (partition into the
subfamily and its complement). -/
theorem summable_subfamily {J : Type} [Countable J] {x : J → M} (hx : Summable x)
    (P : J → Prop) : Summable (fun j : {j // P j} => x j.1) := by
  classical
  obtain ⟨h, -⟩ := (summable_iff_partition x (fun j => decide (P j))).1 hx
  have := h true
  let e : {j // P j} ≃ {j // decide (P j) = true} :=
    Equiv.subtypeEquivRight (fun j => by simp)
  exact ((sumsTo_comp_equiv' e (fun j : {j // decide (P j) = true} => x j.1)
    (fun j : {j // P j} => x j.1) (fun _ => rfl) _).2 (sumsTo_sum this)).summable

/-- Reindexing along an injection preserves summability. -/
theorem summable_comp_injective {J J' : Type} [Countable J] [Countable J'] {x : J → M}
    (hx : Summable x) (ψ : J' → J) (hψ : Function.Injective ψ) : Summable (x ∘ ψ) := by
  have h1 := summable_subfamily hx (· ∈ Set.range ψ)
  exact ((sumsTo_comp_equiv' (Equiv.ofInjective ψ hψ) (fun j : {j // j ∈ Set.range ψ} => x j.1)
    (x ∘ ψ) (fun _ => rfl) _).2 (sumsTo_sum h1)).summable

/-- Splitting a sum along a predicate. -/
theorem sumsTo_split {J : Type} [Countable J] (x : J → M) (P : J → Prop) (s : M) :
    SumsTo x s ↔ ∃ u v, SumsTo (fun j : {j // P j} => x j.1) u ∧
      SumsTo (fun j : {j // ¬ P j} => x j.1) v ∧ SumsTo ![u, v] s := by
  classical
  rw [← sumsTo_sum_iff, sumsTo_comp_equiv' (Equiv.sumCompl P) x _ (by rintro (j | j) <;> rfl)]

/-- Splitting off the last member of a family over `Fin (n+1)`. -/
theorem sumsTo_fin_last_iff {n : ℕ} (f : Fin (n + 1) → M) (s : M) :
    SumsTo f s ↔ ∃ u, SumsTo (fun i : Fin n => f i.castSucc) u ∧
      SumsTo ![u, f (Fin.last n)] s := by
  have hy : ∀ i, f i = Sum.elim (fun i : Fin n => f (Fin.castAdd 1 i))
      (fun j : Fin 1 => f (Fin.natAdd n j)) (finSumFinEquiv.symm i) := by
    intro i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    rcases j with j | j <;> simp
  rw [sumsTo_comp_equiv' finSumFinEquiv.symm _ _ hy, sumsTo_sum_iff]
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    have hv' : v = f (Fin.last n) := hv.unique (sumsTo_of_unique' _ 0)
    rw [hv'] at huv
    exact ⟨u, hu, huv⟩
  · rintro ⟨u, hu, huv⟩
    exact ⟨u, f (Fin.last n), hu, sumsTo_of_unique' (fun j : Fin 1 => f (Fin.natAdd n j)) 0,
      huv⟩

/-- `ℕ ≃ ℕ ⊕ 1`, splitting off `0`. -/
def natSuccEquiv : ℕ ≃ ℕ ⊕ PUnit.{1} where
  toFun n := match n with
    | 0 => Sum.inr PUnit.unit
    | n + 1 => Sum.inl n
  invFun p := match p with
    | Sum.inl n => n + 1
    | Sum.inr _ => 0
  left_inv n := by cases n <;> rfl
  right_inv p := by rcases p with n | ⟨⟩ <;> rfl

/-- Splitting off the first member of a family over `ℕ`. -/
theorem sumsTo_nat_succ_iff (x : ℕ → M) (s : M) :
    SumsTo x s ↔ ∃ u, SumsTo (fun n => x (n + 1)) u ∧ SumsTo ![u, x 0] s := by
  rw [sumsTo_comp_equiv' natSuccEquiv (Sum.elim (fun n => x (n + 1)) (fun _ => x 0)) x
    (by intro n; cases n <;> rfl), sumsTo_sum_iff]
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    have hv' : v = x 0 := hv.unique (sumsTo_of_unique' (fun _ : PUnit.{1} => x 0) PUnit.unit)
    rw [hv'] at huv
    exact ⟨u, hu, huv⟩
  · rintro ⟨u, hu, huv⟩
    exact ⟨u, x 0, hu, sumsTo_of_unique' _ PUnit.unit, huv⟩

/-- A family over `ℕ` is summable if all its initial segments are. -/
theorem summable_nat_of_fin (x : ℕ → M) (h : ∀ n, Summable (fun i : Fin n => x i)) :
    Summable x := by
  refine limit x fun F => ?_
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range F
  have := summable_comp_injective (h n) (fun j : F => (⟨j.1, Finset.mem_range.1 (hn j.2)⟩ :
    Fin n)) (fun a b hab => Subtype.ext (congrArg Fin.val hab))
  exact this

/-- `x` together with one more element `a` is summable if every finite part
of `x` sums to something summable with `a` (via the limit axiom). -/
theorem summable_sum_elim_of_finite {J : Type} [Countable J] (x : J → M) (a : M)
    (h : ∀ F : Finset J, ∃ t, SumsTo (fun j : F => x j.1) t ∧ Summable ![t, a]) :
    Summable (Sum.elim x (fun _ : Unit => a)) := by
  classical
  refine limit _ fun G => ?_
  let F : Finset J := G.preimage Sum.inl Sum.inl_injective.injOn
  obtain ⟨t, ht, hta⟩ := h F
  have hz : Summable (Sum.elim (fun j : F => x j.1) (fun _ : Unit => a)) :=
    ((sumsTo_sum_iff _ _ _).2 ⟨t, a, ht, sumsTo_of_unique' _ (), sumsTo_sum hta⟩).summable
  let ψ : G → F ⊕ Unit := fun p => match p with
    | ⟨Sum.inl j, hj⟩ => Sum.inl ⟨j, Finset.mem_preimage.2 hj⟩
    | ⟨Sum.inr _, _⟩ => Sum.inr ()
  have hψ : Function.Injective ψ := by
    rintro ⟨(j | ⟨⟩), hj⟩ ⟨(j' | ⟨⟩), hj'⟩ e <;> simp_all [ψ]
  have := summable_comp_injective hz ψ hψ
  refine (sumsTo_congr (y := fun p : G => Sum.elim x (fun _ : Unit => a) p.1) ?_).1
    (sumsTo_sum this) |>.summable
  rintro ⟨(j | ⟨⟩), hj⟩ <;> rfl

end SigmaPAM

open SigmaPAM

/-- **SIG 2** (main.tex:249, Definition): a map `f : M → N` of σ-PAMs is
**σ-additive** if for every summable countable family `(x_j)` the family
`(f x_j)` is summable and `f (⋁ x_j) = ⋁ f x_j`. -/
def IsSigmaAdditive {M : Type u} {N : Type v} [SigmaPAM M] [SigmaPAM N] (f : M → N) : Prop :=
  ∀ (J : Type) [Countable J] (x : J → M) (h : Summable x),
    ∃ h' : Summable (f ∘ x), f (sum x h) = sum (f ∘ x) h'

/-- **SIG 2** (main.tex:249, Definition): `g : M × N → L` is
**σ-biadditive** if it is σ-additive in each argument. -/
def IsSigmaBiadditive {M : Type u} {N : Type v} {L : Type w} [SigmaPAM M] [SigmaPAM N]
    [SigmaPAM L] (g : M → N → L) : Prop :=
  (∀ x, IsSigmaAdditive (g x)) ∧ ∀ y, IsSigmaAdditive (fun x => g x y)

theorem IsSigmaAdditive.sumsTo {M : Type u} {N : Type v} [SigmaPAM M] [SigmaPAM N]
    {f : M → N} (hf : IsSigmaAdditive f) {J : Type} [Countable J] {x : J → M} {s : M}
    (h : SumsTo x s) : SumsTo (fun j => f (x j)) (f s) := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨h', e⟩ := hf J x hx
  exact ⟨h', e.symm⟩

theorem isSigmaAdditive_of_sumsTo {M : Type u} {N : Type v} [SigmaPAM M] [SigmaPAM N]
    {f : M → N} (hf : ∀ {J : Type} [Countable J] (x : J → M) (s : M), SumsTo x s →
      SumsTo (fun j => f (x j)) (f s)) : IsSigmaAdditive f := by
  intro J _ x h
  obtain ⟨h', e⟩ := hf x _ (sumsTo_sum h)
  exact ⟨h', e.symm⟩

/-- A σ-additive map is additive for the induced PCMs. -/
theorem IsSigmaAdditive.isAdditive {M : Type u} {N : Type v} [SigmaPAM M] [SigmaPAM N]
    {f : M → N} (hf : IsSigmaAdditive f) : @IsAdditive M N toPCM toPCM f := by
  let _ : PCM M := toPCM
  let _ : PCM N := toPCM
  refine ⟨?_, ?_⟩
  · have := hf.sumsTo (sumsTo_of_isEmpty (Empty.elim : Empty → M))
    exact this.unique (sumsTo_of_isEmpty _)
  · intro a b h
    have := hf.sumsTo (sumsTo_sum h)
    have e : (fun j => f (![a, b] j)) = ![f a, f b] := by funext i; fin_cases i <;> rfl
    rw [e] at this
    exact ⟨this.summable, this.sum_eq _⟩

/-! ## SIG 3–5: enriched categories, partial projections, PACs -/

/-- The PCM structure on a hom-set enriched over σ-PAMs (the note after
SIG 2, applied to `C(X, Y)`). -/
noncomputable instance homPCM {C : Type u} [Category.{v} C]
    [∀ X Y : C, SigmaPAM (X ⟶ Y)] (X Y : C) : PCM (X ⟶ Y) :=
  SigmaPAM.toPCM

/-- **SIG 3** (main.tex:303, Definition): a category is **enriched over
PCMs** if each hom-set is a PCM and composition is biadditive. -/
class PCMEnriched (C : Type u) [Category.{v} C] [∀ X Y : C, PCM (X ⟶ Y)] : Prop where
  comp_biadditive : ∀ X Y Z : C, IsBiadditive (fun (g : Y ⟶ Z) (f : X ⟶ Y) => f ≫ g)

/-- **SIG 3** (main.tex:303, Definition): a category is **enriched over
σ-PAMs** if each hom-set is a σ-PAM and composition is σ-biadditive. -/
class SigmaPAMEnriched (C : Type u) [Category.{v} C] [∀ X Y : C, SigmaPAM (X ⟶ Y)] :
    Prop where
  comp_sigmaBiadditive :
    ∀ X Y Z : C, IsSigmaBiadditive (fun (g : Y ⟶ Z) (f : X ⟶ Y) => f ≫ g)

/-- **SIG 3** (main.tex:303, Definition): the tree's finPAC axioms
`comp_ovee`, `ovee_comp`, `comp_zero`, `zero_comp` (180VII) say exactly that
composition is biadditive. -/
theorem pcmEnriched_of_finPAC {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] : PCMEnriched C where
  comp_biadditive X Y Z := by
    refine ⟨fun g => ⟨FinPAC.zero_comp _, fun h => ?_⟩, fun f => ⟨FinPAC.comp_zero _, fun h => ?_⟩⟩
    · obtain ⟨h', e⟩ := FinPAC.comp_ovee h g
      exact ⟨h', e.symm⟩
    · obtain ⟨h', e⟩ := FinPAC.ovee_comp h f
      exact ⟨h', e.symm⟩

section PartialProjections

variable {C : Type u} [Category.{v} C] [∀ X Y : C, Zero (X ⟶ Y)]

open Classical in
/-- **SIG 4** (main.tex:314, Definition): the **partial projection**
`▷ᵢ : ∐_j A_j ⟶ Aᵢ` of a coproduct in a category with zero maps, with
`▷ᵢ ∘ κᵢ = id` and `▷ᵢ ∘ κ_k = 0` for `k ≠ i`.  The zero maps are a chosen
family `Zero (X ⟶ Y)` (in every use, the PCM zero). -/
noncomputable def pproj {J : Type w} (A : J → C) [HasCoproduct A] (i : J) : ∐ A ⟶ A i :=
  Sigma.desc fun k => if h : k = i then eqToHom (congrArg A h) else 0

theorem ι_pproj_self {J : Type w} (A : J → C) [HasCoproduct A] (i : J) :
    Sigma.ι A i ≫ pproj A i = 𝟙 (A i) := by
  simp [pproj]

theorem ι_pproj_ne {J : Type w} (A : J → C) [HasCoproduct A] {i k : J} (h : k ≠ i) :
    Sigma.ι A k ≫ pproj A i = 0 := by
  simp [pproj, h]

/-- **SIG 4** (main.tex:314, Definition): a family `(f_j : B ⟶ A_j)` is
**compatible** if some `f : B ⟶ ∐ A_j` has `▷_j ∘ f = f_j` for all `j`. -/
def Compatible {J : Type w} {A : J → C} [HasCoproduct A] {B : C} (f : ∀ j, B ⟶ A j) : Prop :=
  ∃ g : B ⟶ ∐ A, ∀ j, g ≫ pproj A j = f j

end PartialProjections

/-- **SIG 5** (`def:sigma-pac`, main.tex:331, Definition): a **finPAC**
(category with finite coproducts, enriched over PCMs, with the compatible-sum
and untying axioms) is the tree's `FinPAC` (180VII), whose compatible-sum
axiom is phrased with `b : X ⟶ Y + Y`; this is the printed form: compatible
pairs are summable. -/
theorem finPAC_compatible_sum {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] {A B : C} {f g : A ⟶ B}
    (h : ∃ b : A ⟶ B ⨿ B, b ≫ pproj₁ B B = f ∧ b ≫ pproj₂ B B = g) : Perp f g := by
  obtain ⟨b, rfl, rfl⟩ := h
  exact FinPAC.compatible_sum b

/-- **SIG 5** (`def:sigma-pac`, main.tex:331, Definition): a **σ-PAC** is a
category with countable coproducts, enriched over σ-PAMs, such that
*(compatible sum)* compatible countable families `(f_j : A ⟶ B)` are summable,
and *(untying)* if `f, g : A ⟶ B` are summable then so are
`κ₁ ∘ f, κ₂ ∘ g : A ⟶ B + B`. -/
class SigmaPAC (C : Type u) [Category.{v} C] [HasCountableCoproducts C]
    [∀ X Y : C, SigmaPAM (X ⟶ Y)] : Prop extends SigmaPAMEnriched C where
  compatible_sum : ∀ {J : Type} [Countable J] {A B : C} (f : J → (A ⟶ B)),
    Compatible (A := fun _ : J => B) f → Summable f
  untying : ∀ {A B : C} {f g : A ⟶ B}, Summable ![f, g] →
    Summable ![f ≫ (coprod.inl : B ⟶ B ⨿ B), g ≫ (coprod.inr : B ⟶ B ⨿ B)]

section SigmaPACBasics

variable {C : Type u} [Category.{v} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaPAC C]

theorem comp_sumsTo_left {X Y Z : C} (k : Y ⟶ Z) {J : Type} [Countable J]
    {f : J → (X ⟶ Y)} {s : X ⟶ Y} (h : SumsTo f s) : SumsTo (fun j => f j ≫ k) (s ≫ k) :=
  IsSigmaAdditive.sumsTo ((SigmaPAMEnriched.comp_sigmaBiadditive X Y Z).1 k) h

theorem comp_sumsTo_right {W X Y : C} (k : W ⟶ X) {J : Type} [Countable J]
    {f : J → (X ⟶ Y)} {s : X ⟶ Y} (h : SumsTo f s) : SumsTo (fun j => k ≫ f j) (k ≫ s) :=
  IsSigmaAdditive.sumsTo ((SigmaPAMEnriched.comp_sigmaBiadditive W X Y).2 k) h

/-- A σ-PAC is a finPAC for the induced PCMs. -/
instance finPAC_of_sigmaPAC : FinPAC C where
  comp_ovee {X Y Z f g} h k := by
    have := comp_sumsTo_left k (sumsTo_sum h)
    rw [sumsTo_congr (y := ![f ≫ k, g ≫ k]) (by intro i; fin_cases i <;> rfl)] at this
    exact ⟨this.summable, (this.sum_eq _).symm⟩
  ovee_comp {W X Y f g} h k := by
    have := comp_sumsTo_right k (sumsTo_sum h)
    rw [sumsTo_congr (y := ![k ≫ f, k ≫ g]) (by intro i; fin_cases i <;> rfl)] at this
    exact ⟨this.summable, (this.sum_eq _).symm⟩
  comp_zero {X Y Z} f := by
    have := comp_sumsTo_right f (sumsTo_of_isEmpty (Empty.elim : Empty → (Y ⟶ Z)))
    exact this.unique (sumsTo_of_isEmpty _)
  zero_comp {X Y Z} f := by
    have := comp_sumsTo_left f (sumsTo_of_isEmpty (Empty.elim : Empty → (X ⟶ Y)))
    exact this.unique (sumsTo_of_isEmpty _)
  compatible_sum {X Y} b := by
    let d := coprod.desc (Sigma.ι (fun _ : Fin 2 => Y) 0) (Sigma.ι (fun _ : Fin 2 => Y) 1)
    have h0 : d ≫ pproj (fun _ : Fin 2 => Y) 0 = pproj₁ Y Y := by
      refine coprod.hom_ext ?_ ?_
      · rw [coprod.inl_desc_assoc, ι_pproj_self]; exact (coprod.inl_desc _ _).symm
      · rw [coprod.inr_desc_assoc, ι_pproj_ne _ (by decide)]; exact (coprod.inr_desc _ _).symm
    have h1 : d ≫ pproj (fun _ : Fin 2 => Y) 1 = pproj₂ Y Y := by
      refine coprod.hom_ext ?_ ?_
      · rw [coprod.inl_desc_assoc, ι_pproj_ne _ (by decide)]; exact (coprod.inl_desc _ _).symm
      · rw [coprod.inr_desc_assoc, ι_pproj_self]; exact (coprod.inr_desc _ _).symm
    refine SigmaPAC.compatible_sum ![b ≫ pproj₁ Y Y, b ≫ pproj₂ Y Y] ⟨b ≫ d, ?_⟩
    intro j
    rw [Category.assoc]
    fin_cases j
    · exact congrArg (b ≫ ·) h0
    · exact congrArg (b ≫ ·) h1
  untying h := SigmaPAC.untying h

end SigmaPACBasics

/-! **SIG 6** (main.tex:355, Remark): fin/σ-PACs can be characterised as
categories with finite/countable coproducts, zero maps and further axioms
([Cho19, §3.8.1], [AM80, §5]).  A pointer to the literature, no declaration:
the countable characterisation the paper uses is SIG 65
(`lem:charact-sigma-effectus`). -/

/-! ## SIG 7–11: effect algebras -/

/-- **SIG 7** (`def:EA`, main.tex:360, Definition): an **effect algebra** is
a PCM with a top `1` such that each `a` has a unique `a^⊥` with
`a ⊕ a^⊥ = 1`, and `a ⊥ 1` implies `a = 0`: the tree's `EffectAlgebra`
(175I).  `EA` is the category of effect algebras and **additive** maps (not
the tree's `EACat`, whose maps are unital). -/
structure EASub : Type (u + 1) where
  carrier : Type u
  [str : EffectAlgebra carrier]

attribute [instance] EASub.str

instance : CoeSort EASub.{u} (Type u) := ⟨EASub.carrier⟩

/-- **SIG 7** (`def:EA`, main.tex:377, Definition): the category `EA` of
effect algebras and additive maps. -/
instance : Category EASub.{u} where
  Hom E F := { f : E → F // IsAdditive f }
  id E := ⟨id, rfl, fun h => ⟨h, rfl⟩⟩
  comp f g := ⟨g.1 ∘ f.1, by show g.1 (f.1 0) = 0; rw [f.2.1, g.2.1], fun {x y} h => by
    obtain ⟨h₁, e₁⟩ := f.2.2 h
    obtain ⟨h₂, e₂⟩ := g.2.2 h₁
    exact ⟨h₂, by
      show ovee (g.1 (f.1 x)) (g.1 (f.1 y)) h₂ = g.1 (f.1 (ovee x y h))
      rw [e₂, e₁]⟩⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- **SIG 7** (`def:EA`, main.tex:378): effect algebras are posets under
`a ≤ b` iff `a ⊕ c = b` for some `c` (the tree's `≼`, 175V). -/
theorem ea_le_partialOrder {E : Type u} [EffectAlgebra E] :
    (∀ a : E, a ≼ a) ∧ (∀ a b c : E, a ≼ b → b ≼ c → a ≼ c) ∧
      (∀ a b : E, a ≼ b → b ≼ a → a = b) :=
  ⟨pcm_preorder_refl, fun _ _ _ => pcm_preorder_trans, fun _ _ => eabasics_le_antisymm⟩

/-- **SIG 8** (`ex:Boolean-is-effect-algebra`, main.tex:381, Example): a
Boolean algebra is an effect algebra with `(·)^⊥` the complement, `a ⊥ b`
iff `a ∧ b = 0`, and then `a ⊕ b = a ∨ b` (the tree's
`booleanEffectAlgebra`, 175II.5). -/
theorem boolean_effectAlgebra (L : Type u) [BooleanAlgebra L] :
    letI := booleanEffectAlgebra L
    (∀ a b : L, Perp a b ↔ a ⊓ b = ⊥) ∧ (∀ (a b : L) (h : Perp a b), ovee a b h = a ⊔ b) ∧
      (∀ a : L, orth a = aᶜ) ∧ (1 : L) = ⊤ ∧ (0 : L) = ⊥ :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ => rfl, rfl, rfl⟩

/-- **SIG 9** (`ex:standard-effect-algebra`, main.tex:387, Example): the
effects `[0,1]_{B(H)} = {A | 0 ≤ A ≤ 1}` of a Hilbert space form an effect
algebra with `A ⊥ B` iff `A + B ≤ 1`, and then `A ⊕ B = A + B` (the tree's
`orderIntervalEffectAlgebra`, 175II.2, at the Loewner order of `B(H)`). -/
noncomputable def bhEffects (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : EffectAlgebra (Set.Icc (0 : H →L[ℂ] H) 1) :=
  orderIntervalEffectAlgebra (H →L[ℂ] H) 1 zero_le_one

theorem bhEffects_spec (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] :
    letI := bhEffects H
    (∀ A B : Set.Icc (0 : H →L[ℂ] H) 1, Perp A B ↔ (A : H →L[ℂ] H) + B ≤ 1) ∧
      ∀ (A B : Set.Icc (0 : H →L[ℂ] H) 1) (h : Perp A B),
        ((ovee A B h : Set.Icc (0 : H →L[ℂ] H) 1) : H →L[ℂ] H) = A + B :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => rfl⟩

/-- **SIG 10** (`partial-remark`, main.tex:396, Remark): the morphisms of `EA`
are only *subunital*: an additive map satisfies `f 1 ≤ 1` (and is monotone),
but need not satisfy `f 1 = 1`. -/
theorem additive_subunital {E F : Type u} [EffectAlgebra E] [EffectAlgebra F] (f : E → F)
    (hf : IsAdditive f) : f 1 ≼ 1 ∧ ∀ a b : E, a ≼ b → f a ≼ f b := by
  refine ⟨⟨orth (f 1), EffectAlgebra.perp_orth _, EffectAlgebra.ovee_orth _⟩, ?_⟩
  rintro a b ⟨c, h, rfl⟩
  obtain ⟨h', e⟩ := hf.2 h
  exact ⟨f c, h', e⟩

theorem additive_not_unital :
    ∃ f : Bool → Bool, IsAdditive f ∧ f 1 ≠ 1 :=
  ⟨fun _ => false, ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩, by decide⟩

/-! **SIG 11** (main.tex:413, Remark): the category of effect algebras with
unital maps is isomorphic to the Eilenberg–Moore category of the
free–forgetful adjunction between orthomodular posets and bounded posets
([Harding 2004], [Jenča 2015]).  A cited result, not formalised (see
`PLAN.md`): no declaration. -/

end Papers.SIG
