/-
Papers/OAP/Yosida.lean

A. Westerbaan, B. Westerbaan, J. van de Wetering, *A characterisation of
ordered abstract probabilities* (LICS 2020, arXiv:1912.10040), source
`../papers/1912.10040/first.tex`, §8: **OAP 64**, Yosida's representation
theorem.

The paper cites the theorem (Yosida 1941, cf. B. Westerbaan, *Yosida duality*,
arXiv:1612.03327) without proof, and it is not in Mathlib.  The proof here
follows *Yosida duality* (§§1–6), with two economies:

* the maximal Riesz ideal `M` is never quotiented: the functional
  `V → ℝ` it induces is read off directly as the "cut"
  `φ(x) = inf {r | x ≤ r·1 modulo M}` (`IsVal`), using that `V/M` is totally
  ordered (`posPart_mem_or_negPart_mem`, the paper's `2 ⇒ 3`, via the
  perp ideal of `x⁺`), and that `1 ∉ M`;
* density of the image uses Mathlib's lattice Stone–Weierstrass
  (`ContinuousMap.sublattice_closure_eq_top`) in place of the paper's
  Theorem (Stone–Weierstrass).

Conventions: an order unit space is the tree's `Theses.B.Eff.OrderUnitSpace`
(on top of `[Lattice V]` here), Archimedean is the tree's `OUSArchimedean`,
and norm-completeness in the order-unit norm is `OUSNormComplete` below
(sequential, stated with the order so that it needs no norm instance).
-/
import Theses.B.Eff.OrderUnit

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

namespace Papers.OAP

open Theses.B.Eff

universe u

noncomputable section

/-! ## Norm-completeness in the order-unit norm -/

/-- An order unit space is **norm-complete** (in its order-unit norm
`‖x‖ = inf {r | -r·1 ≤ x ≤ r·1}`) when every Cauchy sequence converges.
Stated with the order directly: `‖x‖ ≤ ε` is (for an Archimedean space)
`-ε·1 ≤ x ≤ ε·1`, and the Cauchy condition is symmetric in `m, n`. -/
def OUSNormComplete (V : Type u) [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [OrderUnitSpace V] : Prop :=
  ∀ s : ℕ → V, (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, s m - s n ≤ ε • ouUnit V) →
    ∃ v : V, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      s n - v ≤ ε • ouUnit V ∧ v - s n ≤ ε • ouUnit V

section Riesz

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Lattice V] [OrderUnitSpace V]

/-! ## Elementary Riesz-space facts -/

omit [OrderUnitSpace V] in
private theorem abs_def' (x : V) : |x| = x ⊔ -x := rfl

/-- Multiplication by a non-negative scalar preserves binary suprema. -/
theorem yos_smul_sup {c : ℝ} (hc : 0 ≤ c) (a b : V) : c • (a ⊔ b) = c • a ⊔ c • b := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  apply le_antisymm
  · have h1 : a ⊔ b ≤ c⁻¹ • (c • a ⊔ c • b) := by
      apply sup_le
      · have := ou_smul_le_smul (inv_nonneg.2 hc.le) (le_sup_left : c • a ≤ c • a ⊔ c • b)
        rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
      · have := ou_smul_le_smul (inv_nonneg.2 hc.le) (le_sup_right : c • b ≤ c • a ⊔ c • b)
        rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
    have := ou_smul_le_smul hc.le h1
    rwa [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at this
  · exact sup_le (ou_smul_le_smul hc.le le_sup_left) (ou_smul_le_smul hc.le le_sup_right)

theorem yos_posPart_smul {c : ℝ} (hc : 0 ≤ c) (x : V) : (c • x)⁺ = c • x⁺ := by
  rw [posPart_def, posPart_def, yos_smul_sup hc, smul_zero]

theorem yos_abs_smul (c : ℝ) (x : V) : |c • x| = |c| • |x| := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc, abs_def', abs_def', yos_smul_sup hc, smul_neg]
  · have : c • x = (-c) • (-x) := by rw [neg_smul, smul_neg, neg_neg]
    rw [this, abs_of_nonpos hc, abs_def', abs_def', yos_smul_sup (neg_nonneg.2 hc), smul_neg,
      neg_neg, sup_comm]

omit [OrderUnitSpace V] in
theorem yos_posPart_add_le [IsOrderedAddMonoid V] (a b : V) : (a + b)⁺ ≤ a⁺ + b⁺ :=
  sup_le (add_le_add (le_posPart a) (le_posPart b))
    (add_nonneg (posPart_nonneg a) (posPart_nonneg b))

omit [OrderUnitSpace V] in
theorem yos_posPart_sup_le [IsOrderedAddMonoid V] (a b : V) : (a ⊔ b)⁺ ≤ a⁺ + b⁺ := by
  refine sup_le (sup_le ?_ ?_) (add_nonneg (posPart_nonneg a) (posPart_nonneg b))
  · exact (le_posPart a).trans (le_add_of_nonneg_right (posPart_nonneg b))
  · exact (le_posPart b).trans (le_add_of_nonneg_left (posPart_nonneg a))

omit [OrderUnitSpace V] in
theorem yos_posPart_le_abs [IsOrderedAddMonoid V] (x : V) : x⁺ ≤ |x| :=
  sup_le (le_abs_self x) (abs_nonneg x)

omit [OrderUnitSpace V] in
/-- The Riesz inequality `(a + b) ∧ c ≤ a ∧ c + b ∧ c` for positive `a, b, c`. -/
theorem yos_add_inf_le [IsOrderedAddMonoid V] {a b c : V} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) : (a + b) ⊓ c ≤ a ⊓ c + b ⊓ c := by
  rw [add_inf, inf_add, inf_add]
  refine le_inf (le_inf ?_ ?_) (le_inf ?_ ?_)
  · exact inf_le_left
  · exact inf_le_right.trans (le_add_of_nonneg_right hb)
  · exact inf_le_right.trans (le_add_of_nonneg_left ha)
  · exact inf_le_right.trans (le_add_of_nonneg_left hc)

omit [OrderUnitSpace V] in
theorem yos_nsmul_inf_le [IsOrderedAddMonoid V] {a c : V} (ha : 0 ≤ a) (hc : 0 ≤ c) (n : ℕ) :
    (n • a) ⊓ c ≤ n • (a ⊓ c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    exact (yos_add_inf_le (nsmul_nonneg ha n) ha hc).trans (add_le_add_left ih _)

/-! ## Riesz ideals -/

/-- A **Riesz ideal**: a set containing `0`, closed under addition, and solid
(`|x| ≤ |a|`, `a ∈ I` ⇒ `x ∈ I`).  Closure under real scalars follows
(`IsRieszIdeal.smul_mem`), so this is the paper's Lemma 5 point 2. -/
def IsRieszIdeal (I : Set V) : Prop :=
  (0 : V) ∈ I ∧ (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) ∧ ∀ a ∈ I, ∀ x : V, |x| ≤ |a| → x ∈ I

namespace IsRieszIdeal

variable {I : Set V} (hI : IsRieszIdeal I)
include hI

theorem zero_mem : (0 : V) ∈ I := hI.1
theorem add_mem {x y : V} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := hI.2.1 x hx y hy
theorem of_abs_le {a x : V} (ha : a ∈ I) (h : |x| ≤ |a|) : x ∈ I := hI.2.2 a ha x h

theorem neg_mem {x : V} (hx : x ∈ I) : -x ∈ I := hI.of_abs_le hx (by rw [abs_neg])

theorem sub_mem {x y : V} (hx : x ∈ I) (hy : y ∈ I) : x - y ∈ I := by
  rw [sub_eq_add_neg]; exact hI.add_mem hx (hI.neg_mem hy)

theorem abs_mem {x : V} (hx : x ∈ I) : |x| ∈ I := hI.of_abs_le hx (by rw [abs_abs])

theorem of_nonneg_le {a x : V} (ha : a ∈ I) (h0 : 0 ≤ x) (h : x ≤ a) : x ∈ I :=
  hI.of_abs_le ha (by rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans h)]; exact h)

theorem nsmul_mem {x : V} (hx : x ∈ I) (n : ℕ) : n • x ∈ I := by
  induction n with
  | zero => simpa using hI.zero_mem
  | succ n ih => rw [succ_nsmul]; exact hI.add_mem ih hx

theorem smul_mem {x : V} (hx : x ∈ I) (c : ℝ) : c • x ∈ I := by
  obtain ⟨n, hn⟩ := exists_nat_ge |c|
  have h1 : n • |x| ∈ I := hI.nsmul_mem (hI.abs_mem hx) n
  refine hI.of_abs_le h1 ?_
  rw [yos_abs_smul, abs_of_nonneg (nsmul_nonneg (abs_nonneg x) n), ← Nat.cast_smul_eq_nsmul ℝ]
  have := ou_smul_nonneg (sub_nonneg.2 hn) (abs_nonneg x)
  rw [sub_smul] at this
  exact sub_nonneg.1 this

theorem posPart_mem {x : V} (hx : x ∈ I) : x⁺ ∈ I :=
  hI.of_nonneg_le (hI.abs_mem hx) (posPart_nonneg x) (yos_posPart_le_abs x)

end IsRieszIdeal

omit [OrderUnitSpace V] in
theorem isRieszIdeal_zero [IsOrderedAddMonoid V] : IsRieszIdeal ({0} : Set V) := by
  refine ⟨rfl, fun x hx y hy => by simp_all, fun a ha x hx => ?_⟩
  rw [Set.mem_singleton_iff] at ha ⊢
  rw [ha, abs_zero] at hx
  exact le_antisymm ((le_abs_self x).trans hx) (neg_nonpos.1 ((neg_le_abs x).trans hx))

/-- The "perp" ideal `{y | |y| ∧ a ∈ M}` of a positive `a` over an ideal `M`
(the preimage of `q(a)^⊥` under `q : V → V/M`; *Yosida duality*, Lemma 6). -/
def perpSet (M : Set V) (a : V) : Set V := {y | |y| ⊓ a ∈ M}

theorem isRieszIdeal_perpSet {M : Set V} (hM : IsRieszIdeal M) {a : V} (ha : 0 ≤ a) :
    IsRieszIdeal (perpSet M a) := by
  refine ⟨?_, fun x hx y hy => ?_, fun b hb x hx => ?_⟩
  · show |(0 : V)| ⊓ a ∈ M
    rw [abs_zero, inf_eq_left.2 ha]; exact hM.zero_mem
  · show |x + y| ⊓ a ∈ M
    refine hM.of_nonneg_le (hM.add_mem hx hy) (le_inf (abs_nonneg _) ha) ?_
    exact (inf_le_inf_right a (abs_add_le x y)).trans
      (yos_add_inf_le (abs_nonneg x) (abs_nonneg y) ha)
  · show |x| ⊓ a ∈ M
    exact hM.of_nonneg_le hb (le_inf (abs_nonneg _) ha)
      (inf_le_inf_right a hx)

theorem subset_perpSet {M : Set V} (hM : IsRieszIdeal M) {a : V} (ha : 0 ≤ a) :
    M ⊆ perpSet M a := fun _ hm =>
  hM.of_nonneg_le (hM.abs_mem hm) (le_inf (abs_nonneg _) ha) inf_le_left

/-! ## Maximal ideals: totality of the quotient -/

/-- In a maximal Riesz ideal not containing the unit, `V/M` is totally
ordered: for each `x`, `x⁺ ∈ M` or `x⁻ ∈ M` (*Yosida duality*, Prop. 7,
`2 ⇒ 3`, via the perp ideal of `x⁺`). -/
theorem posPart_mem_or_negPart_mem {M : Set V} (hM : IsRieszIdeal M)
    (hmax : ∀ N, IsRieszIdeal N → ouUnit V ∉ N → M ⊆ N → N ⊆ M) (x : V) :
    x⁺ ∈ M ∨ x⁻ ∈ M := by
  by_cases hu : ouUnit V ∈ perpSet M x⁺
  · left
    have hu' : ouUnit V ⊓ x⁺ ∈ M := by
      have : |ouUnit V| ⊓ x⁺ ∈ M := hu
      rwa [abs_of_nonneg ou_unit_nonneg] at this
    obtain ⟨n, hn⟩ := ou_exists_le_smul_unit (x⁺)
    rw [Nat.cast_smul_eq_nsmul] at hn
    refine hM.of_nonneg_le (hM.nsmul_mem hu' n) (posPart_nonneg x) ?_
    have := yos_nsmul_inf_le (ou_unit_nonneg (X := V)) (posPart_nonneg x) n
    rwa [inf_eq_right.2 hn] at this
  · right
    refine hmax _ (isRieszIdeal_perpSet hM (posPart_nonneg x)) hu
      (subset_perpSet hM (posPart_nonneg x)) ?_
    show |x⁻| ⊓ x⁺ ∈ M
    rw [abs_of_nonneg (negPart_nonneg x), inf_comm, posPart_inf_negPart_eq_zero]
    exact hM.zero_mem

/-! ## The functional induced by a maximal ideal -/

/-- `x ≤ y` modulo `M`. -/
def LeMod (M : Set V) (x y : V) : Prop := (x - y)⁺ ∈ M

section LeMod

variable {M : Set V} (hM : IsRieszIdeal M)
include hM

theorem leMod_of_le {x y : V} (h : x ≤ y) : LeMod M x y := by
  unfold LeMod; rw [posPart_eq_zero.2 (sub_nonpos.2 h)]; exact hM.zero_mem

theorem leMod_trans {x y z : V} (h1 : LeMod M x y) (h2 : LeMod M y z) : LeMod M x z := by
  unfold LeMod at *
  refine hM.of_nonneg_le (hM.add_mem h1 h2) (posPart_nonneg _) ?_
  have : x - z = (x - y) + (y - z) := by abel
  rw [this]; exact yos_posPart_add_le _ _

theorem leMod_add {x y x' y' : V} (h1 : LeMod M x y) (h2 : LeMod M x' y') :
    LeMod M (x + x') (y + y') := by
  unfold LeMod at *
  refine hM.of_nonneg_le (hM.add_mem h1 h2) (posPart_nonneg _) ?_
  have : x + x' - (y + y') = (x - y) + (x' - y') := by abel
  rw [this]; exact yos_posPart_add_le _ _

theorem leMod_smul {c : ℝ} (hc : 0 ≤ c) {x y : V} (h : LeMod M x y) :
    LeMod M (c • x) (c • y) := by
  unfold LeMod at *
  rw [← smul_sub, yos_posPart_smul hc]; exact hM.smul_mem h c

theorem leMod_neg {x y : V} (h : LeMod M x y) : LeMod M (-y) (-x) := by
  unfold LeMod at *
  have : -y - -x = x - y := by abel
  rwa [this]

theorem leMod_of_mem_left {m : V} (hm : m ∈ M) : LeMod M m 0 := by
  unfold LeMod; rw [sub_zero]; exact hM.posPart_mem hm

theorem leMod_of_mem_right {m : V} (hm : m ∈ M) : LeMod M 0 m := by
  unfold LeMod; rw [zero_sub]; exact hM.posPart_mem (hM.neg_mem hm)

theorem not_leMod_unit (hu : ouUnit V ∉ M) {r s : ℝ} (h : r < s) :
    ¬ LeMod M (s • ouUnit V) (r • ouUnit V) := by
  intro hle
  unfold LeMod at hle
  rw [← sub_smul, posPart_eq_self.2 (ou_smul_unit_nonneg (sub_nonneg.2 h.le))] at hle
  apply hu
  have := hM.smul_mem hle (s - r)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 h.ne'), one_smul] at this

end LeMod

/-- `c` is the value at `x` of the functional induced by `M`: `x` lies
below `r·1` modulo `M` for every `r > c`, and above it for every `r < c`. -/
def IsVal (M : Set V) (x : V) (c : ℝ) : Prop :=
  (∀ r, c < r → LeMod M x (r • ouUnit V)) ∧ (∀ r, r < c → LeMod M (r • ouUnit V) x)

section IsVal

variable {M : Set V} (hM : IsRieszIdeal M) (hu : ouUnit V ∉ M)
include hM hu

theorem IsVal.not_lt {x : V} {c d : ℝ} (hc : IsVal M x c) (hd : IsVal M x d) : ¬ c < d := by
  intro h
  have h1 : c < c + (d - c) / 3 := by linarith
  have h2 : d - (d - c) / 3 < d := by linarith
  have h3 : c + (d - c) / 3 < d - (d - c) / 3 := by linarith
  exact not_leMod_unit hM hu h3 (leMod_trans hM (hd.2 _ h2) (hc.1 _ h1))

theorem IsVal.unique {x : V} {c d : ℝ} (hc : IsVal M x c) (hd : IsVal M x d) : c = d :=
  le_antisymm (_root_.not_lt.1 (IsVal.not_lt hM hu hd hc))
    (_root_.not_lt.1 (IsVal.not_lt hM hu hc hd))

theorem exists_isVal (htot : ∀ x : V, x⁺ ∈ M ∨ x⁻ ∈ M) (x : V) : ∃ c, IsVal M x c := by
  set S : Set ℝ := {r | LeMod M x (r • ouUnit V)} with hS
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit x
  obtain ⟨m, hm⟩ := ou_exists_le_smul_unit (-x)
  have hne : S.Nonempty := ⟨n, leMod_of_le hM hn⟩
  have hlow : (-(m : ℝ)) • ouUnit V ≤ x := by
    rw [neg_smul]; exact neg_le.1 hm
  have hbdd : BddBelow S := by
    refine ⟨-(m : ℝ), fun r hr => ?_⟩
    by_contra hlt
    exact not_leMod_unit hM hu (not_le.1 hlt) (leMod_trans hM (leMod_of_le hM hlow) hr)
  refine ⟨sInf S, fun r hr => ?_, fun r hr => ?_⟩
  · obtain ⟨s, hs, hsr⟩ := exists_lt_of_csInf_lt hne hr
    exact leMod_trans hM hs (leMod_of_le hM (ou_smul_unit_mono hsr.le))
  · have hnot : r ∉ S := fun h => absurd (csInf_le hbdd h) (not_le.2 hr)
    rcases htot (x - r • ouUnit V) with h | h
    · exact absurd h hnot
    · show (r • ouUnit V - x)⁺ ∈ M
      rwa [← neg_sub, posPart_neg]

theorem IsVal.add {x y : V} {a b : ℝ} (hx : IsVal M x a) (hy : IsVal M y b) :
    IsVal M (x + y) (a + b) := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · have e : r • ouUnit V = (a + (r - a - b) / 2) • ouUnit V + (b + (r - a - b) / 2) • ouUnit V := by
      rw [← add_smul]; congr 1; ring
    rw [e]
    exact leMod_add hM (hx.1 _ (by linarith)) (hy.1 _ (by linarith))
  · have e : r • ouUnit V = (a - (a + b - r) / 2) • ouUnit V + (b - (a + b - r) / 2) • ouUnit V := by
      rw [← add_smul]; congr 1; ring
    rw [e]
    exact leMod_add hM (hx.2 _ (by linarith)) (hy.2 _ (by linarith))

theorem IsVal.neg {x : V} {a : ℝ} (hx : IsVal M x a) : IsVal M (-x) (-a) := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · have := leMod_neg hM (hx.2 (-r) (by linarith))
    rwa [neg_smul, neg_neg] at this
  · have := leMod_neg hM (hx.1 (-r) (by linarith))
    rwa [neg_smul, neg_neg] at this

theorem IsVal.smul_pos {x : V} {a : ℝ} (hx : IsVal M x a) {c : ℝ} (hc : 0 < c) :
    IsVal M (c • x) (c * a) := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · have := leMod_smul hM hc.le (hx.1 (r / c) (by rw [lt_div_iff₀ hc]; linarith))
    rwa [smul_smul, mul_div_cancel₀ _ hc.ne'] at this
  · have := leMod_smul hM hc.le (hx.2 (r / c) (by rw [div_lt_iff₀ hc]; linarith))
    rwa [smul_smul, mul_div_cancel₀ _ hc.ne'] at this

theorem isVal_zero : IsVal M (0 : V) 0 :=
  ⟨fun _ hr => leMod_of_le hM (ou_smul_unit_nonneg hr.le),
    fun r hr => leMod_of_le hM (by
      have := ou_smul_unit_mono (X := V) hr.le; rwa [zero_smul] at this)⟩

theorem IsVal.smul {x : V} {a : ℝ} (hx : IsVal M x a) (c : ℝ) : IsVal M (c • x) (c * a) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have := (hx.neg hM hu).smul_pos hM hu (neg_pos.2 hc)
    rwa [neg_smul, smul_neg, neg_neg, neg_mul_neg] at this
  · rw [zero_smul, zero_mul]; exact isVal_zero hM hu
  · exact hx.smul_pos hM hu hc

theorem IsVal.sup {x y : V} {a b : ℝ} (hx : IsVal M x a) (hy : IsVal M y b) :
    IsVal M (x ⊔ y) (max a b) := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · have h1 := hx.1 r (lt_of_le_of_lt (le_max_left a b) hr)
    have h2 := hy.1 r (lt_of_le_of_lt (le_max_right a b) hr)
    unfold LeMod at *
    rw [sup_sub]
    exact hM.of_nonneg_le (hM.add_mem h1 h2) (posPart_nonneg _) (yos_posPart_sup_le _ _)
  · rcases lt_max_iff.1 hr with h | h
    · exact leMod_trans hM (hx.2 r h) (leMod_of_le hM le_sup_left)
    · exact leMod_trans hM (hy.2 r h) (leMod_of_le hM le_sup_right)

theorem isVal_unit : IsVal M (ouUnit V) 1 := by
  refine ⟨fun r hr => leMod_of_le hM ?_, fun r hr => leMod_of_le hM ?_⟩
  · have := ou_smul_unit_mono (X := V) hr.le; rwa [one_smul] at this
  · have := ou_smul_unit_mono (X := V) hr.le; rwa [one_smul] at this

theorem isVal_of_mem {m : V} (hm : m ∈ M) : IsVal M m 0 :=
  ⟨fun _ hr => leMod_trans hM (leMod_of_mem_left hM hm) (leMod_of_le hM (ou_smul_unit_nonneg hr.le)),
    fun r hr => leMod_trans hM (leMod_of_le hM (by
      have := ou_smul_unit_mono (X := V) hr.le; rwa [zero_smul] at this))
      (leMod_of_mem_right hM hm)⟩

end IsVal

/-! ## The Yosida spectrum -/

variable (V) in
/-- The **Yosida spectrum** of `V`: the real-valued unital linear functionals
on `V` preserving binary suprema, as a subset of `ℝ^V` (so with the
pointwise topology, OAP 64). -/
def yosidaSpectrum : Set (V → ℝ) :=
  {φ | (∀ x y, φ (x + y) = φ x + φ y) ∧ (∀ (c : ℝ) x, φ (c • x) = c * φ x) ∧
    (∀ x y, φ (x ⊔ y) = max (φ x) (φ y)) ∧ φ (ouUnit V) = 1}

variable (V) in
/-- The Yosida spectrum as a topological space (subspace of `ℝ^V`). -/
abbrev YosidaSpectrum : Type u := yosidaSpectrum V

namespace YosidaSpectrum

variable (φ : YosidaSpectrum V)

theorem map_add (x y : V) : φ.1 (x + y) = φ.1 x + φ.1 y := φ.2.1 x y
theorem map_smul (c : ℝ) (x : V) : φ.1 (c • x) = c * φ.1 x := φ.2.2.1 c x
theorem map_sup (x y : V) : φ.1 (x ⊔ y) = max (φ.1 x) (φ.1 y) := φ.2.2.2.1 x y
theorem map_unit : φ.1 (ouUnit V) = 1 := φ.2.2.2.2

theorem map_neg (x : V) : φ.1 (-x) = -φ.1 x := by
  rw [← neg_one_smul ℝ x, φ.map_smul]; ring

theorem map_sub (x y : V) : φ.1 (x - y) = φ.1 x - φ.1 y := by
  rw [sub_eq_add_neg, φ.map_add, φ.map_neg]; ring

theorem map_inf (x y : V) : φ.1 (x ⊓ y) = min (φ.1 x) (φ.1 y) := by
  have : x ⊓ y = -((-x) ⊔ (-y)) := by rw [neg_sup, neg_neg, neg_neg]
  rw [this, φ.map_neg, φ.map_sup, φ.map_neg, φ.map_neg, max_neg_neg, neg_neg]

theorem mono {x y : V} (h : x ≤ y) : φ.1 x ≤ φ.1 y := by
  have := φ.map_sup x y
  rw [sup_eq_right.2 h] at this
  rw [this]; exact le_max_left _ _

theorem map_smul_unit (c : ℝ) : φ.1 (c • ouUnit V) = c := by
  rw [φ.map_smul, φ.map_unit, mul_one]

end YosidaSpectrum

/-- A bound for `|φ x|` uniform over the spectrum. -/
private def specBound (x : V) : ℝ := ((Classical.choose (ou_exists_le_smul_unit |x|) : ℕ) : ℝ)

private theorem abs_le_specBound (φ : YosidaSpectrum V) (x : V) : |φ.1 x| ≤ specBound x := by
  have h : |x| ≤ specBound x • ouUnit V := Classical.choose_spec (ou_exists_le_smul_unit |x|)
  rw [abs_le]
  constructor
  · have h1 : -x ≤ (specBound x) • ouUnit V := (neg_le_abs x).trans h
    have := φ.mono h1
    rw [φ.map_neg, φ.map_smul_unit] at this
    linarith
  · have := φ.mono ((le_abs_self x).trans h)
    rwa [φ.map_smul_unit] at this

theorem isClosed_yosidaSpectrum : IsClosed (yosidaSpectrum V) := by
  have h1 : IsClosed {φ : V → ℝ | ∀ x y, φ (x + y) = φ x + φ y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply _) ((continuous_apply x).add (continuous_apply y))
  have h2 : IsClosed {φ : V → ℝ | ∀ (c : ℝ) x, φ (c • x) = c * φ x} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun c => isClosed_iInter fun x =>
      isClosed_eq (continuous_apply _) (continuous_const.mul (continuous_apply _))
  have h3 : IsClosed {φ : V → ℝ | ∀ x y, φ (x ⊔ y) = max (φ x) (φ y)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply _) ((continuous_apply x).max (continuous_apply y))
  have h4 : IsClosed {φ : V → ℝ | φ (ouUnit V) = 1} :=
    isClosed_eq (continuous_apply _) continuous_const
  exact h1.inter (h2.inter (h3.inter h4))

theorem isCompact_yosidaSpectrum : IsCompact (yosidaSpectrum V) := by
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun x : V => isCompact_Icc (a := -specBound x) (b := specBound x))
    isClosed_yosidaSpectrum ?_
  intro φ hφ
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left]
  intro x
  exact abs_le.1 (abs_le_specBound ⟨φ, hφ⟩ x)

instance : CompactSpace (YosidaSpectrum V) :=
  isCompact_iff_compactSpace.1 isCompact_yosidaSpectrum

example : T2Space (YosidaSpectrum V) := inferInstance

/-! ## Separation by the spectrum -/

/-- **Separation** (*Yosida duality*, Prop. 8): in an Archimedean
lattice-ordered order unit space, every `v ≰ 0` is sent to a positive
number by some point of the spectrum.  Proof: pick `ε > 0` with `v ≰ ε·1`,
put `w = (v - ε·1)⁺ ≠ 0`, extend the ideal `w^⊥` (which misses `1`) by
Zorn to a maximal ideal `M` missing `1`, and read off the functional
induced by `M`; it vanishes on `(v - ε·1)⁻ ∈ w^⊥ ⊆ M`, so its value at `v`
is at least `ε`. -/
theorem exists_spectrum_pos (hA : OUSArchimedean V) {v : V} (hv : ¬ v ≤ 0) :
    ∃ φ : YosidaSpectrum V, 0 < φ.1 v := by
  obtain ⟨ε, hε, hvε⟩ : ∃ ε : ℝ, 0 < ε ∧ ¬ v ≤ ε • ouUnit V := by
    by_contra h
    push Not at h
    exact hv (hA v h)
  set y := v - ε • ouUnit V with hy
  set w := y⁺ with hw
  have hw0 : w ≠ 0 := fun h => hvε (sub_nonpos.1 (posPart_eq_zero.1 h))
  set J := perpSet ({0} : Set V) w with hJ
  have hJI : IsRieszIdeal J := isRieszIdeal_perpSet isRieszIdeal_zero (posPart_nonneg y)
  have huJ : ouUnit V ∉ J := by
    intro h
    have h' : ouUnit V ⊓ w = 0 := by
      have : |ouUnit V| ⊓ w ∈ ({0} : Set V) := h
      rwa [abs_of_nonneg ou_unit_nonneg, Set.mem_singleton_iff] at this
    obtain ⟨n, hn⟩ := ou_exists_le_smul_unit w
    rw [Nat.cast_smul_eq_nsmul] at hn
    have := yos_nsmul_inf_le (ou_unit_nonneg (X := V)) (posPart_nonneg y) n
    rw [inf_eq_right.2 hn, h', nsmul_zero] at this
    exact hw0 (le_antisymm this (posPart_nonneg y))
  -- Zorn
  set S : Set (Set V) := {I | IsRieszIdeal I ∧ ouUnit V ∉ I} with hS
  obtain ⟨M, hJM, hMmax⟩ := zorn_subset_nonempty S (fun c hcS hchain hne => by
    refine ⟨⋃₀ c, ⟨⟨?_, ?_, ?_⟩, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · obtain ⟨I, hI⟩ := hne
      exact Set.mem_sUnion.2 ⟨I, hI, (hcS hI).1.zero_mem⟩
    · rintro x ⟨I, hI, hxI⟩ y ⟨K, hK, hyK⟩
      rcases hchain.total hI hK with h | h
      · exact ⟨K, hK, (hcS hK).1.add_mem (h hxI) hyK⟩
      · exact ⟨I, hI, (hcS hI).1.add_mem hxI (h hyK)⟩
    · rintro a ⟨I, hI, haI⟩ x hx
      exact ⟨I, hI, (hcS hI).1.of_abs_le haI hx⟩
    · rintro ⟨I, hI, huI⟩
      exact (hcS hI).2 huI) J ⟨hJI, huJ⟩
  have hM : IsRieszIdeal M := hMmax.prop.1
  have huM : ouUnit V ∉ M := hMmax.prop.2
  have htot : ∀ x : V, x⁺ ∈ M ∨ x⁻ ∈ M :=
    posPart_mem_or_negPart_mem hM (fun N hN huN hMN => hMmax.2 ⟨hN, huN⟩ hMN)
  choose val hval using exists_isVal hM huM htot
  have hval_eq : ∀ {x c}, IsVal M x c → val x = c := fun h => (hval _).unique hM huM h
  refine ⟨⟨val, fun x y => hval_eq ((hval x).add hM huM (hval y)),
    fun c x => hval_eq ((hval x).smul hM huM c),
    fun x y => hval_eq ((hval x).sup hM huM (hval y)),
    hval_eq (isVal_unit hM huM)⟩, ?_⟩
  show 0 < val v
  -- `y⁻ ∈ J ⊆ M`, i.e. `ε·1 ≤ v` modulo `M`
  have hyneg : y⁻ ∈ M := hJM (by
    show |y⁻| ⊓ w ∈ ({0} : Set V)
    rw [abs_of_nonneg (negPart_nonneg y), inf_comm, posPart_inf_negPart_eq_zero]; rfl)
  have hle : LeMod M (ε • ouUnit V) v := by
    unfold LeMod
    rw [← neg_sub, posPart_neg]; exact hyneg
  by_contra hlt
  push Not at hlt
  have hlt' : val v < ε := hlt.trans_lt hε
  exact not_leMod_unit hM huM (show (val v + ε) / 2 < ε by linarith)
    (leMod_trans hM hle ((hval v).1 _ (by linarith)))

/-! ## The representation -/

variable (V) in
/-- The Yosida representation `ϑ : V → C(Φ)`, `ϑ(v)(φ) = φ(v)`. -/
def yosidaMap : V →ₗ[ℝ] C(YosidaSpectrum V, ℝ) where
  toFun v := ⟨fun φ => φ.1 v, (continuous_apply v).comp continuous_subtype_val⟩
  map_add' x y := by ext φ; exact φ.map_add x y
  map_smul' c x := by ext φ; exact φ.map_smul c x

@[simp] theorem yosidaMap_apply (v : V) (φ : YosidaSpectrum V) : yosidaMap V v φ = φ.1 v := rfl

theorem yosidaMap_unit : yosidaMap V (ouUnit V) = 1 := by
  ext φ; exact φ.map_unit

theorem yosidaMap_smul_unit (c : ℝ) : yosidaMap V (c • ouUnit V) = ContinuousMap.const _ c := by
  ext φ; exact φ.map_smul_unit c

theorem yosidaMap_sup (x y : V) : yosidaMap V (x ⊔ y) = yosidaMap V x ⊔ yosidaMap V y := by
  ext φ; exact φ.map_sup x y

theorem yosidaMap_inf (x y : V) : yosidaMap V (x ⊓ y) = yosidaMap V x ⊓ yosidaMap V y := by
  ext φ; exact φ.map_inf x y

theorem yosidaMap_mono {x y : V} (h : x ≤ y) : yosidaMap V x ≤ yosidaMap V y :=
  fun φ => φ.mono h

theorem yosidaMap_le_iff (hA : OUSArchimedean V) {x y : V} :
    yosidaMap V x ≤ yosidaMap V y ↔ x ≤ y := by
  refine ⟨fun h => ?_, yosidaMap_mono⟩
  by_contra hxy
  obtain ⟨φ, hφ⟩ := exists_spectrum_pos hA (v := x - y) (fun h' => hxy (sub_nonpos.1 h'))
  have : φ.1 x ≤ φ.1 y := h φ
  rw [φ.map_sub] at hφ
  linarith

theorem yosidaMap_injective (hA : OUSArchimedean V) : Function.Injective (yosidaMap V) :=
  fun _ _ h => le_antisymm ((yosidaMap_le_iff hA).1 h.le) ((yosidaMap_le_iff hA).1 h.ge)

/-- `v ≤ r·1` iff every point of the spectrum gives `v` a value `≤ r`. -/
theorem le_smul_unit_iff (hA : OUSArchimedean V) (v : V) (r : ℝ) :
    v ≤ r • ouUnit V ↔ ∀ φ : YosidaSpectrum V, φ.1 v ≤ r := by
  rw [← yosidaMap_le_iff hA, yosidaMap_smul_unit]
  rfl

/-- The representation is **isometric** for the order-unit norm:
`‖ϑ(v)‖ ≤ r ⇔ -r·1 ≤ v ≤ r·1`. -/
theorem norm_yosidaMap_le_iff (hA : OUSArchimedean V) (v : V) {r : ℝ} (hr : 0 ≤ r) :
    ‖yosidaMap V v‖ ≤ r ↔ v ≤ r • ouUnit V ∧ -v ≤ r • ouUnit V := by
  rw [ContinuousMap.norm_le _ hr, le_smul_unit_iff hA, le_smul_unit_iff hA]
  simp only [yosidaMap_apply, Real.norm_eq_abs, abs_le, YosidaSpectrum.map_neg]
  constructor
  · intro h; exact ⟨fun φ => (h φ).2, fun φ => by linarith [(h φ).1]⟩
  · intro h φ; exact ⟨by linarith [h.2 φ], h.1 φ⟩

theorem yosidaMap_denseRange :
    closure (Set.range (yosidaMap V)) = Set.univ := by
  have := ContinuousMap.sublattice_closure_eq_top (Set.range (yosidaMap V))
    ⟨_, Set.mem_range_self 0⟩
    (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x ⊓ y, yosidaMap_inf x y⟩)
    (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x ⊔ y, yosidaMap_sup x y⟩)
    (by
      intro g φ ψ
      by_cases hφψ : φ = ψ
      · subst hφψ
        exact ⟨_, ⟨g φ • ouUnit V, rfl⟩, by simp [YosidaSpectrum.map_unit]⟩
      · obtain ⟨z, hz⟩ : ∃ z, φ.1 z ≠ ψ.1 z := by
          by_contra h
          push Not at h
          exact hφψ (Subtype.ext (funext h))
        have hd : φ.1 z - ψ.1 z ≠ 0 := sub_ne_zero.2 hz
        set α := (g φ - g ψ) / (φ.1 z - ψ.1 z)
        set β := g φ - α * φ.1 z
        refine ⟨_, ⟨α • z + β • ouUnit V, rfl⟩, ?_, ?_⟩
        · simp only [yosidaMap_apply, YosidaSpectrum.map_add, YosidaSpectrum.map_smul,
            YosidaSpectrum.map_unit, β]
          ring
        · simp only [yosidaMap_apply, YosidaSpectrum.map_add, YosidaSpectrum.map_smul,
            YosidaSpectrum.map_unit, β, α]
          field_simp
          ring)
  simpa using this

theorem yosidaMap_surjective (hA : OUSArchimedean V) (hC : OUSNormComplete V) :
    Function.Surjective (yosidaMap V) := by
  intro f
  have hf : f ∈ closure (Set.range (yosidaMap V)) := by
    rw [yosidaMap_denseRange]; trivial
  have happrox : ∀ n : ℕ, ∃ x : V, dist f (yosidaMap V x) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨g, ⟨x, rfl⟩, hg⟩ := Metric.mem_closure_iff.1 hf (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨x, hg⟩
  choose s hs using happrox
  -- `‖ϑ(a - b)‖ ≤ δ` with `δ ≥ 0` gives `a - b ≤ δ·1` and `b - a ≤ δ·1`
  have hnorm : ∀ a b : V, ∀ δ : ℝ, 0 ≤ δ → dist (yosidaMap V a) (yosidaMap V b) ≤ δ →
      a - b ≤ δ • ouUnit V ∧ b - a ≤ δ • ouUnit V := by
    intro a b δ hδ h
    rw [dist_eq_norm, ← map_sub, norm_yosidaMap_le_iff hA _ hδ, neg_sub] at h
    exact h
  have hsmall : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, 1 / ((n : ℝ) + 1) < δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    refine ⟨N, fun n hn => ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  obtain ⟨v, hv⟩ := hC s (by
    intro ε hε
    obtain ⟨N, hN⟩ := hsmall (ε / 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    refine (hnorm (s m) (s n) ε hε.le ?_).1
    calc dist (yosidaMap V (s m)) (yosidaMap V (s n))
        ≤ dist (yosidaMap V (s m)) f + dist f (yosidaMap V (s n)) := dist_triangle _ _ _
      _ ≤ ε := by rw [dist_comm]; linarith [hs m, hs n, hN m hm, hN n hn])
  refine ⟨v, ?_⟩
  refine dist_le_zero.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
  obtain ⟨N1, hN1⟩ := hv (δ / 2) (by positivity)
  obtain ⟨N2, hN2⟩ := hsmall (δ / 2) (by positivity)
  set n := max N1 N2
  have h1 : dist (yosidaMap V v) (yosidaMap V (s n)) ≤ δ / 2 := by
    rw [dist_eq_norm, ← map_sub, norm_yosidaMap_le_iff hA _ (by positivity), neg_sub]
    exact ⟨(hN1 n (le_max_left _ _)).2, (hN1 n (le_max_left _ _)).1⟩
  have h2 := hs n
  have h3 := hN2 n (le_max_right _ _)
  calc dist (yosidaMap V v) f ≤ dist (yosidaMap V v) (yosidaMap V (s n)) + dist (yosidaMap V (s n)) f :=
        dist_triangle _ _ _
    _ ≤ 0 + δ := by rw [dist_comm (yosidaMap V (s n))]; linarith

/-- **OAP 64** (`prop:yosida`, first.tex:2465, Theorem; Yosida, cf.
B. Westerbaan, *Yosida duality*): let `V` be a norm-complete lattice-ordered
Archimedean order unit space, and `Φ` its Yosida spectrum — the compact
Hausdorff space (`YosidaSpectrum V`, instances `CompactSpace` and `T2Space`)
of real-valued binary-suprema-preserving unital linear functionals on `V`
with the pointwise topology of `ℝ^V`.  Then `ϑ : V → C(Φ)`,
`ϑ(v)(φ) = φ(v)`, is an order isomorphism.

Stated with the extras a consumer needs: `ϑ` is linear (it is a `LinearMap`),
bijective, an order embedding (hence an order isomorphism), unital,
preserves `⊔` and `⊓`, and is isometric for the order-unit norm.  The
bundled forms are `yosidaLinearEquiv` and `yosidaOrderIso`.  The paper prints
no proof; this one follows *Yosida duality* (see the file header). -/
theorem oap64_yosida (hA : OUSArchimedean V) (hC : OUSNormComplete V) :
    Function.Bijective (yosidaMap V) ∧
    (∀ v w : V, yosidaMap V v ≤ yosidaMap V w ↔ v ≤ w) ∧
    yosidaMap V (ouUnit V) = 1 ∧
    (∀ v w : V, yosidaMap V (v ⊔ w) = yosidaMap V v ⊔ yosidaMap V w) ∧
    (∀ v w : V, yosidaMap V (v ⊓ w) = yosidaMap V v ⊓ yosidaMap V w) ∧
    (∀ (v : V) (r : ℝ), 0 ≤ r →
      (‖yosidaMap V v‖ ≤ r ↔ v ≤ r • ouUnit V ∧ -v ≤ r • ouUnit V)) :=
  ⟨⟨yosidaMap_injective hA, yosidaMap_surjective hA hC⟩, fun _ _ => yosidaMap_le_iff hA,
    yosidaMap_unit, yosidaMap_sup, yosidaMap_inf, fun v _ hr => norm_yosidaMap_le_iff hA v hr⟩

/-- OAP 64, bundled as a linear equivalence `V ≃ₗ C(Φ)`. -/
def yosidaLinearEquiv (hA : OUSArchimedean V) (hC : OUSNormComplete V) :
    V ≃ₗ[ℝ] C(YosidaSpectrum V, ℝ) :=
  LinearEquiv.ofBijective (yosidaMap V) (oap64_yosida hA hC).1

@[simp] theorem yosidaLinearEquiv_apply (hA : OUSArchimedean V) (hC : OUSNormComplete V)
    (v : V) : yosidaLinearEquiv hA hC v = yosidaMap V v := rfl

/-- OAP 64, bundled as an order isomorphism `V ≃o C(Φ)` (with underlying
map `yosidaMap V`). -/
def yosidaOrderIso (hA : OUSArchimedean V) (hC : OUSNormComplete V) :
    V ≃o C(YosidaSpectrum V, ℝ) where
  toEquiv := (yosidaLinearEquiv hA hC).toEquiv
  map_rel_iff' := yosidaMap_le_iff hA

@[simp] theorem yosidaOrderIso_apply (hA : OUSArchimedean V) (hC : OUSNormComplete V)
    (v : V) : yosidaOrderIso hA hC v = yosidaMap V v := rfl

end Riesz

end

end Papers.OAP
