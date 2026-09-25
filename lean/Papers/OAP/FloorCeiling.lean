/-
Papers/OAP/FloorCeiling.lean

A. Westerbaan, B. Westerbaan, J. van de Wetering, *A characterisation of
ordered abstract probabilities* (LICS 2020, arXiv:1912.10040), source
`../papers/1912.10040/first.tex`: §5 *Floors, ceilings and division* —
points **OAP 27**–**OAP 43**.

Conventions (see `Papers/README.md`, `Papers/OAP/PLAN.md`):

* Infinite sums (OAP 27) are `HasOSum x s` for an arbitrary index type; for
  sequences the working notion is `HasSeqSum x s` (partial sums
  `psum x N = x 0 ⋎ ⋯ ⋎ x (N-1)` all defined, and `s` their supremum), and
  `oap27_nat` proves the two agree on `ℕ`.  The paper's sequences start at
  index `0` or `1`; ours always start at `0`.
* `ceil a`, `floor a` (OAP 30), `odiv a b` = the paper's `a/b` (OAP 40) and
  `emInf a b` = `a ∧ b` (OAP 37) are total functions, meaningful in an
  ω-complete effect monoid; their defining properties are theorems.
* The mirror images of left-handed statements (`b·(·)` versus `(·)·b`) are
  obtained by passing to the opposite effect monoid `EMOp M` (same effect
  algebra, reversed multiplication), whose order, sums and complements are
  those of `M` by definition.
-/
import Papers.OAP.Basic
import Theses.B.Eff.StatesPredicates

set_option warn.classDefReducibility false

namespace Papers.OAP

open Theses.B.Eff
open scoped Papers.OAP

universe u v

/-! ## Finite and infinite sums (OAP 27) -/

section Sums

variable {E : Type u} [EffectAlgebra E]

theorem isSumOf_unique' {l : List E} {s t : E} (hs : PCM.IsSumOf l s)
    (ht : PCM.IsSumOf l t) : s = t := by
  induction l generalizing s t with
  | nil => rw [PCM.isSumOf_nil_iff.1 hs, PCM.isSumOf_nil_iff.1 ht]
  | cons a l ih =>
    obtain ⟨s', hs', -, rfl⟩ := isSumOf_cons'.1 hs
    obtain ⟨t', ht', -, rfl⟩ := isSumOf_cons'.1 ht
    rw [ih hs' ht']

/-- The finite sum `⋁_{i ∈ F} xᵢ` exists and equals `t` (the sum of the
`xᵢ` listed in any order without repetition). -/
def HasFinsetSum {I : Type v} (x : I → E) (F : Finset I) (t : E) : Prop :=
  ∃ l : List I, l.Nodup ∧ (∀ i, i ∈ l ↔ i ∈ F) ∧ PCM.IsSumOf (l.map x) t

theorem HasFinsetSum.unique {I : Type v} {x : I → E} {F : Finset I} {s t : E}
    (hs : HasFinsetSum x F s) (ht : HasFinsetSum x F t) : s = t := by
  obtain ⟨l, hl, hlF, hls⟩ := hs
  obtain ⟨l', hl', hlF', hlt⟩ := ht
  have hp : l.Perm l' := (List.perm_ext_iff_of_nodup hl hl').2 fun i => by
    rw [hlF, hlF']
  exact isSumOf_unique' (PCM.isSumOf_perm (hp.map x) hls) hlt

/-- **OAP 27** (first.tex:964, Definition): the sum `⋁_{i∈I} xᵢ` of a
(potentially infinite) family **exists** and equals `s` when every finite
sub-sum `⋁_{i∈S} xᵢ` exists and `s` is the supremum of these finite
sub-sums. -/
def HasOSum {I : Type v} (x : I → E) (s : E) : Prop :=
  (∀ F : Finset I, ∃ t, HasFinsetSum x F t) ∧
    IsLUB {t | ∃ F : Finset I, HasFinsetSum x F t} s

theorem HasOSum.unique {I : Type v} {x : I → E} {s t : E} (hs : HasOSum x s)
    (ht : HasOSum x t) : s = t := hs.2.unique ht.2

/-- Partial sums of a sequence: `psum x N = x 0 ⋎ ⋯ ⋎ x (N-1)`. -/
noncomputable def psum (x : ℕ → E) : ℕ → E
  | 0 => 0
  | n + 1 => psum x n ⋎ x n

@[simp] theorem psum_zero (x : ℕ → E) : psum x 0 = 0 := rfl

theorem psum_succ (x : ℕ → E) (n : ℕ) : psum x (n + 1) = psum x n ⋎ x n := rfl

/-- All partial sums of `x` exist. -/
def SeqSummable (x : ℕ → E) : Prop := ∀ n, Perp (psum x n) (x n)

/-- The sum `⋁ₙ xₙ` of a sequence exists and equals `s`. -/
def HasSeqSum (x : ℕ → E) (s : E) : Prop := SeqSummable x ∧ IsLUB (Set.range (psum x)) s

theorem HasSeqSum.unique {x : ℕ → E} {s t : E} (hs : HasSeqSum x s) (ht : HasSeqSum x t) :
    s = t := hs.2.unique ht.2

theorem isSumOf_range {x : ℕ → E} (hx : SeqSummable x) (n : ℕ) :
    PCM.IsSumOf ((List.range n).map x) (psum x n) := by
  induction n with
  | zero => exact PCM.IsSumOf.nil
  | succ n ih =>
    rw [List.range_succ, List.map_append]
    exact isSumOf_append.2 ⟨_, _, ih, isSumOf_singleton.2 rfl, hx n, rfl⟩

theorem seqSummable_of_isSumOf {x : ℕ → E}
    (h : ∀ n, ∃ t, PCM.IsSumOf ((List.range n).map x) t) : SeqSummable x := by
  have key : ∀ n, PCM.IsSumOf ((List.range n).map x) (psum x n) ∧
      (∀ t, PCM.IsSumOf ((List.range (n + 1)).map x) t → Perp (psum x n) (x n)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨PCM.IsSumOf.nil, fun t ht => ?_⟩
      exact zero_perp _
    | succ n ih =>
      obtain ⟨t, ht⟩ := h (n + 1)
      have hp := ih.2 t ht
      have hsum : PCM.IsSumOf ((List.range (n + 1)).map x) (psum x (n + 1)) := by
        rw [List.range_succ, List.map_append]
        exact isSumOf_append.2 ⟨_, _, ih.1, isSumOf_singleton.2 rfl, hp, rfl⟩
      refine ⟨hsum, fun t' ht' => ?_⟩
      rw [List.range_succ, List.map_append] at ht'
      obtain ⟨s, r, hs, hr, hsr, -⟩ := isSumOf_append.1 ht'
      rw [isSumOf_unique' hs hsum, isSumOf_singleton.1 hr] at hsr
      exact hsr
  exact fun n => (key n).2 _ (h (n + 1)).choose_spec

theorem hasFinsetSum_range {x : ℕ → E} (hx : SeqSummable x) (n : ℕ) :
    HasFinsetSum x (Finset.range n) (psum x n) :=
  ⟨List.range n, List.nodup_range, fun i => by simp, isSumOf_range hx n⟩

/-- Every finite sub-sum of a summable sequence exists and lies below a
partial sum. -/
theorem exists_hasFinsetSum_le {x : ℕ → E} (hx : SeqSummable x) (F : Finset ℕ) :
    ∃ t, HasFinsetSum x F t ∧ ∃ N, t ≤ psum x N := by
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range F
  have hp := List.filter_append_perm (fun i => decide (i ∈ F)) (List.range N)
  have hs := PCM.isSumOf_perm (hp.symm.map x) (isSumOf_range hx N)
  rw [List.map_append] at hs
  obtain ⟨s, r, hs, -, hsr, e⟩ := isSumOf_append.1 hs
  refine ⟨s, ⟨_, (List.nodup_range).filter _, fun i => ?_, hs⟩, N, e ▸ le_oplus_left hsr⟩
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.1 (hN h), h⟩⟩

/-- **OAP 27** (first.tex:964, Definition), for sequences: the sum
`⋁ₙ xₙ` in the sense of the definition (supremum of the finite sub-sums)
exists and equals `s` iff all partial sums `x₀ ⋁ ⋯ ⋁ x_{N-1}` exist and `s`
is their supremum. -/
theorem oap27_nat {x : ℕ → E} {s : E} : HasOSum x s ↔ HasSeqSum x s := by
  have ub : SeqSummable x → (upperBounds {t | ∃ F : Finset ℕ, HasFinsetSum x F t} =
      upperBounds (Set.range (psum x))) := by
    intro hx
    ext u
    constructor
    · rintro hu _ ⟨n, rfl⟩; exact hu ⟨_, hasFinsetSum_range hx n⟩
    · rintro hu t ⟨F, hF⟩
      obtain ⟨t', ht', N, hN⟩ := exists_hasFinsetSum_le hx F
      rw [hF.unique ht']
      exact le_trans hN (hu ⟨N, rfl⟩)
  constructor
  · rintro ⟨hF, hs⟩
    have hx : SeqSummable x := seqSummable_of_isSumOf fun n => by
      obtain ⟨t, l, hl, hlF, hlt⟩ := hF (Finset.range n)
      have hp : l.Perm (List.range n) :=
        (List.perm_ext_iff_of_nodup hl List.nodup_range).2 fun i => by simp [hlF]
      exact ⟨t, PCM.isSumOf_perm (hp.map x) hlt⟩
    refine ⟨hx, ?_, ?_⟩
    · rw [← ub hx]; exact hs.1
    · intro u hu; rw [← ub hx] at hu; exact hs.2 hu
  · rintro ⟨hx, hs⟩
    refine ⟨fun F => (exists_hasFinsetSum_le hx F).imp fun _ h => h.1, ?_, ?_⟩
    · rw [ub hx]; exact hs.1
    · intro u hu; rw [ub hx] at hu; exact hs.2 hu

theorem psum_mono {x : ℕ → E} (hx : SeqSummable x) : Monotone (psum x) :=
  monotone_nat_of_le_succ fun n => le_oplus_left (hx n)

theorem HasSeqSum.psum_le {x : ℕ → E} {s : E} (h : HasSeqSum x s) (n : ℕ) : psum x n ≤ s :=
  h.2.1 ⟨n, rfl⟩

theorem HasSeqSum.le_sum {x : ℕ → E} {s : E} (h : HasSeqSum x s) (n : ℕ) : x n ≤ s :=
  le_trans (le_oplus_right (h.1 n)) (h.psum_le (n + 1))

theorem exists_hasSeqSum [OmegaComplete E] {x : ℕ → E} (hx : SeqSummable x) :
    ∃ s, HasSeqSum x s :=
  (OmegaComplete.exists_isLUB _ (psum_mono hx)).imp fun _ h => ⟨hx, h⟩

/-- Termwise smaller sequences of a summable sequence are summable, with
smaller partial sums. -/
theorem psum_le_psum {x y : ℕ → E} (hy : SeqSummable y) (hxy : ∀ n, x n ≤ y n) :
    SeqSummable x ∧ ∀ n, psum x n ≤ psum y n := by
  have key : ∀ n, psum x n ≤ psum y n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact oplus_le_oplus ih (hxy n) (hy n)
  exact ⟨fun n => perp_of_le (key n) (hxy n) (hy n), key⟩

theorem HasSeqSum.mono {x y : ℕ → E} {s t : E} (hs : HasSeqSum x s) (ht : HasSeqSum y t)
    (hxy : ∀ n, x n ≤ y n) : s ≤ t :=
  hs.2.2 (by rintro _ ⟨n, rfl⟩; exact le_trans ((psum_le_psum ht.1 hxy).2 n) (ht.psum_le n))

open Classical in
/-- The sum `⋁ₙ xₙ` when it exists (junk `0` otherwise). -/
noncomputable def seqSum (x : ℕ → E) : E := if h : ∃ s, HasSeqSum x s then h.choose else 0

theorem HasSeqSum.seqSum_eq {x : ℕ → E} {s : E} (h : HasSeqSum x s) : seqSum x = s := by
  have h' : ∃ s, HasSeqSum x s := ⟨s, h⟩
  unfold seqSum
  split
  · next hh => exact hh.choose_spec.unique h
  · next hh => exact absurd h' hh

theorem hasSeqSum_seqSum [OmegaComplete E] {x : ℕ → E} (hx : SeqSummable x) :
    HasSeqSum x (seqSum x) := by
  obtain ⟨s, hs⟩ := exists_hasSeqSum hx
  rwa [hs.seqSum_eq]

/-- If `b ≤ xₖ` for all `k < n` and `x₀ ⋁ ⋯ ⋁ x_{n-1}` exists, then `nb`
exists (and lies below that partial sum). -/
theorem isNSum_of_le_psum {x : ℕ → E} (hx : SeqSummable x) {b : E} :
    ∀ n, (∀ k < n, b ≤ x k) → ∃ s, IsNSum b n s ∧ s ≤ psum x n := by
  intro n
  induction n with
  | zero => intro _; exact ⟨0, IsNSum.zero, le_rfl⟩
  | succ n ih =>
    intro hb
    obtain ⟨s, hs, hsle⟩ := ih fun k hk => hb k (Nat.lt_succ_of_lt hk)
    have hbn := hb n (Nat.lt_succ_self n)
    exact ⟨_, hs.succ (perp_of_le hsle hbn (hx n)), oplus_le_oplus hsle hbn (hx n)⟩

/-- In an ω-complete effect algebra, a common lower bound of the terms of a
summable sequence is `0` (OAP 26, point 1). -/
theorem eq_zero_of_le_seqSummable [OmegaComplete E] {x : ℕ → E} (hx : SeqSummable x)
    {b : E} (hb : ∀ k, b ≤ x k) : b = 0 :=
  oap26_1 fun n => (isNSum_of_le_psum hx n fun k _ => hb k).imp fun _ h => h.1

/-- Termwise sums of summable sequences: if `xₙ ⊥ yₙ` and `(xₙ ⋁ yₙ)ₙ` is
summable, then so are `x` and `y`, with partial sums adding up. -/
theorem psum_oplus {x y : ℕ → E} (hxy : ∀ n, Perp (x n) (y n))
    (h : SeqSummable fun n => x n ⋎ y n) (n : ℕ) :
    Perp (psum x n) (psum y n) ∧ psum (fun n => x n ⋎ y n) n = psum x n ⋎ psum y n ∧
      Perp (psum x n) (x n) ∧ Perp (psum y n) (y n) := by
  have step : ∀ n, Perp (psum x n) (psum y n) →
      psum (fun n => x n ⋎ y n) n = psum x n ⋎ psum y n →
      Perp (psum x n) (x n) ∧ Perp (psum y n) (y n) ∧ Perp (psum x (n + 1)) (psum y (n + 1)) ∧
        psum (fun n => x n ⋎ y n) (n + 1) = psum x (n + 1) ⋎ psum y (n + 1) := by
    intro n h1 e1
    have hn := h n
    rw [e1] at hn
    -- `(Σx ⋁ Σy) ⋁ (xₙ ⋁ yₙ) = (Σx ⋁ xₙ) ⋁ (Σy ⋁ yₙ)`
    obtain ⟨h2, h3, h4, e2⟩ := oplus_oplus_comm h1 (hxy n) hn
    refine ⟨h2, h3, h4, ?_⟩
    rw [psum_succ, e1, psum_succ, psum_succ, e2]
  have key : ∀ n, Perp (psum x n) (psum y n) ∧
      psum (fun n => x n ⋎ y n) n = psum x n ⋎ psum y n := by
    intro n
    induction n with
    | zero => exact ⟨zero_perp _, by simp [psum_zero]⟩
    | succ n ih => exact ⟨(step n ih.1 ih.2).2.2.1, (step n ih.1 ih.2).2.2.2⟩
  exact ⟨(key n).1, (key n).2, (step n (key n).1 (key n).2).1, (step n (key n).1 (key n).2).2.1⟩

/-- Suprema of increasing sequences add: if `f`, `g` are increasing with
`fₙ ⊥ gₙ`, `⋁f = F` and `⋁g = G`, then `F ⊥ G` and `⋁ₙ (fₙ ⋁ gₙ) = F ⋁ G`
(two applications of OAP 24, point 1). -/
theorem isLUB_oplus_of_monotone {f g : ℕ → E} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ n, Perp (f n) (g n)) {F G : E} (hF : IsLUB (Set.range f) F)
    (hG : IsLUB (Set.range g) G) :
    Perp F G ∧ IsLUB (Set.range fun n => f n ⋎ g n) (F ⋎ G) := by
  have hp : ∀ m n, Perp (f m) (g n) := fun m n =>
    perp_of_le (hf (le_max_left m n)) (hg (le_max_right m n)) (hfg (max m n))
  have h1 : ∀ m, Perp (f m) G ∧ IsLUB ((f m ⋎ ·) '' Set.range g) (f m ⋎ G) := fun m =>
    oap24_1 (Set.range_nonempty g) (by rintro _ ⟨n, rfl⟩; exact le_orth_of_perp (hp m n)) hG
  obtain ⟨hGF, h2⟩ := oap24_1 (x := G) (Set.range_nonempty f)
    (by rintro _ ⟨n, rfl⟩; exact le_orth_of_perp (PCM.perp_comm (h1 n).1)) hF
  have hFG : Perp F G := PCM.perp_comm hGF
  refine ⟨hFG, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩; exact oplus_le_oplus (hF.1 ⟨n, rfl⟩) (hG.1 ⟨n, rfl⟩) hFG
  · intro u hu
    have hmn : ∀ m n, f m ⋎ g n ≤ u := fun m n =>
      le_trans (oplus_le_oplus (hf (le_max_left m n)) (hg (le_max_right m n))
        (hfg (max m n))) (hu ⟨max m n, rfl⟩)
    have hm : ∀ m, f m ⋎ G ≤ u := fun m => (h1 m).2.2 (by rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact hmn m n)
    rw [oplus_comm]
    exact h2.2 (by rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩; show G ⋎ f m ≤ u; rw [oplus_comm]; exact hm m)

/-- Sums of sequences add termwise. -/
theorem HasSeqSum.oplus {x y : ℕ → E} {s t : E} (hxy : ∀ n, Perp (x n) (y n))
    (h : SeqSummable fun n => x n ⋎ y n) (hs : HasSeqSum x s) (ht : HasSeqSum y t) :
    Perp s t ∧ HasSeqSum (fun n => x n ⋎ y n) (s ⋎ t) := by
  obtain ⟨hst, hl⟩ := isLUB_oplus_of_monotone (psum_mono hs.1) (psum_mono ht.1)
    (fun n => (psum_oplus hxy h n).1) hs.2 ht.2
  refine ⟨hst, h, ?_⟩
  have e : psum (fun n => x n ⋎ y n) = fun n => psum x n ⋎ psum y n :=
    funext fun n => (psum_oplus hxy h n).2.1
  rw [e]; exact hl

end Sums

/-! ## Ceilings and floors (OAP 28–36) -/

section CeilFloor

variable {M : Type u} [EffectMonoid M]

theorem pow_orth_comm (a : M) (n : ℕ) : a ^ n * orth a = orth a * a ^ n := by
  induction n with
  | zero => rw [pow_zero, emul_one, eone_mul]
  | succ n ih =>
    rw [emul_pow_succ, emul_assoc, oap17, ← emul_assoc, ih, emul_assoc]

theorem pow_succ_eq_mul (a : M) (n : ℕ) : a ^ (n + 1) = a * a ^ n := pow_succ' a n

/-- `x·aⁿ ≤ x·aᵐ` for `m ≤ n`. -/
theorem emul_pow_antitone (x a : M) : Antitone fun n : ℕ => x * a ^ n :=
  antitone_nat_of_succ_le fun n => by
    rw [emul_pow_succ, ← emul_assoc]; exact emul_le_left _ _

theorem pow_antitone (a : M) : Antitone fun n : ℕ => a ^ n :=
  antitone_nat_of_succ_le fun n => by rw [emul_pow_succ]; exact emul_le_left _ _

/-- The computation in the proof of OAP 28:
`1 = a^⊥ ⋁ a^⊥·a ⋁ ⋯ ⋁ a^⊥·a^{N-1} ⋁ a^N`. -/
theorem psum_orth_mul_pow (a : M) (N : ℕ) :
    Perp (psum (fun n => orth a * a ^ n) N) (a ^ N) ∧
      psum (fun n => orth a * a ^ n) N ⋎ a ^ N = 1 := by
  induction N with
  | zero => exact ⟨zero_perp _, by rw [psum_zero, pow_zero, zero_oplus]⟩
  | succ N ih =>
    -- `a^N = (a^⊥ ⋁ a)·a^N = a^⊥·a^N ⋁ a^{N+1}`
    obtain ⟨h1, e1⟩ := oplus_mul (a ^ N) (PCM.perp_comm (perp_orth a))
    rw [orth_oplus, eone_mul, ← pow_succ_eq_mul] at e1
    rw [← pow_succ_eq_mul] at h1
    obtain ⟨hp, e⟩ := ih
    rw [e1] at hp e
    obtain ⟨h2, h3⟩ := perp_assoc_left h1 hp
    refine ⟨h3, ?_⟩
    rw [psum_succ, ← e, oplus_assoc' h1 hp]

theorem seqSummable_orth_mul_pow (a : M) : SeqSummable fun n => orth a * a ^ n := by
  intro N
  obtain ⟨h1, -⟩ := oplus_mul (a ^ N) (PCM.perp_comm (perp_orth a))
  obtain ⟨hp, e⟩ := psum_orth_mul_pow a N
  have e1 := (oplus_mul (a ^ N) (PCM.perp_comm (perp_orth a))).2
  rw [orth_oplus, eone_mul] at e1
  rw [e1] at hp
  exact (perp_assoc_left h1 hp).1

theorem psum_orth_mul_pow_eq (a : M) (N : ℕ) :
    psum (fun n => orth a * a ^ n) N = orth (a ^ N) := by
  obtain ⟨hp, e⟩ := psum_orth_mul_pow a N
  rw [eq_orth_of_oplus hp e, orth_orth]

/-- **OAP 28** (`lem:proto-ceilfloor`, first.tex:977, Lemma): for every `N`,
the sum `a^⊥ ⋁ a^⊥·a ⋁ ⋯ ⋁ a^⊥·a^{N-1}` exists and equals `(a^N)^⊥`. -/
theorem oap28 (a : M) (N : ℕ) :
    PCM.IsSumOf ((List.range N).map fun n => orth a * a ^ n) (orth (a ^ N)) := by
  rw [← psum_orth_mul_pow_eq]; exact isSumOf_range (seqSummable_orth_mul_pow a) N

/-- **OAP 29** (first.tex:1008, Corollary): in an ω-complete effect monoid
the sum `⋁ₙ a^⊥·aⁿ` exists. -/
theorem oap29 [OmegaComplete M] (a : M) : ∃ s, HasOSum (fun n => orth a * a ^ n) s :=
  (exists_hasSeqSum (seqSummable_orth_mul_pow a)).imp fun _ h => oap27_nat.2 h

/-- The series `a·(a^⊥)ⁿ` defining the ceiling (OAP 29 applied to `a^⊥`). -/
theorem seqSummable_mul_orth_pow (a : M) : SeqSummable fun n => a * orth a ^ n := by
  have := seqSummable_orth_mul_pow (orth a)
  simp only [orth_orth] at this
  exact this

theorem psum_mul_orth_pow_eq (a : M) (N : ℕ) :
    psum (fun n => a * orth a ^ n) N = orth (orth a ^ N) := by
  have := psum_orth_mul_pow_eq (orth a) N
  simp only [orth_orth] at this
  exact this

/-- **OAP 30** (first.tex:1013, Definition): the **ceiling**
`⌈a⌉ ≡ ⋁ₙ a·(a^⊥)ⁿ` (meaningful in an ω-complete effect monoid; the sum is
`seqSum`, junk when it does not exist). -/
noncomputable def ceil (a : M) : M := seqSum fun n => a * orth a ^ n

open Classical in
/-- **OAP 30** (first.tex:1013, Definition): the **floor** `⌊a⌋ ≡ ⋀ₙ aⁿ`
(junk `0` when the infimum does not exist). -/
noncomputable def floor (a : M) : M :=
  if h : ∃ m, IsGLB (Set.range fun n : ℕ => a ^ n) m then h.choose else 0

section Omega

variable [OmegaComplete M]

/-- **OAP 30** (first.tex:1013, Definition): in an ω-complete effect monoid,
`⌈a⌉` is the sum `⋁ₙ a·(a^⊥)ⁿ` (which exists by OAP 29). -/
theorem oap30_ceil (a : M) : HasOSum (fun n => a * orth a ^ n) (ceil a) :=
  oap27_nat.2 (hasSeqSum_seqSum (seqSummable_mul_orth_pow a))

theorem hasSeqSum_ceil (a : M) : HasSeqSum (fun n => a * orth a ^ n) (ceil a) :=
  hasSeqSum_seqSum (seqSummable_mul_orth_pow a)

/-- **OAP 30** (first.tex:1013, Definition): in an ω-complete effect monoid,
`⌊a⌋` is the infimum `⋀ₙ aⁿ` (which exists: a decreasing sequence). -/
theorem oap30_floor (a : M) : IsGLB (Set.range fun n : ℕ => a ^ n) (floor a) := by
  have h : ∃ m, IsGLB (Set.range fun n : ℕ => a ^ n) m :=
    OmegaComplete.exists_isGLB _ (pow_antitone a)
  unfold floor
  split
  · next hh => exact hh.choose_spec
  · next hh => exact absurd h hh

theorem floor_le_pow (a : M) (n : ℕ) : floor a ≤ a ^ n := (oap30_floor a).1 ⟨n, rfl⟩

/-- **OAP 31** (`lem:infaperpan`, first.tex:1049, Lemma): `⋀ₙ a^⊥·aⁿ = 0`
(the infimum existing). -/
theorem oap31 (a : M) : IsGLB (Set.range fun n : ℕ => orth a * a ^ n) 0 := by
  obtain ⟨b, hb⟩ := OmegaComplete.exists_isGLB _ (emul_pow_antitone (orth a) a)
  -- `b ≤ a^⊥·aᵏ` for all `k`, and `⋁ₖ a^⊥·aᵏ` exists, so `nb` exists for all `n`
  have : b = 0 := eq_zero_of_le_seqSummable (seqSummable_orth_mul_pow a)
    fun k => hb.1 ⟨k, rfl⟩
  exact this ▸ hb

theorem floor_mul_orth (a : M) : floor a * orth a = 0 := by
  refine eq_zero_of_le_zero ((oap31 a).2 ?_)
  rintro _ ⟨n, rfl⟩
  show floor a * orth a ≤ orth a * a ^ n
  rw [← pow_orth_comm]
  exact emul_le_emul_right (floor_le_pow a n) _

theorem orth_mul_floor (a : M) : orth a * floor a = 0 := by
  refine eq_zero_of_le_zero ((oap31 a).2 ?_)
  rintro _ ⟨n, rfl⟩
  exact emul_le_emul_left (orth a) (floor_le_pow a n)

/-- **OAP 32** (`lem:flooraa`, first.tex:1071, Lemma): `⌊a⌋ = ⌊a⌋·a = a·⌊a⌋`. -/
theorem oap32 (a : M) : floor a = floor a * a ∧ floor a = a * floor a := by
  constructor
  · -- `⌊a⌋·a^⊥ ≤ ⋀ₙ aⁿ·a^⊥ = ⋀ₙ a^⊥·aⁿ = 0`
    obtain ⟨-, e⟩ := emul_oplus_emul_orth (floor a) a
    rw [floor_mul_orth, oplus_zero] at e
    exact e.symm
  · obtain ⟨-, e⟩ := emul_oplus_orth_emul a (floor a)
    rw [orth_mul_floor, oplus_zero] at e
    exact e.symm

omit [OmegaComplete M] in
/-- `a·bₙ = 0` for all `n` gives `a·⋁ₙ bₙ = 0` (the proof of OAP 33, for
`HasSeqSum`). -/
theorem mul_eq_zero_of_hasSeqSum {a s : M} {b : ℕ → M} (hs : HasSeqSum b s)
    (h : ∀ n, a * b n = 0) : a * s = 0 := by
  -- `a·s_N = 0` for the partial sums `s_N`
  have h0 : ∀ N, a * psum b N = 0 := by
    intro N
    induction N with
    | zero => exact emul_zero a
    | succ N ih => rw [psum_succ, (mul_oplus a (hs.1 N)).2, ih, h N, oplus_zero]
  -- so `s_N = a^⊥·s_N ≤ a^⊥·s`, whence `s ≤ a^⊥·s ≤ s`
  have h1 : ∀ N, psum b N = orth a * psum b N := fun N => by
    obtain ⟨-, e⟩ := emul_oplus_orth_emul a (psum b N)
    rw [h0 N, zero_oplus] at e
    exact e.symm
  have h2 : orth a * s = s := le_antisymm (emul_le_right _ _) (hs.2.2 (by
    rintro _ ⟨N, rfl⟩
    rw [h1 N]; exact emul_le_emul_left _ (hs.psum_le N)))
  obtain ⟨hp, e⟩ := emul_oplus_orth_emul a s
  rw [h2] at hp e
  exact oplus_right_cancel hp (zero_perp s) (by rw [zero_oplus]; exact e)

omit [OmegaComplete M] in
/-- **OAP 33** (`lem:zerodivsum`, first.tex:1109, Lemma): if `⋁ₙ bₙ` exists
and `a·bₙ = 0` for all `n`, then `a·⋁ₙ bₙ = 0`. -/
theorem oap33 {a s : M} {b : ℕ → M} (hs : HasOSum b s) (h : ∀ n, a * b n = 0) :
    a * s = 0 :=
  mul_eq_zero_of_hasSeqSum (oap27_nat.1 hs) h

/-- **OAP 34** (`prop:ceilprod`, first.tex:1133, Proposition): `a·b = 0`
implies `a·⌈b⌉ = 0`. -/
theorem oap34 {a b : M} (h : a * b = 0) : a * ceil b = 0 :=
  mul_eq_zero_of_hasSeqSum (hasSeqSum_ceil b) fun n => by rw [← emul_assoc, h, ezero_mul]

/-- **OAP 35** (`prop:ceilfloor`, first.tex:1169, Proposition), point 3:
`⌈a⌉^⊥ = ⌊a^⊥⌋` and `⌊a⌋^⊥ = ⌈a^⊥⌉`. -/
theorem oap35_3 (a : M) : orth (ceil a) = floor (orth a) ∧ orth (floor a) = ceil (orth a) := by
  have h1 : ∀ a : M, orth (ceil a) = floor (orth a) := by
    intro a
    -- the partial sums of `⌈a⌉` are `((a^⊥)^N)^⊥` (OAP 28)
    have hl : IsLUB (orth '' Set.range fun n : ℕ => orth a ^ n) (ceil a) := by
      have := (hasSeqSum_ceil a).2
      rwa [show psum (fun n => a * orth a ^ n) = orth ∘ fun n => orth a ^ n
        from funext (psum_mul_orth_pow_eq a), Set.range_comp] at this
    exact (isGLB_orth_of_isLUB hl).unique (oap30_floor (orth a))
  refine ⟨h1 a, ?_⟩
  have := h1 (orth a)
  rw [orth_orth] at this
  rw [← this, orth_orth]

theorem floor_idem (a : M) : floor a * floor a = floor a := by
  -- `⌊a⌋·a^⊥ = 0` gives `⌊a⌋·⌈a^⊥⌉ = 0`, i.e. `⌊a⌋·⌊a⌋^⊥ = 0`
  have h := oap34 (floor_mul_orth a)
  rw [← (oap35_3 a).2] at h
  exact (oap18 _).2 h

theorem floor_le (a : M) : floor a ≤ a := by
  have := floor_le_pow a 1; rwa [pow_one] at this

theorem le_floor {a p : M} (hp : p * p = p) (hpa : p ≤ a) : p ≤ floor a := by
  refine (oap30_floor a).2 ?_
  rintro _ ⟨n, rfl⟩
  show p ≤ a ^ n
  induction n with
  | zero => exact le_one' p
  | succ n ih =>
    rw [emul_pow_succ, ← hp]
    exact le_trans (emul_le_emul_right ih p) (emul_le_emul_left _ hpa)

/-- **OAP 35** (`prop:ceilfloor`, first.tex:1169, Proposition), point 1:
`⌊a⌋` is an idempotent below `a`, and the greatest such. -/
theorem oap35_1 (a : M) : IsGreatest {p : M | p * p = p ∧ p ≤ a} (floor a) :=
  ⟨⟨floor_idem a, floor_le a⟩, fun _ ⟨hp, hpa⟩ => le_floor hp hpa⟩

theorem ceil_eq_orth_floor (a : M) : ceil a = orth (floor (orth a)) := by
  rw [← (oap35_3 a).1, orth_orth]

theorem ceil_idem (a : M) : ceil a * ceil a = ceil a := by
  rw [ceil_eq_orth_floor]; exact idem_orth (floor_idem _)

theorem le_ceil (a : M) : a ≤ ceil a := by
  rw [ceil_eq_orth_floor, ← orth_le_orth_iff, orth_orth]; exact floor_le _

theorem ceil_le {a p : M} (hp : p * p = p) (hap : a ≤ p) : ceil a ≤ p := by
  rw [ceil_eq_orth_floor, ← orth_le_orth_iff, orth_orth]
  exact le_floor (idem_orth hp) (orth_le_orth hap)

/-- **OAP 35** (`prop:ceilfloor`, first.tex:1169, Proposition), point 2:
`⌈a⌉` is the least idempotent above `a`. -/
theorem oap35_2 (a : M) : IsLeast {p : M | p * p = p ∧ a ≤ p} (ceil a) :=
  ⟨⟨ceil_idem a, le_ceil a⟩, fun _ ⟨hp, hap⟩ => ceil_le hp hap⟩

theorem ceil_of_idem {p : M} (hp : p * p = p) : ceil p = p :=
  le_antisymm (ceil_le hp le_rfl) (le_ceil p)

theorem floor_of_idem {p : M} (hp : p * p = p) : floor p = p :=
  le_antisymm (floor_le p) (le_floor hp le_rfl)

theorem ceil_mono {a b : M} (h : a ≤ b) : ceil a ≤ ceil b :=
  ceil_le (ceil_idem b) (le_trans h (le_ceil b))

/-- **OAP 36** (`lem:sumofceil`, first.tex:1218, Lemma): for summable `a`,
`b`, `⌈a ⋁ b⌉` is the supremum of `⌈a⌉` and `⌈b⌉`. -/
theorem oap36 {a b : M} (h : Perp a b) : IsLUB {ceil a, ceil b} (ceil (a ⋎ b)) := by
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ (rfl | rfl)
    · exact ceil_mono (le_oplus_left h)
    · exact ceil_mono (le_oplus_right h)
  · -- `a ≤ ⌈a⌉ ≤ ⌊u⌋` and `b ≤ ⌈b⌉ ≤ ⌊u⌋`, so `a ⋁ b ≤ ⌊u⌋` (OAP 23)
    have ha : ceil a ≤ floor u := le_floor (ceil_idem a) (hu (Set.mem_insert _ _))
    have hb : ceil b ≤ floor u := le_floor (ceil_idem b) (hu (Set.mem_insert_of_mem _ rfl))
    have hab : a ⋎ b ≤ floor u :=
      oap23 (floor_idem u) (le_trans (le_ceil a) ha) (le_trans (le_ceil b) hb) h
    exact le_trans (ceil_le (floor_idem u) hab) (floor_le u)

end Omega

end CeilFloor

/-! ## Infima and suprema (OAP 37–39) -/

section Lattice

variable {M : Type u} [EffectMonoid M]

/-- The sequences of OAP 37, indexed from `0`: `(a₀, b₀) = (a, b)`,
`aₙ₊₁ = aₙ·bₙ^⊥`, `bₙ₊₁ = aₙ^⊥·bₙ`. -/
def infSeq (a b : M) : ℕ → M × M
  | 0 => (a, b)
  | n + 1 => ((infSeq a b n).1 * orth (infSeq a b n).2, orth (infSeq a b n).1 * (infSeq a b n).2)

/-- The terms `aₙ·bₙ` of OAP 37. -/
def infTerm (a b : M) (n : ℕ) : M := (infSeq a b n).1 * (infSeq a b n).2

/-- **OAP 37** (`thm:latticeemon`, first.tex:1238): the infimum
`a ∧ b ≡ ⋁ₙ aₙ·bₙ` (junk when the sum does not exist). -/
noncomputable def emInf (a b : M) : M := seqSum (infTerm a b)

/-- **OAP 37** (`thm:latticeemon`, first.tex:1238): the supremum
`a ∨ b ≡ (a^⊥ ∧ b^⊥)^⊥`. -/
noncomputable def emSup (a b : M) : M := orth (emInf (orth a) (orth b))

/-- The first step of the proof of OAP 37: `(⋁_{n<N} aₙ·bₙ) ⋁ a_N = a` and
`(⋁_{n<N} aₙ·bₙ) ⋁ b_N = b`, all sums existing. -/
theorem psum_infTerm (a b : M) (N : ℕ) :
    Perp (psum (infTerm a b) N) (infSeq a b N).1 ∧
      psum (infTerm a b) N ⋎ (infSeq a b N).1 = a ∧
    Perp (psum (infTerm a b) N) (infSeq a b N).2 ∧
      psum (infTerm a b) N ⋎ (infSeq a b N).2 = b := by
  induction N with
  | zero => exact ⟨zero_perp _, zero_oplus _, zero_perp _, zero_oplus _⟩
  | succ N ih =>
    obtain ⟨ha, ea, hb, eb⟩ := ih
    -- `a_N = a_N·b_N ⋁ a_N·b_N^⊥` and `b_N = a_N·b_N ⋁ a_N^⊥·b_N`
    obtain ⟨h1, e1⟩ := emul_oplus_emul_orth (infSeq a b N).1 (infSeq a b N).2
    obtain ⟨h2, e2⟩ := emul_oplus_orth_emul (infSeq a b N).1 (infSeq a b N).2
    rw [← e1] at ha ea
    rw [← e2] at hb eb
    obtain ⟨-, ha'⟩ := perp_assoc_left h1 ha
    obtain ⟨-, hb'⟩ := perp_assoc_left h2 hb
    refine ⟨ha', ?_, hb', ?_⟩
    · show psum (infTerm a b) N ⋎ (infSeq a b N).1 * (infSeq a b N).2 ⋎
        (infSeq a b N).1 * orth (infSeq a b N).2 = a
      rw [oplus_assoc' h1 ha]; exact ea
    · show psum (infTerm a b) N ⋎ (infSeq a b N).1 * (infSeq a b N).2 ⋎
        orth (infSeq a b N).1 * (infSeq a b N).2 = b
      rw [oplus_assoc' h2 hb]; exact eb

theorem seqSummable_infTerm (a b : M) : SeqSummable (infTerm a b) := fun N => by
  obtain ⟨ha, -⟩ := psum_infTerm a b N
  obtain ⟨h1, e1⟩ := emul_oplus_emul_orth (infSeq a b N).1 (infSeq a b N).2
  rw [← e1] at ha
  exact (perp_assoc_left h1 ha).1

theorem psum_infTerm_le (a b : M) (N : ℕ) : psum (infTerm a b) N ≤ a ∧ psum (infTerm a b) N ≤ b := by
  obtain ⟨ha, ea, hb, eb⟩ := psum_infTerm a b N
  exact ⟨le_of_le_of_eq (le_oplus_left ha) ea, le_of_le_of_eq (le_oplus_left hb) eb⟩

section Omega

variable [OmegaComplete M]

theorem hasSeqSum_emInf (a b : M) : HasSeqSum (infTerm a b) (emInf a b) :=
  hasSeqSum_seqSum (seqSummable_infTerm a b)

/-- `a = ⋀ₘ aₘ ⋁ ⋁ₙ aₙ·bₙ` (in the proof of OAP 37), via OAP 24 point 5. -/
theorem isGLB_infSeq_fst (a b : M) :
    emInf a b ≤ a ∧ IsGLB (Set.range fun n => (infSeq a b n).1) (a ⊖ emInf a b) := by
  have hs := hasSeqSum_emInf a b
  have hle : emInf a b ≤ a := hs.2.2 (by rintro _ ⟨N, rfl⟩; exact (psum_infTerm_le a b N).1)
  refine ⟨hle, ?_⟩
  have h := oap24_5 (x := a) (Set.range_nonempty _)
    (by rintro _ ⟨N, rfl⟩; exact (psum_infTerm_le a b N).1) hs.2
  have e : (a ⊖ ·) '' Set.range (psum (infTerm a b)) = Set.range fun n => (infSeq a b n).1 := by
    rw [← Set.range_comp]; congr 1; funext N
    obtain ⟨hp, e, -, -⟩ := psum_infTerm a b N
    exact (osub_eq_iff (psum_infTerm_le a b N).1).2 ⟨hp, e⟩
  rwa [e] at h

theorem isGLB_infSeq_snd (a b : M) :
    emInf a b ≤ b ∧ IsGLB (Set.range fun n => (infSeq a b n).2) (b ⊖ emInf a b) := by
  have hs := hasSeqSum_emInf a b
  have hle : emInf a b ≤ b := hs.2.2 (by rintro _ ⟨N, rfl⟩; exact (psum_infTerm_le a b N).2)
  refine ⟨hle, ?_⟩
  have h := oap24_5 (x := b) (Set.range_nonempty _)
    (by rintro _ ⟨N, rfl⟩; exact (psum_infTerm_le a b N).2) hs.2
  have e : (b ⊖ ·) '' Set.range (psum (infTerm a b)) = Set.range fun n => (infSeq a b n).2 := by
    rw [← Set.range_comp]; congr 1; funext N
    obtain ⟨-, -, hp, e⟩ := psum_infTerm a b N
    exact (osub_eq_iff (psum_infTerm_le a b N).2).2 ⟨hp, e⟩
  rwa [e] at h

theorem isGLB_emInf (a b : M) : IsGLB {a, b} (emInf a b) := by
  set m := emInf a b
  obtain ⟨hma, hα⟩ := isGLB_infSeq_fst a b
  obtain ⟨hmb, hβ⟩ := isGLB_infSeq_snd a b
  set α := a ⊖ m
  set β := b ⊖ m
  refine ⟨by rintro _ (rfl | rfl); exacts [hma, hmb], fun l hl => ?_⟩
  have hla : l ≤ a := hl (Set.mem_insert _ _)
  have hlb : l ≤ b := hl (Set.mem_insert_of_mem _ rfl)
  -- intermezzo: `(⋀ aₙ)·(⋀ bₙ) ≤ aₙ·bₙ` for all `n`, and `⋁ aₙ·bₙ` exists, so it is `0`
  have hαβ : α * β = 0 := eq_zero_of_le_seqSummable (seqSummable_infTerm a b) fun n =>
    le_trans (emul_le_emul_right (hα.1 ⟨n, rfl⟩) β) (emul_le_emul_left _ (hβ.1 ⟨n, rfl⟩))
  -- `p ≡ ⌈⋀ bₙ⌉`: `p·⋀aₙ = 0` (OAP 34, OAP 20) and `p^⊥·⋀bₙ = 0` (OAP 19)
  set p := ceil β
  have hp : p * p = p := ceil_idem β
  have hpα : p * α = 0 := by rw [oap20 hp]; exact oap34 hαβ
  have hpβ : orth p * β = 0 := orth_emul_eq_zero_of_le hp (le_ceil β)
  -- `p·a = p·(a ∧ b)` and `p^⊥·b = p^⊥·(a ∧ b)`
  have hpa : p * a = p * m := by
    have e := oplus_osub hma
    obtain ⟨-, e'⟩ := mul_oplus p (perp_osub hma)
    rw [e, hpα, oplus_zero] at e'
    exact e'
  have hpb : orth p * b = orth p * m := by
    have e := oplus_osub hmb
    obtain ⟨-, e'⟩ := mul_oplus (orth p) (perp_osub hmb)
    rw [e, hpβ, oplus_zero] at e'
    exact e'
  -- `ℓ = p·ℓ ⋁ p^⊥·ℓ ≤ p·a ⋁ p^⊥·b = p·(a ∧ b) ⋁ p^⊥·(a ∧ b) = a ∧ b`
  obtain ⟨-, el⟩ := emul_oplus_orth_emul p l
  obtain ⟨hm, em⟩ := emul_oplus_orth_emul p m
  have := oplus_le_oplus (emul_le_emul_left p hla) (emul_le_emul_left (orth p) hlb)
    (by rw [hpa, hpb]; exact hm)
  rwa [el, hpa, hpb, em] at this

theorem isLUB_emSup (a b : M) : IsLUB {a, b} (emSup a b) := by
  apply isLUB_orth_of_isGLB
  rw [Set.image_pair]
  exact isGLB_emInf (orth a) (orth b)

/-- **OAP 37** (`thm:latticeemon`, first.tex:1238, Theorem): in an ω-complete
effect monoid any `a`, `b` have an infimum `a ∧ b = ⋁ₙ aₙ·bₙ` (the sum
existing), where `a₀ = a`, `b₀ = b`, `aₙ₊₁ = aₙ·bₙ^⊥`, `bₙ₊₁ = aₙ^⊥·bₙ`
(indices shifted down by one); consequently they have a supremum
`a ∨ b = (a^⊥ ∧ b^⊥)^⊥`. -/
theorem oap37 (a b : M) :
    HasOSum (infTerm a b) (emInf a b) ∧ IsGLB {a, b} (emInf a b) ∧
      IsLUB {a, b} (orth (emInf (orth a) (orth b))) :=
  ⟨oap27_nat.2 (hasSeqSum_emInf a b), isGLB_emInf a b, isLUB_emSup a b⟩

theorem emInf_le_left (a b : M) : emInf a b ≤ a := (isGLB_emInf a b).1 (Set.mem_insert _ _)

theorem emInf_le_right (a b : M) : emInf a b ≤ b :=
  (isGLB_emInf a b).1 (Set.mem_insert_of_mem _ rfl)

theorem le_emInf {a b c : M} (ha : c ≤ a) (hb : c ≤ b) : c ≤ emInf a b :=
  (isGLB_emInf a b).2 (by rintro _ (rfl | rfl); exacts [ha, hb])

theorem le_emSup_left (a b : M) : a ≤ emSup a b := (isLUB_emSup a b).1 (Set.mem_insert _ _)

theorem le_emSup_right (a b : M) : b ≤ emSup a b :=
  (isLUB_emSup a b).1 (Set.mem_insert_of_mem _ rfl)

theorem emSup_le {a b c : M} (ha : a ≤ c) (hb : b ≤ c) : emSup a b ≤ c :=
  (isLUB_emSup a b).2 (by rintro _ (rfl | rfl); exacts [ha, hb])

variable (M) in
/-- **OAP 37** (`thm:latticeemon`, first.tex:1238, Theorem): an ω-complete
effect monoid is a lattice (with the effect algebra order). -/
noncomputable def emLattice : Lattice M where
  __ := eaPartialOrder M
  sup := emSup
  inf := emInf
  le_sup_left := le_emSup_left
  le_sup_right := le_emSup_right
  sup_le _ _ _ := emSup_le
  inf_le_left := emInf_le_left
  inf_le_right := emInf_le_right
  le_inf _ _ _ := le_emInf

/-- **OAP 38** (`cor:intervalsuprema`, first.tex:1337, Corollary), suprema:
for `a ≤ b` and non-empty `S ⊆ [a,b]`, an element of `[a,b]` is the
supremum of `S` in `[a,b]` iff it is the supremum of `S` in `M`, and `S` has
a supremum in `M` iff it has one in `[a,b]`. -/
theorem oap38_sup {a b : M} (_hab : a ≤ b) {S : Set M} (hne : S.Nonempty)
    (hS : S ⊆ Set.Icc a b) :
    (∀ x : Set.Icc a b, IsLUB (Subtype.val ⁻¹' S : Set (Set.Icc a b)) x ↔ IsLUB S x.1) ∧
      ((∃ x : Set.Icc a b, IsLUB (Subtype.val ⁻¹' S : Set (Set.Icc a b)) x) ↔
        ∃ x, IsLUB S x) := by
  obtain ⟨s0, hs0⟩ := hne
  have key : ∀ x : Set.Icc a b, IsLUB (Subtype.val ⁻¹' S : Set (Set.Icc a b)) x ↔
      IsLUB S x.1 := by
    intro x
    constructor
    · intro hx
      refine ⟨fun s hs => hx.1 (show (⟨s, hS hs⟩ : Set.Icc a b) ∈ Subtype.val ⁻¹' S from hs),
        fun u hu => ?_⟩
      -- `b ∧ u` is an upper bound of `S` inside `[a,b]`
      have hv : emInf b u ∈ Set.Icc a b :=
        ⟨le_emInf (le_trans (hS hs0).1 (hS hs0).2) (le_trans (hS hs0).1 (hu hs0)),
          emInf_le_left b u⟩
      have : x ≤ ⟨emInf b u, hv⟩ := hx.2 fun s hs => le_emInf (hS hs).2 (hu hs)
      exact le_trans this (emInf_le_right b u)
    · intro hx
      exact ⟨fun s hs => hx.1 hs, fun y hy => hx.2 fun s hs =>
        hy (show (⟨s, hS hs⟩ : Set.Icc a b) ∈ Subtype.val ⁻¹' S from hs)⟩
  refine ⟨key, ⟨fun ⟨x, hx⟩ => ⟨x.1, (key x).1 hx⟩, fun ⟨x, hx⟩ => ?_⟩⟩
  have hmem : x ∈ Set.Icc a b := ⟨le_trans (hS hs0).1 (hx.1 hs0), hx.2 fun s hs => (hS hs).2⟩
  exact ⟨⟨x, hmem⟩, (key ⟨x, hmem⟩).2 hx⟩

/-- **OAP 38** (`cor:intervalsuprema`, first.tex:1337, Corollary), infima:
"Similar reasoning applies to infima of `S`." -/
theorem oap38_inf {a b : M} (_hab : a ≤ b) {S : Set M} (hne : S.Nonempty)
    (hS : S ⊆ Set.Icc a b) :
    (∀ x : Set.Icc a b, IsGLB (Subtype.val ⁻¹' S : Set (Set.Icc a b)) x ↔ IsGLB S x.1) ∧
      ((∃ x : Set.Icc a b, IsGLB (Subtype.val ⁻¹' S : Set (Set.Icc a b)) x) ↔
        ∃ x, IsGLB S x) := by
  obtain ⟨s0, hs0⟩ := hne
  have key : ∀ x : Set.Icc a b, IsGLB (Subtype.val ⁻¹' S : Set (Set.Icc a b)) x ↔
      IsGLB S x.1 := by
    intro x
    constructor
    · intro hx
      refine ⟨fun s hs => hx.1 (show (⟨s, hS hs⟩ : Set.Icc a b) ∈ Subtype.val ⁻¹' S from hs),
        fun u hu => ?_⟩
      -- `a ∨ u` is a lower bound of `S` inside `[a,b]`
      have hv : emSup a u ∈ Set.Icc a b :=
        ⟨le_emSup_left a u,
          emSup_le (le_trans (hS hs0).1 (hS hs0).2) (le_trans (hu hs0) (hS hs0).2)⟩
      have : (⟨emSup a u, hv⟩ : Set.Icc a b) ≤ x := hx.2 fun s hs => emSup_le (hS hs).1 (hu hs)
      exact le_trans (le_emSup_right a u) this
    · intro hx
      exact ⟨fun s hs => hx.1 hs, fun y hy => hx.2 fun s hs =>
        hy (show (⟨s, hS hs⟩ : Set.Icc a b) ∈ Subtype.val ⁻¹' S from hs)⟩
  refine ⟨key, ⟨fun ⟨x, hx⟩ => ⟨x.1, (key x).1 hx⟩, fun ⟨x, hx⟩ => ?_⟩⟩
  have hmem : x ∈ Set.Icc a b := ⟨hx.2 fun s hs => (hS hs).1, le_trans (hx.1 hs0) (hS hs0).2⟩
  exact ⟨⟨x, hmem⟩, (key ⟨x, hmem⟩).2 hx⟩

/-- **OAP 39** (`cor:sumomegaem`, first.tex:1371, Corollary), point 1: for
non-empty `S` with `a ⋁ s` defined for all `s ∈ S`, `⋁S` exists iff
`⋁ (a ⋁ S)` exists, and then `a ⋁ ⋁S = ⋁ (a ⋁ S)`. -/
theorem oap39_1 {a : M} {S : Set M} (hne : S.Nonempty) (hS : ∀ s ∈ S, Perp a s) :
    ((∃ m, IsLUB S m) ↔ ∃ j, IsLUB ((a ⋎ ·) '' S) j) ∧
      ∀ m, IsLUB S m → Perp a m ∧ IsLUB ((a ⋎ ·) '' S) (a ⋎ m) := by
  have hS' : ∀ s ∈ S, s ≤ orth a := fun s hs => le_orth_of_perp (hS s hs)
  have fwd : ∀ m, IsLUB S m → Perp a m ∧ IsLUB ((a ⋎ ·) '' S) (a ⋎ m) :=
    fun m hm => oap24_1 hne hS' hm
  refine ⟨⟨fun ⟨m, hm⟩ => ⟨_, (fwd m hm).2⟩, fun ⟨j, hj⟩ => ?_⟩, fwd⟩
  -- `a ⋁ (·) : [0, a^⊥] → [a, 1]` is an order isomorphism, so `j ⊖ a` is the
  -- supremum of `S` in `[0, a^⊥]`, hence in `M` (OAP 38)
  obtain ⟨s0, hs0⟩ := hne
  have haj : a ≤ j := le_trans (le_oplus_left (hS s0 hs0)) (hj.1 ⟨s0, hs0, rfl⟩)
  have hmem : j ⊖ a ∈ Set.Icc 0 (orth a) := ⟨zero_le' _, osub_le_orth haj⟩
  have hsub : S ⊆ Set.Icc 0 (orth a) := fun s hs => ⟨zero_le' s, hS' s hs⟩
  refine ⟨j ⊖ a, ((oap38_sup (zero_le' _) ⟨s0, hs0⟩ hsub).1 ⟨j ⊖ a, hmem⟩).1 ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs⟩ (hsS : s ∈ S)
    show s ≤ j ⊖ a
    rw [← oplus_le_oplus_left_iff (hS s hsS) (perp_osub haj), oplus_osub haj]
    exact hj.1 ⟨s, hsS, rfl⟩
  · rintro ⟨y, hy0, hy⟩ hyS
    show j ⊖ a ≤ y
    have hay : Perp a y := PCM.perp_comm (perp_iff_le_orth.2 hy)
    rw [← oplus_le_oplus_left_iff (perp_osub haj) hay, oplus_osub haj]
    refine hj.2 ?_
    rintro _ ⟨s, hs, rfl⟩
    exact oplus_le_oplus le_rfl (hyS (show (⟨s, hsub hs⟩ : Set.Icc 0 (orth a)) ∈
      Subtype.val ⁻¹' S from hs)) hay

/-- **OAP 39** (`cor:sumomegaem`, first.tex:1371, Corollary), point 2: for
non-empty `S` with `a ⋁ s` defined for all `s ∈ S`, `⋀S` exists iff
`⋀ (a ⋁ S)` exists, and then `a ⋁ ⋀S = ⋀ (a ⋁ S)`. -/
theorem oap39_2 {a : M} {S : Set M} (hne : S.Nonempty) (hS : ∀ s ∈ S, Perp a s) :
    ((∃ m, IsGLB S m) ↔ ∃ j, IsGLB ((a ⋎ ·) '' S) j) ∧
      ∀ m, IsGLB S m → Perp a m ∧ IsGLB ((a ⋎ ·) '' S) (a ⋎ m) := by
  have hS' : ∀ s ∈ S, s ≤ orth a := fun s hs => le_orth_of_perp (hS s hs)
  obtain ⟨s0, hs0⟩ := hne
  have fwd : ∀ m, IsGLB S m → Perp a m ∧ IsGLB ((a ⋎ ·) '' S) (a ⋎ m) := by
    intro m hm
    have ham : Perp a m := perp_of_le le_rfl (hm.1 hs0) (hS s0 hs0)
    refine ⟨ham, ?_⟩
    -- `a ⋁ ⋀S` is the infimum of `a ⋁ S` in `[a, 1]`, hence in `M` (OAP 38)
    have hsub : (a ⋎ ·) '' S ⊆ Set.Icc a 1 := by
      rintro _ ⟨s, hs, rfl⟩; exact ⟨le_oplus_left (hS s hs), le_one' _⟩
    refine ((oap38_inf (le_one' a) (Set.Nonempty.image (a ⋎ ·) ⟨s0, hs0⟩) hsub).1
      (⟨a ⋎ m, le_oplus_left ham, le_one' _⟩ : Set.Icc a 1)).1 ⟨?_, ?_⟩
    · rintro ⟨_, -⟩ ⟨s, hs, rfl⟩
      exact oplus_le_oplus le_rfl (hm.1 hs) (hS s hs)
    · intro y' hy
      obtain ⟨y, hay, hy1⟩ := y'
      show y ≤ a ⋎ m
      have hya : y ⊖ a ≤ m := hm.2 fun s hs => by
        rw [← oplus_le_oplus_left_iff (perp_osub hay) (hS s hs), oplus_osub hay]
        exact hy (show (⟨a ⋎ s, (hsub ⟨s, hs, rfl⟩)⟩ : Set.Icc a 1) ∈ Subtype.val ⁻¹' _ from
          ⟨s, hs, rfl⟩)
      calc y = a ⋎ (y ⊖ a) := (oplus_osub hay).symm
        _ ≤ a ⋎ m := oplus_le_oplus le_rfl hya ham
  refine ⟨⟨fun ⟨m, hm⟩ => ⟨_, (fwd m hm).2⟩, fun ⟨j, hj⟩ => ?_⟩, fwd⟩
  obtain ⟨m, hm, -, -⟩ := oap24_2 ⟨s0, hs0⟩ hS' hj
  exact ⟨m, hm⟩

end Omega

end Lattice

/-! ## Division (OAP 40–41) -/

section Division

variable {M : Type u} [EffectMonoid M]

/-- **OAP 40** (first.tex:1397, Definition): the **division**
`a/b ≡ ⋁ₙ a·(b^⊥)ⁿ` (for `a ≤ b` in an ω-complete effect monoid; junk
otherwise). -/
noncomputable def odiv (a b : M) : M := seqSum fun n => a * orth b ^ n

theorem seqSummable_odiv {a b : M} (h : a ≤ b) : SeqSummable fun n => a * orth b ^ n :=
  (psum_le_psum (seqSummable_mul_orth_pow b) fun _ => emul_le_emul_right h _).1

theorem psum_mul_left (a : M) {y : ℕ → M} (hy : SeqSummable y) :
    SeqSummable (fun n => a * y n) ∧ ∀ N, psum (fun n => a * y n) N = a * psum y N := by
  have key : ∀ N, psum (fun n => a * y n) N = a * psum y N := by
    intro N
    induction N with
    | zero => exact (emul_zero a).symm
    | succ N ih => rw [psum_succ, psum_succ, ih, (mul_oplus a (hy N)).2]
  exact ⟨fun N => by rw [key N]; exact (mul_oplus a (hy N)).1, key⟩

theorem psum_mul_right (a : M) {y : ℕ → M} (hy : SeqSummable y) :
    SeqSummable (fun n => y n * a) ∧ ∀ N, psum (fun n => y n * a) N = psum y N * a := by
  have key : ∀ N, psum (fun n => y n * a) N = psum y N * a := by
    intro N
    induction N with
    | zero => exact (ezero_mul a).symm
    | succ N ih => rw [psum_succ, psum_succ, ih, (oplus_mul a (hy N)).2]
  exact ⟨fun N => by rw [key N]; exact (oplus_mul a (hy N)).1, key⟩

theorem mul_orth_pow_comm (b : M) (n : ℕ) : b * orth b ^ n = orth b ^ n * b := by
  have := pow_orth_comm (orth b) n
  rw [orth_orth] at this
  exact this.symm

section Omega

variable [OmegaComplete M]

theorem hasSeqSum_odiv {a b : M} (h : a ≤ b) : HasSeqSum (fun n => a * orth b ^ n) (odiv a b) :=
  hasSeqSum_seqSum (seqSummable_odiv h)

/-- **OAP 40** (first.tex:1397, Definition): for `a ≤ b` the sum
`a/b = ⋁ₙ a·(b^⊥)ⁿ` exists, "because its partial sums lie below `⌈b⌉`". -/
theorem oap40 {a b : M} (h : a ≤ b) :
    HasOSum (fun n => a * orth b ^ n) (odiv a b) ∧ odiv a b ≤ ceil b :=
  ⟨oap27_nat.2 (hasSeqSum_odiv h),
    (hasSeqSum_odiv h).mono (hasSeqSum_ceil b) fun _ => emul_le_emul_right h _⟩

theorem odiv_le_ceil {a b : M} (h : a ≤ b) : odiv a b ≤ ceil b := (oap40 h).2

theorem odiv_mono {a a' b : M} (h : a ≤ a') (h' : a' ≤ b) : odiv a b ≤ odiv a' b :=
  (hasSeqSum_odiv (le_trans h h')).mono (hasSeqSum_odiv h') fun _ => emul_le_emul_right h _

omit [OmegaComplete M] in
/-- **OAP 41** (`lem:div`, first.tex:1409, Lemma), point 1: `b/b = ⌈b⌉`. -/
theorem oap41_1 (b : M) : odiv b b = ceil b := rfl

/-- **OAP 41** (`lem:div`, first.tex:1409, Lemma), point 2:
`(a₁ ⋁ a₂)/b = a₁/b ⋁ a₂/b` for summable `a₁`, `a₂` with `a₁ ⋁ a₂ ≤ b`. -/
theorem oap41_2 {a₁ a₂ b : M} (h : Perp a₁ a₂) (hb : a₁ ⋎ a₂ ≤ b) :
    Perp (odiv a₁ b) (odiv a₂ b) ∧ odiv (a₁ ⋎ a₂) b = odiv a₁ b ⋎ odiv a₂ b := by
  have h1 : a₁ ≤ b := le_trans (le_oplus_left h) hb
  have h2 : a₂ ≤ b := le_trans (le_oplus_right h) hb
  have e : (fun n => a₁ * orth b ^ n ⋎ a₂ * orth b ^ n) = fun n => (a₁ ⋎ a₂) * orth b ^ n :=
    funext fun n => (oplus_mul _ h).2.symm
  have hs : SeqSummable fun n => a₁ * orth b ^ n ⋎ a₂ * orth b ^ n := by
    rw [e]; exact seqSummable_odiv hb
  obtain ⟨hp, hsum⟩ := (hasSeqSum_odiv h1).oplus (fun n => (oplus_mul _ h).1) hs
    (hasSeqSum_odiv h2)
  rw [e] at hsum
  exact ⟨hp, (hasSeqSum_odiv hb).unique hsum⟩

/-- `(a·c)/b ≤ a·(c/b)` for `c ≤ b` (the first display in the proof of
OAP 41, point 3). -/
theorem odiv_mul_le (a : M) {c b : M} (hc : c ≤ b) : odiv (a * c) b ≤ a * odiv c b := by
  have hac : a * c ≤ b := le_trans (emul_le_right a c) hc
  refine (hasSeqSum_odiv hac).2.2 ?_
  rintro _ ⟨N, rfl⟩
  have e : (fun n => a * c * orth b ^ n) = fun n => a * (c * orth b ^ n) :=
    funext fun n => emul_assoc _ _ _
  show psum (fun n => a * c * orth b ^ n) N ≤ a * odiv c b
  rw [e, (psum_mul_left a (seqSummable_odiv hc)).2 N]
  exact emul_le_emul_left a ((hasSeqSum_odiv hc).psum_le N)

/-- **OAP 41** (`lem:div`, first.tex:1409, Lemma), point 3:
`(a·b)/b = a·⌈b⌉`. -/
theorem oap41_3 (a b : M) : odiv (a * b) b = a * ceil b := by
  obtain ⟨hp, e⟩ := emul_oplus_orth_emul a b
  have h1 : odiv (a * b) b ≤ a * ceil b := odiv_mul_le a le_rfl
  have h2 : odiv (orth a * b) b ≤ orth a * ceil b := odiv_mul_le (orth a) le_rfl
  obtain ⟨-, e'⟩ := oap41_2 hp (le_of_eq e)
  rw [e] at e'
  obtain ⟨hq, eq⟩ := emul_oplus_orth_emul a (ceil b)
  -- `⌈b⌉ = b/b = (a·b)/b ⋁ (a^⊥·b)/b ≤ a·⌈b⌉ ⋁ a^⊥·⌈b⌉ = ⌈b⌉`: forcing (OAP 22)
  refine (oap22_forcing h1 h2 hq ?_).1
  rw [eq, ← e']
  exact le_rfl

/-- `a ≤ (a/b)·b` for `a ≤ b` (in the proof of OAP 41, point 4). -/
theorem le_odiv_mul {a b : M} (h : a ≤ b) : a ≤ odiv a b * b := by
  have hab : a * b ≤ b := emul_le_right a b
  calc a = a * ceil b := (emul_eq_of_le' (ceil_idem b) (le_trans h (le_ceil b))).symm
    _ = odiv (a * b) b := (oap41_3 a b).symm
    _ ≤ odiv a b * b := (hasSeqSum_odiv hab).2.2 (by
        rintro _ ⟨N, rfl⟩
        have e : (fun n => a * b * orth b ^ n) = fun n => a * orth b ^ n * b :=
          funext fun n => by rw [emul_assoc, mul_orth_pow_comm, emul_assoc]
        show psum (fun n => a * b * orth b ^ n) N ≤ odiv a b * b
        rw [e, (psum_mul_right b (seqSummable_odiv h)).2 N]
        exact emul_le_emul_right ((hasSeqSum_odiv h).psum_le N) b)

/-- **OAP 41** (`lem:div`, first.tex:1409, Lemma), point 4: `(a/b)·b = a`
for `a ≤ b`. -/
theorem oap41_4 {a b : M} (h : a ≤ b) : odiv a b * b = a := by
  have h1 := le_odiv_mul h
  have h2 := le_odiv_mul (osub_le h)
  obtain ⟨hp, e⟩ := oap41_2 (perp_osub h) (le_of_eq (oplus_osub h))
  rw [oplus_osub h] at e
  obtain ⟨hq, eq⟩ := oplus_mul b hp
  -- `b = a ⋁ (b ⊖ a) ≤ (a/b)·b ⋁ ((b ⊖ a)/b)·b = (b/b)·b = ⌈b⌉·b = b`: forcing
  refine ((oap22_forcing h1 h2 hq ?_).1).symm
  rw [← eq, ← e, oplus_osub h]
  exact le_of_eq (emul_eq_of_le (ceil_idem b) (le_ceil b))

/-- **OAP 41** (`lem:div`, first.tex:1409, Lemma), point 5:
`Mb = {a·b ; a ∈ M} = [0, b]`. -/
theorem oap41_5 (b : M) : Set.range (fun a => a * b) = Set.Iic b := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact emul_le_right a b
  · intro hx; exact ⟨odiv x b, oap41_4 hx⟩

end Omega

/-- An order isomorphism `[0, c] ≅ [0, d]` from mutually inverse monotone
maps. -/
def isoIic {c d : M} (f g : M → M) (hf : ∀ x ≤ c, f x ≤ d) (hg : ∀ y ≤ d, g y ≤ c)
    (gf : ∀ x ≤ c, g (f x) = x) (fg : ∀ y ≤ d, f (g y) = y) (fm : Monotone f)
    (gm : ∀ y y', y' ≤ d → y ≤ y' → g y ≤ g y') : Set.Iic c ≃o Set.Iic d where
  toFun x := ⟨f x, hf x x.2⟩
  invFun y := ⟨g y, hg y y.2⟩
  left_inv x := Subtype.ext (gf x x.2)
  right_inv y := Subtype.ext (fg y y.2)
  map_rel_iff' {x x'} := by
    constructor
    · intro h
      have h' : f x.1 ≤ f x'.1 := h
      have := gm _ _ (hf _ x'.2) h'
      rw [gf _ x.2, gf _ x'.2] at this
      exact this
    · intro h; exact fm (show x.1 ≤ x'.1 from h)

theorem isoIic_apply {c d : M} (f g : M → M) (hf : ∀ x ≤ c, f x ≤ d) (hg : ∀ y ≤ d, g y ≤ c)
    (gf : ∀ x ≤ c, g (f x) = x) (fg : ∀ y ≤ d, f (g y) = y) (fm : Monotone f)
    (gm : ∀ y y', y' ≤ d → y ≤ y' → g y ≤ g y') (x : Set.Iic c) :
    (isoIic f g hf hg gf fg fm gm x : M) = f x := rfl

variable [OmegaComplete M]

/-- The order isomorphism `a ↦ a·b : [0, ⌈b⌉] → [0, b]`, with inverse
`a ↦ a/b`. -/
noncomputable def mulRightIso (b : M) : Set.Iic (ceil b) ≃o Set.Iic b :=
  isoIic (· * b) (odiv · b) (fun x _ => emul_le_right x b) (fun _ hy => odiv_le_ceil hy)
    (fun x hx => by
      show odiv (x * b) b = x
      rw [oap41_3]; exact emul_eq_of_le' (ceil_idem b) hx)
    (fun _ hy => oap41_4 hy) (fun _ _ h => emul_le_emul_right h b)
    (fun _ _ hy' h => odiv_mono h hy')

end Division

/-! ## The opposite effect monoid -/

/-- The **opposite** of an effect monoid `M`: the same effect algebra, with
multiplication `a ·ᵒᵖ b = b·a`.  Mirror images of statements about `M` are
obtained by instantiating them at `EMOp M`. -/
def EMOp (M : Type u) : Type u := M

section Op

variable {M : Type u} [EffectMonoid M]

instance : EffectMonoid (EMOp M) :=
  letI : EffectAlgebra (EMOp M) := inferInstanceAs (EffectAlgebra M)
  letI : Mul (EMOp M) := ⟨fun a b => @HMul.hMul M M M _ b a⟩
  EffectMonoid.ofBiadditive (EMOp M) (fun a => emul_one (M := M) a)
    (fun a => eone_mul (M := M) a) (fun a b c => emul_assoc (M := M) c b a)
    (fun a _ _ h => oplus_mul (M := M) a h) (fun a _ _ h => mul_oplus (M := M) a h)

instance [OmegaComplete M] : OmegaComplete (EMOp M) :=
  ⟨fun f hf => OmegaComplete.exists_isLUB (E := M) f hf⟩

theorem ceil_op [OmegaComplete M] (a : M) : ceil (M := EMOp M) a = ceil a := by
  have h1 : IsLeast {p : M | p * p = p ∧ a ≤ p} (ceil (M := EMOp M) a) :=
    oap35_2 (M := EMOp M) a
  exact h1.unique (oap35_2 a)

/-- The mirror division `b\a ≡ ⋁ₙ (b^⊥)ⁿ·a` (the proof of OAP 41, point 6):
the division of the opposite effect monoid. -/
noncomputable def ldiv (b a : M) : M := odiv (M := EMOp M) a b

variable [OmegaComplete M]

theorem ldiv_self (b : M) : ldiv b b = ceil b := ceil_op b

theorem mul_ldiv {a b : M} (h : a ≤ b) : b * ldiv b a = a := oap41_4 (M := EMOp M) h

theorem ldiv_mul (a b : M) : ldiv b (b * a) = ceil b * a := by
  have := oap41_3 (M := EMOp M) a b
  rw [ceil_op] at this
  exact this

theorem ldiv_le_ceil {a b : M} (h : a ≤ b) : ldiv b a ≤ ceil b := by
  have := odiv_le_ceil (M := EMOp M) h
  rw [ceil_op] at this
  exact this

theorem ldiv_mono {a a' b : M} (h : a ≤ a') (h' : a' ≤ b) : ldiv b a ≤ ldiv b a' :=
  odiv_mono (M := EMOp M) h h'

/-- **OAP 41** (`lem:div`, first.tex:1409, Lemma), point 5, mirrored (used in
the proof of point 6): `bM = [0, b]`. -/
theorem oap41_5' (b : M) : Set.range (fun a => b * a) = Set.Iic b := oap41_5 (M := EMOp M) b

/-- The order isomorphism `a ↦ b·a : [0, ⌈b⌉] → [0, b]`, with inverse
`a ↦ b\a`. -/
noncomputable def mulLeftIso (b : M) : Set.Iic (ceil b) ≃o Set.Iic b :=
  isoIic (b * ·) (ldiv b ·) (fun x _ => emul_le_left b x) (fun _ hy => ldiv_le_ceil hy)
    (fun x hx => by
      show ldiv b (b * x) = x
      rw [ldiv_mul]; exact emul_eq_of_le (ceil_idem b) hx)
    (fun _ hy => mul_ldiv hy) (fun _ _ h => emul_le_emul_left b h)
    (fun _ _ hy' h => ldiv_mono h hy')

/-- **OAP 41** (`lem:div`, first.tex:1409, Lemma), point 6: the maps
`a ↦ a·b` and `a ↦ b·a` are order isomorphisms `M⌈b⌉ → Mb`; here
`M⌈b⌉ = [0, ⌈b⌉]` and `Mb = [0, b]` by point 5. -/
theorem oap41_6 (b : M) :
    Set.range (fun a => a * ceil b) = Set.Iic (ceil b) ∧ Set.range (fun a => a * b) = Set.Iic b ∧
    (∃ e : Set.Iic (ceil b) ≃o Set.Iic b, ∀ x, (e x : M) = x * b) ∧
      ∃ e : Set.Iic (ceil b) ≃o Set.Iic b, ∀ x, (e x : M) = b * x :=
  ⟨oap41_5 (ceil b), oap41_5 b, ⟨mulRightIso b, fun _ => rfl⟩, ⟨mulLeftIso b, fun _ => rfl⟩⟩

end Op

/-! ## Normality of multiplication (OAP 43) -/

section Normal

variable {M : Type u} [EffectMonoid M] [OmegaComplete M]

omit [OmegaComplete M] in
/-- An element above both `p` and `p^⊥`, for an idempotent `p`, is `1`. -/
theorem eq_one_of_le_of_orth_le {p u : M} (hp : p * p = p) (h1 : p ≤ u) (h2 : orth p ≤ u) :
    u = 1 := by
  have e1 : p * u = p := le_antisymm (emul_le_left p u)
    (le_of_eq_of_le hp.symm (emul_le_emul_left p h1))
  have e2 : orth p * u = orth p := le_antisymm (emul_le_left _ u)
    (le_of_eq_of_le (idem_orth hp).symm (emul_le_emul_left (orth p) h2))
  obtain ⟨-, e⟩ := emul_oplus_orth_emul p u
  rw [e1, e2, oplus_orth] at e
  exact e.symm

/-- `c ≡ b ⋁ ⌈b⌉^⊥` has `⌈c⌉ = ⌈b⌉ ∨ ⌈b⌉^⊥ = 1` (OAP 36). -/
theorem ceil_oplus_orth_ceil (b : M) :
    Perp b (orth (ceil b)) ∧ ceil (b ⋎ orth (ceil b)) = 1 := by
  have hbp : Perp b (orth (ceil b)) := perp_iff_le_orth.2 (by rw [orth_orth]; exact le_ceil b)
  refine ⟨hbp, ?_⟩
  have h := (oap36 hbp).1
  rw [ceil_of_idem (idem_orth (ceil_idem b))] at h
  exact eq_one_of_le_of_orth_le (ceil_idem b) (h (Set.mem_insert _ _))
    (h (Set.mem_insert_of_mem _ rfl))

/-- `(·)·c` preserves suprema when `⌈c⌉ = 1`: it is then an order
isomorphism `M → [0, c]` (OAP 41, point 6), and suprema in `[0, c]` are
suprema in `M` (OAP 38). -/
theorem isLUB_mul_of_ceil_eq_one {c : M} (hc : ceil c = 1) {S : Set M} (hne : S.Nonempty)
    {m : M} (h : IsLUB S m) : IsLUB ((· * c) '' S) (m * c) := by
  have hsub : (· * c) '' S ⊆ Set.Icc 0 c := by
    rintro _ ⟨s, -, rfl⟩; exact ⟨zero_le' _, emul_le_right s c⟩
  refine ((oap38_sup (zero_le' c) (Set.Nonempty.image _ hne) hsub).1
    (⟨m * c, zero_le' _, emul_le_right m c⟩ : Set.Icc 0 c)).1 ⟨?_, ?_⟩
  · rintro ⟨_, -⟩ ⟨s, hs, rfl⟩
    exact emul_le_emul_right (h.1 hs) c
  · intro y' hy
    obtain ⟨y, hy0, hyc⟩ := y'
    show m * c ≤ y
    have hm : m ≤ odiv y c := h.2 fun s hs => by
      have hsy : s * c ≤ y := hy (show (⟨s * c, hsub ⟨s, hs, rfl⟩⟩ : Set.Icc 0 c) ∈
        Subtype.val ⁻¹' _ from ⟨s, hs, rfl⟩)
      have := odiv_mono hsy hyc
      rwa [oap41_3, hc, emul_one] at this
    calc m * c ≤ odiv y c * c := emul_le_emul_right hm c
      _ = y := oap41_4 hyc

/-- `(·)·c` preserves infima when `⌈c⌉ = 1`. -/
theorem isGLB_mul_of_ceil_eq_one {c : M} (hc : ceil c = 1) {S : Set M} (hne : S.Nonempty)
    {m : M} (h : IsGLB S m) : IsGLB ((· * c) '' S) (m * c) := by
  have hsub : (· * c) '' S ⊆ Set.Icc 0 c := by
    rintro _ ⟨s, -, rfl⟩; exact ⟨zero_le' _, emul_le_right s c⟩
  refine ((oap38_inf (zero_le' c) (Set.Nonempty.image _ hne) hsub).1
    (⟨m * c, zero_le' _, emul_le_right m c⟩ : Set.Icc 0 c)).1 ⟨?_, ?_⟩
  · rintro ⟨_, -⟩ ⟨s, hs, rfl⟩
    exact emul_le_emul_right (h.1 hs) c
  · intro y' hy
    obtain ⟨y, hy0, hyc⟩ := y'
    show y ≤ m * c
    have hm : odiv y c ≤ m := h.2 fun s hs => by
      have hsy : y ≤ s * c := hy (show (⟨s * c, hsub ⟨s, hs, rfl⟩⟩ : Set.Icc 0 c) ∈
        Subtype.val ⁻¹' _ from ⟨s, hs, rfl⟩)
      have := odiv_mono hsy (emul_le_right s c)
      rwa [oap41_3, hc, emul_one] at this
    calc y = odiv y c * c := (oap41_4 hyc).symm
      _ ≤ m * c := emul_le_emul_right hm c

/-- OAP 43, point 1, for right multiplication: `(⋁S)·b = ⋁_{s∈S} s·b`. -/
theorem isLUB_mul_right {S : Set M} (hne : S.Nonempty) {m : M} (h : IsLUB S m) (b : M) :
    IsLUB ((· * b) '' S) (m * b) := by
  obtain ⟨hbp, hc⟩ := ceil_oplus_orth_ceil b
  set p := ceil b
  set c := b ⋎ orth p
  have hcS := isLUB_mul_of_ceil_eq_one hc hne h
  refine ⟨by rintro _ ⟨s, hs, rfl⟩; exact emul_le_emul_right (h.1 hs) b, fun u hu => ?_⟩
  -- replace the upper bound `u` by `u' ≡ u ∧ (⋁S)·b ≤ ⌈b⌉`
  set u' := emInf u (m * b)
  have hu' : ∀ s ∈ S, s * b ≤ u' := fun s hs =>
    le_emInf (hu ⟨s, hs, rfl⟩) (emul_le_emul_right (h.1 hs) b)
  have hu'p : u' ≤ p := le_trans (emInf_le_right _ _) (le_trans (emul_le_right m b) (le_ceil b))
  have hq : Perp u' (m * orth p) := perp_of_le hu'p (emul_le_right m (orth p)) (perp_orth p)
  -- `(⋁S)·c = ⋁ s·c ≤ u' ⋁ (⋁S)·⌈b⌉^⊥`, then cancel `(⋁S)·⌈b⌉^⊥`
  have key : m * c ≤ u' ⋎ m * orth p := hcS.2 (by
    rintro _ ⟨s, hs, rfl⟩
    show s * (b ⋎ orth p) ≤ u' ⋎ m * orth p
    rw [(mul_oplus s hbp).2]
    exact oplus_le_oplus (hu' s hs) (emul_le_emul_right (h.1 hs) _) hq)
  have hm := mul_oplus m hbp
  rw [hm.2, oplus_comm (m * b), oplus_comm u'] at key
  exact le_trans ((oplus_le_oplus_left_iff (PCM.perp_comm hm.1) (PCM.perp_comm hq)).1 key)
    (emInf_le_left _ _)

/-- OAP 43, point 2, for right multiplication: `(⋀S)·b = ⋀_{s∈S} s·b`. -/
theorem isGLB_mul_right {S : Set M} (hne : S.Nonempty) {m : M} (h : IsGLB S m) (b : M) :
    IsGLB ((· * b) '' S) (m * b) := by
  obtain ⟨hbp, hc⟩ := ceil_oplus_orth_ceil b
  set p := ceil b
  set c := b ⋎ orth p
  have hcS := isGLB_mul_of_ceil_eq_one hc hne h
  refine ⟨by rintro _ ⟨s, hs, rfl⟩; exact emul_le_emul_right (h.1 hs) b, fun l hl => ?_⟩
  obtain ⟨s0, hs0⟩ := hne
  have hlp : l ≤ p := le_trans (hl ⟨s0, hs0, rfl⟩) (le_trans (emul_le_right s0 b) (le_ceil b))
  have hq : Perp l (m * orth p) := perp_of_le hlp (emul_le_right m (orth p)) (perp_orth p)
  -- `ℓ ⋁ (⋀S)·⌈b⌉^⊥ ≤ s·b ⋁ s·⌈b⌉^⊥ = s·c`, so `≤ (⋀S)·c`; cancel
  have key : l ⋎ m * orth p ≤ m * c := hcS.2 (by
    rintro _ ⟨s, hs, rfl⟩
    show l ⋎ m * orth p ≤ s * (b ⋎ orth p)
    rw [(mul_oplus s hbp).2]
    exact oplus_le_oplus (hl ⟨s, hs, rfl⟩) (emul_le_emul_right (h.1 hs) _) (mul_oplus s hbp).1)
  have hm := mul_oplus m hbp
  rw [hm.2, oplus_comm l, oplus_comm (m * b)] at key
  exact (oplus_le_oplus_left_iff (PCM.perp_comm hq) (PCM.perp_comm hm.1)).1 key

/-- OAP 43, point 1, for left multiplication: `b·⋁S = ⋁_{s∈S} b·s` (the case
the print proves; here the mirror image of `isLUB_mul_right`). -/
theorem isLUB_mul_left {S : Set M} (hne : S.Nonempty) {m : M} (h : IsLUB S m) (b : M) :
    IsLUB ((b * ·) '' S) (b * m) :=
  isLUB_mul_right (M := EMOp M) hne h b

/-- OAP 43, point 2, for left multiplication: `b·⋀S = ⋀_{s∈S} b·s`. -/
theorem isGLB_mul_left {S : Set M} (hne : S.Nonempty) {m : M} (h : IsGLB S m) (b : M) :
    IsGLB ((b * ·) '' S) (b * m) :=
  isGLB_mul_right (M := EMOp M) hne h b

/-- **OAP 43** (`thm:multisnormal`, first.tex:1525, Theorem), point 1: for
non-empty `S ⊆ M`, if `⋁S` exists then so does `⋁_{s∈S} b·s·b'`, and
`b·(⋁S)·b' = ⋁_{s∈S} b·s·b'`. -/
theorem oap43_1 {S : Set M} (hne : S.Nonempty) {m : M} (h : IsLUB S m) (b b' : M) :
    IsLUB ((fun s => b * s * b') '' S) (b * m * b') := by
  have h2 := isLUB_mul_left (Set.Nonempty.image _ hne) (isLUB_mul_right hne h b') b
  rw [Set.image_image] at h2
  have e : (fun s => b * s * b') = fun s => b * (s * b') := funext fun s => emul_assoc _ _ _
  rw [e, emul_assoc]
  exact h2

/-- **OAP 43** (`thm:multisnormal`, first.tex:1525, Theorem), point 2: for
non-empty `S ⊆ M`, if `⋀S` exists then so does `⋀_{s∈S} b·s·b'`, and
`b·(⋀S)·b' = ⋀_{s∈S} b·s·b'`. -/
theorem oap43_2 {S : Set M} (hne : S.Nonempty) {m : M} (h : IsGLB S m) (b b' : M) :
    IsGLB ((fun s => b * s * b') '' S) (b * m * b') := by
  have h2 := isGLB_mul_left (Set.Nonempty.image _ hne) (isGLB_mul_right hne h b') b
  rw [Set.image_image] at h2
  have e : (fun s => b * s * b') = fun s => b * (s * b') := funext fun s => emul_assoc _ _ _
  rw [e, emul_assoc]
  exact h2

end Normal

/-! ## Effect divisoids (OAP 42) -/

section Divisoid

variable (M : Type u) [EffectMonoid M] [OmegaComplete M]

/-- **OAP 42** (first.tex:1511, Remark): "any ω-complete effect monoid is a
so called *effect divisoid*" (thesis B, 195II; the tree's
`Theses.B.Eff.EffectDivisoid`).  The thesis' division `a/b` satisfies
`b·(a/b) = a`, so it is the mirror division `b\a` of the proof of OAP 41
(point 6), i.e. the division of the opposite effect monoid.  The converse
("there is a non-commutative effect divisoid", citing Cho's thesis, together
with OAP 70) is not formalised here. -/
noncomputable def oap42_divisoid : EffectDivisoid M where
  div a b := ldiv b a
  div_le {a b} h := by
    show ldiv b a ≤ ldiv b b
    rw [ldiv_self]; exact ldiv_le_ceil h
  mul_div {a b} h := mul_ldiv h
  div_unique {a b c} _ hc e := by
    have hc' : c ≤ ceil b := by rw [← ldiv_self]; exact hc
    show c = ldiv b a
    rw [← e, ldiv_mul, emul_eq_of_le (ceil_idem b) hc']
  le_div_self a := by show a ≤ ldiv a a; rw [ldiv_self]; exact le_ceil a
  div_div_self a := by
    show ldiv (ldiv a a) (ldiv a a) = ldiv a a
    rw [ldiv_self, ldiv_self, ceil_of_idem (ceil_idem a)]

end Divisoid

end Papers.OAP
