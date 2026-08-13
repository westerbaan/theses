/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 2: Von Neumann Algebras — vn.tex, lines 2183–3780.

  §Projections
    parsec 550: projections in a C*-algebra
    Ceiling and Floor       (parsecs 560–580)
    Range and Support       (parsecs 590–620)
    Carrier and Commutant   (parsecs 630–660)
    Central Support and Central Carrier  (parsecs 670–700)

Statements only; every proof is `sorry`.  See CONVENTIONS.md for the
numbering and naming conventions, and `Theses/A/VN/Basic.lean` for the
encoding of the ultraweak/ultrastrong topologies.

The ceiling `⌈b⌉`, floor `⌊b⌋`, suprema/infima of projections, carriers and
central supports are actual (noncomputable) definitions, obtained by choice
from `sorry`-ed existence-and-uniqueness lemmas.
-/
import Theses.A.VN.Basic

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
open Filter Topology Theses Theses.A.CStar

namespace Theses.A.VN

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-! ## Parsec 550: projections

**55I** (vn.tex:2185): overview — nothing to formalize.

**55II** (vn.tex:2204, Definition): an element `p` of a C*-algebra is a
**projection** when `p* p = p`.  This is Mathlib's `IsStarProjection`
(idempotent and self-adjoint, an equivalent rendering).

**55III** (vn.tex:2210, Examples): the projections of `ℂ`, `L^∞(X)` and
`B(H)` — descriptive examples, not converted. -/

/-! ### Auxiliary: effects versus a projection

The two workhorses of parsec 550 are:  for an effect `b` and a projection
`p`,  `b ≤ p  ↔  b p^⊥ = 0`  and  `p ≤ b  ↔  p b^⊥ = 0`.  Everything in
**55VIII**–**55X** is an instance of one of them (applied to `b`, `√b` or
`b²`), and the argument is exactly the one the thesis gives for **55X**:
conjugate by `p^⊥` (resp. `p`) and use the C*-identity. -/

section EffectsAux

theorem norm_le_one_of_mem_effects {a : A} (ha : a ∈ effects A) : ‖a‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg a ha.1).mpr ha.2

/-- `a² ≤ a` for an effect `a`. -/
theorem mul_self_le_self {a : A} (ha : a ∈ effects A) : a * a ≤ a := by
  refine (mul_self_le_norm_smul ha.1).trans ?_
  have h := smul_nonneg
    (by linarith [norm_le_one_of_mem_effects ha] : (0 : ℝ) ≤ 1 - ‖a‖) ha.1
  rw [sub_smul, one_smul, sub_nonneg] at h
  exact h

theorem sqrt_mem_effects {a : A} (ha : a ∈ effects A) :
    CFC.sqrt a ∈ effects A :=
  ⟨CFC.sqrt_nonneg a, by simpa using CFC.sqrt_le_sqrt a 1 ha.2⟩

theorem sq_mem_effects {a : A} (ha : a ∈ effects A) : a ^ 2 ∈ effects A := by
  have h2 : a ^ 2 = a * a := sq a
  refine ⟨h2 ▸ ?_, h2 ▸ (mul_self_le_self ha).trans ha.2⟩
  simpa [(IsSelfAdjoint.of_nonneg ha.1).star_eq] using star_mul_self_nonneg a

/-- `1 ≥ b ≥ b² ≥ b⁴ ≥ ⋯ ≥ 0` (the opening line of the proof of **56VI**):
the powers of an effect decrease.  `b^{n+1} ≤ b^n` is `b ≤ 1` conjugated by
`b^k` when `n = 2k`, and `b² ≤ b` conjugated by `b^k` when `n = 2k+1`. -/
theorem pow_antitone_of_mem_effects {b : A} (hb : b ∈ effects A) :
    Antitone (fun n : ℕ => b ^ n) := by
  refine antitone_nat_of_succ_le fun n => ?_
  have hsa : ∀ k : ℕ, star (b ^ k) = b ^ k := fun k =>
    ((IsSelfAdjoint.of_nonneg hb.1).pow k).star_eq
  have hcat : ∀ i j : ℕ, b ^ i * b * b ^ j = b ^ (i + 1 + j) := fun i j => by
    rw [← pow_succ, ← pow_add]
  have hcat2 : ∀ i j : ℕ, b ^ i * (b * b) * b ^ j = b ^ (i + 2 + j) := fun i j => by
    rw [← sq, ← pow_add, ← pow_add]
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `n = 2k`: `b^{2k+1} = b^k b b^k ≤ b^k 1 b^k = b^{2k}`
    have h := star_left_conjugate_le_conjugate hb.2 (b ^ k)
    rw [hsa k, mul_one] at h
    calc b ^ (n + 1) = b ^ k * b * b ^ k := by rw [hcat, hk]; congr 1; omega
      _ ≤ b ^ k * b ^ k := h
      _ = b ^ n := by rw [← pow_add, hk]
  · -- `n = 2k+1`: `b^{2k+2} = b^k b² b^k ≤ b^k b b^k = b^{2k+1}`
    have h := star_left_conjugate_le_conjugate (mul_self_le_self hb) (b ^ k)
    rw [hsa k] at h
    calc b ^ (n + 1) = b ^ k * (b * b) * b ^ k := by
          rw [hcat2, hk]; congr 1; omega
      _ ≤ b ^ k * b * b ^ k := h
      _ = b ^ n := by rw [hcat, hk]; congr 1; omega

/-- Powers of an effect are effects. -/
theorem pow_mem_effects {b : A} (hb : b ∈ effects A) (n : ℕ) :
    b ^ n ∈ effects A := by
  refine ⟨?_, by simpa using pow_antitone_of_mem_effects hb (Nat.zero_le n)⟩
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have h : (0 : A) ≤ star (b ^ k) * (b ^ k) := star_mul_self_nonneg _
    rw [((IsSelfAdjoint.of_nonneg hb.1).pow k).star_eq, ← pow_add] at h
    rwa [hk]
  · have h := star_left_conjugate_nonneg hb.1 (b ^ k)
    rw [((IsSelfAdjoint.of_nonneg hb.1).pow k).star_eq] at h
    have he : b ^ k * b * b ^ k = b ^ n := by
      rw [← pow_succ, ← pow_add, hk]; congr 1; omega
    rwa [he] at h

/-- For `0 ≤ b` and any `c`, `b c = 0` iff `√b c = 0`: multiply on the left
by `c*` and use the C*-identity. -/
theorem sqrt_mul_eq_zero_iff {b : A} (hb : 0 ≤ b) (c : A) :
    CFC.sqrt b * c = 0 ↔ b * c = 0 := by
  constructor
  · intro h
    rw [← CFC.sqrt_mul_sqrt_self b hb, mul_assoc, h, mul_zero]
  · intro h
    rw [← CStarRing.star_mul_self_eq_zero_iff (CFC.sqrt b * c), star_mul,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq]
    calc star c * CFC.sqrt b * (CFC.sqrt b * c)
        = star c * (CFC.sqrt b * CFC.sqrt b * c) := by noncomm_ring
      _ = star c * (b * c) := by rw [CFC.sqrt_mul_sqrt_self b hb]
      _ = 0 := by rw [h, mul_zero]

/-- **Key lemma 1**: an effect `b` lies below a projection `p` iff
`b p^⊥ = 0`. -/
theorem le_proj_iff {b p : A} (hb : b ∈ effects A) (hp : IsStarProjection p) :
    b ≤ p ↔ b * (1 - p) = 0 := by
  constructor
  · intro h
    rw [mul_sub, mul_one,
      (hp.mul_right_and_mul_left_of_nonneg_of_le hb.1 h).1, sub_self]
  · intro h
    have hbp : b * p = b := by
      have := h; rw [mul_sub, mul_one, sub_eq_zero] at this; exact this.symm
    have hpb : p * b = b := by
      simpa [(IsSelfAdjoint.of_nonneg hb.1).star_eq, hp.isSelfAdjoint.star_eq]
        using congrArg star hbp
    have hcon := star_left_conjugate_le_conjugate hb.2 p
    rw [hp.isSelfAdjoint.star_eq, mul_one, hp.isIdempotentElem.eq] at hcon
    rwa [hpb, hbp] at hcon

/-- **Key lemma 2**: a projection `p` lies below an effect `b` iff
`p b^⊥ = 0`. -/
theorem proj_le_iff {b p : A} (hb : b ∈ effects A) (hp : IsStarProjection p) :
    p ≤ b ↔ p * (1 - b) = 0 := by
  have hb' : (0 : A) ≤ 1 - b := sub_nonneg.mpr hb.2
  constructor
  · intro h
    -- `p(1-b)p ≤ p(1-p)p = 0` and `p(1-b)p = (√(1-b) p)* (√(1-b) p) ≥ 0`
    have hcon : p * (1 - b) * p ≤ p * (1 - p) * p := by
      have := star_left_conjugate_le_conjugate (sub_le_sub_left h 1) p
      rwa [hp.isSelfAdjoint.star_eq] at this
    rw [hp.mul_one_sub_self, zero_mul] at hcon
    have hnn : (0 : A) ≤ p * (1 - b) * p := by
      have := star_left_conjugate_nonneg hb' p
      rwa [hp.isSelfAdjoint.star_eq] at this
    have hzero : p * (1 - b) * p = 0 := le_antisymm hcon hnn
    have hsq : star (CFC.sqrt (1 - b) * p) * (CFC.sqrt (1 - b) * p) = 0 := by
      rw [star_mul, hp.isSelfAdjoint.star_eq,
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1 - b))).star_eq]
      calc p * CFC.sqrt (1 - b) * (CFC.sqrt (1 - b) * p)
          = p * (CFC.sqrt (1 - b) * CFC.sqrt (1 - b)) * p := by noncomm_ring
        _ = p * (1 - b) * p := by rw [CFC.sqrt_mul_sqrt_self _ hb']
        _ = 0 := hzero
    have h0 : (1 - b) * p = 0 :=
      (sqrt_mul_eq_zero_iff hb' p).mp
        (CStarRing.star_mul_self_eq_zero_iff _ |>.mp hsq)
    simpa [(IsSelfAdjoint.of_nonneg hb').star_eq, hp.isSelfAdjoint.star_eq]
      using congrArg star h0
  · intro h
    have hpb : p * b = p := by
      rw [mul_sub, mul_one, sub_eq_zero] at h; exact h.symm
    have hbp : b * p = p := by
      simpa [(IsSelfAdjoint.of_nonneg hb.1).star_eq, hp.isSelfAdjoint.star_eq]
        using congrArg star hpb
    -- `b = p + p^⊥ b p^⊥`
    have hexp : b - p = (1 - p) * b * (1 - p) := by
      have e : (1 - p) * b * (1 - p)
          = b - p * b - b * p + p * (b * p) := by noncomm_ring
      rw [e, hpb, hbp, hp.isIdempotentElem.eq]
      abel
    have : (0 : A) ≤ (1 - p) * b * (1 - p) := by
      have := star_left_conjugate_nonneg hb.1 (1 - p)
      rwa [hp.one_sub.isSelfAdjoint.star_eq] at this
    rw [← hexp, sub_nonneg] at this
    exact this

/-- Auxiliary: for `0 ≤ x` and self-adjoint `c`, `c x c = 0` iff `x c = 0`
(the C*-identity argument of **55X**). -/
private theorem conj_sa_eq_zero_iff {x c : A} (hx : 0 ≤ x) (hc : IsSelfAdjoint c) :
    c * x * c = 0 ↔ x * c = 0 := by
  have hxsa : star (CFC.sqrt x) = CFC.sqrt x :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)).star_eq
  have hxx : CFC.sqrt x * CFC.sqrt x = x := CFC.sqrt_mul_sqrt_self x hx
  have hkey : star (CFC.sqrt x * c) * (CFC.sqrt x * c) = c * x * c := by
    rw [star_mul, hxsa, hc.star_eq]
    calc c * CFC.sqrt x * (CFC.sqrt x * c)
        = c * (CFC.sqrt x * CFC.sqrt x) * c := by noncomm_ring
      _ = c * x * c := by rw [hxx]
  refine ⟨fun h => ?_, fun h => by rw [mul_assoc, h, mul_zero]⟩
  exact (sqrt_mul_eq_zero_iff hx c).mp
    ((CStarRing.star_mul_self_eq_zero_iff _).mp (hkey.trans h))

/-- Auxiliary: for an effect `x` and a projection `p`,
`p^⊥ x p^⊥ = 0` iff `x ≤ p` (the C*-identity argument of **55X**). -/
private theorem conj_ortho_eq_zero_iff {x p : A} (hx : x ∈ effects A)
    (hp : IsStarProjection p) : (1 - p) * x * (1 - p) = 0 ↔ x ≤ p :=
  (conj_sa_eq_zero_iff hx.1 hp.one_sub.isSelfAdjoint).trans (le_proj_iff hx hp).symm

end EffectsAux

omit [PartialOrder A] [StarOrderedRing A] in
/-- **55IV** (`projection-basic`, vn.tex:2232, Exercise), part 1: `0` and
`1` are projections. -/
theorem projection_basic_1 :
    IsStarProjection (0 : A) ∧ IsStarProjection (1 : A) :=
  ⟨IsStarProjection.zero _, IsStarProjection.one _⟩

/-- **55IV** (`projection-basic`, vn.tex:2232, Exercise), part 2: a
projection is an effect: `p* = p` and `0 ≤ p ≤ 1`. -/
theorem projection_basic_2 (p : A) (hp : IsStarProjection p) :
    IsSelfAdjoint p ∧ p ∈ effects A :=
  ⟨hp.isSelfAdjoint, hp.nonneg, hp.le_one⟩

omit [PartialOrder A] [StarOrderedRing A] in
/-- **55IV** (`projection-basic`, vn.tex:2232, Exercise), part 3: the
orthocomplement `p^⊥ = 1 - p` of a projection is a projection. -/
theorem projection_basic_3 (p : A) (hp : IsStarProjection p) :
    IsStarProjection (1 - p) :=
  hp.one_sub

/-- **55IV** (`projection-basic`, vn.tex:2232, Exercise), part 4: an effect
`a` is a projection iff `a·a^⊥ = 0`. -/
theorem projection_basic_4 (a : A) (ha : a ∈ effects A) :
    IsStarProjection a ↔ a * (1 - a) = 0 := by
  refine ⟨fun h => h.mul_one_sub_self, fun h => ⟨?_, IsSelfAdjoint.of_nonneg ha.1⟩⟩
  rw [mul_sub, mul_one, sub_eq_zero] at h
  exact h.symm

section AdContraposed

/-- First half of the thesis's argument for **55V**: from `a* p a ≤ q^⊥` one
gets `q a* p a q ≤ q q^⊥ q = 0`, whence `p a q = 0` by the C*-identity. -/
private theorem paq_eq_zero_of_le {a p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : star a * p * a ≤ 1 - q) : p * a * q = 0 := by
  have hcon := star_left_conjugate_le_conjugate h q
  rw [hq.isSelfAdjoint.star_eq, hq.mul_one_sub_self, zero_mul] at hcon
  have hnn : (0 : A) ≤ q * (star a * p * a) * q := by
    have := star_left_conjugate_nonneg (star_left_conjugate_nonneg hp.nonneg a) q
    rwa [hq.isSelfAdjoint.star_eq] at this
  have hzero : q * (star a * p * a) * q = 0 := le_antisymm hcon hnn
  rw [← CStarRing.star_mul_self_eq_zero_iff (p * a * q)]
  have h1 : star (p * a * q) = q * star a * p := by
    rw [star_mul, star_mul, hq.isSelfAdjoint.star_eq, hp.isSelfAdjoint.star_eq]
    noncomm_ring
  rw [h1]
  calc q * star a * p * (p * a * q) = q * (star a * (p * p) * a) * q := by
        noncomm_ring
    _ = q * (star a * p * a) * q := by rw [hp.isIdempotentElem.eq]
    _ = 0 := hzero

/-- Second half of the thesis's argument for **55V**: from `p a q = 0` one
gets `a q a* = p^⊥ (a q a*) p^⊥ ≤ p^⊥`, using `a q a* ≤ a a* ≤ ‖a‖²·1 ≤ 1`. -/
private theorem le_of_paq_eq_zero {a p q : A} (ha : ‖a‖ ≤ 1)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p * a * q = 0) :
    a * q * star a ≤ 1 - p := by
  have hstar : q * star a * p = 0 := by
    have h1 : star (p * a * q) = q * star a * p := by
      rw [star_mul, star_mul, hq.isSelfAdjoint.star_eq, hp.isSelfAdjoint.star_eq]
      noncomm_ring
    rw [← h1, h, star_zero]
  have e1 : (1 - p) * (a * q) = a * q := by
    have e : (1 - p) * (a * q) = a * q - p * a * q := by noncomm_ring
    rw [e, h, sub_zero]
  have e2 : q * star a * (1 - p) = q * star a := by
    have e : q * star a * (1 - p) = q * star a - q * star a * p := by noncomm_ring
    rw [e, hstar, sub_zero]
  have hqq : a * q * (q * star a) = a * q * star a := by
    calc a * q * (q * star a) = a * (q * q) * star a := by noncomm_ring
      _ = a * q * star a := by rw [hq.isIdempotentElem.eq]
  have key : (1 - p) * (a * q * star a) * (1 - p) = a * q * star a := by
    calc (1 - p) * (a * q * star a) * (1 - p)
        = (1 - p) * (a * q * (q * star a)) * (1 - p) := by rw [hqq]
      _ = (1 - p) * (a * q) * (q * star a * (1 - p)) := by noncomm_ring
      _ = a * q * (q * star a) := by rw [e1, e2]
      _ = a * q * star a := hqq
  -- `a q a* ≤ a a* ≤ 1`
  have hle1 : a * q * star a ≤ 1 := by
    have h1 := star_left_conjugate_le_conjugate hq.le_one (star a)
    rw [star_star, mul_one] at h1
    refine h1.trans ?_
    have hnn : (0 : A) ≤ a * star a := mul_star_self_nonneg a
    have hn : ‖a * star a‖ ≤ 1 := by
      calc ‖a * star a‖ ≤ ‖a‖ * ‖star a‖ := norm_mul_le _ _
        _ ≤ 1 := by rw [norm_star]; nlinarith [norm_nonneg a]
    refine (le_norm_smul_one hnn).trans ?_
    have := smul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ‖a * star a‖) (zero_le_one (α := A))
    rw [sub_smul, one_smul, sub_nonneg] at this
    exact this
  have hconj := star_left_conjugate_le_conjugate hle1 (1 - p)
  rw [hp.one_sub.isSelfAdjoint.star_eq, key, mul_one,
    hp.one_sub.isIdempotentElem.eq] at hconj
  exact hconj

/-- **55V** (`ad-contraposed`, vn.tex:2250, Lemma): for `‖a‖ ≤ 1` and
projections `p`, `q`: `a* p a ≤ q^⊥` iff `p a q = 0` iff `a q a* ≤ p^⊥`. -/
theorem ad_contraposed (a p q : A) (ha : ‖a‖ ≤ 1)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    List.TFAE
      [star a * p * a ≤ 1 - q,
       p * a * q = 0,
       a * q * star a ≤ 1 - p] := by
  tfae_have 1 → 2 := fun h => paq_eq_zero_of_le hp hq h
  tfae_have 2 → 3 := fun h => le_of_paq_eq_zero ha hp hq h
  tfae_have 3 → 1 := by
    intro h
    have h' : star (star a) * q * star a ≤ 1 - p := by rwa [star_star]
    have h2 : q * star a * p = 0 := paq_eq_zero_of_le hq hp h'
    have h3 : star a * p * star (star a) ≤ 1 - q :=
      le_of_paq_eq_zero (by rwa [norm_star]) hq hp h2
    rwa [star_star] at h3
  tfae_finish

end AdContraposed

/-- **55VIII** (`projection-above-effect`, vn.tex:2278): for an effect `a`
and a projection `p` the following are equivalent: `a ≤ p`; `p√a = √a`;
`√a p = √a`; `p^⊥√a = 0`; `√a p^⊥ = 0`; `a² ≤ p`; `pa = a`; `ap = a`;
`p^⊥ a = 0`; `a p^⊥ = 0`; `√a ≤ p`. -/
theorem projection_above_effect (a p : A) (ha : a ∈ effects A)
    (hp : IsStarProjection p) :
    List.TFAE
      [a ≤ p,
       p * CFC.sqrt a = CFC.sqrt a,
       CFC.sqrt a * p = CFC.sqrt a,
       (1 - p) * CFC.sqrt a = 0,
       CFC.sqrt a * (1 - p) = 0,
       a ^ 2 ≤ p,
       p * a = a,
       a * p = a,
       (1 - p) * a = 0,
       a * (1 - p) = 0,
       CFC.sqrt a ≤ p] := by
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha.1
  have hsq : IsSelfAdjoint (CFC.sqrt a) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  tfae_have 1 ↔ 10 := le_proj_iff ha hp
  tfae_have 10 ↔ 8 := by rw [mul_sub, mul_one, sub_eq_zero, eq_comm]
  tfae_have 8 ↔ 7 := by
    constructor <;> intro h <;>
      simpa [hsa.star_eq, hp.isSelfAdjoint.star_eq] using congrArg star h
  tfae_have 7 ↔ 9 := by rw [sub_mul, one_mul, sub_eq_zero, eq_comm]
  tfae_have 10 ↔ 5 := (sqrt_mul_eq_zero_iff ha.1 (1 - p)).symm
  tfae_have 5 ↔ 3 := by rw [mul_sub, mul_one, sub_eq_zero, eq_comm]
  tfae_have 3 ↔ 2 := by
    constructor <;> intro h <;>
      simpa [hsq.star_eq, hp.isSelfAdjoint.star_eq] using congrArg star h
  tfae_have 2 ↔ 4 := by rw [sub_mul, one_mul, sub_eq_zero, eq_comm]
  tfae_have 5 ↔ 11 := (le_proj_iff (sqrt_mem_effects ha) hp).symm
  tfae_have 6 ↔ 10 := by
    refine (le_proj_iff (sq_mem_effects ha) hp).trans ?_
    have h := sqrt_mul_eq_zero_iff (b := a ^ 2) (sq_mem_effects ha).1 (1 - p)
    rw [CFC.sqrt_sq a ha.1] at h
    exact h.symm
  tfae_finish

/-- **55IX** (`projection-below-effect`, vn.tex:2291): for an effect `a` and
a projection `p` the following are equivalent: `p ≤ a`; `p√a = p`;
`√a p = p`; `p(√a)^⊥ = 0`; `(√a)^⊥ p = 0`; `p ≤ a²`; `ap = p`; `pa = p`;
`p a^⊥ = 0`; `a^⊥ p = 0`; `p ≤ √a`. -/
theorem projection_below_effect (a p : A) (ha : a ∈ effects A)
    (hp : IsStarProjection p) :
    List.TFAE
      [p ≤ a,
       p * CFC.sqrt a = p,
       CFC.sqrt a * p = p,
       p * (1 - CFC.sqrt a) = 0,
       (1 - CFC.sqrt a) * p = 0,
       p ≤ a ^ 2,
       a * p = p,
       p * a = p,
       p * (1 - a) = 0,
       (1 - a) * p = 0,
       p ≤ CFC.sqrt a] := by
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha.1
  have hsq : IsSelfAdjoint (CFC.sqrt a) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  -- `a ≤ √a` and `a² ≤ a` for an effect `a`
  have hasqrt : a ≤ CFC.sqrt a := by
    have h := mul_self_le_self (sqrt_mem_effects ha)
    rwa [CFC.sqrt_mul_sqrt_self a ha.1] at h
  have hsqle : a ^ 2 ≤ a := by rw [sq]; exact mul_self_le_self ha
  tfae_have 1 ↔ 9 := proj_le_iff ha hp
  tfae_have 9 ↔ 8 := by rw [mul_sub, mul_one, sub_eq_zero, eq_comm]
  tfae_have 8 ↔ 7 := by
    constructor <;> intro h <;>
      simpa [hsa.star_eq, hp.isSelfAdjoint.star_eq] using congrArg star h
  tfae_have 7 ↔ 10 := by rw [sub_mul, one_mul, sub_eq_zero, eq_comm]
  tfae_have 11 ↔ 4 := proj_le_iff (sqrt_mem_effects ha) hp
  tfae_have 4 ↔ 2 := by rw [mul_sub, mul_one, sub_eq_zero, eq_comm]
  tfae_have 2 ↔ 3 := by
    constructor <;> intro h <;>
      simpa [hsq.star_eq, hp.isSelfAdjoint.star_eq] using congrArg star h
  tfae_have 3 ↔ 5 := by rw [sub_mul, one_mul, sub_eq_zero, eq_comm]
  tfae_have 1 → 11 := fun h => h.trans hasqrt
  tfae_have 3 → 7 := by
    intro h
    calc a * p = CFC.sqrt a * (CFC.sqrt a * p) := by
          rw [← mul_assoc, CFC.sqrt_mul_sqrt_self a ha.1]
      _ = p := by rw [h, h]
  tfae_have 8 → 6 := by
    intro h
    refine (proj_le_iff (sq_mem_effects ha) hp).mpr ?_
    rw [mul_sub, mul_one, sq, ← mul_assoc, h, h, sub_self]
  tfae_have 6 → 1 := fun h => h.trans hsqle
  tfae_finish

/-- **55X** (`projection-order-sharp`, vn.tex:2305, Lemma): an effect `a` is
a projection iff the only effect below both `a` and `a^⊥` is `0`. -/
theorem projection_order_sharp (a : A) (ha : a ∈ effects A) :
    IsStarProjection a ↔
      ∀ b ∈ effects A, b ≤ a → b ≤ 1 - a → b = 0 := by
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha.1
  constructor
  · -- `b ≤ a` gives `b a^⊥ = 0`, `b ≤ a^⊥` gives `b a = 0`, so `b = 0`
    intro hpa b hb hba hbc
    have h1 : b * (1 - a) = 0 := (le_proj_iff hb hpa).mp hba
    have h2 : b * a = 0 := by
      have := (le_proj_iff hb hpa.one_sub).mp hbc
      simpa using this
    have e : b = b * a + b * (1 - a) := by noncomm_ring
    rw [h1, h2, add_zero] at e
    exact e
  · -- `a a^⊥ = √a a^⊥ √a` is an effect below `a` and below `a^⊥`
    intro h
    have hx0 : (0 : A) ≤ a - a * a := sub_nonneg.mpr (mul_self_le_self ha)
    have haa : (0 : A) ≤ a * a := by
      simpa [hsa.star_eq] using star_mul_self_nonneg a
    have hxa : a - a * a ≤ a := by simpa using haa
    have hxc : a - a * a ≤ 1 - a := by
      have hone : (0 : A) ≤ (1 - a) * (1 - a) := by
        simpa [hsa.star_eq] using star_mul_self_nonneg (1 - a)
      have e : (1 - a) * (1 - a) = (1 - a) - (a - a * a) := by noncomm_ring
      rw [e, sub_nonneg] at hone
      exact hone
    have hzero := h (a - a * a) ⟨hx0, hxa.trans ha.2⟩ hxa hxc
    rw [projection_basic_4 a ha]
    have e : a * (1 - a) = a - a * a := by noncomm_ring
    rw [e, hzero]

/-- **55XII** (vn.tex:2323, Definition): a subset `E` of projections is
**orthogonal** (its members *pairwise orthogonal*) when any two members are
equal or have product `0`. -/
def OrthogonalSet (E : Set A) : Prop :=
  (∀ p ∈ E, IsStarProjection p) ∧ ∀ p ∈ E, ∀ q ∈ E, p = q ∨ p * q = 0

/-- **55XIII** (`orthogonal-tuple-of-projections`, vn.tex:2334, Exercise),
part 1: for projections `p`, `q` the following are equivalent: `pq = 0`;
`qp = 0`; `pqp = 0`; `p + q ≤ 1`; `p ≤ q^⊥`; `p + q` is a projection. -/
theorem orthogonal_tuple_of_projections_1 (p q : A)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    List.TFAE
      [p * q = 0,
       q * p = 0,
       p * q * p = 0,
       p + q ≤ 1,
       p ≤ 1 - q,
       IsStarProjection (p + q)] := by
  have hpe : p ∈ effects A := ⟨hp.nonneg, hp.le_one⟩
  tfae_have 1 ↔ 2 := by
    constructor <;> intro h <;>
      simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
        using congrArg star h
  tfae_have 1 → 3 := by intro h; rw [h, zero_mul]
  tfae_have 3 → 2 := by
    intro h
    rw [← CStarRing.star_mul_self_eq_zero_iff (q * p)]
    have h1 : star (q * p) = p * q := by
      rw [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
    rw [h1]
    calc p * q * (q * p) = p * (q * q) * p := by noncomm_ring
      _ = p * q * p := by rw [hq.isIdempotentElem.eq]
      _ = 0 := h
  tfae_have 5 ↔ 1 := by simpa using le_proj_iff hpe hq.one_sub
  tfae_have 5 ↔ 4 := le_sub_iff_add_le
  tfae_have 1 → 6 := fun h => hp.add hq h
  tfae_have 6 → 4 := fun h => h.le_one
  tfae_finish

omit [PartialOrder A] [StarOrderedRing A] in
/-- A finite sum of pairwise orthogonal projections is a projection. -/
theorem isStarProjection_sum {ι : Type*} (s : Finset ι)
    (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i * p j = 0) :
    IsStarProjection (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine (hp a).add (ih fun i hi j hj hij =>
        h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      exact h a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
        (by rintro rfl; exact ha hj)

/-- **55XIII** (`orthogonal-tuple-of-projections`, vn.tex:2334, Exercise),
part 2: a finite tuple of projections is pairwise orthogonal iff
`∑ᵢ pᵢ ≤ 1` iff `∑ᵢ pᵢ` is a projection. -/
theorem orthogonal_tuple_of_projections_2 {n : ℕ} (p : Fin n → A)
    (hp : ∀ i, IsStarProjection (p i)) :
    List.TFAE
      [Pairwise fun i j => p i * p j = 0,
       ∑ i, p i ≤ 1,
       IsStarProjection (∑ i, p i)] := by
  tfae_have 1 → 3 := fun h =>
    isStarProjection_sum Finset.univ p hp fun i _ j _ hij => h hij
  tfae_have 3 → 2 := fun h => h.le_one
  tfae_have 2 → 1 := by
    intro h i j hij
    -- `p i + p j ≤ ∑ₖ pₖ ≤ 1`, so `p i * p j = 0` by part 1
    have hsub : p i + p j ≤ ∑ k, p k := by
      have := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ ({i, j} : Finset (Fin n)))
        (fun k _ _ => (hp k).nonneg)
      rwa [Finset.sum_pair hij] at this
    exact ((orthogonal_tuple_of_projections_1 (p i) (p j) (hp i) (hp j)).out 3 0).mp
      (hsub.trans h)
  tfae_finish

/-- **55XIII** (`orthogonal-tuple-of-projections`, vn.tex:2334, Exercise),
part 2 (second half): for a pairwise orthogonal finite tuple of projections,
`∑ᵢ pᵢ` is the least projection above all `pᵢ`. -/
theorem orthogonal_tuple_of_projections_2' {n : ℕ} (p : Fin n → A)
    (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise fun i j => p i * p j = 0) :
    IsLeast {q : A | IsStarProjection q ∧ ∀ i, p i ≤ q} (∑ i, p i) := by
  have hsum : IsStarProjection (∑ i, p i) :=
    ((orthogonal_tuple_of_projections_2 p hp).out 0 2).mp horth
  refine ⟨⟨hsum, fun i => ?_⟩, ?_⟩
  · exact Finset.single_le_sum (f := p) (fun k _ => (hp k).nonneg)
      (Finset.mem_univ i)
  · rintro q ⟨hq, hle⟩
    refine (hsum.le_iff_mul_eq_right hq).mpr ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      ((hp i).le_iff_mul_eq_right hq).mp (hle i)

/-- **55XIV** (`projection-below-projection`, vn.tex:2353, Exercise): the
difference `q - p` of projections `p ≤ q` is a projection. -/
theorem projection_below_projection (p q : A) (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p ≤ q) : IsStarProjection (q - p) :=
  (hp.le_iff_sub hq).mp hpq

/-! ## Parsec 560: Ceiling and Floor -/

section CeilFloor

/-! ### Auxiliary: the iterated square roots `b^{1/2ⁿ}`

The thesis builds `⌈b⌉` as `⋁ₙ b^{1/2ⁿ}` (56I.20).  We write `b^{1/2ⁿ}` as
the `n`-fold iterate of `CFC.sqrt`, which is the form the *statement* of
`vna_ceil_sup` uses; the only property of the exponents that is needed is
`b^{1/2^{n+1}} · b^{1/2^{n+1}} = b^{1/2ⁿ}`. -/

/-- `b^{1/2ⁿ}`. -/
private noncomputable abbrev sqrtIter (b : A) (n : ℕ) : A :=
  (fun x : A => CFC.sqrt x)^[n] b

private theorem sqrtIter_succ (b : A) (n : ℕ) :
    sqrtIter b (n + 1) = CFC.sqrt (sqrtIter b n) :=
  Function.iterate_succ_apply' _ _ _

private theorem sqrtIter_mem_effects {b : A} (hb : b ∈ effects A) (n : ℕ) :
    sqrtIter b n ∈ effects A := by
  induction n with
  | zero => exact hb
  | succ n ih => rw [sqrtIter_succ]; exact sqrt_mem_effects ih

/-- `b^{1/2^{n+1}} · b^{1/2^{n+1}} = b^{1/2ⁿ}`. -/
private theorem sqrtIter_mul_self {b : A} (hb : b ∈ effects A) (n : ℕ) :
    sqrtIter b (n + 1) * sqrtIter b (n + 1) = sqrtIter b n := by
  rw [sqrtIter_succ]
  exact CFC.sqrt_mul_sqrt_self _ (sqrtIter_mem_effects hb n).1

/-- `0 ≤ b ≤ b^{1/2} ≤ b^{1/4} ≤ ⋯ ≤ 1` (56I.20). -/
private theorem sqrtIter_monotone {b : A} (hb : b ∈ effects A) :
    Monotone (sqrtIter b) := by
  refine monotone_nat_of_le_succ fun n => ?_
  have h := mul_self_le_self (sqrt_mem_effects (sqrtIter_mem_effects hb n))
  rwa [CFC.sqrt_mul_sqrt_self _ (sqrtIter_mem_effects hb n).1, ← sqrtIter_succ] at h

/-- **56I**.30 (`vna-ceil-point-1`), first half: whatever commutes with `b`
commutes with every `b^{1/2ⁿ}` (by `sqrt`, cstar.tex **23VII**). -/
private theorem sqrtIter_comm {b : A} (hb : b ∈ effects A) {a : A}
    (h : a * b = b * a) (n : ℕ) :
    a * sqrtIter b n = sqrtIter b n * a := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [sqrtIter_succ]
      exact (sqrt_commute _ (sqrtIter_mem_effects hb n).1 a ih).1

private theorem sqrtIter_comm_sqrtIter {b : A} (hb : b ∈ effects A) (m n : ℕ) :
    sqrtIter b m * sqrtIter b n = sqrtIter b n * sqrtIter b m :=
  sqrtIter_comm hb (sqrtIter_comm hb rfl m).symm n

variable [VonNeumannAlgebra A]

/-! `isLUB_coe_of_isLUB` (an `IsLUB` in `sa(A)` is an `IsLUB` in `A`) now
lives in `Theses/A/VN/Basic.lean`, next to its `IsGLB` mirror, because the
normal Gelfand–Naimark construction of parsec 480 needs it. -/

/-- Auxiliary: `√x·x·√x = x²`. -/
private theorem conj_sqrt_self {x : A} (hx : 0 ≤ x) :
    CFC.sqrt x * x * CFC.sqrt x = x * x := by
  have hxx : CFC.sqrt x * CFC.sqrt x = x := CFC.sqrt_mul_sqrt_self x hx
  calc CFC.sqrt x * x * CFC.sqrt x
      = CFC.sqrt x * (CFC.sqrt x * CFC.sqrt x) * CFC.sqrt x := by rw [hxx]
    _ = (CFC.sqrt x * CFC.sqrt x) * (CFC.sqrt x * CFC.sqrt x) := by noncomm_ring
    _ = x * x := by rw [hxx]

/-- **56I** (`vna-ceil`, vn.tex:2362, Proposition), the construction: for an
effect `b`, the supremum `p = ⋁ₙ b^{1/2ⁿ}` exists, is a projection, is the
least projection above `b`, and commutes with everything that `b` commutes
with.  This is the thesis's proof 56I.20–50. -/
private theorem exists_ceil_effect {b : A} (hb : b ∈ effects A) :
    ∃ p : A, IsStarProjection p ∧ IsLUB (Set.range (sqrtIter b)) p ∧
      (∀ q : A, IsStarProjection q → b ≤ q → p ≤ q) ∧
      (∀ a : A, a * b = b * a → a * p = p * a) := by
  classical
  -- the chain `D = {b^{1/2ⁿ}}` and its supremum `s`
  set E : ℕ → selfAdjoint A := fun n =>
    ⟨sqrtIter b n, IsSelfAdjoint.of_nonneg (sqrtIter_mem_effects hb n).1⟩ with hE
  have hEmono : Monotone E := fun m n hmn =>
    Subtype.coe_le_coe.mp (sqrtIter_monotone hb hmn)
  set D : Set (selfAdjoint A) := Set.range E with hD
  have hne : D.Nonempty := ⟨E 0, 0, rfl⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨E (max m n), ⟨max m n, rfl⟩, hEmono (le_max_left _ _),
      hEmono (le_max_right _ _)⟩
  have hbdd : BddAbove D := by
    refine ⟨⟨1, IsSelfAdjoint.one A⟩, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact Subtype.coe_le_coe.mp (sqrtIter_mem_effects hb n).2
  have h3 : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, hbdd⟩
  set s : selfAdjoint A := dirSup D h3 with hs
  set p : A := ((s : selfAdjoint A) : A) with hp
  have hlubSA : IsLUB D s := isLUB_dirSup D h3
  have hrange : Subtype.val '' D = Set.range (sqrtIter b) := by
    rw [hD, ← Set.range_comp]; rfl
  have hlub : IsLUB (Set.range (sqrtIter b)) p := by
    rw [← hrange]; exact isLUB_coe_of_isLUB hne hlubSA
  have hben : ∀ n, sqrtIter b n ≤ p := fun n => hlub.1 ⟨n, rfl⟩
  have hp1 : p ≤ 1 :=
    hlub.2 (by rintro _ ⟨n, rfl⟩; exact (sqrtIter_mem_effects hb n).2)
  have hp0 : (0 : A) ≤ p := le_trans hb.1 (hben 0)
  have hpeff : p ∈ effects A := ⟨hp0, hp1⟩
  -- **56I**.30: whatever commutes with `b` commutes with `p` (**44XIII**)
  have hcomm : ∀ a : A, a * b = b * a → a * p = p * a := by
    intro a ha
    exact vna_supremum_commutes D h3 a (by
      rintro _ ⟨n, rfl⟩
      exact sqrtIter_comm hb ha n)
  -- and therefore so does `√p` (`sqrt`, cstar.tex **23VII**)
  have hsqp : ∀ n, sqrtIter b n * CFC.sqrt p = CFC.sqrt p * sqrtIter b n := fun n =>
    (sqrt_commute p hp0 _ (hcomm _ (sqrtIter_comm hb rfl n).symm)).1
  have hsqsq : CFC.sqrt p * CFC.sqrt p = p := CFC.sqrt_mul_sqrt_self p hp0
  -- **56I**.40: `p² = p`; `p² ≤ p` because `p ≤ 1`
  have hpp_le : p * p ≤ p := mul_self_le_self hpeff
  have hle_pp : p ≤ p * p := by
    refine hlub.2 ?_
    rintro _ ⟨k, rfl⟩
    -- `p² = √p·p·√p ≥ √p·b^{1/2^{k+1}}·√p = b^{1/2^{k+2}}·p·b^{1/2^{k+2}}`
    -- `      ≥ b^{1/2^{k+2}}·b^{1/2^{k+1}}·b^{1/2^{k+2}} = b^{1/2^k}`
    have hsqsa : star (CFC.sqrt p) = CFC.sqrt p :=
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq
    have hEsa : star (sqrtIter b (k + 1 + 1)) = sqrtIter b (k + 1 + 1) :=
      (IsSelfAdjoint.of_nonneg (sqrtIter_mem_effects hb (k + 1 + 1)).1).star_eq
    have step1 : CFC.sqrt p * sqrtIter b (k + 1) * CFC.sqrt p ≤ p * p := by
      have hmono := star_left_conjugate_le_conjugate (hben (k + 1)) (CFC.sqrt p)
      rw [hsqsa] at hmono
      exact hmono.trans (le_of_eq (conj_sqrt_self hp0))
    have step2 : CFC.sqrt p * sqrtIter b (k + 1) * CFC.sqrt p
        = sqrtIter b (k + 1 + 1) * p * sqrtIter b (k + 1 + 1) := by
      calc CFC.sqrt p * sqrtIter b (k + 1) * CFC.sqrt p
          = CFC.sqrt p * (sqrtIter b (k + 1 + 1) * sqrtIter b (k + 1 + 1))
              * CFC.sqrt p := by rw [sqrtIter_mul_self hb (k + 1)]
        _ = (CFC.sqrt p * sqrtIter b (k + 1 + 1))
              * (sqrtIter b (k + 1 + 1) * CFC.sqrt p) := by noncomm_ring
        _ = (sqrtIter b (k + 1 + 1) * CFC.sqrt p)
              * (CFC.sqrt p * sqrtIter b (k + 1 + 1)) := by rw [hsqp (k + 1 + 1)]
        _ = sqrtIter b (k + 1 + 1) * (CFC.sqrt p * CFC.sqrt p)
              * sqrtIter b (k + 1 + 1) := by noncomm_ring
        _ = sqrtIter b (k + 1 + 1) * p * sqrtIter b (k + 1 + 1) := by rw [hsqsq]
    have step3 : sqrtIter b (k + 1 + 1) * sqrtIter b (k + 1) * sqrtIter b (k + 1 + 1)
        ≤ sqrtIter b (k + 1 + 1) * p * sqrtIter b (k + 1 + 1) := by
      have hmono :=
        star_left_conjugate_le_conjugate (hben (k + 1)) (sqrtIter b (k + 1 + 1))
      rwa [hEsa] at hmono
    have step4 : sqrtIter b (k + 1 + 1) * sqrtIter b (k + 1) * sqrtIter b (k + 1 + 1)
        = sqrtIter b k := by
      calc sqrtIter b (k + 1 + 1) * sqrtIter b (k + 1) * sqrtIter b (k + 1 + 1)
          = sqrtIter b (k + 1)
              * (sqrtIter b (k + 1 + 1) * sqrtIter b (k + 1 + 1)) := by
            rw [sqrtIter_comm_sqrtIter hb (k + 1 + 1) (k + 1)]; noncomm_ring
        _ = sqrtIter b (k + 1) * sqrtIter b (k + 1) := by
            rw [sqrtIter_mul_self hb (k + 1)]
        _ = sqrtIter b k := sqrtIter_mul_self hb k
    calc sqrtIter b k
        = sqrtIter b (k + 1 + 1) * sqrtIter b (k + 1) * sqrtIter b (k + 1 + 1) :=
          step4.symm
      _ ≤ sqrtIter b (k + 1 + 1) * p * sqrtIter b (k + 1 + 1) := step3
      _ = CFC.sqrt p * sqrtIter b (k + 1) * CFC.sqrt p := step2.symm
      _ ≤ p * p := step1
  refine ⟨p, ⟨le_antisymm hpp_le hle_pp, s.2⟩, hlub, ?_, hcomm⟩
  -- **56I**.50: `p` is the *least* projection above `b`
  intro q hq hbq
  refine hlub.2 ?_
  rintro _ ⟨n, rfl⟩
  induction n with
  | zero => exact hbq
  | succ n ih =>
      rw [sqrtIter_succ]
      exact ((projection_above_effect _ q (sqrtIter_mem_effects hb n) hq).out 0 10).mp ih

/-- Auxiliary (the rescaling `⌈b⌉ = ⌈‖b‖⁻¹b⌉` of **59I**): a nonzero
positive `b` has the same "absorbing" projections and the same commutant as
the effect `‖b‖⁻¹b`. -/
private theorem exists_normalize {b : A} (hb : 0 ≤ b) (hbne : b ≠ 0) :
    ∃ b' : A, b' ∈ effects A ∧ (∀ p : A, b * p = b ↔ b' * p = b') ∧
      (∀ a : A, a * b = b * a ↔ a * b' = b' * a) := by
  have hn : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hbne
  have hne : (‖b‖ : ℝ) ≠ 0 := ne_of_gt hn
  refine ⟨(‖b‖⁻¹ : ℝ) • b, ⟨smul_nonneg (by positivity) hb, ?_⟩, fun p => ?_, fun a => ?_⟩
  · refine (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (smul_nonneg (by positivity) hb)).mp ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      inv_mul_cancel₀ hne]
  · rw [smul_mul_assoc]
    refine ⟨fun h => by rw [h], fun h => ?_⟩
    have h2 := congrArg (fun x : A => (‖b‖ : ℝ) • x) h
    simpa [smul_smul, mul_inv_cancel₀ hne] using h2
  · rw [mul_smul_comm, smul_mul_assoc]
    refine ⟨fun h => by rw [h], fun h => ?_⟩
    have h2 := congrArg (fun x : A => (‖b‖ : ℝ) • x) h
    simpa [smul_smul, mul_inv_cancel₀ hne] using h2

/-- **56I** (`vna-ceil`, vn.tex:2362, Proposition), well-definedness (in the
uniform formulation of 59III `ceil-basic`): every positive `b` in a von
Neumann algebra has a least projection `p` with `b·p = b`. -/
theorem exists_ceil (b : A) (hb : 0 ≤ b) :
    ∃! p : A, IsStarProjection p ∧ b * p = b ∧
      ∀ q : A, IsStarProjection q → b * q = b → p ≤ q := by
  -- uniqueness is automatic from the two minimality clauses
  suffices hex : ∃ p : A, IsStarProjection p ∧ b * p = b ∧
      ∀ q : A, IsStarProjection q → b * q = b → p ≤ q by
    obtain ⟨p, hp⟩ := hex
    exact ⟨p, hp, fun q hq => le_antisymm (hq.2.2 p hp.1 hp.2.1) (hp.2.2 q hq.1 hq.2.1)⟩
  rcases eq_or_ne b 0 with rfl | hbne
  · exact ⟨0, IsStarProjection.zero A, by simp, fun q hq _ => hq.nonneg⟩
  -- the general positive case is the effect case rescaled by `‖b‖⁻¹` (59I)
  obtain ⟨b', hb'eff, hscale, -⟩ := exists_normalize hb hbne
  obtain ⟨p, hproj, hlub, hleast, -⟩ := exists_ceil_effect hb'eff
  have hb'p : b' ≤ p := hlub.1 ⟨0, rfl⟩
  refine ⟨p, hproj, (hscale p).mpr
    (((projection_above_effect b' p hb'eff hproj).out 0 7).mp hb'p), fun q hq hbq => ?_⟩
  exact hleast q hq
    (((projection_above_effect b' q hb'eff hq).out 0 7).mpr ((hscale q).mp hbq))

open scoped Classical in
/-- **56I**/**59I** (`vna-ceil`/`ceill`, vn.tex:2362/2684): the **ceiling**
`⌈b⌉` of a positive element `b` of a von Neumann algebra: the least
projection `p` with `b·p = b`.  For an effect `b` this is the least
projection above `b` (56I); for general positive `b` it agrees with the
extension `⌈b⌉ = ⌈‖b‖⁻¹·b⌉` of 59I.  (Junk value `0` off the positive
cone.) -/
noncomputable def ceil (b : A) : A :=
  if hb : 0 ≤ b then (exists_ceil b hb).choose else 0

/-- The defining property of `⌈b⌉` for positive `b`. -/
theorem ceil_spec {b : A} (hb : 0 ≤ b) :
    IsStarProjection (ceil b) ∧ b * ceil b = b ∧
      ∀ q : A, IsStarProjection q → b * q = b → ceil b ≤ q := by
  rw [ceil, dif_pos hb]
  exact (exists_ceil b hb).choose_spec.1

/-- `⌈b⌉` is characterized by its defining property. -/
theorem ceil_eq_of_isLeast {b : A} (hb : 0 ≤ b) {p : A}
    (hproj : IsStarProjection p) (hbp : b * p = b)
    (hleast : ∀ q : A, IsStarProjection q → b * q = b → p ≤ q) : ceil b = p := by
  obtain ⟨h1, h2, h3⟩ := ceil_spec hb
  exact le_antisymm (h3 p hproj hbp) (hleast _ h1 h2)

/-- **56I** (`vna-ceil`, vn.tex:2362, Proposition): for an *effect* `b`,
`⌈b⌉` is the least projection above `b`. -/
theorem vna_ceil (b : A) (hb : b ∈ effects A) :
    IsLeast {p : A | IsStarProjection p ∧ b ≤ p} (ceil b) := by
  obtain ⟨h1, h2, h3⟩ := ceil_spec hb.1
  refine ⟨⟨h1, ((projection_above_effect b _ hb h1).out 0 7).mpr h2⟩, ?_⟩
  rintro q ⟨hq, hbq⟩
  exact h3 q hq (((projection_above_effect b q hb hq).out 0 7).mp hbq)

/-- **56I** (`vna-ceil`, vn.tex:2362, Proposition), formula:
`⌈b⌉ = ⋁ₙ b^{1/2ⁿ}` for an effect `b` (the iterated square roots). -/
theorem vna_ceil_sup (b : A) (hb : b ∈ effects A) :
    IsLUB (Set.range fun n : ℕ => (fun x : A => CFC.sqrt x)^[n] b) (ceil b) := by
  obtain ⟨p, hproj, hlub, hleast, -⟩ := exists_ceil_effect hb
  have hb'p : b ≤ p := hlub.1 ⟨0, rfl⟩
  have hceil : ceil b = p := by
    refine ceil_eq_of_isLeast hb.1 hproj
      (((projection_above_effect b p hb hproj).out 0 7).mp hb'p) fun q hq hbq => ?_
    exact hleast q hq (((projection_above_effect b q hb hq).out 0 7).mpr hbq)
  rw [hceil]
  exact hlub

/-- **56I** (`vna-ceil`, vn.tex:2362, Proposition), moreover: whatever
commutes with `b` commutes with `⌈b⌉`. -/
theorem vna_ceil_comm (b : A) (hb : 0 ≤ b) (a : A) (h : a * b = b * a) :
    a * ceil b = ceil b * a := by
  rcases eq_or_ne b 0 with rfl | hbne
  · have h0 : ceil (0 : A) = 0 := by
      refine ceil_eq_of_isLeast le_rfl (IsStarProjection.zero A) (by simp) ?_
      exact fun q hq _ => hq.nonneg
    rw [h0, mul_zero, zero_mul]
  obtain ⟨b', hb'eff, hscale, hcomm'⟩ := exists_normalize hb hbne
  obtain ⟨p, hproj, hlub, hleast, hpcomm⟩ := exists_ceil_effect hb'eff
  have hb'p : b' ≤ p := hlub.1 ⟨0, rfl⟩
  have hceil : ceil b = p := by
    refine ceil_eq_of_isLeast hb hproj
      ((hscale p).mpr (((projection_above_effect b' p hb'eff hproj).out 0 7).mp hb'p))
      fun q hq hbq => ?_
    exact hleast q hq
      (((projection_above_effect b' q hb'eff hq).out 0 7).mpr ((hscale q).mp hbq))
  rw [hceil]
  exact hpcomm a ((hcomm' a).mp h)

/-- Auxiliary: `⌈b^⊥⌉` is a projection (**56I**). -/
private theorem ceil_isStarProjection {b : A} (hb : b ∈ effects A) :
    IsStarProjection (ceil (1 - b)) :=
  (vna_ceil (1 - b) (effect_orthosupplement b hb)).1.1

/-- Auxiliary (the duality `⌊b⌋ = ⌈b^⊥⌉^⊥` behind **56VI**): for a projection
`q` and an effect `b`,
`q ≤ b  ↔  b^⊥q = 0  ↔  b^⊥ ≤ q^⊥  ↔  ⌈b^⊥⌉ ≤ q^⊥  ↔  q ≤ ⌈b^⊥⌉^⊥`. -/
private theorem proj_le_iff_le_ceil_compl {b : A} (hb : b ∈ effects A)
    {q : A} (hq : IsStarProjection q) : q ≤ b ↔ q ≤ 1 - ceil (1 - b) := by
  have hb' : (1 : A) - b ∈ effects A := effect_orthosupplement b hb
  obtain ⟨⟨hc, hbc⟩, hcleast⟩ := vna_ceil (1 - b) hb'
  have e1 : q ≤ b ↔ q * (1 - b) = 0 := proj_le_iff hb hq
  have e2 : ((1 : A) - b) * q = 0 ↔ q * (1 - b) = 0 := by
    constructor <;> intro h <;>
      simpa [(IsSelfAdjoint.of_nonneg hb'.1).star_eq, hq.isSelfAdjoint.star_eq]
        using congrArg star h
  have e3 : (1 : A) - b ≤ 1 - q ↔ ((1 : A) - b) * q = 0 := by
    have h := le_proj_iff hb' hq.one_sub
    rwa [sub_sub_cancel] at h
  have e4 : ceil (1 - b) ≤ 1 - q ↔ (1 : A) - b ≤ 1 - q :=
    ⟨fun h => hbc.trans h, fun h => hcleast ⟨hq.one_sub, h⟩⟩
  rw [e1, ← e2, ← e3, ← e4]
  exact le_sub_comm.symm

/-- **56VI** (`vna-floor`, vn.tex:2419, Proposition), well-definedness:
every effect `b` of a von Neumann algebra has a greatest projection `p` with
`p·b = p`. -/
theorem exists_floor (b : A) (hb : b ∈ effects A) :
    ∃! p : A, IsStarProjection p ∧ p * b = p ∧
      ∀ q : A, IsStarProjection q → q * b = q → q ≤ p := by
  have hple : (1 : A) - ceil (1 - b) ≤ b :=
    (proj_le_iff_le_ceil_compl hb (ceil_isStarProjection hb).one_sub).mpr le_rfl
  have hmem : ((1 : A) - ceil (1 - b)) * b = 1 - ceil (1 - b) :=
    ((projection_below_effect b _ hb (ceil_isStarProjection hb).one_sub).out 0 7).mp hple
  refine ⟨1 - ceil (1 - b), ⟨(ceil_isStarProjection hb).one_sub, hmem, fun q hq hqb => ?_⟩,
    fun q hq => le_antisymm ?_ (hq.2.2 _ (ceil_isStarProjection hb).one_sub hmem)⟩
  · exact (proj_le_iff_le_ceil_compl hb hq).mp
      (((projection_below_effect b q hb hq).out 0 7).mpr hqb)
  · exact (proj_le_iff_le_ceil_compl hb hq.1).mp
      (((projection_below_effect b q hb hq.1).out 0 7).mpr hq.2.1)

open scoped Classical in
/-- **56VI** (`vna-floor`, vn.tex:2419, Proposition): the **floor** `⌊b⌋` of
an effect `b` of a von Neumann algebra: the greatest projection below `b`
(characterized as the greatest projection `p` with `p·b = p`, cf. 56XI).
(Junk value `0` off the effects.) -/
noncomputable def floor (b : A) : A :=
  if hb : b ∈ effects A then (exists_floor b hb).choose else 0

/-- The defining property of `⌊b⌋` for an effect `b`. -/
theorem floor_spec {b : A} (hb : b ∈ effects A) :
    IsStarProjection (floor b) ∧ floor b * b = floor b ∧
      ∀ q : A, IsStarProjection q → q * b = q → q ≤ floor b := by
  rw [floor, dif_pos hb]
  exact (exists_floor b hb).choose_spec.1

theorem floor_le {b : A} (hb : b ∈ effects A) : floor b ≤ b :=
  ((projection_below_effect b _ hb (floor_spec hb).1).out 0 7).mpr (floor_spec hb).2.1

/-- **56XIII**.1 in the form in which **56VI** produces it: `⌊b⌋ = ⌈b^⊥⌉^⊥`. -/
theorem floor_eq_one_sub_ceil {b : A} (hb : b ∈ effects A) :
    floor b = 1 - ceil (1 - b) := by
  obtain ⟨h1, -, h3⟩ := floor_spec hb
  have hcp : IsStarProjection (ceil (1 - b)) := ceil_isStarProjection hb
  have hple : (1 : A) - ceil (1 - b) ≤ b :=
    (proj_le_iff_le_ceil_compl hb hcp.one_sub).mpr le_rfl
  refine le_antisymm ((proj_le_iff_le_ceil_compl hb h1).mp (floor_le hb)) ?_
  exact h3 _ hcp.one_sub
    (((projection_below_effect b _ hb hcp.one_sub).out 0 7).mp hple)

/-- **56VI**: `⌊b⌋` is the greatest projection below the effect `b`. -/
theorem floor_isGreatest {b : A} (hb : b ∈ effects A) :
    IsGreatest {p : A | IsStarProjection p ∧ p ≤ b} (floor b) := by
  obtain ⟨h1, -, h3⟩ := floor_spec hb
  refine ⟨⟨h1, floor_le hb⟩, ?_⟩
  rintro q ⟨hq, hqb⟩
  exact h3 q hq (((projection_below_effect b q hb hq).out 0 7).mp hqb)

/-- **56VI** (`vna-floor`, vn.tex:2419, Proposition): `⌊b⌋` is the greatest
projection below the effect `b`, and equals `⋀ₙ b^{2ⁿ}`. -/
theorem vna_floor (b : A) (hb : b ∈ effects A) :
    IsGreatest {p : A | IsStarProjection p ∧ p ≤ b} (floor b) ∧
      IsGLB (Set.range fun n : ℕ => b ^ (2 ^ n)) (floor b) := by
  refine ⟨floor_isGreatest hb, ?_⟩
  -- **56VI**.70: the filtered set `1 ≥ b ≥ b² ≥ b⁴ ≥ ⋯ ≥ 0` and its infimum
  -- `q = ⋀ₙ b^{2ⁿ}` (`infima_in_vna`, **43Ia**)
  set E : ℕ → selfAdjoint A := fun n =>
    ⟨b ^ 2 ^ n, IsSelfAdjoint.of_nonneg (pow_mem_effects hb (2 ^ n)).1⟩ with hE
  have hEanti : Antitone E := fun m n hmn =>
    Subtype.coe_le_coe.mp
      (pow_antitone_of_mem_effects hb (Nat.pow_le_pow_right (by norm_num) hmn))
  set F : Set (selfAdjoint A) := Set.range E with hF
  have hne : F.Nonempty := ⟨E 0, 0, rfl⟩
  have hdir : DirectedOn (· ≥ ·) F := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨E (max m n), ⟨max m n, rfl⟩, hEanti (le_max_left _ _),
      hEanti (le_max_right _ _)⟩
  have hbdd : BddBelow F := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact Subtype.coe_le_coe.mp (pow_mem_effects hb (2 ^ n)).1
  obtain ⟨p, hglbSA⟩ := infima_in_vna F hne hdir hbdd
  set q : A := ((p : selfAdjoint A) : A) with hq
  have hrange : Subtype.val '' F = Set.range (fun n : ℕ => b ^ 2 ^ n) := by
    rw [hF, ← Set.range_comp]; rfl
  have hglb : IsGLB (Set.range fun n : ℕ => b ^ 2 ^ n) q := by
    rw [← hrange]; exact isGLB_coe_of_isGLB hne hglbSA
  have hqle : ∀ n : ℕ, q ≤ b ^ 2 ^ n := fun n => hglb.1 ⟨n, rfl⟩
  have hq0 : (0 : A) ≤ q := hglb.2 (by
    rintro _ ⟨n, rfl⟩; exact (pow_mem_effects hb (2 ^ n)).1)
  have hqb : q ≤ b := by simpa using hqle 0
  have hqeff : q ∈ effects A := ⟨hq0, hqb.trans hb.2⟩
  -- **56VI**.80: `b` commutes with `q` (a variation on **44XIII**)
  have hcomm : b * q = q * b :=
    vna_infimum_commutes hne hdir hglbSA b (by
      rintro _ ⟨n, rfl⟩
      exact ((Commute.refl b).pow_right (2 ^ n)).eq)
  -- and therefore so does `√q` (`sqrt`, cstar.tex **23VII**)
  have hsq0 : (0 : A) ≤ CFC.sqrt q := CFC.sqrt_nonneg q
  have hsqb : Commute (CFC.sqrt q) b := ((sqrt_commute q hq0 b hcomm).1).symm
  have hsqpow : ∀ k : ℕ, CFC.sqrt q * b ^ k = b ^ k * CFC.sqrt q := fun k =>
    (hsqb.pow_right k).eq
  have hsqsq : CFC.sqrt q * CFC.sqrt q = q := CFC.sqrt_mul_sqrt_self q hq0
  have hbsa : ∀ k : ℕ, star (b ^ k) = b ^ k := fun k =>
    ((IsSelfAdjoint.of_nonneg hb.1).pow k).star_eq
  -- `q ≤ b^{2^m} q b^{2^m}` — the inner application of `ad_normal_inf`:
  -- `b^{2^m} q b^{2^m} = ⋀ₙ b^{2^m} b^{2ⁿ} b^{2^m}` and `q ≤ b^{2^m+2ⁿ+2^m}`
  have hstep : ∀ m : ℕ, q ≤ b ^ 2 ^ m * q * b ^ 2 ^ m := by
    intro m
    have hAD := ad_normal_inf (b ^ 2 ^ m) hne hdir hglbSA
    simp only [hbsa] at hAD
    rw [hrange] at hAD
    refine hAD.2 ?_
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    have hprod : b ^ 2 ^ m * b ^ 2 ^ n * b ^ 2 ^ m = b ^ (2 ^ m + 2 ^ n + 2 ^ m) := by
      rw [← pow_add, ← pow_add]
    have hexp : 2 ^ m + 2 ^ n + 2 ^ m ≤ 2 ^ (max (m + 1) n + 1) := by
      have h1 : 2 ^ (m + 1) ≤ 2 ^ max (m + 1) n :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : 2 ^ n ≤ 2 ^ max (m + 1) n :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have h3 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
      have h4 : 2 ^ (max (m + 1) n + 1) = 2 ^ max (m + 1) n + 2 ^ max (m + 1) n := by
        rw [pow_succ]; ring
      omega
    calc q ≤ b ^ 2 ^ (max (m + 1) n + 1) := hqle _
      _ ≤ b ^ (2 ^ m + 2 ^ n + 2 ^ m) := pow_antitone_of_mem_effects hb hexp
      _ = b ^ 2 ^ m * b ^ 2 ^ n * b ^ 2 ^ m := hprod.symm
  -- **56VI**.90: `q² = q`.  `q² ≤ q` because `q ≤ 1`; for `q ≤ q²` use the
  -- outer application of `ad_normal_inf`, to the shifted chain `(b^{2^{m+1}})ₘ`
  set G : Set (selfAdjoint A) := Set.range (fun m : ℕ => E (m + 1)) with hG
  have hGne : G.Nonempty := ⟨E 1, 0, rfl⟩
  have hGdir : DirectedOn (· ≥ ·) G := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨E (max m n + 1), ⟨max m n, rfl⟩, hEanti (by omega), hEanti (by omega)⟩
  have hGglb : IsGLB G p := by
    refine ⟨?_, fun v hv => hglbSA.2 ?_⟩
    · rintro _ ⟨m, rfl⟩
      exact hglbSA.1 ⟨m + 1, rfl⟩
    · rintro _ ⟨n, rfl⟩
      exact le_trans (hv ⟨n, rfl⟩) (hEanti (Nat.le_succ n))
  have hqq : q ≤ q * q := by
    have hAD := ad_normal_inf (CFC.sqrt q) hGne hGdir hGglb
    simp only [(IsSelfAdjoint.of_nonneg hsq0).star_eq] at hAD
    rw [conj_sqrt_self hq0] at hAD
    refine hAD.2 ?_
    rintro _ ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, rfl⟩
    -- `√q b^{2^{m+1}} √q = b^{2^m} q b^{2^m} ≥ q`
    have hsplit : b ^ 2 ^ (m + 1) = b ^ 2 ^ m * b ^ 2 ^ m := by
      rw [← pow_add]; congr 1; rw [pow_succ]; ring
    have : CFC.sqrt q * b ^ 2 ^ (m + 1) * CFC.sqrt q
        = b ^ 2 ^ m * q * b ^ 2 ^ m := by
      calc CFC.sqrt q * b ^ 2 ^ (m + 1) * CFC.sqrt q
          = CFC.sqrt q * b ^ 2 ^ m * (b ^ 2 ^ m * CFC.sqrt q) := by
            rw [hsplit]; noncomm_ring
        _ = b ^ 2 ^ m * CFC.sqrt q * (CFC.sqrt q * b ^ 2 ^ m) := by
            rw [hsqpow (2 ^ m)]
        _ = b ^ 2 ^ m * (CFC.sqrt q * CFC.sqrt q) * b ^ 2 ^ m := by noncomm_ring
        _ = b ^ 2 ^ m * q * b ^ 2 ^ m := by rw [hsqsq]
    show q ≤ CFC.sqrt q * ((E (m + 1) : selfAdjoint A) : A) * CFC.sqrt q
    rw [hE]
    exact this ▸ hstep m
  have hqproj : IsStarProjection q :=
    ⟨le_antisymm (mul_self_le_self hqeff) hqq, p.2⟩
  -- **56VI**.100: `q` is the greatest projection below `b`, i.e. `q = ⌊b⌋`
  have hfb : ∀ k : ℕ, floor b * b ^ k = floor b := by
    intro k
    induction k with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, (floor_spec hb).2.1]
  have hfloorq : floor b ≤ q := hglb.2 (by
    rintro _ ⟨n, rfl⟩
    exact ((projection_below_effect (b ^ 2 ^ n) (floor b)
      (pow_mem_effects hb (2 ^ n)) (floor_spec hb).1).out 0 7).mpr (hfb _))
  have hqf : q = floor b :=
    le_antisymm ((floor_isGreatest hb).2 ⟨hqproj, hqb⟩) hfloorq
  rwa [hqf] at hglb

/-- **56VI** (`vna-floor`, vn.tex:2419, Proposition), moreover: whatever
commutes with `b` commutes with `⌊b⌋`. -/
theorem vna_floor_comm (b : A) (hb : b ∈ effects A) (a : A)
    (h : a * b = b * a) : a * floor b = floor b * a := by
  have hb' : (1 : A) - b ∈ effects A := effect_orthosupplement b hb
  have h' : a * (1 - b) = (1 - b) * a := by
    rw [mul_sub, sub_mul, mul_one, one_mul, h]
  have hc := vna_ceil_comm (1 - b) hb'.1 a h'
  rw [floor_eq_one_sub_ceil hb, mul_sub, sub_mul, mul_one, one_mul, hc]

/-- **56XI** (`ceil-floor-second-property`, vn.tex:2471, Exercise), part 1:
for an effect `a` and a projection `p`: `pa = a` iff `ap = a` iff
`⌈a⌉ ≤ p`.  In particular `⌈a⌉` is the least projection `p` with `a = ap`,
and `a = a⌈a⌉ = ⌈a⌉a`. -/
theorem ceil_floor_second_property_1 (a p : A) (ha : a ∈ effects A)
    (hp : IsStarProjection p) :
    List.TFAE [p * a = a, a * p = a, ceil a ≤ p] := by
  obtain ⟨⟨hcp, hac⟩, hcleast⟩ := vna_ceil a ha
  tfae_have 1 ↔ 2 := (projection_above_effect a p ha hp).out 6 7
  have e : a * p = a ↔ a ≤ p := (projection_above_effect a p ha hp).out 7 0
  tfae_have 2 ↔ 3 :=
    e.trans ⟨fun h => hcleast ⟨hp, h⟩, fun h => hac.trans h⟩
  tfae_finish

/-- **56XI** (`ceil-floor-second-property`, vn.tex:2471, Exercise), part 2:
for an effect `a` and a projection `p`: `pa = p` iff `ap = p` iff
`p ≤ ⌊a⌋`.  In particular `⌊a⌋` is the greatest projection `p` with
`p = ap`, and `⌊a⌋ = a⌊a⌋ = ⌊a⌋a`. -/
theorem ceil_floor_second_property_2 (a p : A) (ha : a ∈ effects A)
    (hp : IsStarProjection p) :
    List.TFAE [p * a = p, a * p = p, p ≤ floor a] := by
  obtain ⟨⟨hfp, hfa⟩, hfgreatest⟩ := floor_isGreatest ha
  tfae_have 1 ↔ 2 := (projection_below_effect a p ha hp).out 7 6
  have e : p * a = p ↔ p ≤ a := (projection_below_effect a p ha hp).out 7 0
  tfae_have 1 ↔ 3 :=
    e.trans ⟨fun h => hfgreatest ⟨hp, h⟩, fun h => h.trans hfa⟩
  tfae_finish

/-! **56XII** (vn.tex:2491, Example): ceiling and floor in `L^∞(X)` —
descriptive example, not converted (cf. 51IX on `L^∞`). -/

/-- **56XIII** (`ceil-floor-basic`, vn.tex:2505, Exercise), part 1:
`⌈a⌉^⊥ = ⌊a^⊥⌋` and `⌊a⌋^⊥ = ⌈a^⊥⌉` for an effect `a`. -/
theorem ceil_floor_basic_1 (a : A) (ha : a ∈ effects A) :
    1 - ceil a = floor (1 - a) ∧ 1 - floor a = ceil (1 - a) := by
  have ha' : (1 : A) - a ∈ effects A := effect_orthosupplement a ha
  constructor
  · rw [floor_eq_one_sub_ceil ha', sub_sub_cancel]
  · rw [floor_eq_one_sub_ceil ha, sub_sub_cancel]

/-- **56XIII** (`ceil-floor-basic`, vn.tex:2505, Exercise), part 2:
`⌈λa⌉ = ⌈a⌉` for `λ ∈ (0,1]`, and for `λ ∈ (0,1)` the projection
`⌈λa + λ^⊥b⌉` is the least projection above both `⌈a⌉` and `⌈b⌉` (the
supremum in the poset of projections). -/
theorem ceil_floor_basic_2 (a b : A) (ha : a ∈ effects A)
    (hb : b ∈ effects A) (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1) :
    ceil ((l : ℂ) • a) = ceil a ∧
      IsLeast {p : A | IsStarProjection p ∧ ceil a ≤ p ∧ ceil b ≤ p}
        (ceil ((l : ℂ) • a + ((1 - l : ℝ) : ℂ) • b)) := by
  rw [Complex.coe_smul, Complex.coe_smul]
  have hm0 : (0 : ℝ) < 1 - l := by linarith
  have hsmul : ∀ {x : A} {r : ℝ}, x ∈ effects A → 0 ≤ r → r ≤ 1 → r • x ∈ effects A := by
    intro x r hx hr0 hr1
    refine ⟨smul_nonneg hr0 hx.1, ?_⟩
    have h1 : r • x ≤ x := by
      have h := smul_nonneg (by linarith : (0 : ℝ) ≤ 1 - r) hx.1
      rw [sub_smul, one_smul, sub_nonneg] at h
      exact h
    exact h1.trans hx.2
  have hla : (l : ℝ) • a ∈ effects A := hsmul ha hl0.le hl1.le
  -- for a projection `p`, `r·x ≤ p ↔ x ≤ p` when `r > 0`
  have hscale : ∀ {x : A} {r : ℝ} {p : A}, x ∈ effects A → 0 < r → r ≤ 1 →
      IsStarProjection p → (r • x ≤ p ↔ x ≤ p) := by
    intro x r p hx hr0 hr1 hp
    rw [le_proj_iff (hsmul hx hr0.le hr1) hp, le_proj_iff hx hp, smul_mul_assoc]
    refine ⟨fun h => ?_, fun h => by rw [h, smul_zero]⟩
    have h2 := congrArg (fun z : A => (r⁻¹ : ℝ) • z) h
    simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hr0)] using h2
  constructor
  · refine (vna_ceil _ hla).unique ?_
    have hset : {p : A | IsStarProjection p ∧ (l : ℝ) • a ≤ p}
        = {p : A | IsStarProjection p ∧ a ≤ p} :=
      Set.ext fun p => and_congr_right fun hp => hscale ha hl0 hl1.le hp
    rw [hset]
    exact vna_ceil a ha
  -- the convex combination
  set c : A := (l : ℝ) • a + ((1 - l : ℝ)) • b with hcdef
  have hceff : c ∈ effects A := by
    refine ⟨add_nonneg (smul_nonneg hl0.le ha.1) (smul_nonneg hm0.le hb.1), ?_⟩
    have hone : (l : ℝ) • (1 : A) + ((1 - l : ℝ)) • (1 : A) = 1 := by
      rw [← add_smul]; norm_num
    have h1 : (l : ℝ) • (1 - a) + ((1 - l : ℝ)) • (1 - b) = 1 - c := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, hone, hcdef]
    have h2 : (0 : A) ≤ (l : ℝ) • (1 - a) + ((1 - l : ℝ)) • (1 - b) :=
      add_nonneg (smul_nonneg hl0.le (sub_nonneg.mpr ha.2))
        (smul_nonneg hm0.le (sub_nonneg.mpr hb.2))
    rw [h1, sub_nonneg] at h2
    exact h2
  have hset2 : {p : A | IsStarProjection p ∧ ceil a ≤ p ∧ ceil b ≤ p}
      = {p : A | IsStarProjection p ∧ c ≤ p} := by
    ext p
    refine and_congr_right fun hp => ?_
    have ea : ceil a ≤ p ↔ a ≤ p :=
      ⟨fun h => (vna_ceil a ha).1.2.trans h, fun h => (vna_ceil a ha).2 ⟨hp, h⟩⟩
    have eb : ceil b ≤ p ↔ b ≤ p :=
      ⟨fun h => (vna_ceil b hb).1.2.trans h, fun h => (vna_ceil b hb).2 ⟨hp, h⟩⟩
    have expand : (1 - p) * c * (1 - p)
        = (l : ℝ) • ((1 - p) * a * (1 - p))
          + ((1 - l : ℝ)) • ((1 - p) * b * (1 - p)) := by
      rw [hcdef, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
        smul_mul_assoc]
    have hAnn : (0 : A) ≤ (1 - p) * a * (1 - p) := by
      have := star_left_conjugate_nonneg ha.1 (1 - p)
      rwa [hp.one_sub.isSelfAdjoint.star_eq] at this
    have hBnn : (0 : A) ≤ (1 - p) * b * (1 - p) := by
      have := star_left_conjugate_nonneg hb.1 (1 - p)
      rwa [hp.one_sub.isSelfAdjoint.star_eq] at this
    rw [ea, eb, ← conj_ortho_eq_zero_iff ha hp, ← conj_ortho_eq_zero_iff hb hp,
      ← conj_ortho_eq_zero_iff hceff hp, expand]
    refine ⟨fun h => by rw [h.1, h.2, smul_zero, smul_zero, add_zero], fun h => ?_⟩
    have hA0 : (l : ℝ) • ((1 - p) * a * (1 - p)) = 0 := by
      refine le_antisymm ?_ (smul_nonneg hl0.le hAnn)
      have e : (l : ℝ) • ((1 - p) * a * (1 - p))
          = -(((1 - l : ℝ)) • ((1 - p) * b * (1 - p))) := by
        rw [eq_neg_iff_add_eq_zero]; exact h
      rw [e, neg_nonpos]
      exact smul_nonneg hm0.le hBnn
    have hB0 : ((1 - l : ℝ)) • ((1 - p) * b * (1 - p)) = 0 := by
      rw [hA0, zero_add] at h; exact h
    constructor
    · have h2 := congrArg (fun z : A => (l⁻¹ : ℝ) • z) hA0
      simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hl0)] using h2
    · have h2 := congrArg (fun z : A => ((1 - l : ℝ)⁻¹) • z) hB0
      simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hm0)] using h2
  rw [hset2]
  exact vna_ceil c hceff

/-- **56XIII** (`ceil-floor-basic`, vn.tex:2505, Exercise), part 3:
`⌊a⌋ = ⌊a²⌋` and `⌈a⌉ = ⌈a²⌉` for an effect `a`. -/
theorem ceil_floor_basic_3 (a : A) (ha : a ∈ effects A) :
    floor a = floor (a ^ 2) ∧ ceil a = ceil (a ^ 2) := by
  have ha2 : a ^ 2 ∈ effects A := sq_mem_effects ha
  -- for a projection `p`, `p ≤ a ↔ p ≤ a²` and `a ≤ p ↔ a² ≤ p` (**55VIII**/**55IX**)
  have hbelow : {p : A | IsStarProjection p ∧ p ≤ a}
      = {p : A | IsStarProjection p ∧ p ≤ a ^ 2} := by
    ext p
    exact and_congr_right fun hp => (projection_below_effect a p ha hp).out 0 5
  have habove : {p : A | IsStarProjection p ∧ a ≤ p}
      = {p : A | IsStarProjection p ∧ a ^ 2 ≤ p} := by
    ext p
    exact and_congr_right fun hp => (projection_above_effect a p ha hp).out 0 5
  refine ⟨(floor_isGreatest ha).unique ?_, (vna_ceil a ha).unique ?_⟩
  · rw [hbelow]; exact floor_isGreatest ha2
  · rw [habove]; exact vna_ceil (a ^ 2) ha2

/-- **56XIV** (`vna-directed-supremum-projections`, vn.tex:2526, Lemma): the
supremum of a directed set of projections of a von Neumann algebra is a
projection. -/
theorem vna_directed_supremum_projections (D : Set A) (s : A)
    (hD : ∀ p ∈ D, IsStarProjection p) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hs : IsLUB D s) :
    IsStarProjection s := by
  -- `dp = d` for `d ∈ D` (**55IX**); `(d)_d → p` and `(dp)_d → p²` ultraweakly
  -- (**44VI**, **44VII**), so `p = p²` by uniqueness of ultraweak limits.
  obtain ⟨d₀, hd₀⟩ := hne
  have hs0 : (0 : A) ≤ s := (hD d₀ hd₀).nonneg.trans (hs.1 hd₀)
  have hs1 : s ≤ 1 := hs.2 fun d hd => (hD d hd).le_one
  have hssa : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg hs0
  set D' : Set (selfAdjoint A) := {d : selfAdjoint A | (d : A) ∈ D} with hD'def
  have hval : Subtype.val '' D' = D := by
    ext x
    exact ⟨by rintro ⟨d, hd, rfl⟩; exact hd,
      fun hx => ⟨⟨x, (hD x hx).isSelfAdjoint⟩, hx, rfl⟩⟩
  have hne' : D'.Nonempty := ⟨⟨d₀, (hD d₀ hd₀).isSelfAdjoint⟩, hd₀⟩
  have hdir' : DirectedOn (· ≤ ·) D' := by
    intro x hx y hy
    obtain ⟨c, hc, hxc, hyc⟩ := hdir _ hx _ hy
    exact ⟨⟨c, (hD c hc).isSelfAdjoint⟩, hc, hxc, hyc⟩
  have hbdd' : BddAbove D' := ⟨⟨s, hssa⟩, fun d hd => hs.1 hd⟩
  have h3 : D'.Nonempty ∧ DirectedOn (· ≤ ·) D' ∧ BddAbove D' := ⟨hne', hdir', hbdd'⟩
  have hlubSA : IsLUB D' (⟨s, hssa⟩ : selfAdjoint A) := by
    refine ⟨fun d hd => hs.1 hd, fun u hu => hs.2 ?_⟩
    rw [← hval]
    rintro _ ⟨d, hd, rfl⟩
    exact hu hd
  have hdsup : ((dirSup D' h3 : selfAdjoint A) : A) = s := by
    rw [(isLUB_dirSup D' h3).unique hlubSA]
  have : Nonempty D' := ⟨⟨⟨d₀, (hD d₀ hd₀).isSelfAdjoint⟩, hd₀⟩⟩
  have : IsDirectedOrder D' := directedOn_iff_isDirectedOrder.mp hdir'
  refine ⟨?_, hssa⟩
  show s * s = s
  refine sub_eq_zero.mp (np_separating (s * s - s) fun ω => ?_)
  have h1 := (uwTendsto_iff _ _ _).mp (vna_supremum_mult D' h3 s).1 ω
  have h2 := (uwTendsto_iff _ _ _).mp (vna_supremum_uwlimit D' h3) ω
  rw [hdsup] at h1 h2
  have heq : (fun d : D' => (ω (((d : selfAdjoint A) : A) * s) : ℂ))
      = fun d : D' => (ω ((d : selfAdjoint A) : A) : ℂ) := by
    funext d
    have hd : ((d : selfAdjoint A) : A) * s = ((d : selfAdjoint A) : A) :=
      ((projection_below_effect s _ ⟨hs0, hs1⟩ (hD _ d.2)).out 0 7).mp (hs.1 d.2)
    rw [hd]
  rw [heq] at h1
  rw [npFunctional_sub, sub_eq_zero]
  exact tendsto_nhds_unique h1 h2

/-- Auxiliary: `⌈p⌉ = p` for a projection. -/
theorem ceil_of_isStarProjection {p : A} (hp : IsStarProjection p) : ceil p = p :=
  (vna_ceil p ⟨hp.nonneg, hp.le_one⟩).unique
    ⟨⟨hp, le_rfl⟩, fun q hq => hq.2⟩

/-- Auxiliary (the binary join of projections): `⌈p + q⌉` is the least
projection above both `p` and `q`. -/
private theorem isLeast_ceil_add {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    IsLeast {r : A | IsStarProjection r ∧ p ≤ r ∧ q ≤ r} (ceil (p + q)) := by
  have hpq : (0 : A) ≤ p + q := add_nonneg hp.nonneg hq.nonneg
  obtain ⟨h1, h2, h3⟩ := ceil_spec hpq
  -- for a projection `r`: `(p+q)r = p+q ↔ p ≤ r ∧ q ≤ r`
  have key : ∀ r : A, IsStarProjection r →
      ((p + q) * r = p + q ↔ p ≤ r ∧ q ≤ r) := by
    intro r hr
    constructor
    · intro h
      have hzero : (1 - r) * (p + q) * (1 - r) = 0 := by
        have hpr : (p + q) * (1 - r) = 0 := by
          rw [mul_sub, mul_one, h, sub_self]
        rw [mul_assoc, hpr, mul_zero]
      have hsplit : (1 - r) * p * (1 - r) + (1 - r) * q * (1 - r) = 0 := by
        rw [← hzero]; noncomm_ring
      have hpnn : (0 : A) ≤ (1 - r) * p * (1 - r) := by
        have := star_left_conjugate_nonneg hp.nonneg (1 - r)
        rwa [hr.one_sub.isSelfAdjoint.star_eq] at this
      have hqnn : (0 : A) ≤ (1 - r) * q * (1 - r) := by
        have := star_left_conjugate_nonneg hq.nonneg (1 - r)
        rwa [hr.one_sub.isSelfAdjoint.star_eq] at this
      have hp0 : (1 - r) * p * (1 - r) = 0 := by
        refine le_antisymm ?_ hpnn
        have : (1 - r) * p * (1 - r) = -((1 - r) * q * (1 - r)) := by
          rw [eq_neg_iff_add_eq_zero]; exact hsplit
        rw [this, neg_nonpos]
        exact hqnn
      have hq0 : (1 - r) * q * (1 - r) = 0 := by
        rw [hp0, zero_add] at hsplit; exact hsplit
      exact ⟨(conj_ortho_eq_zero_iff ⟨hp.nonneg, hp.le_one⟩ hr).mp hp0,
        (conj_ortho_eq_zero_iff ⟨hq.nonneg, hq.le_one⟩ hr).mp hq0⟩
    · rintro ⟨hpr, hqr⟩
      have e1 : p * r = p :=
        ((projection_above_effect p r ⟨hp.nonneg, hp.le_one⟩ hr).out 0 7).mp hpr
      have e2 : q * r = q :=
        ((projection_above_effect q r ⟨hq.nonneg, hq.le_one⟩ hr).out 0 7).mp hqr
      rw [add_mul, e1, e2]
  refine ⟨⟨h1, ((key _ h1).mp h2).1, ((key _ h1).mp h2).2⟩, ?_⟩
  rintro r ⟨hr, hpr, hqr⟩
  exact h3 r hr ((key r hr).mpr ⟨hpr, hqr⟩)

/-- **56XVI** (vn.tex:2542, Exercise), suprema: every set of projections of
a von Neumann algebra has a supremum `⋃A` *in the poset of projections*. -/
theorem exists_projSup (P : Set A) (hP : ∀ p ∈ P, IsStarProjection p) :
    ∃! s : A, IsStarProjection s ∧ (∀ p ∈ P, p ≤ s) ∧
      ∀ q : A, IsStarProjection q → (∀ p ∈ P, p ≤ q) → s ≤ q := by
  -- `D` = the projections below *every* projection upper-bounding `P`.  It is
  -- directed (binary joins) and contains `P`, so its supremum is a projection
  -- (**56XIV**) and is the join of `P` in the poset of projections.
  classical
  set D : Set A := {d : A | IsStarProjection d ∧
    ∀ r : A, IsStarProjection r → (∀ p ∈ P, p ≤ r) → d ≤ r} with hDdef
  have hPD : P ⊆ D := fun p hp => ⟨hP p hp, fun r _ hr => hr p hp⟩
  have hne : D.Nonempty := ⟨0, IsStarProjection.zero A, fun r hr _ => hr.nonneg⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro x ⟨hx, hxle⟩ y ⟨hy, hyle⟩
    obtain ⟨⟨hj, hxj, hyj⟩, hjleast⟩ := isLeast_ceil_add hx hy
    exact ⟨ceil (x + y), ⟨hj, fun r hr hrP =>
      hjleast ⟨hr, hxle r hr hrP, hyle r hr hrP⟩⟩, hxj, hyj⟩
  have hbdd : BddAbove D := ⟨1, fun d hd => hd.1.le_one⟩
  set D' : Set (selfAdjoint A) := {d : selfAdjoint A | (d : A) ∈ D} with hD'def
  have hval : Subtype.val '' D' = D := by
    ext x
    exact ⟨by rintro ⟨d, hd, rfl⟩; exact hd,
      fun hx => ⟨⟨x, (hx.1).isSelfAdjoint⟩, hx, rfl⟩⟩
  obtain ⟨d₀, hd₀⟩ := id hne
  have hne' : D'.Nonempty := ⟨⟨d₀, hd₀.1.isSelfAdjoint⟩, hd₀⟩
  have hdir' : DirectedOn (· ≤ ·) D' := by
    intro x hx y hy
    obtain ⟨c, hc, hxc, hyc⟩ := hdir _ hx _ hy
    exact ⟨⟨c, hc.1.isSelfAdjoint⟩, hc, hxc, hyc⟩
  have hbdd' : BddAbove D' := ⟨⟨1, IsSelfAdjoint.one A⟩, fun d hd => hd.1.le_one⟩
  have h3 : D'.Nonempty ∧ DirectedOn (· ≤ ·) D' ∧ BddAbove D' := ⟨hne', hdir', hbdd'⟩
  set s : A := ((dirSup D' h3 : selfAdjoint A) : A) with hsdef
  have hlubSA : IsLUB D' (dirSup D' h3) := isLUB_dirSup D' h3
  have hlub : IsLUB D s := by
    rw [← hval]
    exact isLUB_coe_of_isLUB hne' hlubSA
  have hproj : IsStarProjection s :=
    vna_directed_supremum_projections D s (fun d hd => hd.1) hne hdir hlub
  refine ⟨s, ⟨hproj, fun p hp => hlub.1 (hPD hp), fun q hq hqP => ?_⟩, ?_⟩
  · exact hlub.2 fun d hd => hd.2 q hq hqP
  · rintro t ⟨ht, htP, htleast⟩
    exact le_antisymm (htleast s hproj fun p hp => hlub.1 (hPD hp))
      (hlub.2 fun d hd => hd.2 t ht htP)

open scoped Classical in
/-- **56XVI** (vn.tex:2542, Exercise): the supremum `⋃P` of a set of
projections in the poset of projections (junk value `0` if `P` contains a
non-projection). -/
noncomputable def projSup (P : Set A) : A :=
  if hP : ∀ p ∈ P, IsStarProjection p then (exists_projSup P hP).choose else 0

/-- The defining property of `⋃P`. -/
theorem projSup_spec {P : Set A} (hP : ∀ p ∈ P, IsStarProjection p) :
    IsStarProjection (projSup P) ∧ (∀ p ∈ P, p ≤ projSup P) ∧
      ∀ q : A, IsStarProjection q → (∀ p ∈ P, p ≤ q) → projSup P ≤ q := by
  rw [projSup, dif_pos hP]
  exact (exists_projSup P hP).choose_spec.1

theorem projSup_eq {P : Set A} (hP : ∀ p ∈ P, IsStarProjection p) {s : A}
    (hs : IsStarProjection s) (hub : ∀ p ∈ P, p ≤ s)
    (hleast : ∀ q : A, IsStarProjection q → (∀ p ∈ P, p ≤ q) → s ≤ q) :
    projSup P = s :=
  (exists_projSup P hP).unique (projSup_spec hP) ⟨hs, hub, hleast⟩

/-- **56XVI** (vn.tex:2542, Exercise), infima: every set of projections of a
von Neumann algebra has an infimum `⋂A` in the poset of projections. -/
theorem exists_projInf (P : Set A) (hP : ∀ p ∈ P, IsStarProjection p) :
    ∃! s : A, IsStarProjection s ∧ (∀ p ∈ P, s ≤ p) ∧
      ∀ q : A, IsStarProjection q → (∀ p ∈ P, q ≤ p) → q ≤ s := by
  -- `p ↦ p^⊥` is an order anti-isomorphism of the poset of projections
  classical
  set P' : Set A := (fun p : A => 1 - p) '' P with hP'def
  have hP'proj : ∀ p ∈ P', IsStarProjection p := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hP p hp).one_sub
  obtain ⟨u, ⟨hu, huP, huleast⟩, -⟩ := exists_projSup P' hP'proj
  refine ⟨1 - u, ⟨hu.one_sub, fun p hp => sub_le_comm.mp (huP _ ⟨p, hp, rfl⟩),
    fun q hq hqP => ?_⟩, ?_⟩
  · refine le_sub_comm.mp (huleast (1 - q) hq.one_sub ?_)
    rintro _ ⟨p, hp, rfl⟩
    exact sub_le_sub_left (hqP p hp) 1
  · rintro t ⟨ht, htP, htgreatest⟩
    refine le_antisymm (le_sub_comm.mp (huleast (1 - t) ht.one_sub ?_))
      (htgreatest _ hu.one_sub fun p hp => sub_le_comm.mp (huP _ ⟨p, hp, rfl⟩))
    rintro _ ⟨p, hp, rfl⟩
    exact sub_le_sub_left (htP p hp) 1

open scoped Classical in
/-- **56XVI** (vn.tex:2542, Exercise): the infimum `⋂P` of a set of
projections in the poset of projections (junk value `0`). -/
noncomputable def projInf (P : Set A) : A :=
  if hP : ∀ p ∈ P, IsStarProjection p then (exists_projInf P hP).choose else 0

/-- The defining property of `⋂P`. -/
theorem projInf_spec {P : Set A} (hP : ∀ p ∈ P, IsStarProjection p) :
    IsStarProjection (projInf P) ∧ (∀ p ∈ P, projInf P ≤ p) ∧
      ∀ q : A, IsStarProjection q → (∀ p ∈ P, q ≤ p) → q ≤ projInf P := by
  rw [projInf, dif_pos hP]
  exact (exists_projInf P hP).choose_spec.1

theorem projInf_eq {P : Set A} (hP : ∀ p ∈ P, IsStarProjection p) {s : A}
    (hs : IsStarProjection s) (hlb : ∀ p ∈ P, s ≤ p)
    (hgreatest : ∀ q : A, IsStarProjection q → (∀ p ∈ P, q ≤ p) → q ≤ s) :
    projInf P = s :=
  (exists_projInf P hP).unique (projInf_spec hP) ⟨hs, hlb, hgreatest⟩

/-! ### Auxiliary: the ceiling calculus

Everything in **56XVII**, **59III**–**59VI** is read off the defining property of `⌈a⌉`
(the least projection `p` with `ap = a`, `ceil_spec`) through the two
elementary equivalences

  `a p = a  ↔  a p^⊥ = 0`   and   `x c = 0  ↔  c* x c = 0`  (`x ≥ 0`),

the second being `conj_sa_eq_zero_iff`.  The one genuinely nontrivial input
is `ceil_mul_eq_zero` (`bc = 0 ⟹ ⌈b⌉c = 0`), which uses the supremum
formula **56I** together with **44VIII** (`ad_normal`). -/

/-- `⌈0⌉ = 0`. -/
theorem ceil_zero : ceil (0 : A) = 0 :=
  ceil_eq_of_isLeast le_rfl (IsStarProjection.zero A) (by simp)
    fun q hq _ => hq.nonneg

/-- Two positive elements with the same "absorbing" projections have the
same ceiling. -/
private theorem ceil_congr {x y : A} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ∀ p : A, IsStarProjection p → (x * p = x ↔ y * p = y)) :
    ceil x = ceil y := by
  obtain ⟨hx1, hx2, hx3⟩ := ceil_spec hx
  obtain ⟨hy1, hy2, hy3⟩ := ceil_spec hy
  exact le_antisymm (hx3 _ hy1 ((h _ hy1).mpr hy2)) (hy3 _ hx1 ((h _ hx1).mp hx2))

/-- `⌈λa⌉ = ⌈a⌉` for `λ > 0` (**59III**.4, first half). -/
theorem ceil_smul {a : A} (ha : 0 ≤ a) {l : ℝ} (hl : 0 < l) :
    ceil (l • a) = ceil a := by
  refine ceil_congr (smul_nonneg hl.le ha) ha fun p _ => ?_
  rw [smul_mul_assoc]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have h2 := congrArg (fun z : A => (l⁻¹ : ℝ) • z) h
  simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hl)] using h2

/-- `a p = a` iff `a p^⊥ = 0`. -/
private theorem mul_eq_iff_mul_ortho_eq_zero (a p : A) :
    a * p = a ↔ a * (1 - p) = 0 := by
  rw [mul_sub, mul_one, sub_eq_zero, eq_comm]

/-- For `0 ≤ x` and a projection `p`: `x* x p = x* x` iff `x p = x`
(the C*-identity `‖x p^⊥‖² = ‖p^⊥ x* x p^⊥‖`). -/
private theorem star_mul_self_absorb_iff (a : A) {p : A}
    (hp : IsStarProjection p) :
    star a * a * p = star a * a ↔ a * p = a := by
  rw [mul_eq_iff_mul_ortho_eq_zero, mul_eq_iff_mul_ortho_eq_zero,
    ← conj_sa_eq_zero_iff (star_mul_self_nonneg a) hp.one_sub.isSelfAdjoint,
    ← CStarRing.star_mul_self_eq_zero_iff (a * (1 - p))]
  rw [star_mul, hp.one_sub.isSelfAdjoint.star_eq]
  constructor <;> intro h
  · rw [← h]; noncomm_ring
  · rw [← h]; noncomm_ring

/-! `isLUB_sa_of_isLUB` (the converse of `isLUB_coe_of_isLUB`) now lives in
`Theses/A/VN/Basic.lean` for the same reason. -/

/-- **The** calculation rule behind **59IV** and **60VIII**: if `bc = 0`
for positive `b`, then already `⌈b⌉c = 0`.

For an effect `b` this is **44VIII** (`ad_normal`) applied to the chain
`b^{1/2ⁿ}` whose supremum is `⌈b⌉` (**56I**): `bc = 0` gives
`b^{1/2ⁿ}c = 0` for every `n` (by `sqrt_mul_eq_zero_iff`), hence
`c*⌈b⌉c = ⋁ₙ c* b^{1/2ⁿ} c = 0`, and `c*⌈b⌉c = (⌈b⌉c)*(⌈b⌉c)`. -/
theorem ceil_mul_eq_zero {b : A} (hb : 0 ≤ b) {c : A} (h : b * c = 0) :
    ceil b * c = 0 := by
  -- reduce to the case of an effect by the rescaling of **59I**
  suffices hkey : ∀ b' : A, b' ∈ effects A → b' * c = 0 → ceil b' * c = 0 by
    rcases eq_or_ne b 0 with rfl | hbne
    · rw [ceil_zero, zero_mul]
    have hn : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hbne
    have hb'nn : (0 : A) ≤ (‖b‖⁻¹ : ℝ) • b := smul_nonneg (by positivity) hb
    have hb'eff : (‖b‖⁻¹ : ℝ) • b ∈ effects A := by
      refine ⟨hb'nn, (CStarAlgebra.norm_le_one_iff_of_nonneg _ hb'nn).mp ?_⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
        inv_mul_cancel₀ (ne_of_gt hn)]
    have hb'c : ((‖b‖⁻¹ : ℝ) • b) * c = 0 := by
      rw [smul_mul_assoc, h, smul_zero]
    rw [← ceil_smul hb (inv_pos.mpr hn)]
    exact hkey _ hb'eff hb'c
  clear h hb
  intro b hb h
  -- `b^{1/2ⁿ} c = 0` for every `n`
  have hzero : ∀ n : ℕ, sqrtIter b n * c = 0 := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih =>
        rw [sqrtIter_succ]
        exact (sqrt_mul_eq_zero_iff (sqrtIter_mem_effects hb n).1 c).mpr ih
  -- the chain and its supremum `⌈b⌉` in `sa(A)`
  set E : ℕ → selfAdjoint A := fun n =>
    ⟨sqrtIter b n, IsSelfAdjoint.of_nonneg (sqrtIter_mem_effects hb n).1⟩ with hE
  have hEmono : Monotone E := fun m n hmn =>
    Subtype.coe_le_coe.mp (sqrtIter_monotone hb hmn)
  set D : Set (selfAdjoint A) := Set.range E with hD
  have hne : D.Nonempty := ⟨E 0, 0, rfl⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨E (max m n), ⟨max m n, rfl⟩, hEmono (le_max_left _ _),
      hEmono (le_max_right _ _)⟩
  have hbdd : BddAbove D := by
    refine ⟨⟨1, IsSelfAdjoint.one A⟩, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact Subtype.coe_le_coe.mp (sqrtIter_mem_effects hb n).2
  have h3 : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, hbdd⟩
  set s : selfAdjoint A := ⟨ceil b, (ceil_spec hb.1).1.isSelfAdjoint⟩ with hs
  have hval : Subtype.val '' D = Set.range (sqrtIter b) := by
    rw [hD, ← Set.range_comp]; rfl
  have hlub : IsLUB D s := by
    refine isLUB_sa_of_isLUB ?_
    rw [hval]
    exact vna_ceil_sup b hb
  have hdirSup : dirSup D h3 = s := (isLUB_dirSup D h3).unique hlub
  -- **44VIII**: `c* ⌈b⌉ c = ⋁ₙ c* b^{1/2ⁿ} c = 0`
  have hAD := ad_normal c D h3
  rw [hdirSup] at hAD
  have hzeroSup : star c * ceil b * c = 0 := by
    refine le_antisymm (hAD.2 ?_) ?_
    · rintro _ ⟨d, ⟨n, rfl⟩, rfl⟩
      show star c * sqrtIter b n * c ≤ 0
      rw [mul_assoc, hzero n, mul_zero]
    · have h0 : star c * ((E 0 : selfAdjoint A) : A) * c
          ≤ star c * ((s : selfAdjoint A) : A) * c := hAD.1 ⟨E 0, ⟨0, rfl⟩, rfl⟩
      have he0 : ((E 0 : selfAdjoint A) : A) = b := rfl
      rw [he0, mul_assoc, h, mul_zero] at h0
      exact h0
  -- `c* ⌈b⌉ c = (⌈b⌉c)* (⌈b⌉c)`
  refine (CStarRing.star_mul_self_eq_zero_iff (ceil b * c)).mp ?_
  rw [star_mul, (ceil_spec hb.1).1.isSelfAdjoint.star_eq]
  calc star c * ceil b * (ceil b * c)
      = star c * (ceil b * ceil b) * c := by noncomm_ring
    _ = star c * ceil b * c := by rw [(ceil_spec hb.1).1.isIdempotentElem.eq]
    _ = 0 := hzeroSup

/-- **59III**.1 in the form the ceiling calculus needs: for positive `a`
and a projection `p`, `⌈a⌉ ≤ p` iff `ap = a`. -/
theorem ceil_le_iff {a : A} (ha : 0 ≤ a) {p : A} (hp : IsStarProjection p) :
    ceil a ≤ p ↔ a * p = a := by
  obtain ⟨h1, h2, h3⟩ := ceil_spec ha
  refine ⟨fun h => ?_, fun h => h3 p hp h⟩
  have hcp : ceil a * p = ceil a :=
    ((projection_below_effect p (ceil a) ⟨hp.nonneg, hp.le_one⟩ h1).out 0 7).mp h
  calc a * p = a * ceil a * p := by rw [h2]
    _ = a * (ceil a * p) := by noncomm_ring
    _ = a * ceil a := by rw [hcp]
    _ = a := h2

/-- `⌈·⌉` is monotone on the positive cone: `0 ≤ a ≤ b` gives
`⌈a⌉ ≤ ⌈b⌉`, because `0 ≤ ⌈b⌉^⊥ a ⌈b⌉^⊥ ≤ ⌈b⌉^⊥ b ⌈b⌉^⊥ = 0`. -/
theorem ceil_mono {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) : ceil a ≤ ceil b := by
  have hb : (0 : A) ≤ b := ha.trans hab
  obtain ⟨h1, h2, -⟩ := ceil_spec hb
  have hsa := h1.one_sub.isSelfAdjoint
  refine (ceil_spec ha).2.2 _ h1 ?_
  rw [mul_eq_iff_mul_ortho_eq_zero, ← conj_sa_eq_zero_iff ha hsa]
  have hzb : (1 - ceil b) * b * (1 - ceil b) = 0 := by
    rw [conj_sa_eq_zero_iff hb hsa, ← mul_eq_iff_mul_ortho_eq_zero]
    exact h2
  have hle : (1 - ceil b) * a * (1 - ceil b) ≤ (1 - ceil b) * b * (1 - ceil b) := by
    have h := star_left_conjugate_le_conjugate hab (1 - ceil b)
    rwa [hsa.star_eq] at h
  have hnn : (0 : A) ≤ (1 - ceil b) * a * (1 - ceil b) := by
    have h := star_left_conjugate_nonneg ha (1 - ceil b)
    rwa [hsa.star_eq] at h
  exact le_antisymm (hzb ▸ hle) hnn

/-- **44VIII** (`ad_normal`) in the shape used for suprema of ceilings: if
`s = ⋁D` for a nonempty directed set `D` of self-adjoint elements and
`c d c = 0` for every `d ∈ D` (with `c` self-adjoint), then `c s c = 0`. -/
private theorem conj_eq_zero_of_isLUB {D : Set A} {s c : A}
    (hsa : ∀ d ∈ D, IsSelfAdjoint d) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) (hc : IsSelfAdjoint c)
    (h : ∀ d ∈ D, c * d * c = 0) : c * s * c = 0 := by
  obtain ⟨d₀, hd₀⟩ := hne
  have hssa : IsSelfAdjoint s := by
    have hd : IsSelfAdjoint (s - d₀) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr (hlub.1 hd₀))
    simpa using hd.add (hsa d₀ hd₀)
  -- transport `D` to `sa(A)`
  set D' : Set (selfAdjoint A) := {x : selfAdjoint A | (x : A) ∈ D} with hD'
  have hval : Subtype.val '' D' = D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hsa x hx⟩, hx, rfl⟩
  have hne' : D'.Nonempty := ⟨⟨d₀, hsa d₀ hd₀⟩, hd₀⟩
  have hdir' : DirectedOn (· ≤ ·) D' := by
    intro x hx y hy
    obtain ⟨z, hz, hxz, hyz⟩ := hdir _ hx _ hy
    exact ⟨⟨z, hsa z hz⟩, hz, hxz, hyz⟩
  set s' : selfAdjoint A := ⟨s, hssa⟩ with hs'
  have hlub' : IsLUB D' s' := by
    refine isLUB_sa_of_isLUB ?_
    rw [hval]; exact hlub
  have hbdd : BddAbove D' := ⟨s', hlub'.1⟩
  have h3 : D'.Nonempty ∧ DirectedOn (· ≤ ·) D' ∧ BddAbove D' := ⟨hne', hdir', hbdd⟩
  have hdirSup : dirSup D' h3 = s' := (isLUB_dirSup D' h3).unique hlub'
  have hAD := ad_normal c D' h3
  rw [hdirSup, hc.star_eq] at hAD
  refine le_antisymm (hAD.2 ?_) ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact le_of_eq (h _ hd)
  · have h0 : c * ((⟨d₀, hsa d₀ hd₀⟩ : selfAdjoint A) : A) * c ≤ c * s * c :=
      hAD.1 ⟨⟨d₀, hsa d₀ hd₀⟩, hd₀, rfl⟩
    rw [show ((⟨d₀, hsa d₀ hd₀⟩ : selfAdjoint A) : A) = d₀ from rfl, h _ hd₀] at h0
    exact h0

/-- **56XVII**/**59V** (`ceil-supremum`/`ceil-suprema`, vn.tex:2554/2768),
the common content: `⌈⋁D⌉ = ⋃_{d∈D}⌈d⌉` for a nonempty directed set `D` of
positive elements with supremum `s`.  `⊇` is monotonicity of `⌈·⌉`; `⊆` is
**44VIII**: writing `r` for the right-hand side, `r^⊥ d r^⊥ = 0` for every
`d ∈ D`, hence `r^⊥ s r^⊥ = 0`, i.e. `⌈s⌉ ≤ r`. -/
private theorem ceil_isLUB_aux {D : Set A} {s : A} (hD : ∀ d ∈ D, 0 ≤ d)
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hs : IsLUB D s) :
    ceil s = projSup (ceil '' D) := by
  obtain ⟨d₀, hd₀⟩ := hne
  have hs0 : (0 : A) ≤ s := (hD d₀ hd₀).trans (hs.1 hd₀)
  have hP : ∀ p ∈ ceil '' D, IsStarProjection p := by
    rintro _ ⟨d, hd, rfl⟩
    exact (ceil_spec (hD d hd)).1
  refine (projSup_eq hP (ceil_spec hs0).1 ?_ ?_).symm
  · rintro _ ⟨d, hd, rfl⟩
    exact ceil_mono (hD d hd) (hs.1 hd)
  · intro q hq hle
    refine (ceil_spec hs0).2.2 q hq ?_
    rw [mul_eq_iff_mul_ortho_eq_zero, ← conj_sa_eq_zero_iff hs0 hq.one_sub.isSelfAdjoint]
    refine conj_eq_zero_of_isLUB (fun d hd => IsSelfAdjoint.of_nonneg (hD d hd))
      ⟨d₀, hd₀⟩ hdir hs hq.one_sub.isSelfAdjoint fun d hd => ?_
    rw [conj_sa_eq_zero_iff (hD d hd) hq.one_sub.isSelfAdjoint,
      ← mul_eq_iff_mul_ortho_eq_zero]
    exact (ceil_le_iff (hD d hd) hq).mp (hle _ ⟨d, hd, rfl⟩)

/-- **56XVII** (`ceil-supremum`, vn.tex:2554, Exercise), part 1:
`⌈⋁D⌉ = ⋃_{d∈D} ⌈d⌉` for a directed set `D` of effects. -/
theorem ceil_supremum_1 (D : Set A) (s : A) (hD : ∀ d ∈ D, d ∈ effects A)
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hs : IsLUB D s) :
    ceil s = projSup (ceil '' D) :=
  ceil_isLUB_aux (fun d hd => (hD d hd).1) hne hdir hs

/-- **56XVII** (`ceil-supremum`, vn.tex:2554, Exercise), part 2:
`⌊⋀D⌋ = ⋂_{d∈D} ⌊d⌋` for a filtered set `D` of effects. -/
theorem ceil_supremum_2 (D : Set A) (s : A) (hD : ∀ d ∈ D, d ∈ effects A)
    (hne : D.Nonempty) (hdir : DirectedOn (· ≥ ·) D) (hs : IsGLB D s) :
    floor s = projInf (floor '' D) := by
  -- no `ad_normal` needed here: `⌊·⌋` is characterized order-theoretically
  obtain ⟨d₀, hd₀⟩ := hne
  have hseff : s ∈ effects A :=
    ⟨hs.2 fun d hd => (hD d hd).1, (hs.1 hd₀).trans (hD d₀ hd₀).2⟩
  have hP : ∀ p ∈ floor '' D, IsStarProjection p := by
    rintro _ ⟨d, hd, rfl⟩
    exact (floor_spec (hD d hd)).1
  refine (projInf_eq hP (floor_spec hseff).1 ?_ ?_).symm
  · rintro _ ⟨d, hd, rfl⟩
    exact (floor_isGreatest (hD d hd)).2
      ⟨(floor_spec hseff).1, (floor_le hseff).trans (hs.1 hd)⟩
  · intro q hq hle
    refine (floor_isGreatest hseff).2 ⟨hq, hs.2 fun d hd => ?_⟩
    exact (hle _ ⟨d, hd, rfl⟩).trans (floor_le (hD d hd))

/-- **56XVII** (`ceil-supremum`, vn.tex:2554, Exercise), part 3: `⌈·⌉` does
not preserve filtered infima and `⌊·⌋` does not preserve directed suprema
(witness `1, ½, ⅓, …`); consequently neither is ultraweakly, ultrastrongly,
or norm continuous on `[0,1]_A` (for nontrivial `A`).  We record the norm
discontinuity. -/
theorem ceil_supremum_3 [Nontrivial A] :
    ¬ContinuousOn (fun a : A => ceil a) (effects A) ∧
      ¬ContinuousOn (fun a : A => floor a) (effects A) :=
  sorry

/-- **56XVIII** (`sum-of-orthogonal-projections`, vn.tex:2577, Exercise):
for a family `(pᵢ)_{i∈I}` of pairwise orthogonal projections, the net of
partial sums `∑_{i∈F} pᵢ` (over finite `F ⊆ I`) converges ultrastrongly to
`⋃ᵢ pᵢ`. -/
theorem sum_of_orthogonal_projections {ι : Type*} (p : ι → A)
    (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise fun i j => p i * p j = 0) :
    USTendsto (fun F : Finset ι => ∑ i ∈ F, p i) atTop
      (projSup (Set.range p)) :=
  sorry

/-! ## Parsec 570 (`floor-sequential-product`) -/

/-- **57I** (vn.tex:2590, Lemma): for effects `a`, `b`:
`⌊√a b √a⌋ = ⌊a⌋ ∩ ⌊b⌋`, the greatest projection below both `a` and
`b`. -/
theorem floor_sequential_product (a b : A) (ha : a ∈ effects A)
    (hb : b ∈ effects A) :
    floor (CFC.sqrt a * b * CFC.sqrt a) = projInf {floor a, floor b} := by
  have hsa : star (CFC.sqrt a) = CFC.sqrt a :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  have haa : CFC.sqrt a * CFC.sqrt a = a := CFC.sqrt_mul_sqrt_self a ha.1
  set c : A := CFC.sqrt a * b * CFC.sqrt a with hcdef
  have hcnn : (0 : A) ≤ c := by
    have := star_left_conjugate_nonneg hb.1 (CFC.sqrt a)
    rwa [hsa] at this
  have hca : c ≤ a := by
    have h := star_left_conjugate_le_conjugate hb.2 (CFC.sqrt a)
    rw [hsa, mul_one, haa] at h
    exact h
  have hceff : c ∈ effects A := ⟨hcnn, hca.trans ha.2⟩
  obtain ⟨⟨hfp, hfc⟩, hfgreat⟩ := floor_isGreatest hceff
  set f : A := floor c with hfdef
  -- `f ≤ a`, hence `f √a = f`, and `f c f = f`, so `f b f = f`, so `f ≤ b`
  have hfa : f ≤ a := hfc.trans hca
  have hfsqrt : CFC.sqrt a * f = f :=
    ((projection_below_effect a f ha hfp).out 0 2).mp hfa
  have hfsqrt' : f * CFC.sqrt a = f :=
    ((projection_below_effect a f ha hfp).out 0 1).mp hfa
  have hfcf : f * c * f = f := by
    have h1 : f * c = f := ((projection_below_effect c f hceff hfp).out 0 7).mp hfc
    rw [h1, hfp.isIdempotentElem.eq]
  have hfbf : f * b * f = f := by
    calc f * b * f = (f * CFC.sqrt a) * b * (CFC.sqrt a * f) := by
          rw [hfsqrt, hfsqrt']
      _ = f * c * f := by rw [hcdef]; noncomm_ring
      _ = f := hfcf
  have hfb : f ≤ b := by
    refine (proj_le_iff hb hfp).mpr ?_
    have hzero : f * (1 - b) * f = 0 := by
      have e : f * (1 - b) * f = f * f - f * b * f := by noncomm_ring
      rw [e, hfbf, hfp.isIdempotentElem.eq, sub_self]
    have h1 : (1 - b) * f = 0 :=
      (conj_sa_eq_zero_iff (sub_nonneg.mpr hb.2) hfp.isSelfAdjoint).mp hzero
    simpa [(IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hb.2)).star_eq,
      hfp.isSelfAdjoint.star_eq] using congrArg star h1
  -- `f` is the greatest projection below both `⌊a⌋` and `⌊b⌋`
  have hPproj : ∀ p ∈ ({floor a, floor b} : Set A), IsStarProjection p := by
    rintro p (rfl | rfl)
    · exact (floor_spec ha).1
    · exact (floor_spec hb).1
  refine (projInf_eq hPproj hfp ?_ ?_).symm
  · rintro p (rfl | rfl)
    · exact (floor_isGreatest ha).2 ⟨hfp, hfa⟩
    · exact (floor_isGreatest hb).2 ⟨hfp, hfb⟩
  · intro e he hle
    have hea : e ≤ a := (hle _ (by left; rfl)).trans (floor_le ha)
    have heb : e ≤ b := (hle _ (by right; rfl)).trans (floor_le hb)
    refine hfgreat ⟨he, ?_⟩
    refine ((projection_below_effect c e hceff he).out 0 7).mpr ?_
    have h1 : e * CFC.sqrt a = e := ((projection_below_effect a e ha he).out 0 1).mp hea
    have h2 : e * b = e := ((projection_below_effect b e hb he).out 0 7).mp heb
    calc e * c = e * CFC.sqrt a * b * CFC.sqrt a := by rw [hcdef]; noncomm_ring
      _ = e * b * CFC.sqrt a := by rw [h1]
      _ = e * CFC.sqrt a := by rw [h2]
      _ = e := h1

/-! ## Parsec 580

**58I** (vn.tex:2628): discussion — nothing to formalize. -/

/-- **58II** (`floor-difference`, vn.tex:2641, Lemma): for a projection `p`
and an effect `a ≤ p`: `p - ⌈a⌉ = ⌊p - a⌋`. -/
theorem floor_difference (p a : A) (hp : IsStarProjection p)
    (ha : a ∈ effects A) (hap : a ≤ p) :
    p - ceil a = floor (p - a) := by
  obtain ⟨⟨hcp, hac⟩, hcleast⟩ := vna_ceil a ha
  have hcple : ceil a ≤ p := hcleast ⟨hp, hap⟩
  have hpa : p - a ∈ effects A :=
    ⟨sub_nonneg.mpr hap, (sub_le_self p ha.1).trans hp.le_one⟩
  -- `p - ⌈a⌉` is a projection below `p - a`
  have hdproj : IsStarProjection (p - ceil a) :=
    projection_below_projection _ _ hcp hp hcple
  have hdle : p - ceil a ≤ p - a := sub_le_sub_left hac p
  refine ((floor_isGreatest hpa).unique ⟨⟨hdproj, hdle⟩, ?_⟩).symm
  rintro q ⟨hq, hqle⟩
  -- the trick: `a ≤ p - q`, and `p - q` is a projection
  have hqp : q ≤ p := hqle.trans (sub_le_self p ha.1)
  have hpq : IsStarProjection (p - q) := projection_below_projection _ _ hq hp hqp
  have hapq : a ≤ p - q := le_sub_comm.mp hqle
  exact le_sub_comm.mp (hcleast ⟨hpq, hapq⟩)

/-- **58IV** (`ceil-sequential-product`, vn.tex:2663, Proposition):
`⌈pqp⌉ = p ∩ (p^⊥ ∪ q)` for projections `p`, `q`. -/
theorem ceil_sequential_product (p q : A) (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    ceil (p * q * p) = projInf {p, projSup {1 - p, q}} :=
  sorry

/-! ## Parsec 590: Range and Support

**59I** (`ceill`, vn.tex:2684, Notation): the extension of `⌈·⌉` to all
positive `b` — by `⌈b⌉ := ⌈‖b‖⁻¹ b⌉` when `b ≰ 1` — is built into our
definition of `ceil` (the least projection `p` with `bp = b`); the
consistency claim is `ceil_scale` below.  The **support** and **range**
projections of an arbitrary element are defined here.

**59II** (vn.tex:2706, Remark): rationale for the notation — nothing to
formalize. -/

/-- **59I** (`ceill`, vn.tex:2684, Notation), consistency of the extension:
`⌈b⌉ = ⌈‖b‖⁻¹ b⌉` for positive nonzero `b`. -/
theorem ceil_scale (b : A) (hb : 0 ≤ b) (hne : b ≠ 0) :
    ceil b = ceil ((‖b‖⁻¹ : ℂ) • b) := by
  have hn : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hne
  rw [← Complex.ofReal_inv, Complex.coe_smul]
  exact (ceil_smul hb (inv_pos.mpr hn)).symm

/-- **59I** (`ceill`, vn.tex:2684, Notation): the **support projection**
`⌈b⌋ = ⌈b* b⌉` of an element `b` of a von Neumann algebra. -/
noncomputable def suppProj (b : A) : A := ceil (star b * b)

/-- **59I** (`ceill`, vn.tex:2684, Notation): the **range projection**
`⌊b⌉ = ⌈b b*⌉` of an element `b` of a von Neumann algebra. -/
noncomputable def rangeProj (b : A) : A := ceil (b * star b)

/-- **59III** (`ceil-basic`, vn.tex:2728, Exercise), part 1: for positive
`a` and a projection `p`: `pa = a` iff `ap = a` iff `⌈a⌉ ≤ p`; so `⌈a⌉` is
the least projection `p` with `ap = a`. -/
theorem ceil_basic_1 (a p : A) (ha : 0 ≤ a) (hp : IsStarProjection p) :
    List.TFAE [p * a = a, a * p = a, ceil a ≤ p] := by
  obtain ⟨hc1, hc2, hc3⟩ := ceil_spec ha
  have hasa : star a = a := (IsSelfAdjoint.of_nonneg ha).star_eq
  tfae_have 1 → 2 := by
    intro h
    have h' := congrArg star h
    rwa [star_mul, hp.isSelfAdjoint.star_eq, hasa] at h'
  tfae_have 2 → 3 := fun h => hc3 p hp h
  tfae_have 3 → 1 := by
    intro h
    -- `⌈a⌉ ≤ p` gives `p⌈a⌉ = ⌈a⌉`, and `⌈a⌉a = a` is `a⌈a⌉ = a` starred
    have h1 : ceil a * p = ceil a :=
      ((projection_below_effect p (ceil a) ⟨hp.nonneg, hp.le_one⟩ hc1).out 0 7).mp h
    have h2 : p * ceil a = ceil a := by
      have h' := congrArg star h1
      rwa [star_mul, hp.isSelfAdjoint.star_eq, hc1.isSelfAdjoint.star_eq] at h'
    have h3 : ceil a * a = a := by
      have h' := congrArg star hc2
      rwa [star_mul, hc1.isSelfAdjoint.star_eq, hasa] at h'
    calc p * a = p * (ceil a * a) := by rw [h3]
      _ = p * ceil a * a := by noncomm_ring
      _ = a := by rw [h2, h3]
  tfae_finish

/-- **59III** (`ceil-basic`, vn.tex:2728, Exercise), part 2:
`⌈a⌉a = a⌈a⌉`, and in fact whatever commutes with positive `a` commutes
with `⌈a⌉`. -/
theorem ceil_basic_2 (a b : A) (ha : 0 ≤ a) (h : b * a = a * b) :
    b * ceil a = ceil a * b :=
  vna_ceil_comm a ha b h

/-- **59III** (`ceil-basic`, vn.tex:2728, Exercise), part 3: `a = 0` iff
`⌈a⌉ = 0` for positive `a`. -/
theorem ceil_basic_3 (a : A) (ha : 0 ≤ a) : a = 0 ↔ ceil a = 0 := by
  refine ⟨fun h => by rw [h, ceil_zero], fun h => ?_⟩
  have h2 := (ceil_spec ha).2.1
  rwa [h, mul_zero, eq_comm] at h2

/-- **59III** (`ceil-basic`, vn.tex:2728, Exercise), part 4:
`⌈a⌉ = ⌈λa⌉` for `λ > 0`, and `⌈a + b⌉ = ⌈a⌉ ∪ ⌈b⌉` for positive `a`,
`b`. -/
theorem ceil_basic_4 (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) (l : ℝ)
    (hl : 0 < l) :
    ceil ((l : ℂ) • a) = ceil a ∧ ceil (a + b) = projSup {ceil a, ceil b} := by
  refine ⟨by rw [Complex.coe_smul]; exact ceil_smul ha hl, ?_⟩
  have hab : (0 : A) ≤ a + b := add_nonneg ha hb
  have hP : ∀ p ∈ ({ceil a, ceil b} : Set A), IsStarProjection p := by
    rintro p (rfl | rfl)
    · exact (ceil_spec ha).1
    · exact (ceil_spec hb).1
  -- for a projection `p`: `(a+b)p = a+b ↔ ap = a ∧ bp = b`, because
  -- `p^⊥(a+b)p^⊥ = p^⊥ap^⊥ + p^⊥bp^⊥` is a sum of two positives
  have hsplit : ∀ p : A, IsStarProjection p →
      ((a + b) * p = a + b ↔ (a * p = a ∧ b * p = b)) := by
    intro p hp
    have hpsa := hp.one_sub.isSelfAdjoint
    rw [mul_eq_iff_mul_ortho_eq_zero, mul_eq_iff_mul_ortho_eq_zero,
      mul_eq_iff_mul_ortho_eq_zero, ← conj_sa_eq_zero_iff hab hpsa,
      ← conj_sa_eq_zero_iff ha hpsa, ← conj_sa_eq_zero_iff hb hpsa]
    have hexpand : (1 - p) * (a + b) * (1 - p)
        = (1 - p) * a * (1 - p) + (1 - p) * b * (1 - p) := by noncomm_ring
    have hA : (0 : A) ≤ (1 - p) * a * (1 - p) := by
      have h := star_left_conjugate_nonneg ha (1 - p)
      rwa [hpsa.star_eq] at h
    have hB : (0 : A) ≤ (1 - p) * b * (1 - p) := by
      have h := star_left_conjugate_nonneg hb (1 - p)
      rwa [hpsa.star_eq] at h
    rw [hexpand]
    refine ⟨fun h => ⟨?_, ?_⟩, fun h => by rw [h.1, h.2, add_zero]⟩
    · refine le_antisymm ?_ hA
      have he : (1 - p) * a * (1 - p) = -((1 - p) * b * (1 - p)) := by
        rw [eq_neg_iff_add_eq_zero]; exact h
      rw [he, neg_nonpos]; exact hB
    · refine le_antisymm ?_ hB
      have he : (1 - p) * b * (1 - p) = -((1 - p) * a * (1 - p)) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
      rw [he, neg_nonpos]; exact hA
  obtain ⟨hs1, hs2, hs3⟩ := ceil_spec hab
  obtain ⟨hab1, hab2⟩ := (hsplit _ hs1).mp hs2
  refine (projSup_eq hP hs1 ?_ ?_).symm
  · rintro p (rfl | rfl)
    · exact (ceil_spec ha).2.2 _ hs1 hab1
    · exact (ceil_spec hb).2.2 _ hs1 hab2
  · intro q hq hle
    refine hs3 q hq ((hsplit q hq).mpr ⟨?_, ?_⟩)
    · exact ((ceil_basic_1 a q ha hq).out 2 1).mp (hle _ (by left; rfl))
    · exact ((ceil_basic_1 b q hb hq).out 2 1).mp (hle _ (by right; rfl))

/-- **59III** (`ceil-basic`, vn.tex:2728, Exercise), part 5: `⌈a²⌉ = ⌈a⌉`
for positive `a`. -/
theorem ceil_basic_5 (a : A) (ha : 0 ≤ a) : ceil (a ^ 2) = ceil a := by
  have hsa : star a = a := (IsSelfAdjoint.of_nonneg ha).star_eq
  have hsq : a ^ 2 = star a * a := by rw [hsa, sq]
  have h2 : (0 : A) ≤ a ^ 2 := hsq ▸ star_mul_self_nonneg a
  refine ceil_congr h2 ha fun p hp => ?_
  rw [hsq]
  exact star_mul_self_absorb_iff a hp

/-- **59IV** (`ceil-pos-part`, vn.tex:2756, Exercise), part 1:
`⌈a₊⌉⌈a₋⌉ = 0` for self-adjoint `a`. -/
theorem ceil_pos_part_1 (a : A) (ha : IsSelfAdjoint a) :
    ceil (posPart a) * ceil (negPart a) = 0 := by
  -- `a₊a₋ = 0` (`cstar-pos-neg-part`), so `⌈a₊⌉a₋ = 0` and then
  -- `⌈a₊⌉⌈a₋⌉ = 0`, by `ceil_mul_eq_zero` twice
  have h1 : ceil (posPart a) * negPart a = 0 :=
    ceil_mul_eq_zero (CFC.posPart_nonneg a) (CFC.posPart_mul_negPart a)
  have h2 : negPart a * ceil (posPart a) = 0 := by
    have h := congrArg star h1
    rw [star_mul, (IsSelfAdjoint.of_nonneg (CFC.negPart_nonneg a)).star_eq,
      (ceil_spec (CFC.posPart_nonneg a)).1.isSelfAdjoint.star_eq, star_zero] at h
    exact h
  have h3 : ceil (negPart a) * ceil (posPart a) = 0 :=
    ceil_mul_eq_zero (CFC.negPart_nonneg a) h2
  have h := congrArg star h3
  rw [star_mul, (ceil_spec (CFC.negPart_nonneg a)).1.isSelfAdjoint.star_eq,
    (ceil_spec (CFC.posPart_nonneg a)).1.isSelfAdjoint.star_eq, star_zero] at h
  exact h

/-- **59IV** (`ceil-pos-part`, vn.tex:2756, Exercise), part 2:
`⌈a₊⌉a = a⌈a₊⌉ = a₊` and `⌈a₋⌉a = a⌈a₋⌉ = -a₋` for self-adjoint `a`. -/
theorem ceil_pos_part_2 (a : A) (ha : IsSelfAdjoint a) :
    ceil (posPart a) * a = posPart a ∧
      a * ceil (posPart a) = posPart a ∧
      ceil (negPart a) * a = -negPart a ∧
      a * ceil (negPart a) = -negPart a := by
  have hp0 := CFC.posPart_nonneg a
  have hn0 := CFC.negPart_nonneg a
  have hsplit : posPart a - negPart a = a := CFC.posPart_sub_negPart a ha
  -- `⌈a₊⌉a₊ = a₊`, `⌈a₊⌉a₋ = 0` and dually
  have e1 : ceil (posPart a) * posPart a = posPart a :=
    ((ceil_basic_1 (posPart a) _ hp0 (ceil_spec hp0).1).out 2 0).mp le_rfl
  have e2 : ceil (negPart a) * negPart a = negPart a :=
    ((ceil_basic_1 (negPart a) _ hn0 (ceil_spec hn0).1).out 2 0).mp le_rfl
  have e3 : ceil (posPart a) * negPart a = 0 :=
    ceil_mul_eq_zero hp0 (CFC.posPart_mul_negPart a)
  have e4 : ceil (negPart a) * posPart a = 0 :=
    ceil_mul_eq_zero hn0 (CFC.negPart_mul_posPart a)
  have star_ceil_pos := (ceil_spec hp0).1.isSelfAdjoint.star_eq
  have star_ceil_neg := (ceil_spec hn0).1.isSelfAdjoint.star_eq
  have hpsa : star (posPart a) = posPart a := (IsSelfAdjoint.of_nonneg hp0).star_eq
  have hnsa : star (negPart a) = negPart a := (IsSelfAdjoint.of_nonneg hn0).star_eq
  have l1 : ceil (posPart a) * a = posPart a := by
    calc ceil (posPart a) * a
        = ceil (posPart a) * (posPart a - negPart a) := by rw [hsplit]
      _ = posPart a := by rw [mul_sub, e1, e3, sub_zero]
  have l3 : ceil (negPart a) * a = -negPart a := by
    calc ceil (negPart a) * a
        = ceil (negPart a) * (posPart a - negPart a) := by rw [hsplit]
      _ = -negPart a := by rw [mul_sub, e2, e4, zero_sub]
  refine ⟨l1, ?_, l3, ?_⟩
  · have h := congrArg star l1
    rwa [star_mul, ha.star_eq, star_ceil_pos, hpsa] at h
  · have h := congrArg star l3
    rwa [star_mul, ha.star_eq, star_ceil_neg, star_neg, hnsa] at h

/-- **59V** (`ceil-suprema`, vn.tex:2768, Exercise):
`⌈⋁D⌉ = ⋃_{d∈D} ⌈d⌉` for a bounded directed set `D` of *positive*
elements. -/
theorem ceil_suprema (D : Set A) (s : A) (hD : ∀ d ∈ D, 0 ≤ d)
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hs : IsLUB D s) :
    ceil s = projSup (ceil '' D) :=
  ceil_isLUB_aux hD hne hdir hs

/-- **59VI** (`ceill-basic`, vn.tex:2773, Exercise), part 1: the support
`⌈a⌋ = ⌈a* a⌉` is the least projection `p` with `ap = a`. -/
theorem ceill_basic_1 (a : A) :
    IsLeast {p : A | IsStarProjection p ∧ a * p = a} (suppProj a) := by
  obtain ⟨h1, h2, h3⟩ := ceil_spec (star_mul_self_nonneg a)
  refine ⟨⟨h1, (star_mul_self_absorb_iff a h1).mp h2⟩, ?_⟩
  rintro q ⟨hq, hqa⟩
  exact h3 q hq ((star_mul_self_absorb_iff a hq).mpr hqa)

/-- **59VI** (`ceill-basic`, vn.tex:2773, Exercise), part 2: the range
`⌊a⌉ = ⌈a a*⌉` is the least projection `p` with `pa = a`. -/
theorem ceill_basic_2 (a : A) :
    IsLeast {p : A | IsStarProjection p ∧ p * a = a} (rangeProj a) := by
  have hstar : ∀ p : A, IsStarProjection p → (p * a = a ↔ star a * p = star a) := by
    intro p hp
    constructor <;> intro h
    · have h' := congrArg star h
      rwa [star_mul, hp.isSelfAdjoint.star_eq] at h'
    · have h' := congrArg star h
      rwa [star_mul, hp.isSelfAdjoint.star_eq, star_star] at h'
  have hrw : rangeProj a = suppProj (star a) := by
    rw [rangeProj, suppProj, star_star]
  obtain ⟨⟨h1, h2⟩, h3⟩ := ceill_basic_1 (star a)
  rw [hrw]
  refine ⟨⟨h1, (hstar _ h1).mpr h2⟩, ?_⟩
  rintro q ⟨hq, hqa⟩
  exact h3 ⟨hq, (hstar q hq).mp hqa⟩

/-- **59VI** (`ceill-basic`, vn.tex:2773, Exercise), part 3:
`⌈a*⌋ = ⌊a⌉` and `⌊a*⌉ = ⌈a⌋`. -/
theorem ceill_basic_3 (a : A) :
    suppProj (star a) = rangeProj a ∧ rangeProj (star a) = suppProj a := by
  constructor
  · rw [suppProj, rangeProj, star_star]
  · rw [rangeProj, suppProj, star_star]

/-- **59VI** (`ceill-basic`, vn.tex:2773, Exercise), part 4:
`⌈ab⌋ ≤ ⌈b⌋` and `⌊ab⌉ ≤ ⌊a⌉`. -/
theorem ceill_basic_4 (a b : A) :
    suppProj (a * b) ≤ suppProj b ∧ rangeProj (a * b) ≤ rangeProj a := by
  constructor
  · refine (ceill_basic_1 (a * b)).2 ⟨(ceill_basic_1 b).1.1, ?_⟩
    rw [mul_assoc, (ceill_basic_1 b).1.2]
  · refine (ceill_basic_2 (a * b)).2 ⟨(ceill_basic_2 a).1.1, ?_⟩
    rw [← mul_assoc, (ceill_basic_2 a).1.2]

end CeilFloor

/-- **59VII** (`hilb-ceil`, vn.tex:2796, Exercise), parts 1–2: for a bounded
operator `T` on a Hilbert space, `⌊T⌉` is the projection onto the closure of
the range of `T`, and `⌈T⌋` is the projection onto the support
`(ker T)^⊥` of `T` (a projection is here identified by its set of fixed
points). -/
theorem hilb_ceil_1 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    {x : H | rangeProj T x = x} = closure (Set.range T) ∧
      {x : H | suppProj T x = x} = ((LinearMap.ker (T : H →ₗ[ℂ] H))ᗮ : Set H) :=
  sorry

/-- **59VII** (`hilb-ceil`, vn.tex:2796, Exercise), part 3: for an effect
`T` on a Hilbert space, `⌊T⌋` is the projection onto
`{x | Tx = x}`. -/
theorem hilb_ceil_2 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : T ∈ effects (H →L[ℂ] H)) :
    {x : H | floor T x = x} = {x : H | T x = x} :=
  sorry

/-! ## Parsec 600 -/

section Functionals

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B]

/-- Kadison's inequality (`omega-norm-basic`, cstar.tex **30IV**.1) for an
np-functional: `|ω(a* b)|² ≤ ω(a* a)·ω(b* b)`. -/
private theorem npFunctional_cauchy_schwarz (ω : NPFunctional A) (a b : A) :
    ((‖ω (star a * b)‖ : ℂ)) ^ 2 ≤ ω (star a * a) * ω (star b * b) :=
  omega_norm_basic_1 ω.toPositiveLinearMap.toLinearMap
    (fun _ hx => npFunctional_nonneg ω hx) a b

private theorem npFunctional_smul_real (ω : NPFunctional A) (r : ℝ) (x : A) :
    ω (r • x) = (r : ℂ) * ω x := by
  rw [← Complex.coe_smul]
  exact map_smul ω.toPositiveLinearMap _ _

/-- Kadison's inequality in the form **60I** uses it: `ω(a) = 0` forces
`ω(√a) = 0`, because `ω(√a)² ≤ ω(1)·ω(a)`. -/
private theorem npFunctional_sqrt_eq_zero {x : A} (hx : 0 ≤ x)
    (ω : NPFunctional A) (h : ω x = 0) : ω (CFC.sqrt x) = 0 := by
  have hcs := npFunctional_cauchy_schwarz ω 1 (CFC.sqrt x)
  rw [star_one, one_mul, mul_one,
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)).star_eq,
    CFC.sqrt_mul_sqrt_self x hx, h, mul_zero] at hcs
  have hnn : (0 : ℝ) ≤ ‖ω (CFC.sqrt x)‖ := norm_nonneg _
  have hle : ((‖ω (CFC.sqrt x)‖ ^ 2 : ℝ) : ℂ) ≤ 0 := by push_cast; exact hcs
  have h2 : (‖ω (CFC.sqrt x)‖ : ℝ) ^ 2 ≤ 0 := by
    exact_mod_cast Complex.real_le_real.mp (by simpa using hle)
  have : ‖ω (CFC.sqrt x)‖ = 0 := by nlinarith
  exact norm_eq_zero.mp this

/-- **60I** (`ceil-functionals-lemma`, vn.tex:2817, Lemma): for positive `a`
and an np-functional `ω`: `ω(a) = 0` iff `ω(⌈a⌉) = 0`. -/
theorem ceil_functionals_lemma (a : A) (ha : 0 ≤ a) (ω : NPFunctional A) :
    ω a = 0 ↔ ω (ceil a) = 0 := by
  -- 60I.20: the claim reduces to the case of an effect by rescaling
  suffices hkey : ∀ b : A, b ∈ effects A → (ω b = 0 ↔ ω (ceil b) = 0) by
    rcases eq_or_ne a 0 with rfl | hane
    · rw [ceil_zero]
    have hn : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr hane
    have hnn : (0 : A) ≤ (‖a‖⁻¹ : ℝ) • a := smul_nonneg (by positivity) ha
    have heff : (‖a‖⁻¹ : ℝ) • a ∈ effects A := by
      refine ⟨hnn, (CStarAlgebra.norm_le_one_iff_of_nonneg _ hnn).mp ?_⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
        inv_mul_cancel₀ (ne_of_gt hn)]
    have hceq : ceil ((‖a‖⁻¹ : ℝ) • a) = ceil a := ceil_smul ha (inv_pos.mpr hn)
    have hkey' := hkey _ heff
    rw [hceq, npFunctional_smul_real, mul_eq_zero] at hkey'
    have hne0 : ((‖a‖⁻¹ : ℝ) : ℂ) ≠ 0 := by
      simpa using (ne_of_gt (inv_pos.mpr hn))
    rw [or_iff_right hne0] at hkey'
    exact hkey'
  intro b hb
  constructor
  · -- 60I.20: `ω(b^{1/2ⁿ}) = 0` for all `n` (Kadison), and `⌈b⌉ = ⋁ₙ b^{1/2ⁿ}`
    intro h
    have hzero : ∀ n : ℕ, ω (sqrtIter b n) = 0 := by
      intro n
      induction n with
      | zero => exact h
      | succ n ih =>
          rw [sqrtIter_succ]
          exact npFunctional_sqrt_eq_zero (sqrtIter_mem_effects hb n).1 ω ih
    -- normality of `ω` turns the supremum into a supremum
    set E : ℕ → selfAdjoint A := fun n =>
      ⟨sqrtIter b n, IsSelfAdjoint.of_nonneg (sqrtIter_mem_effects hb n).1⟩ with hE
    have hEmono : Monotone E := fun m n hmn =>
      Subtype.coe_le_coe.mp (sqrtIter_monotone hb hmn)
    set D : Set (selfAdjoint A) := Set.range E with hD
    have hne : D.Nonempty := ⟨E 0, 0, rfl⟩
    have hdir : DirectedOn (· ≤ ·) D := by
      rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      exact ⟨E (max m n), ⟨max m n, rfl⟩, hEmono (le_max_left _ _),
        hEmono (le_max_right _ _)⟩
    set s : selfAdjoint A := ⟨ceil b, (ceil_spec hb.1).1.isSelfAdjoint⟩ with hs
    have hval : Subtype.val '' D = Set.range (sqrtIter b) := by
      rw [hD, ← Set.range_comp]; rfl
    have hlub : IsLUB D s := by
      refine isLUB_sa_of_isLUB ?_
      rw [hval]
      exact vna_ceil_sup b hb
    have hnorm := ω.preservesDirSups' D s hne hdir hlub
    refine le_antisymm ?_ (npFunctional_nonneg ω (ceil_spec hb.1).1.nonneg)
    refine hnorm.2 ?_
    rintro _ ⟨d, ⟨n, rfl⟩, rfl⟩
    exact le_of_eq (hzero n)
  · -- `b ≤ ⌈b⌉`, so `0 ≤ ω(b) ≤ ω(⌈b⌉) = 0`
    intro h
    refine le_antisymm ?_ (npFunctional_nonneg ω hb.1)
    have := npFunctional_mono ω (vna_ceil b hb).1.2
    rwa [h] at this

/-- **60III** (`ceil-functionals`, vn.tex:2855, Proposition): for positive
`a`, `b`: `⌈a⌉ ≤ ⌈b⌉` iff every np-functional vanishing on `b` vanishes on
`a`. -/
theorem ceil_functionals (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ceil a ≤ ceil b ↔
      ∀ ω : NPFunctional A, ω b = 0 → ω a = 0 := by
  constructor
  · -- 60III.40: `0 ≤ ω(⌈a⌉) ≤ ω(⌈b⌉) = 0`, twice **60I**
    intro h ω hωb
    have h1 : ω (ceil b) = 0 := (ceil_functionals_lemma b hb ω).mp hωb
    have h2 : ω (ceil a) = 0 := by
      refine le_antisymm ?_ (npFunctional_nonneg ω (ceil_spec ha).1.nonneg)
      have hm := npFunctional_mono ω h
      rwa [h1] at hm
    exact (ceil_functionals_lemma a ha ω).mpr h2
  · -- 60III.40: it suffices that `⌈b⌉^⊥⌈a⌉⌈b⌉^⊥ = 0`; test against `ω(r·r)`
    intro h
    have hrp : IsStarProjection ((1 : A) - ceil b) := (ceil_spec hb).1.one_sub
    have hrsa : star ((1 : A) - ceil b) = 1 - ceil b := hrp.isSelfAdjoint.star_eq
    have hbr : (1 - ceil b) * b * (1 - ceil b) = 0 := by
      have hb0 : b * (1 - ceil b) = 0 := by
        rw [mul_sub, mul_one, (ceil_spec hb).2.1, sub_self]
      rw [mul_assoc, hb0, mul_zero]
    have hzero : (1 - ceil b) * ceil a * (1 - ceil b) = 0 := by
      refine np_separating _ fun ω => ?_
      have hωb : conjNP (1 - ceil b) ω b = 0 := by
        rw [conjNP_apply, hrsa, hbr]
        exact npFunctional_zero ω
      have hωa := (ceil_functionals_lemma a ha (conjNP (1 - ceil b) ω)).mp
        (h (conjNP (1 - ceil b) ω) hωb)
      rwa [conjNP_apply, hrsa] at hωa
    exact (conj_ortho_eq_zero_iff
      ⟨(ceil_spec ha).1.nonneg, (ceil_spec ha).1.le_one⟩ (ceil_spec hb).1).mp hzero

/-! `isSelfAdjoint_map_of_positive` and `compNP` (with `compNP_apply`) now
live in `Theses/A/VN/Basic.lean`: the normal Gelfand–Naimark construction of
parsec 480 needs them, and `compNP` *is* the easy half of **48II**. -/

/-- **60V** (`ncp-ceil`, vn.tex:2893, Proposition): for an np-map
`f : A → B` between von Neumann algebras and positive `a`:
`⌈f(a)⌉ = ⌈f(⌈a⌉)⌉`. -/
theorem ncp_ceil (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) (a : A)
    (ha : 0 ≤ a) : ceil (f a) = ceil (f (ceil a)) := by
  -- 60VI: by **60III** it suffices that `ω(f(a)) = 0 ↔ ω(f(⌈a⌉)) = 0`, and
  -- that is **60I** for the np-functional `ω ∘ f`
  have hz : (f (0 : A) : B) = 0 := map_zero f
  have hfa : (0 : B) ≤ f a := by
    have h : (f (0 : A) : B) ≤ f a := f.monotone ha
    rwa [hz] at h
  have hfc : (0 : B) ≤ f (ceil a) := by
    have h : (f (0 : A) : B) ≤ f (ceil a) := f.monotone (ceil_spec ha).1.nonneg
    rwa [hz] at h
  refine le_antisymm ((ceil_functionals _ _ hfa hfc).mpr fun ω hω => ?_)
    ((ceil_functionals _ _ hfc hfa).mpr fun ω hω => ?_)
  · exact (ceil_functionals_lemma a ha (compNP f hf ω)).mpr hω
  · exact (ceil_functionals_lemma a ha (compNP f hf ω)).mp hω

/-- Conjugation `x ↦ c* x c` as a positive linear map (`ad_normal`, **44VIII**,
says it is normal). -/
private noncomputable def conjPMap (c : A) : A →ₚ[ℂ] A where
  toFun := fun x => star c * x * c
  map_add' := fun x y => by noncomm_ring
  map_smul' := fun r x => by
    simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc]
  monotone' := fun _ _ h => star_left_conjugate_le_conjugate h c

private theorem conjPMap_preservesDirSups (c : A) :
    PreservesDirSups ⇑(conjPMap c) := by
  intro D s hne hdir hlub
  have h3 : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, ⟨s, hlub.1⟩⟩
  have hs : dirSup D h3 = s := (isLUB_dirSup D h3).unique hlub
  have hAD := ad_normal c D h3
  rw [hs] at hAD
  exact hAD

/-- **60VII** (`ceil-fundamental`, vn.tex:2906, Exercise), part 1:
`⌈a* b a⌉ = ⌈a* ⌈b⌉ a⌉` for `b ≥ 0`. -/
theorem ceil_fundamental_1 (a b : A) (hb : 0 ≤ b) :
    ceil (star a * b * a) = ceil (star a * ceil b * a) :=
  ncp_ceil (conjPMap a) (conjPMap_preservesDirSups a) b hb

/-- **60VII** (`ceil-fundamental`, vn.tex:2906, Exercise), part 2:
`⌈ab⌋ = ⌈⌈a⌋b⌋` and `⌊ab⌉ = ⌊a⌊b⌉⌉`. -/
theorem ceil_fundamental_2 (a b : A) :
    suppProj (a * b) = suppProj (suppProj a * b) ∧
      rangeProj (a * b) = rangeProj (a * rangeProj b) := by
  have hsa := (ceill_basic_1 a).1.1
  have hrb := (ceill_basic_2 b).1.1
  constructor
  · -- `⌈ab⌋ = ⌈b*(a*a)b⌉ = ⌈b*⌈a*a⌉b⌉ = ⌈b*⌈a⌋⌈a⌋b⌉ = ⌈⌈a⌋b⌋`
    have h1 : star (a * b) * (a * b) = star b * (star a * a) * b := by
      rw [star_mul]; noncomm_ring
    have h2 : star (suppProj a * b) * (suppProj a * b) = star b * suppProj a * b := by
      rw [star_mul, hsa.isSelfAdjoint.star_eq]
      calc star b * suppProj a * (suppProj a * b)
          = star b * (suppProj a * suppProj a) * b := by noncomm_ring
        _ = star b * suppProj a * b := by rw [hsa.isIdempotentElem.eq]
    rw [suppProj, suppProj, h1, h2]
    exact ceil_fundamental_1 b (star a * a) (star_mul_self_nonneg a)
  · -- the same computation for `⌊·⌉`, conjugating by `a*`
    have hnn : (0 : A) ≤ b * star b := by simpa using star_mul_self_nonneg (star b)
    have h1 : (a * b) * star (a * b) = star (star a) * (b * star b) * star a := by
      rw [star_mul, star_star]; noncomm_ring
    have h2 : (a * rangeProj b) * star (a * rangeProj b)
        = star (star a) * rangeProj b * star a := by
      rw [star_mul, star_star, hrb.isSelfAdjoint.star_eq]
      calc a * rangeProj b * (rangeProj b * star a)
          = a * (rangeProj b * rangeProj b) * star a := by noncomm_ring
        _ = a * rangeProj b * star a := by rw [hrb.isIdempotentElem.eq]
    rw [rangeProj, rangeProj, h1, h2]
    exact ceil_fundamental_1 (star a) (b * star b) hnn

/-- Auxiliary: `p ≤ q` gives `pq = p`, for projections. -/
private theorem proj_mul_of_le {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : p ≤ q) : p * q = p :=
  ((projection_below_effect q p ⟨hq.nonneg, hq.le_one⟩ hp).out 0 7).mp h

/-- Auxiliary: for projections, `p ≤ q^⊥` iff `pq = 0`. -/
private theorem proj_le_one_sub_iff {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) : p ≤ 1 - q ↔ p * q = 0 := by
  have h := (projection_below_effect (1 - q) p
    ⟨hq.one_sub.nonneg, hq.one_sub.le_one⟩ hp).out 0 8
  rwa [sub_sub_cancel] at h

/-- Auxiliary: `⌈x⌋ ≤ q` gives `xq = x` (**59VI**.1). -/
private theorem mul_eq_of_suppProj_le {x q : A} (hq : IsStarProjection q)
    (h : suppProj x ≤ q) : x * q = x := by
  obtain ⟨h1, h2⟩ := (ceill_basic_1 x).1
  calc x * q = x * suppProj x * q := by rw [h2]
    _ = x * (suppProj x * q) := by noncomm_ring
    _ = x * suppProj x := by rw [proj_mul_of_le h1 hq h]
    _ = x := h2

/-- Auxiliary: `⌈x⌋ = 0` iff `x = 0`. -/
private theorem suppProj_eq_zero_iff {x : A} : suppProj x = 0 ↔ x = 0 := by
  rw [suppProj, ← ceil_basic_3 _ (star_mul_self_nonneg x),
    CStarRing.star_mul_self_eq_zero_iff]

/-- **60VIII** (`mult-cancellation`, vn.tex:2921, Exercise), part 1:
`cb = 0` iff `⌈c⌋⌊b⌉ = 0` iff `⌈c⌋ ≤ ⌊b⌉^⊥`. -/
theorem mult_cancellation_1 (b c : A) :
    List.TFAE
      [c * b = 0,
       suppProj c * rangeProj b = 0,
       suppProj c ≤ 1 - rangeProj b] := by
  have hsc := (ceill_basic_1 c).1.1
  have hrb := (ceill_basic_2 b).1.1
  tfae_have 1 → 2 := by
    intro h
    -- `c*c b = 0`, so `⌈c⌋b = 0`, so `(bb*)⌈c⌋ = 0`, so `⌊b⌉⌈c⌋ = 0`
    have h1 : (star c * c) * b = 0 := by rw [mul_assoc, h, mul_zero]
    have h2 : suppProj c * b = 0 := ceil_mul_eq_zero (star_mul_self_nonneg c) h1
    have h3 : (b * star b) * suppProj c = 0 := by
      have h' := congrArg star (by rw [← mul_assoc, h2, zero_mul] :
        suppProj c * (b * star b) = 0)
      rwa [star_mul, star_mul, star_star, hsc.isSelfAdjoint.star_eq, star_zero] at h'
    have h4 : rangeProj b * suppProj c = 0 := by
      have hnn : (0 : A) ≤ b * star b := by
        simpa using star_mul_self_nonneg (star b)
      have := ceil_mul_eq_zero hnn h3
      rwa [← rangeProj] at this
    have h' := congrArg star h4
    rwa [star_mul, hsc.isSelfAdjoint.star_eq, hrb.isSelfAdjoint.star_eq,
      star_zero] at h'
  tfae_have 2 → 3 := fun h => (proj_le_one_sub_iff hsc hrb).mpr h
  tfae_have 3 → 1 := by
    intro h
    have h2 : suppProj c * rangeProj b = 0 := (proj_le_one_sub_iff hsc hrb).mp h
    calc c * b = (c * suppProj c) * (rangeProj b * b) := by
          rw [(ceill_basic_1 c).1.2, (ceill_basic_2 b).1.2]
      _ = c * (suppProj c * rangeProj b) * b := by noncomm_ring
      _ = 0 := by rw [h2, mul_zero, zero_mul]
  tfae_finish

/-- **60VIII** (`mult-cancellation`, vn.tex:2921, Exercise), part 2:
`c₁b = c₂b → c₁ = c₂` when `⌈cᵢ⌋ ≤ ⌊b⌉`. -/
theorem mult_cancellation_2 (b c₁ c₂ : A)
    (h₁ : suppProj c₁ ≤ rangeProj b) (h₂ : suppProj c₂ ≤ rangeProj b)
    (h : c₁ * b = c₂ * b) : c₁ = c₂ := by
  have hrb := (ceill_basic_2 b).1.1
  set c : A := c₁ - c₂ with hc
  have hcb : c * b = 0 := by rw [hc, sub_mul, h, sub_self]
  -- `⌈c⌋ ≤ ⌊b⌉` because `c⌊b⌉ = c`
  have hcr : c * rangeProj b = c := by
    rw [hc, sub_mul, mul_eq_of_suppProj_le hrb h₁, mul_eq_of_suppProj_le hrb h₂]
  have hle : suppProj c ≤ rangeProj b := (ceill_basic_1 c).2 ⟨hrb, hcr⟩
  have hzero : suppProj c * rangeProj b = 0 :=
    ((mult_cancellation_1 b c).out 0 1).mp hcb
  have : suppProj c = 0 := by
    rw [← proj_mul_of_le (ceill_basic_1 c).1.1 hrb hle, hzero]
  have := suppProj_eq_zero_iff.mp this
  rwa [hc, sub_eq_zero] at this

/-- **60VIII** (`mult-cancellation`, vn.tex:2921, Exercise), part 3:
`b* c₁ b = b* c₂ b → c₁ = c₂` for `c₁, c₂ ∈ ⌊b⌉A⌊b⌉`. -/
theorem mult_cancellation_3 (b c₁ c₂ : A)
    (h₁ : rangeProj b * c₁ * rangeProj b = c₁)
    (h₂ : rangeProj b * c₂ * rangeProj b = c₂)
    (h : star b * c₁ * b = star b * c₂ * b) : c₁ = c₂ := by
  have hrb := (ceill_basic_2 b).1.1
  have hrbb : rangeProj b * b = b := (ceill_basic_2 b).1.2
  set c : A := c₁ - c₂ with hc
  have hcc : rangeProj b * c * rangeProj b = c := by
    rw [hc, mul_sub, sub_mul, h₁, h₂]
  have hbcb : star b * c * b = 0 := by
    rw [hc, mul_sub, sub_mul, h, sub_self]
  -- first `cb = 0`: `⌊b⌉⌊cb⌉ = 0` by part 1 applied to `b*·(cb)`
  have hcb : c * b = 0 := by
    have hstep : suppProj (star b) * rangeProj (c * b) = 0 :=
      ((mult_cancellation_1 (c * b) (star b)).out 0 1).mp (by
        rw [← mul_assoc]; exact hbcb)
    rw [(ceill_basic_3 b).1] at hstep
    calc c * b = rangeProj b * c * rangeProj b * b := by rw [hcc]
      _ = rangeProj b * (c * b) := by rw [mul_assoc, mul_assoc, hrbb]
      _ = rangeProj b * (rangeProj (c * b) * (c * b)) := by
          rw [(ceill_basic_2 (c * b)).1.2]
      _ = (rangeProj b * rangeProj (c * b)) * (c * b) := by noncomm_ring
      _ = 0 := by rw [hstep, zero_mul]
  -- then `⌈c⌋ ≤ ⌊b⌉` and part 1 give `⌈c⌋ = 0`
  have hcr : c * rangeProj b = c := by
    calc c * rangeProj b = rangeProj b * c * rangeProj b * rangeProj b := by rw [hcc]
      _ = rangeProj b * c * rangeProj b := by
          rw [mul_assoc, hrb.isIdempotentElem.eq]
      _ = c := hcc
  have hle : suppProj c ≤ rangeProj b := (ceill_basic_1 c).2 ⟨hrb, hcr⟩
  have hzero : suppProj c * rangeProj b = 0 :=
    ((mult_cancellation_1 b c).out 0 1).mp hcb
  have hs0 : suppProj c = 0 := by
    rw [← proj_mul_of_le (ceill_basic_1 c).1.1 hrb hle, hzero]
  have := suppProj_eq_zero_iff.mp hs0
  rwa [hc, sub_eq_zero] at this

/-- **60IX** (`ncp-union`, vn.tex:2942, Exercise), part 1:
`⌈f(p ∪ q)⌉ = ⌈f(p)⌉ ∪ ⌈f(q)⌉` for an np-map `f` and projections `p`,
`q`. -/
theorem ncp_union_1 (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) (p q : A)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ceil (f (projSup {p, q})) = projSup {ceil (f p), ceil (f q)} := by
  -- the hint: `p ∪ q = ⌈½p + ½q⌉` (**56XIII**.2), so `⌈f(p∪q)⌉ = ⌈f(½p+½q)⌉`
  -- by **60V**, and `⌈½f(p) + ½f(q)⌉ = ⌈f p⌉ ∪ ⌈f q⌉` by **59III**.4
  have hpe : p ∈ effects A := ⟨hp.nonneg, hp.le_one⟩
  have hqe : q ∈ effects A := ⟨hq.nonneg, hq.le_one⟩
  set c : A := ((2⁻¹ : ℝ) : ℂ) • p + (((1 - 2⁻¹ : ℝ)) : ℂ) • q with hc
  have hleast := (ceil_floor_basic_2 p q hpe hqe 2⁻¹ (by norm_num) (by norm_num)).2
  rw [ceil_of_isStarProjection hp, ceil_of_isStarProjection hq] at hleast
  have hPproj : ∀ r ∈ ({p, q} : Set A), IsStarProjection r := by
    rintro r (rfl | rfl)
    · exact hp
    · exact hq
  have hsup : projSup ({p, q} : Set A) = ceil c := by
    refine projSup_eq hPproj hleast.1.1 ?_ ?_
    · rintro r (rfl | rfl)
      · exact hleast.1.2.1
      · exact hleast.1.2.2
    · intro r hr hle
      exact hleast.2 ⟨hr, hle _ (by left; rfl), hle _ (by right; rfl)⟩
  have hcnn : (0 : A) ≤ c := by
    rw [hc, Complex.coe_smul, Complex.coe_smul]
    exact add_nonneg (smul_nonneg (by norm_num) hp.nonneg)
      (smul_nonneg (by norm_num) hq.nonneg)
  have hfp : (0 : B) ≤ f p := by
    have hz : (f (0 : A) : B) = 0 := map_zero f
    have h : (f (0 : A) : B) ≤ f p := f.monotone hp.nonneg
    rwa [hz] at h
  have hfq : (0 : B) ≤ f q := by
    have hz : (f (0 : A) : B) = 0 := map_zero f
    have h : (f (0 : A) : B) ≤ f q := f.monotone hq.nonneg
    rwa [hz] at h
  have hfc : f c = ((2⁻¹ : ℝ) : ℂ) • f p + (((1 - 2⁻¹ : ℝ)) : ℂ) • f q := by
    rw [hc, map_add, map_smul, map_smul]
  rw [hsup, ← ncp_ceil f hf c hcnn, hfc]
  have h5 := (ceil_basic_4 (f p) (f q) hfp hfq 2⁻¹ (by norm_num)).1
  have h6 := (ceil_basic_4 (f q) (f p) hfq hfp (1 - 2⁻¹) (by norm_num)).1
  have hsum : ceil (((2⁻¹ : ℝ) : ℂ) • f p + (((1 - 2⁻¹ : ℝ)) : ℂ) • f q)
      = projSup {ceil (((2⁻¹ : ℝ) : ℂ) • f p), ceil ((((1 - 2⁻¹ : ℝ)) : ℂ) • f q)} :=
    (ceil_basic_4 _ _ (by rw [Complex.coe_smul]; exact smul_nonneg (by norm_num) hfp)
      (by rw [Complex.coe_smul]; exact smul_nonneg (by norm_num) hfq) 1 one_pos).2
  rw [hsum, h5, h6]

/-- **60IX** (`ncp-union`, vn.tex:2942, Exercise), part 2:
`⌈f(⋃P)⌉ = ⋃_{p∈P} ⌈f(p)⌉` for every set `P` of projections. -/
theorem ncp_union_2 (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) (P : Set A)
    (hP : ∀ p ∈ P, IsStarProjection p) :
    ceil (f (projSup P)) = projSup ((fun p => ceil (f p)) '' P) := by
  -- Write `r` for the right-hand side.  The set `D` of projections `q` with
  -- `⌈f(q)⌉ ≤ r` contains `P`, is closed under binary joins by **60IX**.1, and
  -- contains its own directed supremum because `f` is normal (**59V**).  Hence
  -- `⋃P ≤ ⋁D ∈ D`, which gives `⌈f(⋃P)⌉ ≤ r`.
  classical
  have hz : (f (0 : A) : B) = 0 := map_zero f
  have hfnn : ∀ a : A, 0 ≤ a → (0 : B) ≤ f a := fun a ha => by
    have h : (f (0 : A) : B) ≤ f a := f.monotone ha
    rwa [hz] at h
  have hRproj : ∀ x ∈ ((fun p => ceil (f p)) '' P), IsStarProjection x := by
    rintro _ ⟨p, hp, rfl⟩
    exact (ceil_spec (hfnn _ (hP p hp).nonneg)).1
  obtain ⟨hrproj, hrub, hrleast⟩ := projSup_spec hRproj
  obtain ⟨hsproj, hsub, hsleast⟩ := projSup_spec hP
  refine le_antisymm ?_ (hrleast _ (ceil_spec (hfnn _ hsproj.nonneg)).1 ?_)
  · set D : Set A := {q : A | IsStarProjection q ∧
      ceil (f q) ≤ projSup ((fun p => ceil (f p)) '' P)} with hDdef
    have hDproj : ∀ q ∈ D, IsStarProjection q := fun _ hq => hq.1
    have hPD : P ⊆ D := fun p hp => ⟨hP p hp, hrub _ ⟨p, hp, rfl⟩⟩
    have hne : D.Nonempty :=
      ⟨0, IsStarProjection.zero A, by rw [hz, ceil_zero]; exact hrproj.nonneg⟩
    have hdir : DirectedOn (· ≤ ·) D := by
      rintro x ⟨hx, hxle⟩ y ⟨hy, hyle⟩
      have hxy : ∀ p ∈ ({x, y} : Set A), IsStarProjection p := by
        rintro p (rfl | rfl)
        exacts [hx, hy]
      obtain ⟨hjp, hjub, -⟩ := projSup_spec hxy
      refine ⟨projSup {x, y}, ⟨hjp, ?_⟩, hjub _ (by left; rfl), hjub _ (by right; rfl)⟩
      rw [ncp_union_1 f hf x y hx hy]
      refine (projSup_spec ?_).2.2 _ hrproj ?_
      · rintro p (rfl | rfl)
        exacts [(ceil_spec (hfnn _ hx.nonneg)).1, (ceil_spec (hfnn _ hy.nonneg)).1]
      · rintro p (rfl | rfl)
        exacts [hxle, hyle]
    set D' : Set (selfAdjoint A) := {d : selfAdjoint A | (d : A) ∈ D} with hD'def
    have hval : Subtype.val '' D' = D := by
      ext x
      exact ⟨by rintro ⟨d, hd, rfl⟩; exact hd,
        fun hx => ⟨⟨x, (hDproj x hx).isSelfAdjoint⟩, hx, rfl⟩⟩
    obtain ⟨d₀, hd₀⟩ := id hne
    have hne' : D'.Nonempty := ⟨⟨d₀, (hDproj d₀ hd₀).isSelfAdjoint⟩, hd₀⟩
    have hdir' : DirectedOn (· ≤ ·) D' := by
      intro x hx y hy
      obtain ⟨c, hc, hxc, hyc⟩ := hdir _ hx _ hy
      exact ⟨⟨c, (hDproj c hc).isSelfAdjoint⟩, hc, hxc, hyc⟩
    have hbdd' : BddAbove D' :=
      ⟨⟨1, IsSelfAdjoint.one A⟩, fun d hd => (hDproj _ hd).le_one⟩
    have h3 : D'.Nonempty ∧ DirectedOn (· ≤ ·) D' ∧ BddAbove D' := ⟨hne', hdir', hbdd'⟩
    have hlubSA : IsLUB D' (dirSup D' h3) := isLUB_dirSup D' h3
    set t : A := ((dirSup D' h3 : selfAdjoint A) : A) with htdef
    have hlub : IsLUB D t := by
      rw [← hval]; exact isLUB_coe_of_isLUB hne' hlubSA
    have htproj : IsStarProjection t :=
      vna_directed_supremum_projections D t hDproj hne hdir hlub
    have hfimg : IsLUB (⇑f '' D) (f t) := by
      have h := hf D' (dirSup D' h3) hne' hdir' hlubSA
      rwa [show (fun d : selfAdjoint A => f (d : A)) '' D' = ⇑f '' D by
        rw [← hval, Set.image_image]] at h
    have hdirf : DirectedOn (· ≤ ·) (⇑f '' D) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨c, hc, hxc, hyc⟩ := hdir x hx y hy
      exact ⟨f c, ⟨c, hc, rfl⟩, f.monotone hxc, f.monotone hyc⟩
    have hceilt : ceil (f t) ≤ projSup ((fun p => ceil (f p)) '' P) := by
      rw [ceil_isLUB_aux (D := ⇑f '' D)
        (by rintro _ ⟨d, hd, rfl⟩; exact hfnn _ (hDproj d hd).nonneg)
        ⟨f d₀, d₀, hd₀, rfl⟩ hdirf hfimg]
      refine (projSup_spec ?_).2.2 _ hrproj ?_
      · rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
        exact (ceil_spec (hfnn _ (hDproj d hd).nonneg)).1
      · rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
        exact hd.2
    refine le_trans (ceil_mono (hfnn _ hsproj.nonneg) (f.monotone ?_)) hceilt
    exact hsleast t htproj fun p hp => hlub.1 (hPD hp)
  · rintro _ ⟨p, hp, rfl⟩
    exact ceil_mono (hfnn _ (hP p hp).nonneg) (f.monotone (hsub p hp))

/-- **60IX** (`ncp-union`, vn.tex:2942, Exercise), part 3: there is a
greatest projection `e` with `f(e) = 0`. -/
theorem ncp_union_3 (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) :
    ∃ e : A, IsGreatest {p : A | IsStarProjection p ∧ f p = 0} e := by
  -- take `e = ⋃E` with `E` the set of projections killed by `f`; by part 2,
  -- `⌈f(e)⌉ = ⋃_{p∈E} ⌈f(p)⌉ = 0`, so `f(e) = 0`
  classical
  set E : Set A := {p : A | IsStarProjection p ∧ f p = 0} with hEdef
  have hE : ∀ p ∈ E, IsStarProjection p := fun _ hp => hp.1
  obtain ⟨heproj, heub, -⟩ := projSup_spec hE
  refine ⟨projSup E, ⟨heproj, ?_⟩, fun p hp => heub p hp⟩
  have himg : ∀ x ∈ ((fun p => ceil (f p)) '' E), IsStarProjection x := by
    rintro _ ⟨p, hp, rfl⟩
    show IsStarProjection (ceil (f p))
    rw [hp.2, ceil_zero]
    exact IsStarProjection.zero B
  have hzero : projSup ((fun p => ceil (f p)) '' E) = 0 := by
    refine projSup_eq himg (IsStarProjection.zero B) ?_ fun q hq _ => hq.nonneg
    rintro _ ⟨p, hp, rfl⟩
    show ceil (f p) ≤ 0
    rw [hp.2, ceil_zero]
  have h := ncp_union_2 f hf E hE
  rw [hzero] at h
  have hfe : (0 : B) ≤ f (projSup E) := by
    have h0 : (f (0 : A) : B) ≤ f (projSup E) := f.monotone heproj.nonneg
    rwa [map_zero f] at h0
  exact (ceil_basic_3 _ hfe).mpr h

/-! ## Parsec 610

**61I** (vn.tex:2967): the equation `⌈f(⌈a⌋)⌉ = ⌈f(a)⌋` fails for np-maps —
nothing to formalize. -/

/-- **61II** (`ncp-ceill`, vn.tex:2983, Proposition): for an *ncp*-map
`f : A → B` and any `a`: `⌈f(a)⌋ ≤ ⌈f(⌈a⌋)⌉` and `⌊f(a)⌉ ≤ ⌈f(⌊a⌉)⌉`.
(The thesis displays the inequalities in the opposite direction, but its
proof — via `f(a)* f(a) ≤ ‖f(1)‖² f(a* a)` — establishes the direction
stated here, and the displayed direction fails, e.g. for the trace on `M₂`
at `a = e₁₂`.) -/
theorem ncp_ceill (f : NCPMap A B) (a : A) :
    suppProj (f a) ≤ ceil (f (suppProj a)) ∧
      rangeProj (f a) ≤ ceil (f (rangeProj a)) :=
  sorry

/-! ## Parsec 620 -/

/-- **62I** (vn.tex:3010, Proposition): for an ncpsu-map `f : A → B` and an
effect `a`: `⌊f(a)⌋ = ⌊f(⌊a⌋)⌋`. -/
theorem ncpsu_floor (f : NCPSUMap A B) (a : A) (ha : a ∈ effects A) :
    floor (f.toNCPMap a) = floor (f.toNCPMap (floor a)) :=
  sorry

/-! ## Parsec 630: Carrier -/

/-- **63I** (`carrier`, vn.tex:3043, Definition), well-definedness (via
**60IX**): every np-map `f : A → B` has a least projection `p` with
`f(p^⊥) = 0`. -/
theorem exists_carrier (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) :
    ∃! p : A, IsStarProjection p ∧ f (1 - p) = 0 ∧
      ∀ q : A, IsStarProjection q → f (1 - q) = 0 → p ≤ q := by
  -- the carrier is `e^⊥` for `e` the greatest projection with `f(e) = 0`
  -- (**60IX**.3)
  obtain ⟨e, ⟨heproj, hfe⟩, hegreat⟩ := ncp_union_3 f hf
  refine ⟨1 - e, ⟨heproj.one_sub, by rwa [sub_sub_cancel],
    fun q hq hq0 => sub_le_comm.mp (hegreat ⟨hq.one_sub, hq0⟩)⟩, ?_⟩
  rintro p ⟨hp, hp0, hpleast⟩
  exact le_antisymm (hpleast _ heproj.one_sub (by rwa [sub_sub_cancel]))
    (sub_le_comm.mp (hegreat ⟨hp.one_sub, hp0⟩))

/-- **63I** (`carrier`, vn.tex:3043, Definition): the **carrier** `⌈f⌉` of
an np-map `f : A → B` between von Neumann algebras: the least projection
`p` with `f(p^⊥) = 0`. -/
noncomputable def carrier (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) : A :=
  (exists_carrier f hf).choose

/-- **63I** (`carrier`, vn.tex:3043, Definition), specialized to
np-functionals: the carrier `⌈ω⌉` of `ω : A → ℂ`. -/
noncomputable def npCarrier (ω : NPFunctional A) : A :=
  carrier ω.toPositiveLinearMap ω.preservesDirSups'

/-- The defining property of `⌈f⌉`: it is the least projection `p` with
`f(p^⊥) = 0`. -/
theorem carrier_spec (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) :
    IsStarProjection (carrier f hf) ∧ f (1 - carrier f hf) = 0 ∧
      ∀ q : A, IsStarProjection q → f (1 - q) = 0 → carrier f hf ≤ q :=
  (exists_carrier f hf).choose_spec.1

theorem carrier_eq (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) {p : A}
    (hp : IsStarProjection p) (h0 : f (1 - p) = 0)
    (hleast : ∀ q : A, IsStarProjection q → f (1 - q) = 0 → p ≤ q) :
    carrier f hf = p :=
  (exists_carrier f hf).unique (carrier_spec f hf) ⟨hp, h0, hleast⟩

/-- Auxiliary: an np-map is positive, so it sends positive elements to
positive elements. -/
private theorem pmap_nonneg (f : A →ₚ[ℂ] B) {a : A} (ha : 0 ≤ a) : (0 : B) ≤ f a := by
  have h : (f (0 : A) : B) ≤ f a := f.monotone ha
  rwa [map_zero f] at h

/-- Auxiliary: `f(q^⊥) = 0` for `⌈f⌉ ≤ q`. -/
private theorem map_ortho_eq_zero_of_carrier_le (f : A →ₚ[ℂ] B)
    (hf : PreservesDirSups ⇑f) {q : A} (hq : 0 ≤ 1 - q)
    (h : (1 : A) - q ≤ 1 - carrier f hf) : f (1 - q) = 0 :=
  le_antisymm (by
    have h2 : (f (1 - q) : B) ≤ f (1 - carrier f hf) := f.monotone h
    rwa [(carrier_spec f hf).2.1] at h2) (pmap_nonneg f hq)

/-- **63II** (`carrier-basic`, vn.tex:3054, Exercise), part 1:
`⌈λf⌉ = ⌈f⌉` for `λ > 0` (the scaled map given pointwise). -/
theorem carrier_basic_1 (f g : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f)
    (hg : PreservesDirSups ⇑g) (l : ℝ) (hl : 0 < l)
    (h : ∀ a, g a = (l : ℂ) • f a) :
    carrier g hg = carrier f hf := by
  have hlne : ((l : ℂ)) ≠ 0 := by
    simpa using hl.ne'
  have hiff : ∀ a : A, g a = 0 ↔ f a = 0 := fun a => by
    rw [h a, smul_eq_zero]
    simp [hlne]
  exact carrier_eq g hg (carrier_spec f hf).1
    ((hiff _).mpr (carrier_spec f hf).2.1)
    fun q hq hq0 => (carrier_spec f hf).2.2 q hq ((hiff _).mp hq0)

/-- **63II** (`carrier-basic`, vn.tex:3054, Exercise), part 2:
`⌈f + g⌉ = ⌈f⌉ ∪ ⌈g⌉` (the sum given pointwise). -/
theorem carrier_basic_2 (f g h : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f)
    (hg : PreservesDirSups ⇑g) (hh : PreservesDirSups ⇑h)
    (hsum : ∀ a, h a = f a + g a) :
    carrier h hh = projSup {carrier f hf, carrier g hg} := by
  have hP : ∀ p ∈ ({carrier f hf, carrier g hg} : Set A), IsStarProjection p := by
    rintro p (rfl | rfl)
    exacts [(carrier_spec f hf).1, (carrier_spec g hg).1]
  obtain ⟨hsproj, hsub, hsleast⟩ := projSup_spec hP
  refine carrier_eq h hh hsproj ?_ ?_
  · have hnn : (0 : A) ≤ 1 - projSup {carrier f hf, carrier g hg} :=
      hsproj.one_sub.nonneg
    rw [hsum]
    rw [map_ortho_eq_zero_of_carrier_le f hf hnn
        (sub_le_sub_left (hsub _ (by left; rfl)) 1),
      map_ortho_eq_zero_of_carrier_le g hg hnn
        (sub_le_sub_left (hsub _ (by right; rfl)) 1), add_zero]
  · intro q hq hq0
    rw [hsum] at hq0
    have hfq : (0 : B) ≤ f (1 - q) := pmap_nonneg f hq.one_sub.nonneg
    have hgq : (0 : B) ≤ g (1 - q) := pmap_nonneg g hq.one_sub.nonneg
    have hf0 : f (1 - q) = 0 := by
      refine le_antisymm ?_ hfq
      have : (f (1 - q) : B) = -g (1 - q) := by
        rw [eq_neg_iff_add_eq_zero]; exact hq0
      rw [this, neg_nonpos]
      exact hgq
    have hg0 : g (1 - q) = 0 := by
      rw [hf0, zero_add] at hq0; exact hq0
    refine hsleast q hq ?_
    rintro p (rfl | rfl)
    exacts [(carrier_spec f hf).2.2 q hq hf0, (carrier_spec g hg).2.2 q hq hg0]

/-- **63II** (`carrier-basic`, vn.tex:3054, Exercise), part 3: `⌈f⌉ = 1` iff
`f` is faithful. -/
theorem carrier_basic_3 (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) :
    carrier f hf = 1 ↔ ∀ a : A, 0 ≤ a → f a = 0 → a = 0 := by
  constructor
  · intro h a ha hfa
    -- `f(⌈a⌉) = 0` by **60V**, so `⌈f⌉ ≤ ⌈a⌉^⊥ = 1 - ⌈a⌉`, i.e. `⌈a⌉ = 0`
    have hc : ceil (f (ceil a)) = 0 := by
      rw [← ncp_ceil f hf a ha, hfa, ceil_zero]
    have hfc : (f (ceil a) : B) = 0 :=
      (ceil_basic_3 _ (pmap_nonneg f (ceil_spec ha).1.nonneg)).mpr hc
    have hle : carrier f hf ≤ 1 - ceil a :=
      (carrier_spec f hf).2.2 _ (ceil_spec ha).1.one_sub (by rwa [sub_sub_cancel])
    rw [h] at hle
    have : ceil a ≤ 0 := by
      have h2 := sub_le_sub_left hle 1
      simpa using h2
    have hz : ceil a = 0 := le_antisymm this (ceil_spec ha).1.nonneg
    exact (ceil_basic_3 a ha).mpr hz
  · intro hfaith
    have h0 : (1 : A) - carrier f hf = 0 :=
      hfaith _ (carrier_spec f hf).1.one_sub.nonneg (carrier_spec f hf).2.1
    exact (sub_eq_zero.mp h0).symm

/-- **63II** (`carrier-basic`, vn.tex:3054, Exercise), part 4: for
multiplicative `f`: `⌈f⌉ = 1` iff `f` is injective. -/
theorem carrier_basic_4 (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f)
    (hmul : ∀ a b : A, f (a * b) = f a * f b) :
    carrier f hf = 1 ↔ Function.Injective ⇑f := by
  rw [carrier_basic_3]
  constructor
  · intro hfaith a b hab
    -- `f(c) = 0` for `c = a - b`, so `f(c*c) = f(c*)f(c) = 0`, so `c*c = 0`
    have hc : (f (a - b) : B) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hab
    have h2 : (f (star (a - b) * (a - b)) : B) = 0 := by
      rw [hmul, hc, mul_zero]
    have := hfaith _ (star_mul_self_nonneg (a - b)) h2
    exact sub_eq_zero.mp (CStarRing.star_mul_self_eq_zero_iff (a - b) |>.mp this)
  · intro hinj a _ hfa
    exact hinj (by rw [hfa, map_zero f])

/-- **63III** (vn.tex:3074, Exercise), part 1: `⌈a*(·)a⌉ = ⌈aa*⌉ = ⌊a⌉` for
the np-map `a*(·)a : A → A`. -/
theorem carrier_ad (a : A) (g : A →ₚ[ℂ] A) (hg : PreservesDirSups ⇑g)
    (h : ∀ b, g b = star a * b * a) :
    carrier g hg = rangeProj a := by
  obtain ⟨hrproj, hra⟩ := (ceill_basic_2 a).1
  have hrrnn : (0 : A) ≤ a * star a := by
    have h' := star_mul_self_nonneg (star a)
    rwa [star_star] at h'
  refine carrier_eq g hg hrproj ?_ ?_
  · rw [h]
    have : ((1 : A) - rangeProj a) * a = 0 := by rw [sub_mul, one_mul, hra, sub_self]
    rw [show star a * (1 - rangeProj a) * a = star a * ((1 - rangeProj a) * a) by
      noncomm_ring, this, mul_zero]
  · intro q hq hq0
    rw [h] at hq0
    -- `a* q^⊥ a = (q^⊥a)*(q^⊥a) = 0`, so `q^⊥a = 0`, i.e. `qa = a`
    have hstar : star ((1 : A) - q) = 1 - q := hq.one_sub.isSelfAdjoint.star_eq
    have hzero : ((1 : A) - q) * a = 0 := by
      refine (CStarRing.star_mul_self_eq_zero_iff (((1 : A) - q) * a)).mp ?_
      rw [star_mul, hstar]
      calc star a * (1 - q) * ((1 - q) * a)
          = star a * ((1 - q) * (1 - q)) * a := by noncomm_ring
        _ = star a * (1 - q) * a := by rw [hq.one_sub.isIdempotentElem.eq]
        _ = 0 := hq0
    have hqa : q * a = a := by
      have := sub_eq_zero.mp (by rw [sub_mul, one_mul] at hzero; exact hzero)
      exact this.symm
    refine (ceil_le_iff hrrnn hq).mpr ?_
    have hsq : star a * q = star a := by
      have h' := congrArg star hqa
      rwa [star_mul, hq.isSelfAdjoint.star_eq] at h'
    calc a * star a * q = a * (star a * q) := by noncomm_ring
      _ = a * star a := by rw [hsq]

/-- **63III** (vn.tex:3074, Exercise), part 2: for a bounded operator
`T : H → K` between Hilbert spaces, the carrier of
`T*(·)T : B(K) → B(H)` is the projection onto the closure of the range of
`T` (identified by its fixed points). -/
theorem carrier_ad_operator {H K : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (T : H →L[ℂ] K)
    (g : (K →L[ℂ] K) →ₚ[ℂ] (H →L[ℂ] H)) (hg : PreservesDirSups ⇑g)
    (h : ∀ S, g S = ContinuousLinearMap.adjoint T ∘L S ∘L T) :
    {y : K | carrier g hg y = y} = closure (Set.range T) :=
  sorry

/-- **63III** (vn.tex:3074, Exercise), part 3: `⌈⟨x,(·)x⟩⌉ = |x⟩⟨x|` for a
unit vector `x` of a Hilbert space, the vector functional taken on all of
`B(H)`. -/
theorem carrier_vector_functional {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (x : H) (hx : ‖x‖ = 1)
    (ω : NPFunctional (H →L[ℂ] H)) (hω : ∀ T : H →L[ℂ] H, ω T = ⟪x, T x⟫) :
    npCarrier ω = ketbra x x := by
  -- `|x⟩⟨x|` kills `ω` on its orthocomplement, and any projection `q` with
  -- `ω(q^⊥) = 0` satisfies `‖q^⊥x‖² = 0`, i.e. `qx = x`, hence
  -- `q|x⟩⟨x| = |x⟩⟨x|`
  have hxx : ⟪x, x⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx]
    norm_num
  have hkb : ∀ z : H, (ketbra x x) z = ⟪x, z⟫ • x := fun _ => rfl
  have hsa : IsSelfAdjoint (ketbra x x) := by
    have h : (ketbra x x) = ContinuousLinearMap.adjoint (ketbra x x) := by
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro u v
      rw [hkb, hkb, inner_smul_left, inner_smul_right, ← inner_conj_symm x u]
      simp [mul_comm]
    exact h.symm
  have hidem : IsIdempotentElem (ketbra x x) := by
    ext z
    simp only [ContinuousLinearMap.mul_apply, hkb, inner_smul_right, hxx, mul_one]
  have hproj : IsStarProjection (ketbra x x) := ⟨hidem, hsa⟩
  refine carrier_eq ω.toPositiveLinearMap ω.preservesDirSups' hproj ?_ ?_
  · have h : (ω (1 - ketbra x x) : ℂ) = 0 := by
      rw [hω]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hkb,
        inner_sub_right, inner_smul_right, hxx, mul_one, sub_self]
    exact h
  · intro q hq hq0
    have h0 : ⟪x, ((1 : H →L[ℂ] H) - q) x⟫ = 0 := by
      rw [← hω]; exact hq0
    have hadj : ContinuousLinearMap.adjoint ((1 : H →L[ℂ] H) - q) = (1 : H →L[ℂ] H) - q :=
      hq.one_sub.isSelfAdjoint
    have h1 : ⟪((1 : H →L[ℂ] H) - q) x, ((1 : H →L[ℂ] H) - q) x⟫ = 0 := by
      have hstep := ContinuousLinearMap.adjoint_inner_right
        ((1 : H →L[ℂ] H) - q) x (((1 : H →L[ℂ] H) - q) x)
      rw [hadj] at hstep
      rw [← hstep, show ((1 : H →L[ℂ] H) - q) (((1 : H →L[ℂ] H) - q) x)
        = (((1 : H →L[ℂ] H) - q) * ((1 : H →L[ℂ] H) - q)) x from rfl,
        hq.one_sub.isIdempotentElem.eq]
      exact h0
    have hzx : ((1 : H →L[ℂ] H) - q) x = 0 := inner_self_eq_zero.mp h1
    have hqx : q x = x := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero] at hzx
      exact hzx.symm
    refine ((projection_below_effect q _ ⟨hq.nonneg, hq.le_one⟩ hproj).out 0 6).mpr ?_
    ext z
    simp only [ContinuousLinearMap.mul_apply, hkb, map_smul, hqx]

end Functionals

/-- **63IV** (`cp-comprehension`, vn.tex:3107, Lemma): for a positive map
`f : A → B` between C*-algebras and an effect `p` with `f(p^⊥) = 0`:
`f(a) = f(pa) = f(ap) = f(pap)` for all `a`. -/
theorem cp_comprehension (f : A →ₚ[ℂ] B) (p : A) (hp : p ∈ effects A)
    (h : f (1 - p) = 0) (a : A) :
    f a = f (p * a) ∧ f a = f (a * p) ∧ f a = f (p * a * p) :=
  sorry

section Commutant

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B]

/-- **63VI** (`carrier-fundamental`, vn.tex:3145, Corollary): an np-map
`f : A → B` satisfies `f(a) = f(⌈f⌉a) = f(a⌈f⌉) = f(⌈f⌉a⌈f⌉)`. -/
theorem carrier_fundamental (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f)
    (a : A) :
    f a = f (carrier f hf * a) ∧ f a = f (a * carrier f hf) ∧
      f a = f (carrier f hf * a * carrier f hf) := by
  -- **63IV**'s argument run through the np-functionals of `B` (which are
  -- separating), rather than through the states of `B`: for an np-functional
  -- `ω` on `B` the composite `g = ω ∘ f` kills `p^⊥ = 1 - ⌈f⌉`, hence
  -- `|g(p^⊥x)|² ≤ g((p^⊥)²)·g(x*x) = 0` by Kadison's inequality.
  set p : A := carrier f hf with hpdef
  have hpproj : IsStarProjection p := (carrier_spec f hf).1
  have hf0 : f (1 - p) = 0 := (carrier_spec f hf).2.1
  have hosa : star ((1 : A) - p) = 1 - p := hpproj.one_sub.isSelfAdjoint.star_eq
  have hoo : ((1 : A) - p) * (1 - p) = 1 - p := hpproj.one_sub.isIdempotentElem.eq
  -- for every np-functional `ω` on `B`, `ω(f(p^⊥ x)) = 0 = ω(f(x p^⊥))`
  have hzero : ∀ (g : NPFunctional A) (y : A),
      ((‖g y‖ : ℂ)) ^ 2 ≤ 0 → g y = 0 := by
    intro g y hcs
    have hle : ((‖g y‖ ^ 2 : ℝ) : ℂ) ≤ 0 := by push_cast; exact hcs
    have h2 : (‖g y‖ : ℝ) ^ 2 ≤ 0 := by
      exact_mod_cast Complex.real_le_real.mp (by simpa using hle)
    have hnn : (0 : ℝ) ≤ ‖g y‖ := norm_nonneg _
    have : ‖g y‖ = 0 := by nlinarith
    exact norm_eq_zero.mp this
  have hgp : ∀ ω : NPFunctional B,
      (compNP f hf ω) (star ((1 : A) - p) * (1 - p)) = 0 := by
    intro ω
    rw [hosa, hoo]
    show ω (f (1 - p)) = 0
    rw [hf0]
    exact map_zero ω.toPositiveLinearMap
  have hleft : ∀ (ω : NPFunctional B) (x : A), ω (f (((1 : A) - p) * x)) = 0 := by
    intro ω x
    have hcs := npFunctional_cauchy_schwarz (compNP f hf ω) ((1 : A) - p) x
    rw [hgp ω, zero_mul, hosa] at hcs
    exact hzero (compNP f hf ω) _ hcs
  have hright : ∀ (ω : NPFunctional B) (x : A), ω (f (x * ((1 : A) - p))) = 0 := by
    intro ω x
    have hcs := npFunctional_cauchy_schwarz (compNP f hf ω) (star x) ((1 : A) - p)
    rw [hgp ω, mul_zero, star_star] at hcs
    exact hzero (compNP f hf ω) _ hcs
  have hL : ∀ x : A, (f x : B) = f (p * x) := by
    intro x
    refine sub_eq_zero.mp (np_separating _ fun ω => ?_)
    have h := hleft ω x
    rw [sub_mul, one_mul, map_sub] at h
    exact h
  have hR : ∀ x : A, (f x : B) = f (x * p) := by
    intro x
    refine sub_eq_zero.mp (np_separating _ fun ω => ?_)
    have h := hright ω x
    rw [mul_sub, mul_one, map_sub] at h
    exact h
  exact ⟨hL a, hR a, by rw [← hR (p * a), ← hL a]⟩

/-! ## Parsec 640 -/

/-- **64II** (`abelian-projections-norm-dense`, vn.tex:3162, Proposition):
every element of a *commutative* von Neumann algebra is the norm limit of
linear combinations of projections. -/
theorem abelian_projections_norm_dense {C : Type*} [CommCStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] [VonNeumannAlgebra C] (a : C) :
    a ∈ closure (Submodule.span ℂ {p : C | IsStarProjection p} : Set C) :=
  sorry

/-! ## Parsec 650: the commutant -/

variable (A) in
/-- **65II** (`commutant`, vn.tex:3208, Definition): the **commutant**
`S^□` of a subset `S` of a von Neumann algebra `A`: all `a ∈ A` commuting
with every member of `S` (Mathlib: `Set.centralizer`).  The commutant
`Z(A) = A^□` of `A` itself is its **centre**. -/
def commutant (S : Set A) : Set A := Set.centralizer S

variable (A) in
/-- **65II** (`commutant`, vn.tex:3208, Definition): the **centre**
`Z(A) = A^□` of a von Neumann algebra. -/
def centre : Set A := commutant A Set.univ

/-- **65III** (`commutant-basic`, vn.tex:3222, Exercise), part 1: the Galois
properties of `(·)^□`: `S ⊆ T^□ ↔ T ⊆ S^□`; antitonicity; `S ⊆ S^□□`; and
`S^□□□ = S^□`. -/
theorem commutant_basic_1 (S T : Set A) :
    (S ⊆ commutant A T ↔ T ⊆ commutant A S) ∧
      (S ⊆ T → commutant A T ⊆ commutant A S) ∧
      S ⊆ commutant A (commutant A S) ∧
      commutant A (commutant A (commutant A S)) = commutant A S :=
  ⟨⟨fun h t ht s hs => (h hs t ht).symm, fun h s hs t ht => (h ht s hs).symm⟩,
    fun h => Set.centralizer_subset h,
    Set.subset_centralizer_centralizer,
    Set.centralizer_centralizer_centralizer S⟩

/-- **65III** (`commutant-basic`, vn.tex:3222, Exercise), part 2: `S^□` is
closed under addition and (scalar) multiplication, contains `1`, and is
ultraweakly closed. -/
theorem commutant_basic_2 (S : Set A) :
    (1 : A) ∈ commutant A S ∧
      (∀ a ∈ commutant A S, ∀ b ∈ commutant A S, a + b ∈ commutant A S) ∧
      (∀ a ∈ commutant A S, ∀ b ∈ commutant A S, a * b ∈ commutant A S) ∧
      (∀ (z : ℂ), ∀ a ∈ commutant A S, z • a ∈ commutant A S) ∧
      @IsClosed A (ultraweak A) (commutant A S) :=
  sorry

/-- **65III** (`commutant-basic`, vn.tex:3222, Exercise), part 3
(counterexample): the commutant need not be closed under the involution
(witness `{[[0,1],[0,0]]}^□` in `M₂`). -/
theorem commutant_basic_3 :
    ∃ S : Set (CStarMatrix (Fin 2) (Fin 2) ℂ),
      ¬∀ a ∈ commutant _ S, star a ∈ commutant _ S :=
  sorry

/-- **65III** (`commutant-basic`, vn.tex:3222, Exercise), part 3 (main): if
`S` is closed under the involution, then `S^□` is a von Neumann subalgebra
of `A`; in particular so are `Z(A)` and `S^□□` (which contains `S`), and
`S^□□` is commutative when `S` is. -/
theorem commutant_basic_3' (S : Set A) (hS : ∀ s ∈ S, star s ∈ S) :
    (∃ T : StarSubalgebra ℂ A, IsVNSubalgebra A T ∧
        (T : Set A) = commutant A S) ∧
      (S ⊆ commutant A S →
        ∀ a ∈ commutant A (commutant A S), ∀ b ∈ commutant A (commutant A S),
          a * b = b * a) :=
  sorry

/-- **65III** (`commutant-basic`, vn.tex:3222, Exercise), part 4: for a von
Neumann subalgebra `S` (star-closed), `S^□□` is a von Neumann subalgebra
containing `S` — but `S^□□ = S` can fail: `(A ∩ ℂ)^□ = A`, so
`(A ∩ ℂ)^□□ = Z(A)` (the scalars' double commutant is the centre). -/
theorem commutant_basic_4 :
    commutant A (Set.range (algebraMap ℂ A)) = Set.univ ∧
      commutant A (commutant A (Set.range (algebraMap ℂ A))) = centre A := by
  have h : commutant A (Set.range (algebraMap ℂ A)) = Set.univ := by
    refine Set.eq_univ_of_forall fun a => ?_
    rintro _ ⟨z, rfl⟩
    exact (Algebra.commutes z a)
  exact ⟨h, by rw [h]; rfl⟩

/-- **65III** (`commutant-basic`, vn.tex:3222, Exercise), part 5: for (the
carrier `R` of) a von Neumann subalgebra of `A`: `Z(R) = R ∩ R^□`. -/
theorem commutant_basic_5 (R : Set A) :
    R ∩ commutant A R = {a ∈ R | ∀ b ∈ R, a * b = b * a} :=
  Set.ext fun a =>
    ⟨fun h => ⟨h.1, fun b hb => (h.2 b hb).symm⟩,
      fun h => ⟨h.1, fun b hb => (h.2 b hb).symm⟩⟩

/-- **65IV** (`projections-norm-dense`, vn.tex:3279, Proposition): every
self-adjoint element `a` of a von Neumann algebra is the norm limit of
linear combinations of projections from `{a}^□□`. -/
theorem projections_norm_dense (a : A) (ha : IsSelfAdjoint a) :
    a ∈ closure (Submodule.span ℂ
      {p : A | IsStarProjection p ∧ p ∈ commutant A (commutant A {a})} :
        Set A) :=
  sorry

/-! ## Parsec 660: ultracyclic projections -/

variable (A) in
/-- **66II** (vn.tex:3301, Definition): a projection `p` of a von Neumann
algebra is **ultracyclic** if `p = ⌈ω⌉` for some np-functional `ω`.
(**66III**, Remark: relation to cyclic projections — nothing to
formalize.) -/
def Ultracyclic (p : A) : Prop :=
  ∃ ω : NPFunctional A, p = npCarrier ω

/-- **66IV** (`ultracyclic-basic`, vn.tex:3334, Exercise), part 1: the
supremum of two ultracyclic projections is ultracyclic. -/
theorem ultracyclic_basic_1 (p q : A) (hp : Ultracyclic A p)
    (hq : Ultracyclic A q) : Ultracyclic A (projSup {p, q}) :=
  sorry

/-- **66IV** (`ultracyclic-basic`, vn.tex:3334, Exercise), part 2: a
projection below an ultracyclic projection is ultracyclic. -/
theorem ultracyclic_basic_2 (p q : A) (hp : IsStarProjection p)
    (hq : Ultracyclic A q) (hpq : p ≤ q) : Ultracyclic A p :=
  sorry

/-- **66IV** (`ultracyclic-basic`, vn.tex:3334, Exercise), part 3: every
projection `p` is the directed supremum of ultracyclic projections:
`p = ⋁_ω ⌈ω⌉` over the np-functionals `ω` with `ω(p^⊥) = 0`. -/
theorem ultracyclic_basic_3 (p : A) (hp : IsStarProjection p) :
    p = projSup {q : A | ∃ ω : NPFunctional A, ω (1 - p) = 0 ∧
      q = npCarrier ω} :=
  sorry

/-- **66IV** (`ultracyclic-basic`, vn.tex:3334, Exercise), part 4: every
projection is the sum of a family of pairwise orthogonal ultracyclic
projections. -/
theorem ultracyclic_basic_4 (p : A) (hp : IsStarProjection p) :
    ∃ (ι : Type _) (ω : ι → NPFunctional A),
      (Pairwise fun i j => npCarrier (ω i) * npCarrier (ω j) = 0) ∧
        p = projSup (Set.range fun i => npCarrier (ω i)) :=
  sorry

/-! ## Parsec 670: central elements -/

variable (A) in
/-- **67I** (vn.tex:3363, Definition): an element `a` of a von Neumann
algebra is **central** when it commutes with every element (i.e.
`a ∈ Z(A)`). -/
def IsCentral (a : A) : Prop := ∀ b : A, a * b = b * a

/-- **67II** (`central-examples`, vn.tex:3370, Examples), part 3: in `B(H)`
only the scalars are central.  (Parts 1–2 — commutative algebras and direct
sums — are immediate from the definitions and not converted.  **67III**,
Remark: such von Neumann algebras are called *factors*.) -/
theorem central_examples_3 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    IsCentral (H →L[ℂ] H) T ↔ ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) :=
  sorry

/-- **67IV** (`central-projections-sums`, vn.tex:3408, Exercise), part 1:
for a central projection `c` of a von Neumann algebra `A`, the corner
`cA = {ca : a ∈ A}` is closed under the algebra operations and under
bounded directed suprema of self-adjoint elements, and is a von Neumann
algebra with unit `c` (all but the unit being that of `A`). -/
theorem central_projections_sums_1 (c : A) (hc : IsStarProjection c)
    (hcentral : IsCentral A c) :
    (∀ x ∈ {b : A | c * b = b}, ∀ y ∈ {b : A | c * b = b},
        x + y ∈ {b : A | c * b = b} ∧ x * y ∈ {b : A | c * b = b} ∧
          star x ∈ {b : A | c * b = b}) ∧
      c * c = c ∧  -- `c` is the unit of the corner `cA`
      (∀ (D : Set (selfAdjoint A)) (s : selfAdjoint A),
        (∀ d ∈ D, c * (d : A) = (d : A)) → D.Nonempty →
          DirectedOn (· ≤ ·) D → IsLUB D s → c * (s : A) = (s : A)) :=
  sorry

/-- **67IV** (`central-projections-sums`, vn.tex:3408, Exercise), part 2:
given a family of central projections `(cᵢ)` with `∑ᵢ cᵢ = 1` (pairwise
orthogonal, supremum `1`), `a ↦ (cᵢa)ᵢ` is an nmiu-isomorphism
`A ≅ ⊕ᵢ cᵢA` — rendered concretely: every norm-bounded choice of elements
of the corners is uniquely of the form `(cᵢa)ᵢ`. -/
theorem central_projections_sums_2 {ι : Type*} (c : ι → A)
    (hc : ∀ i, IsStarProjection (c i) ∧ IsCentral A (c i))
    (horth : Pairwise fun i j => c i * c j = 0)
    (hsum : projSup (Set.range c) = 1)
    (b : ι → A) (hb : ∀ i, c i * b i = b i)
    (hbdd : BddAbove (Set.range fun i => ‖b i‖)) :
    ∃! a : A, ∀ i, c i * a = b i :=
  sorry

/-! ## Parsec 680: central support -/

/-- **68I** (`cceil-fundamental`, vn.tex:3437, Proposition), the content: for
a projection `e` of a von Neumann algebra, `⋃_{a∈A} ⌈a* e a⌉` is the least
central projection above `e`.  This is the author's proof: centrality comes
from `⌈ce b⌋ = ⌈b* c b⌉ = ⋃_a ⌈b* ⌈a* e a⌉ b⌉ = ⋃_a ⌈(ab)* e (ab)⌉ ≤ c`
(**60IX**.2 and **60VII**.1), and minimality from `e ≤ q ⟹ eaq = eqa = ea`. -/
private theorem isLeast_centralAbove {e : A} (he : IsStarProjection e) :
    IsLeast {p : A | IsStarProjection p ∧ IsCentral A p ∧ e ≤ p}
      (projSup {x : A | ∃ a : A, x = ceil (star a * e * a)}) := by
  classical
  set S : Set A := {x : A | ∃ a : A, x = ceil (star a * e * a)} with hSdef
  have hSnn : ∀ a : A, (0 : A) ≤ star a * e * a := fun a =>
    star_left_conjugate_nonneg he.nonneg a
  have hSproj : ∀ x ∈ S, IsStarProjection x := by
    rintro _ ⟨a, rfl⟩
    exact (ceil_spec (hSnn a)).1
  obtain ⟨hcproj, hcub, hcleast⟩ := projSup_spec hSproj
  set c : A := projSup S with hcdef
  have hec : e ≤ c :=
    hcub e ⟨1, by rw [star_one, one_mul, mul_one, ceil_of_isStarProjection he]⟩
  -- the key step: `⌈cb⌋ ≤ c`, i.e. `cbc = cb`
  have hkey : ∀ b : A, c * b * c = c * b := by
    intro b
    have e1 : star (c * b) * (c * b) = star b * c * b := by
      rw [star_mul, hcproj.isSelfAdjoint.star_eq]
      calc star b * c * (c * b) = star b * (c * c) * b := by noncomm_ring
        _ = star b * c * b := by rw [hcproj.isIdempotentElem.eq]
    have h2 := ncp_union_2 (conjPMap b) (conjPMap_preservesDirSups b) S hSproj
    have himgproj : ∀ x ∈ ((fun p => ceil ((conjPMap b) p)) '' S),
        IsStarProjection x := by
      rintro _ ⟨p, hp, rfl⟩
      exact (ceil_spec (star_left_conjugate_nonneg (hSproj p hp).nonneg b)).1
    have himgS : ∀ x ∈ ((fun p => ceil ((conjPMap b) p)) '' S), x ∈ S := by
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      refine ⟨a * b, ?_⟩
      show ceil (star b * ceil (star a * e * a) * b) = ceil (star (a * b) * e * (a * b))
      rw [← ceil_fundamental_1 b (star a * e * a) (hSnn a), star_mul]
      congr 1
      noncomm_ring
    have h3 : suppProj (c * b) ≤ c := by
      rw [suppProj, e1]
      refine le_of_eq_of_le (?_ : ceil (star b * c * b) = _)
        ((projSup_spec himgproj).2.2 c hcproj fun x hx => hcub x (himgS x hx))
      exact h2
    exact mul_eq_of_suppProj_le hcproj h3
  refine ⟨⟨hcproj, fun b => ?_, hec⟩, ?_⟩
  · -- `bc = cbc = cb`
    have h4 : c * b * c = b * c := by
      have h := congrArg star (hkey (star b))
      simp only [star_mul, star_star, hcproj.isSelfAdjoint.star_eq] at h
      rw [← mul_assoc] at h
      exact h
    rw [← hkey b, h4]
  · rintro q ⟨hq, hqc, heq⟩
    refine hcleast q hq ?_
    rintro _ ⟨a, rfl⟩
    refine (ceil_le_iff (hSnn a) hq).mpr ?_
    have heq' : e * q = e := proj_mul_of_le he hq heq
    calc star a * e * a * q = star a * e * (a * q) := by noncomm_ring
      _ = star a * e * (q * a) := by rw [hqc a]
      _ = star a * (e * q) * a := by noncomm_ring
      _ = star a * e * a := by rw [heq']

/-- **68III** (`central support`, vn.tex:3472, Definition),
well-definedness: every element `a` of a von Neumann algebra has a least
central projection `p` with `pa = a`. -/
theorem exists_cceil (a : A) :
    ∃! p : A, IsStarProjection p ∧ IsCentral A p ∧ p * a = a ∧
      ∀ q : A, IsStarProjection q → IsCentral A q → q * a = a → p ≤ q := by
  -- take the least central projection above `⌊a⌉` (**68I**); it absorbs `a`
  -- because `⌊a⌉a = a`, and a central projection `q` with `qa = a` dominates
  -- `⌊a⌉ = ⌈aa*⌉` because `q(aa*) = aa*`
  obtain ⟨hrproj, hra⟩ := (ceill_basic_2 a).1
  obtain ⟨⟨hcproj, hccentral, hrc⟩, hcleast⟩ := isLeast_centralAbove hrproj
  set c : A := projSup {x : A | ∃ b : A, x = ceil (star b * rangeProj a * b)} with hcdef
  have hcr : c * rangeProj a = rangeProj a := by
    have h := congrArg star (proj_mul_of_le hrproj hcproj hrc)
    rwa [star_mul, hrproj.isSelfAdjoint.star_eq, hcproj.isSelfAdjoint.star_eq] at h
  have hca : c * a = a := by
    calc c * a = c * (rangeProj a * a) := by rw [hra]
      _ = c * rangeProj a * a := by noncomm_ring
      _ = rangeProj a * a := by rw [hcr]
      _ = a := hra
  have hleast : ∀ q : A, IsStarProjection q → IsCentral A q → q * a = a → c ≤ q := by
    intro q hq hqc hqa
    refine hcleast ⟨hq, hqc, ?_⟩
    have hnn : (0 : A) ≤ a * star a := by
      have h := star_mul_self_nonneg (star a)
      rwa [star_star] at h
    refine (ceil_le_iff hnn hq).mpr ?_
    calc a * star a * q = q * (a * star a) := (hqc _).symm
      _ = q * a * star a := by noncomm_ring
      _ = a * star a := by rw [hqa]
  refine ⟨c, ⟨hcproj, hccentral, hca, hleast⟩, ?_⟩
  rintro p ⟨hp, hpc, hpa, hpleast⟩
  exact le_antisymm (hpleast c hcproj hccentral hca) (hleast p hp hpc hpa)

/-- **68III** (`central support`, vn.tex:3472, Definition): the **central
support** `⌈⌈a⌉⌉` of `a`: the least central projection `p` with
`pa = a`. -/
noncomputable def cceil (a : A) : A := (exists_cceil a).choose

/-- The defining property of `⌈⌈a⌉⌉`: it is the least central projection `p`
with `pa = a`. -/
theorem cceil_isLeast (a : A) :
    IsLeast {p : A | IsStarProjection p ∧ IsCentral A p ∧ p * a = a} (cceil a) := by
  obtain ⟨h1, h2, h3, h4⟩ := (exists_cceil a).choose_spec.1
  exact ⟨⟨h1, h2, h3⟩, fun q hq => h4 q hq.1 hq.2.1 hq.2.2⟩

/-- Auxiliary: for projections, `e ≤ p` iff `pe = e`. -/
private theorem proj_le_iff_mul_left {e p : A} (he : IsStarProjection e)
    (hp : IsStarProjection p) : e ≤ p ↔ p * e = e :=
  (projection_below_effect p e ⟨hp.nonneg, hp.le_one⟩ he).out 0 6

/-- Auxiliary: for projections, `e ≤ p` iff `ep = e`. -/
private theorem proj_le_iff_mul_right {e p : A} (he : IsStarProjection e)
    (hp : IsStarProjection p) : e ≤ p ↔ e * p = e :=
  (projection_below_effect p e ⟨hp.nonneg, hp.le_one⟩ he).out 0 7

/-- Auxiliary: two elements absorbed by the same central projections have the
same central support. -/
private theorem cceil_congr {x y : A}
    (h : ∀ p : A, IsStarProjection p → IsCentral A p → (p * x = x ↔ p * y = y)) :
    cceil x = cceil y := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := cceil_isLeast y
  exact (cceil_isLeast x).unique
    ⟨⟨h1, h2, (h _ h1 h2).mpr h3⟩,
      fun q hq => h4 ⟨hq.1, hq.2.1, (h _ hq.1 hq.2.1).mp hq.2.2⟩⟩

/-- **68I** (`cceil-fundamental`, vn.tex:3437, Proposition): for a
projection `e`, `⌈⌈e⌉⌉ = ⋃_{a∈A} ⌈a* e a⌉` is the least central projection
above `e`. -/
theorem cceil_fundamental (e : A) (he : IsStarProjection e) :
    IsLeast {p : A | IsStarProjection p ∧ IsCentral A p ∧ e ≤ p} (cceil e) ∧
      cceil e = projSup {x : A | ∃ a : A, x = ceil (star a * e * a)} := by
  have hset : {p : A | IsStarProjection p ∧ IsCentral A p ∧ e ≤ p}
      = {p : A | IsStarProjection p ∧ IsCentral A p ∧ p * e = e} := by
    ext p
    exact ⟨fun h => ⟨h.1, h.2.1, (proj_le_iff_mul_left he h.1).mp h.2.2⟩,
      fun h => ⟨h.1, h.2.1, (proj_le_iff_mul_left he h.1).mpr h.2.2⟩⟩
  have h1 : IsLeast {p : A | IsStarProjection p ∧ IsCentral A p ∧ e ≤ p} (cceil e) := by
    rw [hset]; exact cceil_isLeast e
  exact ⟨h1, h1.unique (isLeast_centralAbove he)⟩

/-- **68III** (`central support`, vn.tex:3472, Definition), embedded claims:
`⌈⌈a⌉⌉ = ⌈⌈⌈a⌋⌉⌉ = ⌈⌈⌊a⌉⌉⌉`, and for a central projection `c`:
`⌈⌈a⌉⌉ ≤ c` iff `ac = a` iff `ca = a`. -/
theorem cceil_eq_cceil_supp (a : A) :
    cceil a = cceil (suppProj a) ∧ cceil a = cceil (rangeProj a) ∧
      ∀ c : A, IsStarProjection c → IsCentral A c →
        ((cceil a ≤ c ↔ a * c = a) ∧ (cceil a ≤ c ↔ c * a = a)) := by
  -- For a central projection `p`, `pa = a` iff `⌈a⌋ ≤ p` iff `⌊a⌉ ≤ p`; the
  -- three claims all follow from this one equivalence.
  have hssnn : (0 : A) ≤ star a * a := star_mul_self_nonneg a
  have hrrnn : (0 : A) ≤ a * star a := by
    have h := star_mul_self_nonneg (star a)
    rwa [star_star] at h
  obtain ⟨hsproj, hsa⟩ := (ceill_basic_1 a).1
  obtain ⟨hrproj, hra⟩ := (ceill_basic_2 a).1
  have hsupp : ∀ p : A, IsStarProjection p → IsCentral A p →
      (p * a = a ↔ p * suppProj a = suppProj a) := by
    intro p hp hpc
    constructor
    · intro h
      refine (proj_le_iff_mul_left hsproj hp).mp ((ceil_le_iff hssnn hp).mpr ?_)
      calc star a * a * p = star a * (a * p) := by noncomm_ring
        _ = star a * (p * a) := by rw [hpc a]
        _ = star a * a := by rw [h]
    · intro h
      have hle : suppProj a ≤ p := (proj_le_iff_mul_left hsproj hp).mpr h
      rw [hpc a]
      exact mul_eq_of_suppProj_le hp hle
  have hrange : ∀ p : A, IsStarProjection p → IsCentral A p →
      (p * a = a ↔ p * rangeProj a = rangeProj a) := by
    intro p hp hpc
    constructor
    · intro h
      refine (proj_le_iff_mul_left hrproj hp).mp
        ((ceil_le_iff hrrnn hp).mpr ?_)
      calc a * star a * p = p * (a * star a) := (hpc _).symm
        _ = p * a * star a := by noncomm_ring
        _ = a * star a := by rw [h]
    · intro h
      calc p * a = p * (rangeProj a * a) := by rw [hra]
        _ = p * rangeProj a * a := by noncomm_ring
        _ = rangeProj a * a := by rw [h]
        _ = a := hra
  refine ⟨cceil_congr hsupp, cceil_congr hrange, fun c hc hcentral => ?_⟩
  have hkey : cceil a ≤ c ↔ c * a = a := by
    constructor
    · intro h
      calc c * a = c * (cceil a * a) := by rw [(cceil_isLeast a).1.2.2]
        _ = c * cceil a * a := by noncomm_ring
        _ = cceil a * a := by rw [(proj_le_iff_mul_left (cceil_isLeast a).1.1 hc).mp h]
        _ = a := (cceil_isLeast a).1.2.2
    · exact fun h => (cceil_isLeast a).2 ⟨hc, hcentral, h⟩
  exact ⟨by rw [hkey, hcentral a], hkey⟩

/-- **68IV** (`cceil-basic`, vn.tex:3490, Exercise), part 1:
`⌈⌈a⌉⌉ = ⌈⌈a*⌉⌉ = ⌈⌈a*a⌉⌉ = ⌈⌈aa*⌉⌉`. -/
theorem cceil_basic_1 (a : A) :
    cceil a = cceil (star a) ∧ cceil a = cceil (star a * a) ∧
      cceil a = cceil (a * star a) := by
  have hssnn : (0 : A) ≤ star a * a := star_mul_self_nonneg a
  have hrrnn : (0 : A) ≤ a * star a := by
    have h := star_mul_self_nonneg (star a)
    rwa [star_star] at h
  obtain ⟨hsproj, hsa⟩ := (ceill_basic_1 a).1
  obtain ⟨hrproj, hra⟩ := (ceill_basic_2 a).1
  refine ⟨cceil_congr ?_, cceil_congr ?_, cceil_congr ?_⟩
  · intro p hp hpc
    constructor <;> intro h
    · have h' := congrArg star h
      rwa [star_mul, hp.isSelfAdjoint.star_eq, ← hpc (star a)] at h'
    · have h' := congrArg star h
      rw [star_mul, star_star, hp.isSelfAdjoint.star_eq] at h'
      rw [hpc a]
      exact h'
  · intro p hp hpc
    constructor <;> intro h
    · calc p * (star a * a) = p * star a * a := by noncomm_ring
        _ = star a * p * a := by rw [hpc (star a)]
        _ = star a * (p * a) := by noncomm_ring
        _ = star a * a := by rw [h]
    · have hle : suppProj a ≤ p :=
        (ceil_le_iff hssnn hp).mpr (by rw [← hpc (star a * a)]; exact h)
      rw [hpc a]
      exact mul_eq_of_suppProj_le hp hle
  · intro p hp hpc
    constructor <;> intro h
    · calc p * (a * star a) = p * a * star a := by noncomm_ring
        _ = a * star a := by rw [h]
    · have hle : rangeProj a ≤ p :=
        (ceil_le_iff hrrnn hp).mpr (by rw [← hpc (a * star a)]; exact h)
      calc p * a = p * (rangeProj a * a) := by rw [hra]
        _ = p * rangeProj a * a := by noncomm_ring
        _ = rangeProj a * a := by rw [(proj_le_iff_mul_left hrproj hp).mp hle]
        _ = a := hra

/-- **68IV** (`cceil-basic`, vn.tex:3490, Exercise), part 2:
`⌈⌈⋁D⌉⌉ = ⋃_{d∈D} ⌈⌈d⌉⌉` for bounded directed `D` of *positive* elements;
`⌈⌈⋃E⌉⌉ = ⋃_{e∈E} ⌈⌈e⌉⌉` for sets of projections `E`; and
`⌈⌈a+b⌉⌉ = ⌈⌈⌈a⌉ ∪ ⌈b⌉⌉⌉ = ⌈⌈a⌉⌉ ∪ ⌈⌈b⌉⌉` for positive `a`, `b`.

**Erratum (author).**  vn.tex:3497 states the first clause "for any bounded
directed subset of `𝒜`" and the third "for all `a,b ∈ 𝒜`", both without
positivity, and both are then **false**: central support is monotone on
*positive* elements only.  For the first take `D = {−1, 0}`, which is directed
and bounded with `⋁D = 0`, so `⌈⌈⋁D⌉⌉ = 0` while `⌈⌈−1⌉⌉ ∪ ⌈⌈0⌉⌉ = 1`; for the
third take `a = 1`, `b = −1`, giving `⌈⌈0⌉⌉ = 0` against `1`.  Both clauses need
positivity, which is what is assumed here. -/
theorem cceil_basic_2 (D : Set (selfAdjoint A)) (s : selfAdjoint A)
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hs : IsLUB D s)
    (hDpos : ∀ d ∈ D, 0 ≤ (d : A))
    (E : Set A) (hE : ∀ e ∈ E, IsStarProjection e) (a b : A) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    cceil (s : A) = projSup ((fun d : selfAdjoint A => cceil (d : A)) '' D) ∧
      cceil (projSup E) = projSup (cceil '' E) ∧
      cceil (a + b) = cceil (projSup {ceil a, ceil b}) ∧
      cceil (projSup {ceil a, ceil b}) = projSup {cceil a, cceil b} :=
  sorry

/-- **68IV** (`cceil-basic`, vn.tex:3490, Exercise), part 3:
`⌈⌈a⌉⌉c = ⌈⌈ac⌉⌉` for central projections `c`; consequently
`⌈⌈a⌉⌉⌈⌈b⌉⌉ = ⌈⌈a⌈⌈b⌉⌉⌉⌉ = ⌈⌈⌈⌈a⌉⌉b⌉⌉ = ⌈⌈a⌉⌉ ∩ ⌈⌈b⌉⌉`. -/
theorem cceil_basic_3 (a b c : A) (hc : IsStarProjection c)
    (hcentral : IsCentral A c) :
    cceil a * c = cceil (a * c) ∧
      cceil a * cceil b = cceil (a * cceil b) ∧
      cceil a * cceil b = projInf {cceil a, cceil b} := by
  -- `⌈⌈x⌉⌉y` is the least central projection absorbing `xy`: for a central
  -- projection `q` with `q(xy) = xy`, the central projection `1 - y(1-q)`
  -- absorbs `x`, hence dominates `⌈⌈x⌉⌉`, which gives `⌈⌈x⌉⌉y(1-q) = 0`.
  have key : ∀ x y : A, IsStarProjection y → IsCentral A y →
      cceil x * y = cceil (x * y) := by
    intro x y hy hyc
    obtain ⟨⟨hpproj, hpc, hpx⟩, hpleast⟩ := cceil_isLeast x
    have hprod : IsStarProjection (cceil x * y) := hpproj.mul hy (hyc (cceil x)).symm
    have hprodc : IsCentral A (cceil x * y) := by
      intro z
      calc cceil x * y * z = cceil x * (y * z) := by noncomm_ring
        _ = cceil x * (z * y) := by rw [hyc z]
        _ = cceil x * z * y := by noncomm_ring
        _ = z * cceil x * y := by rw [hpc z]
        _ = z * (cceil x * y) := by noncomm_ring
    have hIL : IsLeast {p : A | IsStarProjection p ∧ IsCentral A p ∧ p * (x * y) = x * y}
        (cceil x * y) := by
      refine ⟨⟨hprod, hprodc, ?_⟩, ?_⟩
      · calc cceil x * y * (x * y) = cceil x * (y * x) * y := by noncomm_ring
          _ = cceil x * (x * y) * y := by rw [hyc x]
          _ = cceil x * x * (y * y) := by noncomm_ring
          _ = x * y := by rw [hpx, hy.isIdempotentElem.eq]
      · rintro q ⟨hq, hqc, hqxy⟩
        set t : A := y * (1 - q) with htdef
        have hcomm : Commute y ((1 : A) - q) :=
          show y * (1 - q) = (1 - q) * y by
            rw [mul_sub, sub_mul, mul_one, one_mul, hqc y]
        have htproj : IsStarProjection t := hy.mul hq.one_sub hcomm
        have htc : IsCentral A t := by
          intro z
          calc y * (1 - q) * z = y * ((1 - q) * z) := by noncomm_ring
            _ = y * (z * (1 - q)) := by
                rw [show ((1 : A) - q) * z = z * (1 - q) by
                  rw [sub_mul, mul_sub, one_mul, mul_one, hqc z]]
            _ = y * z * (1 - q) := by noncomm_ring
            _ = z * y * (1 - q) := by rw [hyc z]
            _ = z * (y * (1 - q)) := by noncomm_ring
        have htx : t * x = 0 := by
          have h1 : y * q * x = x * y := by
            rw [hyc q, mul_assoc, hyc x, hqxy]
          calc y * (1 - q) * x = y * x - y * q * x := by noncomm_ring
            _ = x * y - x * y := by rw [hyc x, h1]
            _ = 0 := sub_self _
        have hrx : ((1 : A) - t) * x = x := by rw [sub_mul, one_mul, htx, sub_zero]
        have hle : cceil x ≤ 1 - t := hpleast ⟨htproj.one_sub, by
          intro z
          have h := htc z
          rw [sub_mul, mul_sub, one_mul, mul_one, h], hrx⟩
        have hzero : cceil x * t = 0 := by
          have h := (proj_le_iff_mul_right hpproj htproj.one_sub).mp hle
          rw [mul_sub, mul_one] at h
          exact sub_eq_self.mp h
        refine (proj_le_iff_mul_right hprod hq).mpr ?_
        have h2 : cceil x * y * (1 - q) = 0 := by
          rw [mul_assoc]; exact hzero
        rw [mul_sub, mul_one, sub_eq_zero] at h2
        exact h2.symm
    exact hIL.unique (cceil_isLeast (x * y))
  refine ⟨key a c hc hcentral,
    key a (cceil b) (cceil_isLeast b).1.1 (cceil_isLeast b).1.2.1, ?_⟩
  have hpa := (cceil_isLeast a).1
  have hpb := (cceil_isLeast b).1
  have hprod : IsStarProjection (cceil a * cceil b) :=
    hpa.1.mul hpb.1 (hpb.2.1 (cceil a)).symm
  refine (projInf_eq ?_ hprod ?_ ?_).symm
  · rintro p (rfl | rfl)
    exacts [hpa.1, hpb.1]
  · rintro p (rfl | rfl)
    · refine (proj_le_iff_mul_right hprod hpa.1).mpr ?_
      calc cceil a * cceil b * cceil a = cceil a * (cceil b * cceil a) := by noncomm_ring
        _ = cceil a * (cceil a * cceil b) := by rw [hpb.2.1 (cceil a)]
        _ = cceil a * cceil a * cceil b := by noncomm_ring
        _ = cceil a * cceil b := by rw [hpa.1.isIdempotentElem.eq]
    · refine (proj_le_iff_mul_right hprod hpb.1).mpr ?_
      calc cceil a * cceil b * cceil b = cceil a * (cceil b * cceil b) := by noncomm_ring
        _ = cceil a * cceil b := by rw [hpb.1.isIdempotentElem.eq]
  · intro q hq hle
    refine (proj_le_iff_mul_left hq hprod).mpr ?_
    calc cceil a * cceil b * q = cceil a * (cceil b * q) := by noncomm_ring
      _ = cceil a * q := by rw [(proj_le_iff_mul_left hq hpb.1).mp (hle _ (by right; rfl))]
      _ = q := (proj_le_iff_mul_left hq hpa.1).mp (hle _ (by left; rfl))

/-! ## Parsec 690: central carrier -/

/-- **69I** (`cceil-map-def`, vn.tex:3521, Definition): the **central
carrier** `⌈⌈f⌉⌉ = ⌈⌈⌈f⌉⌉⌉` of an np-map `f : A → B`. -/
noncomputable def cceilMap (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) : A :=
  cceil (carrier f hf)

/-- **69I** (`cceil-map-def`, vn.tex:3521, Definition), embedded claim: for
a central *effect* `c`: `f(c^⊥) = 0` iff `⌈f⌉ ≤ c` iff `⌈⌈f⌉⌉ ≤ c`; so
`⌈⌈f⌉⌉` is the least central effect (and projection) `p` with
`f(p^⊥) = 0`. -/
theorem cceilMap_least (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f) (c : A)
    (hc : c ∈ effects A) (hcentral : IsCentral A c) :
    (f (1 - c) = 0 ↔ carrier f hf ≤ c) ∧
      (carrier f hf ≤ c ↔ cceilMap f hf ≤ c) := by
  -- everything goes through `⌊c⌋ = ⌈c^⊥⌉^⊥`, the greatest projection below
  -- `c`, which is central because `c` is
  have hcompl : (1 : A) - c ∈ effects A := effect_orthosupplement c hc
  have hceilproj : IsStarProjection (ceil (1 - c)) := (ceil_spec hcompl.1).1
  have hfloor : floor c = 1 - ceil (1 - c) := floor_eq_one_sub_ceil hc
  have hfloorproj : IsStarProjection (floor c) := (floor_spec hc).1
  have hcarrier := carrier_spec f hf
  have hfc : IsCentral A (floor c) := by
    intro b
    have hb : b * ((1 : A) - c) = (1 - c) * b := by
      rw [mul_sub, sub_mul, mul_one, one_mul, hcentral b]
    have hcomm := ceil_basic_2 (1 - c) b hcompl.1 hb
    rw [hfloor, sub_mul, mul_sub, one_mul, mul_one, hcomm]
  refine ⟨⟨fun h => ?_, fun h =>
    map_ortho_eq_zero_of_carrier_le f hf hcompl.1 (sub_le_sub_left h 1)⟩,
    ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h1 : ceil (f (ceil (1 - c))) = 0 := by
      rw [← ncp_ceil f hf _ hcompl.1, h, ceil_zero]
    have h2 : (f (ceil (1 - c)) : B) = 0 :=
      (ceil_basic_3 _ (pmap_nonneg f hceilproj.nonneg)).mpr h1
    refine le_trans ?_ (floor_le hc)
    rw [hfloor]
    exact hcarrier.2.2 _ hceilproj.one_sub (by rwa [sub_sub_cancel])
  · have hle : carrier f hf ≤ floor c := (floor_isGreatest hc).2 ⟨hcarrier.1, h⟩
    refine le_trans ?_ (floor_le hc)
    exact (cceil_isLeast (carrier f hf)).2
      ⟨hfloorproj, hfc, (proj_le_iff_mul_left hcarrier.1 hfloorproj).mp hle⟩
  · exact le_trans ((proj_le_iff_mul_left hcarrier.1
      (cceil_isLeast (carrier f hf)).1.1).mpr
      (cceil_isLeast (carrier f hf)).1.2.2) h

/-- **69II** (`prop:weakly-closed-ideal`, vn.tex:3539, Proposition): every
two-sided ideal `D` of a von Neumann algebra that is closed under bounded
directed suprema of self-adjoint elements is `cA` for a unique central
projection `c`; moreover `c` is the greatest projection in `D`. -/
theorem weakly_closed_ideal (D : TwoSidedIdeal A)
    (hD : ∀ (S : Set (selfAdjoint A)) (s : selfAdjoint A),
      (∀ x ∈ S, (x : A) ∈ D) → S.Nonempty → DirectedOn (· ≤ ·) S →
        IsLUB S s → (s : A) ∈ D) :
    (∃! c : A, IsStarProjection c ∧ IsCentral A c ∧
        ∀ a : A, a ∈ D ↔ c * a = a) ∧
      ∀ c : A, IsStarProjection c → IsCentral A c →
        (∀ a : A, a ∈ D ↔ c * a = a) →
        IsGreatest {p : A | IsStarProjection p ∧ p ∈ D} c :=
  sorry

/-- **69IV** (`carrier-miu`, vn.tex:3611, Corollary): the carrier of an
nmiu-map `f : A → B` is central (`⌈f⌉ = ⌈⌈f⌉⌉`), and
`ker f = ⌈⌈f⌉⌉^⊥ A` (i.e. `f(a) = 0` iff `⌈f⌉·a = 0`).  (The carrier is
taken through any positive-map avatar `g` of `f`.) -/
theorem carrier_miu (f : NMIUMap A B) (g : A →ₚ[ℂ] B)
    (hg : PreservesDirSups ⇑g) (heq : ∀ a, g a = f a) :
    IsCentral A (carrier g hg) ∧
      ∀ a : A, f a = 0 ↔ carrier g hg * a = 0 := by
  -- `e = ⌈f⌉^⊥` absorbs the kernel of `f` on the right (`f(x) = 0` forces
  -- `g(⌈x⌋) = 0` by **60V**, so `⌈x⌋ ≤ e`); applied to `x = eb` this gives
  -- `ebe = eb`, and applied to `x = eb*` (after taking adjoints) `ebe = be`
  have hmul : ∀ x y : A, (f (x * y) : B) = f x * f y := fun x y => map_mul f.toStarAlgHom x y
  have hstar : ∀ x : A, (f (star x) : B) = star (f x) := fun x => map_star f.toStarAlgHom x
  set p : A := carrier g hg with hpdef
  have hpproj : IsStarProjection p := (carrier_spec g hg).1
  have heproj : IsStarProjection ((1 : A) - p) := hpproj.one_sub
  have hkey : ∀ x : A, (f x : B) = 0 → x * ((1 : A) - p) = x := by
    intro x hx
    have h1 : (g (star x * x) : B) = 0 := by
      rw [heq, hmul, hx, mul_zero]
    have h2 : ceil (g (suppProj x)) = 0 := by
      rw [suppProj, ← ncp_ceil g hg _ (star_mul_self_nonneg x), h1, ceil_zero]
    have h3 : (g (suppProj x) : B) = 0 :=
      (ceil_basic_3 _ (pmap_nonneg g (ceill_basic_1 x).1.1.nonneg)).mpr h2
    have h4 : p ≤ 1 - suppProj x :=
      (carrier_spec g hg).2.2 _ (ceill_basic_1 x).1.1.one_sub (by rwa [sub_sub_cancel])
    exact mul_eq_of_suppProj_le heproj (le_sub_comm.mp h4)
  have hfe : (f ((1 : A) - p) : B) = 0 := by rw [← heq]; exact (carrier_spec g hg).2.1
  have hebe : ∀ b : A, ((1 : A) - p) * b * (1 - p) = (1 - p) * b := by
    intro b
    refine hkey (((1 : A) - p) * b) ?_
    rw [hmul, hfe, zero_mul]
  have hcentral : IsCentral A ((1 : A) - p) := by
    intro b
    have h := congrArg star (hebe (star b))
    simp only [star_mul, star_star, heproj.isSelfAdjoint.star_eq] at h
    calc ((1 : A) - p) * b = (1 - p) * b * (1 - p) := (hebe b).symm
      _ = (1 - p) * (b * (1 - p)) := by noncomm_ring
      _ = b * (1 - p) := h
  have hpcentral : IsCentral A p := by
    intro b
    have h := hcentral b
    rw [sub_mul, mul_sub, one_mul, mul_one] at h
    exact sub_right_inj.mp h
  refine ⟨hpcentral, fun a => ?_⟩
  · constructor
    · intro ha
      have hae : a * ((1 : A) - p) = a := hkey a ha
      rw [mul_sub, mul_one, sub_eq_self] at hae
      rw [hpcentral a, hae]
    · intro ha
      have hea : ((1 : A) - p) * a = a := by rw [sub_mul, one_mul, ha, sub_zero]
      calc (f a : B) = f (((1 : A) - p) * a) := by rw [hea]
        _ = f ((1 : A) - p) * f a := hmul _ _
        _ = 0 := by rw [hfe, zero_mul]

/-- **69IVa** (`nmiu-factors`, vn.tex:3619, Exercise): an nmiu-map
`f : A → B` factors through the corner `⌈⌈f⌉⌉A` as an nmiu-surjection
`a ↦ ⌈⌈f⌉⌉a` followed by an nmiu-injection — rendered concretely:
`f(a) = f(⌈f⌉a)` for all `a`, and `f(a) = f(b)` iff `⌈f⌉a = ⌈f⌉b`. -/
theorem nmiu_factors (f : NMIUMap A B) (g : A →ₚ[ℂ] B)
    (hg : PreservesDirSups ⇑g) (heq : ∀ a, g a = f a) (a b : A) :
    f a = f (carrier g hg * a) ∧
      (f a = f b ↔ carrier g hg * a = carrier g hg * b) := by
  -- `f(a) = f(⌈f⌉a)` is **63VI**; the second claim is **69IV** applied to
  -- `a - b`
  have hker := (carrier_miu f g hg heq).2
  have hsub : ∀ x y : A, (f (x - y) : B) = f x - f y := fun x y =>
    map_sub f.toStarAlgHom x y
  refine ⟨by rw [← heq, ← heq]; exact (carrier_fundamental g hg a).1, ?_, ?_⟩
  · intro h
    have h0 : (f (a - b) : B) = 0 := by rw [hsub]; exact sub_eq_zero.mpr h
    have h1 := (hker (a - b)).mp h0
    rw [mul_sub, sub_eq_zero] at h1
    exact h1
  · intro h
    have h0 : carrier g hg * (a - b) = 0 := by rw [mul_sub, h, sub_self]
    have h1 := (hker (a - b)).mpr h0
    rw [hsub, sub_eq_zero] at h1
    exact h1

/-- **69IVb** (`nmiu-image`, vn.tex:3637): the image of an nmiu-map
`f : A → B` between von Neumann algebras is a von Neumann subalgebra of
`B`. -/
theorem nmiu_image (f : NMIUMap A B) :
    IsVNSubalgebra B f.toStarAlgHom.range :=
  sorry

/-- **69V** (`proto-gns-ceil`, vn.tex:3642, Lemma): `⌈⌈ω⌉⌉ = ⌈ρ_ω⌉` for an
np-functional `ω` on a von Neumann algebra with GNS representation `ρ_ω` —
rendered: for every normal cyclic representation `(ρ, ξ)` of `ω` on a
Hilbert space `H`, the carrier of `ρ` is the central support of `⌈ω⌉`. -/
theorem proto_gns_ceil {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (ω : NPFunctional A)
    (ρ : MIUMap A (H →L[ℂ] H)) (g : A →ₚ[ℂ] (H →L[ℂ] H))
    (hg : PreservesDirSups ⇑g) (heq : ∀ a, g a = ρ a) (ξ : H)
    (hξ : ∀ a : A, ω a = ⟪ξ, ρ a ξ⟫)
    (hcyc : Dense (Set.range fun a : A => ρ a ξ)) :
    carrier g hg = cceil (npCarrier ω) :=
  sorry

/-- **69VII** (`gns-ceil`, vn.tex:3670, Proposition):
`⌈ρ_Ω⌉ = ⋃_{ω∈Ω} ⌈⌈ω⌉⌉` for a collection `Ω` of np-functionals — rendered:
for every normal representation `ρ` on a Hilbert space in which each
`ω ∈ Ω` is given by a vector `x_ω`, with the `ρ(a)x_ω` spanning a dense
subspace, the carrier of `ρ` is `⋃_{ω∈Ω} ⌈⌈ω⌉⌉`. -/
theorem gns_ceil {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (Ω : Set (NPFunctional A)) (ρ : MIUMap A (H →L[ℂ] H))
    (g : A →ₚ[ℂ] (H →L[ℂ] H)) (hg : PreservesDirSups ⇑g)
    (heq : ∀ a, g a = ρ a) (x : Ω → H)
    (hx : ∀ ω : Ω, ∀ a : A, (ω : NPFunctional A) a = ⟪x ω, ρ a (x ω)⟫)
    (hcyc : Dense (Submodule.span ℂ
      (Set.range fun p : Ω × A => ρ p.2 (x p.1)) : Set H)) :
    carrier g hg =
      projSup {p : A | ∃ ω ∈ Ω, p = cceil (npCarrier ω)} :=
  sorry

variable (A) in
/-- A collection `Ω` of np-functionals is **centre separating**
(`separating`, cstar.tex 21II): a central positive `a` with `ω(a) = 0` for
all `ω ∈ Ω` is zero. -/
def CentreSeparating (Ω : Set (NPFunctional A)) : Prop :=
  ∀ a : A, IsCentral A a → 0 ≤ a → (∀ ω ∈ Ω, ω a = 0) → a = 0

/-- **69IX** (`vn-center-separating`, vn.tex:3693, Corollary): for a
collection `Ω` of np-functionals on a von Neumann algebra the following are
equivalent: (1) `Ω` is centre separating; (2) a central projection `z` with
`ω(z) = 0` for all `ω ∈ Ω` is zero; (3) `⋃_{ω∈Ω}⌈⌈ω⌉⌉ = 1` (equivalently:
the representation `ρ_Ω` is injective, cf. **69VII**). -/
theorem vn_center_separating (Ω : Set (NPFunctional A)) :
    List.TFAE
      [CentreSeparating A Ω,
       ∀ z : A, IsStarProjection z → IsCentral A z →
         (∀ ω ∈ Ω, ω z = 0) → z = 0,
       projSup {p : A | ∃ ω ∈ Ω, p = cceil (npCarrier ω)} = 1] :=
  sorry

/-! ## Parsec 700: the classification of commutative von Neumann algebras

**70I** (vn.tex:3743): introduction — nothing to formalize. -/

/-- **70II** (`central-projection-central-carrier`, vn.tex:3749, Exercise):
every central projection `c` of a von Neumann algebra is of the form
`c = ∑ᵢ ⌈⌈ωᵢ⌉⌉` for a family of np-functionals with pairwise orthogonal
central carriers. -/
theorem central_projection_central_carrier (c : A)
    (hc : IsStarProjection c) (hcentral : IsCentral A c) :
    ∃ (ι : Type _) (ω : ι → NPFunctional A),
      (Pairwise fun i j =>
        cceil (npCarrier (ω i)) * cceil (npCarrier (ω j)) = 0) ∧
      c = projSup (Set.range fun i => cceil (npCarrier (ω i))) :=
  sorry

end Commutant

/-- **70III** (`cvn`, vn.tex:3758, Theorem): every commutative von Neumann
algebra is nmiu-isomorphic to a direct sum `⊕ᵢ L^∞(Xᵢ)` of `L^∞`s of finite
complete measure spaces.
-- FIXME(typecheck): the target `⊕ᵢ L^∞(Xᵢ)` has no Mathlib carrier (cf.
51IX), so we state the reduction actually proved: `1 = ∑ᵢ ⌈⌈ωᵢ⌉⌉` for
np-functionals `ωᵢ` each faithful on its corner `⌈⌈ωᵢ⌉⌉A` — each corner is
then `L^∞(Xᵢ)` by 54XI (`cvn_faithful_1`). -/
theorem cvn {C : Type*} [CommCStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] [VonNeumannAlgebra C] :
    ∃ (ι : Type _) (ω : ι → NPFunctional C),
      (Pairwise fun i j =>
        cceil (npCarrier (ω i)) * cceil (npCarrier (ω j)) = 0) ∧
      projSup (Set.range fun i => cceil (npCarrier (ω i))) = 1 ∧
      ∀ i, ∀ a : C, 0 ≤ a → cceil (npCarrier (ω i)) * a = a →
        (ω i) a = 0 → a = 0 :=
  sorry

end Theses.A.VN
